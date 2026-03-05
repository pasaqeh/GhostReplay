--!strict

--[[
	GhostReplay - Last Update: 2026-03-05
	! This module is still in development and may be unstable or have missing features.
	
	By pasaqeh(Simon) -- roblox name / @pasaqeh -- discord name

	! Script exactly has: 729 lines of code excluding empty lines and comments.

	! Used in pair with loader with init() and start() functions and requires 3 folders, for Remote events, for pooled ghost models
	and workspace folder for spawned ghosts.


	-[Description]------------------------------------

	This module implements a ghost replay system for players in a Roblox game.
	Automatically, replay happens on player death, where a "ghost" of the player's last life is spawned and replays their movements and chat messages.
	The system supports multiple ghosts per player, with a limit on how many are stored and active at once.
	Recordings capture the player's CFrame at a fixed tickrate, and replays interpolate between these frames for smooth movement.
	Chat messages sent by the player during their life are also recorded and displayed as overhead text on the ghost during replay.

	! THIS FUNCTION ISN'T TESTED BY ME, BECAUSE I HAVE NO ACCESS TO CHAT (REGION RESTRICTED), SO THERE MIGHT POSSIBLE BE BUGS.


	-[Methods]------------------------------------

	- Module.init()
	 must be called before anything else, and only once. This sets up necessary connections and state.

	- Module.start()
	 must be called after init, and only once. This starts the recording and replay loops.

	- Module.BindGhostReplayOnDeath(player) --> boolean
	Can be called to bind the ghost replay functionality to a player's death.
	When that player dies, a ghost will be spawned that replays their last life.
	This is automatically called for all players if AUTO_ON_DEATH_REPLAY is true (in testing purposes).
	It can also be activated through remote events.

	- Module.UnbindGhostReplayOnDeath(player) --> boolean
	Can be called to unbind the ghost replay functionality from a player.
	Also can be activated through remote events

	- Module.GetPlayerGhost(player, ghostId) --> Ghost?
	Can be called to get a specific ghost instance for a player, if it exists.

	- Module.CreatePlayerGhostFromBase(player, ghostBase) --> Ghost?
	Can be called to create a ghost for a player from a GhostBase snapshot.

	- Module.CreatePlayerGhost(player, ghostProperties, ghostMessages)  --> Ghost?
	Can be called to create

	- Module.RemovePlayerGhost(player, ghostId) --> boolean
	Can be called to remove a specific ghost for a player.


	Notes:
	- Server-authoritative: all recording and playback is server-driven.
	- Ghost Models are anchored, non-colliding, and semi-transparent.
	- Ghosts are tagged via CollectionService with GHOST_TAG and have OwnerId + Id attributes for identification.

]]

--// Services
local ReplicatedStorage = game:GetService("ReplicatedStorage")
local Players = game:GetService("Players")
local CollectionService = game:GetService("CollectionService")
local RunService = game:GetService("RunService")
local ServerStorage = game:GetService("ServerStorage")
local TextChatService = game:GetService("TextChatService")
local TextService = game:GetService("TextService")

-- // Folders
local ReplayGhosts = workspace:WaitForChild("_ReplayGhosts")
local PooledGhosts = ServerStorage:WaitForChild("PooledGhosts")

--// Constants
local DEBUG_TEST_MESSAGES = true
local DEBUG_MESSAGE_INTERVAL = 5
local RECORDING_FPS = 30
local REPLAY_TICKRATE = 30
local REPLAY_STEP = 1 / REPLAY_TICKRATE
local MAX_GHOSTS_PER_PLAYER = 20
local MAX_STORED_GHOSTS_PER_PLAYER = MAX_GHOSTS_PER_PLAYER
local AUTO_ON_DEATH_REPLAY = true
local MAX_GHOST_HEALTH = 100
local GHOST_TAG = "Ghost"
local MAX_CHAT_MESSAGES_PER_LIFE = 50
local MAX_CHAT_MESSAGE_LEN = 120

-- // Overhead gui constants
local OVERHEAD_GUI_FONT = Enum.Font.FredokaOne
local OVERHEAD_GUI_TEXT_SIZE = 24
local OVERHEAD_GUI_TEXT_COLOR = Color3.new(1, 1, 1)
local OVERHEAD_GUI_TEXT_STROKE_COLOR = Color3.new(0, 0, 0)
local OVERHEAD_GUI_TEXT_STROKE_THICKNESS = 2
local OVERHEAD_GUI_OFFSET = Vector3.new(0, 3, 0)

--// Types
type ActiveReplayTask = {
	Player: Player,
	Ghost: Ghost,
	Generation: number,

	Frames: { CFrame },
	FrameCount: number,

	StartTime: number,
	Duration: number,

	NextGuiUpdateTime: number,

	-- NEW (chat replay)
	Messages: { GhostMessage },
	NextMessageIndex: number,
}

-- // Exported types
export type GhostMessage = {
	Message: TextFilterResult,
	Time: number,
}

export type GhostProperties = {
	RecordedCFrames: { CFrame },
	StartingCFrame: CFrame,
	LastCFrame: CFrame,
	TimeAlive: number,
}

export type GhostBase = {
	Properties: GhostProperties,
	Messages: { GhostMessage },
}

export type GhostOverheadGui = BillboardGui & {
	TimeLeftLabel: TextLabel,
}

export type Ghost = {
	Properties: GhostProperties,
	Messages: { GhostMessage },
	Model: Model,
	OverheadGui: GhostOverheadGui,
	Id: number,
}

export type GhostReplay = {
	--Must be called once before any other method.
	init: () -> (),

	--Must be called once after init(). Starts recording/replay loops.
	start: () -> (),
	--Enables recording + auto replay on death for this player.
	--Returns false if player invalid, already bound, or character/humanoid not ready.
	BindGhostReplayOnDeath: (player: Player?) -> boolean,

	--Disables recording/replay for this player and clears connections + per-life state.
	--Returns false if player invalid or not currently bound.
	UnbindGhostReplayOnDeath: (player: Player?) -> boolean,

	--Returns the currently spawned ghost (from currentGhostsOnDeathReplays) for a player by id.
	GetPlayerGhost: (player: Player?, ghostId: number?) -> Ghost?,

	--Spawns a ghost from a stored GhostBase snapshot, inserts it into active list,
	--enforces MAX_GHOSTS_PER_PLAYER, and returns the created Ghost.
	CreatePlayerGhostFromBase: (player: Player?, ghostBase: GhostBase?) -> Ghost?,

	--Convenience wrapper that builds a GhostBase from properties/messages then calls CreatePlayerGhostFromBase.
	CreatePlayerGhost: (player: Player?, ghostProperties: GhostProperties?, ghostMessages: { GhostMessage }?) -> Ghost?,

	--Removes one active ghost by id, releases pooled model, destroys overhead gui.
	RemovePlayerGhost: (player: Player?, ghostId: number?) -> boolean,
}

-- // Module
local GhostReplay = {} :: GhostReplay

--// States
local State = {
	playersWithGhosts = {} :: { [Player]: boolean },

	storedGhostsOnDeathReplays = {} :: { [Player]: { GhostBase } },
	currentGhostsOnDeathReplays = {} :: { [Player]: { Ghost } },

	nextGhostId = {} :: { [Player]: number },

	startingTime = {} :: { [Player]: number },
	recordAccum = {} :: { [Player]: number },
	onDeathGhostProperties = {} :: { [Player]: GhostProperties },
	onDeathMessages = {} :: { [Player]: { GhostMessage } },
	lastRecordedCFrame = {} :: { [Player]: CFrame? },

	processingPlayersDeath = {} :: { [Player]: boolean },
	onDeathReplayConnections = {} :: { [Player]: { RBXScriptConnection } },
	replayGeneration = {} :: { [Player]: number },

	activeReplays = {} :: { [number]: ActiveReplayTask },
	nextReplayTaskId = 0,

	initialized = false,
	started = false,
}

--// Connections functions
local function disconnectAll(connections: { RBXScriptConnection }?)
	if not connections then
		return
	end
	for _, connection in connections do
		if connection.Connected then
			connection:Disconnect()
		end
	end
end

local function clearPlayerConnections(player: Player)
	disconnectAll(State.onDeathReplayConnections[player])
	State.onDeathReplayConnections[player] = nil
end

--// Clone helpers functions
local function cloneGhostMessages(messages: { GhostMessage }): { GhostMessage }
	local out = table.create(#messages) :: { GhostMessage }
	for i, message in messages do
		out[i] = { Message = message.Message, Time = message.Time }
	end
	return out
end

local function cloneGhostProperties(properties: GhostProperties): GhostProperties
	local frames = properties.RecordedCFrames
	local framesCopy = table.create(#frames) :: { CFrame }
	for i, frame in frames do
		framesCopy[i] = frame
	end

	return {
		RecordedCFrames = framesCopy,
		StartingCFrame = properties.StartingCFrame,
		LastCFrame = properties.LastCFrame,
		TimeAlive = properties.TimeAlive,
	}
end

local function buildGhostBaseSnapshot(properties: GhostProperties, messages: { GhostMessage }): GhostBase
	return {
		Properties = cloneGhostProperties(properties),
		Messages = cloneGhostMessages(messages),
	}
end

-- // Chat functions
local function displayGhostMessage(taskObject: ActiveReplayTask, elapsed: number)
	local messages = taskObject.Messages
	local index = taskObject.NextMessageIndex

	if index > #messages then
		return
	end

	local ghost = taskObject.Ghost
	local model = ghost.Model
	if not model or not model.Parent then
		return
	end

	local bubbleTarget = model:FindFirstChild("Head")
	if not bubbleTarget then
		bubbleTarget = model.PrimaryPart
	end
	if not bubbleTarget or not bubbleTarget:IsA("BasePart") then
		return
	end

	while index <= #messages do
		local msg = messages[index]
		if elapsed < msg.Time then
			break
		end

		local filteredMessage = msg.Message:GetNonChatStringForBroadcastAsync()
		TextChatService:DisplayBubble(bubbleTarget, filteredMessage)

		index += 1
	end

	taskObject.NextMessageIndex = index
end

local function debugGenerateMessages(taskObject: ActiveReplayTask, elapsed: number)
	if not DEBUG_TEST_MESSAGES then
		return
	end

	local messages = taskObject.Messages
	local expectedCount = math.floor(elapsed / DEBUG_MESSAGE_INTERVAL)

	if #messages >= expectedCount then
		return
	end

	local nextIndex = #messages + 1
	local timeStamp = nextIndex * DEBUG_MESSAGE_INTERVAL
	local text = "Test message " .. tostring(nextIndex)

	local ok, filtered = pcall(function()
		return TextService:FilterStringAsync(text, taskObject.Player.UserId)
	end)
	if not ok or not filtered then
		return
	end

	table.insert(messages, {
		Message = filtered,
		Time = timeStamp,
	})
end

--// GUI helpers functions
local function formatTime(seconds: number): string
	local minutes = math.floor(seconds / 60)
	local secs = math.floor(seconds % 60)
	return string.format("%02d:%02d", minutes, secs)
end

local function createGhostOverheadGui(startingTime: number, enabled: boolean?): GhostOverheadGui
	local gui = Instance.new("BillboardGui")
	gui.Name = "GhostOverheadGui"
	gui.Size = UDim2.new(0, 200, 0, 50)
	gui.StudsOffset = OVERHEAD_GUI_OFFSET
	gui.AlwaysOnTop = true
	gui.Enabled = enabled or false

	local timeLeftLabel = Instance.new("TextLabel")
	timeLeftLabel.Name = "TimeLeftLabel"
	timeLeftLabel.Size = UDim2.new(1, 0, 1, 0)
	timeLeftLabel.BackgroundTransparency = 1
	timeLeftLabel.TextColor3 = OVERHEAD_GUI_TEXT_COLOR
	timeLeftLabel.Font = OVERHEAD_GUI_FONT
	timeLeftLabel.TextSize = OVERHEAD_GUI_TEXT_SIZE
	timeLeftLabel.Text = formatTime(startingTime)
	timeLeftLabel.Parent = gui

	local uistroke = Instance.new("UIStroke")
	uistroke.Color = OVERHEAD_GUI_TEXT_STROKE_COLOR
	uistroke.Thickness = OVERHEAD_GUI_TEXT_STROKE_THICKNESS
	uistroke.Parent = timeLeftLabel

	return gui :: GhostOverheadGui
end

--// Pooling helpers
local function destroyScripts(model: Model)
	for _, child in model:GetChildren() do
		if child:IsA("Script") or child:IsA("LocalScript") then
			child:Destroy()
		end
	end
end

local function configureGhostModel(model: Model)
	local hum = model:FindFirstChildOfClass("Humanoid")
	if hum then
		hum.DisplayDistanceType = Enum.HumanoidDisplayDistanceType.None
		hum.MaxHealth = math.max(hum.MaxHealth, MAX_GHOST_HEALTH)
		hum.Health = hum.MaxHealth
		hum:SetStateEnabled(Enum.HumanoidStateType.Dead, false)
	end

	for _, inst in model:GetDescendants() do
		if inst:IsA("BasePart") then
			inst.Transparency = 0.5
			inst.Anchored = true
			inst.CanCollide = false
			inst.CanTouch = false
			inst.CanQuery = false
		end
	end
end

local function getUserPoolFolder(player: Player): Folder
	local folderName = tostring(player.UserId)
	local existing = PooledGhosts:FindFirstChild(folderName)
	if existing and existing:IsA("Folder") then
		return existing
	end

	local folder = Instance.new("Folder")
	folder.Name = folderName
	folder.Parent = PooledGhosts
	return folder
end

local function destroyUserPoolFolder(player: Player)
	local folderName = tostring(player.UserId)
	local existing = PooledGhosts:FindFirstChild(folderName)
	if existing and existing:IsA("Folder") then
		existing:Destroy()
	end
end

local function acquirePooledGhostModel(player: Player): Model?
	local userPool = getUserPoolFolder(player)
	local pooled = userPool:FindFirstChildWhichIsA("Model")
	if pooled then
		return pooled
	end

	-- // Fallback cloning character
	local character = player.Character
	if not character then
		return nil
	end

	character.Archivable = true
	local ghostModel = character:Clone()
	ghostModel.Name = "Ghost"
	character.Archivable = false

	destroyScripts(ghostModel)
	configureGhostModel(ghostModel)

	return ghostModel
end

local function releasePooledGhostModel(player: Player, model: Model)
	local existingGui = model:FindFirstChild("GhostOverheadGui")
	if existingGui and existingGui:IsA("BillboardGui") then
		existingGui:Destroy()
	end

	if CollectionService:HasTag(model, GHOST_TAG) then
		CollectionService:RemoveTag(model, GHOST_TAG)
	end
	model:SetAttribute("OwnerUserId", nil)
	model:SetAttribute("Id", nil)

	for _, inst in model:GetDescendants() do
		if inst:IsA("BasePart") then
			inst.Anchored = true
			inst.CanCollide = false
			inst.CanTouch = false
			inst.CanQuery = false
			inst.Transparency = 0.5
		end
	end

	if player.Parent ~= Players then
		model:Destroy()
		return
	end

	local userPool = getUserPoolFolder(player)
	model.Parent = userPool
end

local function createGhost(player: Player, ghostId: number, ghostBase: GhostBase): Ghost?
	local ghostModel = acquirePooledGhostModel(player)
	if not ghostModel then
		warn("Failed to acquire pooled ghost model, PLAYER_NAME: " .. player.Name)
		return nil
	end

	destroyScripts(ghostModel)
	configureGhostModel(ghostModel)

	local overheadGui = createGhostOverheadGui(ghostBase.Properties.TimeAlive, true)
	overheadGui.Parent = ghostModel.PrimaryPart or ghostModel:FindFirstChild("Head") or ghostModel

	ghostModel:PivotTo(ghostBase.Properties.StartingCFrame)
	ghostModel:SetAttribute("OwnerUserId", player.UserId)
	ghostModel:SetAttribute("Id", ghostId)

	ghostModel.Parent = ReplayGhosts
	CollectionService:AddTag(ghostModel, GHOST_TAG)

	local ghost: Ghost = {
		Properties = cloneGhostProperties(ghostBase.Properties),
		Messages = cloneGhostMessages(ghostBase.Messages),
		Model = ghostModel,
		OverheadGui = overheadGui,
		Id = ghostId,
	}

	return ghost
end

local function findPlayerGhost(player: Player, ghostId: number): Ghost?
	local list = State.currentGhostsOnDeathReplays[player]
	if not list then
		return nil
	end

	for _, currentGhost in list do
		if currentGhost.Id == ghostId then
			return currentGhost
		end
	end

	return nil
end

local function removePlayerGhost(player: Player, ghostId: number): boolean
	local list = State.currentGhostsOnDeathReplays[player]
	if not list then
		warn("Ghost list does not exist for player, PLAYER_NAME: " .. player.Name)
		return false
	end

	for i = 1, #list do
		local ghost = list[i]
		if ghost.Id == ghostId then
			if ghost.OverheadGui and ghost.OverheadGui.Parent then
				ghost.OverheadGui:Destroy()
			end
			if ghost.Model then
				releasePooledGhostModel(player, ghost.Model)
			end
			table.remove(list, i)
			return true
		end
	end

	return false
end

local function removeAllPlayerGhosts(player: Player)
	local list = State.currentGhostsOnDeathReplays[player]
	if not list or #list == 0 then
		return
	end

	for i = #list, 1, -1 do
		local ghost = list[i]
		if ghost.OverheadGui and ghost.OverheadGui.Parent then
			ghost.OverheadGui:Destroy()
		end
		if ghost.Model then
			releasePooledGhostModel(player, ghost.Model)
		end
		table.remove(list, i)
	end
end

-- // Tasks functions
local function startReplayTask(player: Player, ghost: Ghost, generation: number)
	local model = ghost.Model
	if not model or not model.Parent then
		return
	end

	local frames = ghost.Properties.RecordedCFrames
	local frameCount = #frames
	if frameCount == 0 then
		removePlayerGhost(player, ghost.Id)
		return
	end

	State.nextReplayTaskId += 1
	local taskId = State.nextReplayTaskId

	local startTime = workspace:GetServerTimeNow()
	local duration = math.max(0, (frameCount - 1) / RECORDING_FPS)

	model:PivotTo(frames[1])

	State.activeReplays[taskId] = {
		Player = player,
		Ghost = ghost,
		Generation = generation,

		Frames = frames,
		FrameCount = frameCount,

		StartTime = startTime,
		Duration = duration,

		NextGuiUpdateTime = startTime,

		Messages = ghost.Messages,
		NextMessageIndex = 1,
	}
end

local function finalizeLifeAndSpawnGhost(player: Player)
	State.processingPlayersDeath[player] = true

	local props = State.onDeathGhostProperties[player]
	local msgs = State.onDeathMessages[player]
	if not props or not msgs then
		return
	end

	local base = buildGhostBaseSnapshot(props, msgs)

	local stored = State.storedGhostsOnDeathReplays[player]
	if not stored then
		stored = {}
		State.storedGhostsOnDeathReplays[player] = stored
	end

	table.insert(stored, base)
	while #stored > MAX_STORED_GHOSTS_PER_PLAYER do
		table.remove(stored, 1)
	end

	local replayGeneration = (State.replayGeneration[player] or 0) + 1
	State.replayGeneration[player] = replayGeneration

	removeAllPlayerGhosts(player)

	for _, storedBase in stored do
		local playerGhost = GhostReplay.CreatePlayerGhostFromBase(player, storedBase)
		if playerGhost then
			startReplayTask(player, playerGhost, replayGeneration)
		end
	end
end

local function beginLifeRecording(player: Player, character: Model)
	local humanoid = character:FindFirstChildOfClass("Humanoid")
	if not humanoid then
		warn("Player humanoid is invalid during beginLifeRecording, PLAYER_NAME: " .. player.Name)
		return
	end

	State.onDeathMessages[player] = {}
	State.startingTime[player] = workspace:GetServerTimeNow()
	State.processingPlayersDeath[player] = false

	local pivot = character:GetPivot()
	State.onDeathGhostProperties[player] = {
		RecordedCFrames = { pivot },
		StartingCFrame = pivot,
		LastCFrame = pivot,
		TimeAlive = 0,
	}
	State.lastRecordedCFrame[player] = pivot

	humanoid.Died:Once(function()
		finalizeLifeAndSpawnGhost(player)
	end)
end

local function setupPlayerState(player: Player)
	State.currentGhostsOnDeathReplays[player] = {}
	State.storedGhostsOnDeathReplays[player] = {}
	State.onDeathMessages[player] = {}
	State.processingPlayersDeath[player] = false
	State.recordAccum[player] = 0
	State.nextGhostId[player] = 0
	State.replayGeneration[player] = 0

	if not AUTO_ON_DEATH_REPLAY then
		return
	end
	if player.Character then
		GhostReplay.BindGhostReplayOnDeath(player)
	else
		player.CharacterAdded:Once(function()
			GhostReplay.BindGhostReplayOnDeath(player)
		end)
	end
end

function GhostReplay.init()
	if State.initialized then
		warn("GhostReplay.init() already called")
		return
	end
	State.initialized = true

	Players.PlayerAdded:Connect(setupPlayerState)

	for _, player in Players:GetPlayers() do
		setupPlayerState(player)
	end

	Players.PlayerRemoving:Connect(function(player: Player)
		if State.playersWithGhosts[player] then
			GhostReplay.UnbindGhostReplayOnDeath(player)
		end

		removeAllPlayerGhosts(player)
		clearPlayerConnections(player)

		State.playersWithGhosts[player] = nil
		State.currentGhostsOnDeathReplays[player] = nil
		State.storedGhostsOnDeathReplays[player] = nil
		State.processingPlayersDeath[player] = nil
		State.onDeathGhostProperties[player] = nil
		State.onDeathMessages[player] = nil
		State.startingTime[player] = nil
		State.recordAccum[player] = nil
		State.lastRecordedCFrame[player] = nil
		State.nextGhostId[player] = nil
		State.replayGeneration[player] = nil

		destroyUserPoolFolder(player)
	end)
end

function GhostReplay.start()
	if State.started then
		warn("GhostReplay.start() already called")
		return
	end
	State.started = true

	local recordStep = 1 / RECORDING_FPS
	local recordAccum = 0
	local replayAccum = 0

	RunService.Heartbeat:Connect(function(dt: number)
		-- // Recording
		recordAccum += dt
		while recordAccum >= recordStep do
			recordAccum -= recordStep

			for player, _ in State.playersWithGhosts do
				if State.processingPlayersDeath[player] then
					continue
				end

				local character = player.Character
				if not character then
					continue
				end

				local props = State.onDeathGhostProperties[player]
				if not props then
					continue
				end

				local pivot = character:GetPivot()
				table.insert(props.RecordedCFrames, pivot)
				props.LastCFrame = pivot
				props.TimeAlive += recordStep
				State.lastRecordedCFrame[player] = pivot
			end
		end

		-- // Replay
		replayAccum += dt
		if replayAccum < REPLAY_STEP then
			return
		end
		replayAccum -= REPLAY_STEP

		local now = workspace:GetServerTimeNow()

		for taskId, taskObject in State.activeReplays do
			local player = taskObject.Player
			local ghost = taskObject.Ghost
			local model = ghost.Model

			if State.replayGeneration[player] ~= taskObject.Generation then
				State.activeReplays[taskId] = nil
				continue
			end

			if not model or not model.Parent then
				State.activeReplays[taskId] = nil
				continue
			end

			local elapsed = now - taskObject.StartTime
			if elapsed < 0 then
				elapsed = 0
			end
			debugGenerateMessages(taskObject, elapsed)
			displayGhostMessage(taskObject, elapsed)

			if ghost.OverheadGui and ghost.OverheadGui.Parent and now >= taskObject.NextGuiUpdateTime then
				local timeLeft = math.max(0, taskObject.Duration - elapsed)
				ghost.OverheadGui.TimeLeftLabel.Text = formatTime(timeLeft)
				taskObject.NextGuiUpdateTime = now + 0.25
			end

			local framePos = math.clamp(1 + (elapsed * RECORDING_FPS), 1, taskObject.FrameCount)
			local low = math.floor(framePos)
			local high = math.min(low + 1, taskObject.FrameCount)
			local alpha = framePos - low

			local cframe: CFrame
			if low == high then
				cframe = taskObject.Frames[low]
			else
				cframe = taskObject.Frames[low]:Lerp(taskObject.Frames[high], alpha)
			end

			model:PivotTo(cframe)

			if elapsed >= taskObject.Duration then
				State.activeReplays[taskId] = nil
				removePlayerGhost(player, ghost.Id)
			end
		end
	end)
end

function GhostReplay.BindGhostReplayOnDeath(player: Player?): boolean
	if not player or player.Parent ~= Players then
		return false
	end
	if State.playersWithGhosts[player] then
		return false
	end

	clearPlayerConnections(player)

	local character = player.Character
	if not character then
		return false
	end

	local humanoid = character:FindFirstChildOfClass("Humanoid")
	if not humanoid or humanoid.Health <= 0 then
		return false
	end

	State.playersWithGhosts[player] = true
	State.replayGeneration[player] = 0
	State.onDeathReplayConnections[player] = {}

	table.insert(
		State.onDeathReplayConnections[player],
		player.CharacterAdded:Connect(function(newCharacter: Model)
			beginLifeRecording(player, newCharacter)
		end)
	)

	table.insert(
		State.onDeathReplayConnections[player],
		player.CharacterRemoving:Connect(function()
			State.recordAccum[player] = nil
			State.onDeathGhostProperties[player] = nil
			State.onDeathMessages[player] = {}
			State.startingTime[player] = nil
			State.lastRecordedCFrame[player] = nil
		end)
	)

	table.insert(
		State.onDeathReplayConnections[player],
		player.Chatted:Connect(function(message: string)
			local startTime = State.startingTime[player]
			local messages = State.onDeathMessages[player]
			if not startTime or not messages then
				return
			end
			if #messages >= MAX_CHAT_MESSAGES_PER_LIFE then
				return
			end
			if #message > MAX_CHAT_MESSAGE_LEN then
				message = string.sub(message, 1, MAX_CHAT_MESSAGE_LEN)
			end

			local success, result = pcall(function()
				return TextService:FilterStringAsync(message, player.UserId)
			end)
			if not success then
				return
			end

			table.insert(messages, {
				Message = result,
				Time = workspace:GetServerTimeNow() - startTime,
			})
		end)
	)

	beginLifeRecording(player, character)
	return true
end

function GhostReplay.UnbindGhostReplayOnDeath(player: Player?): boolean
	if not player or player.Parent ~= Players then
		return false
	end
	if not State.playersWithGhosts[player] then
		return false
	end

	clearPlayerConnections(player)

	State.playersWithGhosts[player] = nil
	State.processingPlayersDeath[player] = nil
	State.onDeathGhostProperties[player] = nil
	State.recordAccum[player] = nil
	State.startingTime[player] = nil
	State.onDeathMessages[player] = nil
	State.lastRecordedCFrame[player] = nil
	State.replayGeneration[player] = nil
	return true
end

function GhostReplay.GetPlayerGhost(player: Player?, ghostId: number?): Ghost?
	if not player or player.Parent ~= Players then
		return nil
	end
	if typeof(ghostId) ~= "number" then
		return nil
	end
	return findPlayerGhost(player, ghostId :: number)
end

function GhostReplay.CreatePlayerGhostFromBase(player: Player?, ghostBase: GhostBase?): Ghost?
	if not player or player.Parent ~= Players then
		return nil
	end

	local list = State.currentGhostsOnDeathReplays[player]
	if not list then
		return nil
	end

	if not ghostBase then
		return nil
	end

	local ghostId = (State.nextGhostId[player] or 0) + 1
	State.nextGhostId[player] = ghostId

	local ghost = createGhost(player, ghostId, ghostBase)
	if not ghost then
		return nil
	end

	table.insert(list, ghost)

	while #list > MAX_GHOSTS_PER_PLAYER do
		local oldest = table.remove(list, 1)
		if oldest then
			if oldest.OverheadGui and oldest.OverheadGui.Parent then
				oldest.OverheadGui:Destroy()
			end
			if oldest.Model then
				releasePooledGhostModel(player, oldest.Model)
			end
		end
	end

	return ghost
end

function GhostReplay.CreatePlayerGhost(
	player: Player?,
	ghostProperties: GhostProperties?,
	ghostMessages: { GhostMessage }?
): Ghost?
	if not ghostProperties then
		return nil
	end

	local base: GhostBase = {
		Properties = cloneGhostProperties(ghostProperties),
		Messages = ghostMessages and cloneGhostMessages(ghostMessages) or {},
	}

	return GhostReplay.CreatePlayerGhostFromBase(player, base)
end

function GhostReplay.RemovePlayerGhost(player: Player?, ghostId: number?): boolean
	if not player or player.Parent ~= Players then
		return false
	end
	if typeof(ghostId) ~= "number" then
		return false
	end
	return removePlayerGhost(player, ghostId :: number)
end

return GhostReplay