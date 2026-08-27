local Players = game:GetService("Players")
local RunService = game:GetService("RunService")
local UserInputService = game:GetService("UserInputService")
local Lighting = game:GetService("Lighting")
local StatsService = game:GetService("Stats")
local Workspace = game:GetService("Workspace")

local player = Players.LocalPlayer
if not player then
	error("Autonomous Performance Engine: LocalPlayer is not available. Run after the game has loaded.")
end

local playerGui = player:WaitForChild("PlayerGui", 15)
if not playerGui then
	error("Autonomous Performance Engine: PlayerGui was not available.")
end

-- UI host: PlayerGui is preferred for normal LocalScripts; executor environments
-- may expose gethui(), which is a more reliable client UI container there.
local function getUIHost()
	local host = playerGui
	local ok, hui = pcall(function()
		return type(gethui) == "function" and gethui() or nil
	end)
	if ok and hui then host = hui end
	return host
end
local UIHost = getUIHost()
local bootGui = Instance.new("ScreenGui")
bootGui.Name = "AutonomousPerfBoot"
bootGui.ResetOnSpawn = false
bootGui.IgnoreGuiInset = true
bootGui.DisplayOrder = 1000000
bootGui.Parent = UIHost
local bootLabel = Instance.new("TextLabel")
bootLabel.AnchorPoint = Vector2.new(1, 0.5)
bootLabel.Position = UDim2.new(1, -18, 0.5, 0)
bootLabel.Size = UDim2.fromOffset(230, 42)
bootLabel.BackgroundColor3 = Color3.fromRGB(18, 18, 23)
bootLabel.BackgroundTransparency = 0.08
bootLabel.TextColor3 = Color3.fromRGB(255, 255, 255)
bootLabel.Font = Enum.Font.GothamBold
bootLabel.TextSize = 14
bootLabel.Text = "APE - Initializing..."
bootLabel.Parent = bootGui
Instance.new("UICorner", bootLabel).CornerRadius = UDim.new(0, 10)


--=============================================================
-- CONFIG
--=============================================================
local CONFIG = {
	SampleWindow = 0.5,
	HistoryLength = 60,
	FrameRingSize = 60,
	SpikeMultiplier = 3.5,
	SpikeMinDelta = 0.05,
	AttackRate = 0.9,
	DecayRate = 0.06,
	SpikeJump = 0.20,
	RecoveryMargin = 1.12,
	DefaultTargetFPS = 60,
	MinTargetFPS = 24,
	MaxTargetFPS = 120,
	StreamingRadiusFloor = 128,
	DefaultAutoOptimize = true,

	-- v3 closed-loop decision settings
	DecisionInterval = 2,      -- seconds between normal decision ticks
	SettleTime = 1.5,          -- seconds to wait before measuring an action's effect
	MaxBatch = 5,              -- max objects touched per action (keeps attribution clean)
	MinImprovementMs = 0.4,    -- below this measured improvement, revert the batch
	LearnAlpha = 0.4,          -- EMA weight for updating learned impact per object
	SpikeDecayInterval = 30,   -- seconds between halving spike-association scores
	SpikeDecayFactor = 0.5,
	JitterSpikyThreshold = 12, -- ms jitter above which we call conditions "spiky"

	-- v4 causal experiment settings
	ExperimentBatch = 1,
	BaselineSamples = 4,
	SettleSamples = 4,
	MinImprovementMs = 0.4,
	NoiseFloorMs = 0.25,
	ConfidenceAlpha = 0.22,
	MaxExperimentsPerObject = 8,
	ExperimentCooldown = 0.75,
	ContextTolerance = 0.18,
	RestoreTestEnabled = true,
}

--=============================================================
-- STATE
--=============================================================
local state = {
	fps = 60,
	smoothedFPS = 60,
	frameTimeMs = 16.6,
	jitterMs = 0,
	ping = 0,
	intensity = 0,
	targetFPS = CONFIG.DefaultTargetFPS,
	autoOptimize = CONFIG.DefaultAutoOptimize,
	panelOpen = false,
	compact = false,
	lastSpikeAt = 0,
	sampleTimer = 0,
	decisionTimer = 0,
	resortTimer = 0,
	spikeDecayTimer = 0,
	actionState = "idle", -- "idle" | "settling"
	diagnosis = "stable", -- "stable" | "sustained" | "spiky"
	log = {},

	history = {fps = {}, ping = {}, frametime = {}},

	session = {
		startClock = os.clock(),
		fpsMin = math.huge, fpsMax = 0, fpsSum = 0, fpsCount = 0,
		pingMin = math.huge, pingMax = 0, pingSum = 0, pingCount = 0,
		optimizationEvents = 0,
		timeInBand = {low = 0, medium = 0, high = 0, extreme = 0},
	},
}

local pendingAction = nil -- {batch, baseline, direction, startClock}

-- Frame-time ring buffer (jitter + spike detection)
local frameRing = {}
local frameRingSum, frameRingSumSq, frameRingIndex = 0, 0, 1
for i = 1, CONFIG.FrameRingSize do
	frameRing[i] = 1 / 60
	frameRingSum += frameRing[i]
	frameRingSumSq += frameRing[i] ^ 2
end

local function pushFrameTime(dt)
	local old = frameRing[frameRingIndex]
	frameRingSum = frameRingSum - old + dt
	frameRingSumSq = frameRingSumSq - old ^ 2 + dt ^ 2
	frameRing[frameRingIndex] = dt
	frameRingIndex = (frameRingIndex % CONFIG.FrameRingSize) + 1

	local n = CONFIG.FrameRingSize
	local mean = frameRingSum / n
	local variance = math.max(0, frameRingSumSq / n - mean ^ 2)
	state.frameTimeMs = mean * 1000
	state.jitterMs = math.sqrt(variance) * 1000
	return mean
end

local function addLog(msg)
	table.insert(state.log, 1, ("[%s] %s"):format(os.date("%H:%M:%S"), msg))
	if #state.log > 24 then table.remove(state.log) end
end

local function pushHistory(list, value)
	table.insert(list, value)
	if #list > CONFIG.HistoryLength then table.remove(list, 1) end
end

--=============================================================
-- COST-WEIGHTED, LEARNING OBJECT REGISTRY
--=============================================================
local registry = {}
local registryLookup = {}

local KIND_BASE_WEIGHT = {
	ParticleEmitter = 1.0, Trail = 0.6, Beam = 0.6, Fire = 0.8, Smoke = 0.5, Sparkles = 0.4,
}

local function estimateCost(inst)
	if inst:IsA("ParticleEmitter") then
		local rate = inst.Rate or 20
		local lifeAvg = 1
		local ok, life = pcall(function() return inst.Lifetime end)
		if ok and life then lifeAvg = (life.Min + life.Max) / 2 end
		return KIND_BASE_WEIGHT.ParticleEmitter * math.clamp(rate * lifeAvg, 1, 500)
	elseif inst:IsA("Trail") then
		return KIND_BASE_WEIGHT.Trail * math.clamp((inst.Lifetime or 1) * 10, 1, 100)
	elseif inst:IsA("Beam") then
		return KIND_BASE_WEIGHT.Beam * 20
	elseif inst:IsA("Fire") then
		return KIND_BASE_WEIGHT.Fire * math.clamp((inst.Size or 5) * 5, 1, 100)
	elseif inst:IsA("Smoke") then
		return KIND_BASE_WEIGHT.Smoke * 15
	elseif inst:IsA("Sparkles") then
		return KIND_BASE_WEIGHT.Sparkles * 10
	end
	return 0
end

local function registerInstance(inst)
	if registryLookup[inst] then return end
	local kind = inst.ClassName
	if not KIND_BASE_WEIGHT[kind] then return end
	local initialEnabled = true
	pcall(function() initialEnabled = inst.Enabled end)
	local entry = {
		inst = inst, kind = kind, cost = estimateCost(inst),
		disabledByUs = false, originalValue = initialEnabled,
		learnedImpact = 0, sampleCount = 0, spikeAssociation = 0,
		impactEMA = 0, impactVariance = 0, confidence = 0,
		experimentCount = 0, successCount = 0, failCount = 0,
		lastTestAt = -math.huge, lastResult = "untested",
		contextFPS = 0, contextJitter = 0,
	}
	registryLookup[inst] = entry
	table.insert(registry, entry)
	inst.Destroying:Connect(function()
		registryLookup[inst] = nil
		for i = #registry, 1, -1 do
			if registry[i] == entry then table.remove(registry, i) break end
		end
	end)
end

for _, inst in ipairs(Workspace:GetDescendants()) do registerInstance(inst) end
Workspace.DescendantAdded:Connect(registerInstance)

local postEffects = {}
local postEffectsDisabledByUs = false
local function cachePostEffect(inst)
	if inst:IsA("PostEffect") and postEffects[inst] == nil then postEffects[inst] = inst.Enabled end
end
for _, inst in ipairs(Lighting:GetChildren()) do cachePostEffect(inst) end
Lighting.ChildAdded:Connect(cachePostEffect)

local originalGlobalShadows = Lighting.GlobalShadows
local originalStreamingRadius = 1000
pcall(function() originalStreamingRadius = Workspace.StreamingTargetRadius end)
local shadowsDisabledByUs = false
local streamingReducedByUs = false

local function resortRegistry()
	for i = #registry, 1, -1 do
		if not registry[i].inst.Parent then
			registryLookup[registry[i].inst] = nil
			table.remove(registry, i)
		end
	end
end

--=============================================================
-- RANKING: static cost, scaled by what we've actually learned, plus
-- a spike-association bonus that fades over time.
--=============================================================
local function computeFinalRank(entry)
	local learnedMultiplier = 1
	if entry.sampleCount > 0 then
		local ratio = entry.learnedImpact / math.max(entry.cost, 0.01)
		learnedMultiplier = math.clamp(1 + ratio, 0.15, 4)
	end

	local exploration = entry.sampleCount == 0
		and math.max(entry.cost * 0.18, 2)
		or (1 / math.sqrt(entry.sampleCount + 1)) * math.max(entry.cost * 0.08, 1)

	local confidenceBonus = entry.confidence * math.max(entry.cost, 1) * 0.15
	local base = entry.cost * learnedMultiplier + exploration + confidenceBonus

	if state.diagnosis == "spiky" then
		return entry.spikeAssociation * 12 + base * 0.25
	else
		return base + entry.spikeAssociation * 2
	end
end

local function collectCandidates(wantEnabledOnes)
	local list = {}
	for _, e in ipairs(registry) do
		if e.inst.Parent then
			if wantEnabledOnes and not e.disabledByUs then
				table.insert(list, e)
			elseif (not wantEnabledOnes) and e.disabledByUs then
				table.insert(list, e)
			end
		end
	end
	return list
end

local lastDiagnosis = "stable"
local function updateDiagnosis()
	if state.jitterMs > CONFIG.JitterSpikyThreshold and state.smoothedFPS >= state.targetFPS * 0.85 then
		state.diagnosis = "spiky"
	elseif state.smoothedFPS < state.targetFPS * 0.85 then
		state.diagnosis = "sustained"
	else
		state.diagnosis = "stable"
	end
	if state.diagnosis ~= lastDiagnosis then
		local text = state.diagnosis == "spiky" and "Diagnosis: frame-time spikes, average FPS is fine"
			or state.diagnosis == "sustained" and "Diagnosis: sustained low FPS"
			or "Diagnosis: stable"
		addLog(text)
		lastDiagnosis = state.diagnosis
	end
end

--=============================================================
-- ACTIONS: apply a batch, wait, measure, keep-or-revert, learn.
--=============================================================
local function median(values)
	if #values == 0 then return 0 end
	local copy = table.clone(values)
	table.sort(copy)
	local n = #copy
	if n % 2 == 1 then return copy[(n + 1) / 2] end
	return (copy[n / 2] + copy[n / 2 + 1]) / 2
end

local function contextSignature()
	return {
		fps = state.smoothedFPS,
		jitter = state.jitterMs,
		intensity = state.intensity,
		diagnosis = state.diagnosis,
	}
end

local function contextDistance(a, b)
	if not a or not b then return 1 end
	local fps = math.abs(a.fps - b.fps) / math.max(state.targetFPS, 1)
	local jitter = math.abs(a.jitter - b.jitter) / 50
	local intensity = math.abs(a.intensity - b.intensity)
	local diag = a.diagnosis == b.diagnosis and 0 or 0.25
	return math.clamp(fps * 0.55 + jitter * 0.2 + intensity * 0.2 + diag * 0.05, 0, 1)
end

local function collectStableSamples(count)
	local samples = {}
	local deadline = os.clock() + math.max(count, 1) * CONFIG.SampleWindow * 1.5
	while #samples < count and os.clock() < deadline do
		task.wait(CONFIG.SampleWindow)
		local value = state.frameTimeMs
		if value > 0 and value < 500 then table.insert(samples, value) end
	end
	return samples
end

local function applyEntry(e, enabled)
	if not e.inst.Parent then return false end
	local ok = pcall(function() e.inst.Enabled = enabled end)
	if ok then e.disabledByUs = not enabled end
	return ok
end

local function startAction(batch, direction, label)
	if pendingAction or #batch == 0 then return false end
	local e = batch[1]
	if not e or not e.inst.Parent then return false end
	if e.experimentCount >= CONFIG.MaxExperimentsPerObject then return false end
	if os.clock() - e.lastTestAt < CONFIG.ExperimentCooldown then return false end

	local baselineSamples = collectStableSamples(CONFIG.BaselineSamples)
	local baseline = median(baselineSamples)
	if baseline <= 0 then return false end

	local oldValue
	if not pcall(function() oldValue = e.inst.Enabled end) then return false end
	if direction == "disable" and oldValue ~= true then return false end
	if direction == "enable" and not e.disabledByUs then return false end

	e.lastTestAt = os.clock()
	-- originalValue is captured once at registration so restore always returns
	-- the instance to the state it had before this script touched it.
	e.experimentCount += 1
	applyEntry(e, direction == "enable")

	pendingAction = {
		batch = {e},
		baseline = baseline,
		baselineSamples = baselineSamples,
		direction = direction,
		startClock = os.clock(),
		beforeContext = contextSignature(),
		label = label,
	}
	state.actionState = "settling"
	addLog(("%s %s — causal A/B test started (baseline %.2fms)"):format(
		direction == "disable" and "Testing OFF" or "Testing ON", e.Name, baseline))
	return true
end

local function updateLearnedImpact(e, measured, contextOK)
	local prior = e.impactEMA
	e.impactEMA = prior + CONFIG.LearnAlpha * (measured - prior)
	e.learnedImpact = e.impactEMA
	local deviation = math.abs(measured - e.impactEMA)
	e.impactVariance = e.impactVariance * 0.75 + deviation * 0.25
	if contextOK then
		e.sampleCount += 1
		e.contextFPS = state.smoothedFPS
		e.contextJitter = state.jitterMs
		local quality = math.clamp(1 - e.impactVariance /
			math.max(math.abs(e.impactEMA), CONFIG.NoiseFloorMs * 2), 0, 1)
		e.confidence = math.clamp(e.confidence + (quality - e.confidence) * CONFIG.ConfidenceAlpha, 0, 1)
	end
end

local function resolveAction()
	local action = pendingAction
	if not action then return end
	local e = action.batch[1]
	local afterSamples = collectStableSamples(CONFIG.SettleSamples)
	local after = median(afterSamples)
	local delta = action.direction == "disable"
		and (action.baseline - after)
		or (after - action.baseline)

	local contextOK = contextDistance(action.beforeContext, contextSignature()) <= CONFIG.ContextTolerance
	local meaningful = contextOK and delta >= math.max(CONFIG.MinImprovementMs, CONFIG.NoiseFloorMs * 1.5)
	updateLearnedImpact(e, delta, contextOK)

	if action.direction == "disable" then
		if meaningful then
			e.successCount += 1
			e.lastResult = ("useful +%.2fms"):format(delta)
			addLog(("KEPT OFF %s — +%.2fms, confidence %d%%"):format(
				e.Name, delta, math.floor(e.confidence * 100)))
		else
			e.failCount += 1
			e.lastResult = contextOK and "no measurable gain" or "discarded: context changed"
			if e.inst.Parent then pcall(function() e.inst.Enabled = e.originalValue end) end
			e.disabledByUs = false
			e.learnedImpact = math.max(0, e.learnedImpact - CONFIG.NoiseFloorMs)
			addLog(("REVERTED %s — %s (Δ%.2fms)"):format(e.Name, e.lastResult, delta))
		end
	else
		if meaningful then
			e.successCount += 1
			e.lastResult = ("restore cost +%.2fms"):format(delta)
			addLog(("RESTORE TEST %s — +%.2fms cost"):format(e.Name, delta))
		else
			e.failCount += 1
			e.lastResult = "restore had negligible cost"
			addLog(("RESTORE TEST %s — negligible cost"):format(e.Name))
		end
	end

	pendingAction = nil
	state.actionState = "idle"
end

local function runDecisionCycle()
	updateDiagnosis()
	local desiredCount = math.floor(#registry * state.intensity + 0.5)
	local currentDisabled = 0
	for _, e in ipairs(registry) do if e.disabledByUs then currentDisabled += 1 end end

	if desiredCount > currentDisabled then
		local candidates = collectCandidates(true)
		table.sort(candidates, function(a, b) return computeFinalRank(a) > computeFinalRank(b) end)
		for i = 1, #candidates do
			if startAction({candidates[i]}, "disable", "autonomous causal test") then break end
		end
	elseif desiredCount < currentDisabled then
		local candidates = collectCandidates(false)
		table.sort(candidates, function(a, b)
			return (a.learnedImpact * math.max(a.confidence, 0.25))
				< (b.learnedImpact * math.max(b.confidence, 0.25))
		end)
		for i = 1, #candidates do
			if startAction({candidates[i]}, "enable", "least-useful restore test") then break end
		end
	end
end

local function forceRestoreAll()
	if pendingAction and pendingAction.batch then
		for _, e in ipairs(pendingAction.batch) do
			if e.inst.Parent and e.originalValue ~= nil then
				pcall(function() e.inst.Enabled = e.originalValue end)
				e.disabledByUs = false
			end
		end
	end
	pendingAction = nil
	state.actionState = "idle"
	for _, e in ipairs(registry) do
		if e.disabledByUs and e.inst.Parent then
			pcall(function() e.inst.Enabled = e.originalValue end)
		end
		e.disabledByUs = false
	end
	if postEffectsDisabledByUs then
		for inst, wasEnabled in pairs(postEffects) do
			if inst.Parent then pcall(function() inst.Enabled = wasEnabled end) end
		end
		postEffectsDisabledByUs = false
	end
	if shadowsDisabledByUs then Lighting.GlobalShadows = originalGlobalShadows; shadowsDisabledByUs = false end
	if streamingReducedByUs then Workspace.StreamingTargetRadius = originalStreamingRadius; streamingReducedByUs = false end
	state.intensity = 0
end

-- Global, threshold-driven settings (not part of the learning loop — see header notes)
local function applyGlobalEffects(intensity)
	if intensity >= 0.5 and not postEffectsDisabledByUs then
		for inst in pairs(postEffects) do
			if inst.Parent then pcall(function() inst.Enabled = false end) end
		end
		postEffectsDisabledByUs = true
	elseif intensity < 0.5 and postEffectsDisabledByUs then
		for inst, wasEnabled in pairs(postEffects) do
			if inst.Parent then pcall(function() inst.Enabled = wasEnabled end) end
		end
		postEffectsDisabledByUs = false
	end

	if intensity >= 0.7 and not shadowsDisabledByUs then
		Lighting.GlobalShadows = false
		shadowsDisabledByUs = true
	elseif intensity < 0.7 and shadowsDisabledByUs then
		Lighting.GlobalShadows = originalGlobalShadows
		shadowsDisabledByUs = false
	end

	if intensity >= 0.6 then
		local t = (intensity - 0.6) / 0.4
		local target = originalStreamingRadius - t * (originalStreamingRadius - CONFIG.StreamingRadiusFloor)
		Workspace.StreamingTargetRadius = math.max(CONFIG.StreamingRadiusFloor, math.floor(target))
		streamingReducedByUs = true
	elseif streamingReducedByUs then
		Workspace.StreamingTargetRadius = originalStreamingRadius
		streamingReducedByUs = false
	end
end

--=============================================================
-- CONTROLLER (fast attack / slow decay) — decides overall pressure,
-- not which objects. Selection is the closed loop above.
--=============================================================
local function stepController(dt)
	if not state.autoOptimize then return end
	local target = state.targetFPS
	local fps = state.smoothedFPS
	if fps < target then
		local err = (target - fps) / target
		state.intensity = math.clamp(state.intensity + CONFIG.AttackRate * err * dt, 0, 1)
	elseif fps > target * CONFIG.RecoveryMargin then
		state.intensity = math.clamp(state.intensity - CONFIG.DecayRate * dt, 0, 1)
	end
end

--=============================================================
-- MONITORING + DECISION LOOP
--=============================================================
RunService.Heartbeat:Connect(function(dt)
	if dt <= 0 then return end
	local mean = pushFrameTime(dt)

	if dt > mean * CONFIG.SpikeMultiplier and dt > CONFIG.SpikeMinDelta then
		local now = os.clock()
		if now - state.lastSpikeAt > 1 then
			state.lastSpikeAt = now
			state.intensity = math.clamp(state.intensity + CONFIG.SpikeJump, 0, 1)
			for _, e in ipairs(collectCandidates(true)) do
				local aboveAvg = e.cost > 15 -- cheap proxy: only flag reasonably-costly enabled objects
				if aboveAvg then e.spikeAssociation += 1 end
			end
			addLog(("Spike detected (%.0fms frame)"):format(dt * 1000))
			if state.autoOptimize and state.actionState == "idle" then
				local candidates = collectCandidates(true)
				table.sort(candidates, function(a, b) return computeFinalRank(a) > computeFinalRank(b) end)
				if #candidates > 0 then
					startAction({candidates[1]}, "disable", "reflex spike response")
				end
			end
		end
	end

	state.fps = 1 / mean
	state.smoothedFPS = state.smoothedFPS * 0.9 + state.fps * 0.1
	stepController(dt)

	local band = state.intensity < 0.25 and "low" or state.intensity < 0.5 and "medium"
		or state.intensity < 0.75 and "high" or "extreme"
	state.session.timeInBand[band] += dt

	state.sampleTimer += dt
	state.resortTimer += dt
	state.spikeDecayTimer += dt
	state.decisionTimer += dt

	if state.sampleTimer >= CONFIG.SampleWindow then
		state.sampleTimer = 0
		local ok, item = pcall(function() return StatsService.Network.ServerStatsItem["Data Ping"]:GetValue() end)
		if ok and item then state.ping = item end

		pushHistory(state.history.fps, state.smoothedFPS)
		pushHistory(state.history.ping, state.ping)
		pushHistory(state.history.frametime, state.frameTimeMs)

		local s = state.session
		s.fpsMin = math.min(s.fpsMin, state.smoothedFPS)
		s.fpsMax = math.max(s.fpsMax, state.smoothedFPS)
		s.fpsSum += state.smoothedFPS; s.fpsCount += 1
		s.pingMin = math.min(s.pingMin, state.ping)
		s.pingMax = math.max(s.pingMax, state.ping)
		s.pingSum += state.ping; s.pingCount += 1

		if state.autoOptimize then applyGlobalEffects(state.intensity) end
	end

	if state.resortTimer >= 2 then
		state.resortTimer = 0
		resortRegistry()
	end

	if state.spikeDecayTimer >= CONFIG.SpikeDecayInterval then
		state.spikeDecayTimer = 0
		for _, e in ipairs(registry) do e.spikeAssociation *= CONFIG.SpikeDecayFactor end
	end

	if state.autoOptimize then
		if state.actionState == "idle" and state.decisionTimer >= CONFIG.DecisionInterval then
			state.decisionTimer = 0
			runDecisionCycle()
		elseif state.actionState == "settling" and pendingAction
			and os.clock() - pendingAction.startClock >= CONFIG.SettleTime then
			resolveAction()
		end
	end
end)

--=============================================================
-- HEALTH SCORE
--=============================================================
local function computeHealthScore()
	local fpsScore = math.clamp((state.smoothedFPS / state.targetFPS) * 100, 0, 100)
	local jitterScore = math.clamp(100 - state.jitterMs * 4, 0, 100)
	local pingScore
	if state.ping <= 50 then pingScore = 100
	elseif state.ping <= 100 then pingScore = 80
	elseif state.ping <= 150 then pingScore = 60
	elseif state.ping <= 250 then pingScore = 40
	else pingScore = 20 end
	return math.floor(fpsScore * 0.5 + jitterScore * 0.3 + pingScore * 0.2)
end

local function getTopInsights(n)
	local scored = {}
	for _, e in ipairs(registry) do
		if e.sampleCount > 0 and e.inst.Parent then table.insert(scored, e) end
	end
	table.sort(scored, function(a, b)
		return math.abs(a.learnedImpact) * math.max(a.confidence, 0.1)
			> math.abs(b.learnedImpact) * math.max(b.confidence, 0.1)
	end)
	if #scored == 0 then return "Still gathering causal evidence..." end
	local lines = {}
	for i = 1, math.min(n, #scored) do
		local e = scored[i]
		local parentName = e.inst.Parent and e.inst.Parent.Name or "?"
		if e.learnedImpact > 0.3 then
			table.insert(lines, ("%s (%s in %s): +%.1fms benefit • %d%% confidence • %d tests"):format(
				e.inst.Name, e.kind, parentName, e.learnedImpact,
				math.floor(e.confidence * 100), e.experimentCount))
		else
			table.insert(lines, ("%s (%s in %s): negligible • %d%% confidence • %d tests"):format(
				e.inst.Name, e.kind, parentName,
				math.floor(e.confidence * 100), e.experimentCount))
		end
	end
	return table.concat(lines, "\n")
end

--=============================================================
-- UI — premium responsive dashboard
--=============================================================
local existingGui = UIHost:FindFirstChild("AutonomousPerfGui")
if existingGui then existingGui:Destroy() end

local TweenService = game:GetService("TweenService")

local gui = Instance.new("ScreenGui")
gui.Name = "AutonomousPerfGui"
gui.ResetOnSpawn = false
gui.IgnoreGuiInset = true
gui.DisplayOrder = 999999
gui.ZIndexBehavior = Enum.ZIndexBehavior.Sibling
gui.Parent = UIHost
if bootGui and bootGui.Parent then bootGui:Destroy() end

local FONT = Enum.Font.Gotham
local FONT_BOLD = Enum.Font.GothamBold
local BG = Color3.fromRGB(10, 12, 17)
local CARD = Color3.fromRGB(17, 20, 28)
local CARD_2 = Color3.fromRGB(21, 24, 33)
local TEXT = Color3.fromRGB(245, 247, 250)
local MUTED = Color3.fromRGB(150, 158, 174)
local ACCENT = Color3.fromRGB(92, 190, 255)
local GOOD = Color3.fromRGB(83, 224, 145)
local WARN = Color3.fromRGB(255, 194, 82)
local BAD = Color3.fromRGB(255, 91, 105)

local function corner(obj, radius)
	local c = Instance.new("UICorner")
	c.CornerRadius = UDim.new(0, radius)
	c.Parent = obj
	return c
end

local function stroke(obj, color, thickness, transparency)
	local st = Instance.new("UIStroke")
	st.Color = color or Color3.new(1,1,1)
	st.Thickness = thickness or 1
	st.Transparency = transparency or 0
	st.Parent = obj
	return st
end

local function gradient(obj, a, b, rotation)
	local g = Instance.new("UIGradient")
	g.Color = ColorSequence.new(a, b)
	g.Rotation = rotation or 0
	g.Parent = obj
	return g
end

local function tween(obj, props, duration, style, direction)
	local info = TweenInfo.new(duration or 0.18, style or Enum.EasingStyle.Quint, direction or Enum.EasingDirection.Out)
	local tw = TweenService:Create(obj, info, props)
	tw:Play()
	return tw
end

-- A drag helper that distinguishes a real drag from a tap. This fixes the
-- common mobile bug where moving the floating control also activates it.
local function makeDraggable(handle, target, onTap)
	local dragging = false
	local moved = false
	local dragStart
	local startPos
	local pointerInput

	handle.InputBegan:Connect(function(input)
		if input.UserInputType ~= Enum.UserInputType.MouseButton1 and input.UserInputType ~= Enum.UserInputType.Touch then return end
		dragging = true
		moved = false
		dragStart = input.Position
		startPos = target.Position
		pointerInput = input
		input.Changed:Connect(function()
			if input.UserInputState == Enum.UserInputState.End then
				dragging = false
				if not moved and onTap then onTap() end
			end
		end)
	end)

	UserInputService.InputChanged:Connect(function(input)
		if not dragging then return end
		if input.UserInputType ~= Enum.UserInputType.MouseMovement and input.UserInputType ~= Enum.UserInputType.Touch then return end
		local delta = input.Position - dragStart
		if math.abs(delta.X) + math.abs(delta.Y) > 7 then moved = true end
		target.Position = UDim2.new(startPos.X.Scale, startPos.X.Offset + delta.X, startPos.Y.Scale, startPos.Y.Offset + delta.Y)
	end)
	return function() return moved end
end

--=============================================================
-- Floating control: compact, readable, thumb-friendly.
--=============================================================
local floatShadow = Instance.new("Frame")
floatShadow.Name = "FloatShadow"
floatShadow.Size = UDim2.fromOffset(142, 50)
floatShadow.AnchorPoint = Vector2.new(1, 0.5)
floatShadow.Position = UDim2.new(1, -14, 0.72, 4)
floatShadow.BackgroundColor3 = Color3.fromRGB(0,0,0)
floatShadow.BackgroundTransparency = 0.55
floatShadow.BorderSizePixel = 0
floatShadow.ZIndex = 1
floatShadow.Parent = gui
corner(floatShadow, 25)

local float = Instance.new("TextButton")
float.Name = "PerformancePill"
float.Size = UDim2.fromOffset(142, 50)
float.AnchorPoint = Vector2.new(1, 0.5)
float.Position = UDim2.new(1, -14, 0.72, 0)
float.BackgroundColor3 = BG
float.AutoButtonColor = false
float.Text = ""
float.ZIndex = 5
float.Parent = gui
corner(float, 25)
local floatStroke = stroke(float, ACCENT, 1.5, 0.15)
gradient(float, Color3.fromRGB(19, 25, 36), Color3.fromRGB(10, 12, 17), 15)

local floatAccent = Instance.new("Frame")
floatAccent.Size = UDim2.fromOffset(4, 28)
floatAccent.Position = UDim2.fromOffset(9, 11)
floatAccent.BorderSizePixel = 0
floatAccent.BackgroundColor3 = GOOD
floatAccent.ZIndex = 7
floatAccent.Parent = float
corner(floatAccent, 3)

local floatMark = Instance.new("TextLabel")
floatMark.BackgroundTransparency = 1
floatMark.Position = UDim2.fromOffset(19, 5)
floatMark.Size = UDim2.fromOffset(30, 17)
floatMark.Font = FONT_BOLD
floatMark.Text = "APE"
floatMark.TextSize = 10
floatMark.TextColor3 = MUTED
floatMark.TextXAlignment = Enum.TextXAlignment.Left
floatMark.ZIndex = 7
floatMark.Parent = float

local iconLabel = Instance.new("TextLabel")
iconLabel.BackgroundTransparency = 1
iconLabel.Position = UDim2.fromOffset(18, 20)
iconLabel.Size = UDim2.fromOffset(67, 23)
iconLabel.Font = FONT_BOLD
iconLabel.Text = "-- FPS"
iconLabel.TextSize = 17
iconLabel.TextColor3 = TEXT
iconLabel.TextXAlignment = Enum.TextXAlignment.Left
iconLabel.ZIndex = 7
iconLabel.Parent = float

local floatStatus = Instance.new("TextLabel")
floatStatus.BackgroundTransparency = 1
floatStatus.AnchorPoint = Vector2.new(1, 0.5)
floatStatus.Position = UDim2.new(1, -14, 0.5, 0)
floatStatus.Size = UDim2.fromOffset(43, 24)
floatStatus.Font = FONT_BOLD
floatStatus.Text = "READY"
floatStatus.TextSize = 8
floatStatus.TextColor3 = GOOD
floatStatus.TextXAlignment = Enum.TextXAlignment.Right
floatStatus.ZIndex = 7
floatStatus.Parent = float

--=============================================================
-- Dashboard shell
--=============================================================
local panel = Instance.new("Frame")
panel.Name = "Dashboard"
panel.AnchorPoint = Vector2.new(1, 0.5)
panel.Position = UDim2.new(1, -18, 0.5, 0)
panel.Size = UDim2.fromOffset(372, 560)
panel.BackgroundColor3 = BG
panel.Visible = false
panel.ClipsDescendants = true
panel.ZIndex = 20
panel.Parent = gui
corner(panel, 18)
local panelStroke = stroke(panel, Color3.fromRGB(70, 105, 145), 1.2, 0.25)
gradient(panel, Color3.fromRGB(12, 16, 24), Color3.fromRGB(8, 10, 15), 90)
local panelScale = Instance.new("UIScale")
panelScale.Scale = 1
panelScale.Parent = panel

local topGlow = Instance.new("Frame")
topGlow.Size = UDim2.new(1, -32, 0, 2)
topGlow.Position = UDim2.fromOffset(16, 0)
topGlow.BorderSizePixel = 0
topGlow.BackgroundColor3 = ACCENT
topGlow.ZIndex = 21
topGlow.Parent = panel
corner(topGlow, 2)

local header = Instance.new("Frame")
header.Size = UDim2.new(1, 0, 0, 64)
header.BackgroundTransparency = 1
header.ZIndex = 22
header.Parent = panel

local headerGrip = Instance.new("Frame")
headerGrip.Position = UDim2.fromOffset(16, 17)
headerGrip.Size = UDim2.fromOffset(4, 30)
headerGrip.BackgroundColor3 = ACCENT
headerGrip.BorderSizePixel = 0
headerGrip.ZIndex = 23
headerGrip.Parent = header
corner(headerGrip, 2)

local title = Instance.new("TextLabel")
title.BackgroundTransparency = 1
title.Position = UDim2.fromOffset(28, 10)
title.Size = UDim2.new(1, -112, 0, 24)
title.Font = FONT_BOLD
title.TextColor3 = TEXT
title.TextXAlignment = Enum.TextXAlignment.Left
title.TextSize = 17
title.Text = "Performance Engine"
title.ZIndex = 23
title.Parent = header

local subtitle = Instance.new("TextLabel")
subtitle.BackgroundTransparency = 1
subtitle.Position = UDim2.fromOffset(28, 33)
subtitle.Size = UDim2.new(1, -112, 0, 17)
subtitle.Font = FONT
subtitle.TextColor3 = MUTED
subtitle.TextXAlignment = Enum.TextXAlignment.Left
subtitle.TextSize = 10
subtitle.Text = "Adaptive • causal • client-side"
subtitle.ZIndex = 23
subtitle.Parent = header

local compactBtn = Instance.new("TextButton")
compactBtn.Size = UDim2.fromOffset(34, 34)
compactBtn.Position = UDim2.new(1, -82, 0.5, -17)
compactBtn.BackgroundColor3 = CARD_2
compactBtn.AutoButtonColor = false
compactBtn.Text = "—"
compactBtn.TextColor3 = TEXT
compactBtn.Font = FONT_BOLD
compactBtn.TextSize = 16
compactBtn.ZIndex = 24
compactBtn.Parent = header
corner(compactBtn, 10)
stroke(compactBtn, Color3.fromRGB(60,70,88), 1, 0.35)

local closeBtn = Instance.new("TextButton")
closeBtn.Size = UDim2.fromOffset(34, 34)
closeBtn.Position = UDim2.new(1, -42, 0.5, -17)
closeBtn.BackgroundColor3 = CARD_2
closeBtn.AutoButtonColor = false
closeBtn.Text = "×"
closeBtn.TextColor3 = TEXT
closeBtn.Font = FONT
closeBtn.TextSize = 22
closeBtn.ZIndex = 24
closeBtn.Parent = header
corner(closeBtn, 10)
stroke(closeBtn, Color3.fromRGB(60,70,88), 1, 0.35)

local body = Instance.new("ScrollingFrame")
body.Position = UDim2.fromOffset(0, 64)
body.Size = UDim2.new(1, 0, 1, -64)
body.BackgroundTransparency = 1
body.BorderSizePixel = 0
body.ScrollBarThickness = 3
body.ScrollBarImageTransparency = 0.35
body.CanvasSize = UDim2.new(0, 0, 0, 0)
body.AutomaticCanvasSize = Enum.AutomaticSize.Y
body.ScrollingDirection = Enum.ScrollingDirection.Y
body.ZIndex = 22
body.Parent = panel

local layout = Instance.new("UIListLayout")
layout.Padding = UDim.new(0, 8)
layout.SortOrder = Enum.SortOrder.LayoutOrder
layout.Parent = body

local padding = Instance.new("UIPadding")
padding.PaddingLeft = UDim.new(0, 14)
padding.PaddingRight = UDim.new(0, 14)
padding.PaddingTop = UDim.new(0, 6)
padding.PaddingBottom = UDim.new(0, 14)
padding.Parent = body

local order = 0
local function nextOrder() order += 1 return order end

local function sectionLabel(text)
	local l = Instance.new("TextLabel")
	l.BackgroundTransparency = 1
	l.Size = UDim2.new(1, 0, 0, 15)
	l.Font = FONT_BOLD
	l.TextColor3 = MUTED
	l.TextXAlignment = Enum.TextXAlignment.Left
	l.TextSize = 9
	l.Text = text
	l.LayoutOrder = nextOrder()
	l.Parent = body
	return l
end

local function statLabel(defaultText)
	local l = Instance.new("TextLabel")
	l.BackgroundTransparency = 1
	l.Size = UDim2.new(1, 0, 0, 18)
	l.Font = FONT
	l.TextColor3 = TEXT
	l.TextXAlignment = Enum.TextXAlignment.Left
	l.TextSize = 11
	l.Text = defaultText
	l.LayoutOrder = nextOrder()
	l.Parent = body
	return l
end

local function card(parent, size, layoutOrder)
	local f = Instance.new("Frame")
	f.Size = size
	f.BackgroundColor3 = CARD
	f.BorderSizePixel = 0
	f.LayoutOrder = layoutOrder or 1
	f.Parent = parent
	corner(f, 12)
	stroke(f, Color3.fromRGB(52, 62, 80), 1, 0.55)
	return f
end

sectionLabel("LIVE")
local liveCard = card(body, UDim2.new(1, 0, 0, 108), nextOrder())

local function makeMetric(parent, x, y, w, labelText, valueText)
	local wrap = Instance.new("Frame")
	wrap.BackgroundTransparency = 1
	wrap.Position = UDim2.new(x, 0, y, 0)
	wrap.Size = UDim2.new(w, 0, 0, 44)
	wrap.Parent = parent
	local small = Instance.new("TextLabel")
	small.BackgroundTransparency = 1
	small.Size = UDim2.new(1, 0, 0, 14)
	small.Font = FONT_BOLD
	small.TextSize = 8
	small.TextColor3 = MUTED
	small.TextXAlignment = Enum.TextXAlignment.Left
	small.Text = labelText
	small.Parent = wrap
	local val = Instance.new("TextLabel")
	val.BackgroundTransparency = 1
	val.Position = UDim2.fromOffset(0, 13)
	val.Size = UDim2.new(1, 0, 0, 27)
	val.Font = FONT_BOLD
	val.TextSize = 15
	val.TextColor3 = TEXT
	val.TextXAlignment = Enum.TextXAlignment.Left
	val.Text = valueText
	val.Parent = wrap
	return val
end

local fpsLabel = makeMetric(liveCard, 0.05, 0.08, 0.44, "FPS", "--")
local healthLabel = makeMetric(liveCard, 0.51, 0.08, 0.44, "HEALTH", "--/100")
local pingLabel = makeMetric(liveCard, 0.05, 0.52, 0.44, "PING", "-- ms")
local jitterLabel = makeMetric(liveCard, 0.51, 0.52, 0.44, "JITTER", "-- ms")

local intensityLabel = statLabel("Intensity: 0%")
local appliedLabel = statLabel("Applied: 0/0 objects")
local diagnosisLabel = statLabel("Diagnosis: stable")
local experimentLabel = statLabel("Experiment: idle")

sectionLabel("FPS HISTORY")
local chart = card(body, UDim2.new(1, 0, 0, 66), nextOrder())
local BAR_COUNT = CONFIG.HistoryLength
local bars = {}
for i = 1, BAR_COUNT do
	local bar = Instance.new("Frame")
	bar.AnchorPoint = Vector2.new(0, 1)
	bar.Position = UDim2.new((i - 1) / BAR_COUNT, 0, 1, -7)
	bar.Size = UDim2.new(1 / BAR_COUNT, -1, 0, 2)
	bar.BorderSizePixel = 0
	bar.BackgroundColor3 = ACCENT
	bar.Parent = chart
	bars[i] = bar
end

local targetLine = Instance.new("Frame")
targetLine.Size = UDim2.new(1, -12, 0, 1)
targetLine.Position = UDim2.new(0, 6, 0.5, 0)
targetLine.BackgroundColor3 = Color3.fromRGB(95,105,125)
targetLine.BackgroundTransparency = 0.65
targetLine.BorderSizePixel = 0
targetLine.Parent = chart

sectionLabel("TARGET")
local targetRow = card(body, UDim2.new(1, 0, 0, 46), nextOrder())
local minusBtn = Instance.new("TextButton")
minusBtn.Size = UDim2.fromOffset(34, 34)
minusBtn.Position = UDim2.fromOffset(7, 6)
minusBtn.BackgroundColor3 = CARD_2
minusBtn.AutoButtonColor = false
minusBtn.Text = "−"
minusBtn.TextColor3 = TEXT
minusBtn.Font = FONT_BOLD
minusBtn.TextSize = 18
minusBtn.Parent = targetRow
corner(minusBtn, 9)

local targetLabel = Instance.new("TextLabel")
targetLabel.Position = UDim2.fromOffset(48, 0)
targetLabel.Size = UDim2.new(1, -96, 1, 0)
targetLabel.BackgroundTransparency = 1
targetLabel.Font = FONT_BOLD
targetLabel.TextColor3 = TEXT
targetLabel.TextSize = 14
targetLabel.Text = tostring(state.targetFPS) .. " FPS"
targetLabel.Parent = targetRow

local autoBtn = Instance.new("TextButton")
autoBtn.Size = UDim2.fromOffset(34, 34)
autoBtn.Position = UDim2.new(1, -41, 0, 6)
autoBtn.BackgroundColor3 = CARD_2
autoBtn.AutoButtonColor = false
autoBtn.Text = "+"
autoBtn.TextColor3 = TEXT
autoBtn.Font = FONT_BOLD
autoBtn.TextSize = 18
autoBtn.Parent = targetRow
corner(autoBtn, 9)

minusBtn.MouseButton1Click:Connect(function()
	state.targetFPS = math.max(CONFIG.MinTargetFPS, state.targetFPS - 5)
	targetLabel.Text = state.targetFPS .. " FPS"
end)
autoBtn.MouseButton1Click:Connect(function()
	state.targetFPS = math.min(CONFIG.MaxTargetFPS, state.targetFPS + 5)
	targetLabel.Text = state.targetFPS .. " FPS"
end)

sectionLabel("CONTROL")
local optimizeRow = card(body, UDim2.new(1, 0, 0, 50), nextOrder())
local optimizeTitle = Instance.new("TextLabel")
optimizeTitle.BackgroundTransparency = 1
optimizeTitle.Position = UDim2.fromOffset(12, 7)
optimizeTitle.Size = UDim2.new(1, -86, 0, 18)
optimizeTitle.Font = FONT_BOLD
optimizeTitle.TextSize = 11
optimizeTitle.TextColor3 = TEXT
optimizeTitle.TextXAlignment = Enum.TextXAlignment.Left
optimizeTitle.Text = "Automatic optimization"
optimizeTitle.Parent = optimizeRow
local optimizeSub = Instance.new("TextLabel")
optimizeSub.BackgroundTransparency = 1
optimizeSub.Position = UDim2.fromOffset(12, 25)
optimizeSub.Size = UDim2.new(1, -86, 0, 14)
optimizeSub.Font = FONT
optimizeSub.TextSize = 8
optimizeSub.TextColor3 = MUTED
optimizeSub.TextXAlignment = Enum.TextXAlignment.Left
optimizeSub.Text = "Closed-loop performance control"
optimizeSub.Parent = optimizeRow

autoBtn = Instance.new("TextButton")
autoBtn.Size = UDim2.fromOffset(60, 30)
autoBtn.Position = UDim2.new(1, -69, 0.5, -15)
autoBtn.AutoButtonColor = false
autoBtn.Font = FONT_BOLD
autoBtn.TextSize = 9
autoBtn.TextColor3 = TEXT
autoBtn.Parent = optimizeRow
corner(autoBtn, 15)

local function refreshAutoButton()
	if state.autoOptimize then
		autoBtn.Text = "ON"
		autoBtn.BackgroundColor3 = GOOD
		gradient(autoBtn, Color3.fromRGB(56, 190, 120), Color3.fromRGB(84, 224, 145), 0)
	else
		autoBtn.Text = "OFF"
		autoBtn.BackgroundColor3 = Color3.fromRGB(75, 82, 95)
		local g = autoBtn:FindFirstChildOfClass("UIGradient")
		if g then g:Destroy() end
	end
end
refreshAutoButton()
autoBtn.MouseButton1Click:Connect(function()
	state.autoOptimize = not state.autoOptimize
	refreshAutoButton()
	if not state.autoOptimize then forceRestoreAll() end
end)

sectionLabel("SESSION")
local sessionCard = card(body, UDim2.new(1, 0, 0, 76), nextOrder())
local sessionLabel1 = makeMetric(sessionCard, 0.05, 0.07, 0.44, "FPS MIN / AVG / MAX", "-- / -- / --")
local sessionLabel2 = makeMetric(sessionCard, 0.51, 0.07, 0.44, "PING MIN / AVG / MAX", "-- / -- / --")
local sessionLabel3 = Instance.new("TextLabel")
sessionLabel3.BackgroundTransparency = 1
sessionLabel3.Position = UDim2.fromOffset(12, 48)
sessionLabel3.Size = UDim2.new(0.45, 0, 0, 17)
sessionLabel3.Font = FONT
sessionLabel3.TextSize = 9
sessionLabel3.TextColor3 = MUTED
sessionLabel3.TextXAlignment = Enum.TextXAlignment.Left
sessionLabel3.Text = "Events: 0"
sessionLabel3.Parent = sessionCard
local sessionLabel4 = Instance.new("TextLabel")
sessionLabel4.BackgroundTransparency = 1
sessionLabel4.Position = UDim2.new(0.51, 0, 0, 48)
sessionLabel4.Size = UDim2.new(0.44, 0, 0, 17)
sessionLabel4.Font = FONT
sessionLabel4.TextSize = 8
sessionLabel4.TextColor3 = MUTED
sessionLabel4.TextXAlignment = Enum.TextXAlignment.Left
sessionLabel4.Text = "Bands: --"
sessionLabel4.Parent = sessionCard

sectionLabel("LEARNED INSIGHTS")
local insightsCard = card(body, UDim2.new(1, 0, 0, 92), nextOrder())
local insightsLabel = Instance.new("TextLabel")
insightsLabel.BackgroundTransparency = 1
insightsLabel.Position = UDim2.fromOffset(10, 8)
insightsLabel.Size = UDim2.new(1, -20, 1, -16)
insightsLabel.Font = Enum.Font.Code
insightsLabel.TextColor3 = Color3.fromRGB(180, 255, 200)
insightsLabel.TextXAlignment = Enum.TextXAlignment.Left
insightsLabel.TextYAlignment = Enum.TextYAlignment.Top
insightsLabel.TextWrapped = true
insightsLabel.TextSize = 9
insightsLabel.Text = "Gathering causal evidence..."
insightsLabel.Parent = insightsCard

sectionLabel("ACTIVITY")
local logFrame = card(body, UDim2.new(1, 0, 0, 86), nextOrder())
local logLabel = Instance.new("TextLabel")
logLabel.BackgroundTransparency = 1
logLabel.Position = UDim2.fromOffset(10, 8)
logLabel.Size = UDim2.new(1, -20, 1, -16)
logLabel.Font = Enum.Font.Code
logLabel.TextColor3 = Color3.fromRGB(158, 188, 220)
logLabel.TextXAlignment = Enum.TextXAlignment.Left
logLabel.TextYAlignment = Enum.TextYAlignment.Top
logLabel.TextWrapped = true
logLabel.TextSize = 8
logLabel.Text = "Engine started."
logLabel.Parent = logFrame

local panelSize = UDim2.fromOffset(372, 560)

local function setPanelOpen(open)
	state.panelOpen = open
	if open then
		panel.Visible = true
		panel.BackgroundTransparency = 0.08
		panelScale.Scale = 0.965
		tween(panelScale, {Scale = 1}, 0.22, Enum.EasingStyle.Back)
		tween(panel, {BackgroundTransparency = 0}, 0.18)
	else
		tween(panelScale, {Scale = 0.965}, 0.14, Enum.EasingStyle.Quad, Enum.EasingDirection.In)
		local tw = tween(panel, {BackgroundTransparency = 0.08}, 0.14, Enum.EasingStyle.Quad, Enum.EasingDirection.In)
		tw.Completed:Connect(function()
			if not state.panelOpen then panel.Visible = false end
		end)
	end
end

makeDraggable(float, float, function() setPanelOpen(not state.panelOpen) end)
makeDraggable(title, panel, nil)
makeDraggable(subtitle, panel, nil)

closeBtn.MouseButton1Click:Connect(function() setPanelOpen(false) end)
compactBtn.MouseButton1Click:Connect(function()
	state.compact = not state.compact
	body.Visible = not state.compact
	compactBtn.Text = state.compact and "+" or "—"
	panel.Size = state.compact and UDim2.fromOffset(panel.AbsoluteSize.X, 64) or panelSize
end)

local function layoutResponsive()
	local camera = Workspace.CurrentCamera
	if not camera then return end
	local viewport = camera.ViewportSize
	local mobile = UserInputService.TouchEnabled and viewport.X < 700
	if mobile then
		local w = math.max(240, math.min(viewport.X - 16, 430))
		local h = math.max(360, math.min(viewport.Y - 20, 610))
		panelSize = UDim2.fromOffset(w, h)
		if not state.compact then panel.Size = panelSize end
		panel.AnchorPoint = Vector2.new(0.5, 0.5)
		panel.Position = UDim2.new(0.5, 0, 0.5, 0)
		float.Size = UDim2.fromOffset(126, 44)
		floatShadow.Size = UDim2.fromOffset(126, 44)
		float.Position = UDim2.new(1, -10, 1, -18)
		floatShadow.Position = UDim2.new(1, -10, 1, -14)
		floatAccent.Position = UDim2.fromOffset(8, 9)
		floatAccent.Size = UDim2.fromOffset(4, 26)
		floatMark.Position = UDim2.fromOffset(17, 4)
		iconLabel.Position = UDim2.fromOffset(17, 18)
		iconLabel.Size = UDim2.fromOffset(63, 21)
		floatStatus.Position = UDim2.new(1, -10, 0.5, 0)
		floatStatus.Size = UDim2.fromOffset(36, 22)
	else
		panelSize = UDim2.fromOffset(372, 560)
		if not state.compact then panel.Size = panelSize end
		panel.AnchorPoint = Vector2.new(1, 0.5)
		panel.Position = UDim2.new(1, -18, 0.5, 0)
		float.Size = UDim2.fromOffset(142, 50)
		floatShadow.Size = UDim2.fromOffset(142, 50)
		float.Position = UDim2.new(1, -14, 0.72, 0)
		floatShadow.Position = UDim2.new(1, -14, 0.72, 4)
		floatAccent.Position = UDim2.fromOffset(9, 11)
		floatAccent.Size = UDim2.fromOffset(4, 28)
		floatMark.Position = UDim2.fromOffset(19, 5)
		iconLabel.Position = UDim2.fromOffset(18, 20)
		iconLabel.Size = UDim2.fromOffset(67, 23)
		floatStatus.Position = UDim2.new(1, -14, 0.5, 0)
		floatStatus.Size = UDim2.fromOffset(43, 24)
	end
end

layoutResponsive()
local camera = Workspace.CurrentCamera
if camera then camera:GetPropertyChangedSignal("ViewportSize"):Connect(layoutResponsive) end
Workspace:GetPropertyChangedSignal("CurrentCamera"):Connect(function()
	if Workspace.CurrentCamera then Workspace.CurrentCamera:GetPropertyChangedSignal("ViewportSize"):Connect(layoutResponsive) end
	layoutResponsive()
end)

-- Small press feedback makes the floating control feel native instead of like
-- an old-school draggable executor button.
float.MouseEnter:Connect(function() tween(floatStroke, {Transparency = 0}, 0.12) end)
float.MouseLeave:Connect(function() tween(floatStroke, {Transparency = 0.15}, 0.18) end)

--=============================================================
-- UI REFRESH LOOP (display only — never touches game objects)
--=============================================================
task.spawn(function()
	local tick = 0
	while gui.Parent do
		tick += 1
		local health = computeHealthScore()

		iconLabel.Text = tostring(math.floor(state.smoothedFPS)) .. " FPS"
		local healthColor = health >= 75 and Color3.fromRGB(80, 220, 130)
			or health >= 45 and Color3.fromRGB(255, 200, 80)
			or Color3.fromRGB(255, 90, 90)
		floatAccent.BackgroundColor3 = healthColor
		floatStroke.Color = healthColor
		floatStatus.Text = state.autoOptimize and "AUTO" or "PAUSED"
		floatStatus.TextColor3 = healthColor
		floatShadow.Position = UDim2.new(float.Position.X.Scale, float.Position.X.Offset, float.Position.Y.Scale, float.Position.Y.Offset + 4)

		fpsLabel.Text = ("%d  /  %d target"):format(math.floor(state.smoothedFPS), state.targetFPS)
		pingLabel.Text = ("%d ms"):format(math.floor(state.ping))
		jitterLabel.Text = ("%.1f ms"):format(state.jitterMs)
		healthLabel.Text = ("%d / 100"):format(health)
		healthLabel.TextColor3 = healthColor
		intensityLabel.Text = ("Intensity: %d%%"):format(math.floor(state.intensity * 100))
		diagnosisLabel.Text = "Diagnosis: " .. state.diagnosis
		experimentLabel.Text = pendingAction and ("Experiment: " .. (pendingAction.label or "settling")) or "Experiment: idle"

		local disabledCount = 0
		for _, e in ipairs(registry) do if e.disabledByUs then disabledCount += 1 end end
		appliedLabel.Text = ("Applied: %d/%d objects disabled"):format(disabledCount, #registry)

		local hist = state.history.fps
		local maxVal = math.max(30, state.targetFPS * 1.2)
		for i = 1, BAR_COUNT do
			local histIndex = i - (BAR_COUNT - #hist)
			local v = histIndex >= 1 and hist[histIndex] or 0
			local h = math.clamp(v / maxVal, 0.02, 1)
			bars[i].Size = UDim2.new(1 / BAR_COUNT, -1, h, 0)
			bars[i].BackgroundColor3 = v >= state.targetFPS and GOOD
				or v >= state.targetFPS * 0.7 and WARN
				or BAD
		end

		local s = state.session
		local elapsed = os.clock() - s.startClock
		sessionLabel1.Text = ("FPS  min/avg/max: %d / %d / %d"):format(
			s.fpsMin == math.huge and 0 or s.fpsMin, s.fpsCount > 0 and (s.fpsSum / s.fpsCount) or 0, s.fpsMax)
		sessionLabel2.Text = ("Ping min/avg/max: %d / %d / %d"):format(
			s.pingMin == math.huge and 0 or s.pingMin, s.pingCount > 0 and (s.pingSum / s.pingCount) or 0, s.pingMax)
		sessionLabel3.Text = ("Optimization events: %d  (session: %ds)"):format(s.optimizationEvents, math.floor(elapsed))
		sessionLabel4.Text = ("Bands — low %ds / med %ds / high %ds / extreme %ds"):format(
			math.floor(s.timeInBand.low), math.floor(s.timeInBand.medium), math.floor(s.timeInBand.high), math.floor(s.timeInBand.extreme))

		if tick % 10 == 0 then
			insightsLabel.Text = getTopInsights(5)
		end

		if #state.log > 0 then logLabel.Text = table.concat(state.log, "\n") end

		task.wait(0.1)
	end
end)

addLog("Autonomous v4 started — causal experiments enabled (target " .. state.targetFPS .. " FPS)")
