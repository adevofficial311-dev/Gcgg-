local Players = game:GetService("Players")
local RunService = game:GetService("RunService")
local UserInputService = game:GetService("UserInputService")
local Lighting = game:GetService("Lighting")
local StatsService = game:GetService("Stats")
local Workspace = game:GetService("Workspace")
local TweenService = game:GetService("TweenService")

local player = Players.LocalPlayer
if not player then
	error("Script Is Not Available Right Now. Run after the game has loaded.")
end

local playerGui = player:WaitForChild("PlayerGui", 15)
if not playerGui then
	error("Script: PlayerGui was not available.")
end


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
bootGui.Name = "Autonomous Performance Engine"
bootGui.ResetOnSpawn = false
bootGui.IgnoreGuiInset = true
bootGui.DisplayOrder = 1000000
bootGui.Parent = UIHost
local bootLabel = Instance.new("TextLabel")
bootLabel.AnchorPoint = Vector2.new(1, 0.5)
bootLabel.Position = UDim2.new(1, -18, 0.5, 0)
bootLabel.Size = UDim2.fromOffset(230, 42)
bootLabel.BackgroundColor3 = Color3.fromRGB(14, 15, 20)
bootLabel.BackgroundTransparency = 0.05
bootLabel.TextColor3 = Color3.fromRGB(255, 255, 255)
bootLabel.Font = Enum.Font.GothamBold
bootLabel.TextSize = 14
bootLabel.Text = "APE — Initializing..."
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

	
	DecisionInterval = 2,      -- seconds between normal decision ticks
	SettleTime = 1.5,          -- seconds to wait before measuring an action's effect
	MaxBatch = 5,              -- max objects touched per action (keeps attribution clean)
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

-- Log entries are tagged so the Log tab can color them without re-parsing
-- English text. tag one of: "good" | "bad" | "warn" | "info"
local function addLog(msg, tag)
	table.insert(state.log, 1, {
		text = ("[%s] %s"):format(os.date("%H:%M:%S"), msg),
		tag = tag or "info",
	})
	if #state.log > 40 then table.remove(state.log) end
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

-- entry.inst can, in edge cases, already be in a half-destroyed state by the
-- time we log about it. Never let a cosmetic log line throw.
local function entryName(e)
	if not e or not e.inst then return "object" end
	local ok, name = pcall(function() return e.inst.Name end)
	return (ok and name) or e.kind or "object"
end

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
		addLog(text, "info")
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

-- Forward-declared so startAction/resolveAction can notify the UI without
-- the UI section needing to exist yet at this point in the file.
local onEngineEvent = function(_kind, _e, _extra) end

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
		direction == "disable" and "Testing OFF" or "Testing ON", entryName(e), baseline), "info")
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
				entryName(e), delta, math.floor(e.confidence * 100)), "good")
			state.session.optimizationEvents += 1
			onEngineEvent("kept", e, delta)
		else
			e.failCount += 1
			e.lastResult = contextOK and "no measurable gain" or "discarded: context changed"
			if e.inst.Parent then pcall(function() e.inst.Enabled = e.originalValue end) end
			e.disabledByUs = false
			e.learnedImpact = math.max(0, e.learnedImpact - CONFIG.NoiseFloorMs)
			addLog(("REVERTED %s — %s (Δ%.2fms)"):format(entryName(e), e.lastResult, delta), "bad")
			onEngineEvent("reverted", e, delta)
		end
	else
		if meaningful then
			e.successCount += 1
			e.lastResult = ("restore cost +%.2fms"):format(delta)
			addLog(("RESTORE TEST %s — +%.2fms cost"):format(entryName(e), delta), "warn")
		else
			e.failCount += 1
			e.lastResult = "restore had negligible cost"
			addLog(("RESTORE TEST %s — negligible cost"):format(entryName(e)), "info")
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
			addLog(("Spike detected (%.0fms frame)"):format(dt * 1000), "warn")
			onEngineEvent("spike", nil, dt * 1000)
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

-- Structured insight data for the redesigned Insights tab (rows with a real
-- confidence bar), plus a plain-text fallback kept for compact mode.
local function getTopInsightsData(n)
	local scored = {}
	for _, e in ipairs(registry) do
		if e.sampleCount > 0 and e.inst.Parent then table.insert(scored, e) end
	end
	table.sort(scored, function(a, b)
		return math.abs(a.learnedImpact) * math.max(a.confidence, 0.1)
			> math.abs(b.learnedImpact) * math.max(b.confidence, 0.1)
	end)
	local out = {}
	for i = 1, math.min(n, #scored) do
		local e = scored[i]
		local parentName = e.inst.Parent and e.inst.Parent.Name or "?"
		table.insert(out, {
			title = ("%s (%s)"):format(entryName(e), e.kind),
			subtitle = "in " .. parentName,
			impactText = e.learnedImpact > 0.3 and ("+%.1fms"):format(e.learnedImpact) or "negligible",
			positive = e.learnedImpact > 0.3,
			confidence = e.confidence,
			tests = e.experimentCount,
		})
	end
	return out
end

--=============================================================
-- UI — redesigned tabbed dashboard
--=============================================================
local existingGui = UIHost:FindFirstChild("AutonomousPerfGui")
if existingGui then existingGui:Destroy() end

local gui = Instance.new("ScreenGui")
gui.Name = "AutonomousPerfGui"
gui.ResetOnSpawn = false
gui.IgnoreGuiInset = true
gui.DisplayOrder = 999999
gui.ZIndexBehavior = Enum.ZIndexBehavior.Sibling
gui.Parent = UIHost
if bootGui and bootGui.Parent then bootGui:Destroy() end

-- Palette -------------------------------------------------------------
local BG = Color3.fromRGB(9, 10, 14)
local CARD = Color3.fromRGB(18, 20, 27)
local CARD_2 = Color3.fromRGB(24, 27, 36)
local STROKE_C = Color3.fromRGB(54, 60, 76)
local TEXT = Color3.fromRGB(247, 248, 251)
local MUTED = Color3.fromRGB(148, 156, 173)
local FAINT = Color3.fromRGB(92, 99, 114)
local ACCENT = Color3.fromRGB(110, 142, 255)
local ACCENT_2 = Color3.fromRGB(163, 118, 255)
local GOOD = Color3.fromRGB(78, 224, 154)
local WARN = Color3.fromRGB(255, 197, 84)
local BAD = Color3.fromRGB(255, 94, 112)

local FONT = Enum.Font.Gotham
local FONT_MED = Enum.Font.GothamMedium
local FONT_BOLD = Enum.Font.GothamBold
local FONT_BLACK = Enum.Font.GothamBlack
local FONT_MONO = Enum.Font.Code

--=============================================================
-- Small helpers
--=============================================================
local function corner(obj, radius)
	local c = Instance.new("UICorner")
	c.CornerRadius = UDim.new(0, radius)
	c.Parent = obj
	return c
end

local function stroke(obj, color, thickness, transparency)
	local st = Instance.new("UIStroke")
	st.Color = color or Color3.new(1, 1, 1)
	st.Thickness = thickness or 1
	st.Transparency = transparency or 0
	st.ApplyStrokeMode = Enum.ApplyStrokeMode.Border
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

local function pad(obj, l, r, t, b)
	local p = Instance.new("UIPadding")
	p.PaddingLeft = UDim.new(0, l or 0)
	p.PaddingRight = UDim.new(0, r or l or 0)
	p.PaddingTop = UDim.new(0, t or l or 0)
	p.PaddingBottom = UDim.new(0, b or t or l or 0)
	p.Parent = obj
	return p
end

local function tween(obj, props, duration, style, direction)
	local info = TweenInfo.new(duration or 0.18, style or Enum.EasingStyle.Quint, direction or Enum.EasingDirection.Out)
	local tw = TweenService:Create(obj, info, props)
	tw:Play()
	return tw
end

local function label(parent, props)
	local l = Instance.new("TextLabel")
	l.BackgroundTransparency = 1
	l.Font = props.font or FONT
	l.TextSize = props.size or 12
	l.TextColor3 = props.color or TEXT
	l.TextXAlignment = props.align or Enum.TextXAlignment.Left
	l.TextYAlignment = props.valign or Enum.TextYAlignment.Center
	l.Text = props.text or ""
	l.Size = props.uiSize or UDim2.new(1, 0, 0, props.height or 16)
	l.Position = props.position or UDim2.new(0, 0, 0, 0)
	l.TextTruncate = props.truncate or Enum.TextTruncate.AtEnd
	l.TextWrapped = props.wrap or false
	l.LayoutOrder = props.order or 0
	l.ZIndex = props.zindex or 1
	l.Parent = parent
	return l
end

local function card(parent, size, layoutOrder, bg)
	local f = Instance.new("Frame")
	f.Size = size
	f.BackgroundColor3 = bg or CARD
	f.BorderSizePixel = 0
	f.LayoutOrder = layoutOrder or 1
	f.Parent = parent
	corner(f, 14)
	stroke(f, STROKE_C, 1, 0.55)
	return f
end

-- A drag helper that distinguishes a real drag from a tap, so moving the
-- floating pill on mobile doesn't also toggle the panel.
local function makeDraggable(handle, target, onTap)
	local dragging, moved, dragStart, startPos = false, false, nil, nil
	handle.InputBegan:Connect(function(input)
		if input.UserInputType ~= Enum.UserInputType.MouseButton1 and input.UserInputType ~= Enum.UserInputType.Touch then return end
		dragging = true
		moved = false
		dragStart = input.Position
		startPos = target.Position
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
end

-- Animated pill switch used for Auto-Optimize.
local function makeToggle(parent, initial, onChange)
	local wrap = Instance.new("TextButton")
	wrap.Size = UDim2.fromOffset(50, 28)
	wrap.BackgroundColor3 = initial and GOOD or CARD_2
	wrap.AutoButtonColor = false
	wrap.Text = ""
	wrap.Parent = parent
	corner(wrap, 14)
	local knob = Instance.new("Frame")
	knob.Size = UDim2.fromOffset(22, 22)
	knob.Position = initial and UDim2.new(1, -25, 0.5, -11) or UDim2.new(0, 3, 0.5, -11)
	knob.BackgroundColor3 = Color3.fromRGB(255, 255, 255)
	knob.BorderSizePixel = 0
	knob.Parent = wrap
	corner(knob, 11)
	local on = initial
	wrap.MouseButton1Click:Connect(function()
		on = not on
		tween(wrap, {BackgroundColor3 = on and GOOD or CARD_2}, 0.15)
		tween(knob, {Position = on and UDim2.new(1, -25, 0.5, -11) or UDim2.new(0, 3, 0.5, -11)}, 0.16, Enum.EasingStyle.Back)
		onChange(on)
	end)
	return wrap
end

-- Press-and-hold stepper button (single tap steps once, holding repeats).
local function makeStepper(parent, position, text, onStep)
	local btn = Instance.new("TextButton")
	btn.Size = UDim2.fromOffset(36, 36)
	btn.Position = position
	btn.BackgroundColor3 = CARD_2
	btn.AutoButtonColor = false
	btn.Text = text
	btn.TextColor3 = TEXT
	btn.Font = FONT_BOLD
	btn.TextSize = 18
	btn.Parent = parent
	corner(btn, 10)
	local holding = false
	btn.MouseButton1Down:Connect(function()
		holding = true
		onStep()
		task.wait(0.35)
		while holding do
			onStep()
			task.wait(0.09)
		end
	end)
	btn.MouseButton1Up:Connect(function() holding = false end)
	btn.MouseLeave:Connect(function() holding = false end)
	return btn
end

--=============================================================
-- Toast notifications — lightweight feedback without opening the panel
--=============================================================
local toastHost = Instance.new("Frame")
toastHost.Name = "Toasts"
toastHost.AnchorPoint = Vector2.new(1, 0)
toastHost.Position = UDim2.new(1, -14, 0, 14)
toastHost.Size = UDim2.fromOffset(240, 0)
toastHost.AutomaticSize = Enum.AutomaticSize.Y
toastHost.BackgroundTransparency = 1
toastHost.ZIndex = 50
toastHost.Parent = gui
local toastLayout = Instance.new("UIListLayout")
toastLayout.Padding = UDim.new(0, 6)
toastLayout.SortOrder = Enum.SortOrder.LayoutOrder
toastLayout.Parent = toastHost

local function showToast(text, color)
	local t = Instance.new("Frame")
	t.Size = UDim2.new(1, 0, 0, 0)
	t.AutomaticSize = Enum.AutomaticSize.Y
	t.BackgroundColor3 = BG
	t.BackgroundTransparency = 1
	t.ZIndex = 50
	t.Parent = toastHost
	corner(t, 10)
	stroke(t, color, 1, 0.3)
	pad(t, 10, 10, 8, 8)
	local dot = Instance.new("Frame")
	dot.Size = UDim2.fromOffset(6, 6)
	dot.Position = UDim2.fromOffset(0, 4)
	dot.BackgroundColor3 = color
	dot.ZIndex = 51
	dot.Parent = t
	corner(dot, 3)
	local txt = label(t, {
		text = text, font = FONT_MED, size = 11, color = TEXT,
		position = UDim2.fromOffset(14, 0), uiSize = UDim2.new(1, -14, 0, 0),
		wrap = true, zindex = 51,
	})
	txt.AutomaticSize = Enum.AutomaticSize.Y
	t.BackgroundTransparency = 1
	for _, d in ipairs({t}) do d.BackgroundTransparency = 0.08 end
	txt.TextTransparency = 1
	dot.BackgroundTransparency = 1
	tween(t, {BackgroundTransparency = 0.08}, 0.18)
	tween(txt, {TextTransparency = 0}, 0.18)
	tween(dot, {BackgroundTransparency = 0}, 0.18)
	task.delay(2.4, function()
		if not t.Parent then return end
		tween(t, {BackgroundTransparency = 1}, 0.25)
		tween(txt, {TextTransparency = 1}, 0.2)
		tween(dot, {BackgroundTransparency = 1}, 0.2)
		task.wait(0.28)
		t:Destroy()
	end)
end

onEngineEvent = function(kind, e, extra)
	if kind == "spike" then
		showToast(("Frame spike — %.0fms"):format(extra), WARN)
	elseif kind == "kept" then
		showToast(("%s disabled — saved ~%.1fms"):format(entryName(e), extra), GOOD)
	end
	-- "reverted" is intentionally quiet — it's the common case and would spam.
end

--=============================================================
-- Floating pill
--=============================================================
local floatShadow = Instance.new("Frame")
floatShadow.Size = UDim2.fromOffset(138, 52)
floatShadow.AnchorPoint = Vector2.new(1, 0.5)
floatShadow.Position = UDim2.new(1, -14, 0.74, 4)
floatShadow.BackgroundColor3 = Color3.new(0, 0, 0)
floatShadow.BackgroundTransparency = 0.55
floatShadow.BorderSizePixel = 0
floatShadow.ZIndex = 1
floatShadow.Parent = gui
corner(floatShadow, 26)

local float = Instance.new("TextButton")
float.Name = "PerformancePill"
float.Size = UDim2.fromOffset(138, 52)
float.AnchorPoint = Vector2.new(1, 0.5)
float.Position = UDim2.new(1, -14, 0.74, 0)
float.BackgroundColor3 = BG
float.AutoButtonColor = false
float.Text = ""
float.ZIndex = 5
float.Parent = gui
corner(float, 26)
local floatStroke = stroke(float, ACCENT, 1.5, 0.2)
gradient(float, Color3.fromRGB(21, 26, 38), Color3.fromRGB(10, 11, 16), 20)

local floatAccent = Instance.new("Frame")
floatAccent.Size = UDim2.fromOffset(4, 30)
floatAccent.Position = UDim2.fromOffset(10, 11)
floatAccent.BorderSizePixel = 0
floatAccent.BackgroundColor3 = GOOD
floatAccent.ZIndex = 7
floatAccent.Parent = float
corner(floatAccent, 3)

local floatMark = label(float, {
	text = "PERFORMANCE", font = FONT_BOLD, size = 8, color = FAINT,
	position = UDim2.fromOffset(20, 6), uiSize = UDim2.fromOffset(90, 12), zindex = 7,
})

local iconLabel = label(float, {
	text = "-- FPS", font = FONT_BLACK, size = 18, color = TEXT,
	position = UDim2.fromOffset(19, 19), uiSize = UDim2.fromOffset(80, 24), zindex = 7,
})

local floatStatus = Instance.new("TextLabel")
floatStatus.BackgroundTransparency = 1
floatStatus.AnchorPoint = Vector2.new(1, 0.5)
floatStatus.Position = UDim2.new(1, -14, 0.78, 0)
floatStatus.Size = UDim2.fromOffset(50, 16)
floatStatus.Font = FONT_BOLD
floatStatus.Text = "READY"
floatStatus.TextSize = 8
floatStatus.TextColor3 = GOOD
floatStatus.TextXAlignment = Enum.TextXAlignment.Right
floatStatus.ZIndex = 7
floatStatus.Parent = float

float.MouseEnter:Connect(function() tween(floatStroke, {Transparency = 0}, 0.12) end)
float.MouseLeave:Connect(function() tween(floatStroke, {Transparency = 0.2}, 0.18) end)

--=============================================================
-- Dashboard shell
--=============================================================
local panel = Instance.new("Frame")
panel.Name = "Dashboard"
panel.AnchorPoint = Vector2.new(1, 0.5)
panel.Position = UDim2.new(1, -18, 0.5, 0)
panel.Size = UDim2.fromOffset(380, 520)
panel.BackgroundColor3 = BG
panel.Visible = false
panel.ClipsDescendants = true
panel.ZIndex = 20
panel.Parent = gui
corner(panel, 20)
stroke(panel, Color3.fromRGB(72, 88, 128), 1.2, 0.3)
gradient(panel, Color3.fromRGB(14, 17, 25), Color3.fromRGB(8, 9, 13), 90)
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
gradient(topGlow, ACCENT, ACCENT_2, 0)

-- Header ---------------------------------------------------------------
local header = Instance.new("Frame")
header.Size = UDim2.new(1, 0, 0, 58)
header.BackgroundTransparency = 1
header.ZIndex = 22
header.Parent = panel

local headerGrip = Instance.new("Frame")
headerGrip.Position = UDim2.fromOffset(16, 14)
headerGrip.Size = UDim2.fromOffset(4, 30)
headerGrip.BorderSizePixel = 0
headerGrip.ZIndex = 23
headerGrip.Parent = header
corner(headerGrip, 2)
gradient(headerGrip, ACCENT, ACCENT_2, 90)

local title = label(header, {
	text = "Performance Engine", font = FONT_BOLD, size = 16, color = TEXT,
	position = UDim2.fromOffset(28, 8), uiSize = UDim2.new(1, -112, 0, 20),
})
local subtitle = label(header, {
	text = "Adaptive • causal • client-side", font = FONT, size = 10, color = MUTED,
	position = UDim2.fromOffset(28, 28), uiSize = UDim2.new(1, -112, 0, 16),
})

local function headerIconButton(text, xFromRight, sz)
	local b = Instance.new("TextButton")
	b.Size = UDim2.fromOffset(32, 32)
	b.Position = UDim2.new(1, xFromRight, 0.5, -16)
	b.BackgroundColor3 = CARD_2
	b.AutoButtonColor = false
	b.Text = text
	b.TextColor3 = TEXT
	b.Font = FONT
	b.TextSize = sz or 16
	b.ZIndex = 24
	b.Parent = header
	corner(b, 10)
	stroke(b, STROKE_C, 1, 0.35)
	return b
end
local compactBtn = headerIconButton("—", -78, 14)
local closeBtn = headerIconButton("×", -40, 20)

-- Segmented tab bar ------------------------------------------------------
local TAB_NAMES = {"Live", "Insights", "Log", "Settings"}
local tabBar = Instance.new("Frame")
tabBar.Size = UDim2.new(1, -28, 0, 34)
tabBar.Position = UDim2.fromOffset(14, 56)
tabBar.BackgroundColor3 = CARD_2
tabBar.ZIndex = 22
tabBar.Parent = panel
corner(tabBar, 10)
pad(tabBar, 3)

local tabIndicator = Instance.new("Frame")
tabIndicator.Size = UDim2.new(1 / #TAB_NAMES, 0, 1, 0)
tabIndicator.BackgroundColor3 = ACCENT
tabIndicator.ZIndex = 22
tabIndicator.Parent = tabBar
corner(tabIndicator, 8)
gradient(tabIndicator, ACCENT, ACCENT_2, 0)

local tabButtons = {}
for i, name in ipairs(TAB_NAMES) do
	local b = Instance.new("TextButton")
	b.Size = UDim2.new(1 / #TAB_NAMES, 0, 1, 0)
	b.Position = UDim2.new((i - 1) / #TAB_NAMES, 0, 0, 0)
	b.BackgroundTransparency = 1
	b.Text = name
	b.Font = FONT_BOLD
	b.TextSize = 10.5
	b.TextColor3 = i == 1 and TEXT or MUTED
	b.AutoButtonColor = false
	b.ZIndex = 23
	b.Parent = tabBar
	tabButtons[i] = b
end

-- Tab content host -------------------------------------------------------
local tabHost = Instance.new("Frame")
tabHost.Position = UDim2.fromOffset(0, 98)
tabHost.Size = UDim2.new(1, 0, 1, -98)
tabHost.BackgroundTransparency = 1
tabHost.ZIndex = 22
tabHost.Parent = panel

local function makeTabPage()
	local scroller = Instance.new("ScrollingFrame")
	scroller.Size = UDim2.new(1, 0, 1, 0)
	scroller.BackgroundTransparency = 1
	scroller.BorderSizePixel = 0
	scroller.ScrollBarThickness = 3
	scroller.ScrollBarImageTransparency = 0.3
	scroller.CanvasSize = UDim2.new(0, 0, 0, 0)
	scroller.AutomaticCanvasSize = Enum.AutomaticSize.Y
	scroller.ScrollingDirection = Enum.ScrollingDirection.Y
	scroller.Visible = false
	scroller.ZIndex = 22
	scroller.Parent = tabHost
	local l = Instance.new("UIListLayout")
	l.Padding = UDim.new(0, 8)
	l.SortOrder = Enum.SortOrder.LayoutOrder
	l.Parent = scroller
	pad(scroller, 14, 14, 4, 16)
	return scroller
end

local pages = {}
for i = 1, #TAB_NAMES do pages[i] = makeTabPage() end
pages[1].Visible = true

local currentTab = 1
local function selectTab(i)
	if i == currentTab then return end
	currentTab = i
	for idx, b in ipairs(tabButtons) do
		tween(b, {}, 0) -- no-op keeps timing consistent if extended later
		b.TextColor3 = idx == i and TEXT or MUTED
	end
	tween(tabIndicator, {Position = UDim2.new((i - 1) / #TAB_NAMES, 0, 0, 0)}, 0.22, Enum.EasingStyle.Quint)
	for idx, p in ipairs(pages) do p.Visible = idx == i end
end
for i, b in ipairs(tabButtons) do
	b.MouseButton1Click:Connect(function() selectTab(i) end)
end

local function sectionLabel(parent, text, order)
	return label(parent, {
		text = text, font = FONT_BOLD, size = 9.5, color = FAINT,
		order = order, uiSize = UDim2.new(1, 0, 0, 14),
	})
end

--=============================================================
-- LIVE TAB
--=============================================================
local livePage = pages[1]

sectionLabel(livePage, "LIVE", 1)
local metricsCard = card(livePage, UDim2.new(1, 0, 0, 116), 2)
local metricsGrid = Instance.new("UIGridLayout")
metricsGrid.CellSize = UDim2.new(0.485, 0, 0, 46)
metricsGrid.CellPadding = UDim2.new(0.03, 0, 0, 6)
metricsGrid.SortOrder = Enum.SortOrder.LayoutOrder
metricsGrid.Parent = metricsCard
pad(metricsCard, 12, 12, 10, 10)

local function metricTile(parent, order, name, dotColor)
	local wrap = Instance.new("Frame")
	wrap.BackgroundTransparency = 1
	wrap.LayoutOrder = order
	wrap.Parent = parent
	local dot = Instance.new("Frame")
	dot.Size = UDim2.fromOffset(6, 6)
	dot.Position = UDim2.fromOffset(0, 3)
	dot.BackgroundColor3 = dotColor
	dot.Parent = wrap
	corner(dot, 3)
	label(wrap, {
		text = name, font = FONT_BOLD, size = 8.5, color = MUTED,
		position = UDim2.fromOffset(13, 0), uiSize = UDim2.new(1, -13, 0, 12),
	})
	local val = label(wrap, {
		text = "--", font = FONT_BLACK, size = 18, color = TEXT,
		position = UDim2.fromOffset(0, 15), uiSize = UDim2.new(1, 0, 0, 26),
	})
	return val
end

local fpsLabel = metricTile(metricsCard, 1, "FPS", ACCENT)
local healthLabel = metricTile(metricsCard, 2, "HEALTH", GOOD)
local pingLabel = metricTile(metricsCard, 3, "PING", ACCENT_2)
local jitterLabel = metricTile(metricsCard, 4, "JITTER", WARN)

sectionLabel(livePage, "FPS HISTORY", 3)
local chart = card(livePage, UDim2.new(1, 0, 0, 72), 4)
pad(chart, 8, 8, 8, 10)
local chartInner = Instance.new("Frame")
chartInner.BackgroundTransparency = 1
chartInner.Size = UDim2.new(1, 0, 1, 0)
chartInner.Parent = chart
local BAR_COUNT = CONFIG.HistoryLength
local bars = {}
for i = 1, BAR_COUNT do
	local bar = Instance.new("Frame")
	bar.AnchorPoint = Vector2.new(0, 1)
	bar.Position = UDim2.new((i - 1) / BAR_COUNT, 1, 1, 0)
	bar.Size = UDim2.new(1 / BAR_COUNT, -2, 0, 2)
	bar.BorderSizePixel = 0
	bar.BackgroundColor3 = ACCENT
	bar.Parent = chartInner
	corner(bar, 2)
	bars[i] = bar
end
local targetLine = Instance.new("Frame")
targetLine.Size = UDim2.new(1, 0, 0, 1)
targetLine.Position = UDim2.new(0, 0, 0.5, 0)
targetLine.BackgroundColor3 = Color3.fromRGB(110, 118, 138)
targetLine.BackgroundTransparency = 0.6
targetLine.BorderSizePixel = 0
targetLine.ZIndex = 0
targetLine.Parent = chartInner

sectionLabel(livePage, "STATUS", 5)
local chipsRow = Instance.new("Frame")
chipsRow.Size = UDim2.new(1, 0, 0, 26)
chipsRow.BackgroundTransparency = 1
chipsRow.LayoutOrder = 6
chipsRow.Parent = livePage
local chipsLayout = Instance.new("UIListLayout")
chipsLayout.FillDirection = Enum.FillDirection.Horizontal
chipsLayout.Padding = UDim.new(0, 6)
chipsLayout.SortOrder = Enum.SortOrder.LayoutOrder
chipsLayout.Parent = chipsRow

local function makeChip(parent, order)
	local c = Instance.new("Frame")
	c.AutomaticSize = Enum.AutomaticSize.X
	c.Size = UDim2.new(0, 0, 1, 0)
	c.BackgroundColor3 = CARD_2
	c.LayoutOrder = order
	c.Parent = parent
	corner(c, 13)
	pad(c, 10, 10, 0, 0)
	local t = label(c, {text = "--", font = FONT_BOLD, size = 9, color = TEXT, uiSize = UDim2.new(0, 0, 1, 0)})
	t.AutomaticSize = Enum.AutomaticSize.X
	return c, t
end
local diagnosisChip, diagnosisText = makeChip(chipsRow, 1)
local intensityChip, intensityText = makeChip(chipsRow, 2)
local experimentChip, experimentText = makeChip(chipsRow, 3)

sectionLabel(livePage, "APPLIED", 7)
local appliedCard = card(livePage, UDim2.new(1, 0, 0, 40), 8)
local appliedLabel = label(appliedCard, {
	text = "0 / 0 objects disabled", font = FONT_MED, size = 11, color = TEXT,
	position = UDim2.fromOffset(12, 0), uiSize = UDim2.new(1, -24, 1, 0),
})

--=============================================================
-- INSIGHTS TAB
--=============================================================
local insightsPage = pages[2]
sectionLabel(insightsPage, "LEARNED FROM YOUR OWN FRAME TIME", 1)
local insightsEmpty = label(insightsPage, {
	text = "Gathering causal evidence — this fills in once the engine has run a few experiments.",
	font = FONT, size = 10.5, color = MUTED, wrap = true, order = 2,
	uiSize = UDim2.new(1, 0, 0, 32),
})

local INSIGHT_ROW_COUNT = 8
local insightRows = {}
for i = 1, INSIGHT_ROW_COUNT do
	local row = card(insightsPage, UDim2.new(1, 0, 0, 54), i + 2)
	row.Visible = false
	pad(row, 12, 12, 8, 8)
	local nameLbl = label(row, {
		text = "", font = FONT_BOLD, size = 11, color = TEXT,
		uiSize = UDim2.new(1, -70, 0, 14),
	})
	local subLbl = label(row, {
		text = "", font = FONT, size = 8.5, color = MUTED,
		position = UDim2.fromOffset(0, 15), uiSize = UDim2.new(1, -70, 0, 12),
	})
	local impactLbl = label(row, {
		text = "", font = FONT_BOLD, size = 11, color = GOOD,
		position = UDim2.new(1, -60, 0, 0), uiSize = UDim2.fromOffset(60, 14),
		align = Enum.TextXAlignment.Right,
	})
	local barBg = Instance.new("Frame")
	barBg.Position = UDim2.fromOffset(0, 33)
	barBg.Size = UDim2.new(1, 0, 0, 4)
	barBg.BackgroundColor3 = CARD_2
	barBg.Parent = row
	corner(barBg, 2)
	local barFill = Instance.new("Frame")
	barFill.Size = UDim2.new(0, 0, 1, 0)
	barFill.BackgroundColor3 = ACCENT
	barFill.BorderSizePixel = 0
	barFill.Parent = barBg
	corner(barFill, 2)
	local confLbl = label(row, {
		text = "", font = FONT, size = 8, color = FAINT,
		position = UDim2.fromOffset(0, 40), uiSize = UDim2.new(1, 0, 0, 10),
	})
	insightRows[i] = {row = row, name = nameLbl, sub = subLbl, impact = impactLbl, barFill = barFill, conf = confLbl}
end

--=============================================================
-- LOG TAB
--=============================================================
local logPage = pages[3]
sectionLabel(logPage, "ACTIVITY", 1)
local LOG_ROW_COUNT = 24
local logRows = {}
local LOG_COLORS = {good = GOOD, bad = BAD, warn = WARN, info = FAINT}
for i = 1, LOG_ROW_COUNT do
	local row = Instance.new("Frame")
	row.Size = UDim2.new(1, 0, 0, 0)
	row.AutomaticSize = Enum.AutomaticSize.Y
	row.BackgroundTransparency = 1
	row.LayoutOrder = i + 1
	row.Visible = false
	row.Parent = logPage
	local dot = Instance.new("Frame")
	dot.Size = UDim2.fromOffset(6, 6)
	dot.Position = UDim2.fromOffset(2, 5)
	dot.Parent = row
	corner(dot, 3)
	local txt = label(row, {
		text = "", font = FONT_MONO, size = 9.5, color = Color3.fromRGB(178, 190, 210),
		position = UDim2.fromOffset(16, 0), uiSize = UDim2.new(1, -16, 0, 0), wrap = true,
	})
	txt.AutomaticSize = Enum.AutomaticSize.Y
	logRows[i] = {row = row, dot = dot, txt = txt}
end

--=============================================================
-- SETTINGS TAB
--=============================================================
local settingsPage = pages[4]

sectionLabel(settingsPage, "TARGET FRAME RATE", 1)
local targetRow = card(settingsPage, UDim2.new(1, 0, 0, 48), 2)
local targetLabel = label(targetRow, {
	text = tostring(state.targetFPS) .. " FPS", font = FONT_BOLD, size = 15, color = TEXT,
	position = UDim2.fromOffset(50, 0), uiSize = UDim2.new(1, -100, 1, 0), align = Enum.TextXAlignment.Center,
})
makeStepper(targetRow, UDim2.fromOffset(6, 6), "−", function()
	state.targetFPS = math.max(CONFIG.MinTargetFPS, state.targetFPS - 5)
	targetLabel.Text = state.targetFPS .. " FPS"
end)
makeStepper(targetRow, UDim2.new(1, -42, 0, 6), "+", function()
	state.targetFPS = math.min(CONFIG.MaxTargetFPS, state.targetFPS + 5)
	targetLabel.Text = state.targetFPS .. " FPS"
end)

sectionLabel(settingsPage, "CONTROL", 3)
local optimizeRow = card(settingsPage, UDim2.new(1, 0, 0, 54), 4)
label(optimizeRow, {
	text = "Automatic optimization", font = FONT_BOLD, size = 11.5, color = TEXT,
	position = UDim2.fromOffset(12, 8), uiSize = UDim2.new(1, -80, 0, 16),
})
label(optimizeRow, {
	text = "Closed-loop, causally-tested control", font = FONT, size = 8.5, color = MUTED,
	position = UDim2.fromOffset(12, 27), uiSize = UDim2.new(1, -80, 0, 14),
})
local autoToggle = makeToggle(optimizeRow, state.autoOptimize, function(on)
	state.autoOptimize = on
	if not on then forceRestoreAll() end
end)
autoToggle.Position = UDim2.new(1, -62, 0.5, -14)

sectionLabel(settingsPage, "MANUAL OVERRIDE", 5)
local restoreRow = card(settingsPage, UDim2.new(1, 0, 0, 44), 6)
local restoreBtn = Instance.new("TextButton")
restoreBtn.Size = UDim2.new(1, -16, 1, -12)
restoreBtn.Position = UDim2.fromOffset(8, 6)
restoreBtn.BackgroundColor3 = CARD_2
restoreBtn.AutoButtonColor = false
restoreBtn.Text = "Restore everything now"
restoreBtn.Font = FONT_BOLD
restoreBtn.TextSize = 11
restoreBtn.TextColor3 = TEXT
restoreBtn.Parent = restoreRow
corner(restoreBtn, 10)
stroke(restoreBtn, STROKE_C, 1, 0.4)
restoreBtn.MouseButton1Click:Connect(function()
	forceRestoreAll()
	addLog("Manual restore-all triggered from Settings", "info")
	showToast("All effects restored", ACCENT)
end)

sectionLabel(settingsPage, "SESSION", 7)
local sessionCard = card(settingsPage, UDim2.new(1, 0, 0, 108), 8)
pad(sessionCard, 12, 12, 10, 10)
local sessionGrid = Instance.new("UIGridLayout")
sessionGrid.CellSize = UDim2.new(0.485, 0, 0, 34)
sessionGrid.CellPadding = UDim2.new(0.03, 0, 0, 6)
sessionGrid.SortOrder = Enum.SortOrder.LayoutOrder
sessionGrid.Parent = sessionCard

local function sessionTile(order, name)
	local wrap = Instance.new("Frame")
	wrap.BackgroundTransparency = 1
	wrap.LayoutOrder = order
	wrap.Parent = sessionCard
	label(wrap, {text = name, font = FONT_BOLD, size = 8, color = FAINT, uiSize = UDim2.new(1, 0, 0, 11)})
	local v = label(wrap, {
		text = "--", font = FONT_MED, size = 10.5, color = TEXT,
		position = UDim2.fromOffset(0, 13), uiSize = UDim2.new(1, 0, 0, 16), wrap = true,
	})
	return v
end
local sessionFPS = sessionTile(1, "FPS MIN / AVG / MAX")
local sessionPing = sessionTile(2, "PING MIN / AVG / MAX")
local sessionEvents = sessionTile(3, "EVENTS / SESSION TIME")
local sessionBands = sessionTile(4, "INTENSITY BANDS")

--=============================================================
-- Open/close + drag + compact + responsive sizing
--=============================================================
local panelSizeFull = UDim2.fromOffset(380, 520)
local currentPanelSize = panelSizeFull

local function setPanelOpen(open)
	state.panelOpen = open
	if open then
		panel.Visible = true
		panel.BackgroundTransparency = 0.06
		panelScale.Scale = 0.965
		tween(panelScale, {Scale = 1}, 0.22, Enum.EasingStyle.Back)
		tween(panel, {BackgroundTransparency = 0}, 0.18)
	else
		tween(panelScale, {Scale = 0.965}, 0.14, Enum.EasingStyle.Quad, Enum.EasingDirection.In)
		local tw = tween(panel, {BackgroundTransparency = 0.06}, 0.14, Enum.EasingStyle.Quad, Enum.EasingDirection.In)
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
	tabBar.Visible = not state.compact
	tabHost.Visible = not state.compact
	compactBtn.Text = state.compact and "+" or "—"
	panel.Size = state.compact and UDim2.fromOffset(currentPanelSize.X.Offset, 58) or currentPanelSize
end)

-- Height/width are clamped against the *actual* usable screen space (camera
-- viewport minus the Roblox top-bar inset) so the dashboard can never render
-- partially off-screen the way it did in v4.
local GuiService = game:GetService("GuiService")
local function layoutResponsive()
	local camera = Workspace.CurrentCamera
	if not camera then return end
	local viewport = camera.ViewportSize
	local topInset = 36
	local ok, inset = pcall(function() return GuiService:GetGuiInset() end)
	if ok and inset then topInset = math.max(topInset, inset.Y) end

	local usableH = math.max(300, viewport.Y - topInset - 24)
	local mobile = UserInputService.TouchEnabled and viewport.X < 700

	if mobile then
		local w = math.clamp(viewport.X - 20, 260, 400)
		local h = math.min(560, usableH)
		panelSizeFull = UDim2.fromOffset(w, h)
		panel.AnchorPoint = Vector2.new(0.5, 0.5)
		panel.Position = UDim2.new(0.5, 0, 0.5, topInset * 0.25)
		float.Size = UDim2.fromOffset(122, 46)
		floatShadow.Size = UDim2.fromOffset(122, 46)
		float.Position = UDim2.new(1, -10, 1, -20)
		floatShadow.Position = UDim2.new(1, -10, 1, -16)
	else
		local h = math.min(520, usableH)
		panelSizeFull = UDim2.fromOffset(380, h)
		panel.AnchorPoint = Vector2.new(1, 0.5)
		panel.Position = UDim2.new(1, -18, 0.5, 0)
		float.Size = UDim2.fromOffset(138, 52)
		floatShadow.Size = UDim2.fromOffset(138, 52)
		float.Position = UDim2.new(1, -14, 0.74, 0)
		floatShadow.Position = UDim2.new(1, -14, 0.74, 4)
	end
	currentPanelSize = panelSizeFull
	if not state.compact then panel.Size = panelSizeFull end
end

layoutResponsive()
do
	local camera = Workspace.CurrentCamera
	if camera then camera:GetPropertyChangedSignal("ViewportSize"):Connect(layoutResponsive) end
	Workspace:GetPropertyChangedSignal("CurrentCamera"):Connect(function()
		local cam = Workspace.CurrentCamera
		if cam then cam:GetPropertyChangedSignal("ViewportSize"):Connect(layoutResponsive) end
		layoutResponsive()
	end)
end

--=============================================================
-- UI REFRESH LOOP (display only — never touches game objects)
--=============================================================
local function colorFor(health)
	return health >= 75 and GOOD or health >= 45 and WARN or BAD
end

local function refreshInsightsUI()
	local data = getTopInsightsData(INSIGHT_ROW_COUNT)
	insightsEmpty.Visible = #data == 0
	for i = 1, INSIGHT_ROW_COUNT do
		local r = insightRows[i]
		local d = data[i]
		if d then
			r.row.Visible = true
			r.name.Text = d.title
			r.sub.Text = d.subtitle
			r.impact.Text = d.impactText
			r.impact.TextColor3 = d.positive and GOOD or FAINT
			r.conf.Text = ("%d%% confidence • %d tests"):format(math.floor(d.confidence * 100), d.tests)
			tween(r.barFill, {Size = UDim2.new(math.clamp(d.confidence, 0, 1), 0, 1, 0)}, 0.25)
			r.barFill.BackgroundColor3 = d.positive and GOOD or FAINT
		else
			r.row.Visible = false
		end
	end
end

local lastLogCount = -1
local function refreshLogUI()
	if #state.log == lastLogCount then return end
	lastLogCount = #state.log
	for i = 1, LOG_ROW_COUNT do
		local r = logRows[i]
		local entry = state.log[i]
		if entry then
			r.row.Visible = true
			r.txt.Text = entry.text
			local c = LOG_COLORS[entry.tag] or FAINT
			r.dot.BackgroundColor3 = c
		else
			r.row.Visible = false
		end
	end
end

task.spawn(function()
	local tick = 0
	while gui.Parent do
		tick += 1
		local health = computeHealthScore()
		local healthColor = colorFor(health)

		-- Floating pill
		iconLabel.Text = tostring(math.floor(state.smoothedFPS)) .. " FPS"
		floatAccent.BackgroundColor3 = healthColor
		floatStroke.Color = healthColor
		floatStatus.Text = state.autoOptimize and "AUTO" or "PAUSED"
		floatStatus.TextColor3 = healthColor
		floatShadow.Position = UDim2.new(
			float.Position.X.Scale, float.Position.X.Offset,
			float.Position.Y.Scale, float.Position.Y.Offset + 4)

		-- Live tab
		fpsLabel.Text = ("%d"):format(math.floor(state.smoothedFPS))
		fpsLabel.TextColor3 = healthColor
		pingLabel.Text = ("%d ms"):format(math.floor(state.ping))
		jitterLabel.Text = ("%.1f ms"):format(state.jitterMs)
		healthLabel.Text = ("%d"):format(health)
		healthLabel.TextColor3 = healthColor

		local disabledCount = 0
		for _, e in ipairs(registry) do if e.disabledByUs then disabledCount += 1 end end
		appliedLabel.Text = ("%d / %d objects disabled  •  target %d FPS"):format(disabledCount, #registry, state.targetFPS)

		diagnosisText.Text = "Diagnosis: " .. state.diagnosis
		diagnosisChip.BackgroundColor3 = state.diagnosis == "spiky" and Color3.fromRGB(70, 55, 26)
			or state.diagnosis == "sustained" and Color3.fromRGB(70, 30, 34) or CARD_2
		intensityText.Text = ("Intensity %d%%"):format(math.floor(state.intensity * 100))
		experimentText.Text = pendingAction and ("Testing: " .. (pendingAction.label or "settling")) or "Idle"
		experimentChip.BackgroundColor3 = pendingAction and Color3.fromRGB(26, 46, 72) or CARD_2

		local hist = state.history.fps
		local maxVal = math.max(30, state.targetFPS * 1.2)
		for i = 1, BAR_COUNT do
			local histIndex = i - (BAR_COUNT - #hist)
			local v = histIndex >= 1 and hist[histIndex] or 0
			local h = math.clamp(v / maxVal, 0.02, 1)
			bars[i].Size = UDim2.new(1 / BAR_COUNT, -2, h, 0)
			bars[i].BackgroundColor3 = v >= state.targetFPS and GOOD
				or v >= state.targetFPS * 0.7 and WARN
				or BAD
		end

		-- Settings tab / session
		local s = state.session
		local elapsed = os.clock() - s.startClock
		sessionFPS.Text = ("%d / %d / %d"):format(
			s.fpsMin == math.huge and 0 or math.floor(s.fpsMin), math.floor(s.fpsCount > 0 and (s.fpsSum / s.fpsCount) or 0), math.floor(s.fpsMax))
		sessionPing.Text = ("%d / %d / %d"):format(
			s.pingMin == math.huge and 0 or math.floor(s.pingMin), math.floor(s.pingCount > 0 and (s.pingSum / s.pingCount) or 0), math.floor(s.pingMax))
		sessionEvents.Text = ("%d events / %ds"):format(s.optimizationEvents, math.floor(elapsed))
		sessionBands.Text = ("low %ds  med %ds  high %ds  ext %ds"):format(
			math.floor(s.timeInBand.low), math.floor(s.timeInBand.medium), math.floor(s.timeInBand.high), math.floor(s.timeInBand.extreme))

		if tick % 5 == 0 then refreshInsightsUI() end
		refreshLogUI()

		task.wait(0.1)
	end
end)

addLog("Autonomous v5 started — causal experiments enabled (target " .. state.targetFPS .. " FPS)", "info")
