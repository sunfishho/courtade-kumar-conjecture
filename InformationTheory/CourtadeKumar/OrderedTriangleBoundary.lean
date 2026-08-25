import InformationTheory.CourtadeKumar.OrderedTriangleSymmetry

/-! Elementary boundary certificates for the ordered-triangle perspective. -/

open Set
open scoped NNReal

namespace CourtadeKumar

/-- Contracting the half-width of a symmetric pair toward its midpoint can
only increase its average binary entropy. -/
theorem orderedTriangleEntropy_le_channelEntropy
    {alpha : ℝ≥0} (halpha : (alpha : ℝ) ≤ 1 / 2)
    {m u : ℝ} (hu0 : 0 ≤ u) (hum : u ≤ m) (hu1m : u ≤ 1 - m) :
    orderedTriangleEntropy m u ≤
      orderedTriangleChannelEntropy alpha m u := by
  let rho : ℝ := channelRho (alpha : ℝ)
  let A : ℝ := (1 + rho) / 2
  let B : ℝ := (1 - rho) / 2
  let x : ℝ := m - u
  let y : ℝ := m + u
  have halpha0 : (0 : ℝ) ≤ alpha := alpha.2
  have hrho : rho ∈ Icc (0 : ℝ) 1 := by
    dsimp [rho, channelRho]
    constructor <;> linarith [halpha0, halpha]
  have hA : 0 ≤ A := by dsimp [A]; linarith [hrho.1]
  have hB : 0 ≤ B := by dsimp [B]; linarith [hrho.2]
  have hAB : A + B = 1 := by dsimp [A, B]; ring
  have hx : x ∈ Icc (0 : ℝ) 1 := by
    dsimp [x]
    constructor <;> linarith [hum, hu1m, hu0]
  have hy : y ∈ Icc (0 : ℝ) 1 := by
    dsimp [y]
    constructor <;> linarith [hum, hu1m, hu0]
  have hminus : A * x + B * y = m - rho * u := by
    dsimp [A, B, x, y]
    ring
  have hplus : B * x + A * y = m + rho * u := by
    dsimp [A, B, x, y]
    ring
  have hconcave := Real.strictConcave_binEntropy.concaveOn
  have h₁ := hconcave.2 hx hy hA hB hAB
  have h₂ := hconcave.2 hx hy hB hA (by linarith [hAB])
  simp only [smul_eq_mul] at h₁ h₂
  rw [hminus] at h₁
  rw [hplus] at h₂
  have hnat : Real.binEntropy x + Real.binEntropy y ≤
      Real.binEntropy (m - rho * u) + Real.binEntropy (m + rho * u) := by
    calc
      Real.binEntropy x + Real.binEntropy y =
          (A + B) * Real.binEntropy x + (A + B) * Real.binEntropy y := by
            rw [hAB]
            ring
      _ = (A * Real.binEntropy x + B * Real.binEntropy y) +
          (B * Real.binEntropy x + A * Real.binEntropy y) := by ring
      _ ≤ Real.binEntropy (m - rho * u) +
          Real.binEntropy (m + rho * u) := add_le_add h₁ h₂
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold orderedTriangleEntropy orderedTriangleChannelEntropy binaryEntropyBits
  dsimp [rho] at hnat ⊢
  calc
    (Real.binEntropy (m - u) / Real.log 2 +
        Real.binEntropy (m + u) / Real.log 2) / 2 =
        (Real.binEntropy (m - u) + Real.binEntropy (m + u)) /
          (2 * Real.log 2) := by ring
    _ ≤ (Real.binEntropy (m - channelRho (alpha : ℝ) * u) +
        Real.binEntropy (m + channelRho (alpha : ℝ) * u)) /
          (2 * Real.log 2) :=
      (div_le_div_iff_of_pos_right (mul_pos (by norm_num) hlog)).2 hnat
    _ = (Real.binEntropy (m - channelRho (alpha : ℝ) * u) / Real.log 2 +
        Real.binEntropy (m + channelRho (alpha : ℝ) * u) / Real.log 2) / 2 := by
      ring

/-- At zero displacement, `theta = 1` and the zero affine functional form
a valid global support certificate. -/
theorem orderedTriangle_zeroWidth_affineSupport
    (alpha : ℝ≥0) (halpha : (alpha : ℝ) ≤ 1 / 2) :
    TriangleAffineSupport alpha 1 0 0 := by
  intro m u hu0 hum hu1m
  simpa using sub_nonneg.mpr
    (orderedTriangleEntropy_le_channelEntropy halpha hu0 hum hu1m)

/-- The affine certificate required by weak duality exists whenever the
prescribed mean half-width is zero. -/
theorem exists_orderedTriangleAffineSupport_of_averageU_eq_zero
    (alpha : ℝ≥0) (halpha : (alpha : ℝ) ≤ 1 / 2)
    (n : ℕ) (M U : BitVec n → ℝ)
    (hU : cubeAverage n U = 0) :
    let E0 :=
      (bellmanEnvelope (alpha : ℝ) (cubeAverage n M - cubeAverage n U) +
        bellmanEnvelope (alpha : ℝ) (cubeAverage n M + cubeAverage n U)) / 2
    ∃ theta a b : ℝ,
      0 ≤ theta ∧ TriangleAffineSupport alpha theta a b ∧
        bellmanEnvelope (alpha : ℝ) (cubeAverage n M) ≤
          theta * E0 + a * cubeAverage n M + b * cubeAverage n U := by
  dsimp
  refine ⟨1, 0, 0, by norm_num,
    orderedTriangle_zeroWidth_affineSupport alpha halpha, ?_⟩
  rw [hU]
  ring_nf
  exact le_rfl

lemma binaryEntropyBits_nonneg_of_mem_Icc
    {p : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) :
    0 ≤ binaryEntropyBits p := by
  unfold binaryEntropyBits
  exact div_nonneg (Real.binEntropy_nonneg hp.1 hp.2)
    (Real.log_pos (by norm_num)).le

theorem orderedTriangleChannelEntropy_nonneg
    {alpha : ℝ≥0} (halpha : (alpha : ℝ) ≤ 1 / 2)
    {m u : ℝ} (hu0 : 0 ≤ u) (hum : u ≤ m) (hu1m : u ≤ 1 - m) :
    0 ≤ orderedTriangleChannelEntropy alpha m u := by
  have halpha0 : (0 : ℝ) ≤ alpha := alpha.2
  have hrho : channelRho (alpha : ℝ) ∈ Icc (0 : ℝ) 1 := by
    unfold channelRho
    constructor <;> linarith
  have hminus : m - channelRho (alpha : ℝ) * u ∈ Icc (0 : ℝ) 1 := by
    constructor
    · nlinarith [mul_le_mul_of_nonneg_right hrho.2 hu0]
    · nlinarith [mul_nonneg hrho.1 hu0]
  have hplus : m + channelRho (alpha : ℝ) * u ∈ Icc (0 : ℝ) 1 := by
    constructor
    · nlinarith [mul_nonneg hrho.1 hu0]
    · nlinarith [mul_le_mul_of_nonneg_right hrho.2 hu0]
  unfold orderedTriangleChannelEntropy
  exact div_nonneg (add_nonneg
    (binaryEntropyBits_nonneg_of_mem_Icc hminus)
    (binaryEntropyBits_nonneg_of_mem_Icc hplus)) (by norm_num)

/-- With zero entropy multiplier, the zero affine functional is a global
support because channel entropy is nonnegative on the ordered triangle. -/
theorem orderedTriangle_nonnegative_affineSupport
    (alpha : ℝ≥0) (halpha : (alpha : ℝ) ≤ 1 / 2) :
    TriangleAffineSupport alpha 0 0 0 := by
  intro m u hu0 hum hu1m
  simpa using orderedTriangleChannelEntropy_nonneg halpha hu0 hum hu1m

/-- The mean-zero boundary in the manuscript's perspective theorem has an
immediate affine certificate: the target envelope vanishes. -/
theorem exists_orderedTriangleAffineSupport_of_averageM_eq_zero
    (alpha : ℝ≥0) (halpha : (alpha : ℝ) ≤ 1 / 2)
    (n : ℕ) (M U : BitVec n → ℝ)
    (hM : cubeAverage n M = 0) :
    let E0 :=
      (bellmanEnvelope (alpha : ℝ) (cubeAverage n M - cubeAverage n U) +
        bellmanEnvelope (alpha : ℝ) (cubeAverage n M + cubeAverage n U)) / 2
    ∃ theta a b : ℝ,
      0 ≤ theta ∧ TriangleAffineSupport alpha theta a b ∧
        bellmanEnvelope (alpha : ℝ) (cubeAverage n M) ≤
          theta * E0 + a * cubeAverage n M + b * cubeAverage n U := by
  dsimp
  refine ⟨0, 0, 0, by norm_num,
    orderedTriangle_nonnegative_affineSupport alpha halpha, ?_⟩
  rw [hM, bellmanEnvelope_zero]
  norm_num

@[simp] lemma bellmanEnvelope_zero_channel (p : ℝ) :
    bellmanEnvelope 0 p = 0 := by
  simp [bellmanEnvelope, channelS, channelRho, bellmanLambda,
    binaryEntropyBits, Real.binEntropy]

/-- At the noiseless-channel boundary, the zero multiplier and zero affine
functional are a global support, since the target envelope vanishes. -/
theorem orderedTriangle_zeroChannel_affineSupport :
    TriangleAffineSupport (0 : ℝ≥0) 0 0 0 := by
  exact orderedTriangle_nonnegative_affineSupport 0 (by norm_num)

/-- Complete affine-support theorem for the channel boundary `alpha = 0`. -/
theorem orderedTriangleAffineSupportTheorem_zero :
    OrderedTriangleAffineSupportTheorem (0 : ℝ≥0) := by
  intro n M U hdomain
  dsimp
  refine ⟨0, 0, 0, by norm_num, orderedTriangle_zeroChannel_affineSupport, ?_⟩
  simp

end CourtadeKumar
