import InformationTheory.CourtadeKumar.EnvelopeConcavity

/-! Concavity of the explicit envelope, conditional only on `lambda₂ ≥ 0`. -/

open Set
open scoped ENNReal NNReal BigOperators

namespace CourtadeKumar

lemma binaryEntropyBits_concaveOn :
    ConcaveOn ℝ (Icc (0 : ℝ) 1) binaryEntropyBits := by
  have hlog : 0 ≤ (Real.log 2)⁻¹ := by positivity
  have h := Real.strictConcave_binEntropy.concaveOn.smul hlog
  apply h.congr
  intro p hp
  simp [binaryEntropyBits, smul_eq_mul, div_eq_mul_inv, mul_comm]

lemma mul_one_sub_concaveOn :
    ConcaveOn ℝ (Icc (0 : ℝ) 1) (fun p : ℝ ↦ p * (1 - p)) := by
  constructor
  · exact convex_Icc 0 1
  · intro x hx y hy a b ha hb hab
    simp only [smul_eq_mul]
    have hnonneg : 0 ≤ a * b * (x - y) ^ 2 := by positivity
    have hb' : b = 1 - a := by linarith
    subst b
    nlinarith

lemma channelS_nonneg (alpha : ℝ≥0) (halpha : alpha ≤ 1) :
    0 ≤ channelS (alpha : ℝ) := by
  have ha0 : 0 ≤ (alpha : ℝ) := alpha.property
  have ha1 : (alpha : ℝ) ≤ 1 := by exact_mod_cast halpha
  simp only [channelS, channelRho]
  nlinarith

/-- The elementary coefficient inequality `lambda₂ ≥ 0` is the only
remaining input needed for concavity of the explicit Bellman envelope. -/
theorem bellmanEnvelope_concaveOn_of_lambda_nonneg
    (alpha : ℝ≥0) (halpha : alpha ≤ 1)
    (hlambda : 0 ≤ bellmanLambda (alpha : ℝ)) :
    ConcaveOn ℝ (Icc (0 : ℝ) 1) (bellmanEnvelope (alpha : ℝ)) := by
  have hEntropy := binaryEntropyBits_concaveOn.smul (channelS_nonneg alpha halpha)
  have hQuadratic := mul_one_sub_concaveOn.smul (by positivity :
    0 ≤ 4 * bellmanLambda (alpha : ℝ))
  apply (hEntropy.add hQuadratic).congr
  intro p hp
  simp only [Pi.add_apply, smul_eq_mul]
  simp [bellmanEnvelope]
  ring

theorem bellmanEnvelopeSortingDominance_of_lambda_nonneg
    (alpha : ℝ≥0) (halpha : alpha ≤ 1)
    (hlambda : 0 ≤ bellmanLambda (alpha : ℝ)) :
    BellmanEnvelopeSortingDominance alpha :=
  bellmanEnvelopeSortingDominance_of_concave alpha
    (bellmanEnvelope_concaveOn_of_lambda_nonneg alpha halpha hlambda)

end CourtadeKumar
