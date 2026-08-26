import InformationTheory.CourtadeKumar.LRLowShapeTAlgebra

/-!
# Exact resummation of the low-shape `V` coefficients

This file expands the two products in the tangent certificate's analytic
`V` reserve and proves that their Cauchy coefficients sum to the reserve.
-/

open Set
open scoped BigOperators

namespace CourtadeKumar

noncomputable def lrLowDFlowCoeff (v t : ℝ) (n : ℕ) : ℝ :=
  (if n = 0 then lrFlowA v t else 0) -
    lrLowBFlowCoeff (lrFlowBeta v) (v ^ 2 * t ^ 2) n

noncomputable def lrLowFDerivCoeff (v x G : ℝ) (n : ℕ) : ℝ :=
  ((n + 1 : ℕ) : ℝ) *
    (G + lrLowP v x (n + 1) - 4 / (1 + v) * lrLowB (n + 1))

noncomputable def lrLowYTangentCoeff (v x : ℝ) (n : ℕ) : ℝ :=
  ((n + 1 : ℕ) : ℝ) *
    (lrLowP v x (n + 1) -
      4 * lrFlowM v * x * lrLowB (n + 1))

noncomputable def lrLowVConvolutionCoeff (v t : ℝ) (n : ℕ) : ℝ :=
  (∑ k ∈ Finset.range (n + 1),
      lrLowDFlowCoeff v t k *
        lrLowFDerivCoeff v (t ^ 2) (lrGShape t v) (n - k)) +
    (∑ k ∈ Finset.range (n + 1),
      lrLowBFlowCoeff (lrFlowBeta v) (v ^ 2 * t ^ 2) k *
        lrLowYTangentCoeff v (t ^ 2) (n - k))

theorem lrLowDFlowCoeff_hasSum
    {R v t : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1)
    (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasSum (fun n : ℕ ↦ lrLowDFlowCoeff v t n * R ^ n)
      (lrFlowD R v t) := by
  have ha : HasSum (fun n : ℕ ↦
      (if n = 0 then lrFlowA v t else 0) * R ^ n) (lrFlowA v t) := by
    have hi := hasSum_ite_eq (0 : ℕ) (lrFlowA v t)
    convert hi using 1
    funext n
    by_cases hn : n = 0
    · simp [hn]
    · simp [hn]
  have hb := lrLowBFlowCoeff_hasSum hR hv ht
  convert ha.sub hb using 1
  · funext n
    unfold lrLowDFlowCoeff
    ring

theorem lrLowFDerivCoeff_hasSum
    {R v t : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1)
    (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasSum (fun n : ℕ ↦
      lrLowFDerivCoeff v (t ^ 2) (lrGShape t v) n * R ^ n)
      (lrFlowC R v t / (1 - R) ^ 2) := by
  have hg := (lrLow_weighted_geometric_hasSum hR).mul_left (lrGShape t v)
  have hp := lrLowP_derivative_hasSum hR hv ht
  have hb := lrLowB_derivative_hasSum hR
  have h := hg.add hp |>.sub (hb.mul_left (4 / (1 + v)))
  convert h using 1
  · funext n
    unfold lrLowFDerivCoeff
    ring
  · unfold lrFlowC
    have hdenV : 1 + v ≠ 0 := by linarith [hv.1]
    have hdenR : (1 - R) ^ 2 ≠ 0 :=
      pow_ne_zero 2 (sub_ne_zero.mpr hR.2.ne')
    field_simp [hdenV, hdenR]

theorem lrLowYTangentCoeff_hasSum
    {R v t : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1)
    (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasSum (fun n : ℕ ↦ lrLowYTangentCoeff v (t ^ 2) n * R ^ n)
      (lrLowYTangent R v t / (1 - R) ^ 2) := by
  have hp := lrLowP_derivative_hasSum hR hv ht
  have hb := lrLowB_derivative_hasSum hR
  have h := hp.sub (hb.mul_left (4 * lrFlowM v * t ^ 2))
  convert h using 1
  · funext n
    unfold lrLowYTangentCoeff
    ring
  · unfold lrLowYTangent
    have hdenR : (1 - R) ^ 2 ≠ 0 :=
      pow_ne_zero 2 (sub_ne_zero.mpr hR.2.ne')
    field_simp [hdenR]

lemma lrLow_cauchy_power_identity
    (a b : ℕ → ℝ) (R : ℝ) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1),
        (a k * R ^ k) * (b (n - k) * R ^ (n - k)) =
      (∑ k ∈ Finset.range (n + 1), a k * b (n - k)) * R ^ n := by
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  have hkLt : k < n + 1 := Finset.mem_range.mp hk
  have hkLe : k ≤ n := by omega
  have hpow : R ^ k * R ^ (n - k) = R ^ n := by
    rw [← pow_add, Nat.add_sub_of_le hkLe]
  calc
    _ = a k * b (n - k) * (R ^ k * R ^ (n - k)) := by ring
    _ = _ := by rw [hpow]

theorem lrLowVConvolutionCoeff_hasSum
    {R v t : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1)
    (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasSum (fun n : ℕ ↦ lrLowVConvolutionCoeff v t n * R ^ n)
      (lrLowVReserve R v t / (1 - R) ^ 2) := by
  let d : ℕ → ℝ := fun n ↦ lrLowDFlowCoeff v t n * R ^ n
  let f : ℕ → ℝ := fun n ↦
    lrLowFDerivCoeff v (t ^ 2) (lrGShape t v) n * R ^ n
  let b : ℕ → ℝ := fun n ↦
    lrLowBFlowCoeff (lrFlowBeta v) (v ^ 2 * t ^ 2) n * R ^ n
  let y : ℕ → ℝ := fun n ↦ lrLowYTangentCoeff v (t ^ 2) n * R ^ n
  have hd : HasSum d (lrFlowD R v t) := by
    simpa [d] using lrLowDFlowCoeff_hasSum hR hv ht
  have hf : HasSum f (lrFlowC R v t / (1 - R) ^ 2) := by
    simpa [f] using lrLowFDerivCoeff_hasSum hR hv ht
  have hb : HasSum b (lrFlowB R v t) := by
    simpa [b] using lrLowBFlowCoeff_hasSum hR hv ht
  have hy : HasSum y (lrLowYTangent R v t / (1 - R) ^ 2) := by
    simpa [y] using lrLowYTangentCoeff_hasSum hR hv ht
  have hdfProd : Summable (fun q : ℕ × ℕ ↦ d q.1 * f q.2) :=
    summable_mul_of_summable_norm hd.summable.norm hf.summable.norm
  have hbyProd : Summable (fun q : ℕ × ℕ ↦ b q.1 * y q.2) :=
    summable_mul_of_summable_norm hb.summable.norm hy.summable.norm
  have hdfSumm : Summable (fun n : ℕ ↦
      ∑ k ∈ Finset.range (n + 1), d k * f (n - k)) :=
    summable_sum_mul_range_of_summable_mul hdfProd
  have hbySumm : Summable (fun n : ℕ ↦
      ∑ k ∈ Finset.range (n + 1), b k * y (n - k)) :=
    summable_sum_mul_range_of_summable_mul hbyProd
  have hdfValue := hd.summable.tsum_mul_tsum_eq_tsum_sum_range
    hf.summable hdfProd
  have hbyValue := hb.summable.tsum_mul_tsum_eq_tsum_sum_range
    hy.summable hbyProd
  rw [hd.tsum_eq, hf.tsum_eq] at hdfValue
  rw [hb.tsum_eq, hy.tsum_eq] at hbyValue
  have hdf : HasSum (fun n : ℕ ↦
      ∑ k ∈ Finset.range (n + 1), d k * f (n - k))
      (lrFlowD R v t * (lrFlowC R v t / (1 - R) ^ 2)) := by
    rw [hdfValue]
    exact hdfSumm.hasSum
  have hby : HasSum (fun n : ℕ ↦
      ∑ k ∈ Finset.range (n + 1), b k * y (n - k))
      (lrFlowB R v t * (lrLowYTangent R v t / (1 - R) ^ 2)) := by
    rw [hbyValue]
    exact hbySumm.hasSum
  have hsum := hdf.add hby
  convert hsum using 1
  · funext n
    dsimp [d, f, b, y]
    unfold lrLowVConvolutionCoeff
    rw [lrLow_cauchy_power_identity, lrLow_cauchy_power_identity]
    ring
  · unfold lrLowVReserve
    have hden : (1 - R) ^ 2 ≠ 0 :=
      pow_ne_zero 2 (sub_ne_zero.mpr hR.2.ne')
    field_simp [hden]

end CourtadeKumar
