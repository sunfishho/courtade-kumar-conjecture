import InformationTheory.CourtadeKumar.LRCompactVLambdaGroupedCore

/-! Keep the complete shape entropy and truncate only the channel correction.
The omitted correction has a uniform, exponentially small negative budget. -/
open Set
open scoped BigOperators
namespace CourtadeKumar.LRAnalyticCompact

noncomputable def channelU (R : ℝ) (n : ℕ) : ℝ := 1 - lrCompactVScore R n

noncomputable def restoredTerm (R v x : ℝ) (n : ℕ) : ℝ :=
  lrLowA n * channelU R n * (4 * v * x / (1 + v) - lrCompactVT v x n)

noncomputable def restoredHead (N : ℕ) (R v x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range N, restoredTerm R v x (j + 1)

noncomputable def tailDelta (N : ℕ) : ℝ := (1 / 2 : ℝ) ^ (2 * N + 1)

noncomputable def restoredQLower (N : ℕ) (R v t : ℝ) : ℝ :=
  topPhi t + topPhi (v * t) / v -
    4 * v * t ^ 2 / (1 + v) * Real.log 2 + restoredHead N R v (t ^ 2) -
    tailDelta N * Real.log 2

lemma channelU_bounds {R : ℝ} (hR : R ∈ Icc (0 : ℝ) 1)
    {n : ℕ} (hn : 1 ≤ n) : 0 ≤ channelU R n ∧ channelU R n ≤ 1 := by
  unfold channelU
  constructor
  · exact sub_nonneg.mpr (lrCompactVScore_le_one hR hn)
  · linarith [lrCompactVScore_nonneg hR.1 hn]

lemma channelU_formula (R : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    channelU R n = R ^ (n - 1) * (1 + ((n : ℝ) - 1) * (1 - R)) := by
  unfold channelU lrCompactVScore
  rw [show R ^ n = R ^ (n - 1) * R by
    nth_rewrite 1 [show n = (n - 1) + 1 by omega]
    exact pow_succ R (n - 1)]
  ring

lemma shape_cubic_budget {v : ℝ} (hv : v ∈ Icc (1 / 2 : ℝ) 1) :
    1 + v ^ 3 ≤ 4 * v / (1 + v) := by
  have hv0 : 0 ≤ v := by linarith [hv.1]
  have hden : 0 < 1 + v := by linarith
  rw [le_div_iff₀ hden]
  have hp : 0 ≤ v ^ 3 + 2 * v ^ 2 + 2 * v - 1 := by
    nlinarith [pow_nonneg hv0 3, sq_nonneg v, hv.1]
  have hmul := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hv.2) hp
  nlinarith

lemma shape_tail_budget {v x : ℝ} {N n : ℕ}
    (hv : v ∈ Icc (1 / 3 : ℝ) 1) (hx : x ∈ Icc (0 : ℝ) 1)
    (hN : 1 ≤ N) (hn : N + 1 ≤ n) :
    lrCompactVT v x n ≤ 4 * v * x / (1 + v) + tailDelta N := by
  have hv0 : 0 ≤ v := by linarith [hv.1]
  have hden : 0 < 1 + v := by linarith
  have hn1 : 1 ≤ n := by omega
  have hxpow : x ^ n ≤ x := by
    simpa using pow_le_pow_of_le_one hx.1 hx.2 hn1
  have hfirst : lrCompactVT v x n ≤ x * (1 + v ^ (2 * n - 1)) := by
    exact mul_le_mul_of_nonneg_right hxpow (by positivity)
  have hdelta : 0 ≤ tailDelta N := by unfold tailDelta; positivity
  by_cases hvhalf : v ≤ 1 / 2
  · have hg : 1 ≤ 4 * v / (1 + v) := by
      rw [le_div_iff₀ hden]
      linarith [hv.1]
    have hvpow : v ^ (2 * n - 1) ≤ tailDelta N := by
      unfold tailDelta
      exact (pow_le_pow_left₀ hv0 hvhalf _).trans
        (pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega))
    have hxp := mul_le_mul_of_nonneg_left hvpow hx.1
    have hdp := mul_le_mul_of_nonneg_right hx.2 hdelta
    have hgp := mul_le_mul_of_nonneg_right hg hx.1
    rw [show 4 * v * x / (1 + v) = 4 * v / (1 + v) * x by ring]
    nlinarith
  · have hcube := shape_cubic_budget ⟨(lt_of_not_ge hvhalf).le, hv.2⟩
    have hvpow : v ^ (2 * n - 1) ≤ v ^ 3 :=
      pow_le_pow_of_le_one hv0 hv.2 (by omega)
    have hxp := mul_le_mul_of_nonneg_left (hvpow.trans (by linarith : v ^ 3 ≤ 4 * v / (1 + v) - 1)) hx.1
    rw [show 4 * v * x / (1 + v) = 4 * v / (1 + v) * x by ring]
    nlinarith

lemma coefficient_hasSum : HasSum (fun j : ℕ => lrLowA (j + 1)) (Real.log 2) := by
  convert top_hasSum_phiCoefficients using 1
  funext j
  unfold lrLowA
  norm_num only [Nat.cast_add, Nat.cast_one]

lemma restoredTerm_hasSum {R v t : ℝ}
    (hR : R ∈ Ioo (0 : ℝ) 1) (hv : v ∈ Ioo (0 : ℝ) 1)
    (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasSum (fun j : ℕ => restoredTerm R v (t ^ 2) (j + 1))
      ((4 * v * t ^ 2 / (1 + v)) * (Real.log 2 - lrWKernel R 1) -
        (topPhi t + topPhi (v * t) / v - lrFlowPW R v t)) := by
  have hU := coefficient_hasSum.sub (lrCompactVWOneTerm_hasSum hR)
  have hT := (lrCompactVT_hasSum hv ht).sub (lrCompactVPWTerm_hasSum hR hv ht)
  have h := (hU.mul_left (4 * v * t ^ 2 / (1 + v))).sub hT
  convert h using 1
  funext j
  unfold restoredTerm channelU lrCompactVWTerm lrCompactVPWTerm
  simp only [one_pow]
  ring

theorem restoredQLower_le {R v t : ℝ} {N : ℕ}
    (hR : R ∈ Ioo (0 : ℝ) 1) (hv : v ∈ Ioo (0 : ℝ) 1)
    (hvlo : 1 / 3 ≤ v) (ht : t ∈ Ioo (0 : ℝ) 1) (hN : 1 ≤ N) :
    restoredQLower N R v t ≤
      lrFlowPW R v t - 4 * lrWKernel R 1 * (v * t ^ 2 / (1 + v)) := by
  have hx : t ^ 2 ∈ Icc (0 : ℝ) 1 := ⟨sq_nonneg t, by nlinarith [ht.1, ht.2]⟩
  have hdelta : 0 ≤ tailDelta N := by unfold tailDelta; positivity
  have hseries := (restoredTerm_hasSum hR hv ht).add
    (coefficient_hasSum.mul_left (tailDelta N))
  have htail := (hasSum_nat_add_iff' N).2 hseries
  have htail0 := htail.nonneg (by
    intro j
    have hn : N + 1 ≤ j + N + 1 := by omega
    have hshape := shape_tail_budget ⟨hvlo, hv.2.le⟩ hx hN hn
    have hu := channelU_bounds ⟨hR.1.le, hR.2.le⟩ (show 1 ≤ j + N + 1 by omega)
    have ha := (lrLowA_pos (show 1 ≤ j + N + 1 by omega)).le
    have hm := mul_le_mul_of_nonneg_left hshape hu.1
    have hdu := mul_le_mul_of_nonneg_left hu.2 hdelta
    have hsmall : 0 ≤ channelU R (j + N + 1) *
        (4 * v * t ^ 2 / (1 + v) - lrCompactVT v (t ^ 2) (j + N + 1)) + tailDelta N := by
      nlinarith
    have hfinal := mul_nonneg ha hsmall
    unfold restoredTerm
    nlinarith)
  have hhead0 : 0 ≤ ∑ j ∈ Finset.range N, tailDelta N * lrLowA (j + 1) := by
    exact Finset.sum_nonneg (fun j _ => mul_nonneg hdelta (lrLowA_pos (by omega)).le)
  rw [Finset.sum_add_distrib] at htail0
  unfold restoredQLower restoredHead
  rw [show 4 * lrWKernel R 1 * (v * t ^ 2 / (1 + v)) =
    (4 * v * t ^ 2 / (1 + v)) * lrWKernel R 1 by ring]
  nlinarith only [htail0, hhead0]

end CourtadeKumar.LRAnalyticCompact
