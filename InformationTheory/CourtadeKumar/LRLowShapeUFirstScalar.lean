import InformationTheory.CourtadeKumar.LRLowShapeUDifference

/-! Propagation of the first scalar `U` inequality from its base value using
the certified first-difference minorant. -/

open Set

namespace CourtadeKumar

noncomputable def lrLowLambda (v x G : ℝ) (n : ℕ) : ℝ :=
  lrLowR v x G n + 2 * lrFlowBeta v * lrLowEta v x n

lemma lrLowLambda_step_identity
    {v x G : ℝ} (hv : v ∈ Icc (0 : ℝ) 1)
    (hx : x ∈ Icc (0 : ℝ) 1) (j : ℕ) :
    lrLowLambda v x G (j + 1) - lrLowLambda v x G j =
      lrLowA (j + 1) *
        (lrLowTailH v - lrLowT v x (j + 1) +
          2 * lrFlowBeta v *
            (2 * lrFlowM v * x - lrLowT v x (j + 1))) := by
  have hpRec := lrLowP_recursion hv hx j
  have hbRec := lrLowB_recursion j
  unfold lrLowLambda lrLowR lrLowEta
  rw [hpRec, hbRec]
  ring

lemma lrLowUDifference_rescale
    {v x : ℝ} :
    lrLowUDifference v ((20 / 17 : ℝ) * x) =
      lrLowTailH v - x * (1 + v) -
        2 * lrAtanh5Upper (v / (2 + v)) * x * (1 + v ^ 2) / (1 + v) := by
  unfold lrLowUDifference
  norm_num
  ring

theorem lrLowLambda_step_nonneg
    {v x G : ℝ} (hv : v ∈ Ioc (0 : ℝ) 1)
    (hx : x ∈ Icc (0 : ℝ) (17 / 20)) (j : ℕ) :
    lrLowLambda v x G j ≤ lrLowLambda v x G (j + 1) := by
  have hvClosed : v ∈ Icc (0 : ℝ) 1 := ⟨hv.1.le, hv.2⟩
  have hxUnit : x ∈ Icc (0 : ℝ) 1 :=
    ⟨hx.1, hx.2.trans (by norm_num)⟩
  let z := (20 / 17 : ℝ) * x
  have hz : z ∈ Icc (0 : ℝ) 1 := by
    unfold z
    constructor
    · exact mul_nonneg (by norm_num) hx.1
    · nlinarith [hx.2]
  have hD := lrLowUDifference_nonneg hvClosed hz
  rw [lrLowUDifference_rescale] at hD
  have hbetaBounds := lrAtanh5_beta_bounds hv
  have hbeta : lrFlowBeta v ≤ lrAtanh5Upper (v / (2 + v)) := by
    simpa [lrFlowBeta] using hbetaBounds.2
  have hbeta0 : 0 ≤ lrFlowBeta v := by
    unfold lrFlowBeta
    exact Real.log_nonneg (by linarith [hv.1])
  have hT : lrLowT v x (j + 1) ≤ lrLowT v x 1 :=
    lrLowT_antitone_on_positive hvClosed hxUnit (by norm_num) (by omega)
  have hTOne : lrLowT v x 1 = x * (1 + v) := by
    unfold lrLowT
    norm_num
  have hden : 0 < 1 + v := by linarith [hv.1]
  have hq : 2 * lrFlowM v * x - x * (1 + v) =
      -x * (1 + v ^ 2) / (1 + v) := by
    unfold lrFlowM
    field_simp [hden.ne']
    ring
  have hqNonpos : -x * (1 + v ^ 2) / (1 + v) ≤ 0 := by
    exact div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hx.1)
        (by positivity)) hden.le
  have hbetaReplace :
      2 * lrAtanh5Upper (v / (2 + v)) *
          (-x * (1 + v ^ 2) / (1 + v)) ≤
        2 * lrFlowBeta v * (-x * (1 + v ^ 2) / (1 + v)) := by
    exact mul_le_mul_of_nonpos_right (by nlinarith [hbeta]) hqNonpos
  have hcoreAtOne : 0 ≤
      lrLowTailH v - lrLowT v x 1 +
        2 * lrFlowBeta v * (2 * lrFlowM v * x - lrLowT v x 1) := by
    rw [hTOne, hq]
    calc
      0 ≤ lrLowTailH v - x * (1 + v) -
          2 * lrAtanh5Upper (v / (2 + v)) * x * (1 + v ^ 2) / (1 + v) := hD
      _ = lrLowTailH v - x * (1 + v) +
          2 * lrAtanh5Upper (v / (2 + v)) *
            (-x * (1 + v ^ 2) / (1 + v)) := by ring
      _ ≤ lrLowTailH v - x * (1 + v) +
          2 * lrFlowBeta v * (-x * (1 + v ^ 2) / (1 + v)) :=
        by
          convert add_le_add_left hbetaReplace (lrLowTailH v - x * (1 + v)) using 1 <;>
            ring
  have hTMove :
      (1 + 2 * lrFlowBeta v) * lrLowT v x (j + 1) ≤
        (1 + 2 * lrFlowBeta v) * lrLowT v x 1 :=
    mul_le_mul_of_nonneg_left hT (by linarith [hbeta0])
  have hcore : 0 ≤
      lrLowTailH v - lrLowT v x (j + 1) +
        2 * lrFlowBeta v *
          (2 * lrFlowM v * x - lrLowT v x (j + 1)) := by
    nlinarith [hcoreAtOne, hTMove]
  have hdiff := lrLowLambda_step_identity (G := G) hvClosed hxUnit j
  have ha := (lrLowA_pos (by omega : 1 ≤ j + 1)).le
  apply sub_nonneg.mp
  rw [hdiff]
  exact mul_nonneg ha hcore

theorem lrLowLambda_monotone
    {v x G : ℝ} (hv : v ∈ Ioc (0 : ℝ) 1)
    (hx : x ∈ Icc (0 : ℝ) (17 / 20)) :
    Monotone (lrLowLambda v x G) := by
  exact monotone_nat_of_le_succ (lrLowLambda_step_nonneg hv hx)

theorem lrLowLambda_nonneg_of_one
    {v x G : ℝ} (hv : v ∈ Ioc (0 : ℝ) 1)
    (hx : x ∈ Icc (0 : ℝ) (17 / 20))
    (hone : 0 ≤ lrLowLambda v x G 1)
    {n : ℕ} (hn : 1 ≤ n) :
    0 ≤ lrLowLambda v x G n :=
  hone.trans (lrLowLambda_monotone hv hx hn)

end CourtadeKumar
