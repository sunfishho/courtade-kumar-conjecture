import InformationTheory.CourtadeKumar.LRLowShapeUFirstScalar

/-! Analytic bridge from the exact rational `L₁` minorant to the base value
of the first low-shape `U` scalar.  The finite Bernstein check for the
minorant is deliberately kept separate. -/

open Set
open scoped BigOperators

namespace CourtadeKumar

noncomputable def lrLowBetaLower (v : ℝ) : ℝ :=
  lrAtanh5 (v / (2 + v))

noncomputable def lrLowMinusLogLower (v : ℝ) : ℝ :=
  lrAtanh5 ((1 - v) / (1 + v))

noncomputable def lrLowGLower (v : ℝ) : ℝ :=
  (1 + 1 / v) * lrLowBetaLower v + lrLowMinusLogLower v

/-- The retained terms `m=2,...,12` of `p₁`. -/
noncomputable def lrLowP1Lower (v x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range 11,
    lrLowA (k + 2) * lrLowT v x (k + 2)

noncomputable def lrLowB1Upper : ℝ :=
  (693148 : ℝ) / 1000000 - 1 / 2

/-- The manuscript's rational base minorant `𝓛₁`. -/
noncomputable def lrLowL1Minorant (v x : ℝ) : ℝ :=
  lrLowGLower v - lrLowA 1 * lrLowT v x 1 -
    lrLowTailH v * lrLowB1Upper +
    2 * lrLowBetaLower v * lrLowP1Lower v x -
    2 * lrAtanh5Upper (v / (2 + v)) *
      (2 * lrFlowM v * x) * lrLowB1Upper

lemma lrLowBetaLower_nonneg
    {v : ℝ} (hv : v ∈ Ioc (0 : ℝ) 1) :
    0 ≤ lrLowBetaLower v := by
  unfold lrLowBetaLower lrAtanh5
  have hy := (lrBetaRatio_mem_Icc
    (show v ∈ Icc (0 : ℝ) 1 from ⟨hv.1.le, hv.2⟩)).1
  positivity

lemma lrLowGLower_le_lrG
    {v : ℝ} (hv : v ∈ Ioc (0 : ℝ) 1) :
    lrLowGLower v ≤ lrG v := by
  have hbeta := (lrAtanh5_beta_bounds hv).1
  have hminus := lrAtanh5_log_lower hv
  have hfactor : 0 ≤ 1 + 1 / v := by
    exact add_nonneg (by norm_num) (one_div_nonneg.mpr hv.1.le)
  have hscaled := mul_le_mul_of_nonneg_left hbeta hfactor
  unfold lrLowGLower lrLowBetaLower lrLowMinusLogLower lrG
  linarith

lemma lrLowB_one_le_upper : lrLowB 1 ≤ lrLowB1Upper := by
  have hlog := lr_log_two_millionth_bounds.2.le
  unfold lrLowB lrLowB1Upper
  norm_num [lrLowA] at hlog ⊢
  linarith

lemma lrLowB1Upper_nonneg : 0 ≤ lrLowB1Upper := by
  unfold lrLowB1Upper
  norm_num

lemma lrLowP1Lower_nonneg
    {v x : ℝ} (hv : 0 ≤ v) (hx : 0 ≤ x) :
    0 ≤ lrLowP1Lower v x := by
  unfold lrLowP1Lower
  apply Finset.sum_nonneg
  intro k hk
  exact mul_nonneg (lrLowA_pos (by omega)).le (lrLowT_nonneg hv hx _)

lemma lrLowP1Lower_le
    {v x : ℝ} (hv : v ∈ Icc (0 : ℝ) 1)
    (hx : x ∈ Icc (0 : ℝ) 1) :
    lrLowP1Lower v x ≤ lrLowP v x 1 := by
  have hp := lrLowP_hasSum hv hx 1
  have hsum := hp.summable.sum_le_tsum (Finset.range 11) (fun k _ ↦
    mul_nonneg (lrLowA_pos (by omega)).le (lrLowT_nonneg hv.1 hx.1 _))
  rw [hp.tsum_eq] at hsum
  simpa [lrLowP1Lower, add_assoc] using hsum

lemma lrLowP_zero_eq_phi
    {v t : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1)
    (ht : t ∈ Ioc (0 : ℝ) 1) :
    lrLowP v (t ^ 2) 0 = topPhi t + topPhi (v * t) / v := by
  have hx : t ^ 2 ∈ Icc (0 : ℝ) 1 := by
    constructor
    · positivity
    · nlinarith [mul_nonneg ht.1.le (sub_nonneg.mpr ht.2)]
  have hlow := lrLowP_hasSum
    (show v ∈ Icc (0 : ℝ) 1 from ⟨hv.1.le, hv.2.le⟩) hx 0
  have hphi := lrAbelBasePhi_hasSum hv ht
    (show v * t < 1 by
      calc
        v * t ≤ v * 1 := mul_le_mul_of_nonneg_left ht.2 hv.1.le
        _ < 1 := by simpa using hv.2)
  apply HasSum.unique hlow
  convert hphi using 1
  funext k
  unfold lrLowA lrLowT
  norm_num only [Nat.cast_add, Nat.cast_one, zero_add]
  ring

lemma lrGShape_add_p_one
    {v t : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1)
    (ht : t ∈ Ioc (0 : ℝ) 1) :
    lrGShape t v + lrLowP v (t ^ 2) 1 =
      lrG v - lrLowA 1 * lrLowT v (t ^ 2) 1 := by
  have hx : t ^ 2 ∈ Icc (0 : ℝ) 1 := by
    constructor
    · positivity
    · nlinarith [mul_nonneg ht.1.le (sub_nonneg.mpr ht.2)]
  have hrec := lrLowP_recursion
    (show v ∈ Icc (0 : ℝ) 1 from ⟨hv.1.le, hv.2.le⟩) hx 0
  rw [lrLowP_zero_eq_phi hv ht] at hrec
  unfold lrGShape
  linarith

/-- The exact analytic scalar dominates the rational `L₁` minorant. -/
theorem lrLowL1Minorant_le_lambda
    {v t : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1)
    (ht : t ∈ Ioc (0 : ℝ) 1) :
    lrLowL1Minorant v (t ^ 2) ≤
      lrLowLambda v (t ^ 2) (lrGShape t v) 1 := by
  have hvIoc : v ∈ Ioc (0 : ℝ) 1 := ⟨hv.1, hv.2.le⟩
  have hvClosed : v ∈ Icc (0 : ℝ) 1 := ⟨hv.1.le, hv.2.le⟩
  have hx : t ^ 2 ∈ Icc (0 : ℝ) 1 := by
    constructor
    · positivity
    · nlinarith [mul_nonneg ht.1.le (sub_nonneg.mpr ht.2)]
  have hg := lrLowGLower_le_lrG hvIoc
  have hp := lrLowP1Lower_le hvClosed hx
  have hp0 := lrLowP1Lower_nonneg hvClosed.1 hx.1
  have hbetaBounds := lrAtanh5_beta_bounds hvIoc
  have hbeta0 : 0 ≤ lrFlowBeta v := by
    unfold lrFlowBeta
    exact Real.log_nonneg (by linarith [hv.1])
  have hbetaLower : lrLowBetaLower v ≤ lrFlowBeta v := by
    simpa [lrLowBetaLower, lrFlowBeta] using hbetaBounds.1
  have hbetaUpper : lrFlowBeta v ≤ lrAtanh5Upper (v / (2 + v)) := by
    simpa [lrFlowBeta] using hbetaBounds.2
  have hb := lrLowB_one_le_upper
  have hb0 := (lrLowB_pos 1).le
  have hbUpper0 := lrLowB1Upper_nonneg
  have hh0 : 0 ≤ lrLowTailH v :=
    (lrLowTailH_ge_three hvClosed).trans' (by norm_num)
  have hd0 : 0 ≤ 2 * lrFlowM v * t ^ 2 := by
    unfold lrFlowM
    exact mul_nonneg
      (mul_nonneg (by norm_num) (div_nonneg hv.1.le (by linarith [hv.1])))
      (sq_nonneg t)
  have hPProduct :
      lrLowBetaLower v * lrLowP1Lower v (t ^ 2) ≤
        lrFlowBeta v * lrLowP v (t ^ 2) 1 := by
    exact mul_le_mul hbetaLower hp hp0 hbeta0
  have hBProduct :
      lrFlowBeta v * (2 * lrFlowM v * t ^ 2) * lrLowB 1 ≤
        lrAtanh5Upper (v / (2 + v)) *
          (2 * lrFlowM v * t ^ 2) * lrLowB1Upper := by
    have hupper0 : 0 ≤ lrAtanh5Upper (v / (2 + v)) :=
      hbeta0.trans hbetaUpper
    have hfirst := mul_le_mul_of_nonneg_right hbetaUpper hd0
    exact mul_le_mul hfirst hb hb0
      (mul_nonneg hupper0 hd0)
  have hshape := lrGShape_add_p_one hv ht
  unfold lrLowL1Minorant lrLowLambda lrLowR lrLowEta
  rw [hshape]
  nlinarith [mul_le_mul_of_nonneg_left hb hh0, hPProduct, hBProduct]

theorem lrLowLambda_one_nonneg_of_minorant
    {v t : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1)
    (ht : t ∈ Ioc (0 : ℝ) 1)
    (hminorant : 0 ≤ lrLowL1Minorant v (t ^ 2)) :
    0 ≤ lrLowLambda v (t ^ 2) (lrGShape t v) 1 :=
  hminorant.trans (lrLowL1Minorant_le_lambda hv ht)

end CourtadeKumar
