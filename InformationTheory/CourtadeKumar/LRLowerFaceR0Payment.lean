import InformationTheory.CourtadeKumar.LRLowerFaceR0PrimeBound
import InformationTheory.CourtadeKumar.LRLowShapeSeriesBounds

/-!
# Entropy-remainder payment on the lower midpoint face

This file turns the differential facts for `r₀` into the lower bound used in
manuscript inequality (M24).  The endpoint at zero is handled analytically;
no numerical decision procedure is involved.
-/

open Set

namespace CourtadeKumar

noncomputable def lrLowerFaceR0PFormula (y : ℝ) : ℝ :=
  let p := lrLowerFaceP y
  p * Real.negMulLog p +
    (1 - p) * Real.negMulLog (1 - p) - p * (1 - p)

lemma lrLowerFaceR0_eq_pFormula
    {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    lrLowerFaceR0 y = lrLowerFaceR0PFormula y := by
  let p := lrLowerFaceP y
  let z := Real.sqrt (1 - y)
  have hgeom := lrLowerFaceP_geometry hy
  change p ∈ Ioo (0 : ℝ) (1 / 2) ∧
    1 - 2 * p = z ∧ y = 4 * p * (1 - p) at hgeom
  have hp := hgeom.1
  have hpOnePos : 0 < 1 - p := sub_pos.mpr (hp.2.trans (by norm_num))
  have hfour : 4 / y = 1 / (p * (1 - p)) := by
    rw [hgeom.2.2]
    field_simp [hp.1.ne', hpOnePos.ne']
  have hQ : lrCertificateQ y = Real.binEntropy p := by
    rw [lrCertificateQ, topJ_eq_binEntropy]
    change Real.binEntropy ((1 - z) / 2) = Real.binEntropy p
    congr 1
  have hlog : Real.log (4 / y) = -Real.log p - Real.log (1 - p) := by
    rw [hfour, Real.log_div (by norm_num : (1 : ℝ) ≠ 0)
      (mul_ne_zero hp.1.ne' hpOnePos.ne'),
      Real.log_mul hp.1.ne' hpOnePos.ne']
    norm_num
    ring
  unfold lrLowerFaceR0 lrLowerFaceQ0 lrLowerFaceR0PFormula
  change lrCertificateQ y - y / 4 * (Real.log (4 / y) + 1) =
    p * Real.negMulLog p +
      (1 - p) * Real.negMulLog (1 - p) - p * (1 - p)
  rw [hQ, hlog, hgeom.2.2,
    Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  simp only [Real.negMulLog_eq_neg]
  ring

@[simp] lemma lrLowerFaceR0_zero : lrLowerFaceR0 0 = 0 := by
  simp [lrLowerFaceR0, lrCertificateQ, lrLowerFaceQ0, topJ]

@[simp] lemma lrLowerFaceR0PFormula_zero : lrLowerFaceR0PFormula 0 = 0 := by
  simp [lrLowerFaceR0PFormula, lrLowerFaceP]

lemma lrLowerFaceR0_nonneg
    {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    0 ≤ lrLowerFaceR0 y := by
  let p := lrLowerFaceP y
  have hgeom := lrLowerFaceP_geometry hy
  change p ∈ Ioo (0 : ℝ) (1 / 2) ∧ _ at hgeom
  have hp := hgeom.1
  have hpOnePos : 0 < 1 - p := sub_pos.mpr (hp.2.trans (by norm_num))
  have hlogP := Real.log_le_sub_one_of_pos hp.1
  have hlogOne := Real.log_le_sub_one_of_pos hpOnePos
  have hfirst : p ^ 2 * (1 - p) ≤ p * Real.negMulLog p := by
    have hneg : 1 - p ≤ -Real.log p := by linarith
    have hscaled := mul_le_mul_of_nonneg_left hneg (sq_nonneg p)
    simp only [Real.negMulLog_eq_neg]
    nlinarith
  have hsecond : p * (1 - p) ^ 2 ≤
      (1 - p) * Real.negMulLog (1 - p) := by
    have hneg : p ≤ -Real.log (1 - p) := by linarith
    have hscaled := mul_le_mul_of_nonneg_left hneg (sq_nonneg (1 - p))
    simp only [Real.negMulLog_eq_neg]
    nlinarith
  rw [lrLowerFaceR0_eq_pFormula hy]
  unfold lrLowerFaceR0PFormula
  change 0 ≤ p * Real.negMulLog p +
    (1 - p) * Real.negMulLog (1 - p) - p * (1 - p)
  have hnonnegFirst : 0 ≤ p * Real.negMulLog p := by
    exact mul_nonneg hp.1.le
      (Real.negMulLog_nonneg hp.1.le (hp.2.le.trans (by norm_num)))
  have hsum : p ^ 2 * (1 - p) + p * (1 - p) ^ 2 = p * (1 - p) := by
    ring
  linarith

lemma continuous_lrLowerFaceR0PFormula :
    Continuous lrLowerFaceR0PFormula := by
  unfold lrLowerFaceR0PFormula lrLowerFaceP
  fun_prop

lemma continuousWithinAt_lrLowerFaceR0_zero :
    ContinuousWithinAt lrLowerFaceR0 (Ico (0 : ℝ) 1) 0 := by
  apply (continuous_lrLowerFaceR0PFormula.continuousAt).continuousWithinAt.congr
  · intro y hy
    rcases hy.1.eq_or_lt with rfl | hyPos
    · simp
    · exact lrLowerFaceR0_eq_pFormula ⟨hyPos, hy.2⟩
  · simp

lemma continuousWithinAt_lrLowerFaceOmegaR0_zero
    {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    ContinuousWithinAt (lrLowerFaceOmegaR0 s) (Ico (0 : ℝ) 1) 0 := by
  have hb : ContinuousAt (lrCertificateB s) 0 := by
    unfold lrCertificateB
    fun_prop
  have hBs : lrCertificateB s 0 = s := by simp [lrCertificateB]
  have hrb : ContinuousWithinAt
      (fun y ↦ lrLowerFaceR0 (lrCertificateB s y)) (Ico (0 : ℝ) 1) 0 := by
    have hout : ContinuousAt lrLowerFaceR0 (lrCertificateB s 0) := by
      rw [hBs]
      exact (hasDerivAt_lrLowerFaceR0 hs).continuousAt
    exact hout.comp_continuousWithinAt hb.continuousWithinAt
  have hry := continuousWithinAt_lrLowerFaceR0_zero
  have hrpb : ContinuousWithinAt
      (fun y ↦ lrLowerFaceR0Prime (lrCertificateB s y)) (Ico (0 : ℝ) 1) 0 := by
    have hout : ContinuousAt lrLowerFaceR0Prime (lrCertificateB s 0) := by
      rw [hBs]
      exact (hasDerivAt_lrLowerFaceR0Prime hs).continuousAt
    exact hout.comp_continuousWithinAt hb.continuousWithinAt
  unfold lrLowerFaceOmegaR0
  exact (hrb.sub hry).sub
    (((continuousWithinAt_const.mul
      (continuousWithinAt_const.sub continuousWithinAt_id)).mul hrpb))

/-- The monotonicity of the remainder kernel extends to the singular endpoint
`y=0`; this is the endpoint step implicit in (M24). -/
theorem lrLowerFaceOmegaR0_monotoneOn_Ico
    {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    MonotoneOn (lrLowerFaceOmegaR0 s) (Ico (0 : ℝ) 1) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ico (0 : ℝ) 1)
  · intro y hy
    rcases hy.1.eq_or_lt with rfl | hyPos
    · exact continuousWithinAt_lrLowerFaceOmegaR0_zero hs
    · exact (hasDerivAt_lrLowerFaceOmegaR0 hs ⟨hyPos, hy.2⟩).continuousAt.continuousWithinAt
  · intro y hy
    rw [interior_Ico] at hy
    exact (hasDerivAt_lrLowerFaceOmegaR0 hs hy).differentiableAt.differentiableWithinAt
  · intro y hy
    rw [interior_Ico] at hy
    rw [(hasDerivAt_lrLowerFaceOmegaR0 hs hy).deriv]
    exact lrLowerFaceOmegaR0Deriv_nonneg hs hy

lemma lrLowerFaceOmegaR0_zero_lower
    {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    -s * lrLowerFaceR0Prime s ≤ lrLowerFaceOmegaR0 s 0 := by
  unfold lrLowerFaceOmegaR0 lrCertificateB
  rw [lrLowerFaceR0_zero]
  norm_num
  exact lrLowerFaceR0_nonneg hs

/-- A structural lower bound for the complete remainder contribution. -/
lemma lrLowerFacePWR0_lower
    {s k chi v : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1)
    (hv : 0 < v)
    (hchiE : chi * (s * k) ∈ Ico (0 : ℝ) 1)
    (hE : s * k ∈ Ico (0 : ℝ) 1) :
    -(1 + 1 / v) * s * lrLowerFaceR0Prime s ≤
      lrLowerFacePWR0 s k chi v := by
  have hmono := lrLowerFaceOmegaR0_monotoneOn_Ico hs
  have hzero : (0 : ℝ) ∈ Ico (0 : ℝ) 1 := ⟨le_rfl, by norm_num⟩
  have hchi := hmono hzero hchiE hchiE.1
  have he := hmono hzero hE hE.1
  have hbase := lrLowerFaceOmegaR0_zero_lower hs
  have hfirst : -s * lrLowerFaceR0Prime s ≤
      lrLowerFaceOmegaR0 s (chi * (s * k)) := hbase.trans hchi
  have hsecond : (-s * lrLowerFaceR0Prime s) / v ≤
      lrLowerFaceOmegaR0 s (s * k) / v :=
    div_le_div_of_nonneg_right (hbase.trans he) hv.le
  unfold lrLowerFacePWR0
  have hadd := add_le_add hfirst hsecond
  convert hadd using 1 <;> field_simp [hv.ne'] <;> ring

noncomputable def lrLowerFaceLogWeight (y : ℝ) : ℝ :=
  y * Real.log (4 / y)

lemma hasDerivAt_lrLowerFaceLogWeight
    {y : ℝ} (hy : 0 < y) :
    HasDerivAt lrLowerFaceLogWeight (Real.log (4 / y) - 1) y := by
  have hyNe := hy.ne'
  have hquot : HasDerivAt (fun z : ℝ ↦ 4 / z) (-4 / y ^ 2) y := by
    convert (hasDerivAt_const y (4 : ℝ)).div (hasDerivAt_id y) hyNe using 1 <;>
      simp only [id_eq] <;> field_simp [hyNe] <;> ring
  have hquotNe : 4 / y ≠ 0 := div_ne_zero (by norm_num) hyNe
  have hlog := (Real.hasDerivAt_log hquotNe).comp y hquot
  have hprod := (hasDerivAt_id y).mul hlog
  unfold lrLowerFaceLogWeight
  convert hprod using 1
  simp only [Function.comp_apply, id_eq]
  field_simp [hyNe]
  ring

lemma lrLowerFaceLogWeight_monotoneOn :
    MonotoneOn lrLowerFaceLogWeight (Ioc (0 : ℝ) (1 / 128)) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ioc (0 : ℝ) (1 / 128))
  · intro y hy
    exact (hasDerivAt_lrLowerFaceLogWeight hy.1).continuousAt.continuousWithinAt
  · intro y hy
    rw [interior_Ioc] at hy
    exact (hasDerivAt_lrLowerFaceLogWeight hy.1).differentiableAt.differentiableWithinAt
  · intro y hy
    rw [interior_Ioc] at hy
    rw [(hasDerivAt_lrLowerFaceLogWeight hy.1).deriv]
    have harg : (512 : ℝ) ≤ 4 / y := by
      rw [le_div_iff₀ hy.1]
      nlinarith [hy.2]
    have hlogOrder := Real.log_le_log (by norm_num : (0 : ℝ) < 512) harg
    have hlog512 : Real.log (512 : ℝ) = 9 * Real.log 2 := by
      rw [show (512 : ℝ) = 2 ^ 9 by norm_num, Real.log_pow]
      norm_num
    have hlogTwo := lr_log_two_millionth_bounds.1
    rw [hlog512] at hlogOrder
    linarith

lemma lrLowerFaceLogWeight_upper
    {s : ℝ} (hs : s ∈ Ioc (0 : ℝ) (1 / 128)) :
    lrLowerFaceLogWeight s ≤ 9 * Real.log 2 / 128 := by
  have hmono := lrLowerFaceLogWeight_monotoneOn hs
    (show (1 / 128 : ℝ) ∈ Ioc (0 : ℝ) (1 / 128) by norm_num) hs.2
  have hvalue : lrLowerFaceLogWeight (1 / 128 : ℝ) =
      9 * Real.log 2 / 128 := by
    unfold lrLowerFaceLogWeight
    rw [show (4 : ℝ) / (1 / 128) = 2 ^ 9 by norm_num, Real.log_pow]
    norm_num
    ring
  rwa [hvalue] at hmono

lemma lrLowerFaceR0Prime_payment_upper
    {s : ℝ} (hs : s ∈ Ioc (0 : ℝ) (1 / 128)) :
    lrLowerFaceR0Prime s ≤ (9 * Real.log 2 / 128) / 3 := by
  have hsSixteenth : s ∈ Ioo (0 : ℝ) (1 / 16) :=
    ⟨hs.1, hs.2.trans_lt (by norm_num)⟩
  have hprime := lrLowerFaceR0Prime_upper hsSixteenth
  have hweight := lrLowerFaceLogWeight_upper hs
  unfold lrLowerFaceLogWeight at hweight
  calc
    lrLowerFaceR0Prime s ≤ s / 3 * Real.log (4 / s) := hprime
    _ = (s * Real.log (4 / s)) / 3 := by ring
    _ ≤ (9 * Real.log 2 / 128) / 3 := div_le_div_of_nonneg_right hweight (by norm_num)

/-- Manuscript (M24), with its strict rational constant. -/
theorem lrLowerFacePWR0_payment
    {s k chi v : ℝ}
    (hs : s ∈ Ioc (0 : ℝ) (1 / 128))
    (hk : k ∈ Ioc (0 : ℝ) (1 / 4))
    (hchi : chi ∈ Icc (0 : ℝ) 1)
    (hv : v ∈ Ioc (0 : ℝ) 1)
    (hvSq : (511 / 512 : ℝ) < v ^ 2) :
    -(1023 / 1533 : ℝ) * (9 * Real.log 2 / 128) <
      lrLowerFacePWR0 s k chi v / s := by
  have hsUnit : s ∈ Ioo (0 : ℝ) 1 := ⟨hs.1, hs.2.trans_lt (by norm_num)⟩
  have hePos : 0 < s * k := mul_pos hs.1 hk.1
  have heLe : s * k ≤ (1 / 128 : ℝ) * (1 / 4) :=
    mul_le_mul hs.2 hk.2 hk.1.le (by norm_num)
  have heLt : s * k < 1 := heLe.trans_lt (by norm_num)
  have heMem : s * k ∈ Ico (0 : ℝ) 1 := ⟨hePos.le, heLt⟩
  have hchiEMem : chi * (s * k) ∈ Ico (0 : ℝ) 1 := by
    constructor
    · exact mul_nonneg hchi.1 hePos.le
    · calc
        chi * (s * k) ≤ 1 * (s * k) :=
          mul_le_mul_of_nonneg_right hchi.2 hePos.le
        _ < 1 := by simpa using heLt
  have hpw := lrLowerFacePWR0_lower hsUnit hv.1 hchiEMem heMem
  have hpwDiv : -(1 + 1 / v) * lrLowerFaceR0Prime s ≤
      lrLowerFacePWR0 s k chi v / s := by
    rw [le_div_iff₀ hs.1]
    convert hpw using 1 <;> ring
  have hvLower : (511 / 512 : ℝ) < v := by
    have hvSqLe : v ^ 2 ≤ v := by nlinarith [hv.1, hv.2]
    linarith
  have hinv : 1 / v < (512 / 511 : ℝ) := by
    rw [div_lt_div_iff₀ hv.1 (by norm_num : (0 : ℝ) < 511)]
    nlinarith [hvLower]
  have hcoeff : (1 + 1 / v) / 3 < (1023 / 1533 : ℝ) := by
    nlinarith [hinv]
  have hprime := lrLowerFaceR0Prime_payment_upper hs
  have hlogPos : 0 < 9 * Real.log 2 / 128 := by
    positivity
  have hfactorPos : 0 < 1 + 1 / v := by positivity
  have hprodLe : (1 + 1 / v) * lrLowerFaceR0Prime s ≤
      ((1 + 1 / v) / 3) * (9 * Real.log 2 / 128) := by
    have := mul_le_mul_of_nonneg_left hprime hfactorPos.le
    nlinarith
  have hprodLt : (1 + 1 / v) * lrLowerFaceR0Prime s <
      (1023 / 1533 : ℝ) * (9 * Real.log 2 / 128) :=
    hprodLe.trans_lt (mul_lt_mul_of_pos_right hcoeff hlogPos)
  linarith

end CourtadeKumar
