import InformationTheory.CourtadeKumar.LRCertificateQFunctionCore
import InformationTheory.CourtadeKumar.TopCapPrimitive
import InformationTheory.CourtadeKumar.ChannelCap

/-!
# The entropy scalar used by the LR certificates

This file identifies the manuscript's scalar
`Q(y) = log 2 - topPhi (sqrt (1-y))` with the entropy functions already used
by the formal LR flow.  Its first two derivatives are expressed through the
existing `topPsiDeriv` and `topPsiDeriv2`; consequently the numerical checker
and the analytic LR argument refer to exactly the same function.
-/

open Set

namespace CourtadeKumar

/-- The manuscript expression for `Q''`. -/
noncomputable def lrCertificateQSecond (y : ℝ) : ℝ :=
  -topPsiDeriv2 (1 - y)

lemma lrCertificateQ_eq (y : ℝ) :
    lrCertificateQ y = Real.log 2 - topPhi (Real.sqrt (1 - y)) := by
  unfold lrCertificateQ topJ
  ring

@[simp] lemma lrCertificateQ_zero : lrCertificateQ 0 = 0 := by
  rw [lrCertificateQ_eq]
  norm_num [topPhi_one]

lemma lrCertificateQSecond_eq {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    lrCertificateQSecond y =
      (Real.artanh (Real.sqrt (1 - y)) - Real.sqrt (1 - y) / y) /
        (4 * Real.sqrt (1 - y) ^ 3) := by
  have hsqrtSq : Real.sqrt (1 - y) ^ 2 = 1 - y :=
    Real.sq_sqrt (by linarith [hy.2])
  have hyNe : y ≠ 0 := hy.1.ne'
  unfold lrCertificateQSecond topPsiDeriv2 topPsiSlopeGap
  rw [hsqrtSq]
  field_simp [hyNe]
  ring

theorem hasDerivAt_lrCertificateQ {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt lrCertificateQ (lrCertificateQPrime y) y := by
  have hinner : HasDerivAt (fun z : ℝ ↦ 1 - z) (-1) y :=
    (hasDerivAt_id y).const_sub 1
  have harg : 1 - y ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · linarith [hy.2]
    · linarith [hy.1]
  have hphi := (hasDerivAt_topPsi harg).comp y hinner
  have h := (hasDerivAt_const y (Real.log 2)).sub hphi
  rw [show lrCertificateQ =
      fun z : ℝ ↦ Real.log 2 - topPhi (Real.sqrt (1 - z)) from
    funext lrCertificateQ_eq]
  unfold lrCertificateQPrime
  convert h using 1
  all_goals ring

theorem hasDerivAt_lrCertificateQPrime
    {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt lrCertificateQPrime (lrCertificateQSecond y) y := by
  have hinner : HasDerivAt (fun z : ℝ ↦ 1 - z) (-1) y :=
    (hasDerivAt_id y).const_sub 1
  have harg : 1 - y ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · linarith [hy.2]
    · linarith [hy.1]
  have h := (hasDerivAt_topPsiDeriv harg).comp y hinner
  unfold lrCertificateQPrime lrCertificateQSecond
  convert h using 1
  all_goals ring

lemma lrCertificateQPrime_pos {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    0 < lrCertificateQPrime y := by
  have harg : 1 - y ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · linarith [hy.2]
    · linarith [hy.1]
  have hsqrtPos : 0 < Real.sqrt (1 - y) := Real.sqrt_pos.2 (by linarith [hy.2])
  have hsqrtLt : Real.sqrt (1 - y) < 1 := by
    simpa using (Real.sqrt_lt_sqrt_iff harg.1.le).2 harg.2
  rw [lrCertificateQPrime_eq]
  exact div_pos (Real.artanh_pos ⟨hsqrtPos, hsqrtLt⟩) (by positivity)

lemma lrCertificateQ_nonneg {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    0 ≤ lrCertificateQ y := by
  have hsqrtNonneg : 0 ≤ Real.sqrt (1 - y) := Real.sqrt_nonneg _
  have hsqrtLe : Real.sqrt (1 - y) ≤ 1 := by
    rw [Real.sqrt_le_one]
    linarith [hy.1]
  rw [lrCertificateQ, topJ_eq_binEntropy]
  apply Real.binEntropy_nonneg
  · linarith
  · linarith

private lemma negMulLog_le_two_sqrt_sub_two_mul {p : ℝ}
    (hp : p ∈ Ioc (0 : ℝ) 1) :
    Real.negMulLog p ≤ 2 * Real.sqrt p - 2 * p := by
  have hpPos : 0 < p := hp.1
  have hsPos : 0 < Real.sqrt p := Real.sqrt_pos.2 hpPos
  have hlog := Real.log_le_sub_one_of_pos (inv_pos.2 hsPos)
  rw [Real.log_inv, Real.log_sqrt hpPos.le] at hlog
  have hscaled := mul_le_mul_of_nonneg_left hlog hpPos.le
  rw [Real.negMulLog_eq_neg]
  have hsquare : Real.sqrt p ^ 2 = p := Real.sq_sqrt hpPos.le
  field_simp [hsPos.ne'] at hscaled ⊢
  nlinarith

private lemma negMulLog_one_sub_le {p : ℝ} (hp : p ∈ Ico (0 : ℝ) 1) :
    Real.negMulLog (1 - p) ≤ p := by
  have hqPos : 0 < 1 - p := sub_pos.mpr hp.2
  have hlog := Real.log_le_sub_one_of_pos (inv_pos.2 hqPos)
  rw [Real.log_inv] at hlog
  have hscaled := mul_le_mul_of_nonneg_left hlog hqPos.le
  rw [Real.negMulLog_eq_neg]
  field_simp [hqPos.ne'] at hscaled
  nlinarith

private lemma binEntropy_le_two_sqrt {p : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) :
    Real.binEntropy p ≤ 2 * Real.sqrt p := by
  rcases hp with ⟨hp0, hp1⟩
  by_cases hpz : p = 0
  · subst p
    simp
  by_cases hpo : p = 1
  · subst p
    norm_num
  have hpPos : 0 < p := lt_of_le_of_ne hp0 (Ne.symm hpz)
  have hpLt : p < 1 := lt_of_le_of_ne hp1 hpo
  have hfirst := negMulLog_le_two_sqrt_sub_two_mul ⟨hpPos, hp1⟩
  have hsecond := negMulLog_one_sub_le ⟨hp0, hpLt⟩
  rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  linarith

/-- A log-free endpoint majorant.  It is intentionally coarse but tends to
zero uniformly, unlike a generic logarithm payload at a vanishing input. -/
lemma lrCertificateQ_le_two_sqrt {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    lrCertificateQ y ≤ 2 * Real.sqrt y := by
  let p := (1 - Real.sqrt (1 - y)) / 2
  have hsNonneg : 0 ≤ Real.sqrt (1 - y) := Real.sqrt_nonneg _
  have hsLe : Real.sqrt (1 - y) ≤ 1 := by
    rw [Real.sqrt_le_one]
    linarith [hy.1]
  have hpMem : p ∈ Icc (0 : ℝ) 1 := by
    dsimp [p]
    constructor <;> linarith
  have hpLeY : p ≤ y := by
    have hsquare : Real.sqrt (1 - y) ^ 2 = 1 - y :=
      Real.sq_sqrt (by linarith [hy.2])
    dsimp [p]
    nlinarith [sq_nonneg (Real.sqrt (1 - y) - 1)]
  have hsqrtMono : Real.sqrt p ≤ Real.sqrt y :=
    Real.sqrt_le_sqrt hpLeY
  rw [lrCertificateQ, topJ_eq_binEntropy]
  exact (binEntropy_le_two_sqrt hpMem).trans
    (mul_le_mul_of_nonneg_left hsqrtMono (by norm_num))

lemma lrCertificateQSecond_nonpos {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    lrCertificateQSecond y ≤ 0 := by
  unfold lrCertificateQSecond
  exact neg_nonpos.mpr (topPsiDeriv2_nonneg
    (show 1 - y ∈ Ioo (0 : ℝ) 1 by
      constructor
      · linarith [hy.2]
      · linarith [hy.1]))

/-- The elementary lower bound `(C3)` used by the exact interval ledgers. -/
lemma lrCertificateQSecond_lower {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    -1 / (4 * y) ≤ lrCertificateQSecond y := by
  let z := Real.sqrt (1 - y)
  have hzPos : 0 < z := Real.sqrt_pos.2 (by linarith [hy.2])
  have hzLt : z < 1 := by
    have harg : 1 - y ∈ Ioo (0 : ℝ) 1 := by
      constructor
      · linarith [hy.2]
      · linarith [hy.1]
    simpa [z] using (Real.sqrt_lt_sqrt_iff harg.1.le).2 harg.2
  have hzSq : z ^ 2 = 1 - y := by
    dsimp [z]
    exact Real.sq_sqrt (by linarith [hy.2])
  have hyNe : y ≠ 0 := hy.1.ne'
  have hdenPos : 0 < 4 * z ^ 3 := by positivity
  rw [lrCertificateQSecond_eq hy]
  change -1 / (4 * y) ≤
    (Real.artanh z - z / y) / (4 * z ^ 3)
  rw [le_div_iff₀ hdenPos]
  have hart : z ≤ Real.artanh z := (self_lt_artanh ⟨hzPos, hzLt⟩).le
  have hid : -1 / (4 * y) * (4 * z ^ 3) = z - z / y := by
    field_simp [hyNe]
    nlinarith [hzSq]
  rw [hid]
  linarith

/-- The endpoint entropy scalar is concave on its full closed domain.  This
form is useful when a derivative is singular at `0`, because a secant from
the endpoint still controls the derivative at every positive point. -/
theorem lrCertificateQ_concaveOn :
    ConcaveOn ℝ (Icc (0 : ℝ) 1) lrCertificateQ := by
  have hcontinuous : Continuous lrCertificateQ := by
    rw [show lrCertificateQ = fun y : ℝ ↦
        Real.log 2 - topPhi (Real.sqrt (1 - y)) from
      funext lrCertificateQ_eq]
    exact continuous_const.sub
      (continuous_topPhi.comp
        (Real.continuous_sqrt.comp (continuous_const.sub continuous_id)))
  apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc 0 1)
    hcontinuous.continuousOn
  · intro y hy
    rw [interior_Icc] at hy
    exact (hasDerivAt_lrCertificateQ hy).hasDerivWithinAt
  · intro y hy
    rw [interior_Icc] at hy
    exact (hasDerivAt_lrCertificateQPrime hy).hasDerivWithinAt
  · intro y hy
    rw [interior_Icc] at hy
    exact lrCertificateQSecond_nonpos hy

/-- Cancellation-safe endpoint bound for the formally singular factor
`Q'(y)`: multiplication by `y` makes it no larger than `Q(y)`. -/
lemma lrCertificateQ_mul_prime_le {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    y * lrCertificateQPrime y ≤ lrCertificateQ y := by
  have hslope := lrCertificateQ_concaveOn.le_slope_of_hasDerivAt
    (x := (0 : ℝ)) (y := y) (by simp) ⟨hy.1.le, hy.2.le⟩ hy.1
    (hasDerivAt_lrCertificateQ hy)
  rw [slope, lrCertificateQ_zero] at hslope
  have hslope' : lrCertificateQPrime y ≤ lrCertificateQ y / y := by
    simpa [div_eq_mul_inv, mul_comm] using hslope
  rw [le_div_iff₀ hy.1] at hslope'
  simpa [mul_comm] using hslope'

/-- Closed-at-zero version of the endpoint product bound. -/
lemma lrCertificateQ_mul_prime_mem {y : ℝ} (hy : y ∈ Ico (0 : ℝ) 1) :
    y * lrCertificateQPrime y ∈ Icc (0 : ℝ) (lrCertificateQ y) := by
  rcases eq_or_lt_of_le hy.1 with rfl | hyPos
  · simp
  · have hyOpen : y ∈ Ioo (0 : ℝ) 1 := ⟨hyPos, hy.2⟩
    exact ⟨mul_nonneg hyPos.le (lrCertificateQPrime_pos hyOpen).le,
      lrCertificateQ_mul_prime_le hyOpen⟩

theorem lrCertificateQ_strictMonoOn :
    StrictMonoOn lrCertificateQ (Ioo (0 : ℝ) 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioo (0 : ℝ) 1)
  · intro y hy
    exact (hasDerivAt_lrCertificateQ hy).continuousAt.continuousWithinAt
  · intro y hy
    rw [interior_Ioo] at hy
    rw [(hasDerivAt_lrCertificateQ hy).deriv]
    exact lrCertificateQPrime_pos hy

theorem lrCertificateQPrime_antitoneOn :
    AntitoneOn lrCertificateQPrime (Ioo (0 : ℝ) 1) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ioo (0 : ℝ) 1)
  · intro y hy
    exact (hasDerivAt_lrCertificateQPrime hy).continuousAt.continuousWithinAt
  · intro y hy
    rw [interior_Ioo] at hy
    exact (hasDerivAt_lrCertificateQPrime hy).differentiableAt
      |>.differentiableWithinAt
  · intro y hy
    rw [interior_Ioo] at hy
    rw [(hasDerivAt_lrCertificateQPrime hy).deriv]
    exact lrCertificateQSecond_nonpos hy

end CourtadeKumar
