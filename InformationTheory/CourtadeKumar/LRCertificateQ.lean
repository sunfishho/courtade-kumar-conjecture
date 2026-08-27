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

/-- The scalar `Q` used in the midpoint and determinant certificate ledgers. -/
noncomputable def lrCertificateQ (y : ℝ) : ℝ :=
  topJ (Real.sqrt (1 - y))

/-- The manuscript expression for `Q'`. -/
noncomputable def lrCertificateQPrime (y : ℝ) : ℝ :=
  topPsiDeriv (1 - y)

/-- The manuscript expression for `Q''`. -/
noncomputable def lrCertificateQSecond (y : ℝ) : ℝ :=
  -topPsiDeriv2 (1 - y)

lemma lrCertificateQ_eq (y : ℝ) :
    lrCertificateQ y = Real.log 2 - topPhi (Real.sqrt (1 - y)) := by
  unfold lrCertificateQ topJ
  ring

lemma lrCertificateQPrime_eq (y : ℝ) :
    lrCertificateQPrime y =
      Real.artanh (Real.sqrt (1 - y)) /
        (2 * Real.sqrt (1 - y)) := by
  rfl

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
