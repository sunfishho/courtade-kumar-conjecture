import InformationTheory.CourtadeKumar.SingleRayEulerSecantReduction
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Integral-average representation of radial entropy-ratio losses. -/

open Set
open scoped Interval

namespace CourtadeKumar

noncomputable def radialEulerWeight (c r z : ℝ) : ℝ :=
  radialEulerDefect c r z / z ^ 2

noncomputable def radialEulerLogWeight (c r z : ℝ) : ℝ :=
  (-(1 / 2 : ℝ) *
      Real.log ((1 - z) ^ 2 - c ^ 2 * r ^ 2 * z ^ 2)) / z ^ 2

theorem radialEulerWeight_eq_logWeight
    {c r z : ℝ}
    (hminus : (1 - c * r) * z ∈ Ioo (0 : ℝ) 1)
    (hplus : (1 + c * r) * z ∈ Ioo (0 : ℝ) 1) :
    radialEulerWeight c r z = radialEulerLogWeight c r z := by
  unfold radialEulerWeight radialEulerLogWeight
  rw [radialEulerDefect_eq_log hminus hplus]

lemma radialEulerLogArg_pos_physical
    {c r z : ℝ}
    (hminus : (1 - c * r) * z ∈ Ioo (0 : ℝ) 1)
    (hplus : (1 + c * r) * z ∈ Ioo (0 : ℝ) 1) :
    0 < radialEulerLogArg c r z := by
  have hleft : 0 < 1 - (1 - c * r) * z := by linarith [hminus.2]
  have hright : 0 < 1 - (1 + c * r) * z := by linarith [hplus.2]
  unfold radialEulerLogArg
  rw [show (1 - z) ^ 2 - c ^ 2 * r ^ 2 * z ^ 2 =
    (1 - (1 - c * r) * z) * (1 - (1 + c * r) * z) by ring]
  exact mul_pos hleft hright

lemma continuousAt_radialEulerLogWeight
    {c r z : ℝ}
    (hz : z ≠ 0)
    (hminus : (1 - c * r) * z ∈ Ioo (0 : ℝ) 1)
    (hplus : (1 + c * r) * z ∈ Ioo (0 : ℝ) 1) :
    ContinuousAt (radialEulerLogWeight c r) z := by
  have hleft : 0 < 1 - (1 - c * r) * z := by linarith [hminus.2]
  have hright : 0 < 1 - (1 + c * r) * z := by linarith [hplus.2]
  have harg : 0 < (1 - z) ^ 2 - c ^ 2 * r ^ 2 * z ^ 2 := by
    rw [show (1 - z) ^ 2 - c ^ 2 * r ^ 2 * z ^ 2 =
      (1 - (1 - c * r) * z) * (1 - (1 + c * r) * z) by ring]
    exact mul_pos hleft hright
  unfold radialEulerLogWeight
  have hpoly : ContinuousAt
      (fun w : ℝ ↦ (1 - w) ^ 2 - c ^ 2 * r ^ 2 * w ^ 2) z := by
    fun_prop
  have hlog : ContinuousAt
      (fun w : ℝ ↦ Real.log ((1 - w) ^ 2 - c ^ 2 * r ^ 2 * w ^ 2)) z :=
    hpoly.log harg.ne'
  exact (continuousAt_const.mul hlog).div (continuousAt_id.pow 2)
    (pow_ne_zero 2 hz)

theorem continuousOn_radialEulerRatio_physical
    {rho r M z : ℝ}
    (hrho : rho ∈ Icc (0 : ℝ) 1)
    (hr : r ∈ Ioo (0 : ℝ) 1)
    (hM : 0 < M)
    (hzupper : z < (1 + r)⁻¹) :
    ContinuousOn (radialEulerRatio rho r) (Icc M z) := by
  have hargs : ∀ x ∈ Icc M z,
      (1 - rho * r) * x ∈ Ioo (0 : ℝ) 1 ∧
        (1 + rho * r) * x ∈ Ioo (0 : ℝ) 1 ∧
        (1 - r) * x ∈ Ioo (0 : ℝ) 1 ∧
        (1 + r) * x ∈ Ioo (0 : ℝ) 1 := by
    intro x hx
    exact radialEntropyArgs_physical hrho hr
      ⟨hM.trans_le hx.1, hx.2.trans_lt hzupper⟩
  have hlog : ContinuousOn (radialEulerLogRatio rho r) (Icc M z) := by
    intro x hx
    obtain ⟨hRminus, hRplus, hminus, hplus⟩ := hargs x hx
    have hargR := (radialEulerLogArg_pos_physical hRminus hRplus).ne'
    have harg1 := (radialEulerLogArg_pos_physical
      (c := (1 : ℝ)) (r := r) (z := x)
      (by simpa using hminus) (by simpa using hplus)).ne'
    have hden := (radialEulerLog_pos
      (c := (1 : ℝ)) (r := r) (z := x)
      (by simpa using hminus) (by simpa using hplus)).ne'
    exact (hasDerivAt_radialEulerLogRatio hargR harg1 hden).continuousAt.continuousWithinAt
  apply hlog.congr
  intro x hx
  obtain ⟨hRminus, hRplus, hminus, hplus⟩ := hargs x hx
  exact radialEulerRatio_eq_logRatio hRminus hRplus hminus hplus

theorem existsUnique_radialEulerRatio_eq_budget
    {rho r M z budget : ℝ}
    (hrho : rho ∈ Ico (0 : ℝ) 1)
    (hr : r ∈ Ioo (0 : ℝ) 1)
    (hM : 0 < M) (hMz : M < z)
    (hzupper : z < (1 + r)⁻¹)
    (hleft : budget < radialEulerRatio rho r M)
    (hright : radialEulerRatio rho r z < budget) :
    ∃! τ, τ ∈ Ioo M z ∧ radialEulerRatio rho r τ = budget := by
  have hcont := continuousOn_radialEulerRatio_physical
    (show rho ∈ Icc (0 : ℝ) 1 from ⟨hrho.1, hrho.2.le⟩)
    hr hM hzupper
  have hbudget : budget ∈ Icc
      (radialEulerRatio rho r z) (radialEulerRatio rho r M) :=
    ⟨hright.le, hleft.le⟩
  obtain ⟨τ, hτIcc, hτeq⟩ :=
    (intermediate_value_Icc' hMz.le hcont) hbudget
  have hMτ : M < τ := by
    apply lt_of_le_of_ne hτIcc.1
    intro hEq
    subst τ
    linarith
  have hτz : τ < z := by
    apply lt_of_le_of_ne hτIcc.2
    intro hEq
    subst τ
    linarith
  refine ⟨τ, ⟨⟨hMτ, hτz⟩, hτeq⟩, ?_⟩
  intro y hy
  have hyDom : y ∈ Ioo (0 : ℝ) (1 + r)⁻¹ :=
    ⟨hM.trans hy.1.1, hy.1.2.trans hzupper⟩
  have hτDom : τ ∈ Ioo (0 : ℝ) (1 + r)⁻¹ :=
    ⟨hM.trans hMτ, hτz.trans hzupper⟩
  apply (radialEulerRatio_strictAntiOn_physical hrho hr).injOn
    hyDom hτDom
  rw [hy.2, hτeq]

/-- The loss of radial entropy per unit mass is the interval integral of
its positive Euler weight. -/
theorem radialNatEntropyRatio_loss_eq_integral
    {c r M z : ℝ}
    (hc : c ∈ Icc (0 : ℝ) 1)
    (hr : r ∈ Ioo (0 : ℝ) 1)
    (hM : 0 < M) (hMz : M < z)
    (hzupper : z < (1 + r)⁻¹) :
    radialNatEntropyRatio c r M - radialNatEntropyRatio c r z =
      ∫ t in M..z, radialEulerLogWeight c r t := by
  have hargs : ∀ x ∈ Icc M z,
      (1 - c * r) * x ∈ Ioo (0 : ℝ) 1 ∧
        (1 + c * r) * x ∈ Ioo (0 : ℝ) 1 := by
    intro x hx
    obtain ⟨hminus, hplus, _, _⟩ := radialEntropyArgs_physical hc hr
      ⟨hM.trans_le hx.1, hx.2.trans_lt hzupper⟩
    exact ⟨hminus, hplus⟩
  have hcontRatio : ContinuousOn (radialNatEntropyRatio c r) (Icc M z) := by
    intro x hx
    exact (hasDerivAt_radialNatEntropyRatio
      (ne_of_gt (hM.trans_le hx.1)) (hargs x hx).1
        (hargs x hx).2).continuousAt.continuousWithinAt
  have hcontWeight : ContinuousOn (radialEulerLogWeight c r) (Icc M z) := by
    intro x hx
    exact (continuousAt_radialEulerLogWeight
      (ne_of_gt (hM.trans_le hx.1)) (hargs x hx).1 (hargs x hx).2)
        |>.continuousWithinAt
  have hint : IntervalIntegrable (radialEulerLogWeight c r)
      MeasureTheory.volume M z := by
    rw [← uIcc_of_le hMz.le] at hcontWeight
    exact hcontWeight.intervalIntegrable
  have hderiv : ∀ x ∈ Ioo M z,
      HasDerivAt (radialNatEntropyRatio c r)
        (-radialEulerLogWeight c r x) x := by
    intro x hx
    have hxIcc : x ∈ Icc M z := ⟨hx.1.le, hx.2.le⟩
    have hd := hasDerivAt_radialNatEntropyRatio
      (ne_of_gt (hM.trans hx.1)) (hargs x hxIcc).1 (hargs x hxIcc).2
    convert hd using 1
    rw [← radialEulerWeight_eq_logWeight (hargs x hxIcc).1 (hargs x hxIcc).2]
    unfold radialEulerWeight
    ring
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    hMz.le hcontRatio hderiv hint.neg
  rw [intervalIntegral.integral_neg] at hftc
  linarith

/-- Pointwise, the output Euler weight is the input Euler weight multiplied
by the Euler ratio. -/
theorem radialEulerLogWeight_factor
    {rho r z : ℝ}
    (hRminus : (1 - rho * r) * z ∈ Ioo (0 : ℝ) 1)
    (hRplus : (1 + rho * r) * z ∈ Ioo (0 : ℝ) 1)
    (hminus : (1 - r) * z ∈ Ioo (0 : ℝ) 1)
    (hplus : (1 + r) * z ∈ Ioo (0 : ℝ) 1) :
    radialEulerLogWeight rho r z =
      radialEulerRatio rho r z * radialEulerLogWeight 1 r z := by
  rw [← radialEulerWeight_eq_logWeight hRminus hRplus,
    ← radialEulerWeight_eq_logWeight (by simpa using hminus)
      (by simpa using hplus)]
  have hD1 : radialEulerDefect 1 r z ≠ 0 :=
    (radialEulerDefect_pos (by simpa using hminus)
      (by simpa using hplus)).ne'
  unfold radialEulerWeight radialEulerRatio
  field_simp [hD1]

theorem radialEulerLogWeight_pos
    {c r z : ℝ}
    (hz : z ≠ 0)
    (hminus : (1 - c * r) * z ∈ Ioo (0 : ℝ) 1)
    (hplus : (1 + c * r) * z ∈ Ioo (0 : ℝ) 1) :
    0 < radialEulerLogWeight c r z := by
  rw [← radialEulerWeight_eq_logWeight hminus hplus]
  unfold radialEulerWeight
  exact div_pos (radialEulerDefect_pos hminus hplus)
    (sq_pos_of_ne_zero hz)

/-- The quotient of the two Euler-weight integrals.  The factorization above
makes this a positive-weight average of `radialEulerRatio` on `[M,z]`. -/
noncomputable def radialEulerWeightedAverage
    (rho r M z : ℝ) : ℝ :=
  (∫ t in M..z, radialEulerLogWeight rho r t) /
    ∫ t in M..z, radialEulerLogWeight 1 r t

theorem radialEulerWeightedAverage_eq_ratioLoss
    {rho r M z : ℝ}
    (hrho : rho ∈ Icc (0 : ℝ) 1)
    (hr : r ∈ Ioo (0 : ℝ) 1)
    (hM : 0 < M) (hMz : M < z)
    (hzupper : z < (1 + r)⁻¹) :
    radialEulerWeightedAverage rho r M z =
      (radialNatEntropyRatio rho r M -
          radialNatEntropyRatio rho r z) /
        (radialNatEntropyRatio 1 r M -
          radialNatEntropyRatio 1 r z) := by
  rw [radialNatEntropyRatio_loss_eq_integral hrho hr hM hMz hzupper,
    radialNatEntropyRatio_loss_eq_integral
      (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 by simp) hr hM hMz hzupper]
  rfl

theorem integral_radialEulerLogWeight_eq_ratio_mul_inputWeight
    {rho r M z : ℝ}
    (hrho : rho ∈ Icc (0 : ℝ) 1)
    (hr : r ∈ Ioo (0 : ℝ) 1)
    (hM : 0 < M) (hMz : M < z)
    (hzupper : z < (1 + r)⁻¹) :
    (∫ t in M..z, radialEulerLogWeight rho r t) =
      ∫ t in M..z,
        radialEulerRatio rho r t * radialEulerLogWeight 1 r t := by
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le hMz.le] at ht
  obtain ⟨hRminus, hRplus, hminus, hplus⟩ :=
    radialEntropyArgs_physical hrho hr
      ⟨hM.trans_le ht.1, ht.2.trans_lt hzupper⟩
  exact radialEulerLogWeight_factor hRminus hRplus hminus hplus

theorem integral_radialEulerLogWeight_one_pos
    {r M z : ℝ}
    (hr : r ∈ Ioo (0 : ℝ) 1)
    (hM : 0 < M) (hMz : M < z)
    (hzupper : z < (1 + r)⁻¹) :
    0 < ∫ t in M..z, radialEulerLogWeight 1 r t := by
  rw [← radialNatEntropyRatio_loss_eq_integral
    (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 by simp) hr hM hMz hzupper]
  exact radialNatEntropyRatio_one_loss_pos hr hM hMz hzupper

/-- Cumulative slack in the proposed Euler-average bound.  Through the
pointwise factorization it is the input-Euler-weighted signed area between
the budget and the Euler-ratio curve. -/
noncomputable def radialEulerCumulativeSurplus
    (rho r M z budget : ℝ) : ℝ :=
  budget * (∫ t in M..z, radialEulerLogWeight 1 r t) -
    ∫ t in M..z, radialEulerLogWeight rho r t

noncomputable def radialEulerAlgebraicSurplus
    (rho r M z budget : ℝ) : ℝ :=
  budget * (radialNatEntropyRatio 1 r M -
      radialNatEntropyRatio 1 r z) -
    (radialNatEntropyRatio rho r M -
      radialNatEntropyRatio rho r z)

theorem radialEulerCumulativeSurplus_eq_algebraic
    {rho r M z budget : ℝ}
    (hrho : rho ∈ Icc (0 : ℝ) 1)
    (hr : r ∈ Ioo (0 : ℝ) 1)
    (hM : 0 < M) (hMz : M < z)
    (hzupper : z < (1 + r)⁻¹) :
    radialEulerCumulativeSurplus rho r M z budget =
      radialEulerAlgebraicSurplus rho r M z budget := by
  unfold radialEulerCumulativeSurplus radialEulerAlgebraicSurplus
  rw [radialNatEntropyRatio_loss_eq_integral hrho hr hM hMz hzupper,
    radialNatEntropyRatio_loss_eq_integral
      (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 by simp) hr hM hMz hzupper]

/-- The cumulative surplus grows exactly where the budget lies above the
current Euler ratio.  This is the differential crossing law needed for a
second-order area argument. -/
theorem hasDerivAt_radialEulerAlgebraicSurplus
    {rho r M z budget : ℝ}
    (hz : z ≠ 0)
    (hRminus : (1 - rho * r) * z ∈ Ioo (0 : ℝ) 1)
    (hRplus : (1 + rho * r) * z ∈ Ioo (0 : ℝ) 1)
    (hminus : (1 - r) * z ∈ Ioo (0 : ℝ) 1)
    (hplus : (1 + r) * z ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun w ↦ radialEulerAlgebraicSurplus rho r M w budget)
      ((budget - radialEulerRatio rho r z) *
        radialEulerLogWeight 1 r z) z := by
  have hRraw := hasDerivAt_radialNatEntropyRatio hz hRminus hRplus
  have h1raw := hasDerivAt_radialNatEntropyRatio
    (c := (1 : ℝ)) (r := r) hz
    (by simpa using hminus) (by simpa using hplus)
  have hR : HasDerivAt (radialNatEntropyRatio rho r)
      (-radialEulerLogWeight rho r z) z := by
    convert hRraw using 1
    rw [← radialEulerWeight_eq_logWeight hRminus hRplus]
    unfold radialEulerWeight
    ring
  have h1 : HasDerivAt (radialNatEntropyRatio 1 r)
      (-radialEulerLogWeight 1 r z) z := by
    convert h1raw using 1
    rw [← radialEulerWeight_eq_logWeight (by simpa using hminus)
      (by simpa using hplus)]
    unfold radialEulerWeight
    ring
  have hinput := (hasDerivAt_const z (radialNatEntropyRatio 1 r M)).sub h1
  have houtput :=
    (hasDerivAt_const z (radialNatEntropyRatio rho r M)).sub hR
  have htotal := hinput.const_mul budget |>.sub houtput
  have hfactor := radialEulerLogWeight_factor
    hRminus hRplus hminus hplus
  unfold radialEulerAlgebraicSurplus
  convert htotal using 1
  rw [hfactor]
  ring

/-- Around a strict Euler-budget crossing the cumulative surplus is
V-shaped: strictly decreasing before the crossing and strictly increasing
after it. -/
theorem radialEulerAlgebraicSurplus_strictVShape
    {rho r M z budget τ : ℝ}
    (hrho : rho ∈ Ico (0 : ℝ) 1)
    (hr : r ∈ Ioo (0 : ℝ) 1)
    (hM : 0 < M) (hMτ : M < τ) (hτz : τ < z)
    (hzupper : z < (1 + r)⁻¹)
    (hcross : radialEulerRatio rho r τ = budget) :
    StrictAntiOn
        (fun w ↦ radialEulerAlgebraicSurplus rho r M w budget) (Icc M τ) ∧
      StrictMonoOn
        (fun w ↦ radialEulerAlgebraicSurplus rho r M w budget) (Icc τ z) := by
  have hrhoIcc : rho ∈ Icc (0 : ℝ) 1 := ⟨hrho.1, hrho.2.le⟩
  have hargs : ∀ x ∈ Icc M z,
      (1 - rho * r) * x ∈ Ioo (0 : ℝ) 1 ∧
        (1 + rho * r) * x ∈ Ioo (0 : ℝ) 1 ∧
        (1 - r) * x ∈ Ioo (0 : ℝ) 1 ∧
        (1 + r) * x ∈ Ioo (0 : ℝ) 1 := by
    intro x hx
    exact radialEntropyArgs_physical hrhoIcc hr
      ⟨hM.trans_le hx.1, hx.2.trans_lt hzupper⟩
  have hτDom : τ ∈ Ioo (0 : ℝ) (1 + r)⁻¹ :=
    ⟨hM.trans hMτ, hτz.trans hzupper⟩
  have hcontinuous : ∀ {a b : ℝ}, Icc a b ⊆ Icc M z →
      ContinuousOn
        (fun w ↦ radialEulerAlgebraicSurplus rho r M w budget) (Icc a b) := by
    intro a b hsub x hx
    have hxMz := hsub hx
    obtain ⟨hRminus, hRplus, hminus, hplus⟩ := hargs x hxMz
    exact (hasDerivAt_radialEulerAlgebraicSurplus
      (M := M) (budget := budget) (ne_of_gt (hM.trans_le hxMz.1))
        hRminus hRplus hminus hplus).continuousAt.continuousWithinAt
  constructor
  · apply strictAntiOn_of_deriv_neg (convex_Icc M τ)
      (hcontinuous (by intro x hx; exact ⟨hx.1, hx.2.trans hτz.le⟩))
    intro x hx
    rw [interior_Icc] at hx
    have hxMz : x ∈ Icc M z := ⟨hx.1.le, hx.2.le.trans hτz.le⟩
    obtain ⟨hRminus, hRplus, hminus, hplus⟩ := hargs x hxMz
    have hslope := hasDerivAt_radialEulerAlgebraicSurplus
      (M := M) (budget := budget) (ne_of_gt (hM.trans hx.1))
        hRminus hRplus hminus hplus
    rw [hslope.deriv]
    have hxDom : x ∈ Ioo (0 : ℝ) (1 + r)⁻¹ :=
      ⟨hM.trans hx.1, hx.2.trans hτDom.2⟩
    have hratio : budget < radialEulerRatio rho r x := by
      rw [← hcross]
      exact radialEulerRatio_strictAntiOn_physical hrho hr
        hxDom hτDom hx.2
    have hweight : 0 < radialEulerLogWeight 1 r x :=
      radialEulerLogWeight_pos (ne_of_gt (hM.trans hx.1))
        (by simpa using hminus) (by simpa using hplus)
    exact mul_neg_of_neg_of_pos (sub_neg.mpr hratio) hweight
  · apply strictMonoOn_of_deriv_pos (convex_Icc τ z)
      (hcontinuous (by intro x hx; exact ⟨hMτ.le.trans hx.1, hx.2⟩))
    intro x hx
    rw [interior_Icc] at hx
    have hxMz : x ∈ Icc M z := ⟨hMτ.le.trans hx.1.le, hx.2.le⟩
    obtain ⟨hRminus, hRplus, hminus, hplus⟩ := hargs x hxMz
    have hslope := hasDerivAt_radialEulerAlgebraicSurplus
      (M := M) (budget := budget) (ne_of_gt (hM.trans_le hxMz.1))
        hRminus hRplus hminus hplus
    rw [hslope.deriv]
    have hxDom : x ∈ Ioo (0 : ℝ) (1 + r)⁻¹ :=
      ⟨hτDom.1.trans hx.1, hx.2.trans hzupper⟩
    have hratio : radialEulerRatio rho r x < budget := by
      rw [← hcross]
      exact radialEulerRatio_strictAntiOn_physical hrho hr
        hτDom hxDom hx.1
    have hweight : 0 < radialEulerLogWeight 1 r x :=
      radialEulerLogWeight_pos (ne_of_gt (hM.trans_le hxMz.1))
        (by simpa using hminus) (by simpa using hplus)
    exact mul_pos (sub_pos.mpr hratio) hweight

theorem radialEulerWeightedAverage_le_iff_cumulativeSurplus_nonneg
    {rho r M z budget : ℝ}
    (hr : r ∈ Ioo (0 : ℝ) 1)
    (hM : 0 < M) (hMz : M < z)
    (hzupper : z < (1 + r)⁻¹) :
    radialEulerWeightedAverage rho r M z ≤ budget ↔
      0 ≤ radialEulerCumulativeSurplus rho r M z budget := by
  have hden := integral_radialEulerLogWeight_one_pos hr hM hMz hzupper
  unfold radialEulerWeightedAverage radialEulerCumulativeSurplus
  rw [div_le_iff₀ hden]
  constructor <;> intro h <;> linarith

/-- On a strict contact, corrected-reserve positivity is exactly an upper
bound on the Euler ratio averaged with the intrinsic input Euler weight. -/
theorem singleRayCorrectedReserve_nonneg_iff_weightedEulerAverage
    {rho M r z : ℝ}
    (hrho : rho ∈ Icc (0 : ℝ) 1)
    (hM : M ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (hr : r ∈ Ioo (0 : ℝ) 1)
    (hz : z ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (hMz : M < z)
    (hcontact : M / z * radialNatEntropy 1 r z =
      (lowerRayNatEnvelope rho (M * (1 - r)) +
        lowerRayNatEnvelope rho (M * (1 + r))) / 2) :
    0 ≤ singleRayCorrectedReserve rho M r z (M / z) ↔
      radialEulerWeightedAverage rho r M z ≤
        singleRayClosedEulerSlopeBudget rho M r := by
  have hzupper := strictRayContact_upper hr hz
  have hinput := radialNatEntropyRatio_one_loss_pos
    hr hM.1 hMz hzupper
  have hcz : M = M / z * z := by field_simp [hz.1.ne']
  have hreserve :=
    singleRayCorrectedReserve_eq_mass_mul_outputRatioGap_of_contact
      hM.1.ne' hz.1.ne' hcz hcontact
  have havg := radialEulerWeightedAverage_eq_ratioLoss
    hrho hr hM.1 hMz hzupper
  have hbudget := singleRayEulerSlopeBudget_eq_closed_of_contact
    hM hr hz hMz hcontact
  rw [hreserve, mul_nonneg_iff_of_pos_left hM.1, ← hbudget, havg]
  change (0 ≤ radialNatEntropyRatio rho r z -
      lowerRayNatEnvelope rho M / M) ↔ _
  unfold singleRayEulerSlopeBudget
  rw [div_le_div_iff_of_pos_right hinput]
  constructor <;> intro h <;> linarith

/-- Final cumulative form of the strict corrected reserve.  The remaining
analytic task is exactly nonnegativity of this integrated Euler surplus. -/
theorem singleRayCorrectedReserve_nonneg_iff_cumulativeEulerSurplus
    {rho M r z : ℝ}
    (hrho : rho ∈ Icc (0 : ℝ) 1)
    (hM : M ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (hr : r ∈ Ioo (0 : ℝ) 1)
    (hz : z ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (hMz : M < z)
    (hcontact : M / z * radialNatEntropy 1 r z =
      (lowerRayNatEnvelope rho (M * (1 - r)) +
        lowerRayNatEnvelope rho (M * (1 + r))) / 2) :
    0 ≤ singleRayCorrectedReserve rho M r z (M / z) ↔
      0 ≤ radialEulerCumulativeSurplus rho r M z
        (singleRayClosedEulerSlopeBudget rho M r) := by
  rw [singleRayCorrectedReserve_nonneg_iff_weightedEulerAverage
    hrho hM hr hz hMz hcontact]
  exact radialEulerWeightedAverage_le_iff_cumulativeSurplus_nonneg
    hr hM.1 hMz (strictRayContact_upper hr hz)

/-- Easy contact regime: if the explicit budget already dominates the
Euler ratio at the left endpoint, strict decrease makes the whole weighted
average admissible. -/
theorem singleRayCorrectedReserve_nonneg_of_leftEndpointEulerRatio_le
    {rho M r z : ℝ}
    (hrho : rho ∈ Ico (0 : ℝ) 1)
    (hM : M ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (hr : r ∈ Ioo (0 : ℝ) 1)
    (hz : z ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (hMz : M < z)
    (hcontact : M / z * radialNatEntropy 1 r z =
      (lowerRayNatEnvelope rho (M * (1 - r)) +
        lowerRayNatEnvelope rho (M * (1 + r))) / 2)
    (hleft : radialEulerRatio rho r M ≤
      singleRayClosedEulerSlopeBudget rho M r) :
    0 ≤ singleRayCorrectedReserve rho M r z (M / z) := by
  have hzupper := strictRayContact_upper hr hz
  obtain ⟨ξ, hξ, hratio⟩ := exists_radialEulerRatio_eq_ratioLoss
    ⟨hrho.1, hrho.2.le⟩ hr hM.1 hMz hzupper
  have havg := radialEulerWeightedAverage_eq_ratioLoss
    ⟨hrho.1, hrho.2.le⟩ hr hM.1 hMz hzupper
  have hMdom : M ∈ Ioo (0 : ℝ) (1 + r)⁻¹ :=
    ⟨hM.1, hMz.trans hzupper⟩
  have hξdom : ξ ∈ Ioo (0 : ℝ) (1 + r)⁻¹ :=
    ⟨hM.1.trans hξ.1, hξ.2.trans hzupper⟩
  have hdecrease : radialEulerRatio rho r ξ <
      radialEulerRatio rho r M :=
    radialEulerRatio_strictAntiOn_physical hrho hr hMdom hξdom hξ.1
  apply (singleRayCorrectedReserve_nonneg_iff_weightedEulerAverage
    ⟨hrho.1, hrho.2.le⟩ hM hr hz hMz hcontact).2
  rw [havg, hratio]
  exact hdecrease.le.trans hleft

end CourtadeKumar
