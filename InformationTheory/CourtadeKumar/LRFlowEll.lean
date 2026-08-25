import InformationTheory.CourtadeKumar.LRFlowCharts
import Mathlib.Analysis.Convex.Deriv

/-! Monotonicity and convexity of the target level `ell(p)`. -/

open Set

namespace CourtadeKumar

noncomputable def lrFlowEllDeriv (R p : ℝ) : ℝ :=
  (1 - R) * Real.log (1 - p) / p ^ 2 -
    4 * (R * Real.log 2 - topPhi (Real.sqrt R))

noncomputable def lrFlowEllDeriv2 (R p : ℝ) : ℝ :=
  (1 - R) *
    (-p / (1 - p) - 2 * Real.log (1 - p)) / p ^ 3

theorem hasDerivAt_lrPrefixEll
    {R p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (lrPrefixEll R) (lrFlowEllDeriv R p) p := by
  have hp0 : p ≠ 0 := hp.1.ne'
  have hp1 : p ≠ 1 := hp.2.ne
  have hentropy := Real.hasDerivAt_binEntropy hp0 hp1
  have hquot := hentropy.div (hasDerivAt_id p) hp0
  have hfirst := hquot.const_mul (1 - R)
  have hsecond := ((hasDerivAt_const p 1).sub (hasDerivAt_id p)).mul_const
    (4 * (R * Real.log 2 - topPhi (Real.sqrt R)))
  have h := hfirst.add hsecond
  unfold lrPrefixEll lrFlowEllDeriv
  convert h using 1
  · funext q
    simp only [Pi.add_apply, Pi.div_apply, Pi.sub_apply, id_eq]
    ring
  · simp only [id_eq]
    rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
    simp only [Real.negMulLog_eq_neg]
    field_simp [hp0]
    ring

theorem hasDerivAt_lrFlowEllDeriv
    {R p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (lrFlowEllDeriv R) (lrFlowEllDeriv2 R p) p := by
  have hp0 : p ≠ 0 := hp.1.ne'
  have hp1 : 1 - p ≠ 0 := sub_ne_zero.mpr hp.2.ne'
  have honeMinus : HasDerivAt (fun q : ℝ ↦ 1 - q) (-1) p := by
    convert (hasDerivAt_const p 1).sub (hasDerivAt_id p) using 1
    all_goals ring
  have hlog := honeMinus.log hp1
  have hsq := (hasDerivAt_id p).pow 2
  have hquot := hlog.div hsq (pow_ne_zero 2 hp0)
  have h := (hquot.const_mul (1 - R)).sub_const
    (4 * (R * Real.log 2 - topPhi (Real.sqrt R)))
  unfold lrFlowEllDeriv lrFlowEllDeriv2
  convert h using 1
  · funext q
    simp only [Pi.div_apply, Pi.pow_apply, id_eq]
    ring
  · simp only [Pi.pow_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub,
      pow_one, mul_one]
    field_simp [hp0, hp1]

lemma lrFlowEllDeriv2_nonneg
    {R p : ℝ} (hR : R ∈ Icc (0 : ℝ) 1)
    (hp : p ∈ Ioc (0 : ℝ) (1 / 2 : ℝ)) :
    0 ≤ lrFlowEllDeriv2 R p := by
  have honeMinus : 0 < 1 - p := by linarith [hp.2]
  have hlog := Real.log_le_sub_one_of_pos honeMinus
  have hfrac : p / (1 - p) ≤ 2 * p := by
    rw [div_le_iff₀ honeMinus]
    nlinarith [hp.1, hp.2]
  have hlog' : Real.log (1 - p) ≤ -p := by linarith
  have hnum : 0 ≤ -p / (1 - p) - 2 * Real.log (1 - p) := by
    have hleft : -2 * p ≤ -p / (1 - p) := by
      convert neg_le_neg hfrac using 1 <;> ring
    have hright : 2 * p ≤ -2 * Real.log (1 - p) := by
      have hmul := mul_le_mul_of_nonpos_left hlog'
        (by norm_num : (-2 : ℝ) ≤ 0)
      simpa using hmul
    linarith
  unfold lrFlowEllDeriv2
  exact div_nonneg (mul_nonneg (sub_nonneg.mpr hR.2) hnum)
    (pow_nonneg hp.1.le 3)

lemma lrFlowEllDeriv_neg
    {R p : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1)
    (hp : p ∈ Ioc (0 : ℝ) (1 / 2 : ℝ)) :
    lrFlowEllDeriv R p < 0 := by
  have honeMinus : 0 < 1 - p := by linarith [hp.2]
  have hlog : Real.log (1 - p) < 0 := Real.log_neg honeMinus (by linarith [hp.1])
  have hs : 0 < 1 - R := sub_pos.mpr hR.2
  have hrho : Real.sqrt R ∈ Icc (0 : ℝ) 1 := by
    constructor
    · exact Real.sqrt_nonneg R
    · exact (Real.sqrt_le_one).2 hR.2.le
  have henergy := topEnergy_nonneg hrho
    (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 by simp)
  have hsqrtSq : Real.sqrt R ^ 2 = R := Real.sq_sqrt hR.1.le
  have hlambda : 0 ≤ R * Real.log 2 - topPhi (Real.sqrt R) := by
    simpa [topEnergy, topR, hsqrtSq, topPhi_one] using henergy
  unfold lrFlowEllDeriv
  have hfirst : (1 - R) * Real.log (1 - p) / p ^ 2 < 0 := by
    exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hs hlog)
      (sq_pos_of_pos hp.1)
  linarith

theorem strictAntiOn_lrPrefixEll
    {R : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1) :
    StrictAntiOn (lrPrefixEll R) (Ioc (0 : ℝ) (1 / 2 : ℝ)) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioc (0 : ℝ) (1 / 2 : ℝ))
  · intro p hp
    exact (hasDerivAt_lrPrefixEll
      ⟨hp.1, hp.2.trans_lt (by norm_num)⟩).continuousAt.continuousWithinAt
  · intro p hp
    rw [interior_Ioc] at hp
    rw [(hasDerivAt_lrPrefixEll
      ⟨hp.1, lt_trans hp.2 (by norm_num)⟩).deriv]
    exact lrFlowEllDeriv_neg hR ⟨hp.1, hp.2.le⟩

theorem convexOn_lrPrefixEll
    {R : ℝ} (hR : R ∈ Icc (0 : ℝ) 1) :
    ConvexOn ℝ (Ioc (0 : ℝ) (1 / 2 : ℝ)) (lrPrefixEll R) := by
  apply convexOn_of_hasDerivWithinAt2_nonneg
    (convex_Ioc (0 : ℝ) (1 / 2 : ℝ))
  · intro p hp
    exact (hasDerivAt_lrPrefixEll
      ⟨hp.1, lt_of_le_of_lt hp.2 (by norm_num)⟩).continuousAt.continuousWithinAt
  · intro p hp
    rw [interior_Ioc] at hp
    exact (hasDerivAt_lrPrefixEll
      ⟨hp.1, lt_trans hp.2 (by norm_num)⟩).hasDerivWithinAt
  · intro p hp
    rw [interior_Ioc] at hp
    exact (hasDerivAt_lrFlowEllDeriv
      ⟨hp.1, lt_trans hp.2 (by norm_num)⟩).hasDerivWithinAt
  · intro p hp
    rw [interior_Ioc] at hp
    exact lrFlowEllDeriv2_nonneg hR ⟨hp.1, hp.2.le⟩

end CourtadeKumar
