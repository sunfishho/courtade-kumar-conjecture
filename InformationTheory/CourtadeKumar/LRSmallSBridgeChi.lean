import InformationTheory.CourtadeKumar.LRSmallSBridgeCoefficient

/-!
# The `chi log chi` endpoint range in the small-`s` bridge

This formalizes the calculus assertion used in (M28):
`chi log chi / (1+chi)` has one minimum, and that minimum is strictly
larger than `-2/7`.
-/

open Set

namespace CourtadeKumar

noncomputable def lrSmallSBridgeQChi (chi : ℝ) : ℝ :=
  chi * Real.log chi / (1 + chi)

noncomputable def lrSmallSBridgeQChiNumerator (chi : ℝ) : ℝ :=
  Real.log chi + 1 + chi

lemma hasDerivAt_lrSmallSBridgeQChi
    {chi : ℝ} (hchi : 0 < chi) :
    HasDerivAt lrSmallSBridgeQChi
      (lrSmallSBridgeQChiNumerator chi / (1 + chi) ^ 2) chi := by
  have hnum := (hasDerivAt_id chi).mul (Real.hasDerivAt_log hchi.ne')
  have hden := (hasDerivAt_const chi 1).add (hasDerivAt_id chi)
  have hdenNe : 1 + chi ≠ 0 := by linarith
  have h := hnum.div hden hdenNe
  unfold lrSmallSBridgeQChi lrSmallSBridgeQChiNumerator
  convert h using 1
  simp only [Pi.mul_apply, Pi.add_apply, id_eq, one_mul, zero_add]
  field_simp [hdenNe]
  ring

lemma lrSmallSBridgeQChiNumerator_strictMonoOn :
    StrictMonoOn lrSmallSBridgeQChiNumerator (Ioi (0 : ℝ)) := by
  intro a ha b hb hab
  have hlog := Real.strictMonoOn_log ha hb hab
  unfold lrSmallSBridgeQChiNumerator
  linarith

lemma lrSmallSBridgeQChiNumerator_quarter_neg :
    lrSmallSBridgeQChiNumerator (1 / 4 : ℝ) < 0 := by
  have hlog : Real.log (1 / 4 : ℝ) = -2 * Real.log 2 := by
    rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0)
      (by norm_num : (4 : ℝ) ≠ 0),
      show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  unfold lrSmallSBridgeQChiNumerator
  rw [hlog]
  nlinarith [lr_log_two_millionth_bounds.1]

lemma lr_exp_nine_sevenths_gt_seven_halves :
    (7 / 2 : ℝ) < Real.exp (9 / 7) := by
  have hsum := Real.sum_le_exp_of_nonneg
    (show (0 : ℝ) ≤ 9 / 7 by norm_num) 5
  norm_num [Finset.sum_range_succ] at hsum ⊢
  exact (by norm_num : (7 / 2 : ℝ) < 68771 / 19208).trans_le hsum

lemma lrSmallSBridgeQChiNumerator_two_sevenths_pos :
    0 < lrSmallSBridgeQChiNumerator (2 / 7 : ℝ) := by
  have hlog : Real.log (7 / 2 : ℝ) < 9 / 7 :=
    (Real.log_lt_iff_lt_exp (by norm_num)).2
      lr_exp_nine_sevenths_gt_seven_halves
  have hrewrite : Real.log (2 / 7 : ℝ) = -Real.log (7 / 2 : ℝ) := by
    rw [Real.log_div (by norm_num : (2 : ℝ) ≠ 0)
      (by norm_num : (7 : ℝ) ≠ 0),
      Real.log_div (by norm_num : (7 : ℝ) ≠ 0)
        (by norm_num : (2 : ℝ) ≠ 0)]
    ring
  unfold lrSmallSBridgeQChiNumerator
  rw [hrewrite]
  linarith

lemma lrSmallSBridgeQChi_exists_root :
    ∃ w ∈ Ioo (1 / 4 : ℝ) (2 / 7),
      lrSmallSBridgeQChiNumerator w = 0 := by
  let f := lrSmallSBridgeQChiNumerator
  have hab : (1 / 4 : ℝ) ≤ 2 / 7 := by norm_num
  have hcont : ContinuousOn f (Icc (1 / 4 : ℝ) (2 / 7)) := by
    intro x hx
    unfold f lrSmallSBridgeQChiNumerator
    exact ((Real.continuousAt_log (by linarith [hx.1] : x ≠ 0)).add
      continuousAt_const).add continuousAt_id |>.continuousWithinAt
  have hzero : (0 : ℝ) ∈ Icc (f (1 / 4)) (f (2 / 7)) :=
    ⟨lrSmallSBridgeQChiNumerator_quarter_neg.le,
      lrSmallSBridgeQChiNumerator_two_sevenths_pos.le⟩
  rcases intermediate_value_Icc hab hcont hzero with ⟨w, hw, hwzero⟩
  refine ⟨w, ⟨?_, ?_⟩, hwzero⟩
  · by_contra hnot
    have hwEq : w = 1 / 4 := by linarith [hw.1]
    rw [hwEq] at hwzero
    linarith [lrSmallSBridgeQChiNumerator_quarter_neg]
  · by_contra hnot
    have hwEq : w = 2 / 7 := by linarith [hw.2]
    rw [hwEq] at hwzero
    linarith [lrSmallSBridgeQChiNumerator_two_sevenths_pos]

lemma lrSmallSBridgeQChi_at_root
    {w : ℝ} (hwPos : 0 < w)
    (hw : lrSmallSBridgeQChiNumerator w = 0) :
    lrSmallSBridgeQChi w = -w := by
  unfold lrSmallSBridgeQChiNumerator at hw
  unfold lrSmallSBridgeQChi
  have hden : 1 + w ≠ 0 := by linarith
  field_simp [hden]
  nlinarith

/-- The exact endpoint range used for boxes touching `chi=0`. -/
theorem lrSmallSBridgeQChi_lower
    {chi : ℝ} (hchi : chi ∈ Icc (0 : ℝ) 1) :
    (-2 / 7 : ℝ) < lrSmallSBridgeQChi chi := by
  rcases hchi.1.eq_or_lt with rfl | hchiPos
  · norm_num [lrSmallSBridgeQChi]
  · obtain ⟨w, hwMem, hwRoot⟩ := lrSmallSBridgeQChi_exists_root
    have hwPos : 0 < w := (by norm_num : (0 : ℝ) < 1 / 4).trans hwMem.1
    have hrootValue := lrSmallSBridgeQChi_at_root hwPos hwRoot
    have hrootLower : (-2 / 7 : ℝ) < lrSmallSBridgeQChi w := by
      rw [hrootValue]
      linarith [hwMem.2]
    by_cases hchiw : chi ≤ w
    · have hanti : AntitoneOn lrSmallSBridgeQChi (Icc chi w) := by
        apply antitoneOn_of_deriv_nonpos (convex_Icc chi w)
        · intro x hx
          exact (hasDerivAt_lrSmallSBridgeQChi
            (hchiPos.trans_le hx.1)).continuousAt.continuousWithinAt
        · intro x hx
          rw [interior_Icc] at hx
          exact (hasDerivAt_lrSmallSBridgeQChi
            (hchiPos.trans hx.1)).differentiableAt.differentiableWithinAt
        · intro x hx
          rw [interior_Icc] at hx
          rw [(hasDerivAt_lrSmallSBridgeQChi (hchiPos.trans hx.1)).deriv]
          apply div_nonpos_of_nonpos_of_nonneg
          · have hmono := lrSmallSBridgeQChiNumerator_strictMonoOn
              (show x ∈ Ioi (0 : ℝ) from hchiPos.trans hx.1)
              (show w ∈ Ioi (0 : ℝ) from hwPos) hx.2
            linarith
          · positivity
      exact hrootLower.trans_le
        (hanti ⟨le_rfl, hchiw⟩ ⟨hchiw, le_rfl⟩ hchiw)
    · have hwchi : w < chi := lt_of_not_ge hchiw
      have hmono : MonotoneOn lrSmallSBridgeQChi (Icc w chi) := by
        apply monotoneOn_of_deriv_nonneg (convex_Icc w chi)
        · intro x hx
          exact (hasDerivAt_lrSmallSBridgeQChi
            (hwPos.trans_le hx.1)).continuousAt.continuousWithinAt
        · intro x hx
          rw [interior_Icc] at hx
          exact (hasDerivAt_lrSmallSBridgeQChi
            (hwPos.trans hx.1)).differentiableAt.differentiableWithinAt
        · intro x hx
          rw [interior_Icc] at hx
          rw [(hasDerivAt_lrSmallSBridgeQChi (hwPos.trans hx.1)).deriv]
          apply div_nonneg
          · have hnum := lrSmallSBridgeQChiNumerator_strictMonoOn
              (show w ∈ Ioi (0 : ℝ) from hwPos)
              (show x ∈ Ioi (0 : ℝ) from hwPos.trans hx.1) hx.1
            linarith
          · positivity
      exact hrootLower.trans_le
        (hmono ⟨le_rfl, hwchi.le⟩ ⟨hwchi.le, le_rfl⟩ hwchi.le)

end CourtadeKumar
