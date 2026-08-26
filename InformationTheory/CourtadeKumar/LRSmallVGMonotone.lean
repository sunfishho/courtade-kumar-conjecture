import InformationTheory.CourtadeKumar.LRSmallVLogBounds

/-!
# Monotonicity of the scaled `g` term on the small-odds chart

This proves `v g(v) ≤ 3/4` by differentiating the scaled odds entropy and
using the exact terminal logarithm bound.
-/

open Set

namespace CourtadeKumar

noncomputable def lrSmallVG (v : ℝ) : ℝ := v * lrG v

theorem hasDerivAt_lrSmallVG
    {v : ℝ} (hv : 0 < v) :
    HasDerivAt lrSmallVG (Real.log (1 + v) - Real.log v) v := by
  have h := (hasDerivAt_id v).mul (hasDerivAt_lrG hv)
  unfold lrSmallVG
  convert h using 1
  simp only [id_eq, one_mul]
  unfold lrG
  field_simp [hv.ne']
  ring

theorem strictMonoOn_lrSmallVG :
    StrictMonoOn lrSmallVG (Ioo (0 : ℝ) 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioo (0 : ℝ) 1)
  · intro v hv
    exact (hasDerivAt_lrSmallVG hv.1).continuousAt.continuousWithinAt
  · intro v hv
    rw [interior_Ioo] at hv
    rw [(hasDerivAt_lrSmallVG hv.1).deriv]
    have hlog := Real.log_lt_log hv.1 (show v < 1 + v by linarith)
    linarith

lemma lrSmallVG_one_third :
    lrSmallVG (1 / 3 : ℝ) =
      (8 / 3 : ℝ) * Real.log 2 - Real.log 3 := by
  unfold lrSmallVG lrG
  rw [show (1 + (1 / 3 : ℝ)) = 4 / 3 by ring,
    Real.log_div (by norm_num : (4 : ℝ) ≠ 0) (by norm_num),
    Real.log_div (by norm_num : (1 : ℝ) ≠ 0) (by norm_num),
    Real.log_one, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
  norm_num
  ring

theorem lrSmallVG_le_three_fourths
    {v : ℝ} (hv0 : 0 < v) (hv : v ≤ 1 / 3) :
    lrSmallVG v ≤ 3 / 4 := by
  have hvMem : v ∈ Ioo (0 : ℝ) 1 := ⟨hv0, hv.trans_lt (by norm_num)⟩
  have hthirdMem : (1 / 3 : ℝ) ∈ Ioo (0 : ℝ) 1 := by norm_num
  have hmono : lrSmallVG v ≤ lrSmallVG (1 / 3 : ℝ) := by
    rcases hv.eq_or_lt with h | h
    · exact (congrArg lrSmallVG h).le
    · exact (strictMonoOn_lrSmallVG hvMem hthirdMem h).le
  rw [lrSmallVG_one_third] at hmono
  exact hmono.trans lr_smallV_terminal_log_bound.le

end CourtadeKumar
