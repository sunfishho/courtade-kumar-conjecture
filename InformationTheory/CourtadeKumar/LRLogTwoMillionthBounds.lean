import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Exact millionth-scale bounds for `log 2`

This small interface isolates the rational enclosure used by several
certificate developments from the much larger low-shape series theory.
-/

namespace CourtadeKumar

/-- The exact rational enclosure for `log 2` used in the certificate data. -/
theorem lr_log_two_millionth_bounds :
    (693147 : ℝ) / 1000000 < Real.log 2 ∧
      Real.log 2 < (693148 : ℝ) / 1000000 := by
  constructor
  · have h := Real.log_two_gt_d9
    norm_num at h ⊢
    linarith
  · have h := Real.log_two_lt_d9
    norm_num at h ⊢
    linarith

end CourtadeKumar
