import InformationTheory.CourtadeKumar.CenteredPhaseTOP
import Mathlib.Analysis.Convex.Deriv

/-! Monotonicity of the centered entropy-per-displacement profile. -/

open Set

namespace CourtadeKumar

/-- The scalar profile that determines the centered phase contact directly
from the prescribed entropy level. -/
noncomputable def centeredEntropyRatio (r : ℝ) : ℝ :=
  binaryEntropyBits ((1 - r) / 2) / r

lemma centeredEntropyRatio_eq_radial (r : ℝ) :
    centeredEntropyRatio r = radialTriangleEntropy r (1 / 2) / r := by
  rw [centeredEntropyRatio, radialTriangleEntropy_centered]

theorem hasDerivAt_binaryEntropyBits {p : ℝ}
    (hp0 : p ≠ 0) (hp1 : p ≠ 1) :
    HasDerivAt binaryEntropyBits
      ((Real.log (1 - p) - Real.log p) / Real.log 2) p := by
  have hdiff := Real.differentiableAt_binEntropy hp0 hp1
  have hbin : HasDerivAt Real.binEntropy
      (Real.log (1 - p) - Real.log p) p := by
    exact hdiff.hasDerivAt.congr_deriv (Real.deriv_binEntropy p)
  simpa [binaryEntropyBits] using hbin.div_const (Real.log 2)

theorem hasDerivAt_centeredEntropyRatio {r : ℝ}
    (hr : r ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt centeredEntropyRatio
      (((-(1 : ℝ) / 2) *
          ((Real.log (1 - (1 - r) / 2) - Real.log ((1 - r) / 2)) /
            Real.log 2) * r - binaryEntropyBits ((1 - r) / 2)) / r ^ 2) r := by
  have hp : (1 - r) / 2 ∈ Ioo (0 : ℝ) 1 := by
    constructor <;> linarith [hr.1, hr.2]
  have hpderiv : HasDerivAt (fun x : ℝ ↦ (1 - x) / 2) (-(1 : ℝ) / 2) r := by
    convert ((hasDerivAt_const r 1).sub (hasDerivAt_id r)).div_const 2 using 1 <;> ring
  have hentropy := (hasDerivAt_binaryEntropyBits hp.1.ne' hp.2.ne).comp r hpderiv
  have hquot := hentropy.div (hasDerivAt_id r) hr.1.ne'
  convert hquot using 1 <;>
    simp [centeredEntropyRatio, Function.comp_apply] <;> ring

theorem centeredEntropyRatio_gradient_pos {r : ℝ}
    (hr : r ∈ Ioo (0 : ℝ) 1) :
    0 < binaryEntropyBits ((1 - r) / 2) +
      r / 2 *
        ((Real.log (1 - (1 - r) / 2) - Real.log ((1 - r) / 2)) /
          Real.log 2) := by
  let p : ℝ := (1 - r) / 2
  have hp : p ∈ Ioo (0 : ℝ) 1 := by
    dsimp [p]
    constructor <;> linarith [hr.1, hr.2]
  have h1p : 0 < 1 - p := by linarith [hp.2]
  have hprod0 : 0 < p * (1 - p) := mul_pos hp.1 h1p
  have hprod1 : p * (1 - p) < 1 := by
    nlinarith [sq_nonneg (p - 1 / 2)]
  have hlogprod : Real.log p + Real.log (1 - p) < 0 := by
    rw [← Real.log_mul hp.1.ne' h1p.ne']
    exact Real.log_neg hprod0 hprod1
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hformula :
      binaryEntropyBits p + r / 2 *
          ((Real.log (1 - p) - Real.log p) / Real.log 2) =
        -(Real.log p + Real.log (1 - p)) / (2 * Real.log 2) := by
    unfold binaryEntropyBits
    rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
    simp only [Real.negMulLog_eq_neg]
    dsimp [p]
    field_simp [hlog2.ne']
    ring
  change 0 < binaryEntropyBits p + r / 2 *
    ((Real.log (1 - p) - Real.log p) / Real.log 2)
  rw [hformula]
  exact div_pos (neg_pos.mpr hlogprod)
    (mul_pos (by norm_num) hlog2)

theorem deriv_centeredEntropyRatio_neg {r : ℝ}
    (hr : r ∈ Ioo (0 : ℝ) 1) :
    deriv centeredEntropyRatio r < 0 := by
  have hderiv := hasDerivAt_centeredEntropyRatio hr
  rw [hderiv.deriv]
  have hgap := centeredEntropyRatio_gradient_pos hr
  have hrsq : 0 < r ^ 2 := sq_pos_of_pos hr.1
  apply div_neg_of_neg_of_pos _ hrsq
  nlinarith

/-- The centered entropy-per-displacement profile is strictly decreasing
throughout the physical shape interval. -/
theorem strictAntiOn_centeredEntropyRatio :
    StrictAntiOn centeredEntropyRatio (Ioo (0 : ℝ) 1) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioo (0 : ℝ) 1)
  · intro r hr
    exact (hasDerivAt_centeredEntropyRatio hr).continuousAt.continuousWithinAt
  · intro r hr
    rw [interior_Ioo] at hr
    exact deriv_centeredEntropyRatio_neg hr

end CourtadeKumar
