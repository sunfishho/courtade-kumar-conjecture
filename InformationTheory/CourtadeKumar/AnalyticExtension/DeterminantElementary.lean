import InformationTheory.CourtadeKumar.AnalyticExtension.DeterminantLoss
import InformationTheory.CourtadeKumar.AnalyticExtension.MidpointRationalCore

/-! Elementary bounds used by the finite determinant reduction. -/
open Set
namespace CourtadeKumar.LRAnalyticDeterminant

/-- Retain the quadratic cancellation at v = 1 without a numerical log. -/
lemma g0_quadratic_lower {v : ℝ} (hv : v ∈ Ioc (0 : ℝ) 1) :
    -(1 - v) ^ 2 / (4 * v ^ 2) ≤ lrCertificateG0 v := by
  let f : ℝ → ℝ := fun w => lrCertificateG0 w + (1 - w) ^ 2 / (4 * w ^ 2)
  have hd : ∀ w : ℝ, 0 < w → HasDerivAt f
      (lrCertificateG0Prime w - (1 - w) / (2 * w ^ 3)) w := by
    intro w hw
    have h := (hasDerivAt_lrCertificateG0 hw).add
      (((((hasDerivAt_const w 1).sub (hasDerivAt_id w)).pow 2).div
        (((hasDerivAt_id w).pow 2).const_mul 4)) (by dsimp; positivity))
    convert h using 1 <;> dsimp [f] <;> field_simp [hw.ne'] <;> ring
  have hbound : ∀ w ∈ Icc v 1,
      lrCertificateG0Prime w ≤ (1 - w) / (2 * w ^ 3) := by
    intro w hw
    have hw0 : 0 < w := hv.1.trans_le hw.1
    have hp : 0 < 1 + w := by linarith
    have hl := Real.log_le_sub_one_of_pos (div_pos (by norm_num : (0 : ℝ) < 2) hp)
    rw [Real.log_div (by norm_num : (2 : ℝ) ≠ 0) hp.ne'] at hl
    have hrat : 2 / (1 + w) - 1 = (1 - w) / (1 + w) := by
      field_simp [hp.ne']; ring
    rw [hrat] at hl
    have hr : (1 - w) / (1 + w) ≤ (1 - w) / (2 * w) :=
      div_le_div_of_nonneg_left (sub_nonneg.mpr hw.2) (by positivity) (by linarith [hw.2])
    unfold lrCertificateG0Prime
    calc
      _ ≤ ((1 - w) / (2 * w)) / w ^ 2 :=
        div_le_div_of_nonneg_right (hl.trans hr) (sq_nonneg w)
      _ = _ := by field_simp [hw0.ne'] <;> ring
  have ha : AntitoneOn f (Icc v 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc v 1)
    · intro w hw
      exact (hd w (hv.1.trans_le hw.1)).continuousAt.continuousWithinAt
    · intro w hw
      rw [interior_Icc] at hw
      exact (hd w (hv.1.trans hw.1)).differentiableAt.differentiableWithinAt
    · intro w hw
      rw [interior_Icc] at hw
      rw [(hd w (hv.1.trans hw.1)).deriv]
      exact sub_nonpos.mpr (hbound w ⟨hw.1.le, hw.2.le⟩)
  have h := ha ⟨le_rfl, hv.2⟩ ⟨hv.2, le_rfl⟩ hv.2
  have h1 : f 1 = 0 := by norm_num [f, lrCertificateG0]
  rw [h1] at h
  dsimp [f] at h
  rw [neg_div]
  linarith

lemma g0_finite_lower {v : ℝ} (hv : v ∈ Icc (3 / 4 : ℝ) 1) :
    -(4 / 9 : ℝ) * (1 - v) ^ 2 ≤ lrCertificateG0 v := by
  have hv0 : 0 < v := by linarith [hv.1]
  have h := g0_quadratic_lower ⟨hv0, hv.2⟩
  rw [neg_div] at h
  have hq : (1 - v) ^ 2 / (4 * v ^ 2) ≤ (4 / 9 : ℝ) * (1 - v) ^ 2 := by
    rw [div_le_iff₀ (by positivity : 0 < 4 * v ^ 2)]
    have hsq : (9 / 16 : ℝ) ≤ v ^ 2 := by nlinarith [hv.1]
    nlinarith [mul_nonneg (sq_nonneg (1 - v)) (sub_nonneg.mpr hsq)]
  linarith

/-- Every positive tangent parameter yields an upper affine bound at chi=0. -/
lemma entropy_tangent {c a : ℝ} (hc : 0 < c) (ha : 0 < a) :
    -c * Real.log c ≤ a - c * (1 + Real.log a) := by
  have h := Real.log_le_sub_one_of_pos (div_pos ha hc)
  rw [Real.log_div ha.ne' hc.ne'] at h
  have hm := mul_le_mul_of_nonneg_left h hc.le
  have hid : c * (a / c - 1) = a - c := by field_simp [hc.ne'] <;> ring
  rw [hid] at hm
  nlinarith

lemma loss_tangent {p : CertificatePoint} {a : ℝ}
    (hi : LRHighShapeInterior p) (ha : 0 < a) :
    LRAnalyticMidpoint.loss p ≤
      (a - p.chi * (1 + Real.log a)) / (1 + p.chi) -
        LRAnalyticMidpoint.rationalAlpha p.s p.k p.chi := by
  have h := div_le_div_of_nonneg_right (entropy_tangent hi.2.2.1 ha)
    (by linarith [hi.2.2.1] : 0 ≤ 1 + p.chi)
  have hal := LRAnalyticMidpoint.alpha_lower hi
  unfold LRAnalyticMidpoint.loss lrSmallSBridgeQChi
  simp only [neg_mul, neg_div] at h
  linarith

end CourtadeKumar.LRAnalyticDeterminant
