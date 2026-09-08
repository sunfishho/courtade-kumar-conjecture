import InformationTheory.CourtadeKumar.AnalyticExtension.DeterminantElementary

/-! A cubic error bound for the logarithmic D model, small at large k. -/
open Set
namespace CourtadeKumar.LRAnalyticDeterminant

lemma log_model_gap_cubic {z : ℝ} (hz : 0 ≤ z) :
    Real.log (1 + z) / 2 - z / (2 + z) ≤ z ^ 3 / 24 := by
  let f : ℝ → ℝ := fun w => w ^ 3 / 24 - Real.log (1 + w) / 2 + w / (2 + w)
  have hd : ∀ w : ℝ, 0 ≤ w → HasDerivAt f
      (w ^ 2 / 8 - w ^ 2 / (2 * (1 + w) * (2 + w) ^ 2)) w := by
    intro w hw
    have h1 : 1 + w ≠ 0 := by linarith
    have h2 : 2 + w ≠ 0 := by linarith
    have h := ((((hasDerivAt_id w).pow 3).div_const 24).sub
      ((((hasDerivAt_const w 1).add (hasDerivAt_id w)).log h1).div_const 2)).add
      ((hasDerivAt_id w).div ((hasDerivAt_const w 2).add (hasDerivAt_id w)) h2)
    convert h using 1 <;> dsimp [f] <;> field_simp [h1, h2] <;> ring
  have hm : MonotoneOn f (Icc 0 z) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 z)
    · intro w hw
      exact (hd w hw.1).continuousAt.continuousWithinAt
    · intro w hw
      rw [interior_Icc] at hw
      exact (hd w hw.1.le).differentiableAt.differentiableWithinAt
    · intro w hw
      rw [interior_Icc] at hw
      rw [(hd w hw.1.le).deriv]
      have hden : 8 ≤ 2 * (1 + w) * (2 + w) ^ 2 := by
        have hsq : 4 ≤ (2 + w) ^ 2 := by nlinarith [hw.1]
        nlinarith [mul_nonneg hw.1.le (sq_nonneg (2 + w))]
      exact sub_nonneg.mpr (div_le_div_of_nonneg_left (sq_nonneg w) (by norm_num) hden)
  have h := hm ⟨le_rfl, hz⟩ ⟨hz, le_rfl⟩ hz
  have h0 : f 0 = 0 := by norm_num [f]
  rw [h0] at h
  dsimp [f] at h
  linarith

lemma d_gap_cubic {p : CertificatePoint} (hi : LRHighShapeInterior p) :
    lrCertificateD p - lrDeterminantD1 p ≤
      (LRAnalyticMidpoint.rationalD p.s p.k) ^ 3 / 24 := by
  let Y := lrDeterminantY p
  let z := (Y - 1) / (Y + 1)
  have hY : 1 ≤ Y := lrDeterminantY_one_le hi
  have hp : 0 < Y + 1 := by linarith
  have hY0 : 0 < Y := by linarith
  have hz : 0 ≤ z := div_nonneg (by linarith) hp.le
  have hratio : Y / ((1 + Y) / 2) = 1 + z := by
    dsimp [z]; field_simp [hp.ne']; ring
  have hrat : (Y - 1) / (3 * Y + 1) = z / (2 + z) := by
    dsimp [z]
    field_simp [hp.ne', show 3 * Y + 1 ≠ 0 by linarith,
      show 1 + Y * 3 ≠ 0 by linarith]
    ring_nf
    field_simp [show 1 + Y * 3 ≠ 0 by linarith] <;> ring
  have hlog : Real.log Y - Real.log ((1 + Y) / 2) = Real.log (1 + z) := by
    rw [← Real.log_div hY0.ne' (show (1 + Y) / 2 ≠ 0 by linarith), hratio]
  have hk : 0 < p.k := (mul_pos_iff_of_pos_left hi.1.1).mp hi.2.1.1
  have he : p.s * p.k < 1 := hi.2.1.2
  have hYEq : Y = (1 + (1 - p.s) * p.k) / p.k := by
    dsimp [Y, lrDeterminantY, lrCertificateB, lrCertificateE]
    field_simp [hi.1.1.ne', hk.ne']
  have hzEq : z = LRAnalyticMidpoint.rationalD p.s p.k := by
    dsimp [z]
    rw [hYEq]
    unfold LRAnalyticMidpoint.rationalD
    field_simp (disch := nlinarith [hk, he]) [hk.ne']
    ring
  have h := log_model_gap_cubic hz
  rw [hzEq] at h
  rw [lrCertificateD_eq_half_log_determinantY hi]
  unfold lrDeterminantD1
  change 1 / 2 * Real.log Y - (1 / 2 * Real.log ((1 + Y) / 2) +
    (Y - 1) / (3 * Y + 1)) ≤ _
  rw [hrat]
  rw [hzEq] at hlog ⊢
  linarith

end CourtadeKumar.LRAnalyticDeterminant
