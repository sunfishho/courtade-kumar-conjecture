import InformationTheory.CourtadeKumar.LRLowerFaceAssembly

/-!
# Positive logarithmic coefficient in the small-`s` bridge

This proves the analytic monotonicity reduction preceding manuscript (M30):
the coefficient of `L = log (1/s)` in the frozen logarithmic-core reserve is
strictly positive throughout `s ≤ 2⁻¹⁴`, `1/4 ≤ k ≤ 4`, `0 ≤ chi ≤ 1`.
-/

open Set

namespace CourtadeKumar

noncomputable def lrSmallSBridgeLCoeff (s k chi : ℝ) : ℝ :=
  (1 - s * k * (1 + chi) +
    k * chi * Real.log
      (chi * (1 + (1 - s) * k) /
        (1 + (1 - s) * k * chi))) / 8

lemma lrSmallSBridgeLCoeff_lower
    {s k chi : ℝ}
    (hs : s ∈ Ioc (0 : ℝ) (1 / 16384))
    (hk : k ∈ Icc (1 / 4 : ℝ) 4)
    (hchi : chi ∈ Icc (0 : ℝ) 1) :
    (1 - 2 * s * k - s * (1 - s) * k ^ 2) /
        (8 * (1 + (1 - s) * k)) ≤
      lrSmallSBridgeLCoeff s k chi := by
  let R := 1 - s
  have hRnonneg : 0 ≤ R := by
    unfold R
    nlinarith [hs.2]
  have hkPos : 0 < k := (by norm_num : (0 : ℝ) < 1 / 4).trans_le hk.1
  have hdenPos : 0 < 1 + R * k := by
    exact add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg hRnonneg hkPos.le)
  rcases hchi.1.eq_or_lt with rfl | hchiPos
  · unfold lrSmallSBridgeLCoeff
    norm_num
    rw [div_le_iff₀ (mul_pos (by norm_num) hdenPos)]
    ring_nf
    nlinarith
  · have hinnerDenPos : 0 < 1 + R * k * chi := by
      exact add_pos_of_pos_of_nonneg zero_lt_one
        (mul_nonneg (mul_nonneg hRnonneg hkPos.le) hchiPos.le)
    let a := chi * (1 + R * k) / (1 + R * k * chi)
    have ha : 0 < a :=
      div_pos (mul_pos hchiPos hdenPos) hinnerDenPos
    have hlog := Real.one_sub_inv_le_log_of_pos ha
    have hscaleNonneg : 0 ≤ k * chi := mul_nonneg hkPos.le hchiPos.le
    have hscaled := mul_le_mul_of_nonneg_left hlog hscaleNonneg
    have haInv : a⁻¹ =
        (1 + R * k * chi) / (chi * (1 + R * k)) := by
      unfold a
      rw [inv_div]
    rw [haInv] at hscaled
    have hraw :
        1 - s * k * (1 + chi) +
            (k * chi - k * (1 + R * k * chi) / (1 + R * k)) ≤
          1 - s * k * (1 + chi) + k * chi * Real.log a := by
      have hcancel : k * chi *
          (1 - (1 + R * k * chi) / (chi * (1 + R * k))) =
          k * chi - k * (1 + R * k * chi) / (1 + R * k) := by
        field_simp [hchiPos.ne', hdenPos.ne']
      rw [← hcancel]
      linarith
    have hlinear :
        (1 - 2 * s * k - s * R * k ^ 2) / (1 + R * k) ≤
          1 - s * k * (1 + chi) +
            (k * chi - k * (1 + R * k * chi) / (1 + R * k)) := by
      rw [div_le_iff₀ hdenPos]
      have hsKlt : s * k < 1 := by
        have hprod : s * k ≤ (1 / 16384 : ℝ) * 4 :=
          mul_le_mul hs.2 hk.2 hkPos.le (by norm_num)
        exact hprod.trans_lt (by norm_num)
      have hcoefficient : 0 ≤
          k * R * (1 - s * k) * chi :=
        mul_nonneg
          (mul_nonneg (mul_nonneg hkPos.le hRnonneg)
            (sub_nonneg.mpr hsKlt.le)) hchiPos.le
      unfold R at *
      field_simp [hdenPos.ne'] at hraw ⊢
      nlinarith
    unfold R at hlinear
    have hcombined := hlinear.trans hraw
    unfold lrSmallSBridgeLCoeff
    change (1 - 2 * s * k - s * (1 - s) * k ^ 2) /
        (8 * (1 + (1 - s) * k)) ≤
      (1 - s * k * (1 + chi) + k * chi * Real.log a) / 8
    calc
      (1 - 2 * s * k - s * (1 - s) * k ^ 2) /
          (8 * (1 + (1 - s) * k)) =
        ((1 - 2 * s * k - s * (1 - s) * k ^ 2) /
          (1 + (1 - s) * k)) / 8 := by
        have hne : 1 + (1 - s) * k ≠ 0 := by
          simpa [R] using hdenPos.ne'
        field_simp [hne]
      _ ≤ (1 - s * k * (1 + chi) + k * chi * Real.log a) / 8 :=
        div_le_div_of_nonneg_right hcombined (by norm_num)

/-- The coefficient of `L` is positive, so the frozen reserve is minimized
at the endpoint `L = 14 log 2`. -/
theorem lrSmallSBridgeLCoeff_pos
    {s k chi : ℝ}
    (hs : s ∈ Ioc (0 : ℝ) (1 / 16384))
    (hk : k ∈ Icc (1 / 4 : ℝ) 4)
    (hchi : chi ∈ Icc (0 : ℝ) 1) :
    0 < lrSmallSBridgeLCoeff s k chi := by
  have hlower := lrSmallSBridgeLCoeff_lower hs hk hchi
  have hnum : 0 < 1 - 2 * s * k - s * (1 - s) * k ^ 2 := by
    have hsk : s * k ≤ (1 / 16384 : ℝ) * 4 :=
      mul_le_mul hs.2 hk.2
        ((by norm_num : (0 : ℝ) ≤ 1 / 4).trans hk.1) (by norm_num)
    have hsRkSq : s * (1 - s) * k ^ 2 ≤ (1 / 16384 : ℝ) * 1 * 4 ^ 2 := by
      have hR : 0 ≤ 1 - s := by nlinarith [hs.2]
      have hRLe : 1 - s ≤ 1 := by linarith [hs.1]
      have hkSq : k ^ 2 ≤ 4 ^ 2 := by nlinarith [hk.1, hk.2]
      exact mul_le_mul
        (mul_le_mul hs.2 hRLe hR (by norm_num)) hkSq (sq_nonneg k)
          (mul_nonneg (by norm_num) (by norm_num))
    nlinarith
  have hden : 0 < 8 * (1 + (1 - s) * k) := by
    have hR : 0 ≤ 1 - s := by nlinarith [hs.2]
    have hkNonneg : 0 ≤ k := (by norm_num : (0 : ℝ) ≤ 1 / 4).trans hk.1
    positivity
  exact (div_pos hnum hden).trans_le hlower

end CourtadeKumar
