import InformationTheory.CourtadeKumar.LRCompactVPhysicalCorrelation

/-!
# Correlated shape-monomial enclosure

The physical upper bound for `y=v²x` is oriented to a rational box endpoint
and inserted into the second representation

`T_n = x^n + y^n/v`.

Taking the minimum with the ordinary coordinatewise upper endpoint gives the
audited correlated enclosure (M50).
-/

namespace CourtadeKumar

def lrCompactVCorrelatedYUpperQ (box : CertificateBox) : ℚ :=
  1 - (1 - box.sHi) ^ 2 / (1 + box.kHi) ^ 2

noncomputable def lrCompactVCorrelatedYUpper (box : CertificateBox) : ℝ :=
  1 - (1 - (box.sHi : ℝ)) ^ 2 / (1 + (box.kHi : ℝ)) ^ 2

@[simp] theorem cast_lrCompactVCorrelatedYUpperQ (box : CertificateBox) :
    (lrCompactVCorrelatedYUpperQ box : ℝ) =
      lrCompactVCorrelatedYUpper box := by
  simp only [lrCompactVCorrelatedYUpperQ,
    lrCompactVCorrelatedYUpper]
  push_cast
  rfl

theorem lrCompactVCorrelatedYUpper_sound
    {box : CertificateBox} {point : CertificatePoint}
    (hbox : LRCompactVBoxValid box) (hpoint : box.Contains point)
    (hphysical : LRCompactVPhysical point) :
    point.k ^ 2 * point.chi < lrCompactVCorrelatedYUpper box := by
  have hpointBound := lrCompactV_physical_y_upper
    hphysical.1.1 hphysical.1.2.1 hphysical.1.2.2 hphysical.2
  have hRHiNonneg : (0 : ℝ) ≤ box.sHi :=
    (by exact_mod_cast hbox.1 : (0 : ℝ) ≤ box.sLo) |>.trans
      (hpoint.1.trans hpoint.2.1)
  have hRHiLe : (box.sHi : ℝ) ≤ 1 := by exact_mod_cast hbox.2.2.1
  have hvHiNonneg : (0 : ℝ) ≤ box.kHi :=
    (by exact_mod_cast hbox.2.2.2.1 : (0 : ℝ) ≤ box.kLo) |>.trans
      (hpoint.2.2.1.trans hpoint.2.2.2.1)
  have hnum : (1 - (box.sHi : ℝ)) ^ 2 ≤ (1 - point.s) ^ 2 := by
    gcongr
    · exact sub_nonneg.mpr hRHiLe
    · linarith [hpoint.2.1]
  have hdenPoint : 0 < (1 + point.k) ^ 2 :=
    sq_pos_of_pos (by linarith [hphysical.1.2.1.1])
  have hdenHi : 0 < (1 + (box.kHi : ℝ)) ^ 2 :=
    sq_pos_of_pos (by linarith [hvHiNonneg])
  have hdenOrder : (1 + point.k) ^ 2 ≤
      (1 + (box.kHi : ℝ)) ^ 2 := by
    gcongr
    · linarith [hphysical.1.2.1.1]
    · exact hpoint.2.2.2.1
  have hfrac :
      (1 - (box.sHi : ℝ)) ^ 2 /
          (1 + (box.kHi : ℝ)) ^ 2 ≤
        (1 - point.s) ^ 2 / (1 + point.k) ^ 2 := by
    calc
      (1 - (box.sHi : ℝ)) ^ 2 /
          (1 + (box.kHi : ℝ)) ^ 2 ≤
          (1 - point.s) ^ 2 /
            (1 + (box.kHi : ℝ)) ^ 2 := by
        exact div_le_div_of_nonneg_right hnum hdenHi.le
      _ ≤ (1 - point.s) ^ 2 / (1 + point.k) ^ 2 := by
        exact div_le_div_of_nonneg_left (sq_nonneg (1 - point.s))
          hdenPoint hdenOrder
  unfold lrCompactVCorrelatedYUpper
  exact hpointBound.trans_le (sub_le_sub_left hfrac 1)

def lrCompactVCorrelatedTUpperQ
    (box : CertificateBox) (n : ℕ) : ℚ :=
  if n = 0 then
    lrCompactVTQ box.kHi box.chiHi n
  else
    min (lrCompactVTQ box.kHi box.chiHi n)
      (box.chiHi ^ n +
        lrCompactVCorrelatedYUpperQ box ^ n / box.kLo)

def lrCompactVCorrelatedTEnclosure
    (box : CertificateBox) (n : ℕ) : RationalEnclosure :=
  ⟨lrCompactVTQ box.kLo box.chiLo n,
    lrCompactVCorrelatedTUpperQ box n⟩

theorem lrCompactVCorrelatedTEnclosure_sound
    {box : CertificateBox} {point : CertificatePoint}
    (hbox : LRCompactVBoxValid box) (hvLo : (0 : ℚ) < box.kLo)
    (hpoint : box.Contains point)
    (hphysical : LRCompactVPhysical point) (n : ℕ) :
    (lrCompactVCorrelatedTEnclosure box n).Contains
      (lrCompactVT point.k point.chi n) := by
  have hstandard := lrCompactVTEnclosure_sound
    (n := n) hvLo.le hbox.2.2.2.2.2.2.1 hpoint
  have hyUpper := lrCompactVCorrelatedYUpper_sound hbox hpoint hphysical
  have hvLoReal : (0 : ℝ) < box.kLo := by
    exact_mod_cast hvLo
  have hvPoint : 0 < point.k := hphysical.1.2.1.1
  have hxPoint : 0 ≤ point.chi := hphysical.1.2.2.1.le
  have hyPoint : 0 ≤ point.k ^ 2 * point.chi :=
    mul_nonneg (sq_nonneg point.k) hxPoint
  have hyUpper0 : 0 ≤ lrCompactVCorrelatedYUpper box :=
    hyPoint.trans hyUpper.le
  have hxUpper : point.chi ^ n ≤ (box.chiHi : ℝ) ^ n := by
    gcongr
    exact hpoint.2.2.2.2.2
  have hyPow : (point.k ^ 2 * point.chi) ^ n ≤
      lrCompactVCorrelatedYUpper box ^ n := by
    gcongr
  have hquot :
      (point.k ^ 2 * point.chi) ^ n / point.k ≤
        lrCompactVCorrelatedYUpper box ^ n / (box.kLo : ℝ) := by
    calc
      (point.k ^ 2 * point.chi) ^ n / point.k ≤
          lrCompactVCorrelatedYUpper box ^ n / point.k := by
        exact div_le_div_of_nonneg_right hyPow hvPoint.le
      _ ≤ lrCompactVCorrelatedYUpper box ^ n / (box.kLo : ℝ) := by
        exact div_le_div_of_nonneg_left (pow_nonneg hyUpper0 n)
          hvLoReal hpoint.2.2.1
  have hidentity (hn : n ≠ 0) : lrCompactVT point.k point.chi n =
      point.chi ^ n + (point.k ^ 2 * point.chi) ^ n / point.k := by
    have hidx : 2 * n = (2 * n - 1) + 1 := by omega
    unfold lrCompactVT
    rw [mul_pow, ← pow_mul, hidx, pow_succ]
    field_simp [hvPoint.ne']
    simp only [Nat.add_sub_cancel]
  constructor
  · exact hstandard.1
  · change lrCompactVT point.k point.chi n ≤
      ((lrCompactVCorrelatedTUpperQ box n : ℚ) : ℝ)
    by_cases hn : n = 0
    · subst n
      simpa [lrCompactVCorrelatedTUpperQ,
        lrCompactVTEnclosure] using hstandard.2
    · rw [lrCompactVCorrelatedTUpperQ, if_neg hn]
      rw [Rat.cast_min, Rat.cast_add, Rat.cast_div, Rat.cast_pow,
        Rat.cast_pow]
      rw [cast_lrCompactVTQ, cast_lrCompactVCorrelatedYUpperQ]
      have hstandardUpper : lrCompactVT point.k point.chi n ≤
          lrCompactVT (box.kHi : ℝ) (box.chiHi : ℝ) n := by
        simpa [lrCompactVTEnclosure] using hstandard.2
      apply le_min hstandardUpper
      rw [hidentity hn]
      exact add_le_add hxUpper hquot

end CourtadeKumar
