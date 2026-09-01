import InformationTheory.CourtadeKumar.LRCompactVIntervalArithmetic
import InformationTheory.CourtadeKumar.ExactLogEnclosure

/-!
# Cancellation-free full `D` lower enclosure for compact `V`

Writing `y = v^2 x`, the common `log (1+v)` term cancels from `A-B`:

`D(R,y) = (1/2) log ((1-Ry)/(1-y))`.

At the monotone lower corner `(RHi,yLo)`, introduce

`qD = (1-RHi)yLo / (2-(1+RHi)yLo)`.

Then `(1-RHi*yLo)/(1-yLo) = (1+qD)/(1-qD)`.  Consequently the existing
positive odd logarithm series gives a direct rational enclosure of the full
`D`, without separately enclosing `A` and `B` and losing their shared
`log (1+v)` cancellation.
-/

set_option autoImplicit false

namespace CourtadeKumar

/-- Full `D=A-B` in the squared compact coordinate `y=v^2*x`. -/
noncomputable def lrCompactVDFullX (R y : ℝ) : ℝ :=
  (1 / 2 : ℝ) * (Real.log (1 - R * y) - Real.log (1 - y))

/-- The lower endpoint of `y=v^2*x` on a compact box. -/
def lrCompactVDirectDYLoQ (box : CertificateBox) : ℚ :=
  box.kLo ^ 2 * box.chiLo

/-- Half-log-ratio coordinate of the monotone full-`D` corner. -/
def lrCompactVDirectDQ (box : CertificateBox) : ℚ :=
  let yLo := lrCompactVDirectDYLoQ box
  (1 - box.sHi) * yLo / (2 - (1 + box.sHi) * yLo)

/-- Exact positive-series enclosure of the monotone full-`D` corner. -/
def lrCompactVDirectDEnclosure
    (terms : ℕ) (box : CertificateBox) : RationalEnclosure :=
  RationalEnclosure.halfLogRatioEnclosure terms
    (lrCompactVDirectDQ box)

/-- Domain conditions needed by the direct half-log-ratio coordinate. -/
def LRCompactVDirectDValid (box : CertificateBox) : Prop :=
  LRCompactVBoxValid box ∧ box.sHi < 1 ∧ lrCompactVDirectDYLoQ box < 1

/-- Executable validity check for the direct full-`D` enclosure. -/
def LRCompactVDirectDValid.check (box : CertificateBox) : Bool :=
  decide (
    LRCompactVBoxValid.check box = true ∧ box.sHi < 1 ∧
      lrCompactVDirectDYLoQ box < 1)

theorem LRCompactVDirectDValid.of_check {box : CertificateBox}
    (hcheck : LRCompactVDirectDValid.check box = true) :
    LRCompactVDirectDValid box := by
  have hparts :
      LRCompactVBoxValid.check box = true ∧ box.sHi < 1 ∧
        lrCompactVDirectDYLoQ box < 1 := by
    simpa [LRCompactVDirectDValid.check] using hcheck
  exact ⟨LRCompactVBoxValid.of_check hparts.1, hparts.2⟩

private theorem lrCompactVDirectDCoordinate_range
    {R y : ℝ} (hR0 : 0 ≤ R) (hR1 : R < 1)
    (hy0 : 0 ≤ y) (hy1 : y < 1) :
    0 ≤ (1 - R) * y / (2 - (1 + R) * y) ∧
      (1 - R) * y / (2 - (1 + R) * y) < 1 := by
  have hOneRPos : 0 < 1 + R := by linarith
  have hprod : (1 + R) * y < 2 := by
    calc
      (1 + R) * y < (1 + R) * 1 :=
        mul_lt_mul_of_pos_left hy1 hOneRPos
      _ < 2 := by linarith
  have hden : 0 < 2 - (1 + R) * y := by linarith
  constructor
  · exact div_nonneg
      (mul_nonneg (sub_nonneg.mpr hR1.le) hy0) hden.le
  · rw [div_lt_one hden]
    nlinarith

private theorem lrCompactVDFullX_eq_logRatio
    {R y : ℝ} (hR0 : 0 ≤ R) (hR1 : R < 1)
    (hy0 : 0 ≤ y) (hy1 : y < 1) :
    lrCompactVDFullX R y =
      (1 / 2 : ℝ) * Real.log ((1 - R * y) / (1 - y)) := by
  have hRy : R * y < 1 := by
    calc
      R * y ≤ 1 * y := mul_le_mul_of_nonneg_right hR1.le hy0
      _ < 1 := by simpa using hy1
  have hnum : 0 < 1 - R * y := sub_pos.mpr hRy
  have hden : 0 < 1 - y := sub_pos.mpr hy1
  rw [Real.log_div hnum.ne' hden.ne']
  rfl

private theorem lrCompactVDFullX_eq_halfLogRatio
    {R y : ℝ} (hR0 : 0 ≤ R) (hR1 : R < 1)
    (hy0 : 0 ≤ y) (hy1 : y < 1) :
    lrCompactVDFullX R y =
      (1 / 2 : ℝ) * Real.log
        ((1 + ((1 - R) * y / (2 - (1 + R) * y))) /
          (1 - ((1 - R) * y / (2 - (1 + R) * y)))) := by
  have hOneRPos : 0 < 1 + R := by linarith
  have hprod : (1 + R) * y < 2 := by
    calc
      (1 + R) * y < (1 + R) * 1 :=
        mul_lt_mul_of_pos_left hy1 hOneRPos
      _ < 2 := by linarith
  have hcoordDen : 2 - (1 + R) * y ≠ 0 := by linarith
  have hyDen : 1 - y ≠ 0 := by linarith
  have honePlus :
      1 + ((1 - R) * y / (2 - (1 + R) * y)) =
        2 * (1 - R * y) / (2 - (1 + R) * y) := by
    apply (eq_div_iff hcoordDen).2
    rw [add_mul, one_mul, div_mul_cancel₀ _ hcoordDen]
    ring
  have honeSub :
      1 - ((1 - R) * y / (2 - (1 + R) * y)) =
        2 * (1 - y) / (2 - (1 + R) * y) := by
    apply (eq_div_iff hcoordDen).2
    rw [sub_mul, one_mul, div_mul_cancel₀ _ hcoordDen]
    ring
  have hratio :
      (1 + ((1 - R) * y / (2 - (1 + R) * y))) /
          (1 - ((1 - R) * y / (2 - (1 + R) * y))) =
        (1 - R * y) / (1 - y) := by
    rw [honePlus, honeSub]
    rw [div_div_div_cancel_right₀ hcoordDen]
    field_simp [hyDen]
  rw [lrCompactVDFullX_eq_logRatio hR0 hR1 hy0 hy1, hratio]

private theorem lrCompactVDFullX_corner_le
    {R RHi yLo y : ℝ}
    (hR0 : 0 ≤ R) (hRle : R ≤ RHi) (hRHi1 : RHi < 1)
    (hyLo0 : 0 ≤ yLo) (hyLe : yLo ≤ y) (hy1 : y < 1) :
    lrCompactVDFullX RHi yLo ≤ lrCompactVDFullX R y := by
  have hRHi0 : 0 ≤ RHi := hR0.trans hRle
  have hR1 : R < 1 := hRle.trans_lt hRHi1
  have hyLo1 : yLo < 1 := hyLe.trans_lt hy1
  have hdenLo : 0 < 1 - yLo := sub_pos.mpr hyLo1
  have hden : 0 < 1 - y := sub_pos.mpr hy1
  have hRRatio :
      (1 - RHi * yLo) / (1 - yLo) ≤
        (1 - R * yLo) / (1 - yLo) := by
    exact div_le_div_of_nonneg_right
      (sub_le_sub_left (mul_le_mul_of_nonneg_right hRle hyLo0) 1)
      hdenLo.le
  have hyRatio :
      (1 - R * yLo) / (1 - yLo) ≤
        (1 - R * y) / (1 - y) := by
    rw [div_le_div_iff₀ hdenLo hden]
    have hprod := mul_nonneg (sub_nonneg.mpr hR1.le)
      (sub_nonneg.mpr hyLe)
    nlinarith
  have hRHiYLo : RHi * yLo < 1 := by
    calc
      RHi * yLo ≤ 1 * yLo :=
        mul_le_mul_of_nonneg_right hRHi1.le hyLo0
      _ < 1 := by simpa using hyLo1
  have hratioPos : 0 < (1 - RHi * yLo) / (1 - yLo) :=
    div_pos (sub_pos.mpr hRHiYLo) hdenLo
  have hlog := Real.log_le_log hratioPos (hRRatio.trans hyRatio)
  rw [lrCompactVDFullX_eq_logRatio hRHi0 hRHi1 hyLo0 hyLo1,
    lrCompactVDFullX_eq_logRatio hR0 hR1 (hyLo0.trans hyLe) hy1]
  nlinarith

@[simp] theorem cast_lrCompactVDirectDYLoQ (box : CertificateBox) :
    (lrCompactVDirectDYLoQ box : ℝ) =
      (box.kLo : ℝ) ^ 2 * (box.chiLo : ℝ) := by
  simp [lrCompactVDirectDYLoQ]

@[simp] theorem cast_lrCompactVDirectDQ (box : CertificateBox) :
    (lrCompactVDirectDQ box : ℝ) =
      (1 - (box.sHi : ℝ)) * (lrCompactVDirectDYLoQ box : ℝ) /
        (2 - (1 + (box.sHi : ℝ)) *
          (lrCompactVDirectDYLoQ box : ℝ)) := by
  simp [lrCompactVDirectDQ]

/-- The direct rational enclosure contains the exact monotone corner value. -/
theorem lrCompactVDirectDEnclosure_contains_corner
    (terms : ℕ) {box : CertificateBox}
    (hvalid : LRCompactVDirectDValid box) :
    (lrCompactVDirectDEnclosure terms box).Contains
      (lrCompactVDFullX (box.sHi : ℝ)
        (lrCompactVDirectDYLoQ box : ℝ)) := by
  have hR0 : (0 : ℝ) ≤ box.sHi := by
    exact (by exact_mod_cast hvalid.1.1 : (0 : ℝ) ≤ box.sLo) |>.trans
      (by exact_mod_cast hvalid.1.2.1 : (box.sLo : ℝ) ≤ box.sHi)
  have hR1 : (box.sHi : ℝ) < 1 := by exact_mod_cast hvalid.2.1
  have hy0 : (0 : ℝ) ≤ lrCompactVDirectDYLoQ box := by
    rw [cast_lrCompactVDirectDYLoQ]
    exact mul_nonneg (sq_nonneg _)
      (by exact_mod_cast hvalid.1.2.2.2.2.2.2.1)
  have hy1 : (lrCompactVDirectDYLoQ box : ℝ) < 1 := by
    exact_mod_cast hvalid.2.2
  have hqRange := lrCompactVDirectDCoordinate_range hR0 hR1 hy0 hy1
  have hq0 : (0 : ℚ) ≤ lrCompactVDirectDQ box := by
    exact_mod_cast (show (0 : ℝ) ≤ (lrCompactVDirectDQ box : ℝ) by
      simpa using hqRange.1)
  have hq1 : lrCompactVDirectDQ box < (1 : ℚ) := by
    exact_mod_cast (show (lrCompactVDirectDQ box : ℝ) < 1 by
      simpa using hqRange.2)
  have hcontains := RationalEnclosure.contains_halfLogRatioEnclosure
    terms hq0 hq1
  rw [lrCompactVDFullX_eq_halfLogRatio hR0 hR1 hy0 hy1]
  simpa [lrCompactVDirectDEnclosure] using hcontains

/-- The direct corner lower endpoint bounds the full compact-coordinate `D`
at every interior point of the box. -/
theorem lrCompactVDirectDEnclosure_lower_le_fullX
    (terms : ℕ) {box : CertificateBox} {point : CertificatePoint}
    (hvalid : LRCompactVDirectDValid box)
    (hpoint : box.Contains point) (hinterior : LRCompactVInterior point) :
    ((lrCompactVDirectDEnclosure terms box).lower : ℝ) ≤
      lrCompactVDFullX point.s (point.k ^ 2 * point.chi) := by
  have hcorner :=
    (lrCompactVDirectDEnclosure_contains_corner terms hvalid).1
  have hR0 : 0 ≤ point.s :=
    (by exact_mod_cast hvalid.1.1 : (0 : ℝ) ≤ box.sLo) |>.trans hpoint.1
  have hRle : point.s ≤ (box.sHi : ℝ) := hpoint.2.1
  have hRHi1 : (box.sHi : ℝ) < 1 := by exact_mod_cast hvalid.2.1
  have hyLo0 : (0 : ℝ) ≤ lrCompactVDirectDYLoQ box := by
    rw [cast_lrCompactVDirectDYLoQ]
    exact mul_nonneg (sq_nonneg _)
      (by exact_mod_cast hvalid.1.2.2.2.2.2.2.1)
  have hy := lrCompactVYEnclosure_sound hvalid.1 hpoint
  have hyLe : (lrCompactVDirectDYLoQ box : ℝ) ≤
      point.k ^ 2 * point.chi := by
    simpa [lrCompactVYEnclosure] using hy.1
  have hvSqLt : point.k ^ 2 < 1 := by
    nlinarith [hinterior.2.1.1, hinterior.2.1.2]
  have hy1 : point.k ^ 2 * point.chi < 1 := by
    calc
      point.k ^ 2 * point.chi < 1 * point.chi :=
        mul_lt_mul_of_pos_right hvSqLt hinterior.2.2.1
      _ < 1 := by simpa using hinterior.2.2.2
  exact hcorner.trans <|
    lrCompactVDFullX_corner_le hR0 hRle hRHi1 hyLo0 hyLe hy1

theorem lrCompactVDFullX_eq_flowD
    {R v x : ℝ} (hR : 0 ≤ R) (hx : 0 ≤ x) :
    lrCompactVDFullX R (v ^ 2 * x) =
      lrFlowD R v (Real.sqrt x) := by
  have hsquareR : (Real.sqrt R) ^ 2 = R := Real.sq_sqrt hR
  have hsquareX : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt hx
  have hvsquare : (v * Real.sqrt x) ^ 2 = v ^ 2 * x := by
    rw [mul_pow, hsquareX]
  have hRvsquare : (Real.sqrt R * v * Real.sqrt x) ^ 2 =
      R * (v ^ 2 * x) := by
    rw [mul_pow, mul_pow, hsquareR, hsquareX]
    ring
  unfold lrCompactVDFullX lrFlowD lrFlowA lrFlowB lrFlowBeta lrL
  rw [hvsquare, hRvsquare]
  ring

/-- Checker-facing semantic theorem: the direct rational lower endpoint is
below the exact `lrFlowD` throughout the box. -/
theorem lrCompactVDirectDEnclosure_lower_le_flowD
    (terms : ℕ) {box : CertificateBox} {point : CertificatePoint}
    (hvalid : LRCompactVDirectDValid box)
    (hpoint : box.Contains point) (hinterior : LRCompactVInterior point) :
    ((lrCompactVDirectDEnclosure terms box).lower : ℝ) ≤
      lrFlowD point.s point.k (Real.sqrt point.chi) := by
  have hfull := lrCompactVDirectDEnclosure_lower_le_fullX
    terms hvalid hpoint hinterior
  have hR0 : 0 ≤ point.s :=
    (by exact_mod_cast hvalid.1.1 : (0 : ℝ) ≤ box.sLo) |>.trans hpoint.1
  have hx0 : 0 ≤ point.chi :=
    (by exact_mod_cast hvalid.1.2.2.2.2.2.2.1 :
      (0 : ℝ) ≤ box.chiLo) |>.trans hpoint.2.2.2.2.1
  rw [lrCompactVDFullX_eq_flowD hR0 hx0] at hfull
  exact hfull

end CourtadeKumar
