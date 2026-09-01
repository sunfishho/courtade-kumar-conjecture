import InformationTheory.CourtadeKumar.LRCompactVDirectD
import InformationTheory.CourtadeKumar.LRCompactVBEnclosure
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Same-`y` endpoint ratio for grouped compact-`V` leaves

The independent grouped checker divides a lower bound for `D` by an upper
bound for `B` taken over the whole box.  This module keeps the shared squared
shape coordinate `y=v^2*x`: both endpoint quantities are evaluated at
`(R_hi,v_hi,y_lo)`.  A cheap rational side condition proves that

`D(R_hi,y_lo) - lambda * B(R_hi,v_hi,y_lo)`

is the minimum of `D-lambda*B` throughout the box.  This obtains the sharper
same-`y` ratio without formalizing a quotient monotonicity theorem.
-/

set_option autoImplicit false

open Set

namespace CourtadeKumar

/-- `B` with the squared shape coordinate `y` exposed. -/
noncomputable def lrCompactVBFullX (R v y : ℝ) : ℝ :=
  Real.log (1 + v) - (1 / 2 : ℝ) * Real.log (1 - R * y)

/-- The slack whose endpoint minimum certifies `lambda * B ≤ D`. -/
noncomputable def lrCompactVSameYSlack
    (lambda R v y : ℝ) : ℝ :=
  lrCompactVDFullX R y - lambda * lrCompactVBFullX R v y

namespace RationalEnclosure

/-- Half-log coordinate for `-(1/2) log (1-z)`. -/
def halfLogOneSubCoordinate (z : ℚ) : ℚ :=
  z / (2 - z)

/-- Deterministic positive-series enclosure of `-(1/2) log (1-z)`. -/
def halfLogOneSubEnclosure (terms : ℕ) (z : ℚ) :
    RationalEnclosure :=
  halfLogRatioEnclosure terms (halfLogOneSubCoordinate z)

theorem contains_halfLogOneSubEnclosure
    (terms : ℕ) {z : ℚ} (hz0 : (0 : ℚ) ≤ z) (hz1 : z < 1) :
    (halfLogOneSubEnclosure terms z).Contains
      (-(1 / 2 : ℝ) * Real.log (1 - (z : ℝ))) := by
  have hden : (0 : ℚ) < 2 - z := by linarith
  have hq0 : (0 : ℚ) ≤ halfLogOneSubCoordinate z := by
    exact div_nonneg hz0 hden.le
  have hq1 : halfLogOneSubCoordinate z < 1 := by
    rw [halfLogOneSubCoordinate, div_lt_one hden]
    linarith
  have htwoNe : (2 - z : ℚ) ≠ 0 := hden.ne'
  have honeNe : (1 - z : ℚ) ≠ 0 := by linarith
  have hratio :
      (1 + halfLogOneSubCoordinate z) /
          (1 - halfLogOneSubCoordinate z) =
        1 / (1 - z) := by
    have hqDen :
        (1 - halfLogOneSubCoordinate z : ℚ) ≠ 0 := by
      linarith
    apply (div_eq_iff hqDen).2
    unfold halfLogOneSubCoordinate
    field_simp [htwoNe, honeNe]
    ring
  have hratioReal :
      (1 + (halfLogOneSubCoordinate z : ℝ)) /
          (1 - (halfLogOneSubCoordinate z : ℝ)) =
        1 / (1 - (z : ℝ)) := by
    exact_mod_cast hratio
  have hcontains := contains_halfLogRatioEnclosure terms hq0 hq1
  rw [hratioReal] at hcontains
  have hlog :
      Real.log (1 / (1 - (z : ℝ))) =
        -Real.log (1 - (z : ℝ)) := by
    rw [one_div, Real.log_inv]
  rw [hlog] at hcontains
  convert hcontains using 1
  all_goals ring

end RationalEnclosure

/-- Same-`y` endpoint `R*y`. -/
def lrCompactVSameYEndpointZQ (box : CertificateBox) : ℚ :=
  box.sHi * lrCompactVDirectDYLoQ box

/-- Tight endpoint enclosure for `B(R_hi,v_hi,y_lo)`. -/
def lrCompactVSameYBEndpointEnclosure
    (logTerms halfLogTerms : ℕ) (box : CertificateBox)
    (logOnePlusVHi : RationalEnclosure.LogRangeCertificate) :
    RationalEnclosure :=
  RationalEnclosure.add
    (logOnePlusVHi.enclosure logTerms)
    (RationalEnclosure.halfLogOneSubEnclosure halfLogTerms
      (lrCompactVSameYEndpointZQ box))

/-- Executable lower ratio formed from the same endpoint `y`. -/
def lrCompactVSameYLambda
    (bEndpoint d : RationalEnclosure) : ℚ :=
  d.nonnegativeLower / bEndpoint.upper

theorem lrCompactVSameYLambda_nonnegative
    {bEndpoint d : RationalEnclosure}
    (hbUpper : (0 : ℚ) < bEndpoint.upper) :
    (0 : ℚ) ≤ lrCompactVSameYLambda bEndpoint d := by
  unfold lrCompactVSameYLambda
  exact div_nonneg
    (RationalEnclosure.nonnegativeLower_nonnegative d) hbUpper.le

theorem cast_lrCompactVSameYLambda_mul_le
    {bEndpoint d : RationalEnclosure} {B D : ℝ}
    (hBUpper : B ≤ (bEndpoint.upper : ℝ))
    (hbUpper : (0 : ℚ) < bEndpoint.upper)
    (hdLower : (d.lower : ℝ) ≤ D) (hD0 : 0 ≤ D) :
    (lrCompactVSameYLambda bEndpoint d : ℝ) * B ≤ D := by
  have hlambdaQ := lrCompactVSameYLambda_nonnegative
    (bEndpoint := bEndpoint) (d := d) hbUpper
  have hlambda : (0 : ℝ) ≤ lrCompactVSameYLambda bEndpoint d := by
    exact_mod_cast hlambdaQ
  have hfirst := mul_le_mul_of_nonneg_left hBUpper hlambda
  have hbNe : bEndpoint.upper ≠ 0 := hbUpper.ne'
  have hcancelQ :
      lrCompactVSameYLambda bEndpoint d * bEndpoint.upper =
        d.nonnegativeLower := by
    unfold lrCompactVSameYLambda
    exact div_mul_cancel₀ _ hbNe
  have hcancel :
      (lrCompactVSameYLambda bEndpoint d : ℝ) *
          (bEndpoint.upper : ℝ) =
        (d.nonnegativeLower : ℝ) := by
    exact_mod_cast hcancelQ
  have hclamp : (d.nonnegativeLower : ℝ) ≤ D := by
    change ((max 0 d.lower : ℚ) : ℝ) ≤ D
    rw [Rat.cast_max, Rat.cast_zero]
    exact max_le hD0 hdLower
  exact hfirst.trans (hcancel.le.trans hclamp)

theorem lrCompactVSameYBEndpointEnclosure_sound
    (logTerms halfLogTerms : ℕ) {box : CertificateBox}
    {logOnePlusVHi : RationalEnclosure.LogRangeCertificate}
    (hvalid : LRCompactVDirectDValid box)
    (hlogcheck : logOnePlusVHi.check (1 + box.kHi) = true) :
    (lrCompactVSameYBEndpointEnclosure
      logTerms halfLogTerms box logOnePlusVHi).Contains
      (lrCompactVBFullX (box.sHi : ℝ) (box.kHi : ℝ)
        (lrCompactVDirectDYLoQ box : ℝ)) := by
  rcases hvalid.1 with
    ⟨hsLo0, hsLoHi, hsHi1, hkLo0, hkLoHi, hkHi1,
      hchiLo0, hchiLoHi, hchiHi1⟩
  have hlogV := logOnePlusVHi.sound logTerms hlogcheck
  have hyLo0 : (0 : ℚ) ≤ lrCompactVDirectDYLoQ box := by
    unfold lrCompactVDirectDYLoQ
    exact mul_nonneg (sq_nonneg _) hchiLo0
  have hz0 : (0 : ℚ) ≤ lrCompactVSameYEndpointZQ box := by
    unfold lrCompactVSameYEndpointZQ
    exact mul_nonneg (hsLo0.trans hsLoHi) hyLo0
  have hz1 : lrCompactVSameYEndpointZQ box < (1 : ℚ) := by
    unfold lrCompactVSameYEndpointZQ
    calc
      box.sHi * lrCompactVDirectDYLoQ box ≤
          1 * lrCompactVDirectDYLoQ box :=
        mul_le_mul_of_nonneg_right hsHi1 hyLo0
      _ < 1 := by simpa using hvalid.2.2
  have hlogRY := RationalEnclosure.contains_halfLogOneSubEnclosure
    halfLogTerms hz0 hz1
  have hsum := RationalEnclosure.contains_add hlogV hlogRY
  simpa [lrCompactVSameYBEndpointEnclosure, lrCompactVBFullX,
    lrCompactVSameYEndpointZQ, Rat.cast_mul] using hsum

theorem lrCompactVBFullX_eq_flowB
    {R v x : ℝ} (hR : 0 ≤ R) (hx : 0 ≤ x) :
    lrCompactVBFullX R v (v ^ 2 * x) =
      lrFlowB R v (Real.sqrt x) := by
  have hsquareR : (Real.sqrt R) ^ 2 = R := Real.sq_sqrt hR
  have hsquareX : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt hx
  have hargSquare :
      (Real.sqrt R * v * Real.sqrt x) ^ 2 =
        R * (v ^ 2 * x) := by
    rw [mul_pow, mul_pow, hsquareR, hsquareX]
    ring
  unfold lrCompactVBFullX lrFlowB lrFlowBeta lrL
  rw [hargSquare]
  ring

theorem hasDerivAt_lrCompactVSameYSlack_y
    {lambda R v y : ℝ} (hry : 1 - R * y ≠ 0)
    (hy : 1 - y ≠ 0) :
    HasDerivAt (fun z ↦ lrCompactVSameYSlack lambda R v z)
      (((1 - R) - lambda * R * (1 - y)) /
        (2 * (1 - y) * (1 - R * y))) y := by
  have hinnerRY : HasDerivAt (fun z : ℝ ↦ 1 - R * z) (-R) y := by
    convert (hasDerivAt_const y 1).sub
      ((hasDerivAt_id y).const_mul R) using 1
    all_goals ring
  have hinnerY : HasDerivAt (fun z : ℝ ↦ 1 - z) (-1) y := by
    convert (hasDerivAt_const y 1).sub (hasDerivAt_id y) using 1
    all_goals ring
  have hlogRY := hinnerRY.log hry
  have hlogY := hinnerY.log hy
  have hD := (hlogRY.sub hlogY).const_mul (1 / 2 : ℝ)
  have hB := (hasDerivAt_const y (Real.log (1 + v))).sub
    (hlogRY.const_mul (1 / 2 : ℝ))
  have hslack := hD.sub (hB.const_mul lambda)
  unfold lrCompactVSameYSlack lrCompactVDFullX lrCompactVBFullX
  convert hslack using 1
  all_goals
    field_simp [hry, hy]
    ring

/-- The rational endpoint slope condition makes the same-`y` slack increase
from `yLo` throughout the box. -/
theorem lrCompactVSameYSlack_mono_y
    {lambda R v yLo y : ℝ}
    (hlambda : 0 ≤ lambda) (hR0 : 0 ≤ R) (hR1 : R < 1)
    (hyLo0 : 0 ≤ yLo) (hyLe : yLo ≤ y) (hy1 : y < 1)
    (hslope : lambda * R * (1 - yLo) ≤ 1 - R) :
    lrCompactVSameYSlack lambda R v yLo ≤
      lrCompactVSameYSlack lambda R v y := by
  have hmono : MonotoneOn
      (fun z ↦ lrCompactVSameYSlack lambda R v z) (Icc yLo y) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc yLo y)
    · intro z hz
      have hz0 : 0 ≤ z := hyLo0.trans hz.1
      have hz1 : z < 1 := hz.2.trans_lt hy1
      have hRz : R * z < 1 := by
        calc
          R * z ≤ 1 * z := mul_le_mul_of_nonneg_right hR1.le hz0
          _ < 1 := by simpa using hz1
      exact (hasDerivAt_lrCompactVSameYSlack_y
        (by linarith) (by linarith)).continuousAt.continuousWithinAt
    · intro z hz
      rw [interior_Icc] at hz
      have hz0 : 0 ≤ z := hyLo0.trans hz.1.le
      have hz1 : z < 1 := hz.2.trans hy1
      have hRz : R * z < 1 := by
        calc
          R * z ≤ 1 * z := mul_le_mul_of_nonneg_right hR1.le hz0
          _ < 1 := by simpa using hz1
      exact (hasDerivAt_lrCompactVSameYSlack_y
        (by linarith) (by linarith)).differentiableAt
          |>.differentiableWithinAt
    · intro z hz
      rw [interior_Icc] at hz
      have hz0 : 0 ≤ z := hyLo0.trans hz.1.le
      have hz1 : z < 1 := hz.2.trans hy1
      have hRz : R * z < 1 := by
        calc
          R * z ≤ 1 * z := mul_le_mul_of_nonneg_right hR1.le hz0
          _ < 1 := by simpa using hz1
      have hfactor : 0 ≤ lambda * R := mul_nonneg hlambda hR0
      have hsideZ : lambda * R * (1 - z) ≤ 1 - R := by
        exact (mul_le_mul_of_nonneg_left
          (sub_le_sub_left hz.1.le 1) hfactor).trans hslope
      rw [(hasDerivAt_lrCompactVSameYSlack_y
        (by linarith) (by linarith)).deriv]
      exact div_nonneg (sub_nonneg.mpr hsideZ)
        (mul_nonneg
          (mul_nonneg (by norm_num) (sub_nonneg.mpr hz1.le))
          (sub_nonneg.mpr hRz.le))
  exact hmono ⟨le_rfl, hyLe⟩ ⟨hyLe, le_rfl⟩ hyLe

theorem lrCompactVSameYSlack_anti_v
    {lambda R v vHi y : ℝ} (hlambda : 0 ≤ lambda)
    (hv0 : 0 ≤ v) (hvLe : v ≤ vHi) :
    lrCompactVSameYSlack lambda R vHi y ≤
      lrCompactVSameYSlack lambda R v y := by
  have hlog : Real.log (1 + v) ≤ Real.log (1 + vHi) :=
    Real.log_le_log (by linarith) (by linarith)
  have hscaled := mul_le_mul_of_nonneg_left hlog hlambda
  unfold lrCompactVSameYSlack lrCompactVBFullX
  linarith

theorem lrCompactVSameYSlack_anti_R
    {lambda R RHi v y : ℝ} (hlambda : 0 ≤ lambda)
    (hRLe : R ≤ RHi) (hRHi1 : RHi < 1)
    (hy0 : 0 ≤ y) (hy1 : y < 1) :
    lrCompactVSameYSlack lambda RHi v y ≤
      lrCompactVSameYSlack lambda R v y := by
  have hRHiY : RHi * y < 1 := by
    calc
      RHi * y ≤ 1 * y :=
        mul_le_mul_of_nonneg_right hRHi1.le hy0
      _ < 1 := by simpa using hy1
  have hargOrder : 1 - RHi * y ≤ 1 - R * y := by
    exact sub_le_sub_left
      (mul_le_mul_of_nonneg_right hRLe hy0) 1
  have hlog : Real.log (1 - RHi * y) ≤
      Real.log (1 - R * y) :=
    Real.log_le_log (by linarith) hargOrder
  have hcoeff : 0 ≤ (1 + lambda) / 2 := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hlog hcoeff
  unfold lrCompactVSameYSlack lrCompactVDFullX lrCompactVBFullX
  nlinarith

/-- The same-`y` endpoint is a lower bound for `D-lambda*B` throughout a
valid compact box whenever the executable slope condition holds. -/
theorem lrCompactVSameYSlack_corner_le
    {lambda : ℝ} (hlambda : 0 ≤ lambda)
    {box : CertificateBox} {point : CertificatePoint}
    (hvalid : LRCompactVDirectDValid box)
    (hpoint : box.Contains point) (hinterior : LRCompactVInterior point)
    (hslope : lambda * (box.sHi : ℝ) *
        (1 - (lrCompactVDirectDYLoQ box : ℝ)) ≤
      1 - (box.sHi : ℝ)) :
    lrCompactVSameYSlack lambda (box.sHi : ℝ) (box.kHi : ℝ)
        (lrCompactVDirectDYLoQ box : ℝ) ≤
      lrCompactVSameYSlack lambda point.s point.k
        (point.k ^ 2 * point.chi) := by
  rcases hvalid.1 with
    ⟨hsLo0, hsLoHi, hsHi1, hkLo0, hkLoHi, hkHi1,
      hchiLo0, hchiLoHi, hchiHi1⟩
  have hRHi0 : (0 : ℝ) ≤ box.sHi := by exact_mod_cast hsLo0.trans hsLoHi
  have hRHi1 : (box.sHi : ℝ) < 1 := by exact_mod_cast hvalid.2.1
  have hv0 : 0 ≤ point.k :=
    (by exact_mod_cast hkLo0 : (0 : ℝ) ≤ box.kLo) |>.trans
      hpoint.2.2.1
  have hyLo0 : (0 : ℝ) ≤ lrCompactVDirectDYLoQ box := by
    rw [cast_lrCompactVDirectDYLoQ]
    exact mul_nonneg (sq_nonneg _)
      (by exact_mod_cast hchiLo0)
  have hy := lrCompactVYEnclosure_sound hvalid.1 hpoint
  have hyLe : (lrCompactVDirectDYLoQ box : ℝ) ≤
      point.k ^ 2 * point.chi := by
    simpa [lrCompactVYEnclosure] using hy.1
  have hy1 : point.k ^ 2 * point.chi < 1 := by
    have hvSqLt : point.k ^ 2 < 1 := by
      nlinarith [hinterior.2.1.1, hinterior.2.1.2]
    calc
      point.k ^ 2 * point.chi < 1 * point.chi :=
        mul_lt_mul_of_pos_right hvSqLt hinterior.2.2.1
      _ < 1 := by simpa using hinterior.2.2.2
  have hyStep := lrCompactVSameYSlack_mono_y
    (lambda := lambda) (R := (box.sHi : ℝ))
    (v := (box.kHi : ℝ))
    (yLo := (lrCompactVDirectDYLoQ box : ℝ))
    (y := point.k ^ 2 * point.chi)
    hlambda hRHi0 hRHi1 hyLo0 hyLe hy1 hslope
  have hvStep := lrCompactVSameYSlack_anti_v
    (lambda := lambda) (R := (box.sHi : ℝ))
    (v := point.k) (vHi := (box.kHi : ℝ))
    (y := point.k ^ 2 * point.chi)
    hlambda hv0 hpoint.2.2.2.1
  have hRStep := lrCompactVSameYSlack_anti_R
    (lambda := lambda) (R := point.s) (RHi := (box.sHi : ℝ))
    (v := point.k) (y := point.k ^ 2 * point.chi)
    hlambda hpoint.2.1 hRHi1 (hyLo0.trans hyLe) hy1
  exact hyStep.trans (hvStep.trans hRStep)

/-- Checker-facing same-`y` ratio theorem.  All transcendental endpoint
quantities are enclosed by kernel-proved series; the remaining monotonicity
condition is an exact rational comparison. -/
theorem lrCompactVSameYLambda_mul_flowB_le_flowD
    (logTerms halfLogTerms dTerms : ℕ)
    {box : CertificateBox} {point : CertificatePoint}
    {logOnePlusVHi : RationalEnclosure.LogRangeCertificate}
    (hvalid : LRCompactVDirectDValid box)
    (hpoint : box.Contains point) (hinterior : LRCompactVInterior point)
    (hlogcheck : logOnePlusVHi.check (1 + box.kHi) = true)
    (hbUpper : (0 : ℚ) <
      (lrCompactVSameYBEndpointEnclosure
        logTerms halfLogTerms box logOnePlusVHi).upper)
    (hslope :
      let bEndpoint := lrCompactVSameYBEndpointEnclosure
        logTerms halfLogTerms box logOnePlusVHi
      let d := lrCompactVDirectDEnclosure dTerms box
      let lambda := lrCompactVSameYLambda bEndpoint d
      lambda * box.sHi * (1 - lrCompactVDirectDYLoQ box) ≤
        1 - box.sHi) :
    let bEndpoint := lrCompactVSameYBEndpointEnclosure
      logTerms halfLogTerms box logOnePlusVHi
    let d := lrCompactVDirectDEnclosure dTerms box
    let lambda := lrCompactVSameYLambda bEndpoint d
    (lambda : ℝ) *
        lrFlowB point.s point.k (Real.sqrt point.chi) ≤
      lrFlowD point.s point.k (Real.sqrt point.chi) := by
  let bEndpoint := lrCompactVSameYBEndpointEnclosure
    logTerms halfLogTerms box logOnePlusVHi
  let d := lrCompactVDirectDEnclosure dTerms box
  let lambda := lrCompactVSameYLambda bEndpoint d
  have hbEndpoint := lrCompactVSameYBEndpointEnclosure_sound
    logTerms halfLogTerms hvalid hlogcheck
  have hdEndpoint :=
    lrCompactVDirectDEnclosure_contains_corner dTerms hvalid
  have hRHi0 : (0 : ℝ) ≤ box.sHi := by
    exact_mod_cast hvalid.1.1.trans hvalid.1.2.1
  have hRHi1 : (box.sHi : ℝ) < 1 := by exact_mod_cast hvalid.2.1
  have hyLo0 : (0 : ℝ) ≤ lrCompactVDirectDYLoQ box := by
    rw [cast_lrCompactVDirectDYLoQ]
    exact mul_nonneg (sq_nonneg _)
      (by exact_mod_cast hvalid.1.2.2.2.2.2.2.1)
  have hyLo1 : (lrCompactVDirectDYLoQ box : ℝ) < 1 := by
    exact_mod_cast hvalid.2.2
  have hargOrder :
      1 - (lrCompactVDirectDYLoQ box : ℝ) ≤
        1 - (box.sHi : ℝ) *
          (lrCompactVDirectDYLoQ box : ℝ) := by
    have hprod := mul_le_mul_of_nonneg_right
      (show (box.sHi : ℝ) ≤ 1 by exact_mod_cast hvalid.1.2.2.1)
      hyLo0
    linarith
  have hlogOrder := Real.log_le_log (by linarith) hargOrder
  have hD0 : 0 ≤ lrCompactVDFullX (box.sHi : ℝ)
      (lrCompactVDirectDYLoQ box : ℝ) := by
    unfold lrCompactVDFullX
    linarith
  have hlambdaEndpoint :
      (lambda : ℝ) *
          lrCompactVBFullX (box.sHi : ℝ) (box.kHi : ℝ)
            (lrCompactVDirectDYLoQ box : ℝ) ≤
        lrCompactVDFullX (box.sHi : ℝ)
          (lrCompactVDirectDYLoQ box : ℝ) := by
    dsimp [lambda, bEndpoint, d]
    exact cast_lrCompactVSameYLambda_mul_le
      hbEndpoint.2 hbUpper hdEndpoint.1 hD0
  have hlambdaQ : (0 : ℚ) ≤ lambda := by
    dsimp [lambda]
    exact lrCompactVSameYLambda_nonnegative hbUpper
  have hlambda : (0 : ℝ) ≤ lambda := by exact_mod_cast hlambdaQ
  have hslopeReal :
      (lambda : ℝ) * (box.sHi : ℝ) *
          (1 - (lrCompactVDirectDYLoQ box : ℝ)) ≤
        1 - (box.sHi : ℝ) := by
    exact_mod_cast (show
      lambda * box.sHi * (1 - lrCompactVDirectDYLoQ box) ≤
        1 - box.sHi by simpa [lambda, bEndpoint, d] using hslope)
  have hcorner := lrCompactVSameYSlack_corner_le
    hlambda hvalid hpoint hinterior hslopeReal
  have hcorner0 :
      0 ≤ lrCompactVSameYSlack lambda (box.sHi : ℝ) (box.kHi : ℝ)
        (lrCompactVDirectDYLoQ box : ℝ) := by
    exact sub_nonneg.mpr hlambdaEndpoint
  have hpoint0 := hcorner0.trans hcorner
  have hR0 : 0 ≤ point.s :=
    (by exact_mod_cast hvalid.1.1 : (0 : ℝ) ≤ box.sLo) |>.trans
      hpoint.1
  have hx0 : 0 ≤ point.chi :=
    (by exact_mod_cast hvalid.1.2.2.2.2.2.2.1 :
      (0 : ℝ) ≤ box.chiLo) |>.trans hpoint.2.2.2.2.1
  unfold lrCompactVSameYSlack at hpoint0
  rw [lrCompactVDFullX_eq_flowD hR0 hx0,
    lrCompactVBFullX_eq_flowB hR0 hx0] at hpoint0
  exact sub_nonneg.mp hpoint0

end CourtadeKumar
