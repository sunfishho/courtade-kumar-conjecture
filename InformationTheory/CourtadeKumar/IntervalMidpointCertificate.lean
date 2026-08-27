import InformationTheory.CourtadeKumar.ExactIntervalArithmetic

/-!
# Midpoint-form interval certificates

This file proves the three-coordinate midpoint estimate used at accepted
determinant leaves.  It is independent of how the value and derivative
enclosures are computed.  Later modules may establish the coordinatewise
Lipschitz hypotheses by verified interval automatic differentiation.
-/

namespace CourtadeKumar

def CertificateBox.sInterval (box : CertificateBox) : RationalEnclosure :=
  ⟨box.sLo, box.sHi⟩

def CertificateBox.kInterval (box : CertificateBox) : RationalEnclosure :=
  ⟨box.kLo, box.kHi⟩

def CertificateBox.chiInterval (box : CertificateBox) : RationalEnclosure :=
  ⟨box.chiLo, box.chiHi⟩

/-- Exact rational midpoint of a certificate box, interpreted in `ℝ³`. -/
def CertificateBox.midpoint (box : CertificateBox) : CertificatePoint where
  s := RationalEnclosure.center box.sInterval
  k := RationalEnclosure.center box.kInterval
  chi := RationalEnclosure.center box.chiInterval

theorem CertificateBox.midpoint_mem
    {box : CertificateBox} {point : CertificatePoint}
    (hpoint : box.Contains point) :
    box.Contains box.midpoint := by
  rcases hpoint with ⟨hsLo, hsHi, hkLo, hkHi, hchiLo, hchiHi⟩
  have hsValid : (box.sLo : ℝ) ≤ (box.sHi : ℝ) := hsLo.trans hsHi
  have hkValid : (box.kLo : ℝ) ≤ (box.kHi : ℝ) := hkLo.trans hkHi
  have hchiValid : (box.chiLo : ℝ) ≤ (box.chiHi : ℝ) := hchiLo.trans hchiHi
  have hsMid : (box.sLo : ℝ) ≤ box.midpoint.s ∧
      box.midpoint.s ≤ (box.sHi : ℝ) := by
    constructor <;>
      norm_num [CertificateBox.midpoint, RationalEnclosure.center,
        CertificateBox.sInterval] <;> linarith
  have hkMid : (box.kLo : ℝ) ≤ box.midpoint.k ∧
      box.midpoint.k ≤ (box.kHi : ℝ) := by
    constructor <;>
      norm_num [CertificateBox.midpoint, RationalEnclosure.center,
        CertificateBox.kInterval] <;> linarith
  have hchiMid : (box.chiLo : ℝ) ≤ box.midpoint.chi ∧
      box.midpoint.chi ≤ (box.chiHi : ℝ) := by
    constructor <;>
      norm_num [CertificateBox.midpoint, RationalEnclosure.center,
        CertificateBox.chiInterval] <;> linarith
  exact ⟨hsMid.1, hsMid.2, hkMid.1, hkMid.2, hchiMid.1, hchiMid.2⟩

/-- The absolute-value bound represented by a derivative enclosure. -/
def RationalEnclosure.maxAbs (interval : RationalEnclosure) : ℚ :=
  max |interval.lower| |interval.upper|

theorem RationalEnclosure.maxAbs_nonnegative (interval : RationalEnclosure) :
    (0 : ℚ) ≤ interval.maxAbs := by
  exact (abs_nonneg interval.lower).trans (le_max_left _ _)

theorem RationalEnclosure.abs_le_maxAbs
    {interval : RationalEnclosure} {x : ℝ}
    (hx : interval.Contains x) :
    |x| ≤ (interval.maxAbs : ℝ) := by
  have hlower : -((interval.maxAbs : ℚ) : ℝ) ≤ x := by
    have hmax : |interval.lower| ≤ interval.maxAbs := le_max_left _ _
    have hneg : -(interval.maxAbs : ℚ) ≤ interval.lower := by
      exact (neg_le_of_abs_le hmax)
    have hnegReal : -((interval.maxAbs : ℚ) : ℝ) ≤
        (interval.lower : ℝ) := by
      exact_mod_cast hneg
    exact hnegReal.trans hx.1
  have hupper : x ≤ (interval.maxAbs : ℚ) := by
    have hmax : |interval.upper| ≤ interval.maxAbs := le_max_right _ _
    have hup : interval.upper ≤ interval.maxAbs := le_trans (le_abs_self _) hmax
    have hupReal : (interval.upper : ℝ) ≤
        (interval.maxAbs : ℚ) := by
      exact_mod_cast hup
    exact hx.2.trans hupReal
  exact (abs_le).2 ⟨hlower, hupper⟩

/-- Coordinatewise Lipschitz control of a target on one certificate box. -/
structure BoxCoordinateLipschitz
    (target : CertificatePoint → ℝ) (box : CertificateBox)
    (sBound kBound chiBound : ℝ) : Prop where
  s : ∀ p q, box.Contains p → box.Contains q →
    p.k = q.k → p.chi = q.chi →
    |target p - target q| ≤ sBound * |p.s - q.s|
  k : ∀ p q, box.Contains p → box.Contains q →
    p.s = q.s → p.chi = q.chi →
    |target p - target q| ≤ kBound * |p.k - q.k|
  chi : ∀ p q, box.Contains p → box.Contains q →
    p.s = q.s → p.k = q.k →
    |target p - target q| ≤ chiBound * |p.chi - q.chi|

/-- The data recomputed at a midpoint-form accepted leaf. -/
structure MidpointCertificate where
  value : RationalEnclosure
  derivS : RationalEnclosure
  derivK : RationalEnclosure
  derivChi : RationalEnclosure

/-- Rational lower bound obtained from the midpoint value minus the three
derivative-radius losses. -/
def MidpointCertificate.lowerBound
    (box : CertificateBox) (certificate : MidpointCertificate) : ℚ :=
  certificate.value.lower -
    certificate.derivS.maxAbs * RationalEnclosure.radius box.sInterval -
    certificate.derivK.maxAbs * RationalEnclosure.radius box.kInterval -
    certificate.derivChi.maxAbs * RationalEnclosure.radius box.chiInterval

def MidpointCertificate.check
    (box : CertificateBox) (certificate : MidpointCertificate) : Bool :=
  decide (0 < certificate.lowerBound box)

theorem MidpointCertificate.sound
    {target : CertificatePoint → ℝ}
    {box : CertificateBox} {certificate : MidpointCertificate}
    (hvalue : certificate.value.Contains (target box.midpoint))
    (hlipschitz : BoxCoordinateLipschitz target box
      certificate.derivS.maxAbs certificate.derivK.maxAbs
      certificate.derivChi.maxAbs)
    (hcheck : certificate.check box = true)
    {point : CertificatePoint} (hpoint : box.Contains point) :
    0 < target point := by
  let center := box.midpoint
  let afterS : CertificatePoint := { point with s := center.s }
  let afterK : CertificatePoint := { afterS with k := center.k }
  have hcenter : box.Contains center := box.midpoint_mem hpoint
  have hafterS : box.Contains afterS := by
    rcases hpoint with ⟨_, _, hkLo, hkHi, hchiLo, hchiHi⟩
    exact ⟨hcenter.1, hcenter.2.1, hkLo, hkHi, hchiLo, hchiHi⟩
  have hafterK : box.Contains afterK := by
    exact ⟨hcenter.1, hcenter.2.1, hcenter.2.2.1, hcenter.2.2.2.1,
      hpoint.2.2.2.2.1, hpoint.2.2.2.2.2⟩
  have hsRadius :
      |point.s - center.s| ≤ (RationalEnclosure.radius box.sInterval : ℝ) := by
    exact RationalEnclosure.abs_sub_center_le_radius
      (a := box.sInterval) ⟨hpoint.1, hpoint.2.1⟩
  have hkRadius :
      |afterS.k - center.k| ≤ (RationalEnclosure.radius box.kInterval : ℝ) := by
    exact RationalEnclosure.abs_sub_center_le_radius
      (a := box.kInterval) ⟨hpoint.2.2.1, hpoint.2.2.2.1⟩
  have hchiRadius :
      |afterK.chi - center.chi| ≤
        (RationalEnclosure.radius box.chiInterval : ℝ) := by
    exact RationalEnclosure.abs_sub_center_le_radius
      (a := box.chiInterval) ⟨hpoint.2.2.2.2.1, hpoint.2.2.2.2.2⟩
  have hs := hlipschitz.s point afterS hpoint hafterS rfl rfl
  have hk := hlipschitz.k afterS afterK hafterS hafterK rfl rfl
  have hchi := hlipschitz.chi afterK center hafterK hcenter rfl rfl
  have hsBound :
      |target point - target afterS| ≤
        (certificate.derivS.maxAbs : ℝ) *
          (RationalEnclosure.radius box.sInterval : ℝ) :=
    hs.trans (mul_le_mul_of_nonneg_left hsRadius
      (by exact_mod_cast certificate.derivS.maxAbs_nonnegative))
  have hkBound :
      |target afterS - target afterK| ≤
        (certificate.derivK.maxAbs : ℝ) *
          (RationalEnclosure.radius box.kInterval : ℝ) :=
    hk.trans (mul_le_mul_of_nonneg_left hkRadius
      (by exact_mod_cast certificate.derivK.maxAbs_nonnegative))
  have hchiBound :
      |target afterK - target center| ≤
        (certificate.derivChi.maxAbs : ℝ) *
          (RationalEnclosure.radius box.chiInterval : ℝ) :=
    hchi.trans (mul_le_mul_of_nonneg_left hchiRadius
      (by exact_mod_cast certificate.derivChi.maxAbs_nonnegative))
  have htotal :
      |target point - target center| ≤
        (certificate.derivS.maxAbs : ℝ) *
            (RationalEnclosure.radius box.sInterval : ℝ) +
          (certificate.derivK.maxAbs : ℝ) *
            (RationalEnclosure.radius box.kInterval : ℝ) +
          (certificate.derivChi.maxAbs : ℝ) *
            (RationalEnclosure.radius box.chiInterval : ℝ) := by
    calc
      |target point - target center| =
          |(target point - target afterS) +
            (target afterS - target afterK) +
            (target afterK - target center)| := by congr 1; ring
      _ ≤ |target point - target afterS| +
          |target afterS - target afterK| +
          |target afterK - target center| := by
            calc
              _ ≤ |(target point - target afterS) +
                    (target afterS - target afterK)| +
                    |target afterK - target center| := abs_add_le _ _
              _ ≤ (|target point - target afterS| +
                    |target afterS - target afterK|) +
                    |target afterK - target center| :=
                  add_le_add (abs_add_le _ _) le_rfl
      _ ≤ _ := add_le_add (add_le_add hsBound hkBound) hchiBound
  have hpositive : (0 : ℚ) < certificate.lowerBound box := by
    simpa [MidpointCertificate.check] using hcheck
  have hpositiveReal : (0 : ℝ) < (certificate.lowerBound box : ℚ) := by
    exact_mod_cast hpositive
  have habsLower : -(target point - target center) ≤
      |target point - target center| := neg_le_abs _
  have hvalueLower : (certificate.value.lower : ℝ) ≤ target center := by
    change (certificate.value.lower : ℝ) ≤ target box.midpoint
    exact hvalue.1
  norm_num [MidpointCertificate.lowerBound] at hpositiveReal
  norm_num at htotal
  linarith

end CourtadeKumar
