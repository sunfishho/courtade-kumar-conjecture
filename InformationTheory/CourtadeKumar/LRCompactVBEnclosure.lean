import InformationTheory.CourtadeKumar.LRCompactVPZeroSeries

/-!
# Checked logarithmic enclosure for the compact `B` factor

In squared compact coordinates,

`B(R,v,√x) = log(1+v) - (1/2) log(1-R v² x)`.

Both logarithm inputs have exact rational endpoint intervals.  Untrusted
range-reduction data is accepted only through the kernel-proved logarithm
checker.
-/

namespace CourtadeKumar

/-- Exact interval for `1+v`. -/
def lrCompactVOnePlusVEnclosure (box : CertificateBox) :
    RationalEnclosure :=
  RationalEnclosure.add (RationalEnclosure.point 1) box.kInterval

theorem lrCompactVOnePlusVEnclosure_sound
    {box : CertificateBox} {point : CertificatePoint}
    (hpoint : box.Contains point) :
    (lrCompactVOnePlusVEnclosure box).Contains (1 + point.k) := by
  have hv : box.kInterval.Contains point.k :=
    ⟨hpoint.2.2.1, hpoint.2.2.2.1⟩
  have hone : (RationalEnclosure.point 1).Contains (1 : ℝ) := by
    norm_num [RationalEnclosure.point, RationalEnclosure.Contains]
  exact RationalEnclosure.contains_add hone hv

/-- Exact monotone-product interval for `R v² x`. -/
def lrCompactVRYEnclosure (box : CertificateBox) : RationalEnclosure :=
  RationalEnclosure.mulNonnegative box.sInterval
    (lrCompactVYEnclosure box)

theorem lrCompactVRYEnclosure_sound
    {box : CertificateBox} {point : CertificatePoint}
    (hbox : LRCompactVBoxValid box) (hpoint : box.Contains point) :
    (lrCompactVRYEnclosure box).Contains
      (point.s * (point.k ^ 2 * point.chi)) := by
  have hR : box.sInterval.Contains point.s :=
    ⟨hpoint.1, hpoint.2.1⟩
  have hy := lrCompactVYEnclosure_sound hbox hpoint
  have hyLower : (0 : ℚ) ≤ (lrCompactVYEnclosure box).lower := by
    simp only [lrCompactVYEnclosure]
    exact mul_nonneg (sq_nonneg box.kLo) hbox.2.2.2.2.2.2.1
  exact RationalEnclosure.contains_mulNonnegative hbox.1 hyLower hR hy

/-- Exact interval for `1-R v² x`. -/
def lrCompactVOneSubRYEnclosure (box : CertificateBox) :
    RationalEnclosure :=
  RationalEnclosure.sub (RationalEnclosure.point 1)
    (lrCompactVRYEnclosure box)

theorem lrCompactVOneSubRYEnclosure_sound
    {box : CertificateBox} {point : CertificatePoint}
    (hbox : LRCompactVBoxValid box) (hpoint : box.Contains point) :
    (lrCompactVOneSubRYEnclosure box).Contains
      (1 - point.s * (point.k ^ 2 * point.chi)) := by
  have hone : (RationalEnclosure.point 1).Contains (1 : ℝ) := by
    norm_num [RationalEnclosure.point, RationalEnclosure.Contains]
  exact RationalEnclosure.contains_sub hone
    (lrCompactVRYEnclosure_sound hbox hpoint)

/-- Untrusted range reductions for the two logarithms in `B`. -/
structure LRCompactVBCertificate where
  logOnePlusV : RationalEnclosure.LogIntervalCertificate
  logOneSubRY : RationalEnclosure.LogIntervalCertificate

namespace LRCompactVBCertificate

def check (box : CertificateBox)
    (certificate : LRCompactVBCertificate) : Bool :=
  decide (
    LRCompactVBoxValid.check box = true ∧
    certificate.logOnePlusV.check
      (lrCompactVOnePlusVEnclosure box) = true ∧
    certificate.logOneSubRY.check
      (lrCompactVOneSubRYEnclosure box) = true)

def evaluate (terms : ℕ) (box : CertificateBox)
    (certificate : LRCompactVBCertificate) : RationalEnclosure :=
  RationalEnclosure.add
    (certificate.logOnePlusV.enclosure terms)
    (RationalEnclosure.scale (-1 / 2)
      (certificate.logOneSubRY.enclosure terms))

theorem sound
    (terms : ℕ) {box : CertificateBox} {point : CertificatePoint}
    {certificate : LRCompactVBCertificate}
    (hpoint : box.Contains point) (hinterior : LRCompactVInterior point)
    (hcheck : certificate.check box = true) :
    (certificate.evaluate terms box).Contains
      (lrFlowB point.s point.k (Real.sqrt point.chi)) := by
  have hparts :
      LRCompactVBoxValid.check box = true ∧
      certificate.logOnePlusV.check
        (lrCompactVOnePlusVEnclosure box) = true ∧
      certificate.logOneSubRY.check
        (lrCompactVOneSubRYEnclosure box) = true := by
    simpa [check] using hcheck
  have hbox := LRCompactVBoxValid.of_check hparts.1
  have hlogV := certificate.logOnePlusV.sound terms hparts.2.1
    (lrCompactVOnePlusVEnclosure_sound hpoint)
  have hlogRY := certificate.logOneSubRY.sound terms hparts.2.2
    (lrCompactVOneSubRYEnclosure_sound hbox hpoint)
  have hscaled := RationalEnclosure.contains_scale (-1 / 2 : ℚ) hlogRY
  have hsum := RationalEnclosure.contains_add hlogV hscaled
  have hsquareR : (Real.sqrt point.s) ^ 2 = point.s :=
    Real.sq_sqrt hinterior.1.1.le
  have hsquareX : (Real.sqrt point.chi) ^ 2 = point.chi :=
    Real.sq_sqrt hinterior.2.2.1.le
  have hargSquare :
      (Real.sqrt point.s * point.k * Real.sqrt point.chi) ^ 2 =
        point.s * (point.k ^ 2 * point.chi) := by
    rw [mul_pow, mul_pow, hsquareR, hsquareX]
    ring
  unfold evaluate lrFlowB lrFlowBeta lrL
  rw [hargSquare]
  convert hsum using 1 <;> norm_num <;> ring

end LRCompactVBCertificate

end CourtadeKumar
