import InformationTheory.CourtadeKumar.LRCompactVLeafChecker

/-!
# One-sided physical-domain discard for compact `V` boxes

The compact chart is relevant only when

`J=(1+x)B-A > 0`.

A discard leaf proves an upper enclosure for `J` is nonpositive.  As with
accepted leaves, all arithmetic is recomputed by Lean and the only untrusted
data consists of checked logarithm range reductions.
-/

namespace CourtadeKumar

/-- Exact interval for `1-v²x`. -/
def lrCompactVOneSubYEnclosure (box : CertificateBox) :
    RationalEnclosure :=
  RationalEnclosure.sub (RationalEnclosure.point 1)
    (lrCompactVYEnclosure box)

theorem lrCompactVOneSubYEnclosure_sound
    {box : CertificateBox} {point : CertificatePoint}
    (hbox : LRCompactVBoxValid box) (hpoint : box.Contains point) :
    (lrCompactVOneSubYEnclosure box).Contains
      (1 - point.k ^ 2 * point.chi) := by
  have hone : (RationalEnclosure.point 1).Contains (1 : ℝ) := by
    norm_num [RationalEnclosure.point, RationalEnclosure.Contains]
  exact RationalEnclosure.contains_sub hone
    (lrCompactVYEnclosure_sound hbox hpoint)

/-- Compact-coordinate form of `A`. -/
noncomputable def lrCompactVAX (v x : ℝ) : ℝ :=
  Real.log (1 + v) - (1 / 2 : ℝ) * Real.log (1 - v ^ 2 * x)

/-- Compact physicality scalar. -/
noncomputable def lrCompactVJX (point : CertificatePoint) : ℝ :=
  (1 + point.chi) *
      lrFlowB point.s point.k (Real.sqrt point.chi) -
    lrCompactVAX point.k point.chi

/-- Relevance predicate used by the compact subdivision tree. -/
def LRCompactVPhysical (point : CertificatePoint) : Prop :=
  LRCompactVInterior point ∧ 0 < lrCompactVJX point

theorem lrCompactVAX_flow
    {v t : ℝ} :
    lrCompactVAX v (t ^ 2) = lrFlowA v t := by
  unfold lrCompactVAX lrFlowA lrFlowBeta lrL
  rw [mul_pow]
  ring

theorem lrCompactVJX_flow
    {R v t : ℝ} (ht : 0 < t) :
    lrCompactVJX (lrCompactVFlowPoint R v t) = lrFlowJ R v t := by
  unfold lrCompactVJX lrCompactVFlowPoint
  rw [Real.sqrt_sq_eq_abs, abs_of_pos ht, lrCompactVAX_flow]
  unfold lrFlowJ lrFlowD
  ring

theorem lrCompactVFlowPoint_physical
    {R v t : ℝ} (hR : R ∈ Set.Ioo (0 : ℝ) 1)
    (hv : v ∈ Set.Ioo (0 : ℝ) 1)
    (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (hJ : 0 < lrFlowJ R v t) :
    LRCompactVPhysical (lrCompactVFlowPoint R v t) := by
  exact ⟨lrCompactVFlowPoint_interior hR hv ht,
    by simpa [lrCompactVJX_flow ht.1] using hJ⟩

/-- Discard payload.  The `B` certificate supplies the shared `log(1+v)`
range reduction; only one additional logarithm is needed for `A`. -/
structure LRCompactVDiscardCertificate where
  b : LRCompactVBCertificate
  logOneSubY : RationalEnclosure.LogIntervalCertificate

namespace LRCompactVDiscardCertificate

def aEnclosure (terms : ℕ) (box : CertificateBox)
    (certificate : LRCompactVDiscardCertificate) : RationalEnclosure :=
  RationalEnclosure.add
    (certificate.b.logOnePlusV.enclosure terms)
    (RationalEnclosure.scale (-1 / 2)
      (certificate.logOneSubY.enclosure terms))

def jEnclosure (terms : ℕ) (box : CertificateBox)
    (certificate : LRCompactVDiscardCertificate) : RationalEnclosure :=
  let onePlusX := RationalEnclosure.add
    (RationalEnclosure.point 1) box.chiInterval
  RationalEnclosure.sub
    (RationalEnclosure.mul onePlusX
      (certificate.b.evaluate terms box))
    (certificate.aEnclosure terms box)

def check (terms : ℕ) (box : CertificateBox)
    (certificate : LRCompactVDiscardCertificate) : Bool :=
  decide (
    certificate.b.check box = true ∧
    certificate.logOneSubY.check
      (lrCompactVOneSubYEnclosure box) = true ∧
    (certificate.jEnclosure terms box).upper ≤ 0)

theorem aEnclosure_sound
    (terms : ℕ) {box : CertificateBox} {point : CertificatePoint}
    {certificate : LRCompactVDiscardCertificate}
    (hpoint : box.Contains point)
    (hbcheck : certificate.b.check box = true)
    (hlogcheck : certificate.logOneSubY.check
      (lrCompactVOneSubYEnclosure box) = true) :
    (certificate.aEnclosure terms box).Contains
      (lrCompactVAX point.k point.chi) := by
  have hbparts :
      LRCompactVBoxValid.check box = true ∧
      certificate.b.logOnePlusV.check
        (lrCompactVOnePlusVEnclosure box) = true ∧
      certificate.b.logOneSubRY.check
        (lrCompactVOneSubRYEnclosure box) = true := by
    simpa [LRCompactVBCertificate.check] using hbcheck
  have hbox := LRCompactVBoxValid.of_check hbparts.1
  have hlogV := certificate.b.logOnePlusV.sound terms hbparts.2.1
    (lrCompactVOnePlusVEnclosure_sound hpoint)
  have hlogY := certificate.logOneSubY.sound terms hlogcheck
    (lrCompactVOneSubYEnclosure_sound hbox hpoint)
  have hscaled := RationalEnclosure.contains_scale (-1 / 2 : ℚ) hlogY
  unfold aEnclosure lrCompactVAX
  convert RationalEnclosure.contains_add hlogV hscaled using 1 <;> ring

theorem jEnclosure_sound
    (terms : ℕ) {box : CertificateBox} {point : CertificatePoint}
    {certificate : LRCompactVDiscardCertificate}
    (hpoint : box.Contains point) (hinterior : LRCompactVInterior point)
    (hbcheck : certificate.b.check box = true)
    (hlogcheck : certificate.logOneSubY.check
      (lrCompactVOneSubYEnclosure box) = true) :
    (certificate.jEnclosure terms box).Contains
      (lrCompactVJX point) := by
  have hB := certificate.b.sound terms hpoint hinterior hbcheck
  have hA := certificate.aEnclosure_sound terms hpoint hbcheck hlogcheck
  have hx : box.chiInterval.Contains point.chi :=
    ⟨hpoint.2.2.2.2.1, hpoint.2.2.2.2.2⟩
  have hone : (RationalEnclosure.point 1).Contains (1 : ℝ) := by
    norm_num [RationalEnclosure.point, RationalEnclosure.Contains]
  have honePlusX := RationalEnclosure.contains_add hone hx
  have hprod := RationalEnclosure.contains_mul honePlusX hB
  simpa [jEnclosure, lrCompactVJX] using
    RationalEnclosure.contains_sub hprod hA

theorem excludes_physical
    (terms : ℕ) {box : CertificateBox}
    {certificate : LRCompactVDiscardCertificate}
    (hcheck : certificate.check terms box = true) :
    ∀ point, box.Contains point → ¬ LRCompactVPhysical point := by
  have hparts :
      certificate.b.check box = true ∧
      certificate.logOneSubY.check
        (lrCompactVOneSubYEnclosure box) = true ∧
      (certificate.jEnclosure terms box).upper ≤ 0 := by
    simpa [check] using hcheck
  intro point hpoint hphysical
  have hJ := certificate.jEnclosure_sound terms hpoint
    hphysical.1 hparts.1 hparts.2.1
  have hUpperReal :
      ((certificate.jEnclosure terms box).upper : ℝ) ≤ 0 := by
    exact_mod_cast hparts.2.2
  linarith [hJ.2, hphysical.2]

end LRCompactVDiscardCertificate

/-- Concrete subdivision theorem with both accepted and discarded compact
leaves fully checked. -/
theorem lrCompactVPhysicalSubdivisionCertificate_sound
    (logTerms pZeroTerms wTerms N : ℕ)
    {box : CertificateBox}
    {certificate : SubdivisionCertificate
      LRCompactVLeafCertificate LRCompactVDiscardCertificate}
    (hcheck : certificate.check
      (LRCompactVLeafCertificate.check
        logTerms pZeroTerms wTerms N)
      (LRCompactVDiscardCertificate.check logTerms) box = true) :
    ∀ point, box.Contains point → LRCompactVPhysical point →
      0 ≤ lrCompactVReserveTarget point := by
  exact lrCompactVSubdivisionCertificate_sound
    logTerms pZeroTerms wTerms N
    (Relevant := LRCompactVPhysical)
    (fun point hpoint ↦ hpoint.1)
    (fun leaf data hleaf ↦ data.excludes_physical logTerms hleaf)
    hcheck

end CourtadeKumar
