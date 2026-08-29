import InformationTheory.CourtadeKumar.LRDeterminantIdealIntervalEvaluator

/-!
# Coarse global-L certificate for the first bounded ideal-core root

The direct endpoint checker asks for `E'(L₀) > 0`.  Near `k=1/32` this
quantity is positive but numerically tiny, making natural interval subdivision
needlessly large.  The exact separated identity gives a stronger computational
formulation with much larger reserves.

Writing

`E(L) = L * a + b + C₁/(L+C)`,

it is enough to check at `L₀` that

* `E(L₀) - C₁/(L₀+C) > margin`,
* `a = E'(L₀) + C₁/(L₀+C)^2 > 0`, and
* `C₁ >= 0`.

These three enclosures are derived solely from the already verified endpoint
evaluator.  Thus no new transcendental approximation enters the trusted base.
-/

namespace CourtadeKumar

open LRDeterminantIdealEvaluatorCertificate

def LRDeterminantIdealCoarseProperties
    (margin : ℝ) (point : CertificatePoint) : Prop :=
  margin <
      lrDeterminantIdealCore lrDeterminantIdealDeepL0 point.k point.chi -
        lrDeterminantIdealC1 point.k point.chi /
          (lrDeterminantIdealDeepL0 + lrDeterminantIdealC) ∧
    0 < lrDeterminantIdealLambda point.k point.chi / 2 ∧
    0 ≤ lrDeterminantIdealC1 point.k point.chi

/-- Coarse propagation from DA2.  Unlike the direct endpoint criterion, this
does not pay for the small cancellation in `E'(L₀)`. -/
theorem lrDeterminantIdealCore_gt_of_coarseProperties
    {L margin : ℝ} {point : CertificatePoint}
    (hL : lrDeterminantIdealDeepL0 ≤ L)
    (hcoarse : LRDeterminantIdealCoarseProperties margin point) :
    margin < lrDeterminantIdealCore L point.k point.chi := by
  change
    margin <
        lrDeterminantIdealCore lrDeterminantIdealDeepL0 point.k point.chi -
          lrDeterminantIdealC1 point.k point.chi /
            (lrDeterminantIdealDeepL0 + lrDeterminantIdealC) ∧
      0 < lrDeterminantIdealLambda point.k point.chi / 2 ∧
      0 ≤ lrDeterminantIdealC1 point.k point.chi at hcoarse
  rcases hcoarse with ⟨hcoarse, hslopeStrict, hc1⟩
  have hbase := lrDeterminantIdealDeepL0_add_C_pos
  have htop : 0 < L + lrDeterminantIdealC := by linarith
  have hslope : 0 ≤ lrDeterminantIdealLambda point.k point.chi / 2 :=
    hslopeStrict.le
  have hdelta : 0 ≤
      (L - lrDeterminantIdealDeepL0) *
        (lrDeterminantIdealLambda point.k point.chi / 2) :=
    mul_nonneg (sub_nonneg.mpr hL) hslope
  have htail : 0 ≤
      lrDeterminantIdealC1 point.k point.chi /
        (L + lrDeterminantIdealC) :=
    div_nonneg hc1 htop.le
  rw [lrDeterminantIdealCore_eq_separated hbase.ne'] at hcoarse
  rw [lrDeterminantIdealCore_eq_separated htop.ne']
  have hbaseline : margin <
      lrDeterminantIdealDeepL0 *
          lrDeterminantIdealLambda point.k point.chi / 2 +
        lrDeterminantIdealRInf point.k point.chi := by
    have hcancel :
        lrDeterminantIdealDeepL0 *
              lrDeterminantIdealLambda point.k point.chi / 2 +
            lrDeterminantIdealRInf point.k point.chi +
              lrDeterminantIdealC1 point.k point.chi /
                (lrDeterminantIdealDeepL0 + lrDeterminantIdealC) -
            lrDeterminantIdealC1 point.k point.chi /
              (lrDeterminantIdealDeepL0 + lrDeterminantIdealC) =
          lrDeterminantIdealDeepL0 *
              lrDeterminantIdealLambda point.k point.chi / 2 +
            lrDeterminantIdealRInf point.k point.chi := by ring
    rw [hcancel] at hcoarse
    exact hcoarse
  nlinarith

namespace LRDeterminantIdealCoarseEvaluator

def uI (terms : ℕ)
    (certificate : LRDeterminantIdealEvaluatorCertificate) :
    RationalEnclosure :=
  certificate.l0PlusCI terms

def uSquareI (terms : ℕ)
    (certificate : LRDeterminantIdealEvaluatorCertificate) :
    RationalEnclosure :=
  RationalEnclosure.mulNonnegative
    (uI terms certificate) (uI terms certificate)

def evaluate (terms : ℕ) (box : CertificateBox)
    (certificate : LRDeterminantIdealEvaluatorCertificate) :
    LRDeterminantIdealLeafResult :=
  let endpoint := certificate.evaluate terms box
  let u := uI terms certificate
  { core := RationalEnclosure.sub endpoint.core
      (RationalEnclosure.div endpoint.c1 u)
    derivative := RationalEnclosure.add endpoint.derivative
      (RationalEnclosure.div endpoint.c1
        (uSquareI terms certificate))
    c1 := endpoint.c1 }

def accepts (terms : ℕ) (margin : ℚ) (box : CertificateBox)
    (certificate : LRDeterminantIdealEvaluatorCertificate) : Bool :=
  certificate.payloadCheck terms box &&
    (evaluate terms box certificate).check margin

theorem uI_sound
    (terms : ℕ) {box : CertificateBox}
    {certificate : LRDeterminantIdealEvaluatorCertificate}
    (hvalid : certificate.Valid terms box) :
    (uI terms certificate).Contains
      (lrDeterminantIdealDeepL0 + lrDeterminantIdealC) := by
  have hlogTwo := certificate.logTwo.sound terms hvalid.logTwo
    (RationalEnclosure.contains_point 2)
  have hlogFourThird := certificate.logFourThird.sound terms
    hvalid.logFourThird (RationalEnclosure.contains_point (4 / 3))
  have hL0 := RationalEnclosure.contains_scale (14 : ℚ) hlogTwo
  have hC := RationalEnclosure.contains_add
    (RationalEnclosure.contains_sub
      (RationalEnclosure.contains_point 1)
      (RationalEnclosure.contains_scale (2 : ℚ) hlogTwo))
    (RationalEnclosure.contains_scale (16 : ℚ) hlogFourThird)
  have hsum := RationalEnclosure.contains_add hL0 hC
  convert hsum using 1
  unfold lrDeterminantIdealDeepL0 lrDeterminantIdealC
  ring

theorem evaluate_sound
    (terms : ℕ) {box : CertificateBox} {point : CertificatePoint}
    {certificate : LRDeterminantIdealEvaluatorCertificate}
    (hpoint : box.Contains point) (hvalid : certificate.Valid terms box) :
    (evaluate terms box certificate).core.Contains
        (lrDeterminantIdealCore lrDeterminantIdealDeepL0
            point.k point.chi -
          lrDeterminantIdealC1 point.k point.chi /
            (lrDeterminantIdealDeepL0 + lrDeterminantIdealC)) ∧
      (evaluate terms box certificate).derivative.Contains
        (lrDeterminantIdealLambda point.k point.chi / 2) ∧
      (evaluate terms box certificate).c1.Contains
        (lrDeterminantIdealC1 point.k point.chi) := by
  have hendpoint :=
    LRDeterminantIdealEvaluatorCertificate.evaluate_sound
      terms hpoint hvalid
  have hu := uI_sound terms hvalid
  have huLower : (0 : ℚ) < (uI terms certificate).lower := by
    simpa [uI] using hvalid.l0PlusC
  have huSquare := RationalEnclosure.contains_mulNonnegative
    huLower.le huLower.le hu hu
  have huSquareLower : (0 : ℚ) <
      (uSquareI terms certificate).lower := by
    simpa [uSquareI, RationalEnclosure.mulNonnegative] using
      mul_pos huLower huLower
  have hc1OverU := RationalEnclosure.contains_div huLower
    hendpoint.2.2 hu
  have hc1OverUSquare := RationalEnclosure.contains_div huSquareLower
    hendpoint.2.2 huSquare
  have hcore := RationalEnclosure.contains_sub
    hendpoint.1 hc1OverU
  have hslopeRaw := RationalEnclosure.contains_add
    hendpoint.2.1 hc1OverUSquare
  have hslope :
      (evaluate terms box certificate).derivative.Contains
        (lrDeterminantIdealLambda point.k point.chi / 2) := by
    have hbase := lrDeterminantIdealDeepL0_add_C_pos
    convert hslopeRaw using 1
    unfold lrDeterminantIdealLDerivative
    field_simp [hbase.ne']
    ring
  exact ⟨hcore, hslope, hendpoint.2.2⟩

theorem accepts_sound
    (terms : ℕ) (margin : ℚ) {box : CertificateBox}
    {point : CertificatePoint}
    {certificate : LRDeterminantIdealEvaluatorCertificate}
    (hpoint : box.Contains point)
    (haccept : accepts terms margin box certificate = true) :
    LRDeterminantIdealCoarseProperties (margin : ℝ) point := by
  have hparts : certificate.payloadCheck terms box = true ∧
      (evaluate terms box certificate).check margin = true := by
    simpa [accepts] using haccept
  have hsound := evaluate_sound terms hpoint
    (LRDeterminantIdealEvaluatorCertificate.valid_of_payloadCheck hparts.1)
  have hsigns : margin < (evaluate terms box certificate).core.lower ∧
      0 < (evaluate terms box certificate).derivative.lower ∧
      0 ≤ (evaluate terms box certificate).c1.lower := by
    simpa [LRDeterminantIdealLeafResult.check] using hparts.2
  constructor
  · have hrat : (margin : ℝ) <
        ((evaluate terms box certificate).core.lower : ℝ) := by
      exact_mod_cast hsigns.1
    exact hrat.trans_le hsound.1.1
  constructor
  · have hrat : (0 : ℝ) <
        ((evaluate terms box certificate).derivative.lower : ℝ) := by
      exact_mod_cast hsigns.2.1
    exact hrat.trans_le hsound.2.1.1
  · have hrat : (0 : ℝ) ≤
        ((evaluate terms box certificate).c1.lower : ℝ) := by
      exact_mod_cast hsigns.2.2
    exact hrat.trans hsound.2.2.1

def autoAccepts (terms logFuel : ℕ) (margin : ℚ)
    (box : CertificateBox) (_data : Unit) : Bool :=
  let certificate :=
    LRDeterminantIdealEvaluatorCertificate.auto logFuel box
  accepts terms margin box certificate

theorem autoAccepts_sound
    (terms logFuel : ℕ) (margin : ℚ)
    (box : CertificateBox) (_data : Unit)
    (haccept : autoAccepts terms logFuel margin box () = true) :
    ∀ point, box.Contains point →
      LRDeterminantIdealCoarseProperties (margin : ℝ) point := by
  intro point hpoint
  exact accepts_sound terms margin hpoint
    (by simpa [autoAccepts] using haccept)

end LRDeterminantIdealCoarseEvaluator


/-! ## Deterministic replay interface -/

namespace LRDeterminantIdealCoarseReplay

open LRDeterminantIdealCoarseEvaluator

abbrev Tree := SubdivisionCertificate Unit Unit

def noDiscard (_box : CertificateBox) (_data : Unit) : Bool := false

/-- First deep ideal-core replay root.  The ideal core is independent of the
dummy `s` coordinate, retained only to use the common box infrastructure. -/
def rootBox : CertificateBox :=
  { sLo := 0, sHi := 1 / 128
    kLo := 1 / 32, kHi := 1 / 16
    chiLo := 0, chiHi := 1 }

/-- Parameters used by the concrete kernel replay.  Exact-rational offline
auditing leaves a 20.75 ppm minimum core reserve at these values. -/
def terms : ℕ := 8
def logFuel : ℕ := 5
def margin : ℚ := 3 / 5

theorem propagated_of_check {L : ℝ}
    (hL : lrDeterminantIdealDeepL0 ≤ L) {tree : Tree}
    (hcheck : tree.check
      (LRDeterminantIdealCoarseEvaluator.autoAccepts terms logFuel margin)
      noDiscard rootBox = true) :
    ∀ point, rootBox.Contains point →
      (margin : ℝ) < lrDeterminantIdealCore L point.k point.chi := by
  have hproperties : ∀ point, rootBox.Contains point → True →
      LRDeterminantIdealCoarseProperties (margin : ℝ) point := by
    exact subdivisionCertificate_sound
      (Relevant := fun _ ↦ True)
      (Property := LRDeterminantIdealCoarseProperties (margin : ℝ))
      (acceptBox := LRDeterminantIdealCoarseEvaluator.autoAccepts
        terms logFuel margin)
      (discardBox := noDiscard)
      (LRDeterminantIdealCoarseEvaluator.autoAccepts_sound
        terms logFuel margin)
      (by intro box data h; simp [noDiscard] at h)
      hcheck
  intro point hpoint
  exact lrDeterminantIdealCore_gt_of_coarseProperties hL
    (hproperties point hpoint trivial)

end LRDeterminantIdealCoarseReplay
end CourtadeKumar
