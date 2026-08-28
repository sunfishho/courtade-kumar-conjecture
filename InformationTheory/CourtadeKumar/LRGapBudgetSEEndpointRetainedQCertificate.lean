import InformationTheory.CourtadeKumar.LRGapBudgetSEEndpointCertificate

/-!
# Closed-endpoint certificate retaining the regular `Q(B(s,e))` term

The basic endpoint minorant discards three nonnegative terms.  This checker
retains the value-only term `-Q(B(s,e)) v' / v²`, which is nonsingular on
boxes touching `s = 0` and materially strengthens the far-edge estimate.
It is intended for boxes bounded away from `e = 0`, where the ordinary
monotone interval certificate supplies a positive lower bound for `Q`.
-/

namespace CourtadeKumar
namespace LRGapBudgetSEEndpointRetainedQCertificate


def beI (box : CertificateBox) : RationalEnclosure :=
  RationalEnclosure.add (LRGapBudgetSEEndpointCertificate.sI box)
    (RationalEnclosure.mul
      (RationalEnclosure.sub (RationalEnclosure.point 1) (LRGapBudgetSEEndpointCertificate.sI box))
      (LRGapBudgetSEEndpointCertificate.eI box))

structure Payload where
  base : LRGapBudgetSEEndpointCertificate.Payload
  qBE : LRQIntervalCertificate

def evaluate (terms : ℕ) (box : CertificateBox)
    (payload : Payload) : RationalEnclosure :=
  RationalEnclosure.sub
    (LRGapBudgetSEEndpointCertificate.evaluate terms box payload.base)
    (RationalEnclosure.div
      (RationalEnclosure.mul
        (payload.qBE.enclosure terms)
        (LRGapBudgetSEEndpointCertificate.vPrimeI box payload.base))
      (LRGapBudgetSEEndpointCertificate.vSquareI payload.base))

def check (box : CertificateBox) (payload : Payload) : Bool :=
  LRGapBudgetSEEndpointCertificate.check box payload.base && payload.qBE.check (beI box)

set_option maxHeartbeats 1200000 in
theorem evaluate_sound (terms : ℕ) {box : CertificateBox}
    {point : CertificatePoint} {payload : Payload}
    (hpoint : box.Contains point) (hcheck : check box payload = true) :
    (evaluate terms box payload).Contains
      (lrGapBudgetSEChiDerivEEndpointRetainedQMinorant
        point.s point.k point.chi) := by
  have hchecks : LRGapBudgetSEEndpointCertificate.check box payload.base = true ∧
      payload.qBE.check (beI box) = true := by
    simpa [check] using hcheck
  have hparts :
      ((0 : ℚ) < (LRGapBudgetSEEndpointCertificate.xI box).lower ∧
        (0 : ℚ) < (LRGapBudgetSEEndpointCertificate.radicandI box).lower) ∧
      payload.base.vSqrt.check (LRGapBudgetSEEndpointCertificate.radicandI box) = true ∧
      payload.base.qS.check (LRGapBudgetSEEndpointCertificate.sI box) = true ∧
      payload.base.logTwo.check (RationalEnclosure.point 2) = true ∧
      payload.base.logOnePlusV.check
        (LRGapBudgetSEEndpointCertificate.onePlusVI payload.base) = true ∧
      payload.base.logTwoPlusV.check
        (LRGapBudgetSEEndpointCertificate.twoPlusVI payload.base) = true ∧
      ((0 : ℚ) < (LRGapBudgetSEEndpointCertificate.vI payload.base).lower ∧
        (0 : ℚ) < (LRGapBudgetSEEndpointCertificate.onePlusVI payload.base).lower ∧
        (0 : ℚ) < (LRGapBudgetSEEndpointCertificate.twoPlusVI payload.base).lower) := by
    simp only [LRGapBudgetSEEndpointCertificate.check, Bool.and_eq_true, decide_eq_true_eq] at hchecks
    rcases hchecks.1 with
      ⟨⟨⟨⟨⟨⟨hcond, hsqrt⟩, hqSCheck⟩, hlogTwoCheck⟩,
        hlogOneCheck⟩, hlogTwoPlusCheck⟩, hpositive⟩
    exact ⟨hcond, hsqrt, hqSCheck, hlogTwoCheck,
      hlogOneCheck, hlogTwoPlusCheck, hpositive⟩
  have hs : (LRGapBudgetSEEndpointCertificate.sI box).Contains point.s :=
    ⟨hpoint.1, hpoint.2.1⟩
  have he : (LRGapBudgetSEEndpointCertificate.eI box).Contains point.k :=
    ⟨hpoint.2.2.1, hpoint.2.2.2.1⟩
  have hchi : (LRGapBudgetSEEndpointCertificate.chiI box).Contains point.chi :=
    ⟨hpoint.2.2.2.2.1, hpoint.2.2.2.2.2⟩
  have hchiE := RationalEnclosure.contains_mul hchi he
  have hxRaw := RationalEnclosure.contains_sub
    (RationalEnclosure.contains_point 1) hchiE
  set x : ℝ := 1 - point.chi * point.k with hxDef
  have hx : (LRGapBudgetSEEndpointCertificate.xI box).Contains x := by
    rw [hxDef]
    simpa [LRGapBudgetSEEndpointCertificate.xI] using hxRaw
  have hnum := RationalEnclosure.contains_sub
    (RationalEnclosure.contains_point 1) he
  have hrad := RationalEnclosure.contains_div hparts.1.1 hnum hx
  set v : ℝ := Real.sqrt ((1 - point.k) / x) with hvDef
  have hvRaw := payload.base.vSqrt.sound hparts.2.1 hrad
  have hv : (LRGapBudgetSEEndpointCertificate.vI payload.base).Contains v := by
    rw [hvDef]
    simpa [LRGapBudgetSEEndpointCertificate.vI] using hvRaw
  have hvLowerNonneg : (0 : ℚ) ≤ (LRGapBudgetSEEndpointCertificate.vI payload.base).lower :=
    hparts.2.2.2.2.2.2.1.le
  have hxLowerNonneg : (0 : ℚ) ≤ (LRGapBudgetSEEndpointCertificate.xI box).lower :=
    hparts.1.1.le
  have hvSquare := RationalEnclosure.contains_mulNonnegative
    hvLowerNonneg hvLowerNonneg hv hv
  have hxSquare := RationalEnclosure.contains_mulNonnegative
    hxLowerNonneg hxLowerNonneg hx hx
  have htwoV := RationalEnclosure.contains_mulNonnegative
    (by norm_num [RationalEnclosure.point] :
      (0 : ℚ) ≤ (RationalEnclosure.point 2).lower)
    hvLowerNonneg (RationalEnclosure.contains_point 2) hv
  have hden := RationalEnclosure.contains_mulNonnegative
    (by
      dsimp [RationalEnclosure.mulNonnegative, RationalEnclosure.point]
      positivity)
    (by
      dsimp [LRGapBudgetSEEndpointCertificate.xSquareI, RationalEnclosure.mulNonnegative]
      exact mul_nonneg hxLowerNonneg hxLowerNonneg)
    htwoV hxSquare
  have hdenLower : (0 : ℚ) <
      (RationalEnclosure.mulNonnegative
        (RationalEnclosure.mulNonnegative
          (RationalEnclosure.point 2) (LRGapBudgetSEEndpointCertificate.vI payload.base))
        (LRGapBudgetSEEndpointCertificate.xSquareI box)).lower := by
    dsimp [LRGapBudgetSEEndpointCertificate.xSquareI, RationalEnclosure.mulNonnegative,
      RationalEnclosure.point]
    exact mul_pos (mul_pos (by norm_num) hparts.2.2.2.2.2.2.1)
      (mul_pos hparts.1.1 hparts.1.1)
  have hvpRaw := RationalEnclosure.contains_div hdenLower
    (RationalEnclosure.contains_sub hchi
      (RationalEnclosure.contains_point 1)) hden
  set vp : ℝ := (point.chi - 1) / (2 * v * x ^ 2) with hvpDef
  have hvp : (LRGapBudgetSEEndpointCertificate.vPrimeI box payload.base).Contains vp := by
    rw [hvpDef]
    convert hvpRaw using 1 <;> ring
  have honeMinusS := RationalEnclosure.contains_sub
    (RationalEnclosure.contains_point 1) hs
  have hbeRaw := RationalEnclosure.contains_add hs
    (RationalEnclosure.contains_mul honeMinusS he)
  have hbe : (beI box).Contains (lrCertificateB point.s point.k) := by
    simpa [beI, LRGapBudgetSEEndpointCertificate.sI, LRGapBudgetSEEndpointCertificate.eI, lrCertificateB] using hbeRaw
  have hqBE := payload.qBE.sound terms hchecks.2 hbe
  have hvSquareLower : (0 : ℚ) <
      (LRGapBudgetSEEndpointCertificate.vSquareI payload.base).lower := by
    dsimp [LRGapBudgetSEEndpointCertificate.vSquareI, RationalEnclosure.mulNonnegative]
    exact mul_pos hparts.2.2.2.2.2.2.1 hparts.2.2.2.2.2.2.1
  have hquot := RationalEnclosure.contains_div hvSquareLower
    (RationalEnclosure.contains_mul hqBE hvp) hvSquare
  have hbase := LRGapBudgetSEEndpointCertificate.evaluate_sound terms hpoint hchecks.1
  have htotal := RationalEnclosure.contains_sub hbase hquot
  unfold evaluate
    lrGapBudgetSEChiDerivEEndpointRetainedQMinorant
  dsimp only
  rw [← hxDef, ← hvDef, ← hvpDef]
  convert htotal using 1 <;> ring

def nonnegative (terms : ℕ) (box : CertificateBox)
    (payload : Payload) : Bool :=
  decide ((0 : ℚ) ≤ (evaluate terms box payload).lower)

theorem nonnegative_sound (terms : ℕ) {box : CertificateBox}
    {point : CertificatePoint} {payload : Payload}
    (hpoint : box.Contains point) (hcheck : check box payload = true)
    (hnonnegative : nonnegative terms box payload = true) :
    0 ≤ lrGapBudgetSEChiDerivEEndpointRetainedQMinorant
      point.s point.k point.chi := by
  have hsound := evaluate_sound terms hpoint hcheck
  have hlower : (0 : ℝ) ≤ (evaluate terms box payload).lower := by
    exact_mod_cast (show (0 : ℚ) ≤ (evaluate terms box payload).lower by
      simpa [nonnegative] using hnonnegative)
  exact hlower.trans hsound.1

def auto (sqrtFuel logFuel : ℕ) (box : CertificateBox) : Payload :=
  { base := LRGapBudgetSEEndpointCertificate.auto sqrtFuel logFuel box
    qBE := LRQIntervalCertificate.auto sqrtFuel logFuel (beI box) }

def autoAccepts (terms sqrtFuel logFuel : ℕ)
    (box : CertificateBox) (_data : Unit) : Bool :=
  let payload := auto sqrtFuel logFuel box
  check box payload && nonnegative terms box payload

theorem autoAccepts_sound (terms sqrtFuel logFuel : ℕ)
    (box : CertificateBox) (data : Unit)
    (haccept : autoAccepts terms sqrtFuel logFuel box data = true) :
    ∀ point, box.Contains point → LRGapBudgetSETailRelevant point →
      0 ≤ lrGapBudgetSEChiDerivE point.s point.k point.chi := by
  intro point hpoint hrelevant
  have hparts : check box (auto sqrtFuel logFuel box) = true ∧
      nonnegative terms box (auto sqrtFuel logFuel box) = true := by
    simpa [autoAccepts] using haccept
  have hminorant := nonnegative_sound terms hpoint hparts.1 hparts.2
  exact lrGapBudgetSEChiDerivE_nonnegative_of_endpointRetainedQMinorant
    ⟨hrelevant.1.1, hrelevant.1.2.trans (by norm_num)⟩
    hrelevant.2.1 hrelevant.2.2.1 hminorant

end LRGapBudgetSEEndpointRetainedQCertificate
end CourtadeKumar
