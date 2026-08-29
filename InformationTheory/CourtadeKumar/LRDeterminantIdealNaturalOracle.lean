import InformationTheory.CourtadeKumar.LRDeterminantIdealMeanValueEvaluator

/-!
# Zero-aware natural evaluator for both ideal replay scales

This scratch module factors the value-only ideal evaluator through a rational
scale `ell`, so the same checked logarithm/H/qChi payload serves both
`L₀ = 7 log 2` and `L₀ = 14 log 2`.  Only the algebra involving `L₀` is
repeated.  In particular, the zero-aware implementations of
`lrDeterminantIdealH` and `lrSmallSBridgeQChi` are reused verbatim from
`LRDeterminantIdealEvaluatorCertificate`.

The two output modes are exactly the historical correlated-replay triples:

* `globalTail`: `core - C₁/(L₀+C) - margin`, `Lambda/2`, `C₁`;
* `endpoint`: `core - margin`, the exact endpoint `L` derivative, `C₁`.

All proposal data remain untrusted.  `payloadCheck` checks every logarithm,
both removable-singularity certificates, the qChi certificate, and every
positive denominator before the soundness theorem uses them.
-/

namespace CourtadeKumar
namespace LRIdealNaturalOracle

open LRLowKIdealMeanValue
open LRDeterminantIdealEvaluatorCertificate

abbrev Payload := LRDeterminantIdealEvaluatorCertificate

/-- The two exact target layouts used by the historical ideal replay. -/
inductive TargetMode where
  | globalTail
  | endpoint
  deriving DecidableEq, Repr

/-- The real endpoint represented by the exact rational scale. -/
noncomputable def scaledL0 (ell : ℚ) : ℝ := (ell : ℝ) * Real.log 2

noncomputable def globalTailTargets (ell margin : ℚ) : TargetTriple where
  first := fun point ↦
    (lrDeterminantIdealCore (scaledL0 ell) point.k point.chi -
      lrDeterminantIdealC1 point.k point.chi /
        (scaledL0 ell + lrDeterminantIdealC)) - (margin : ℝ)
  second := fun point ↦
    lrDeterminantIdealLambda point.k point.chi / 2
  third := fun point ↦
    lrDeterminantIdealC1 point.k point.chi

noncomputable def endpointTargets (ell margin : ℚ) : TargetTriple where
  first := fun point ↦
    lrDeterminantIdealCore (scaledL0 ell) point.k point.chi - (margin : ℝ)
  second := fun point ↦
    lrDeterminantIdealLDerivative (scaledL0 ell) point.k point.chi
  third := fun point ↦
    lrDeterminantIdealC1 point.k point.chi

noncomputable def targets (ell margin : ℚ) : TargetMode → TargetTriple
  | .globalTail => globalTailTargets ell margin
  | .endpoint => endpointTargets ell margin

/-! ## Scale-parametric interval algebra -/

def scaledL0I (terms : ℕ) (ell : ℚ) (certificate : Payload) :
    RationalEnclosure :=
  RationalEnclosure.scale ell (logTwoI terms certificate)

def scaledB0I (terms : ℕ) (ell : ℚ) (_box : CertificateBox)
    (certificate : Payload) : RationalEnclosure :=
  RationalEnclosure.sub
    (RationalEnclosure.add
      (RationalEnclosure.scale (1 / 2) (scaledL0I terms ell certificate))
      (logTwoI terms certificate))
    (RationalEnclosure.scale (1 / 2) (logOnePlusKI terms certificate))

def scaledPI (terms : ℕ) (ell : ℚ) (box : CertificateBox)
    (certificate : Payload) : RationalEnclosure :=
  RationalEnclosure.sub
    (RationalEnclosure.add
      (RationalEnclosure.add (scaledL0I terms ell certificate)
        (RationalEnclosure.scale 2 (logTwoI terms certificate)))
      (RationalEnclosure.point 1))
    (aI terms box certificate)

def scaledGI (terms : ℕ) (ell : ℚ) (box : CertificateBox)
    (certificate : Payload) : RationalEnclosure :=
  RationalEnclosure.sub
    (RationalEnclosure.add
      (RationalEnclosure.add
        (RationalEnclosure.sub (scaledL0I terms ell certificate)
          (logKI terms certificate))
        (RationalEnclosure.scale 2 (logTwoI terms certificate)))
      (RationalEnclosure.point 1))
    (qChiI terms box certificate)

def scaledTI (terms : ℕ) (ell : ℚ) (box : CertificateBox)
    (certificate : Payload) : RationalEnclosure :=
  RationalEnclosure.sub
    (RationalEnclosure.add
      (RationalEnclosure.add (scaledL0I terms ell certificate)
        (RationalEnclosure.scale 2 (logTwoI terms certificate)))
      (RationalEnclosure.point 1))
    (ahI terms box certificate)

def scaledL0PlusCI (terms : ℕ) (ell : ℚ) (certificate : Payload) :
    RationalEnclosure :=
  RationalEnclosure.add (scaledL0I terms ell certificate)
    (cI terms certificate)

def scaledCoreI (terms : ℕ) (ell : ℚ) (box : CertificateBox)
    (certificate : Payload) : RationalEnclosure :=
  RationalEnclosure.add
    (RationalEnclosure.add
      (RationalEnclosure.mul (d0I terms box certificate)
        (scaledPI terms ell box certificate))
      (RationalEnclosure.mul (scaledB0I terms ell box certificate)
        (RationalEnclosure.sub (scaledPI terms ell box certificate)
          (scaledGI terms ell box certificate))))
    (RationalEnclosure.div
      (RationalEnclosure.mul
        (RationalEnclosure.sub (scaledB0I terms ell box certificate)
          (d0I terms box certificate))
        (scaledTI terms ell box certificate))
      (RationalEnclosure.mulNonnegative (RationalEnclosure.point 3)
        (scaledL0PlusCI terms ell certificate)))

def scaledDerivativeI (terms : ℕ) (ell : ℚ) (box : CertificateBox)
    (certificate : Payload) : RationalEnclosure :=
  RationalEnclosure.sub
    (RationalEnclosure.scale (1 / 2) (lambdaI terms box certificate))
    (RationalEnclosure.div (c1I terms box certificate)
      (RationalEnclosure.mulNonnegative
        (scaledL0PlusCI terms ell certificate)
        (scaledL0PlusCI terms ell certificate)))

def evaluate (terms : ℕ) (ell margin : ℚ) (mode : TargetMode)
    (box : CertificateBox) (certificate : Payload) : IntervalTriple :=
  match mode with
  | .globalTail =>
      { first := RationalEnclosure.sub
          (RationalEnclosure.sub (scaledCoreI terms ell box certificate)
            (RationalEnclosure.div (c1I terms box certificate)
              (scaledL0PlusCI terms ell certificate)))
          (RationalEnclosure.point margin)
        second := RationalEnclosure.scale (1 / 2)
          (lambdaI terms box certificate)
        third := c1I terms box certificate }
  | .endpoint =>
      { first := RationalEnclosure.sub (scaledCoreI terms ell box certificate)
          (RationalEnclosure.point margin)
        second := scaledDerivativeI terms ell box certificate
        third := c1I terms box certificate }

/-! ## Executable validity check -/

/-- The endpoint branch deliberately permits `chiLo = 0`.  As in the reused
qChi certificate, a nontrivial zero-touching box is accepted only after its
upper chi endpoint has been subdivided to at most `1/4`; this is the range on
which the checked endpoint monotonicity enclosure is valid. -/
def payloadCheck (terms : ℕ) (ell : ℚ) (box : CertificateBox)
    (certificate : Payload) : Bool :=
  decide ((0 : ℚ) < box.kLo ∧ box.kLo ≤ box.kHi ∧
      (0 : ℚ) ≤ box.chiLo ∧ box.chiLo ≤ box.chiHi ∧
      box.chiHi ≤ 1) &&
    decide ((0 : ℚ) < (onePlusChiI box).lower ∧
      (0 : ℚ) < (twoKI box).lower ∧
      (0 : ℚ) < (fourKPlusThreeI box).lower) &&
    certificate.logTwo.check (RationalEnclosure.point 2) &&
    certificate.logFourThird.check (RationalEnclosure.point (4 / 3)) &&
    certificate.logK.check (kI box) &&
    certificate.logOnePlusK.check (onePlusKI box) &&
    certificate.logOnePlusKChi.check (onePlusKChiI box) &&
    certificate.logDArg.check (dArgI box) &&
    certificate.hK.check (kI box) &&
    certificate.hKChi.check (kChiI box) &&
    certificate.qChi.check (chiI box) &&
    decide ((0 : ℚ) < (scaledL0PlusCI terms ell certificate).lower)

structure Valid (terms : ℕ) (ell : ℚ) (box : CertificateBox)
    (certificate : Payload) : Prop where
  domain : (0 : ℚ) < box.kLo ∧ box.kLo ≤ box.kHi ∧
    (0 : ℚ) ≤ box.chiLo ∧ box.chiLo ≤ box.chiHi ∧
    box.chiHi ≤ 1
  denominators : (0 : ℚ) < (onePlusChiI box).lower ∧
    (0 : ℚ) < (twoKI box).lower ∧
    (0 : ℚ) < (fourKPlusThreeI box).lower
  logTwo : certificate.logTwo.check (RationalEnclosure.point 2) = true
  logFourThird : certificate.logFourThird.check
    (RationalEnclosure.point (4 / 3)) = true
  logK : certificate.logK.check (kI box) = true
  logOnePlusK : certificate.logOnePlusK.check (onePlusKI box) = true
  logOnePlusKChi : certificate.logOnePlusKChi.check
    (onePlusKChiI box) = true
  logDArg : certificate.logDArg.check (dArgI box) = true
  hK : certificate.hK.check (kI box) = true
  hKChi : certificate.hKChi.check (kChiI box) = true
  qChi : certificate.qChi.check (chiI box) = true
  l0PlusC : (0 : ℚ) < (scaledL0PlusCI terms ell certificate).lower

theorem valid_of_payloadCheck
    {terms : ℕ} {ell : ℚ} {box : CertificateBox}
    {certificate : Payload}
    (hcheck : payloadCheck terms ell box certificate = true) :
    Valid terms ell box certificate := by
  have h :
      ((0 : ℚ) < box.kLo ∧ box.kLo ≤ box.kHi ∧
        (0 : ℚ) ≤ box.chiLo ∧ box.chiLo ≤ box.chiHi ∧
        box.chiHi ≤ 1) ∧
      ((0 : ℚ) < (onePlusChiI box).lower ∧
        (0 : ℚ) < (twoKI box).lower ∧
        (0 : ℚ) < (fourKPlusThreeI box).lower) ∧
      certificate.logTwo.check (RationalEnclosure.point 2) = true ∧
      certificate.logFourThird.check
        (RationalEnclosure.point (4 / 3)) = true ∧
      certificate.logK.check (kI box) = true ∧
      certificate.logOnePlusK.check (onePlusKI box) = true ∧
      certificate.logOnePlusKChi.check (onePlusKChiI box) = true ∧
      certificate.logDArg.check (dArgI box) = true ∧
      certificate.hK.check (kI box) = true ∧
      certificate.hKChi.check (kChiI box) = true ∧
      certificate.qChi.check (chiI box) = true ∧
      (0 : ℚ) < (scaledL0PlusCI terms ell certificate).lower := by
    simpa [payloadCheck, and_assoc] using hcheck
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1,
    h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2⟩

/-! ## Simultaneous soundness -/

set_option maxHeartbeats 1800000 in
theorem evaluate_sound
    (terms : ℕ) (ell margin : ℚ) (mode : TargetMode)
    {box : CertificateBox} {point : CertificatePoint}
    {certificate : Payload}
    (hpoint : box.Contains point)
    (hvalid : Valid terms ell box certificate) :
    (evaluate terms ell margin mode box certificate).first.Contains
        ((targets ell margin mode).first point) ∧
      (evaluate terms ell margin mode box certificate).second.Contains
        ((targets ell margin mode).second point) ∧
      (evaluate terms ell margin mode box certificate).third.Contains
        ((targets ell margin mode).third point) := by
  have hk : (kI box).Contains point.k :=
    ⟨hpoint.2.2.1, hpoint.2.2.2.1⟩
  have hchi : (chiI box).Contains point.chi :=
    ⟨hpoint.2.2.2.2.1, hpoint.2.2.2.2.2⟩
  have hkLowerNonneg : (0 : ℚ) ≤ (kI box).lower := by
    simpa [kI, CertificateBox.kInterval] using hvalid.domain.1.le
  have hchiLowerNonneg : (0 : ℚ) ≤ (chiI box).lower := by
    simpa [chiI, CertificateBox.chiInterval] using hvalid.domain.2.2.1
  have hkchi := RationalEnclosure.contains_mulNonnegative
    hkLowerNonneg hchiLowerNonneg hk hchi
  have honeChi := RationalEnclosure.contains_add
    (RationalEnclosure.contains_point 1) hchi
  have honeK := RationalEnclosure.contains_add
    (RationalEnclosure.contains_point 1) hk
  have honeKChi := RationalEnclosure.contains_add
    (RationalEnclosure.contains_point 1) hkchi
  have htwoK := RationalEnclosure.contains_mulNonnegative
    (by norm_num [RationalEnclosure.point] :
      (0 : ℚ) ≤ (RationalEnclosure.point 2).lower)
    hkLowerNonneg (RationalEnclosure.contains_point 2) hk
  have hinvTwoK := RationalEnclosure.contains_invPositive
    hvalid.denominators.2.1 htwoK
  have hdArg := RationalEnclosure.contains_add
    (RationalEnclosure.contains_point 1) hinvTwoK
  have hfourK := RationalEnclosure.contains_mulNonnegative
    (by norm_num [RationalEnclosure.point] :
      (0 : ℚ) ≤ (RationalEnclosure.point 4).lower)
    hkLowerNonneg (RationalEnclosure.contains_point 4) hk
  have hfourKThree := RationalEnclosure.contains_add hfourK
    (RationalEnclosure.contains_point 3)
  have hlogTwo := certificate.logTwo.sound terms hvalid.logTwo
    (RationalEnclosure.contains_point 2)
  have hlogFourThird := certificate.logFourThird.sound terms
    hvalid.logFourThird (RationalEnclosure.contains_point (4 / 3))
  have hlogK := certificate.logK.sound terms hvalid.logK hk
  have hlogOneK := certificate.logOnePlusK.sound terms
    hvalid.logOnePlusK honeK
  have hlogOneKChi := certificate.logOnePlusKChi.sound terms
    hvalid.logOnePlusKChi honeKChi
  have hlogDArg := certificate.logDArg.sound terms hvalid.logDArg hdArg
  have hhK := certificate.hK.sound terms hvalid.hK hk
  have hhKChi := certificate.hKChi.sound terms hvalid.hKChi hkchi
  have hqChi := certificate.qChi.sound terms hvalid.qChi hchi
  have hL0 := RationalEnclosure.contains_scale ell hlogTwo
  have hC := RationalEnclosure.contains_add
    (RationalEnclosure.contains_sub
      (RationalEnclosure.contains_point 1)
      (RationalEnclosure.contains_scale (2 : ℚ) hlogTwo))
    (RationalEnclosure.contains_scale (16 : ℚ) hlogFourThird)
  have hA := RationalEnclosure.contains_div hvalid.denominators.1
    (RationalEnclosure.contains_add
      (RationalEnclosure.contains_mul hchi hlogOneKChi) hlogOneK)
    honeChi
  have hAH := RationalEnclosure.contains_div hvalid.denominators.1
    (RationalEnclosure.contains_add
      (RationalEnclosure.contains_mul hchi hhKChi) hhK)
    honeChi
  have hD := RationalEnclosure.contains_add
    (RationalEnclosure.contains_scale (1 / 2 : ℚ) hlogDArg)
    (RationalEnclosure.contains_invPositive
      hvalid.denominators.2.2 hfourKThree)
  have hB := RationalEnclosure.contains_sub
    (RationalEnclosure.contains_add
      (RationalEnclosure.contains_scale (1 / 2 : ℚ) hL0) hlogTwo)
    (RationalEnclosure.contains_scale (1 / 2 : ℚ) hlogOneK)
  have hP := RationalEnclosure.contains_sub
    (RationalEnclosure.contains_add
      (RationalEnclosure.contains_add hL0
        (RationalEnclosure.contains_scale (2 : ℚ) hlogTwo))
      (RationalEnclosure.contains_point 1)) hA
  have hG := RationalEnclosure.contains_sub
    (RationalEnclosure.contains_add
      (RationalEnclosure.contains_add
        (RationalEnclosure.contains_sub hL0 hlogK)
        (RationalEnclosure.contains_scale (2 : ℚ) hlogTwo))
      (RationalEnclosure.contains_point 1)) hqChi
  have hT := RationalEnclosure.contains_sub
    (RationalEnclosure.contains_add
      (RationalEnclosure.contains_add hL0
        (RationalEnclosure.contains_scale (2 : ℚ) hlogTwo))
      (RationalEnclosure.contains_point 1)) hAH
  have hLC := RationalEnclosure.contains_add hL0 hC
  have hthreeLC := RationalEnclosure.contains_mulNonnegative
    (by norm_num [RationalEnclosure.point] :
      (0 : ℚ) ≤ (RationalEnclosure.point 3).lower)
    hvalid.l0PlusC.le (RationalEnclosure.contains_point 3) hLC
  have hthreeLCLower : (0 : ℚ) <
      (RationalEnclosure.mulNonnegative (RationalEnclosure.point 3)
        (scaledL0PlusCI terms ell certificate)).lower := by
    dsimp [RationalEnclosure.mulNonnegative, RationalEnclosure.point]
    exact mul_pos (by norm_num) hvalid.l0PlusC
  have hcoreRaw := RationalEnclosure.contains_add
    (RationalEnclosure.contains_add
      (RationalEnclosure.contains_mul hD hP)
      (RationalEnclosure.contains_mul hB
        (RationalEnclosure.contains_sub hP hG)))
    (RationalEnclosure.contains_div hthreeLCLower
      (RationalEnclosure.contains_mul
        (RationalEnclosure.contains_sub hB hD) hT) hthreeLC)
  have hbConst := RationalEnclosure.contains_sub hlogTwo
    (RationalEnclosure.contains_scale (1 / 2 : ℚ) hlogOneK)
  have hS := RationalEnclosure.contains_sub
    (RationalEnclosure.contains_add hlogK hqChi) hA
  have hT0 := RationalEnclosure.contains_sub
    (RationalEnclosure.contains_add
      (RationalEnclosure.contains_scale (2 : ℚ) hlogTwo)
      (RationalEnclosure.contains_point 1)) hAH
  have hLambdaRaw := RationalEnclosure.contains_add
    (RationalEnclosure.contains_add
      (RationalEnclosure.contains_scale (2 : ℚ) hD) hS)
    (RationalEnclosure.contains_point (1 / 3))
  have hC1Raw := RationalEnclosure.contains_scale (1 / 3 : ℚ)
    (RationalEnclosure.contains_mul
      (RationalEnclosure.contains_sub hT0 hC)
      (RationalEnclosure.contains_sub
        (RationalEnclosure.contains_sub hbConst hD)
        (RationalEnclosure.contains_scale (1 / 2 : ℚ) hC)))
  have hLCSquare := RationalEnclosure.contains_mulNonnegative
    hvalid.l0PlusC.le hvalid.l0PlusC.le hLC hLC
  have hLCSquareLower : (0 : ℚ) <
      (RationalEnclosure.mulNonnegative
        (scaledL0PlusCI terms ell certificate)
        (scaledL0PlusCI terms ell certificate)).lower := by
    dsimp [RationalEnclosure.mulNonnegative]
    exact mul_pos hvalid.l0PlusC hvalid.l0PlusC
  have hDerivativeRaw := RationalEnclosure.contains_sub
    (RationalEnclosure.contains_scale (1 / 2 : ℚ) hLambdaRaw)
    (RationalEnclosure.contains_div hLCSquareLower hC1Raw hLCSquare)
  have hcore : (scaledCoreI terms ell box certificate).Contains
      (lrDeterminantIdealCore (scaledL0 ell) point.k point.chi) := by
    convert hcoreRaw using 1
    unfold lrDeterminantIdealCore lrDeterminantIdealD0
      lrDeterminantIdealB0 lrDeterminantIdealP lrDeterminantIdealG
      lrDeterminantIdealT lrDeterminantIdealA lrDeterminantIdealAH
      lrDeterminantIdealC scaledL0
    ring_nf
  have hlambda : (lambdaI terms box certificate).Contains
      (lrDeterminantIdealLambda point.k point.chi) := by
    convert hLambdaRaw using 1
    unfold lrDeterminantIdealLambda lrDeterminantIdealS
      lrDeterminantIdealD0 lrDeterminantIdealA
    ring_nf
  have hc1 : (c1I terms box certificate).Contains
      (lrDeterminantIdealC1 point.k point.chi) := by
    convert hC1Raw using 1
    unfold lrDeterminantIdealC1 lrDeterminantIdealT0
      lrDeterminantIdealC lrDeterminantIdealBConst
      lrDeterminantIdealD0 lrDeterminantIdealAH
    ring_nf
  have hderivative : (scaledDerivativeI terms ell box certificate).Contains
      (lrDeterminantIdealLDerivative (scaledL0 ell)
        point.k point.chi) := by
    convert hDerivativeRaw using 1
    unfold lrDeterminantIdealLDerivative lrDeterminantIdealLambda
      lrDeterminantIdealS lrDeterminantIdealC1 lrDeterminantIdealT0
      lrDeterminantIdealC lrDeterminantIdealBConst
      lrDeterminantIdealD0 lrDeterminantIdealA lrDeterminantIdealAH
      scaledL0
    ring_nf
  cases mode with
  | globalTail =>
      have htail := RationalEnclosure.contains_div hvalid.l0PlusC hc1 hLC
      have hfirst := RationalEnclosure.contains_sub
        (RationalEnclosure.contains_sub hcore htail)
        (RationalEnclosure.contains_point margin)
      have hsecond := RationalEnclosure.contains_scale (1 / 2 : ℚ) hlambda
      exact ⟨by simpa [evaluate, targets, globalTailTargets] using hfirst,
        by simpa [evaluate, targets, globalTailTargets, div_eq_mul_inv,
          mul_comm] using hsecond,
        by simpa [evaluate, targets, globalTailTargets] using hc1⟩
  | endpoint =>
      have hfirst := RationalEnclosure.contains_sub hcore
        (RationalEnclosure.contains_point margin)
      exact ⟨by simpa [evaluate, targets, endpointTargets] using hfirst,
        by simpa [evaluate, targets, endpointTargets] using hderivative,
        by simpa [evaluate, targets, endpointTargets] using hc1⟩

/-! ## `NaturalOracle` packaging and exact replay adapters -/

noncomputable def naturalOracle (terms : ℕ) (ell margin : ℚ)
    (mode : TargetMode) : NaturalOracle (targets ell margin mode) where
  Payload := LRDeterminantIdealEvaluatorCertificate
  payloadCheck := payloadCheck terms ell
  evaluate := evaluate terms ell margin mode
  sound := by
    intro box certificate hcheck point hpoint
    exact evaluate_sound terms ell margin mode hpoint
      (valid_of_payloadCheck hcheck)

theorem scaledL0_seven : scaledL0 7 = lrLowKIdealL0 := by
  norm_num [scaledL0, lrLowKIdealL0]

theorem scaledL0_fourteen : scaledL0 14 = lrDeterminantIdealDeepL0 := by
  norm_num [scaledL0, lrDeterminantIdealDeepL0]

/-- The concrete natural rule used by zero-face leaves of the low-k middle
forest. -/
noncomputable def middleNaturalOracle (terms : ℕ) :
    NaturalOracle middleTargets where
  Payload := LRDeterminantIdealEvaluatorCertificate
  payloadCheck := payloadCheck terms 7
  evaluate := evaluate terms 7 (19 / 50) .globalTail
  sound := by
    intro box certificate hcheck point hpoint
    have hs := evaluate_sound terms 7 (19 / 50) .globalTail hpoint
      (valid_of_payloadCheck hcheck)
    simpa [targets, globalTailTargets, middleTargets, scaledL0_seven] using hs

/-- The concrete natural rule used by zero-face leaves of the low-k upper
forest. -/
noncomputable def upperNaturalOracle (terms : ℕ) :
    NaturalOracle upperTargets where
  Payload := LRDeterminantIdealEvaluatorCertificate
  payloadCheck := payloadCheck terms 7
  evaluate := evaluate terms 7 (19 / 50) .endpoint
  sound := by
    intro box certificate hcheck point hpoint
    have hs := evaluate_sound terms 7 (19 / 50) .endpoint hpoint
      (valid_of_payloadCheck hcheck)
    simpa [targets, endpointTargets, upperTargets, scaledL0_seven] using hs

/-- The concrete natural rule used by zero-face leaves of the restricted
`1 ≤ k ≤ 4` ideal forest. -/
noncomputable def restrictedNaturalOracle (terms : ℕ) :
    NaturalOracle restrictedTargets where
  Payload := LRDeterminantIdealEvaluatorCertificate
  payloadCheck := payloadCheck terms 14
  evaluate := evaluate terms 14 (3 / 5) .endpoint
  sound := by
    intro box certificate hcheck point hpoint
    have hs := evaluate_sound terms 14 (3 / 5) .endpoint hpoint
      (valid_of_payloadCheck hcheck)
    simpa [targets, endpointTargets, restrictedTargets,
      scaledL0_fourteen] using hs

/-- Deterministic certificate proposal.  Soundness never trusts this
constructor: `payloadCheck` reruns every certificate check. -/
def autoPayload (logFuel : ℕ) (box : CertificateBox) : Payload :=
  LRDeterminantIdealEvaluatorCertificate.auto logFuel box

end LRIdealNaturalOracle
end CourtadeKumar
