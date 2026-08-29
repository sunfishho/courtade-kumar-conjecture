import InformationTheory.CourtadeKumar.LRDeterminantIdealSharedPrimitiveAD

/-!
# Semantic soundness of the shared ideal AD graph

This module is deliberately separate from the executable graph.  It gives
explicit real partial derivatives for every quantity needed by the two ideal
certificate modes, proves that the full interval-AD output contains those
values and partials on every positive-`chi` box, and supplies the coordinate
`HasDerivAt` facts consumed by `BoxDerivativeEnclosures`.

The dummy `s` coordinate is absent from the graph, so all `s` partials are
definitionally zero.  Boxes meeting `chi = 0` continue to use the independent
natural/value-only evaluator.
-/

namespace CourtadeKumar
namespace LRLowKIdealSharedPrimitiveADSoundness

open LRLowKIdealSharedPrimitiveAD

/-! ## Explicit real partials -/

noncomputable def idealANumerator (k chi : ℝ) : ℝ :=
  chi * Real.log (1 + k * chi) + Real.log (1 + k)

noncomputable def idealANumeratorK (k chi : ℝ) : ℝ :=
  chi * (chi / (1 + k * chi)) + 1 / (1 + k)

noncomputable def idealANumeratorChi (k chi : ℝ) : ℝ :=
  Real.log (1 + k * chi) + chi * (k / (1 + k * chi))

noncomputable def idealAPartialK (k chi : ℝ) : ℝ :=
  (idealANumeratorK k chi * (1 + chi) -
      idealANumerator k chi * 0) / (1 + chi) ^ 2

noncomputable def idealAPartialChi (k chi : ℝ) : ℝ :=
  (idealANumeratorChi k chi * (1 + chi) -
      idealANumerator k chi) / (1 + chi) ^ 2

noncomputable def idealAHNumerator (k chi : ℝ) : ℝ :=
  chi * lrDeterminantIdealH (k * chi) + lrDeterminantIdealH k

noncomputable def idealAHNumeratorK (k chi : ℝ) : ℝ :=
  chi * (idealHPrime (k * chi) * chi) + idealHPrime k

noncomputable def idealAHNumeratorChi (k chi : ℝ) : ℝ :=
  lrDeterminantIdealH (k * chi) +
    chi * (idealHPrime (k * chi) * k)

noncomputable def idealAHPartialK (k chi : ℝ) : ℝ :=
  (idealAHNumeratorK k chi * (1 + chi) -
      idealAHNumerator k chi * 0) / (1 + chi) ^ 2

noncomputable def idealAHPartialChi (k chi : ℝ) : ℝ :=
  (idealAHNumeratorChi k chi * (1 + chi) -
      idealAHNumerator k chi) / (1 + chi) ^ 2

noncomputable def idealDArg (k : ℝ) : ℝ :=
  1 + 1 / (2 * k)

noncomputable def idealDArgPartialK (k : ℝ) : ℝ :=
  -2 / (2 * k) ^ 2

noncomputable def idealDPartialK (k : ℝ) : ℝ :=
  (idealDArgPartialK k / idealDArg k) / 2 -
    4 / (4 * k + 3) ^ 2

noncomputable def idealBPartialK (k : ℝ) : ℝ :=
  -(1 / (1 + k)) / 2

noncomputable def idealP0PartialK (k chi : ℝ) : ℝ :=
  -idealAPartialK k chi

noncomputable def idealP0PartialChi (k chi : ℝ) : ℝ :=
  -idealAPartialChi k chi

noncomputable def idealSPartialK (k chi : ℝ) : ℝ :=
  1 / k - idealAPartialK k chi

noncomputable def idealSPartialChi (k chi : ℝ) : ℝ :=
  idealQChiPrime chi - idealAPartialChi k chi

noncomputable def idealT0PartialK (k chi : ℝ) : ℝ :=
  -idealAHPartialK k chi

noncomputable def idealT0PartialChi (k chi : ℝ) : ℝ :=
  -idealAHPartialChi k chi

/-- Explicit `k` partial of `Lambda`. -/
noncomputable def idealLambdaPartialK (k chi : ℝ) : ℝ :=
  2 * idealDPartialK k + idealSPartialK k chi

/-- Explicit `chi` partial of `Lambda`. -/
noncomputable def idealLambdaPartialChi (k chi : ℝ) : ℝ :=
  idealSPartialChi k chi

noncomputable def idealRInfPartialK (k chi : ℝ) : ℝ :=
  idealDPartialK k *
      (2 * Real.log 2 + 1 - lrDeterminantIdealA k chi) +
    lrDeterminantIdealD0 k * idealP0PartialK k chi +
    idealBPartialK k * lrDeterminantIdealS k chi +
    lrDeterminantIdealBConst k * idealSPartialK k chi +
    (1 / 6) * idealT0PartialK k chi +
    (1 / 3) * (idealBPartialK k - idealDPartialK k)

noncomputable def idealRInfPartialChi (k chi : ℝ) : ℝ :=
  lrDeterminantIdealD0 k * idealP0PartialChi k chi +
    lrDeterminantIdealBConst k * idealSPartialChi k chi +
    (1 / 6) * idealT0PartialChi k chi

/-- Explicit `k` partial of `C₁`. -/
noncomputable def idealC1PartialK (k chi : ℝ) : ℝ :=
  (1 / 3) *
    (idealT0PartialK k chi *
        (lrDeterminantIdealBConst k - lrDeterminantIdealD0 k -
          lrDeterminantIdealC / 2) +
      (lrDeterminantIdealT0 k chi - lrDeterminantIdealC) *
        (idealBPartialK k - idealDPartialK k))

/-- Explicit `chi` partial of `C₁`. -/
noncomputable def idealC1PartialChi (k chi : ℝ) : ℝ :=
  (1 / 3) *
    (idealT0PartialChi k chi *
      (lrDeterminantIdealBConst k - lrDeterminantIdealD0 k -
        lrDeterminantIdealC / 2))

/-- Explicit endpoint-`L` `k` partial of `F₀ = idealCore L₀`. -/
noncomputable def idealF0PartialK (config : Config) (k chi : ℝ) : ℝ :=
  config.l0 * idealLambdaPartialK k chi / 2 +
    idealRInfPartialK k chi +
    idealC1PartialK k chi /
      (config.l0 + lrDeterminantIdealC)

/-- Explicit endpoint-`L` `chi` partial of `F₀ = idealCore L₀`. -/
noncomputable def idealF0PartialChi (config : Config) (k chi : ℝ) : ℝ :=
  config.l0 * idealLambdaPartialChi k chi / 2 +
    idealRInfPartialChi k chi +
    idealC1PartialChi k chi /
      (config.l0 + lrDeterminantIdealC)

/-- Explicit `k` partial of the first transformed target in either mode. -/
noncomputable def targetFirstPartialK (config : Config)
    (point : CertificatePoint) : ℝ :=
  match config.mode with
  | .globalTail =>
      idealF0PartialK config point.k point.chi -
        idealC1PartialK point.k point.chi /
          (config.l0 + lrDeterminantIdealC)
  | .endpoint => idealF0PartialK config point.k point.chi

/-- Explicit `chi` partial of the first transformed target in either mode. -/
noncomputable def targetFirstPartialChi (config : Config)
    (point : CertificatePoint) : ℝ :=
  match config.mode with
  | .globalTail =>
      idealF0PartialChi config point.k point.chi -
        idealC1PartialChi point.k point.chi /
          (config.l0 + lrDeterminantIdealC)
  | .endpoint => idealF0PartialChi config point.k point.chi

/-- Explicit `k` partial of the second transformed target in either mode. -/
noncomputable def targetSecondPartialK (config : Config)
    (point : CertificatePoint) : ℝ :=
  match config.mode with
  | .globalTail => idealLambdaPartialK point.k point.chi / 2
  | .endpoint =>
      idealLambdaPartialK point.k point.chi / 2 -
        idealC1PartialK point.k point.chi /
          (config.l0 + lrDeterminantIdealC) ^ 2

/-- Explicit `chi` partial of the second transformed target in either mode. -/
noncomputable def targetSecondPartialChi (config : Config)
    (point : CertificatePoint) : ℝ :=
  match config.mode with
  | .globalTail => idealLambdaPartialChi point.k point.chi / 2
  | .endpoint =>
      idealLambdaPartialChi point.k point.chi / 2 -
        idealC1PartialChi point.k point.chi /
          (config.l0 + lrDeterminantIdealC) ^ 2

noncomputable def targetThirdPartialK (_config : Config)
    (point : CertificatePoint) : ℝ :=
  idealC1PartialK point.k point.chi

noncomputable def targetThirdPartialChi (_config : Config)
    (point : CertificatePoint) : ℝ :=
  idealC1PartialChi point.k point.chi

/-! ## Coordinate-only primitive soundness -/

theorem coordinate_inputs_sound
    {box : CertificateBox} {k chi : ℝ}
    (hk : box.kInterval.Contains k)
    (hchi : box.chiInterval.Contains chi) :
    (kAD box).Contains k 0 1 0 ∧
      (chiAD box).Contains chi 0 0 1 := by
  exact ⟨IntervalAD.contains_variableK hk,
    IntervalAD.contains_variableChi hchi⟩

theorem evaluatePrimitives_coordinate_sound
    (terms : ℕ) {box : CertificateBox} {payload : Payload}
    (hvalid : payload.Valid box) {k chi : ℝ}
    (hk : box.kInterval.Contains k)
    (hchi : box.chiInterval.Contains chi) :
    (evaluatePrimitives terms box payload).hK.Contains
        (lrDeterminantIdealH k) 0 (idealHPrime k) 0 ∧
      (evaluatePrimitives terms box payload).hKChi.Contains
        (lrDeterminantIdealH (k * chi)) 0
          (idealHPrime (k * chi) * chi)
          (idealHPrime (k * chi) * k) ∧
      (evaluatePrimitives terms box payload).qChi.Contains
        (lrSmallSBridgeQChi chi) 0 0 (idealQChiPrime chi) := by
  have hinputs := coordinate_inputs_sound hk hchi
  have hkLower : (0 : ℚ) ≤ (kAD box).value.lower := by
    simpa [kAD, CertificateBox.kInterval] using hvalid.domain.1.le
  have hchiLower : (0 : ℚ) ≤ (chiAD box).value.lower := by
    simpa [chiAD, CertificateBox.chiInterval] using
      hvalid.domain.2.2.1.le
  have hkChi := mulNonnegativeAD_sound hkLower hchiLower
    hinputs.1 hinputs.2
  have hkStrict : (0 : ℚ) < (kAD box).value.lower := by
    simpa [kAD, CertificateBox.kInterval] using hvalid.domain.1
  have hchiStrict : (0 : ℚ) < (chiAD box).value.lower := by
    simpa [chiAD, CertificateBox.chiInterval] using
      hvalid.domain.2.2.1
  have hkChiStrict : (0 : ℚ) < (kChiAD box).value.lower := by
    simp only [kChiAD, mulNonnegativeAD,
      RationalEnclosure.mulNonnegative]
    exact mul_pos hkStrict hchiStrict
  exact ⟨by
      simpa [evaluatePrimitives] using
        (idealHAD_sound terms hkStrict hvalid.hK hinputs.1),
    by
      simpa [evaluatePrimitives] using
        (idealHAD_sound terms hkChiStrict hvalid.hKChi hkChi),
    by
      simpa [evaluatePrimitives] using
        (idealQChiAD_sound terms hchiStrict hvalid.qChi hinputs.2)⟩

/-! ## Soundness of the complete shared graph -/

structure ConstantGraphContains (terms : ℕ) (config : Config)
    (payload : Payload) where
  logTwo : (logTwoAD terms payload).Contains (Real.log 2) 0 0 0
  logFourThird : (logFourThirdAD terms payload).Contains
    (Real.log (4 / 3)) 0 0 0
  l0 : (l0AD terms config payload).Contains config.l0 0 0 0
  c : (cAD terms payload).Contains lrDeterminantIdealC 0 0 0
  u : (uAD terms config payload).Contains
    (config.l0 + lrDeterminantIdealC) 0 0 0

theorem constantGraph_sound
    (terms : ℕ) {config : Config} {box : CertificateBox}
    {payload : Payload} (hvalid : payload.Valid box) :
    ConstantGraphContains terms config payload := by
  have hlogTwoRaw := IntervalAD.contains_log terms hvalid.logTwo
    (IntervalAD.contains_const 2)
  have hlogTwo : (logTwoAD terms payload).Contains
      (Real.log 2) 0 0 0 := by
    simpa [logTwoAD] using hlogTwoRaw
  have hlogFourRaw := IntervalAD.contains_log terms hvalid.logFourThird
    (IntervalAD.contains_const (4 / 3))
  have hlogFour : (logFourThirdAD terms payload).Contains
      (Real.log (4 / 3)) 0 0 0 := by
    simpa [logFourThirdAD] using hlogFourRaw
  have hl0Raw := IntervalAD.contains_mul
    (IntervalAD.contains_const config.l0Scale) hlogTwo
  have hl0 : (l0AD terms config payload).Contains config.l0 0 0 0 := by
    simpa [l0AD, Config.l0] using hl0Raw
  have hcRaw := IntervalAD.contains_add
    (IntervalAD.contains_sub (IntervalAD.contains_const 1)
      (IntervalAD.contains_mul (IntervalAD.contains_const 2) hlogTwo))
    (IntervalAD.contains_mul (IntervalAD.contains_const 16) hlogFour)
  have hc : (cAD terms payload).Contains
      lrDeterminantIdealC 0 0 0 := by
    convert hcRaw using 1 <;>
      simp [cAD, lrDeterminantIdealC] <;> ring
  have huRaw := IntervalAD.contains_add hl0 hc
  have hu : (uAD terms config payload).Contains
      (config.l0 + lrDeterminantIdealC) 0 0 0 := by
    simpa [uAD] using huRaw
  exact ⟨hlogTwo, hlogFour, hl0, hc, hu⟩

structure CoordinateGraphContains (terms : ℕ) (config : Config)
    (box : CertificateBox) (payload : Payload) (k chi : ℝ) where
  a : (aAD terms box payload).Contains
    (lrDeterminantIdealA k chi) 0
      (idealAPartialK k chi) (idealAPartialChi k chi)
  ah : (ahAD terms box payload).Contains
    (lrDeterminantIdealAH k chi) 0
      (idealAHPartialK k chi) (idealAHPartialChi k chi)
  d0 : (d0AD terms box payload).Contains
    (lrDeterminantIdealD0 k) 0 (idealDPartialK k) 0
  b : (bConstAD terms box payload).Contains
    (lrDeterminantIdealBConst k) 0 (idealBPartialK k) 0
  p0 : (p0AD terms box payload).Contains
    (2 * Real.log 2 + 1 - lrDeterminantIdealA k chi) 0
      (idealP0PartialK k chi) (idealP0PartialChi k chi)
  s : (sAD terms box payload).Contains
    (lrDeterminantIdealS k chi) 0
      (idealSPartialK k chi) (idealSPartialChi k chi)
  t0 : (t0AD terms box payload).Contains
    (lrDeterminantIdealT0 k chi) 0
      (idealT0PartialK k chi) (idealT0PartialChi k chi)

theorem coordinateGraph_sound
    (terms : ℕ) {config : Config} {box : CertificateBox}
    {payload : Payload} (hvalid : payload.Valid box)
    {k chi : ℝ} (hk : box.kInterval.Contains k)
    (hchi : box.chiInterval.Contains chi) :
    CoordinateGraphContains terms config box payload k chi := by
  have hconstants := constantGraph_sound terms (config := config) hvalid
  have hinputs := coordinate_inputs_sound hk hchi
  have hkAD := hinputs.1
  have hchiAD := hinputs.2
  have hkLower : (0 : ℚ) ≤ (kAD box).value.lower := by
    simpa [kAD, CertificateBox.kInterval] using hvalid.domain.1.le
  have hchiLower : (0 : ℚ) ≤ (chiAD box).value.lower := by
    simpa [chiAD, CertificateBox.chiInterval] using
      hvalid.domain.2.2.1.le
  have hkChi := mulNonnegativeAD_sound hkLower hchiLower hkAD hchiAD
  have honeK := IntervalAD.contains_add (IntervalAD.contains_const 1) hkAD
  have honeKChi := IntervalAD.contains_add
    (IntervalAD.contains_const 1) hkChi
  have honeChi := IntervalAD.contains_add
    (IntervalAD.contains_const 1) hchiAD
  have hlogK := IntervalAD.contains_log terms hvalid.logK hkAD
  have hlogOnePlusK := IntervalAD.contains_log terms
    hvalid.logOnePlusK honeK
  have hlogOnePlusKChi := IntervalAD.contains_log terms
    hvalid.logOnePlusKChi honeKChi
  have hprimitives := evaluatePrimitives_coordinate_sound terms hvalid hk hchi

  have hANumerator := IntervalAD.contains_add
    (IntervalAD.contains_mul hchiAD hlogOnePlusKChi) hlogOnePlusK
  have hAraw := IntervalAD.contains_divPositive hvalid.denominators.1
    hANumerator honeChi
  have hA : (aAD terms box payload).Contains
      (lrDeterminantIdealA k chi) 0
        (idealAPartialK k chi) (idealAPartialChi k chi) := by
    convert hAraw using 1 <;>
      simp [aAD, lrDeterminantIdealA, idealANumerator,
        idealANumeratorK, idealANumeratorChi, idealAPartialK,
        idealAPartialChi] <;> ring

  have hAHNumerator := IntervalAD.contains_add
    (IntervalAD.contains_mul hchiAD hprimitives.2.1) hprimitives.1
  have hAHRaw := IntervalAD.contains_divPositive hvalid.denominators.1
    hAHNumerator honeChi
  have hAH : (ahAD terms box payload).Contains
      (lrDeterminantIdealAH k chi) 0
        (idealAHPartialK k chi) (idealAHPartialChi k chi) := by
    convert hAHRaw using 1 <;>
      simp [ahAD, lrDeterminantIdealAH, idealAHNumerator,
        idealAHNumeratorK, idealAHNumeratorChi, idealAHPartialK,
        idealAHPartialChi] <;> ring

  have htwoK := mulNonnegativeAD_sound
    (by norm_num [IntervalAD.const, RationalEnclosure.point])
    hkLower (IntervalAD.contains_const 2) hkAD
  have hinvTwoK := IntervalAD.contains_invPositive
    hvalid.denominators.2.1 htwoK
  have hdArg := IntervalAD.contains_add
    (IntervalAD.contains_const 1) hinvTwoK
  have hlogDArg := IntervalAD.contains_log terms hvalid.logDArg hdArg
  have hfourK := mulNonnegativeAD_sound
    (by norm_num [IntervalAD.const, RationalEnclosure.point])
    hkLower (IntervalAD.contains_const 4) hkAD
  have hfourKThree := IntervalAD.contains_add hfourK
    (IntervalAD.contains_const 3)
  have hinvFourKThree := IntervalAD.contains_invPositive
    hvalid.denominators.2.2 hfourKThree
  have hD0Raw := IntervalAD.contains_add
    (IntervalAD.contains_mul (IntervalAD.contains_const (1 / 2))
      hlogDArg) hinvFourKThree
  have hD0 : (d0AD terms box payload).Contains
      (lrDeterminantIdealD0 k) 0 (idealDPartialK k) 0 := by
    convert hD0Raw using 1 <;>
      simp [d0AD, lrDeterminantIdealD0, idealDArg,
        idealDArgPartialK, idealDPartialK] <;> ring

  have hBRaw := IntervalAD.contains_sub hconstants.logTwo
    (IntervalAD.contains_mul (IntervalAD.contains_const (1 / 2))
      hlogOnePlusK)
  have hB : (bConstAD terms box payload).Contains
      (lrDeterminantIdealBConst k) 0 (idealBPartialK k) 0 := by
    convert hBRaw using 1 <;>
      simp [bConstAD, lrDeterminantIdealBConst, idealBPartialK] <;> ring

  have hP0Raw := IntervalAD.contains_sub
    (IntervalAD.contains_add
      (IntervalAD.contains_mul (IntervalAD.contains_const 2)
        hconstants.logTwo)
      (IntervalAD.contains_const 1)) hA
  have hP0 : (p0AD terms box payload).Contains
      (2 * Real.log 2 + 1 - lrDeterminantIdealA k chi) 0
        (idealP0PartialK k chi) (idealP0PartialChi k chi) := by
    convert hP0Raw using 1 <;>
      simp [p0AD, idealP0PartialK, idealP0PartialChi] <;> ring

  have hSRaw := IntervalAD.contains_sub
    (IntervalAD.contains_add hlogK hprimitives.2.2) hA
  have hS : (sAD terms box payload).Contains
      (lrDeterminantIdealS k chi) 0
        (idealSPartialK k chi) (idealSPartialChi k chi) := by
    convert hSRaw using 1 <;>
      simp [sAD, lrDeterminantIdealS, idealSPartialK,
        idealSPartialChi] <;> ring

  have hT0Raw := IntervalAD.contains_sub
    (IntervalAD.contains_add
      (IntervalAD.contains_mul (IntervalAD.contains_const 2)
        hconstants.logTwo)
      (IntervalAD.contains_const 1)) hAH
  have hT0 : (t0AD terms box payload).Contains
      (lrDeterminantIdealT0 k chi) 0
        (idealT0PartialK k chi) (idealT0PartialChi k chi) := by
    convert hT0Raw using 1 <;>
      simp [t0AD, lrDeterminantIdealT0, idealT0PartialK,
        idealT0PartialChi] <;> ring
  exact ⟨hA, hAH, hD0, hB, hP0, hS, hT0⟩

structure FullGraphContains (terms : ℕ) (config : Config)
    (box : CertificateBox) (payload : Payload) (k chi : ℝ) where
  lambdaHalf : (lambdaHalfAD terms box payload).Contains
    (lrDeterminantIdealLambda k chi / 2) 0
      (idealLambdaPartialK k chi / 2)
      (idealLambdaPartialChi k chi / 2)
  rInf : (rInfAD terms box payload).Contains
    (lrDeterminantIdealRInf k chi) 0
      (idealRInfPartialK k chi) (idealRInfPartialChi k chi)
  c1 : (c1AD terms box payload).Contains
    (lrDeterminantIdealC1 k chi) 0
      (idealC1PartialK k chi) (idealC1PartialChi k chi)
  f0 : (f0AD terms config box payload).Contains
    (lrDeterminantIdealCore config.l0 k chi) 0
      (idealF0PartialK config k chi) (idealF0PartialChi config k chi)
  uPositive : 0 < config.l0 + lrDeterminantIdealC

theorem fullGraph_sound
    (terms : ℕ) {config : Config} {box : CertificateBox}
    {payload : Payload} (hvalid : FullValid terms config box payload)
    {k chi : ℝ} (hk : box.kInterval.Contains k)
    (hchi : box.chiInterval.Contains chi) :
    FullGraphContains terms config box payload k chi := by
  have hconstants := constantGraph_sound terms (config := config)
    hvalid.payloadValid
  have hcoordinate := coordinateGraph_sound terms (config := config)
    hvalid.payloadValid hk hchi

  have hLambdaRaw := IntervalAD.contains_mul
    (IntervalAD.contains_const (1 / 2))
    (IntervalAD.contains_add
      (IntervalAD.contains_add
        (IntervalAD.contains_mul (IntervalAD.contains_const 2)
          hcoordinate.d0) hcoordinate.s)
      (IntervalAD.contains_const (1 / 3)))
  have hLambda : (lambdaHalfAD terms box payload).Contains
      (lrDeterminantIdealLambda k chi / 2) 0
        (idealLambdaPartialK k chi / 2)
        (idealLambdaPartialChi k chi / 2) := by
    convert hLambdaRaw using 1 <;>
      simp [lambdaHalfAD, lrDeterminantIdealLambda,
        idealLambdaPartialK, idealLambdaPartialChi] <;> ring

  have hRInfRaw := IntervalAD.contains_add
    (IntervalAD.contains_add
      (IntervalAD.contains_mul hcoordinate.d0 hcoordinate.p0)
      (IntervalAD.contains_mul hcoordinate.b hcoordinate.s))
    (IntervalAD.contains_add
      (IntervalAD.contains_mul (IntervalAD.contains_const (1 / 6))
        (IntervalAD.contains_sub hcoordinate.t0 hconstants.c))
      (IntervalAD.contains_mul (IntervalAD.contains_const (1 / 3))
        (IntervalAD.contains_sub hcoordinate.b hcoordinate.d0)))
  have hRInf : (rInfAD terms box payload).Contains
      (lrDeterminantIdealRInf k chi) 0
        (idealRInfPartialK k chi) (idealRInfPartialChi k chi) := by
    convert hRInfRaw using 1 <;>
      simp [rInfAD, lrDeterminantIdealRInf,
        idealRInfPartialK, idealRInfPartialChi] <;> ring

  have hSecond := IntervalAD.contains_sub
    (IntervalAD.contains_sub hcoordinate.b hcoordinate.d0)
    (IntervalAD.contains_mul (IntervalAD.contains_const (1 / 2))
      hconstants.c)
  have hC1Raw := IntervalAD.contains_mul
    (IntervalAD.contains_const (1 / 3))
    (IntervalAD.contains_mul
      (IntervalAD.contains_sub hcoordinate.t0 hconstants.c) hSecond)
  have hC1 : (c1AD terms box payload).Contains
      (lrDeterminantIdealC1 k chi) 0
        (idealC1PartialK k chi) (idealC1PartialChi k chi) := by
    convert hC1Raw using 1 <;>
      simp [c1AD, lrDeterminantIdealC1,
        idealC1PartialK, idealC1PartialChi] <;>
      ring_nf <;> simp

  have huPos : 0 < config.l0 + lrDeterminantIdealC := by
    have hlo : (0 : ℝ) <
        ((uAD terms config payload).value.lower : ℝ) := by
      exact_mod_cast hvalid.uPositive
    exact hlo.trans_le hconstants.u.1.1
  have hquotient := IntervalAD.contains_divPositive hvalid.uPositive
    hC1 hconstants.u
  have hF0Raw := IntervalAD.contains_add
    (IntervalAD.contains_add
      (IntervalAD.contains_mul hconstants.l0 hLambda) hRInf)
    hquotient
  have hcoreEq := lrDeterminantIdealCore_eq_separated
    (L := config.l0) (k := k) (chi := chi) huPos.ne'
  have hF0 : (f0AD terms config box payload).Contains
      (lrDeterminantIdealCore config.l0 k chi) 0
        (idealF0PartialK config k chi)
        (idealF0PartialChi config k chi) := by
    rw [hcoreEq]
    convert hF0Raw using 1 <;>
      simp [f0AD, idealF0PartialK, idealF0PartialChi] <;>
      field_simp [huPos.ne'] <;> ring
  exact ⟨hLambda, hRInf, hC1, hF0, huPos⟩

/-- Full value-and-partial containment of the three transformed outputs.
Only `k` and `chi` membership is needed because the graph is independent of
the dummy `s` coordinate. -/
theorem evaluateTargets_coordinate_sound
    (terms : ℕ) {config : Config} {box : CertificateBox}
    {payload : Payload} (hvalid : FullValid terms config box payload)
    {point : CertificatePoint}
    (hk : box.kInterval.Contains point.k)
    (hchi : box.chiInterval.Contains point.chi) :
    (evaluateTargets terms config box payload).first.Contains
        (targetFirst config point) 0
          (targetFirstPartialK config point)
          (targetFirstPartialChi config point) ∧
      (evaluateTargets terms config box payload).second.Contains
        (targetSecond config point) 0
          (targetSecondPartialK config point)
          (targetSecondPartialChi config point) ∧
      (evaluateTargets terms config box payload).third.Contains
        (targetThird config point) 0
          (targetThirdPartialK config point)
          (targetThirdPartialChi config point) := by
  have hconstants := constantGraph_sound terms (config := config)
    hvalid.payloadValid
  have hfull := fullGraph_sound terms hvalid hk hchi
  have hmargin := IntervalAD.contains_const config.margin
  cases hmode : config.mode with
  | globalTail =>
      have htail := IntervalAD.contains_divPositive hvalid.uPositive
        hfull.c1 hconstants.u
      have hfirstRaw := IntervalAD.contains_sub
        (IntervalAD.contains_sub hfull.f0 htail) hmargin
      have hfirst :
          (evaluateTargets terms config box payload).first.Contains
            (targetFirst config point) 0
              (targetFirstPartialK config point)
              (targetFirstPartialChi config point) := by
        convert hfirstRaw using 1 <;>
          simp [evaluateTargets, hmode, targetFirst,
            targetFirstPartialK, targetFirstPartialChi] <;>
          field_simp [hfull.uPositive.ne'] <;> ring
      have hsecond :
          (evaluateTargets terms config box payload).second.Contains
            (targetSecond config point) 0
              (targetSecondPartialK config point)
              (targetSecondPartialChi config point) := by
        simpa [evaluateTargets, hmode, targetSecond,
          targetSecondPartialK, targetSecondPartialChi] using
          hfull.lambdaHalf
      have hthird :
          (evaluateTargets terms config box payload).third.Contains
            (targetThird config point) 0
              (targetThirdPartialK config point)
              (targetThirdPartialChi config point) := by
        simpa [evaluateTargets, hmode, targetThird,
          targetThirdPartialK, targetThirdPartialChi] using hfull.c1
      exact ⟨hfirst, hsecond, hthird⟩
  | endpoint =>
      have huSquare := mulNonnegativeAD_sound hvalid.uPositive.le
        hvalid.uPositive.le hconstants.u hconstants.u
      have huSquarePositive : (0 : ℚ) <
          (uSquareAD terms config payload).value.lower := by
        simp only [uSquareAD, mulNonnegativeAD,
          RationalEnclosure.mulNonnegative]
        exact mul_pos hvalid.uPositive hvalid.uPositive
      have hderivativeTail := IntervalAD.contains_divPositive
        huSquarePositive hfull.c1 huSquare
      have hfirstRaw := IntervalAD.contains_sub hfull.f0 hmargin
      have hsecondRaw := IntervalAD.contains_sub
        hfull.lambdaHalf hderivativeTail
      have hfirst :
          (evaluateTargets terms config box payload).first.Contains
            (targetFirst config point) 0
              (targetFirstPartialK config point)
              (targetFirstPartialChi config point) := by
        simpa [evaluateTargets, hmode, targetFirst,
          targetFirstPartialK, targetFirstPartialChi] using hfirstRaw
      have hsecond :
          (evaluateTargets terms config box payload).second.Contains
            (targetSecond config point) 0
              (targetSecondPartialK config point)
              (targetSecondPartialChi config point) := by
        convert hsecondRaw using 1 <;>
          simp [evaluateTargets, hmode, targetSecond,
            lrDeterminantIdealLDerivative,
            targetSecondPartialK, targetSecondPartialChi] <;>
          field_simp [hfull.uPositive.ne'] <;> ring
      have hthird :
          (evaluateTargets terms config box payload).third.Contains
            (targetThird config point) 0
              (targetThirdPartialK config point)
              (targetThirdPartialChi config point) := by
        simpa [evaluateTargets, hmode, targetThird,
          targetThirdPartialK, targetThirdPartialChi] using hfull.c1
      exact ⟨hfirst, hsecond, hthird⟩

theorem evaluateTargets_sound
    (terms : ℕ) {config : Config} {box : CertificateBox}
    {payload : Payload} (hvalid : FullValid terms config box payload)
    {point : CertificatePoint} (hpoint : box.Contains point) :
    (evaluateTargets terms config box payload).first.Contains
        (targetFirst config point) 0
          (targetFirstPartialK config point)
          (targetFirstPartialChi config point) ∧
      (evaluateTargets terms config box payload).second.Contains
        (targetSecond config point) 0
          (targetSecondPartialK config point)
          (targetSecondPartialChi config point) ∧
      (evaluateTargets terms config box payload).third.Contains
        (targetThird config point) 0
          (targetThirdPartialK config point)
          (targetThirdPartialChi config point) := by
  exact evaluateTargets_coordinate_sound terms hvalid
    ⟨hpoint.2.2.1, hpoint.2.2.2.1⟩
    ⟨hpoint.2.2.2.2.1, hpoint.2.2.2.2.2⟩

/-! ## Coordinate calculus for the real graph -/

theorem hasDerivAt_idealA_k {k chi : ℝ}
    (hk : 0 < k) (hchi : 0 < chi) :
    HasDerivAt (fun z ↦ lrDeterminantIdealA z chi)
      (idealAPartialK k chi) k := by
  have hkChi : HasDerivAt (fun z : ℝ ↦ z * chi) chi k := by
    simpa using (hasDerivAt_id k).mul_const chi
  have honeKChi := (hasDerivAt_const k 1).add hkChi
  have honeKChiPos : 0 < 1 + k * chi := by positivity
  have hlogKChi := honeKChi.log honeKChiPos.ne'
  have hweighted := (hasDerivAt_const k chi).mul hlogKChi
  have honeK := (hasDerivAt_const k 1).add (hasDerivAt_id k)
  have honeKPos : 0 < 1 + k := by positivity
  have hlogK := honeK.log honeKPos.ne'
  have hnum := hweighted.add hlogK
  have hden := hasDerivAt_const k (1 + chi)
  have hdenNe : 1 + chi ≠ 0 := by positivity
  have hquot := hnum.div hden hdenNe
  convert hquot using 1 <;>
    simp [lrDeterminantIdealA, idealANumerator, idealANumeratorK,
      idealAPartialK] <;> ring

theorem hasDerivAt_idealA_chi {k chi : ℝ}
    (hk : 0 < k) (hchi : 0 < chi) :
    HasDerivAt (fun z ↦ lrDeterminantIdealA k z)
      (idealAPartialChi k chi) chi := by
  have hkChi : HasDerivAt (fun z : ℝ ↦ k * z) k chi := by
    simpa using (hasDerivAt_id chi).const_mul k
  have honeKChi := (hasDerivAt_const chi 1).add hkChi
  have honeKChiPos : 0 < 1 + k * chi := by positivity
  have hlogKChi := honeKChi.log honeKChiPos.ne'
  have hweighted := (hasDerivAt_id chi).mul hlogKChi
  have hlogK := hasDerivAt_const chi (Real.log (1 + k))
  have hnum := hweighted.add hlogK
  have hden := (hasDerivAt_const chi 1).add (hasDerivAt_id chi)
  have hdenNe : 1 + chi ≠ 0 := by positivity
  have hquot := hnum.div hden hdenNe
  convert hquot using 1 <;>
    simp [lrDeterminantIdealA, idealANumerator, idealANumeratorChi,
      idealAPartialChi] <;> ring

theorem hasDerivAt_idealAH_k {k chi : ℝ}
    (hk : 0 < k) (hchi : 0 < chi) :
    HasDerivAt (fun z ↦ lrDeterminantIdealAH z chi)
      (idealAHPartialK k chi) k := by
  have hkChi : HasDerivAt (fun z : ℝ ↦ z * chi) chi k := by
    simpa using (hasDerivAt_id k).mul_const chi
  have hHChi := (hasDerivAt_lrDeterminantIdealH
    (mul_pos hk hchi)).comp k hkChi
  have hweighted := (hasDerivAt_const k chi).mul hHChi
  have hHK := hasDerivAt_lrDeterminantIdealH hk
  have hnum := hweighted.add hHK
  have hden := hasDerivAt_const k (1 + chi)
  have hdenNe : 1 + chi ≠ 0 := by positivity
  have hquot := hnum.div hden hdenNe
  convert hquot using 1 <;>
    simp [lrDeterminantIdealAH, idealHPrime,
      idealAHNumerator, idealAHNumeratorK, idealAHPartialK] <;> ring

theorem hasDerivAt_idealAH_chi {k chi : ℝ}
    (hk : 0 < k) (hchi : 0 < chi) :
    HasDerivAt (fun z ↦ lrDeterminantIdealAH k z)
      (idealAHPartialChi k chi) chi := by
  have hkChi : HasDerivAt (fun z : ℝ ↦ k * z) k chi := by
    simpa using (hasDerivAt_id chi).const_mul k
  have hHChi := (hasDerivAt_lrDeterminantIdealH
    (mul_pos hk hchi)).comp chi hkChi
  have hweighted := (hasDerivAt_id chi).mul hHChi
  have hHK := hasDerivAt_const chi (lrDeterminantIdealH k)
  have hnum := hweighted.add hHK
  have hden := (hasDerivAt_const chi 1).add (hasDerivAt_id chi)
  have hdenNe : 1 + chi ≠ 0 := by positivity
  have hquot := hnum.div hden hdenNe
  convert hquot using 1 <;>
    simp [lrDeterminantIdealAH, idealHPrime,
      idealAHNumerator, idealAHNumeratorChi, idealAHPartialChi] <;> ring

theorem hasDerivAt_idealD0_k {k : ℝ} (hk : 0 < k) :
    HasDerivAt lrDeterminantIdealD0 (idealDPartialK k) k := by
  have htwoK : HasDerivAt (fun z : ℝ ↦ 2 * z) 2 k := by
    simpa using (hasDerivAt_id k).const_mul 2
  have htwoKNe : 2 * k ≠ 0 := by positivity
  have hinvTwoK := (hasDerivAt_const k 1).div htwoK htwoKNe
  have hdArg := (hasDerivAt_const k 1).add hinvTwoK
  have hdArgPos : 0 < idealDArg k := by
    simp [idealDArg]
    positivity
  have hlog := hdArg.log hdArgPos.ne'
  have hfirst := hlog.div_const 2
  have hfourK : HasDerivAt (fun z : ℝ ↦ 4 * z) 4 k := by
    simpa using (hasDerivAt_id k).const_mul 4
  have hfourKThree := hfourK.add_const 3
  have hfourKThreeNe : 4 * k + 3 ≠ 0 := by positivity
  have hsecond := (hasDerivAt_const k 1).div
    hfourKThree hfourKThreeNe
  have hsum := hfirst.add hsecond
  convert hsum using 1 <;>
    simp [lrDeterminantIdealD0, idealDArg, idealDArgPartialK,
      idealDPartialK] <;>
    field_simp [hk.ne'] <;> ring

theorem hasDerivAt_idealBConst_k {k : ℝ} (hk : 0 < k) :
    HasDerivAt lrDeterminantIdealBConst (idealBPartialK k) k := by
  have honeK := (hasDerivAt_const k 1).add (hasDerivAt_id k)
  have honeKPos : 0 < 1 + k := by positivity
  have hlog := honeK.log honeKPos.ne'
  have h := (hasDerivAt_const k (Real.log 2)).sub (hlog.div_const 2)
  convert h using 1 <;>
    simp [lrDeterminantIdealBConst, idealBPartialK] <;> ring

theorem hasDerivAt_idealS_k {k chi : ℝ}
    (hk : 0 < k) (hchi : 0 < chi) :
    HasDerivAt (fun z ↦ lrDeterminantIdealS z chi)
      (idealSPartialK k chi) k := by
  have hlog := Real.hasDerivAt_log hk.ne'
  have hq := hasDerivAt_const k (lrSmallSBridgeQChi chi)
  have hA := hasDerivAt_idealA_k hk hchi
  have h := (hlog.add hq).sub hA
  convert h using 1 <;>
    simp [lrDeterminantIdealS, idealSPartialK] <;> ring

theorem hasDerivAt_idealS_chi {k chi : ℝ}
    (hk : 0 < k) (hchi : 0 < chi) :
    HasDerivAt (fun z ↦ lrDeterminantIdealS k z)
      (idealSPartialChi k chi) chi := by
  have hlog := hasDerivAt_const chi (Real.log k)
  have hq := hasDerivAt_lrSmallSBridgeQChi hchi
  have hA := hasDerivAt_idealA_chi hk hchi
  have h := (hlog.add hq).sub hA
  convert h using 1 <;>
    simp [lrDeterminantIdealS, idealQChiPrime,
      idealSPartialChi] <;> ring

theorem hasDerivAt_idealT0_k {k chi : ℝ}
    (hk : 0 < k) (hchi : 0 < chi) :
    HasDerivAt (fun z ↦ lrDeterminantIdealT0 z chi)
      (idealT0PartialK k chi) k := by
  have hAH := hasDerivAt_idealAH_k hk hchi
  have h := (hasDerivAt_const k (2 * Real.log 2 + 1)).sub hAH
  convert h using 1 <;>
    simp [lrDeterminantIdealT0, idealT0PartialK] <;> ring

theorem hasDerivAt_idealT0_chi {k chi : ℝ}
    (hk : 0 < k) (hchi : 0 < chi) :
    HasDerivAt (fun z ↦ lrDeterminantIdealT0 k z)
      (idealT0PartialChi k chi) chi := by
  have hAH := hasDerivAt_idealAH_chi hk hchi
  have h := (hasDerivAt_const chi (2 * Real.log 2 + 1)).sub hAH
  convert h using 1 <;>
    simp [lrDeterminantIdealT0, idealT0PartialChi] <;> ring

theorem hasDerivAt_idealLambda_k {k chi : ℝ}
    (hk : 0 < k) (hchi : 0 < chi) :
    HasDerivAt (fun z ↦ lrDeterminantIdealLambda z chi)
      (idealLambdaPartialK k chi) k := by
  have hD := hasDerivAt_idealD0_k hk
  have hS := hasDerivAt_idealS_k hk hchi
  have h := ((hD.const_mul 2).add hS).add_const (1 / 3)
  convert h using 1 <;>
    simp [lrDeterminantIdealLambda, idealLambdaPartialK] <;> ring

theorem hasDerivAt_idealLambda_chi {k chi : ℝ}
    (hk : 0 < k) (hchi : 0 < chi) :
    HasDerivAt (fun z ↦ lrDeterminantIdealLambda k z)
      (idealLambdaPartialChi k chi) chi := by
  have hS := hasDerivAt_idealS_chi hk hchi
  have h := ((hasDerivAt_const chi (2 * lrDeterminantIdealD0 k)).add
    hS).add_const (1 / 3)
  convert h using 1 <;>
    simp [lrDeterminantIdealLambda, idealLambdaPartialChi] <;> ring

theorem hasDerivAt_idealRInf_k {k chi : ℝ}
    (hk : 0 < k) (hchi : 0 < chi) :
    HasDerivAt (fun z ↦ lrDeterminantIdealRInf z chi)
      (idealRInfPartialK k chi) k := by
  have hD := hasDerivAt_idealD0_k hk
  have hA := hasDerivAt_idealA_k hk hchi
  have hP0 := (hasDerivAt_const k (2 * Real.log 2 + 1)).sub hA
  have hB := hasDerivAt_idealBConst_k hk
  have hS := hasDerivAt_idealS_k hk hchi
  have hT0 := hasDerivAt_idealT0_k hk hchi
  have h := ((hD.mul hP0).add (hB.mul hS)).add
    (((hT0.sub_const lrDeterminantIdealC).const_mul (1 / 6)).add
      ((hB.sub hD).const_mul (1 / 3)))
  convert h using 1 <;>
    simp [lrDeterminantIdealRInf, idealRInfPartialK,
      idealP0PartialK] <;> try ring
  all_goals
    funext z
    simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply]
    ring

theorem hasDerivAt_idealRInf_chi {k chi : ℝ}
    (hk : 0 < k) (hchi : 0 < chi) :
    HasDerivAt (fun z ↦ lrDeterminantIdealRInf k z)
      (idealRInfPartialChi k chi) chi := by
  have hD := hasDerivAt_const chi (lrDeterminantIdealD0 k)
  have hA := hasDerivAt_idealA_chi hk hchi
  have hP0 := (hasDerivAt_const chi (2 * Real.log 2 + 1)).sub hA
  have hB := hasDerivAt_const chi (lrDeterminantIdealBConst k)
  have hS := hasDerivAt_idealS_chi hk hchi
  have hT0 := hasDerivAt_idealT0_chi hk hchi
  have h := ((hD.mul hP0).add (hB.mul hS)).add
    (((hT0.sub_const lrDeterminantIdealC).const_mul (1 / 6)).add
      (((hasDerivAt_const chi (lrDeterminantIdealBConst k)).sub
        (hasDerivAt_const chi (lrDeterminantIdealD0 k))).const_mul (1 / 3)))
  convert h using 1 <;>
    simp [lrDeterminantIdealRInf, idealRInfPartialChi,
      idealP0PartialChi] <;> try ring
  all_goals
    funext z
    simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply]
    ring

theorem hasDerivAt_idealC1_k {k chi : ℝ}
    (hk : 0 < k) (hchi : 0 < chi) :
    HasDerivAt (fun z ↦ lrDeterminantIdealC1 z chi)
      (idealC1PartialK k chi) k := by
  have hT0 := hasDerivAt_idealT0_k hk hchi
  have hB := hasDerivAt_idealBConst_k hk
  have hD := hasDerivAt_idealD0_k hk
  have hleft := hT0.sub_const lrDeterminantIdealC
  have hright := (hB.sub hD).sub_const (lrDeterminantIdealC / 2)
  have h := (hleft.mul hright).const_mul (1 / 3)
  convert h using 1 <;>
    simp [lrDeterminantIdealC1, idealC1PartialK] <;> try ring
  all_goals
    funext z
    ring

theorem hasDerivAt_idealC1_chi {k chi : ℝ}
    (hk : 0 < k) (hchi : 0 < chi) :
    HasDerivAt (fun z ↦ lrDeterminantIdealC1 k z)
      (idealC1PartialChi k chi) chi := by
  have hT0 := hasDerivAt_idealT0_chi hk hchi
  have hleft := hT0.sub_const lrDeterminantIdealC
  have hright := hasDerivAt_const chi
    (lrDeterminantIdealBConst k - lrDeterminantIdealD0 k -
      lrDeterminantIdealC / 2)
  have h := (hleft.mul hright).const_mul (1 / 3)
  convert h using 1 <;>
    simp [lrDeterminantIdealC1, idealC1PartialChi] <;> try ring
  all_goals
    funext z
    ring

theorem hasDerivAt_idealF0_k {config : Config} {k chi : ℝ}
    (hk : 0 < k) (hchi : 0 < chi)
    (hu : config.l0 + lrDeterminantIdealC ≠ 0) :
    HasDerivAt
      (fun z ↦ lrDeterminantIdealCore config.l0 z chi)
      (idealF0PartialK config k chi) k := by
  have hLambda := hasDerivAt_idealLambda_k hk hchi
  have hRInf := hasDerivAt_idealRInf_k hk hchi
  have hC1 := hasDerivAt_idealC1_k hk hchi
  have hSeparated :=
    ((hLambda.div_const 2).const_mul config.l0).add hRInf |>.add
      (hC1.div_const (config.l0 + lrDeterminantIdealC))
  have heq :
      (fun z ↦ lrDeterminantIdealCore config.l0 z chi) =
        (fun z ↦
          config.l0 * lrDeterminantIdealLambda z chi / 2 +
            lrDeterminantIdealRInf z chi +
            lrDeterminantIdealC1 z chi /
              (config.l0 + lrDeterminantIdealC)) := by
    funext z
    rw [lrDeterminantIdealCore_eq_separated hu]
  rw [heq]
  convert hSeparated using 1
  · funext z
    simp only [Pi.add_apply]
    ring
  · simp only [idealF0PartialK, div_eq_mul_inv]
    ring

theorem hasDerivAt_idealF0_chi {config : Config} {k chi : ℝ}
    (hk : 0 < k) (hchi : 0 < chi)
    (hu : config.l0 + lrDeterminantIdealC ≠ 0) :
    HasDerivAt
      (fun z ↦ lrDeterminantIdealCore config.l0 k z)
      (idealF0PartialChi config k chi) chi := by
  have hLambda := hasDerivAt_idealLambda_chi hk hchi
  have hRInf := hasDerivAt_idealRInf_chi hk hchi
  have hC1 := hasDerivAt_idealC1_chi hk hchi
  have hSeparated :=
    ((hLambda.div_const 2).const_mul config.l0).add hRInf |>.add
      (hC1.div_const (config.l0 + lrDeterminantIdealC))
  have heq :
      (fun z ↦ lrDeterminantIdealCore config.l0 k z) =
        (fun z ↦
          config.l0 * lrDeterminantIdealLambda k z / 2 +
            lrDeterminantIdealRInf k z +
            lrDeterminantIdealC1 k z /
              (config.l0 + lrDeterminantIdealC)) := by
    funext z
    rw [lrDeterminantIdealCore_eq_separated hu]
  rw [heq]
  convert hSeparated using 1
  · funext z
    simp only [Pi.add_apply]
    ring
  · simp only [idealF0PartialChi, div_eq_mul_inv]
    ring

theorem hasDerivAt_targetFirst_s (config : Config)
    (point : CertificatePoint) :
    HasDerivAt (fun s ↦ targetFirst config { point with s := s })
      0 point.s := by
  simpa only [targetFirst_update_s] using
    (hasDerivAt_const point.s (targetFirst config point))

theorem hasDerivAt_targetSecond_s (config : Config)
    (point : CertificatePoint) :
    HasDerivAt (fun s ↦ targetSecond config { point with s := s })
      0 point.s := by
  simpa only [targetSecond_update_s] using
    (hasDerivAt_const point.s (targetSecond config point))

theorem hasDerivAt_targetThird_s (config : Config)
    (point : CertificatePoint) :
    HasDerivAt (fun s ↦ targetThird config { point with s := s })
      0 point.s := by
  simpa only [targetThird_update_s] using
    (hasDerivAt_const point.s (targetThird config point))

theorem hasDerivAt_targetFirst_k (config : Config)
    (point : CertificatePoint) (hk : 0 < point.k)
    (hchi : 0 < point.chi)
    (hu : config.l0 + lrDeterminantIdealC ≠ 0) :
    HasDerivAt
      (fun k ↦ targetFirst config { point with k := k })
      (targetFirstPartialK config point) point.k := by
  have hF0 := hasDerivAt_idealF0_k hk hchi hu
  have hC1 := hasDerivAt_idealC1_k hk hchi
  cases hmode : config.mode with
  | globalTail =>
      have h := (hF0.sub
        (hC1.div_const (config.l0 + lrDeterminantIdealC))).sub_const
          (config.margin : ℝ)
      simpa [targetFirst, targetFirstPartialK, hmode] using h
  | endpoint =>
      simpa [targetFirst, targetFirstPartialK, hmode] using
        hF0.sub_const (config.margin : ℝ)

theorem hasDerivAt_targetFirst_chi (config : Config)
    (point : CertificatePoint) (hk : 0 < point.k)
    (hchi : 0 < point.chi)
    (hu : config.l0 + lrDeterminantIdealC ≠ 0) :
    HasDerivAt
      (fun chi ↦ targetFirst config { point with chi := chi })
      (targetFirstPartialChi config point) point.chi := by
  have hF0 := hasDerivAt_idealF0_chi hk hchi hu
  have hC1 := hasDerivAt_idealC1_chi hk hchi
  cases hmode : config.mode with
  | globalTail =>
      have h := (hF0.sub
        (hC1.div_const (config.l0 + lrDeterminantIdealC))).sub_const
          (config.margin : ℝ)
      simpa [targetFirst, targetFirstPartialChi, hmode] using h
  | endpoint =>
      simpa [targetFirst, targetFirstPartialChi, hmode] using
        hF0.sub_const (config.margin : ℝ)

theorem hasDerivAt_targetSecond_k (config : Config)
    (point : CertificatePoint) (hk : 0 < point.k)
    (hchi : 0 < point.chi)
    (hu : config.l0 + lrDeterminantIdealC ≠ 0) :
    HasDerivAt
      (fun k ↦ targetSecond config { point with k := k })
      (targetSecondPartialK config point) point.k := by
  have hLambda := hasDerivAt_idealLambda_k hk hchi
  have hC1 := hasDerivAt_idealC1_k hk hchi
  cases hmode : config.mode with
  | globalTail =>
      simpa [targetSecond, targetSecondPartialK, hmode] using
        hLambda.div_const 2
  | endpoint =>
      have h := (hLambda.div_const 2).sub
        (hC1.div_const ((config.l0 + lrDeterminantIdealC) ^ 2))
      simpa [targetSecond, targetSecondPartialK, hmode,
        lrDeterminantIdealLDerivative] using h

theorem hasDerivAt_targetSecond_chi (config : Config)
    (point : CertificatePoint) (hk : 0 < point.k)
    (hchi : 0 < point.chi)
    (hu : config.l0 + lrDeterminantIdealC ≠ 0) :
    HasDerivAt
      (fun chi ↦ targetSecond config { point with chi := chi })
      (targetSecondPartialChi config point) point.chi := by
  have hLambda := hasDerivAt_idealLambda_chi hk hchi
  have hC1 := hasDerivAt_idealC1_chi hk hchi
  cases hmode : config.mode with
  | globalTail =>
      simpa [targetSecond, targetSecondPartialChi, hmode] using
        hLambda.div_const 2
  | endpoint =>
      have h := (hLambda.div_const 2).sub
        (hC1.div_const ((config.l0 + lrDeterminantIdealC) ^ 2))
      simpa [targetSecond, targetSecondPartialChi, hmode,
        lrDeterminantIdealLDerivative] using h

theorem hasDerivAt_targetThird_k (config : Config)
    (point : CertificatePoint) (hk : 0 < point.k)
    (hchi : 0 < point.chi) :
    HasDerivAt
      (fun k ↦ targetThird config { point with k := k })
      (targetThirdPartialK config point) point.k := by
  simpa [targetThird, targetThirdPartialK] using
    (hasDerivAt_idealC1_k hk hchi)

theorem hasDerivAt_targetThird_chi (config : Config)
    (point : CertificatePoint) (hk : 0 < point.k)
    (hchi : 0 < point.chi) :
    HasDerivAt
      (fun chi ↦ targetThird config { point with chi := chi })
      (targetThirdPartialChi config point) point.chi := by
  simpa [targetThird, targetThirdPartialChi] using
    (hasDerivAt_idealC1_chi hk hchi)

/-! ## `BoxDerivativeEnclosures` adapters -/

def firstMidpointCertificate (terms : ℕ) (config : Config)
    (box : CertificateBox) (payload : Payload) : MidpointCertificate where
  value := (evaluateTargets terms config box payload).first.value
  derivS := (evaluateTargets terms config box payload).first.derivS
  derivK := (evaluateTargets terms config box payload).first.derivK
  derivChi := (evaluateTargets terms config box payload).first.derivChi

def secondMidpointCertificate (terms : ℕ) (config : Config)
    (box : CertificateBox) (payload : Payload) : MidpointCertificate where
  value := (evaluateTargets terms config box payload).second.value
  derivS := (evaluateTargets terms config box payload).second.derivS
  derivK := (evaluateTargets terms config box payload).second.derivK
  derivChi := (evaluateTargets terms config box payload).second.derivChi

def thirdMidpointCertificate (terms : ℕ) (config : Config)
    (box : CertificateBox) (payload : Payload) : MidpointCertificate where
  value := (evaluateTargets terms config box payload).third.value
  derivS := (evaluateTargets terms config box payload).third.derivS
  derivK := (evaluateTargets terms config box payload).third.derivK
  derivChi := (evaluateTargets terms config box payload).third.derivChi

theorem real_u_positive_of_fullValid
    {terms : ℕ} {config : Config} {box : CertificateBox}
    {payload : Payload} (hvalid : FullValid terms config box payload) :
    0 < config.l0 + lrDeterminantIdealC := by
  have hu := (constantGraph_sound terms (config := config)
    hvalid.payloadValid).u
  have hlo : (0 : ℝ) <
      ((uAD terms config payload).value.lower : ℝ) := by
    exact_mod_cast hvalid.uPositive
  exact hlo.trans_le hu.1.1

theorem positive_coordinates_of_fullValid
    {terms : ℕ} {config : Config} {box : CertificateBox}
    {payload : Payload} (hvalid : FullValid terms config box payload)
    {point : CertificatePoint} (hpoint : box.Contains point) :
    0 < point.k ∧ 0 < point.chi := by
  have hkLo : (0 : ℝ) < (box.kLo : ℝ) := by
    exact_mod_cast hvalid.payloadValid.domain.1
  have hchiLo : (0 : ℝ) < (box.chiLo : ℝ) := by
    exact_mod_cast hvalid.payloadValid.domain.2.2.1
  exact ⟨hkLo.trans_le hpoint.2.2.1,
    hchiLo.trans_le hpoint.2.2.2.2.1⟩

theorem coordinate_midpoint_mem_of_fullValid
    {terms : ℕ} {config : Config} {box : CertificateBox}
    {payload : Payload} (hvalid : FullValid terms config box payload) :
    box.kInterval.Contains box.midpoint.k ∧
      box.chiInterval.Contains box.midpoint.chi := by
  have hkValid : (box.kLo : ℝ) ≤ (box.kHi : ℝ) := by
    exact_mod_cast hvalid.payloadValid.domain.2.1
  have hchiValid : (box.chiLo : ℝ) ≤ (box.chiHi : ℝ) := by
    exact_mod_cast hvalid.payloadValid.domain.2.2.2.1
  constructor
  · constructor <;>
      norm_num [CertificateBox.midpoint, RationalEnclosure.center,
        CertificateBox.kInterval] <;> linarith
  · constructor <;>
      norm_num [CertificateBox.midpoint, RationalEnclosure.center,
        CertificateBox.chiInterval] <;> linarith

theorem first_midpoint_value_sound
    (terms : ℕ) {config : Config} {box : CertificateBox}
    {payload : Payload} (hvalid : FullValid terms config box payload) :
    (firstMidpointCertificate terms config box payload).value.Contains
      (targetFirst config box.midpoint) := by
  have hmid := coordinate_midpoint_mem_of_fullValid hvalid
  simpa [firstMidpointCertificate] using
    (evaluateTargets_coordinate_sound terms hvalid hmid.1 hmid.2).1.1

theorem second_midpoint_value_sound
    (terms : ℕ) {config : Config} {box : CertificateBox}
    {payload : Payload} (hvalid : FullValid terms config box payload) :
    (secondMidpointCertificate terms config box payload).value.Contains
      (targetSecond config box.midpoint) := by
  have hmid := coordinate_midpoint_mem_of_fullValid hvalid
  simpa [secondMidpointCertificate] using
    (evaluateTargets_coordinate_sound terms hvalid hmid.1 hmid.2).2.1.1

theorem third_midpoint_value_sound
    (terms : ℕ) {config : Config} {box : CertificateBox}
    {payload : Payload} (hvalid : FullValid terms config box payload) :
    (thirdMidpointCertificate terms config box payload).value.Contains
      (targetThird config box.midpoint) := by
  have hmid := coordinate_midpoint_mem_of_fullValid hvalid
  simpa [thirdMidpointCertificate] using
    (evaluateTargets_coordinate_sound terms hvalid hmid.1 hmid.2).2.2.1

noncomputable def first_boxDerivativeEnclosures
    (terms : ℕ) {config : Config} {box : CertificateBox}
    {payload : Payload} (hvalid : FullValid terms config box payload) :
    BoxDerivativeEnclosures (targetFirst config) box
      (firstMidpointCertificate terms config box payload) := by
  have hu := (real_u_positive_of_fullValid hvalid).ne'
  refine
    { partialS := fun _ ↦ 0
      partialK := targetFirstPartialK config
      partialChi := targetFirstPartialChi config
      derivS := ?_
      derivK := ?_
      derivChi := ?_
      boundS := ?_
      boundK := ?_
      boundChi := ?_ }
  · intro point _
    exact hasDerivAt_targetFirst_s config point
  · intro point hpoint
    have hp := positive_coordinates_of_fullValid hvalid hpoint
    exact hasDerivAt_targetFirst_k config point hp.1 hp.2 hu
  · intro point hpoint
    have hp := positive_coordinates_of_fullValid hvalid hpoint
    exact hasDerivAt_targetFirst_chi config point hp.1 hp.2 hu
  · intro point hpoint
    simpa [firstMidpointCertificate] using
      (evaluateTargets_sound terms hvalid hpoint).1.2.1
  · intro point hpoint
    simpa [firstMidpointCertificate] using
      (evaluateTargets_sound terms hvalid hpoint).1.2.2.1
  · intro point hpoint
    simpa [firstMidpointCertificate] using
      (evaluateTargets_sound terms hvalid hpoint).1.2.2.2

noncomputable def second_boxDerivativeEnclosures
    (terms : ℕ) {config : Config} {box : CertificateBox}
    {payload : Payload} (hvalid : FullValid terms config box payload) :
    BoxDerivativeEnclosures (targetSecond config) box
      (secondMidpointCertificate terms config box payload) := by
  have hu := (real_u_positive_of_fullValid hvalid).ne'
  refine
    { partialS := fun _ ↦ 0
      partialK := targetSecondPartialK config
      partialChi := targetSecondPartialChi config
      derivS := ?_
      derivK := ?_
      derivChi := ?_
      boundS := ?_
      boundK := ?_
      boundChi := ?_ }
  · intro point _
    exact hasDerivAt_targetSecond_s config point
  · intro point hpoint
    have hp := positive_coordinates_of_fullValid hvalid hpoint
    exact hasDerivAt_targetSecond_k config point hp.1 hp.2 hu
  · intro point hpoint
    have hp := positive_coordinates_of_fullValid hvalid hpoint
    exact hasDerivAt_targetSecond_chi config point hp.1 hp.2 hu
  · intro point hpoint
    simpa [secondMidpointCertificate] using
      (evaluateTargets_sound terms hvalid hpoint).2.1.2.1
  · intro point hpoint
    simpa [secondMidpointCertificate] using
      (evaluateTargets_sound terms hvalid hpoint).2.1.2.2.1
  · intro point hpoint
    simpa [secondMidpointCertificate] using
      (evaluateTargets_sound terms hvalid hpoint).2.1.2.2.2

noncomputable def third_boxDerivativeEnclosures
    (terms : ℕ) {config : Config} {box : CertificateBox}
    {payload : Payload} (hvalid : FullValid terms config box payload) :
    BoxDerivativeEnclosures (targetThird config) box
      (thirdMidpointCertificate terms config box payload) := by
  refine
    { partialS := fun _ ↦ 0
      partialK := targetThirdPartialK config
      partialChi := targetThirdPartialChi config
      derivS := ?_
      derivK := ?_
      derivChi := ?_
      boundS := ?_
      boundK := ?_
      boundChi := ?_ }
  · intro point _
    exact hasDerivAt_targetThird_s config point
  · intro point hpoint
    have hp := positive_coordinates_of_fullValid hvalid hpoint
    exact hasDerivAt_targetThird_k config point hp.1 hp.2
  · intro point hpoint
    have hp := positive_coordinates_of_fullValid hvalid hpoint
    exact hasDerivAt_targetThird_chi config point hp.1 hp.2
  · intro point hpoint
    simpa [thirdMidpointCertificate] using
      (evaluateTargets_sound terms hvalid hpoint).2.2.2.1
  · intro point hpoint
    simpa [thirdMidpointCertificate] using
      (evaluateTargets_sound terms hvalid hpoint).2.2.2.2.1
  · intro point hpoint
    simpa [thirdMidpointCertificate] using
      (evaluateTargets_sound terms hvalid hpoint).2.2.2.2.2

end LRLowKIdealSharedPrimitiveADSoundness
end CourtadeKumar
