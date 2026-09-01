import InformationTheory.CourtadeKumar.LRCompactVCenteredMonotoneLeafCore
import InformationTheory.CourtadeKumar.LRCompactVCenteredMonotoneEvalSound
import InformationTheory.CourtadeKumar.LRCompactVCenteredMonotoneSharedW
import InformationTheory.CourtadeKumar.LRCompactVLambdaCenteredMonotoneConvex
import InformationTheory.CourtadeKumar.LRCompactVLambdaPositiveGroupedReserve

/-!
# Soundness of centered-monotone compact-`V` leaf rows

This module connects the exact Boolean row checker to the analytic reserve
target.  It authenticates the shared fixed-dyadic inputs, reuses the common
endpoint-tight `W_R(1)` proof, interprets the fused observations, and applies
either the monotone-corner or monotone-convex terminal theorem.
-/

set_option autoImplicit false

open Set

namespace CourtadeKumar
namespace LRCompactVCenteredMonotoneLeaf

open LRCompactVFixedDyadic
open LRCompactVCenteredMonotoneEval

private abbrev fixedBits : ℕ := LRCompactVCenteredMonotoneConfig.bits

private theorem commonR_covers_root :
    LRCompactVCenteredMonotoneConfig.rInterval.CoversRatRange fixedBits
      LRCompactVCenteredMonotoneConfig.rootBox.sLo
      LRCompactVCenteredMonotoneConfig.rootBox.sHi := by
  norm_num [NatInterval.CoversRatRange, fixedBits,
    LRCompactVCenteredMonotoneConfig.bits,
    LRCompactVCenteredMonotoneConfig.rInterval,
    LRCompactVCenteredMonotoneConfig.rootBox, decodeNat, scale]

private theorem commonX_covers_root :
    LRCompactVCenteredMonotoneConfig.xInterval.CoversRatRange fixedBits
      LRCompactVCenteredMonotoneConfig.rootBox.chiLo
      LRCompactVCenteredMonotoneConfig.rootBox.chiHi := by
  norm_num [NatInterval.CoversRatRange, fixedBits,
    LRCompactVCenteredMonotoneConfig.bits,
    LRCompactVCenteredMonotoneConfig.xInterval,
    LRCompactVCenteredMonotoneConfig.rootBox, decodeNat, scale]

private theorem rowV_covers_box (row : Row) :
    row.vInterval.CoversRatRange fixedBits row.box.kLo row.box.kHi := by
  simp [NatInterval.CoversRatRange, fixedBits, Row.vInterval, Row.box]

private theorem decode_vRoot_lower :
    decodeNat fixedBits
        LRCompactVCenteredMonotoneConfig.vRootInterval.lower =
      LRCompactVCenteredMonotoneConfig.rootBox.kLo := by
  norm_num [fixedBits, LRCompactVCenteredMonotoneConfig.bits,
    LRCompactVCenteredMonotoneConfig.vRootInterval,
    LRCompactVCenteredMonotoneConfig.rootBox, decodeNat, scale]

private theorem decode_vRoot_upper :
    decodeNat fixedBits
        LRCompactVCenteredMonotoneConfig.vRootInterval.upper =
      LRCompactVCenteredMonotoneConfig.rootBox.kHi := by
  norm_num [fixedBits, LRCompactVCenteredMonotoneConfig.bits,
    LRCompactVCenteredMonotoneConfig.vRootInterval,
    LRCompactVCenteredMonotoneConfig.rootBox, decodeNat, scale]

private theorem decodeNat_sub_real
    {bits left right : ℕ} (h : right ≤ left) :
    (decodeNat bits (left - right) : ℝ) =
      (decodeNat bits left : ℝ) - (decodeNat bits right : ℝ) := by
  have hadd := decodeNat_add_real bits (left - right) right
  rw [Nat.sub_add_cancel h] at hadd
  linarith

private theorem decodeInt_mono
    {bits : ℕ} {left right : ℤ} (h : left ≤ right) :
    (decodeInt bits left : ℝ) ≤ (decodeInt bits right : ℝ) := by
  have hq : decodeInt bits left ≤ decodeInt bits right := by
    unfold decodeInt
    apply (div_le_div_iff_of_pos_right (scale_rat_pos bits)).2
    exact_mod_cast h
  exact_mod_cast hq

private theorem abs_sub_center_le_radius
    {bits lo center hi : ℕ} {x : ℝ}
    (hloCenter : lo ≤ center) (hcenterHi : center ≤ hi)
    (hxLo : (decodeNat bits lo : ℝ) ≤ x)
    (hxHi : x ≤ (decodeNat bits hi : ℝ)) :
    |x - (decodeNat bits center : ℝ)| ≤
      (decodeNat bits (max (center - lo) (hi - center)) : ℝ) := by
  have hleft := IntInterval.decodeNat_mono (bits := bits)
    (Nat.le_max_left (center - lo) (hi - center))
  have hright := IntInterval.decodeNat_mono (bits := bits)
    (Nat.le_max_right (center - lo) (hi - center))
  rw [decodeNat_sub_real hloCenter] at hleft
  rw [decodeNat_sub_real hcenterHi] at hright
  rw [abs_le]
  constructor <;> linarith

private theorem positiveGroupedFinite_nonnegative_of_centered
    {N : ℕ} {lambda R v x : ℝ} (hv : 0 < v)
    (hcentered :
      0 ≤ lrCompactVLambdaCenteredPolynomialFinite N lambda R v x) :
    0 ≤ lrCompactVLambdaPositiveGroupedFinite N lambda R v x := by
  have hfactor : 0 < 1 + v := by linarith
  have hscaled :
      0 ≤ (1 + v) *
        lrCompactVLambdaPositiveGroupedFinite N lambda R v x := by
    rw [lrCompactVLambdaPositiveGroupedFinite_mul_one_add
      hfactor.ne' N lambda R x]
    exact hcentered
  exact (mul_nonneg_iff_of_pos_left hfactor).mp hscaled

private theorem certificateBox_eq_of_fields
    {left right : CertificateBox}
    (hsLo : left.sLo = right.sLo) (hsHi : left.sHi = right.sHi)
    (hkLo : left.kLo = right.kLo) (hkHi : left.kHi = right.kHi)
    (hchiLo : left.chiLo = right.chiLo)
    (hchiHi : left.chiHi = right.chiHi) : left = right := by
  cases left with
  | mk leftSLo leftSHi leftKLo leftKHi leftChiLo leftChiHi =>
      cases right with
      | mk rightSLo rightSHi rightKLo rightKHi rightChiLo rightChiHi =>
          dsimp only at hsLo hsHi hkLo hkHi hchiLo hchiHi
          subst rightSLo
          subst rightSHi
          subst rightKLo
          subst rightKHi
          subst rightChiLo
          subst rightChiHi
          rfl

namespace Row

@[simp] private theorem lambdaValue_sharedInput (row : Row) :
    lambdaValue fixedBits row.sharedInput = (row.lambda : ℝ) := by
  rfl

/-- A checked row range and row-box membership place the point in the common
adjacent root, which authenticates the shared endpoint-kernel enclosure. -/
theorem rootBox_contains_of_rangeCheck
    {row : Row} {point : CertificatePoint}
    (hrange : row.rangeCheck = true) (hpoint : row.box.Contains point) :
    LRCompactVCenteredMonotoneConfig.rootBox.Contains point := by
  have hrange' :
      LRCompactVCenteredMonotoneConfig.vRootInterval.lower ≤ row.vLoNum ∧
      row.vLoNum ≤ row.vHiNum ∧
      row.vHiNum ≤
        LRCompactVCenteredMonotoneConfig.vRootInterval.upper := by
    simpa only [Row.rangeCheck, decide_eq_true_eq] using hrange
  have hkLo :
      (LRCompactVCenteredMonotoneConfig.rootBox.kLo : ℝ) ≤
        (row.box.kLo : ℝ) := by
    have hmono := IntInterval.decodeNat_mono (bits := fixedBits) hrange'.1
    simpa [decode_vRoot_lower, Row.box] using hmono
  have hkHi :
      (row.box.kHi : ℝ) ≤
        (LRCompactVCenteredMonotoneConfig.rootBox.kHi : ℝ) := by
    have hmono := IntInterval.decodeNat_mono (bits := fixedBits) hrange'.2.2
    simpa [decode_vRoot_upper, Row.box] using hmono
  exact ⟨by simpa [Row.box] using hpoint.1,
    by simpa [Row.box] using hpoint.2.1,
    hkLo.trans hpoint.2.2.1,
    hpoint.2.2.2.1.trans hkHi,
    by simpa [Row.box] using hpoint.2.2.2.2.1,
    by simpa [Row.box] using hpoint.2.2.2.2.2⟩

/-- Exact six-field authentication recovers equality with the derived row
box. -/
theorem box_eq_of_boxMatches
    {box : CertificateBox} {row : Row}
    (hmatch : boxMatches box row = true) : box = row.box := by
  have hfields :
      box.sLo = row.box.sLo ∧ box.sHi = row.box.sHi ∧
      box.kLo = row.box.kLo ∧ box.kHi = row.box.kHi ∧
      box.chiLo = row.box.chiLo ∧ box.chiHi = row.box.chiHi := by
    simpa only [boxMatches, decide_eq_true_eq] using hmatch
  rcases hfields with ⟨hsLo, hsHi, hkLo, hkHi, hchiLo, hchiHi⟩
  exact certificateBox_eq_of_fields hsLo hsHi hkLo hkHi hchiLo hchiHi

/-- A successful centered-monotone row proves the analytic reserve target
throughout its derived rational box. -/
theorem sound
    (logTerms halfLogTerms dTerms : ℕ) {row : Row}
    (hcheck : row.check logTerms halfLogTerms dTerms = true) :
    ∀ point, row.box.Contains point → LRCompactVPhysical point →
      0 ≤ lrCompactVReserveTarget point := by
  have hcheckParts :
      row.rangeCheck = true ∧
      row.sameYCheck logTerms halfLogTerms dTerms = true ∧
      (match row.geometry with
        | .corner => row.cornerCheck
        | .tangent centerNum => row.tangentCheck centerNum) = true := by
    simpa only [Row.check, Bool.and_eq_true, and_assoc] using hcheck
  have hsameY :
      row.logOnePlusVHi.check (1 + row.box.kHi) = true ∧
      LRCompactVDirectDValid.check row.box = true ∧
      row.lambda * (row.bEndpoint logTerms halfLogTerms).upper ≤
        (row.dEnclosure dTerms).nonnegativeLower ∧
      row.lambda * row.box.sHi *
          (1 - lrCompactVDirectDYLoQ row.box) ≤ 1 - row.box.sHi := by
    simpa only [Row.sameYCheck, decide_eq_true_eq] using hcheckParts.2.1
  have hrangeNat :
      LRCompactVCenteredMonotoneConfig.vRootInterval.lower ≤ row.vLoNum ∧
      row.vLoNum ≤ row.vHiNum ∧
      row.vHiNum ≤
        LRCompactVCenteredMonotoneConfig.vRootInterval.upper := by
    simpa only [Row.rangeCheck, decide_eq_true_eq] using hcheckParts.1
  have hvalid : LRCompactVDirectDValid row.box :=
    LRCompactVDirectDValid.of_check hsameY.2.1
  have hlambdaQ : (0 : ℚ) ≤ row.lambda := by
    simpa only [Row.lambda] using
      decodeNat_nonnegative fixedBits row.lambdaNum
  intro point hpoint hphysical
  have hinterior := hphysical.1
  have hroot := rootBox_contains_of_rangeCheck hcheckParts.1 hpoint
  have hR : row.sharedInput.r.Contains fixedBits point.s := by
    apply NatInterval.contains_of_coversRatRange
      (lo := row.box.sLo) (hi := row.box.sHi)
    · simpa [Row.sharedInput, Row.box] using commonR_covers_root
    · exact hpoint.1
    · exact hpoint.2.1
  have hRunit : point.s ∈ Icc (0 : ℝ) 1 :=
    ⟨hinterior.1.1.le, hinterior.1.2.le⟩
  have hw : row.sharedInput.wOne.Contains fixedBits
      (lrWKernel point.s 1) := by
    simpa [Row.sharedInput, fixedBits] using
      LRCompactVCenteredMonotoneSharedW.sharedWSeed_contains
        hroot hinterior
  have hxPoint : LRCompactVCenteredMonotoneConfig.xInterval.Contains
      fixedBits point.chi := by
    apply NatInterval.contains_of_coversRatRange
      (lo := row.box.chiLo) (hi := row.box.chiHi)
    · simpa [Row.box] using commonX_covers_root
    · exact hpoint.2.2.2.2.1
    · exact hpoint.2.2.2.2.2
  have hvPoint : row.vInterval.Contains fixedBits point.k := by
    exact NatInterval.contains_of_coversRatRange (rowV_covers_box row)
      hpoint.2.2.1 hpoint.2.2.2.1
  have hlambdaReal : (0 : ℝ) ≤ (row.lambda : ℝ) := by
    exact_mod_cast hlambdaQ
  have hlambdaB :
      (row.lambda : ℝ) *
          lrFlowB point.s point.k (Real.sqrt point.chi) ≤
        lrFlowD point.s point.k (Real.sqrt point.chi) := by
    apply lrCompactVSameYCheckedLambda_mul_flowB_le_flowD
      logTerms halfLogTerms dTerms row.lambda hvalid hpoint hinterior hlambdaQ
      hsameY.1
    · simpa only [Row.bEndpoint, Row.dEnclosure] using hsameY.2.2.1
    · exact hsameY.2.2.2
  let vHi : ℝ := (decodeNat fixedBits row.vHiNum : ℝ)
  let xLo : ℝ :=
    (decodeNat fixedBits
      LRCompactVCenteredMonotoneConfig.xInterval.lower : ℝ)
  let xHi : ℝ :=
    (decodeNat fixedBits
      LRCompactVCenteredMonotoneConfig.xInterval.upper : ℝ)
  have hv : point.k ≤ vHi := by
    simpa [vHi, Row.box] using hpoint.2.2.2.1
  have hvHi0 : 0 ≤ vHi := by
    exact decodeNat_real_nonnegative fixedBits row.vHiNum
  have hvHi1 : vHi ≤ 1 := by
    have hle : row.vHiNum ≤ scale fixedBits :=
      hrangeNat.2.2.trans (by
        norm_num [fixedBits, LRCompactVCenteredMonotoneConfig.bits,
          LRCompactVCenteredMonotoneConfig.vRootInterval, scale])
    exact (IntInterval.decodeNat_mono (bits := fixedBits) hle).trans_eq
      (decodeNat_scale_real fixedBits)
  have hxLo0 : 0 ≤ xLo := by
    exact decodeNat_real_nonnegative fixedBits _
  have hxHi0 : 0 ≤ xHi := by
    exact decodeNat_real_nonnegative fixedBits _
  have hxHi1 : xHi ≤ 1 := by
    norm_num [xHi, fixedBits, LRCompactVCenteredMonotoneConfig.bits,
      LRCompactVCenteredMonotoneConfig.xInterval, decodeNat, scale]
  have hvPoint0 : 0 ≤ point.k := hinterior.2.1.1.le
  have hvPoint1 : point.k ≤ 1 := hinterior.2.1.2.le
  have hxPoint0 : 0 ≤ point.chi := hinterior.2.2.1.le
  have hxPoint1 : point.chi ≤ 1 := hinterior.2.2.2.le
  have finish :
      0 ≤ lrCompactVLambdaCenteredPolynomialFinite row.head.terms
          (row.lambda : ℝ) point.s point.k point.chi →
        0 ≤ lrCompactVReserveTarget point := by
    intro hcentered
    have hfinite := positiveGroupedFinite_nonnegative_of_centered
      hinterior.2.1.1 hcentered
    exact lrCompactVReserveTarget_nonneg_of_positiveGroupedFinite
      hphysical hlambdaReal row.head.terms hfinite hlambdaB
  cases hgeometry : row.geometry with
  | corner =>
      have hterminal :
          0 ≤ row.cornerObservation.valueLower ∧
          row.cornerObservation.vDerivativeUpper ≤ 0 ∧
          row.cornerObservation.xDerivativeUpper ≤ 0 := by
        simpa only [hgeometry, Row.cornerCheck, decide_eq_true_eq] using
          hcheckParts.2.2
      have hvTop : row.cornerInput.vHi.Contains fixedBits vHi := by
        simpa [Row.cornerInput, vHi] using
          NatInterval.point_contains fixedBits row.vHiNum
      have hxTop : row.cornerInput.xHi.Contains fixedBits xHi := by
        simpa [Row.cornerInput, xHi] using NatInterval.point_contains
          fixedBits LRCompactVCenteredMonotoneConfig.xInterval.upper
      have hvalueOutput := evalMonotoneCorner_sound
        (bits := fixedBits) (terms := row.head.terms)
        (input := row.cornerInput) (R := point.s) (vTop := vHi)
        (xTop := xHi) (vFull := point.k) (xFull := point.chi)
        hR hRunit hw hvTop hvHi0 hvHi1 hxTop hxHi0 hxHi1
        hvPoint hvPoint0 hvPoint1 hxPoint hxPoint0 hxPoint1
      let lower : ℝ :=
        (decodeInt fixedBits row.cornerObservation.valueLower : ℝ)
      have hlower0 : 0 ≤ lower := by
        exact decodeInt_real_nonnegative_of_nonnegative fixedBits hterminal.1
      have hvalue :
          lower ≤ lrCompactVLambdaCenteredPolynomialFinite row.head.terms
            (row.lambda : ℝ) point.s vHi xHi := by
        simpa [lower, Row.cornerObservation, observeMonotoneCorner,
          Row.cornerInput] using hvalueOutput.valueLower_le
      have hPv : ∀ qv ∈ Icc point.k vHi,
          lrCompactVLambdaCenteredPolynomialV row.head.terms
            (row.lambda : ℝ) point.s qv point.chi ≤ 0 := by
        intro qv hqv
        have hqvContains : row.cornerInput.vFull.Contains fixedBits qv := by
          apply NatInterval.contains_of_coversRatRange
            (lo := row.box.kLo) (hi := row.box.kHi)
          · simpa [Row.cornerInput] using rowV_covers_box row
          · exact hpoint.2.2.1.trans hqv.1
          · simpa [vHi, Row.box] using hqv.2
        have hqv0 : 0 ≤ qv := hvPoint0.trans hqv.1
        have hqv1 : qv ≤ 1 := hqv.2.trans hvHi1
        have houtput := evalMonotoneCorner_sound
          (bits := fixedBits) (terms := row.head.terms)
          (input := row.cornerInput) (R := point.s) (vTop := vHi)
          (xTop := xHi) (vFull := qv) (xFull := point.chi)
          hR hRunit hw hvTop hvHi0 hvHi1 hxTop hxHi0 hxHi1
          hqvContains hqv0 hqv1 hxPoint hxPoint0 hxPoint1
        have hupper := houtput.vDerivative_le_upper
        have hupper0 := decodeInt_real_nonpositive_of_nonpositive fixedBits
          hterminal.2.1
        have hupper' :
            lrCompactVLambdaCenteredPolynomialV row.head.terms
                (row.lambda : ℝ) point.s qv point.chi ≤
              (decodeInt fixedBits
                row.cornerObservation.vDerivativeUpper : ℝ) := by
          simpa [Row.cornerObservation, observeMonotoneCorner,
            Row.cornerInput] using hupper
        exact hupper'.trans hupper0
      have hPx : ∀ qx ∈ Icc point.chi xHi,
          lrCompactVLambdaCenteredPolynomialX row.head.terms
            (row.lambda : ℝ) point.s vHi qx ≤ 0 := by
        intro qx hqx
        have hqxContains : row.cornerInput.xFull.Contains fixedBits qx := by
          constructor
          · exact hxPoint.1.trans hqx.1
          · simpa [Row.cornerInput, xHi] using hqx.2
        have hqx0 : 0 ≤ qx := hxPoint0.trans hqx.1
        have hqx1 : qx ≤ 1 := hqx.2.trans hxHi1
        have houtput := evalMonotoneCorner_sound
          (bits := fixedBits) (terms := row.head.terms)
          (input := row.cornerInput) (R := point.s) (vTop := vHi)
          (xTop := xHi) (vFull := point.k) (xFull := qx)
          hR hRunit hw hvTop hvHi0 hvHi1 hxTop hxHi0 hxHi1
          hvPoint hvPoint0 hvPoint1 hqxContains hqx0 hqx1
        have hupper := houtput.xDerivative_le_upper
        have hupper0 := decodeInt_real_nonpositive_of_nonpositive fixedBits
          hterminal.2.2
        have hupper' :
            lrCompactVLambdaCenteredPolynomialX row.head.terms
                (row.lambda : ℝ) point.s vHi qx ≤
              (decodeInt fixedBits
                row.cornerObservation.xDerivativeUpper : ℝ) := by
          simpa [Row.cornerObservation, observeMonotoneCorner,
            Row.cornerInput] using hupper
        exact hupper'.trans hupper0
      have hbound :=
        lrCompactVLambdaCenteredPolynomialFinite_monotone_corner_lower
          row.head.terms (row.lambda : ℝ) point.s point.k vHi
          point.chi xHi lower hv hxPoint.2 hvalue hPv hPx
      exact finish (hlower0.trans hbound)
  | tangent centerNum =>
      have hterminal :
          LRCompactVCenteredMonotoneConfig.xInterval.lower ≤ centerNum ∧
          centerNum ≤ LRCompactVCenteredMonotoneConfig.xInterval.upper ∧
          (row.tangentObservation centerNum).vDerivativeUpper ≤ 0 ∧
          0 ≤ (row.tangentObservation centerNum).xSecondDerivativeLower ∧
          Int.ofNat (mulUp fixedBits
              (row.tangentObservation centerNum).xGradientMaxAbs
              (Row.tangentRadiusNum centerNum)) ≤
            (row.tangentObservation centerNum).valueLower := by
        simpa only [hgeometry, Row.tangentCheck, fixedBits,
          decide_eq_true_eq] using hcheckParts.2.2
      let xCenter : ℝ := (decodeNat fixedBits centerNum : ℝ)
      let xRadius : ℝ :=
        (decodeNat fixedBits (Row.tangentRadiusNum centerNum) : ℝ)
      have hcenter : xCenter ∈ Icc xLo xHi := by
        constructor
        · simpa [xLo, xCenter] using
            IntInterval.decodeNat_mono (bits := fixedBits) hterminal.1
        · simpa [xCenter, xHi] using
            IntInterval.decodeNat_mono (bits := fixedBits) hterminal.2.1
      have hx : point.chi ∈ Icc xLo xHi := by
        simpa [xLo, xHi, NatInterval.Contains, NatInterval.decode,
          RationalEnclosure.Contains] using hxPoint
      have hdelta : |point.chi - xCenter| ≤ xRadius := by
        simpa [xCenter, xRadius, Row.tangentRadiusNum] using
          abs_sub_center_le_radius hterminal.1 hterminal.2.1
            hxPoint.1 hxPoint.2
      have hvTop : (row.tangentInput centerNum).vHi.Contains
          fixedBits vHi := by
        simpa [Row.tangentInput, vHi] using
          NatInterval.point_contains fixedBits row.vHiNum
      have hxCenterContains :
          (row.tangentInput centerNum).xCenter.Contains fixedBits xCenter := by
        simpa [Row.tangentInput, xCenter] using
          NatInterval.point_contains fixedBits centerNum
      have hxCenter0 : 0 ≤ xCenter :=
        decodeNat_real_nonnegative fixedBits centerNum
      have hxCenter1 : xCenter ≤ 1 := hcenter.2.trans hxHi1
      have hvalueOutput := evalMonotoneTangent_sound
        (bits := fixedBits) (terms := row.head.terms)
        (input := row.tangentInput centerNum) (R := point.s) (vTop := vHi)
        (xCenter := xCenter) (vFull := point.k) (xFull := point.chi)
        hR hRunit hw hvTop hvHi0 hvHi1
        hxCenterContains hxCenter0 hxCenter1
        hvPoint hvPoint0 hvPoint1 hxPoint hxPoint0 hxPoint1
      let lower : ℝ :=
        (decodeInt fixedBits
          (row.tangentObservation centerNum).valueLower : ℝ)
      let gradientRadius : ℝ :=
        (decodeNat fixedBits
          (row.tangentObservation centerNum).xGradientMaxAbs : ℝ)
      have hgradientRadius : 0 ≤ gradientRadius :=
        decodeNat_real_nonnegative fixedBits _
      have hvalue :
          lower ≤ lrCompactVLambdaCenteredPolynomialFinite row.head.terms
            (row.lambda : ℝ) point.s vHi xCenter := by
        simpa [lower, Row.tangentObservation, observeMonotoneTangent,
          Row.tangentInput] using hvalueOutput.valueLower_le
      have hgradient :
          |lrCompactVLambdaCenteredPolynomialX row.head.terms
              (row.lambda : ℝ) point.s vHi xCenter| ≤ gradientRadius := by
        simpa [gradientRadius, Row.tangentObservation,
          observeMonotoneTangent, Row.tangentInput] using
          hvalueOutput.xGradient_abs_le
      have hPv : ∀ qv ∈ Icc point.k vHi,
          lrCompactVLambdaCenteredPolynomialV row.head.terms
            (row.lambda : ℝ) point.s qv point.chi ≤ 0 := by
        intro qv hqv
        have hqvContains :
            (row.tangentInput centerNum).vFull.Contains fixedBits qv := by
          apply NatInterval.contains_of_coversRatRange
            (lo := row.box.kLo) (hi := row.box.kHi)
          · simpa [Row.tangentInput] using rowV_covers_box row
          · exact hpoint.2.2.1.trans hqv.1
          · simpa [vHi, Row.box] using hqv.2
        have hqv0 : 0 ≤ qv := hvPoint0.trans hqv.1
        have hqv1 : qv ≤ 1 := hqv.2.trans hvHi1
        have houtput := evalMonotoneTangent_sound
          (bits := fixedBits) (terms := row.head.terms)
          (input := row.tangentInput centerNum) (R := point.s)
          (vTop := vHi) (xCenter := xCenter) (vFull := qv)
          (xFull := point.chi) hR hRunit hw hvTop hvHi0 hvHi1
          hxCenterContains hxCenter0 hxCenter1 hqvContains hqv0 hqv1
          hxPoint hxPoint0 hxPoint1
        have hupper := houtput.vDerivative_le_upper
        have hupper0 := decodeInt_real_nonpositive_of_nonpositive fixedBits
          hterminal.2.2.1
        have hupper' :
            lrCompactVLambdaCenteredPolynomialV row.head.terms
                (row.lambda : ℝ) point.s qv point.chi ≤
              (decodeInt fixedBits
                (row.tangentObservation centerNum).vDerivativeUpper : ℝ) := by
          simpa [Row.tangentObservation, observeMonotoneTangent,
            Row.tangentInput] using hupper
        exact hupper'.trans hupper0
      have hPxx : ∀ qx ∈ Icc xLo xHi,
          0 ≤ lrCompactVLambdaCenteredPolynomialXX row.head.terms
            (row.lambda : ℝ) point.s vHi qx := by
        intro qx hqx
        have hqxContains :
            (row.tangentInput centerNum).xFull.Contains fixedBits qx := by
          simpa [Row.tangentInput, xLo, xHi, NatInterval.Contains,
            NatInterval.decode, RationalEnclosure.Contains] using hqx
        have hqx0 : 0 ≤ qx := hxLo0.trans hqx.1
        have hqx1 : qx ≤ 1 := hqx.2.trans hxHi1
        have houtput := evalMonotoneTangent_sound
          (bits := fixedBits) (terms := row.head.terms)
          (input := row.tangentInput centerNum) (R := point.s)
          (vTop := vHi) (xCenter := xCenter) (vFull := point.k)
          (xFull := qx) hR hRunit hw hvTop hvHi0 hvHi1
          hxCenterContains hxCenter0 hxCenter1 hvPoint hvPoint0 hvPoint1
          hqxContains hqx0 hqx1
        have hlower := houtput.xSecondDerivativeLower_le
        have hlower0 := decodeInt_real_nonnegative_of_nonnegative fixedBits
          hterminal.2.2.2.1
        exact hlower0.trans (by
          simpa [Row.tangentObservation, observeMonotoneTangent,
            Row.tangentInput] using hlower)
      have hmulQ := decodeNat_le_mulUp fixedBits
        (row.tangentObservation centerNum).xGradientMaxAbs
        (Row.tangentRadiusNum centerNum)
      have hmul : gradientRadius * xRadius ≤
          (decodeNat fixedBits
            (mulUp fixedBits
              (row.tangentObservation centerNum).xGradientMaxAbs
              (Row.tangentRadiusNum centerNum)) : ℝ) := by
        have hmulReal :
            (decodeNat fixedBits
                (row.tangentObservation centerNum).xGradientMaxAbs : ℝ) *
                (decodeNat fixedBits
                  (Row.tangentRadiusNum centerNum) : ℝ) ≤
              (decodeNat fixedBits
                (mulUp fixedBits
                  (row.tangentObservation centerNum).xGradientMaxAbs
                  (Row.tangentRadiusNum centerNum)) : ℝ) := by
          exact_mod_cast hmulQ
        simpa [gradientRadius, xRadius] using hmulReal
      have hrounded :
          (decodeNat fixedBits
              (mulUp fixedBits
                (row.tangentObservation centerNum).xGradientMaxAbs
                (Row.tangentRadiusNum centerNum)) : ℝ) ≤ lower := by
        have hmono := decodeInt_mono (bits := fixedBits)
          hterminal.2.2.2.2
        simpa [lower] using hmono
      have hlowerNonnegative : 0 ≤ lower - gradientRadius * xRadius := by
        linarith
      have hbound :=
        lrCompactVLambdaCenteredPolynomialFinite_monotone_convex_lower
          row.head.terms (row.lambda : ℝ) point.s point.k vHi
          xLo xCenter point.chi xHi lower gradientRadius xRadius
          hv hcenter hx hgradientRadius hdelta hvalue hgradient hPv hPxx
      exact finish (hlowerNonnegative.trans hbound)

/-- Soundness adapter for the external subdivision box accepted by
`Row.checkAt`. -/
theorem soundAt
    (logTerms halfLogTerms dTerms : ℕ)
    {box : CertificateBox} {row : Row}
    (hcheck : checkAt logTerms halfLogTerms dTerms box row = true) :
    ∀ point, box.Contains point → LRCompactVPhysical point →
      0 ≤ lrCompactVReserveTarget point := by
  have hparts : boxMatches box row = true ∧
      row.check logTerms halfLogTerms dTerms = true := by
    simpa only [checkAt, Bool.and_eq_true] using hcheck
  have hbox := box_eq_of_boxMatches hparts.1
  intro point hpoint hphysical
  apply sound logTerms halfLogTerms dTerms hparts.2 point
  · simpa only [hbox] using hpoint
  · exact hphysical

end Row
end LRCompactVCenteredMonotoneLeaf
end CourtadeKumar
