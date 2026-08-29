import InformationTheory.CourtadeKumar.LRDeterminantUpperKHistoricalACAD
import InformationTheory.CourtadeKumar.LRDeterminantUpperKHistoricalACValues
import InformationTheory.CourtadeKumar.LRDeterminantUpperKHistoricalThreeCoordinateBase

/-!
# Semantic assembly for the historical upper-`K` evaluator

This file isolates the final, purely compositional layer of the sharp
historical evaluator.  It deliberately does not prove any of the analytic
facts behind the four `A/C` nodes.  Instead, those facts enter through
ordinary `IntervalAD.Contains` hypotheses.

The arithmetic association is exactly the audited one

`B * (base / e) + D1 * (psi / e)`.

In particular, it is not replaced by the generally wider interval expression
`(B * base + D1 * psi) / e`.  Every result below is proved from the kernel
closure lemmas for interval addition, multiplication, and positive division.
-/

namespace CourtadeKumar
namespace LRUpperKHistoricalEvaluatorAssembly

open LRUpperKReplayCertificate
open LRUpperKHistoricalACAD
open LRUpperKHistoricalACValues
open LRUpperKHistoricalThreeCoordinateBase

/-! ## Exact real three-jets and their interval semantics -/

/-- A value and its three first partial derivatives in the `(s,K,h)` chart. -/
@[ext] structure Jet3 where
  value : ℝ
  derivS : ℝ
  derivK : ℝ
  derivH : ℝ

namespace Jet3

def add (a b : Jet3) : Jet3 where
  value := a.value + b.value
  derivS := a.derivS + b.derivS
  derivK := a.derivK + b.derivK
  derivH := a.derivH + b.derivH

def mul (a b : Jet3) : Jet3 where
  value := a.value * b.value
  derivS := a.derivS * b.value + a.value * b.derivS
  derivK := a.derivK * b.value + a.value * b.derivK
  derivH := a.derivH * b.value + a.value * b.derivH

noncomputable def div (a b : Jet3) : Jet3 where
  value := a.value / b.value
  derivS := (a.derivS * b.value - a.value * b.derivS) / b.value ^ 2
  derivK := (a.derivK * b.value - a.value * b.derivK) / b.value ^ 2
  derivH := (a.derivH * b.value - a.value * b.derivH) / b.value ^ 2

end Jet3

/-- The semantic bridge from executable rational interval AD to a real jet. -/
def Encloses (node : IntervalAD) (jet : Jet3) : Prop :=
  node.Contains jet.value jet.derivS jet.derivK jet.derivH

theorem encloses_add {a b : IntervalAD} {x y : Jet3}
    (ha : Encloses a x) (hb : Encloses b y) :
    Encloses (IntervalAD.add a b) (Jet3.add x y) := by
  simpa [Encloses, Jet3.add] using IntervalAD.contains_add ha hb

theorem encloses_mul {a b : IntervalAD} {x y : Jet3}
    (ha : Encloses a x) (hb : Encloses b y) :
    Encloses (IntervalAD.mul a b) (Jet3.mul x y) := by
  simpa [Encloses, Jet3.mul] using IntervalAD.contains_mul ha hb

theorem encloses_divPositive {a b : IntervalAD} {x y : Jet3}
    (hbPositive : (0 : ℚ) < b.value.lower)
    (ha : Encloses a x) (hb : Encloses b y) :
    Encloses (IntervalAD.divPositive a b) (Jet3.div x y) := by
  simpa [Encloses, Jet3.div] using
    IntervalAD.contains_divPositive hbPositive ha hb

/-! ## The exact historical association -/

/-- The interval expression used by the audited replay. -/
def historicalAssociationAD
    (b base d1 psi e : IntervalAD) : IntervalAD :=
  IntervalAD.add
    (IntervalAD.mul b (IntervalAD.divPositive base e))
    (IntervalAD.mul d1 (IntervalAD.divPositive psi e))

/-- The corresponding exact real jet. -/
noncomputable def historicalAssociationJet
    (b base d1 psi e : Jet3) : Jet3 :=
  Jet3.add
    (Jet3.mul b (Jet3.div base e))
    (Jet3.mul d1 (Jet3.div psi e))

/-- Kernel-only soundness of the exact audited association, simultaneously
for the value and all three chart derivatives. -/
theorem historicalAssociationAD_sound
    {b base d1 psi e : IntervalAD}
    {bJet baseJet d1Jet psiJet eJet : Jet3}
    (hePositive : (0 : ℚ) < e.value.lower)
    (hb : Encloses b bJet)
    (hbase : Encloses base baseJet)
    (hd1 : Encloses d1 d1Jet)
    (hpsi : Encloses psi psiJet)
    (he : Encloses e eJet) :
    Encloses (historicalAssociationAD b base d1 psi e)
      (historicalAssociationJet bJet baseJet d1Jet psiJet eJet) := by
  have hbaseOver := encloses_divPositive hePositive hbase he
  have hpsiOver := encloses_divPositive hePositive hpsi he
  have hleft := encloses_mul hb hbaseOver
  have hright := encloses_mul hd1 hpsiOver
  simpa [historicalAssociationAD, historicalAssociationJet] using
    encloses_add hleft hright

/-! ## Executable sharp historical nodes -/

/-- Historical `A(y0)` node: monotone-corner value plus sharp derivatives. -/
def aY0HistoricalAD (terms : ℕ) (box : CertificateBox)
    (payload : LRUpperKHistoricalACAD.Payload) : IntervalAD :=
  let partials := aY0Partials terms box payload
  { value := aCornerI terms 40 48 box (y0AD box).value
    derivS := partials.derivS
    derivK := partials.derivK
    derivChi := partials.derivH }

/-- Historical `C(y0)` node: monotone-corner value plus sharp derivatives. -/
def cY0HistoricalAD (terms : ℕ) (box : CertificateBox)
    (payload : LRUpperKHistoricalACAD.Payload) : IntervalAD :=
  let partials := cY0Partials terms box payload
  { value := cCornerI terms 40 48 box (y0AD box).value
    derivS := partials.derivS
    derivK := partials.derivK
    derivChi := partials.derivH }

/-- Historical `A(e)` node. -/
def aEHistoricalAD (terms : ℕ) (box : CertificateBox)
    (payload : LRUpperKHistoricalACAD.Payload) : IntervalAD :=
  let partials := aEPartials terms box payload
  { value := aCornerI terms 40 48 box (eAD box).value
    derivS := partials.derivS
    derivK := partials.derivK
    derivChi := partials.derivH }

/-- Historical `C(e)` node. -/
def cEHistoricalAD (terms : ℕ) (box : CertificateBox)
    (payload : LRUpperKHistoricalACAD.Payload) : IntervalAD :=
  let partials := cEPartials terms box payload
  { value := cCornerI terms 40 48 box (eAD box).value
    derivS := partials.derivS
    derivK := partials.derivK
    derivChi := partials.derivH }

/-- Cancellation-aware historical `Psi`. -/
def psiAD (terms : ℕ) (box : CertificateBox)
    (payload : LRUpperKHistoricalACAD.Payload) : IntervalAD :=
  IntervalAD.add
    (IntervalAD.add
      (payload.base.g0.evaluate terms (vAD box payload.base))
      (aY0HistoricalAD terms box payload))
    (IntervalAD.add
      (IntervalAD.divPositive (aEHistoricalAD terms box payload)
        (vAD box payload.base))
      (IntervalAD.mul (kappaAD box payload.base)
        (wAD terms box payload.base)))

/-- Cancellation-aware historical
`Psi - G + 4*delta*W` (called `base` by the audited checker). -/
def baseAD (terms : ℕ) (box : CertificateBox)
    (payload : LRUpperKHistoricalACAD.Payload) : IntervalAD :=
  IntervalAD.add
    (IntervalAD.add (cY0HistoricalAD terms box payload)
      (IntervalAD.divPositive (cEHistoricalAD terms box payload)
        (vAD box payload.base)))
    (IntervalAD.mul
      (IntervalAD.add (kappaAD box payload.base)
        (IntervalAD.mul (IntervalAD.const 4)
          (deltaAD box payload.base)))
      (wAD terms box payload.base))

/-- Final historical evaluator, retaining the audited division association. -/
def evaluateAD (terms : ℕ) (box : CertificateBox)
    (payload : LRUpperKHistoricalACAD.Payload) : IntervalAD :=
  historicalAssociationAD
    (bFlowAD terms box payload.base)
    (baseAD terms box payload)
    (d1AD terms box payload.base)
    (psiAD terms box payload)
    (eAD box)

/-! ## Real-jet mirror of the sharp construction -/

noncomputable def psiJet
    (g0 aY0 aE v kappa w : Jet3) : Jet3 :=
  Jet3.add (Jet3.add g0 aY0)
    (Jet3.add (Jet3.div aE v) (Jet3.mul kappa w))

noncomputable def baseJet
    (cY0 cE v kappa delta w : Jet3) : Jet3 :=
  Jet3.add (Jet3.add cY0 (Jet3.div cE v))
    (Jet3.mul (Jet3.add kappa
      (Jet3.mul
        { value := 4, derivS := 0, derivK := 0, derivH := 0 }
        delta)) w)

noncomputable def evaluateJet
    (b d1 g0 aY0 aE cY0 cE v kappa delta w e : Jet3) : Jet3 :=
  historicalAssociationJet b (baseJet cY0 cE v kappa delta w) d1
    (psiJet g0 aY0 aE v kappa w) e

theorem psiAD_sound_of_nodes (terms : ℕ)
    {box : CertificateBox}
    {payload : LRUpperKHistoricalACAD.Payload}
    {g0Jet aY0Jet aEJet vJet kappaJet wJet : Jet3}
    (hvPositive : (0 : ℚ) < (vAD box payload.base).value.lower)
    (hg0 : Encloses
      (payload.base.g0.evaluate terms (vAD box payload.base)) g0Jet)
    (haY0 : Encloses (aY0HistoricalAD terms box payload) aY0Jet)
    (haE : Encloses (aEHistoricalAD terms box payload) aEJet)
    (hv : Encloses (vAD box payload.base) vJet)
    (hkappa : Encloses (kappaAD box payload.base) kappaJet)
    (hw : Encloses (wAD terms box payload.base) wJet) :
    Encloses (psiAD terms box payload)
      (psiJet g0Jet aY0Jet aEJet vJet kappaJet wJet) := by
  have haEOver := encloses_divPositive hvPositive haE hv
  have hkappaW := encloses_mul hkappa hw
  have hleft := encloses_add hg0 haY0
  have hright := encloses_add haEOver hkappaW
  simpa [psiAD, psiJet] using encloses_add hleft hright

theorem baseAD_sound_of_nodes (terms : ℕ)
    {box : CertificateBox}
    {payload : LRUpperKHistoricalACAD.Payload}
    {cY0Jet cEJet vJet kappaJet deltaJet wJet : Jet3}
    (hvPositive : (0 : ℚ) < (vAD box payload.base).value.lower)
    (hcY0 : Encloses (cY0HistoricalAD terms box payload) cY0Jet)
    (hcE : Encloses (cEHistoricalAD terms box payload) cEJet)
    (hv : Encloses (vAD box payload.base) vJet)
    (hkappa : Encloses (kappaAD box payload.base) kappaJet)
    (hdelta : Encloses (deltaAD box payload.base) deltaJet)
    (hw : Encloses (wAD terms box payload.base) wJet) :
    Encloses (baseAD terms box payload)
      (baseJet cY0Jet cEJet vJet kappaJet deltaJet wJet) := by
  let fourJet : Jet3 :=
    { value := 4, derivS := 0, derivK := 0, derivH := 0 }
  have hfour : Encloses (IntervalAD.const 4) fourJet := by
    simpa [Encloses, fourJet] using IntervalAD.contains_const 4
  have hcEOver := encloses_divPositive hvPositive hcE hv
  have hkapPlusDelta := encloses_add hkappa (encloses_mul hfour hdelta)
  have hweighted := encloses_mul hkapPlusDelta hw
  have hleft := encloses_add hcY0 hcEOver
  simpa [baseAD, baseJet, fourJet] using encloses_add hleft hweighted

/-- The principal integration theorem.  Its only assumptions about the four
new sharp nodes are the four displayed `Encloses` facts.  All other inputs
are the ordinary component facts already proved internally while establishing
`LRUpperKReplayCertificate.sharpEvaluateSKAD_sound`.

The conclusion covers the value and all three derivatives in one statement. -/
theorem evaluateAD_sound_of_sharp_nodes (terms : ℕ)
    {box : CertificateBox}
    {payload : LRUpperKHistoricalACAD.Payload}
    {bJet d1Jet g0Jet aY0Jet aEJet cY0Jet cEJet vJet
      kappaJet deltaJet wJet eJet : Jet3}
    (hvPositive : (0 : ℚ) < (vAD box payload.base).value.lower)
    (hePositive : (0 : ℚ) < (eAD box).value.lower)
    (hb : Encloses (bFlowAD terms box payload.base) bJet)
    (hd1 : Encloses (d1AD terms box payload.base) d1Jet)
    (hg0 : Encloses
      (payload.base.g0.evaluate terms (vAD box payload.base)) g0Jet)
    (haY0 : Encloses (aY0HistoricalAD terms box payload) aY0Jet)
    (haE : Encloses (aEHistoricalAD terms box payload) aEJet)
    (hcY0 : Encloses (cY0HistoricalAD terms box payload) cY0Jet)
    (hcE : Encloses (cEHistoricalAD terms box payload) cEJet)
    (hv : Encloses (vAD box payload.base) vJet)
    (hkappa : Encloses (kappaAD box payload.base) kappaJet)
    (hdelta : Encloses (deltaAD box payload.base) deltaJet)
    (hw : Encloses (wAD terms box payload.base) wJet)
    (he : Encloses (eAD box) eJet) :
    Encloses (evaluateAD terms box payload)
      (evaluateJet bJet d1Jet g0Jet aY0Jet aEJet cY0Jet cEJet
        vJet kappaJet deltaJet wJet eJet) := by
  have hpsi := psiAD_sound_of_nodes terms hvPositive
    hg0 haY0 haE hv hkappa hw
  have hbase := baseAD_sound_of_nodes terms hvPositive
    hcY0 hcE hv hkappa hdelta hw
  have hresult := historicalAssociationAD_sound hePositive
    hb hbase hd1 hpsi he
  simpa [evaluateAD, evaluateJet] using hresult

/-! ## Adapter to the genuine CK target -/

/-- The desired value and three genuine chart derivatives at a point. -/
noncomputable def upperKTargetJet (coordinate : CertificatePoint) : Jet3 where
  value := lrFiniteDeterminantUpperKReplayTarget
    (lrDeterminantKChartDecode coordinate)
  derivS := targetChartDerivS coordinate
  derivK := targetChartDerivK coordinate
  derivH := targetChartDerivH coordinate

/-- Once the real-jet algebra is identified with `upperKTargetJet`, the
compositional enclosure immediately becomes the exact semantic statement
needed by the three-coordinate midpoint theorem. -/
theorem contains_upperKTarget_of_encloses
    {node : IntervalAD} {jet : Jet3} {coordinate : CertificatePoint}
    (hnode : Encloses node jet)
    (hjet : jet = upperKTargetJet coordinate) :
    node.Contains
      (lrFiniteDeterminantUpperKReplayTarget
        (lrDeterminantKChartDecode coordinate))
      (targetChartDerivS coordinate)
      (targetChartDerivK coordinate)
      (targetChartDerivH coordinate) := by
  subst jet
  simpa [Encloses, upperKTargetJet] using hnode

/-! ## Algebraic identity for the target value -/

/-- At the scalar level, the historical association is exactly
`FirstBracket / e`.  This identity is unconditional because division in a
field distributes over addition even at the totalized value `e = 0`; the
physical evaluator separately checks `e > 0` for interval division. -/
theorem historicalAssociation_value_eq_upperKTarget
    (point : CertificatePoint) :
    lrCertificateBFlow point *
          ((lrDeterminantPsi point - lrCertificateGShape point +
              4 * lrDeterminantDelta point * lrCertificateW point) /
            lrCertificateE point) +
        lrDeterminantD1 point *
          (lrDeterminantPsi point / lrCertificateE point) =
      lrFiniteDeterminantUpperKReplayTarget point := by
  unfold lrFiniteDeterminantUpperKReplayTarget lrDeterminantFirstBracket
  ring

/-! ## Algebraic identity for all three target derivatives -/

/-- The scalar derivative represented by the corresponding component of
`historicalAssociationJet`. -/
noncomputable def historicalAssociationDerivative
    (b b' base base' d1 d1' psi psi' e e' : ℝ) : ℝ :=
  b' * (base / e) +
      b * ((base' * e - base * e') / e ^ 2) +
    (d1' * (psi / e) +
      d1 * ((psi' * e - psi * e') / e ^ 2))

/-- Product/quotient normalization for the audited association. -/
theorem historicalAssociationDerivative_eq_quotientDerivative
    {b b' base base' d1 d1' psi psi' e e' : ℝ}
    (he : e ≠ 0) :
    historicalAssociationDerivative
        b b' base base' d1 d1' psi psi' e e' =
      ((((b' * base + b * base') + (d1' * psi + d1 * psi')) * e -
          (b * base + d1 * psi) * e') / e ^ 2) := by
  unfold historicalAssociationDerivative
  field_simp [he]
  ring

/-- The historical association derivative with every ordinary CK component
substituted in an arbitrary raw `(s,k,chi)` direction. -/
noncomputable def upperKAssociationRawDerivative
    (point : CertificatePoint) (s' k' chi' : ℝ) : ℝ :=
  let e' := s' * point.k + point.s * k'
  let y0' := chi' * lrCertificateE point + point.chi * e'
  let x' := -(chi' * lrCertificateE point + point.chi * e')
  let v' := lrCertificateVDeriv point e' x'
  let b' := lrCertificateBFlowDeriv point s' e' v'
  let d1' := d1Deriv point s' e'
  let g' := lrCertificateGShapeDeriv point y0' e' v'
  let psi' := psiDeriv point s' y0' e' v'
  let delta' := deltaDeriv point x' v'
  let w' := lrCertificateOmegaDeriv point.s 0 s' 0
  let base := lrDeterminantPsi point - lrCertificateGShape point +
    4 * lrDeterminantDelta point * lrCertificateW point
  let base' := psi' - g' +
    4 * (delta' * lrCertificateW point +
      lrDeterminantDelta point * w')
  historicalAssociationDerivative
    (lrCertificateBFlow point) b' base base'
    (lrDeterminantD1 point) d1'
    (lrDeterminantPsi point) psi'
    (lrCertificateE point) e'

/-- Thus the real derivative assembled term-by-term is exactly the production
directional derivative of `FirstBracket/e`. -/
theorem upperKAssociationRawDerivative_eq_targetRawDeriv
    (point : CertificatePoint) (s' k' chi' : ℝ)
    (he : lrCertificateE point ≠ 0) :
    upperKAssociationRawDerivative point s' k' chi' =
      targetRawDeriv point s' k' chi' := by
  unfold upperKAssociationRawDerivative targetRawDeriv
  dsimp only
  unfold historicalAssociationDerivative firstBracketDeriv
    lrDeterminantFirstBracket
  dsimp only
  field_simp [he]
  ring

/-- The exact real jet obtained by applying the preceding raw identity in
the three decoded chart directions. -/
noncomputable def upperKAssociationTargetJet
    (coordinate : CertificatePoint) : Jet3 where
  value := lrFiniteDeterminantUpperKReplayTarget
    (lrDeterminantKChartDecode coordinate)
  derivS := upperKAssociationRawDerivative
    (lrDeterminantKChartDecode coordinate) 1 coordinate.k 0
  derivK := upperKAssociationRawDerivative
    (lrDeterminantKChartDecode coordinate) 0 coordinate.s 0
  derivH := upperKAssociationRawDerivative
    (lrDeterminantKChartDecode coordinate) 0 0 (2 * coordinate.chi)

/-- On the physical positive-`e` chart, the termwise association jet agrees
with the genuine value and all three genuine chart derivatives. -/
theorem upperKAssociationTargetJet_eq_upperKTargetJet
    (coordinate : CertificatePoint)
    (he : lrCertificateE (lrDeterminantKChartDecode coordinate) ≠ 0) :
    upperKAssociationTargetJet coordinate = upperKTargetJet coordinate := by
  apply Jet3.ext
  · rfl
  · simpa [upperKAssociationTargetJet, upperKTargetJet,
      targetChartDerivS] using
      upperKAssociationRawDerivative_eq_targetRawDeriv
        (lrDeterminantKChartDecode coordinate) 1 coordinate.k 0 he
  · simpa [upperKAssociationTargetJet, upperKTargetJet,
      targetChartDerivK] using
      upperKAssociationRawDerivative_eq_targetRawDeriv
        (lrDeterminantKChartDecode coordinate) 0 coordinate.s 0 he
  · simpa [upperKAssociationTargetJet, upperKTargetJet,
      targetChartDerivH] using
      upperKAssociationRawDerivative_eq_targetRawDeriv
        (lrDeterminantKChartDecode coordinate) 0 0
          (2 * coordinate.chi) he

/-!
## Exact production facts still to export

To instantiate `evaluateAD_sound_of_sharp_nodes` at a box point, the
production proof should expose the following facts that it already constructs
locally inside `sharpEvaluateSKAD_sound`:

1. `eAD.Contains (E, e_s, e_K, 0)` and `0 < eAD.value.lower`;
2. `vAD.Contains (V, v_s, v_K, v_h)` and `0 < vAD.value.lower`;
3. full three-coordinate `Contains` facts for `bFlowAD` and `d1AD`;
4. the existing `g0.evaluate`, `wAD`, `kappaAD`, and `deltaAD` facts;
5. the four new facts for `aY0HistoricalAD`, `aEHistoricalAD`,
   `cY0HistoricalAD`, and `cEHistoricalAD`.

No soundness theorem for a larger preassembled expression is required.  The
two positivity checks plus those twelve component enclosures are exactly the
interface consumed above.  The remaining real-algebra step is to identify
the resulting `evaluateJet` with `upperKTargetJet`; its value component is the
preceding theorem.  The three derivative components reduce to
`upperKAssociationTargetJet_eq_upperKTargetJet`; no additional calculus is
needed at this final assembly layer.
-/

end LRUpperKHistoricalEvaluatorAssembly
end CourtadeKumar
