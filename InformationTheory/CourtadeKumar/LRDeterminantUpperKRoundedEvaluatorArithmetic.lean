import InformationTheory.CourtadeKumar.LRDeterminantUpperKDyadicOuterRounding
import InformationTheory.CourtadeKumar.LRDeterminantUpperKExplicitEvaluatorNodes

/-!
# Dyadically rounded upper-K evaluator arithmetic

Every arithmetic operation is followed by verified outward rounding.  This
prevents denominator growth through the final evaluator while preserving the
same real-jet semantics.
-/

namespace CourtadeKumar
namespace LRUpperKRoundedEvaluatorArithmetic

open LRUpperKHistoricalEvaluatorAssembly
open LRUpperKMidpointCoarsening
open LRUpperKDyadicOuterRounding

abbrev Nodes := LRUpperKExplicitEvaluatorNodes.Payload

def outerNodes (bits : ℕ) (nodes : Nodes) : Nodes :=
  { bFlow := outerIntervalAD bits nodes.bFlow
    d1 := outerIntervalAD bits nodes.d1
    g0 := outerIntervalAD bits nodes.g0
    aY0 := outerIntervalAD bits nodes.aY0
    aE := outerIntervalAD bits nodes.aE
    cY0 := outerIntervalAD bits nodes.cY0
    cE := outerIntervalAD bits nodes.cE
    v := outerIntervalAD bits nodes.v
    kappa := outerIntervalAD bits nodes.kappa
    delta := outerIntervalAD bits nodes.delta
    w := outerIntervalAD bits nodes.w
    e := outerIntervalAD bits nodes.e }

def add (bits : ℕ) (a b : IntervalAD) : IntervalAD :=
  outerIntervalAD bits (IntervalAD.add a b)

def mul (bits : ℕ) (a b : IntervalAD) : IntervalAD :=
  outerIntervalAD bits (IntervalAD.mul a b)

def divPositive (bits : ℕ) (a b : IntervalAD) : IntervalAD :=
  outerIntervalAD bits (IntervalAD.divPositive a b)

theorem encloses_add {bits : ℕ} {a b : IntervalAD} {x y : Jet3}
    (ha : Encloses a x) (hb : Encloses b y) :
    Encloses (add bits a b) (Jet3.add x y) := by
  exact encloses_of_covers (outerIntervalAD_covers bits _)
    (LRUpperKHistoricalEvaluatorAssembly.encloses_add ha hb)

theorem encloses_mul {bits : ℕ} {a b : IntervalAD} {x y : Jet3}
    (ha : Encloses a x) (hb : Encloses b y) :
    Encloses (mul bits a b) (Jet3.mul x y) := by
  exact encloses_of_covers (outerIntervalAD_covers bits _)
    (LRUpperKHistoricalEvaluatorAssembly.encloses_mul ha hb)

theorem encloses_divPositive {bits : ℕ} {a b : IntervalAD} {x y : Jet3}
    (hbPositive : (0 : ℚ) < b.value.lower)
    (ha : Encloses a x) (hb : Encloses b y) :
    Encloses (divPositive bits a b) (Jet3.div x y) := by
  exact encloses_of_covers (outerIntervalAD_covers bits _)
    (LRUpperKHistoricalEvaluatorAssembly.encloses_divPositive
      hbPositive ha hb)

def psiAD (bits : ℕ) (nodes : Nodes) : IntervalAD :=
  add bits (add bits nodes.g0 nodes.aY0)
    (add bits (divPositive bits nodes.aE nodes.v)
      (mul bits nodes.kappa nodes.w))

def baseAD (bits : ℕ) (nodes : Nodes) : IntervalAD :=
  add bits (add bits nodes.cY0 (divPositive bits nodes.cE nodes.v))
    (mul bits
      (add bits nodes.kappa
        (mul bits (IntervalAD.const 4) nodes.delta))
      nodes.w)

def historicalAssociationAD (bits : ℕ)
    (b base d1 psi e : IntervalAD) : IntervalAD :=
  add bits
    (mul bits b (divPositive bits base e))
    (mul bits d1 (divPositive bits psi e))

def evaluateAD (bits : ℕ) (nodes : Nodes) : IntervalAD :=
  historicalAssociationAD bits nodes.bFlow (baseAD bits nodes) nodes.d1
    (psiAD bits nodes) nodes.e

theorem psiAD_sound {bits : ℕ} {nodes : Nodes}
    {g0Jet aY0Jet aEJet vJet kappaJet wJet : Jet3}
    (hvPositive : (0 : ℚ) < nodes.v.value.lower)
    (hg0 : Encloses nodes.g0 g0Jet)
    (haY0 : Encloses nodes.aY0 aY0Jet)
    (haE : Encloses nodes.aE aEJet)
    (hv : Encloses nodes.v vJet)
    (hkappa : Encloses nodes.kappa kappaJet)
    (hw : Encloses nodes.w wJet) :
    Encloses (psiAD bits nodes)
      (psiJet g0Jet aY0Jet aEJet vJet kappaJet wJet) := by
  have haEOver := encloses_divPositive (bits := bits) hvPositive haE hv
  have hkappaW := encloses_mul (bits := bits) hkappa hw
  have hleft := encloses_add (bits := bits) hg0 haY0
  have hright := encloses_add (bits := bits) haEOver hkappaW
  simpa [psiAD, psiJet] using encloses_add (bits := bits) hleft hright

theorem baseAD_sound {bits : ℕ} {nodes : Nodes}
    {cY0Jet cEJet vJet kappaJet deltaJet wJet : Jet3}
    (hvPositive : (0 : ℚ) < nodes.v.value.lower)
    (hcY0 : Encloses nodes.cY0 cY0Jet)
    (hcE : Encloses nodes.cE cEJet)
    (hv : Encloses nodes.v vJet)
    (hkappa : Encloses nodes.kappa kappaJet)
    (hdelta : Encloses nodes.delta deltaJet)
    (hw : Encloses nodes.w wJet) :
    Encloses (baseAD bits nodes)
      (baseJet cY0Jet cEJet vJet kappaJet deltaJet wJet) := by
  let fourJet : Jet3 :=
    { value := 4, derivS := 0, derivK := 0, derivH := 0 }
  have hfour : Encloses (IntervalAD.const 4) fourJet := by
    simpa [Encloses, fourJet] using IntervalAD.contains_const 4
  have hcEOver := encloses_divPositive (bits := bits) hvPositive hcE hv
  have hfourDelta := encloses_mul (bits := bits) hfour hdelta
  have hkapPlusDelta := encloses_add (bits := bits) hkappa hfourDelta
  have hweighted := encloses_mul (bits := bits) hkapPlusDelta hw
  have hleft := encloses_add (bits := bits) hcY0 hcEOver
  simpa [baseAD, baseJet, fourJet] using
    encloses_add (bits := bits) hleft hweighted

theorem historicalAssociationAD_sound {bits : ℕ}
    {b base d1 psi e : IntervalAD}
    {bJet baseJet d1Jet psiJet eJet : Jet3}
    (hePositive : (0 : ℚ) < e.value.lower)
    (hb : Encloses b bJet)
    (hbase : Encloses base baseJet)
    (hd1 : Encloses d1 d1Jet)
    (hpsi : Encloses psi psiJet)
    (he : Encloses e eJet) :
    Encloses (historicalAssociationAD bits b base d1 psi e)
      (LRUpperKHistoricalEvaluatorAssembly.historicalAssociationJet
        bJet baseJet d1Jet psiJet eJet) := by
  have hbaseOver := encloses_divPositive (bits := bits) hePositive hbase he
  have hpsiOver := encloses_divPositive (bits := bits) hePositive hpsi he
  have hleft := encloses_mul (bits := bits) hb hbaseOver
  have hright := encloses_mul (bits := bits) hd1 hpsiOver
  simpa [historicalAssociationAD,
    LRUpperKHistoricalEvaluatorAssembly.historicalAssociationJet] using
    encloses_add (bits := bits) hleft hright

theorem evaluateAD_sound_of_nodes {bits : ℕ} {nodes : Nodes}
    {bJet d1Jet g0Jet aY0Jet aEJet cY0Jet cEJet vJet
      kappaJet deltaJet wJet eJet : Jet3}
    (hvPositive : (0 : ℚ) < nodes.v.value.lower)
    (hePositive : (0 : ℚ) < nodes.e.value.lower)
    (hb : Encloses nodes.bFlow bJet)
    (hd1 : Encloses nodes.d1 d1Jet)
    (hg0 : Encloses nodes.g0 g0Jet)
    (haY0 : Encloses nodes.aY0 aY0Jet)
    (haE : Encloses nodes.aE aEJet)
    (hcY0 : Encloses nodes.cY0 cY0Jet)
    (hcE : Encloses nodes.cE cEJet)
    (hv : Encloses nodes.v vJet)
    (hkappa : Encloses nodes.kappa kappaJet)
    (hdelta : Encloses nodes.delta deltaJet)
    (hw : Encloses nodes.w wJet)
    (he : Encloses nodes.e eJet) :
    Encloses (evaluateAD bits nodes)
      (evaluateJet bJet d1Jet g0Jet aY0Jet aEJet cY0Jet cEJet
        vJet kappaJet deltaJet wJet eJet) := by
  have hpsi := psiAD_sound (bits := bits)
    hvPositive hg0 haY0 haE hv hkappa hw
  have hbase := baseAD_sound (bits := bits)
    hvPositive hcY0 hcE hv hkappa hdelta hw
  have hresult := historicalAssociationAD_sound (bits := bits) hePositive
    hb hbase hd1 hpsi he
  simpa [evaluateAD, evaluateJet] using hresult

end LRUpperKRoundedEvaluatorArithmetic
end CourtadeKumar
