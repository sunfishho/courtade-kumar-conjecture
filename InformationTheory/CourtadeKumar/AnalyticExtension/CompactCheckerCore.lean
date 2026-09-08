import InformationTheory.CourtadeKumar.AnalyticExtension.CompactADCore
import InformationTheory.CourtadeKumar.AnalyticExtension.MidpointRationalCheckerCore

/-! Executable compact-V checker. Coordinates are R, v, and t (not t²).
The arithmetic has no real-valued semantics or proof assumptions in this file. -/
namespace CourtadeKumar.LRCompactReducedCertificate
open LRMidpointReducedCertificate (RoundedLog)

structure EndpointLog where
  reciprocal : Bool
  witness : RoundedLog

def EndpointLog.enclosure (d : EndpointLog) : RationalEnclosure :=
  if d.reciprocal then ⟨-d.witness.upper, -d.witness.lower⟩
  else ⟨d.witness.lower, d.witness.upper⟩
def EndpointLog.check (d : EndpointLog) (x : ℚ) : Bool :=
  decide (0 < x) && d.witness.check (if d.reciprocal then x⁻¹ else x)

structure LogInterval where
  lower : EndpointLog
  upper : EndpointLog

def LogInterval.enclosure (d : LogInterval) : RationalEnclosure :=
  ⟨d.lower.enclosure.lower, d.upper.enclosure.upper⟩
def LogInterval.check (d : LogInterval) (a : RationalEnclosure) : Bool :=
  d.lower.check a.lower && d.upper.check a.upper

structure BData where
  logV : LogInterval
  logS : LogInterval

def BData.jet (d : BData) (R v t : Jet) : Jet :=
  bJet R v t d.logV.enclosure d.logS.enclosure

def BData.check (d : BData) (R v t : Jet) : Bool :=
  let args := bLogInputs R v t
  args.1.valid && args.2.valid &&
    d.logV.check args.1.bounds.value && d.logS.check args.2.bounds.value

structure TangentData where
  logA : RoundedLog
  logB : RoundedLog
  logU : RoundedLog
  logC : RoundedLog

def TangentData.aT (d : TangentData) : ℚ := (d.logA.lower + d.logB.lower)/2
def TangentData.au (d : TangentData) : ℚ := -d.logU.upper/2
def TangentData.ac (d : TangentData) : ℚ := -d.logC.upper/2

def TangentData.check (d : TangentData) (a b : ℚ) : Bool :=
  decide (0 ≤ a ∧ a < 1 ∧ 0 ≤ b ∧ b < 1) &&
    d.logA.check ((1+a)/(1-a)) && d.logB.check ((1+b)/(1-b)) &&
    d.logU.check (1/(1-b^2)) && d.logC.check (1/(1-a^2))

def boxR (b : CertificateBox) : RationalEnclosure := ⟨b.sLo,b.sHi⟩
def boxV (b : CertificateBox) : RationalEnclosure := ⟨b.kLo,b.kHi⟩
def boxT (b : CertificateBox) : RationalEnclosure := ⟨b.chiLo,b.chiHi⟩

def constInterval (a : RationalEnclosure) : Jet :=
  ⟨⟨a, RationalEnclosure.point 0, RationalEnclosure.point 0, RationalEnclosure.point 0⟩,true⟩
def rJet (b : CertificateBox) : Jet := ⟨IntervalAD.variableS (boxR b),true⟩
def vJet (b : CertificateBox) : Jet := ⟨IntervalAD.variableK (boxV b),true⟩
def tJet (b : CertificateBox) : Jet := ⟨IntervalAD.variableChi (boxT b),true⟩
def rPoint (b : CertificateBox) : Jet := Jet.const (RationalEnclosure.center (boxR b))
def vPoint (b : CertificateBox) : Jet := Jet.const (RationalEnclosure.center (boxV b))
def tPoint (b : CertificateBox) : Jet := Jet.const (RationalEnclosure.center (boxT b))

structure Leaf where
  tangent : TangentData
  wholeB : BData
  pointB : BData

def Leaf.inputs (b : CertificateBox) (d : Leaf) (L : RationalEnclosure) : Nat → Jet
  | 0 => rJet b | 1 => vJet b | 2 => tJet b
  | 3 => d.wholeB.jet (rJet b) (vJet b) (tJet b)
  | 4 => Jet.const d.tangent.aT | 5 => Jet.const d.tangent.au
  | 6 => Jet.const d.tangent.ac | 7 => constInterval L | _ => Jet.const 0

def Leaf.pointInputs (b : CertificateBox) (d : Leaf) (L : RationalEnclosure) : Nat → Jet
  | 0 => rPoint b | 1 => vPoint b | 2 => tPoint b
  | 3 => d.pointB.jet (rPoint b) (vPoint b) (tPoint b)
  | 4 => Jet.const d.tangent.aT | 5 => Jet.const d.tangent.au
  | 6 => Jet.const d.tangent.ac | 7 => constInterval L | _ => Jet.const 0

def BoxValid (b : CertificateBox) : Prop :=
  0 ≤ b.sLo ∧ b.sLo ≤ b.sHi ∧ b.sHi ≤ 9/10 ∧
  1/3 ≤ b.kLo ∧ b.kLo ≤ b.kHi ∧ b.kHi ≤ 1 ∧
  9/10 ≤ b.chiLo ∧ b.chiLo ≤ b.chiHi ∧ b.chiHi ≤ 1
instance (b : CertificateBox) : Decidable (BoxValid b) := inferInstanceAs (Decidable (_ ∧ _))

def Leaf.precheck (b : CertificateBox) (d : Leaf) : Bool :=
  decide (BoxValid b) &&
  d.tangent.check (RationalEnclosure.center (boxT b))
    (RationalEnclosure.center (boxV b) * RationalEnclosure.center (boxT b)) &&
  d.wholeB.check (rJet b) (vJet b) (tJet b) &&
  d.pointB.check (rPoint b) (vPoint b) (tPoint b)

def boxLoss (b : CertificateBox) (whole : Jet) : ℚ :=
  RationalEnclosure.radius (boxR b) * absBound whole.bounds.derivS +
  RationalEnclosure.radius (boxV b) * absBound whole.bounds.derivK +
  RationalEnclosure.radius (boxT b) * absBound whole.bounds.derivChi

def Leaf.check (L : RationalEnclosure) (b : CertificateBox) (d : Leaf) : Bool :=
  let whole := (targetExpr 24 8).enclose (d.inputs b L)
  let point := (targetExpr 24 8).enclose (d.pointInputs b L)
  d.precheck b && whole.valid && point.valid &&
    decide (0 ≤ point.bounds.value.lower - boxLoss b whole)

def discard (b : CertificateBox) (_ : Unit) : Bool :=
  decide (BoxValid b) && decide
    ((1+b.kHi)^2*(1-b.kLo^2*b.chiLo^2) ≤
      (1-b.sHi*(b.kHi^2*b.chiHi^2))^2)

abbrev Tree := SubdivisionCertificate Leaf Unit
def root : CertificateBox := ⟨0,9/10,1/3,1,9/10,1⟩
def checkTree (L : RationalEnclosure) (b : CertificateBox) (tree : Tree) : Bool :=
  tree.check (Leaf.check L) discard b

end CourtadeKumar.LRCompactReducedCertificate
