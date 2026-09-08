import InformationTheory.CourtadeKumar.ExactLogEnclosureCore
import InformationTheory.CourtadeKumar.IntervalSubdivisionCertificateCore

/-! Small exact-rational checker for the analytic midpoint envelope.
This module contains arithmetic only; its soundness is proved separately. -/
namespace CourtadeKumar.LRMidpointReducedCertificate

inductive Expr where
  | rat (q : ℚ)
  | var (i : Nat)
  | add (a b : Expr)
  | sub (a b : Expr)
  | mul (a b : Expr)
  | div (a b : Expr)

instance (n : Nat) : OfNat Expr n := ⟨.rat n⟩
instance : Add Expr := ⟨.add⟩
instance : Sub Expr := ⟨.sub⟩
instance : Mul Expr := ⟨.mul⟩
instance : Div Expr := ⟨.div⟩

def tightMul (a b : RationalEnclosure) : RationalEnclosure :=
  if 0 ≤ a.lower ∧ 0 ≤ b.lower then RationalEnclosure.mulNonnegative a b
  else RationalEnclosure.mul a b

def Expr.enclose (env : Nat → RationalEnclosure) : Expr → RationalEnclosure
  | .rat q => RationalEnclosure.point q
  | .var i => env i
  | .add a b => RationalEnclosure.add (a.enclose env) (b.enclose env)
  | .sub a b => RationalEnclosure.sub (a.enclose env) (b.enclose env)
  | .mul a b => tightMul (a.enclose env) (b.enclose env)
  | .div a b => tightMul (a.enclose env) (RationalEnclosure.invPositive (b.enclose env))

def Expr.valid (env : Nat → RationalEnclosure) : Expr → Bool
  | .rat _ | .var _ => true
  | .add a b | .sub a b | .mul a b => a.valid env && b.valid env
  | .div a b => a.valid env && (b.valid env && decide (0 < (b.enclose env).lower))

def tExpr : Expr :=
  let s : Expr := .var 0; let k : Expr := .var 1; let c : Expr := .var 2
  (1 - c) / (2 * (1 + (1 - s) * k)) + c * (1 - c) / (2 * (1 + (1 - s) * k * c))

def alphaExpr : Expr :=
  let s : Expr := .var 0; let k : Expr := .var 1; let c : Expr := .var 2
  c / (1 + c) * (2 * ((1 - s) * k) * (1 - c)) / (2 + ((1 - s) * k) * (1 + c))

def dExpr : Expr :=
  let s : Expr := .var 0; let k : Expr := .var 1
  (1 - s * k) / (2 * k + 1 - s * k)

def hExpr : Expr :=
  let s : Expr := .var 0; let k : Expr := .var 1; let c : Expr := .var 2
  1 - k * (1 + c) * s - k * tExpr

def uExpr : Expr :=
  let s : Expr := .var 0; let k : Expr := .var 1; let c : Expr := .var 2
  1 - 2 * s + s * k * (1 - c) / 2 + alphaExpr - tExpr / (1 + c)

def lowerExpr : Expr :=
  let k : Expr := .var 1; let c : Expr := .var 2
  (.var 3) * hExpr + k * (1 + c) * dExpr * uExpr - (.var 4)

structure RoundedLog where
  range : RationalEnclosure.LogRangeCertificate
  lower : ℚ
  upper : ℚ

def RoundedLog.check (r : RoundedLog) (x : ℚ) : Bool :=
  r.range.check x && decide
    (r.lower ≤ (r.range.enclosure 10).lower ∧ (r.range.enclosure 10).upper ≤ r.upper)

structure Leaf where
  logC : RoundedLog
  logALo : RoundedLog
  logAHi : RoundedLog
  logRatioLo : RoundedLog
  logRatioHi : RoundedLog

def BoxValid (b : CertificateBox) : Prop :=
  0 < b.sLo ∧ b.sLo ≤ b.sHi ∧ b.sHi ≤ 1 / 10 ∧
  1 / 4 ≤ b.kLo ∧ b.kLo ≤ b.kHi ∧ b.kHi ≤ 4 ∧
  0 ≤ b.chiLo ∧ b.chiLo ≤ b.chiHi ∧ b.chiHi ≤ 1
instance (b : CertificateBox) : Decidable (BoxValid b) := inferInstanceAs (Decidable (_ ∧ _))

def Leaf.bd (d : Leaf) : RationalEnclosure :=
  ⟨max 0 (d.logRatioLo.lower / 2 + 6 / 11 - d.logAHi.upper),
    d.logRatioHi.upper / 2 + 7 / 10 - d.logALo.lower⟩

def Leaf.payment (b : CertificateBox) (d : Leaf) : ℚ :=
  (5 / 21) * b.sHi * d.logC.upper * (d.logC.upper - d.logALo.lower)

def Leaf.inputs (b : CertificateBox) (d : Leaf) : Nat → RationalEnclosure
  | 0 => ⟨b.sLo, b.sHi⟩
  | 1 => ⟨b.kLo, b.kHi⟩
  | 2 => ⟨b.chiLo, b.chiHi⟩
  | 3 => d.bd
  | 4 => RationalEnclosure.point (d.payment b)
  | _ => RationalEnclosure.point 0

def Leaf.check (b : CertificateBox) (d : Leaf) : Bool :=
  decide (BoxValid b) &&
  (d.logC.check (4 / b.sHi) &&
  (d.logALo.check (1 + (1 - b.sHi) * b.kLo) &&
  (d.logAHi.check (1 + (1 - b.sLo) * b.kHi) &&
  (d.logRatioLo.check (b.kLo / b.sHi) &&
  (d.logRatioHi.check (b.kHi / b.sLo) &&
  (decide (0 ≤ d.logALo.lower ∧ d.logALo.lower ≤ 2) &&
  (uExpr.valid (d.inputs b) &&
  (decide (0 ≤ (uExpr.enclose (d.inputs b)).lower) &&
  (lowerExpr.valid (d.inputs b) &&
    decide (0 ≤ (lowerExpr.enclose (d.inputs b)).lower))))))))))

def root : CertificateBox := ⟨1 / 16384, 1 / 10, 1 / 4, 4, 0, 1⟩
abbrev Tree := SubdivisionCertificate Leaf Unit

def checkTree (tree : Tree) : Bool := tree.check Leaf.check (fun _ _ => false) root

end CourtadeKumar.LRMidpointReducedCertificate
