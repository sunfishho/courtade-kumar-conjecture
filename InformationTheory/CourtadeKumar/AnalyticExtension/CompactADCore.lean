import InformationTheory.CourtadeKumar.IntervalADArithmeticCore
import InformationTheory.CourtadeKumar.LRDeterminantUpperKDyadicOuterRoundingEvalCore

/-! Bounded-precision rational arithmetic for compact-V derivative certificates.
Every operation rounds outward to 56 binary fractional digits. -/
namespace CourtadeKumar.LRCompactReducedCertificate

def bits : Nat := 56
def rounded (a : RationalEnclosure) : RationalEnclosure :=
  LRUpperKDyadicOuterRounding.outerEnclosure bits a

def mul4 (a b : RationalEnclosure) : RationalEnclosure :=
  ⟨min (min (a.lower * b.lower) (a.upper * b.lower))
      (min (a.lower * b.upper) (a.upper * b.upper)),
   max (max (a.lower * b.lower) (a.upper * b.lower))
      (max (a.lower * b.upper) (a.upper * b.upper))⟩

def mulI (a b : RationalEnclosure) : RationalEnclosure := rounded (mul4 a b)
def addI (a b : RationalEnclosure) : RationalEnclosure := rounded (RationalEnclosure.add a b)
def subI (a b : RationalEnclosure) : RationalEnclosure := rounded (RationalEnclosure.sub a b)
def powI (a : RationalEnclosure) (n : Nat) : RationalEnclosure :=
  rounded ⟨a.lower ^ n, a.upper ^ n⟩

structure Jet where
  bounds : IntervalAD
  valid : Bool

def Jet.const (q : ℚ) : Jet := ⟨IntervalAD.const q, true⟩
def Jet.add (a b : Jet) : Jet :=
  ⟨⟨addI a.bounds.value b.bounds.value,
      addI a.bounds.derivS b.bounds.derivS,
      addI a.bounds.derivK b.bounds.derivK,
      addI a.bounds.derivChi b.bounds.derivChi⟩, a.valid && b.valid⟩
def Jet.sub (a b : Jet) : Jet :=
  ⟨⟨subI a.bounds.value b.bounds.value,
      subI a.bounds.derivS b.bounds.derivS,
      subI a.bounds.derivK b.bounds.derivK,
      subI a.bounds.derivChi b.bounds.derivChi⟩, a.valid && b.valid⟩
def Jet.mul (a b : Jet) : Jet :=
  ⟨⟨mulI a.bounds.value b.bounds.value,
      addI (mulI a.bounds.derivS b.bounds.value) (mulI a.bounds.value b.bounds.derivS),
      addI (mulI a.bounds.derivK b.bounds.value) (mulI a.bounds.value b.bounds.derivK),
      addI (mulI a.bounds.derivChi b.bounds.value) (mulI a.bounds.value b.bounds.derivChi)⟩,
    a.valid && b.valid⟩
def Jet.inv (a : Jet) : Jet :=
  let value := rounded (RationalEnclosure.invPositive a.bounds.value)
  let slope := RationalEnclosure.neg (powI value 2)
  ⟨⟨value, mulI slope a.bounds.derivS, mulI slope a.bounds.derivK,
      mulI slope a.bounds.derivChi⟩,
    a.valid && decide (0 < a.bounds.value.lower)⟩
def Jet.div (a b : Jet) : Jet := a.mul b.inv
def Jet.logWith (a : Jet) (value : RationalEnclosure) : Jet :=
  let slope := rounded (RationalEnclosure.invPositive a.bounds.value)
  ⟨⟨value, mulI slope a.bounds.derivS, mulI slope a.bounds.derivK,
      mulI slope a.bounds.derivChi⟩,
    a.valid && decide (0 < a.bounds.value.lower)⟩
def Jet.pow (a : Jet) (n : Nat) : Jet :=
  let value := powI a.bounds.value n
  let slope := mulI (RationalEnclosure.point (n : ℚ)) (powI a.bounds.value (n - 1))
  ⟨⟨value, mulI slope a.bounds.derivS, mulI slope a.bounds.derivK,
      mulI slope a.bounds.derivChi⟩,
    a.valid && decide (0 ≤ a.bounds.value.lower)⟩

inductive Expr where
  | rat (q : ℚ)
  | var (i : Nat)
  | add (a b : Expr)
  | sub (a b : Expr)
  | mul (a b : Expr)
  | div (a b : Expr)
  | pow (a : Expr) (n : Nat)

instance (n : Nat) : OfNat Expr n := ⟨.rat n⟩
instance : Add Expr := ⟨.add⟩
instance : Sub Expr := ⟨.sub⟩
instance : Mul Expr := ⟨.mul⟩
instance : Div Expr := ⟨.div⟩
instance : Pow Expr Nat := ⟨.pow⟩

def Expr.enclose (env : Nat → Jet) : Expr → Jet
  | .rat q => Jet.const q
  | .var i => env i
  | .add a b => (a.enclose env).add (b.enclose env)
  | .sub a b => (a.enclose env).sub (b.enclose env)
  | .mul a b => (a.enclose env).mul (b.enclose env)
  | .div a b => (a.enclose env).div (b.enclose env)
  | .pow a n => (a.enclose env).pow n

def sumExpr (f : Nat → Expr) : Nat → Expr
  | 0 => 0
  | n + 1 => sumExpr f n + f n

def coordinateExpr : Expr :=
  let R : Expr := .var 0; let v : Expr := .var 1; let t : Expr := .var 2
  (1 - R) * (v ^ 2 * t ^ 2) / (2 - (1 + R) * (v ^ 2 * t ^ 2))

def dExpr (M : Nat) : Expr :=
  sumExpr (fun j => coordinateExpr ^ (2 * j + 1) / .rat (2 * j + 1)) M

def shapeExpr (n : Nat) : Expr :=
  (.var 2 : Expr) ^ (2 * n) * (1 + (.var 1 : Expr) ^ (2 * n - 1))

def channelExpr (n : Nat) : Expr :=
  (.var 0 : Expr) ^ (n - 1) * (1 + .rat (n - 1) * (1 - (.var 0 : Expr)))

def hExpr : Expr :=
  4 * (.var 1 : Expr) * (.var 2 : Expr) ^ 2 / (1 + (.var 1 : Expr))

def gExpr : Expr := 4 / (1 + (.var 1 : Expr))

def qExpr (N : Nat) : Expr :=
  (.var 4 : Expr) * (.var 2 : Expr) + (.var 5 : Expr) / (.var 1 : Expr) + (.var 6 : Expr) -
    hExpr * (.var 7 : Expr) +
    sumExpr (fun j => .rat (1 / (2 * (j + 1) * (2 * (j + 1) - 1) : ℚ)) *
      channelExpr (j + 1) * (hExpr - shapeExpr (j + 1))) N -
    .rat ((1 / 2 : ℚ) ^ (2 * N + 1)) * (.var 7 : Expr)

def cExpr (N : Nat) : Expr :=
  sumExpr (fun j => .rat (1 / (2 * (j + 1) * (2 * (j + 1) - 1) : ℚ)) *
    channelExpr (j + 1) * (gExpr - shapeExpr (j + 1))) N

def targetExpr (N M : Nat) : Expr := (.var 3 : Expr) * qExpr N + dExpr M * cExpr N

def absBound (a : RationalEnclosure) : ℚ := max (abs a.lower) (abs a.upper)

def bLogInputs (R v t : Jet) : Jet × Jet :=
  ((Jet.const 1).add v, (Jet.const 1).sub (R.mul ((v.pow 2).mul (t.pow 2))))

def bJet (R v t : Jet) (logV logS : RationalEnclosure) : Jet :=
  let args := bLogInputs R v t
  (args.1.logWith logV).sub ((args.2.logWith logS).div (Jet.const 2))

end CourtadeKumar.LRCompactReducedCertificate
