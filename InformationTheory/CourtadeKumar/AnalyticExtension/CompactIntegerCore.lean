import InformationTheory.CourtadeKumar.AnalyticExtension.CompactADCore
namespace CourtadeKumar.LRCompactIntegerCertificate
open LRCompactReducedCertificate (Expr targetExpr)

def scale : ℤ := 2 ^ 56
structure I where
  lower : ℤ
  upper : ℤ

def fromRat (a : RationalEnclosure) : I :=
  ⟨Int.floor (a.lower * scale), Int.ceil (a.upper * scale)⟩
def addBase (a b : I) : I := ⟨a.lower+b.lower, a.upper+b.upper⟩
def addI (a b : I) : I :=
  if a.lower = 0 ∧ a.upper = 0 then b
  else if b.lower = 0 ∧ b.upper = 0 then a
  else addBase a b
def subI (a b : I) : I := ⟨a.lower-b.upper, a.upper-b.lower⟩
def negI (a : I) : I := ⟨-a.upper, -a.lower⟩
def pointI (q : ℚ) : I := fromRat ⟨q,q⟩
def mulBase (a b : I) : I :=
  let l := min (min (a.lower*b.lower) (a.upper*b.lower))
    (min (a.lower*b.upper) (a.upper*b.upper))
  let u := max (max (a.lower*b.lower) (a.upper*b.lower))
    (max (a.lower*b.upper) (a.upper*b.upper))
  ⟨l / scale, -((-u) / scale)⟩
def mulI (a b : I) : I :=
  if b.lower = 0 ∧ b.upper = 0 then ⟨0,0⟩
  else if a.lower = 0 ∧ a.upper = 0 then ⟨0,0⟩
  else mulBase a b
def powI (a : I) : Nat → I
  | 0 => ⟨scale,scale⟩
  | n+1 => mulI (powI a n) a
def invI (a : I) : I := ⟨scale^2/a.upper, -((-(scale^2))/a.lower)⟩
structure Bounds where
  value : I
  derivS : I
  derivK : I
  derivChi : I
structure Jet where
  bounds : Bounds
  valid : Bool

def Jet.const (q : ℚ) : Jet := ⟨⟨pointI q, pointI 0, pointI 0, pointI 0⟩, true⟩
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
  let value := invI a.bounds.value
  let slope := negI (powI value 2)
  ⟨⟨value, mulI slope a.bounds.derivS, mulI slope a.bounds.derivK,
      mulI slope a.bounds.derivChi⟩,
    a.valid && decide (0 < a.bounds.value.lower)⟩
def Jet.div (a b : Jet) : Jet := a.mul b.inv
def Jet.logWith (a : Jet) (value : I) : Jet :=
  let slope := invI a.bounds.value
  ⟨⟨value, mulI slope a.bounds.derivS, mulI slope a.bounds.derivK,
      mulI slope a.bounds.derivChi⟩,
    a.valid && decide (0 < a.bounds.value.lower)⟩
def Jet.pow (a : Jet) (n : Nat) : Jet :=
  let value := powI a.bounds.value n
  let slope := mulI (pointI (n : ℚ)) (powI a.bounds.value (n - 1))
  ⟨⟨value, mulI slope a.bounds.derivS, mulI slope a.bounds.derivK,
      mulI slope a.bounds.derivChi⟩,
    a.valid⟩

def enclose (env : Nat → Jet) : Expr → Jet
  | .rat q => Jet.const q
  | .var i => env i
  | .add a b => (enclose env a).add (enclose env b)
  | .sub a b => (enclose env a).sub (enclose env b)
  | .mul a b => (enclose env a).mul (enclose env b)
  | .div a b => (enclose env a).div (enclose env b)
  | .pow a n => (enclose env a).pow n

def I.decode (a : I) : RationalEnclosure :=
  ⟨(a.lower : ℚ) / (scale : ℚ), (a.upper : ℚ) / (scale : ℚ)⟩
def Jet.decode (a : Jet) : LRCompactReducedCertificate.Jet :=
  ⟨⟨a.bounds.value.decode, a.bounds.derivS.decode, a.bounds.derivK.decode,
    a.bounds.derivChi.decode⟩, a.valid⟩
def Jet.fromRat (a : LRCompactReducedCertificate.Jet) : Jet :=
  ⟨⟨LRCompactIntegerCertificate.fromRat a.bounds.value, LRCompactIntegerCertificate.fromRat a.bounds.derivS, LRCompactIntegerCertificate.fromRat a.bounds.derivK,
    LRCompactIntegerCertificate.fromRat a.bounds.derivChi⟩, a.valid⟩

def absBound (a : I) : ℤ := max (abs a.lower) (abs a.upper)

def sharedSums (R v t h g : Jet) : Nat → Jet × Jet
  | 0 => (Jet.const 0, Jet.const 0)
  | j+1 =>
    let prev := sharedSums R v t h g j
    let n := j+1
    let sh := (t.pow (2*n)).mul ((Jet.const 1).add (v.pow (2*n-1)))
    let u := (R.pow (n-1)).mul ((Jet.const 1).add ((Jet.const (n-1)).mul ((Jet.const 1).sub R)))
    let au := (Jet.const (1 / (2*n*(2*n-1) : ℚ))).mul u
    ((prev.1).add (au.mul (h.sub sh)), (prev.2).add (au.mul (g.sub sh)))
def sharedDSum (q : Jet) : Nat → Jet
  | 0 => Jet.const 0
  | j+1 => (sharedDSum q j).add ((q.pow (2*j+1)).div (Jet.const (2*j+1)))
def sharedTarget (env : Nat → Jet) (N M : Nat) : Jet :=
  let R := env 0; let v := env 1; let t := env 2
  let h := (((Jet.const 4).mul v).mul (t.pow 2)).div ((Jet.const 1).add v)
  let g := (Jet.const 4).div ((Jet.const 1).add v)
  let y := (v.pow 2).mul (t.pow 2)
  let q := (((Jet.const 1).sub R).mul y).div ((Jet.const 2).sub (((Jet.const 1).add R).mul y))
  let sums := sharedSums R v t h g N
  let Q := (((((env 4).mul t).add ((env 5).div v)).add (env 6)).sub (h.mul (env 7))).add sums.1
  let Q := Q.sub ((Jet.const ((1/2:ℚ)^(2*N+1))).mul (env 7))
  ((env 3).mul Q).add ((sharedDSum q M).mul sums.2)


end CourtadeKumar.LRCompactIntegerCertificate
