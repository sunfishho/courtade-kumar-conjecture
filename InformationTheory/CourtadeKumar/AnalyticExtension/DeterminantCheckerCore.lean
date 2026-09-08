import InformationTheory.CourtadeKumar.AnalyticExtension.MidpointRationalCheckerCore

/-! Pure rational checker for the reduced finite determinant. -/
namespace CourtadeKumar.LRDeterminantReducedCertificate
open LRMidpointReducedCertificate

def pExpr : Expr :=
  let s : Expr := .var 0; let k : Expr := .var 1; let c : Expr := .var 2
  1 - s + s * k * (1 - c) / 2 + alphaExpr

def gExpr : Expr :=
  let s : Expr := .var 0; let C : Expr := .var 3; let h : Expr := .var 4
  (1 - 2 * s * C / 7) * (1 - s) / 3 *
    (1 - (h + .rat (11 / 4)) / (C + .rat (15 / 4)))

def costExpr : Expr :=
  let s : Expr := .var 0; let k : Expr := .var 1; let c : Expr := .var 2
  let C : Expr := .var 3; let e := s * k
  s / (1 + c) * (2 * c / 7 + e * (1 - c) / 2) +
    2 * (dExpr * dExpr * dExpr / 24) * (1 + 2 * e / (3 * (1 + c))) +
    s * s * C / (14 * (1 + c)) * (2 * e + .rat (64 / 7))

def lossExpr (tangent : Bool) : Expr :=
  let c : Expr := .var 2
  if tangent then ((.var 7) + c * ((.var 8) - 1)) / (1 + c) - alphaExpr
  else tExpr / (1 + c)

def coefficientExpr : Expr := pExpr - gExpr

def lowerExpr (tangent : Bool) : Expr :=
  let s : Expr := .var 0; let k : Expr := .var 1; let c : Expr := .var 2
  (.var 6) * coefficientExpr + (.var 5) * ((1 - c * (s * k)) * gExpr - lossExpr tangent - costExpr)

structure Leaf where
  logCLo : RoundedLog
  logCHi : RoundedLog
  logALo : RoundedLog
  logAHi : RoundedLog
  logD : RoundedLog
  tangentPoint : ℚ
  logTangent : RoundedLog
  useTangent : Bool

def BoxValid (b : CertificateBox) : Prop :=
  0 < b.sLo ∧ b.sLo ≤ b.sHi ∧ b.sHi ≤ 1 / 10 ∧
  0 < b.kLo ∧ b.kLo ≤ b.kHi ∧ b.kHi ≤ 4 ∧
  0 ≤ b.chiLo ∧ b.chiLo ≤ b.chiHi ∧ b.chiHi ≤ 1
instance (b : CertificateBox) : Decidable (BoxValid b) := inferInstanceAs (Decidable (_ ∧ _))

def lowerY (b : CertificateBox) : ℚ := 1 / b.kHi + 1 - b.sHi
def Leaf.dLower (b : CertificateBox) (d : Leaf) : ℚ :=
  d.logD.lower / 2 + (lowerY b - 1) / (3 * lowerY b + 1)

def Leaf.hCap (b : CertificateBox) (d : Leaf) : ℚ :=
  let aLo := (1 - b.sHi) * b.kLo
  let aHi := (1 - b.sLo) * b.kHi
  min ((1 + aHi) * d.logAHi.upper / aLo) (1 + aHi / 2)

def Leaf.inputs (b : CertificateBox) (d : Leaf) : Nat → RationalEnclosure
  | 0 => ⟨b.sLo, b.sHi⟩
  | 1 => ⟨b.kLo, b.kHi⟩
  | 2 => ⟨b.chiLo, b.chiHi⟩
  | 3 => ⟨d.logCLo.lower, d.logCHi.upper⟩
  | 4 => RationalEnclosure.point (d.hCap b)
  | 5 => ⟨d.logCLo.lower / 2 - 7 / 10 + 6 / 11 - d.logAHi.upper / 2,
      d.logCHi.upper / 2 - d.logALo.lower / 2⟩
  | 6 => RationalEnclosure.point (d.dLower b)
  | 7 => RationalEnclosure.point d.tangentPoint
  | 8 => RationalEnclosure.point d.logTangent.upper
  | _ => RationalEnclosure.point 0

def Leaf.check (b : CertificateBox) (d : Leaf) : Bool :=
  decide (BoxValid b) &&
  (d.logCLo.check (4 / b.sHi) &&
  (d.logCHi.check (4 / b.sLo) &&
  (d.logALo.check (1 + (1 - b.sHi) * b.kLo) &&
  (d.logAHi.check (1 + (1 - b.sLo) * b.kHi) &&
  (d.logD.check ((1 + lowerY b) / 2) &&
  (decide (0 < d.tangentPoint ∧ d.tangentPoint ≤ 1) &&
  (d.logTangent.check (1 / d.tangentPoint) &&
  (coefficientExpr.valid (d.inputs b) &&
  (decide (0 ≤ (coefficientExpr.enclose (d.inputs b)).lower) &&
  ((lowerExpr d.useTangent).valid (d.inputs b) &&
    decide (0 ≤ ((lowerExpr d.useTangent).enclose (d.inputs b)).lower)))))))))))

abbrev Tree := SubdivisionCertificate Leaf Unit
def checkTree (b : CertificateBox) (tree : Tree) : Bool := tree.check Leaf.check (fun _ _ => false) b

end CourtadeKumar.LRDeterminantReducedCertificate
