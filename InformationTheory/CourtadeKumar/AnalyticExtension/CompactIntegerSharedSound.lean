import InformationTheory.CourtadeKumar.AnalyticExtension.CompactIntegerSound

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CourtadeKumar.LRCompactIntegerCertificate
open LRCompactReducedCertificate (Expr sumExpr channelExpr shapeExpr hExpr gExpr
  coordinateExpr dExpr qExpr cExpr targetExpr)

lemma sharedSums_eq (env : Nat → Jet) (N : Nat) :
    (sharedSums (env 0) (env 1) (env 2) (enclose env hExpr) (enclose env gExpr) N).1 =
      enclose env (sumExpr (fun j => Expr.rat (1 / (2*(j+1)*(2*(j+1)-1):ℚ)) *
        channelExpr (j+1) * (hExpr - shapeExpr (j+1))) N) ∧
    (sharedSums (env 0) (env 1) (env 2) (enclose env hExpr) (enclose env gExpr) N).2 =
      enclose env (sumExpr (fun j => Expr.rat (1 / (2*(j+1)*(2*(j+1)-1):ℚ)) *
        channelExpr (j+1) * (gExpr - shapeExpr (j+1))) N) := by
  induction N with
  | zero => exact ⟨rfl,rfl⟩
  | succ n ih =>
    constructor
    · simp only [sharedSums, sumExpr, enclose, channelExpr, shapeExpr,
        Nat.cast_add, Nat.cast_one]
      rw [ih.1]
      simp only [channelExpr, shapeExpr, Nat.cast_add, Nat.cast_one]
    · simp only [sharedSums, sumExpr, enclose, channelExpr, shapeExpr,
        Nat.cast_add, Nat.cast_one]
      rw [ih.2]
      simp only [channelExpr, shapeExpr, Nat.cast_add, Nat.cast_one]

lemma sharedDSum_eq (env : Nat → Jet) (M : Nat) :
    sharedDSum (enclose env coordinateExpr) M = enclose env (dExpr M) := by
  induction M with
  | zero => rfl
  | succ m ih =>
    change (sharedDSum (enclose env coordinateExpr) m).add _ =
      (enclose env (dExpr m)).add _
    rw [ih]
    rfl

lemma sharedTarget_eq (env : Nat → Jet) (N M : Nat) :
    sharedTarget env N M = enclose env (targetExpr N M) := by
  have hs := sharedSums_eq env N
  have hd := sharedDSum_eq env M
  unfold sharedTarget targetExpr qExpr cExpr
  simp only [enclose]
  rw [← hs.1, ← hs.2, ← hd]
  rfl

end CourtadeKumar.LRCompactIntegerCertificate
