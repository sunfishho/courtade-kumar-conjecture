import Mathlib
import Lean.Meta.Tactic.Grind.Arith.CommRing.ToExpr
import Lean.Data.RArray

/-!
# Kernel checking of exact real polynomial identities

A proved rational-expression normalizer collects positive natural denominators
using least common multiples. Lean's proved commutative-ring normalizer then
reduces equality to a closed integer-polynomial comparison, checked by
`decide +kernel`.

`kernel_ring` first rewrites binomial coefficients using their proved falling-
factorial formula, avoiding recursive binomial evaluation in the kernel. It
recognizes division by closed natural expressions; other operations become
atoms, so variable denominators can first be cleared with `field_simp`.

The module path and namespace are retained for compatibility with the original
native staging implementation. The `native_ring` spelling is a compatibility
alias for `kernel_ring`; neither tactic uses native reduction.
-/

open Lean Meta Elab Tactic

namespace CourtadeKumar.NativePolynomialNormalization

abbrev Context := Lean.Grind.CommRing.Context ℝ
abbrev RingExpr := Lean.Grind.CommRing.Expr

inductive Expr where
  | atom (a : RingExpr)
  | neg (a : Expr)
  | add (a b : Expr)
  | sub (a b : Expr)
  | mul (a b : Expr)
  | pow (a : Expr) (n : Nat)
  | divNat (a : Expr) (n : Nat)

noncomputable def Expr.denote (ctx : Context) : Expr → ℝ
  | .atom a => a.denote ctx
  | .neg a => -a.denote ctx
  | .add a b => a.denote ctx + b.denote ctx
  | .sub a b => a.denote ctx - b.denote ctx
  | .mul a b => a.denote ctx * b.denote ctx
  | .pow a n => a.denote ctx ^ n
  | .divNat a n => a.denote ctx / (n : ℝ)

structure Scaled where
  den : Nat
  num : RingExpr

def Expr.normalize : Expr → Scaled
  | .atom a => ⟨1, a⟩
  | .neg a => let a := a.normalize; ⟨a.den, .neg a.num⟩
  | .add a b =>
      let a := a.normalize; let b := b.normalize
      let d := Nat.lcm a.den b.den
      ⟨d, .add (.mul (.natCast (d / a.den)) a.num)
        (.mul (.natCast (d / b.den)) b.num)⟩
  | .sub a b =>
      let a := a.normalize; let b := b.normalize
      let d := Nat.lcm a.den b.den
      ⟨d, .sub (.mul (.natCast (d / a.den)) a.num)
        (.mul (.natCast (d / b.den)) b.num)⟩
  | .mul a b =>
      let a := a.normalize; let b := b.normalize
      ⟨a.den * b.den, .mul a.num b.num⟩
  | .pow a n => let a := a.normalize; ⟨a.den ^ n, .pow a.num n⟩
  | .divNat a n =>
      if n = 0 then ⟨1, .num 0⟩
      else let a := a.normalize; ⟨a.den * n, a.num⟩

private theorem cast_div_of_dvd {a d : Nat} (ha : 0 < a) (h : a ∣ d) :
    ((d / a : Nat) : ℝ) = (d : ℝ) / (a : ℝ) := by
  apply (eq_div_iff (by exact_mod_cast ha.ne' : (a : ℝ) ≠ 0)).2
  exact_mod_cast Nat.div_mul_cancel h

private theorem lcm_add (a b : Nat) (ha : 0 < a) (hb : 0 < b) (x y : ℝ) :
    x / (a : ℝ) + y / (b : ℝ) =
      (((Nat.lcm a b / a : Nat) : ℝ) * x +
        ((Nat.lcm a b / b : Nat) : ℝ) * y) / (Nat.lcm a b : ℝ) := by
  rw [cast_div_of_dvd ha (Nat.dvd_lcm_left a b),
    cast_div_of_dvd hb (Nat.dvd_lcm_right a b)]
  have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast ha.ne'
  have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  have hd' : (Nat.lcm a b : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.lcm_pos ha hb).ne'
  field_simp

private theorem lcm_sub (a b : Nat) (ha : 0 < a) (hb : 0 < b) (x y : ℝ) :
    x / (a : ℝ) - y / (b : ℝ) =
      (((Nat.lcm a b / a : Nat) : ℝ) * x -
        ((Nat.lcm a b / b : Nat) : ℝ) * y) / (Nat.lcm a b : ℝ) := by
  simpa [sub_eq_add_neg, neg_div] using lcm_add a b ha hb x (-y)

theorem Expr.normalize_spec (ctx : Context) (e : Expr) :
    0 < e.normalize.den ∧
      e.denote ctx = e.normalize.num.denote ctx / (e.normalize.den : ℝ) := by
  induction e with
  | atom a => simp [normalize, denote]
  | neg a ih =>
      refine ⟨ih.1, ?_⟩
      change -a.denote ctx = -a.normalize.num.denote ctx / (a.normalize.den : ℝ)
      rw [ih.2, neg_div]
  | add a b iha ihb =>
      refine ⟨Nat.lcm_pos iha.1 ihb.1, ?_⟩
      change a.denote ctx + b.denote ctx = _
      rw [iha.2, ihb.2]
      exact lcm_add _ _ iha.1 ihb.1 _ _
  | sub a b iha ihb =>
      refine ⟨Nat.lcm_pos iha.1 ihb.1, ?_⟩
      change a.denote ctx - b.denote ctx = _
      rw [iha.2, ihb.2]
      exact lcm_sub _ _ iha.1 ihb.1 _ _
  | mul a b iha ihb =>
      refine ⟨Nat.mul_pos iha.1 ihb.1, ?_⟩
      change a.denote ctx * b.denote ctx =
        (a.normalize.num.denote ctx * b.normalize.num.denote ctx) /
          ((a.normalize.den * b.normalize.den : Nat) : ℝ)
      rw [iha.2, ihb.2, Nat.cast_mul, mul_div_mul_comm]
  | pow a n ih =>
      refine ⟨Nat.pow_pos ih.1, ?_⟩
      change a.denote ctx ^ n = a.normalize.num.denote ctx ^ n /
        ((a.normalize.den ^ n : Nat) : ℝ)
      rw [ih.2, div_pow, Nat.cast_pow]
  | divNat a n ih =>
      by_cases hn : n = 0
      · subst n
        simp [normalize, denote, Lean.Grind.CommRing.Expr.denote,
          Lean.Grind.CommRing.denoteInt_eq]
      · refine ⟨?_, ?_⟩
        · simpa [normalize, hn] using Nat.mul_pos ih.1 (Nat.pos_of_ne_zero hn)
        · change a.denote ctx / (n : ℝ) = _
          simp only [normalize, hn, ↓reduceIte]
          rw [ih.2, Nat.cast_mul, div_div]

def check (a b : Expr) : Bool :=
  let a := a.normalize; let b := b.normalize
  (Lean.Grind.CommRing.Expr.mul a.num (.natCast b.den)).toPoly ==
    (Lean.Grind.CommRing.Expr.mul b.num (.natCast a.den)).toPoly

theorem eq_of_check (ctx : Context) (a b : Expr) (h : check a b = true) :
    a.denote ctx = b.denote ctx := by
  have ha := a.normalize_spec ctx
  have hb := b.normalize_spec ctx
  have ha' : (a.normalize.den : ℝ) ≠ 0 := by exact_mod_cast ha.1.ne'
  have hb' : (b.normalize.den : ℝ) ≠ 0 := by exact_mod_cast hb.1.ne'
  rw [ha.2, hb.2]
  apply (div_eq_div_iff ha' hb').2
  exact Lean.Grind.CommRing.Expr.eq_of_toPoly_eq ctx
    (.mul a.normalize.num (.natCast b.normalize.den))
    (.mul b.normalize.num (.natCast a.normalize.den)) h


end CourtadeKumar.NativePolynomialNormalization

open Lean Meta Elab Tactic

namespace CourtadeKumar.NativePolynomialNormalization.Tactic

private abbrev ReifyM := StateRefT (Array Lean.Expr) MetaM

private def atom (e : Lean.Expr) : ReifyM Lean.Expr := do
  let atoms ← get
  if let some index := atoms.findIdx? (· == e) then
    return mkApp (mkConst ``CourtadeKumar.NativePolynomialNormalization.Expr.atom)
      (mkApp (mkConst ``Lean.Grind.CommRing.Expr.var) (toExpr index))
  modify (·.push e)
  return mkApp (mkConst ``CourtadeKumar.NativePolynomialNormalization.Expr.atom)
    (mkApp (mkConst ``Lean.Grind.CommRing.Expr.var) (toExpr atoms.size))

private partial def reify (e : Lean.Expr) : ReifyM Lean.Expr := do
  let e := e.consumeMData
  match_expr e with
  | OfNat.ofNat _ n _ =>
    return mkApp (mkConst ``CourtadeKumar.NativePolynomialNormalization.Expr.atom)
      (mkApp (mkConst ``Lean.Grind.CommRing.Expr.num) (mkApp (mkConst ``Int.ofNat) n))
  | NatCast.natCast _ _ n =>
    if !n.hasFVar && !n.hasMVar then
      return mkApp (mkConst ``CourtadeKumar.NativePolynomialNormalization.Expr.atom)
        (mkApp (mkConst ``Lean.Grind.CommRing.Expr.natCast) n)
    else atom e
  | Nat.cast _ _ n =>
    if !n.hasFVar && !n.hasMVar then
      return mkApp (mkConst ``CourtadeKumar.NativePolynomialNormalization.Expr.atom)
        (mkApp (mkConst ``Lean.Grind.CommRing.Expr.natCast) n)
    else atom e
  | IntCast.intCast _ _ n =>
    if !n.hasFVar && !n.hasMVar then
      return mkApp (mkConst ``CourtadeKumar.NativePolynomialNormalization.Expr.atom)
        (mkApp (mkConst ``Lean.Grind.CommRing.Expr.intCast) n)
    else atom e
  | Int.cast _ _ n =>
    if !n.hasFVar && !n.hasMVar then
      return mkApp (mkConst ``CourtadeKumar.NativePolynomialNormalization.Expr.atom)
        (mkApp (mkConst ``Lean.Grind.CommRing.Expr.intCast) n)
    else atom e
  | HDiv.hDiv _ _ _ _ a b =>
    let den? := match_expr b.consumeMData with
      | OfNat.ofNat _ n _ => some n
      | Nat.cast _ _ n => some n
      | NatCast.natCast _ _ n => some n
      | _ => none
    if let some n := den? then
      if !n.hasFVar && !n.hasMVar then
        return mkApp2 (mkConst ``CourtadeKumar.NativePolynomialNormalization.Expr.divNat) (← reify a) n
    atom e
  | HAdd.hAdd _ _ _ _ a b =>
    return mkApp2 (mkConst ``CourtadeKumar.NativePolynomialNormalization.Expr.add) (← reify a) (← reify b)
  | HSub.hSub _ _ _ _ a b =>
    return mkApp2 (mkConst ``CourtadeKumar.NativePolynomialNormalization.Expr.sub) (← reify a) (← reify b)
  | HMul.hMul _ _ _ _ a b =>
    return mkApp2 (mkConst ``CourtadeKumar.NativePolynomialNormalization.Expr.mul) (← reify a) (← reify b)
  | Neg.neg _ _ a =>
    return mkApp (mkConst ``CourtadeKumar.NativePolynomialNormalization.Expr.neg) (← reify a)
  | HPow.hPow _ _ _ _ a n =>
    if !n.hasFVar && !n.hasMVar then
      return mkApp2 (mkConst ``CourtadeKumar.NativePolynomialNormalization.Expr.pow) (← reify a) n
    else atom e
  | _ => atom e

private def closePolynomial : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  let some (type, lhs, rhs) := target.eq? |
    throwError "kernel_ring expects an equality"
  unless ← isDefEq type (mkConst ``Real) do
    throwError "kernel_ring expects an equality of real expressions"
  let (a, atoms) ← (reify lhs).run #[]
  let (b, atoms) ← (reify rhs).run atoms
  let ctx ← if h : 0 < atoms.size then
    RArray.toExpr type id (RArray.ofFn (atoms[·]) h)
  else
    RArray.toExpr type id (RArray.leaf lhs)
  let check := mkApp2 (mkConst ``CourtadeKumar.NativePolynomialNormalization.check) a b
  let checked ← mkFreshExprMVar (← mkEq check (mkConst ``Bool.true))
  let proof ← mkAppM ``CourtadeKumar.NativePolynomialNormalization.eq_of_check
    #[ctx, a, b, checked]
  replaceMainGoal [checked.mvarId!]
  evalTactic (← `(tactic| decide +kernel))
  if ← isDefEq (← inferType proof) target then
    goal.assign proof
  else
    let hName ← mkFreshUserName `kernelPolynomialIdentity
    let next ← goal.assert hName (← inferType proof) proof
    let (_, next) ← next.intro1
    setGoals (next :: (← getGoals))
    evalTactic (← `(tactic|
      simpa [CourtadeKumar.NativePolynomialNormalization.Expr.denote,
        Lean.Grind.CommRing.Expr.denote, Lean.Grind.CommRing.denoteInt_eq,
        Lean.Grind.CommRing.Var.denote] using $(mkIdent hName)))

elab "kernel_ring" : tactic => focus do
  let target ← getMainTarget
  if target.getUsedConstants.contains ``Nat.choose then
    evalTactic (← `(tactic| simp (config := { failIfUnchanged := false }) only
      [Nat.choose_eq_descFactorial_div_factorial]))
  unless (← getGoals).isEmpty do
    closePolynomial

/-- Compatibility spelling; the proof is checked entirely by the kernel. -/
macro "native_ring" : tactic => `(tactic| kernel_ring)

end CourtadeKumar.NativePolynomialNormalization.Tactic
