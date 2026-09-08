import InformationTheory.CourtadeKumar.AnalyticExtension.MidpointRationalCheckerCore
import InformationTheory.CourtadeKumar.ExactLogEnclosure

/-! General soundness of the small rational expression checker and of its
rounded endpoint logarithms. No numerical data is imported here. -/
namespace CourtadeKumar.LRMidpointReducedCertificate

noncomputable def Expr.eval (env : Nat → ℝ) : Expr → ℝ
  | .rat q => (q : ℝ)
  | .var i => env i
  | .add a b => a.eval env + b.eval env
  | .sub a b => a.eval env - b.eval env
  | .mul a b => a.eval env * b.eval env
  | .div a b => a.eval env / b.eval env

theorem contains_tightMul {a b : RationalEnclosure} {x y : ℝ}
    (hx : a.Contains x) (hy : b.Contains y) : (tightMul a b).Contains (x * y) := by
  unfold tightMul
  split
  · rename_i h
    exact RationalEnclosure.contains_mulNonnegative h.1 h.2 hx hy
  · exact RationalEnclosure.contains_mul hx hy

theorem Expr.sound (e : Expr) {env : Nat → RationalEnclosure} {values : Nat → ℝ}
    (henv : ∀ i, (env i).Contains (values i)) (hcheck : e.valid env = true) :
    (e.enclose env).Contains (e.eval values) := by
  induction e with
  | rat q => exact RationalEnclosure.contains_point q
  | var i => exact henv i
  | add a b ia ib =>
    have h := Bool.and_eq_true_iff.mp hcheck
    exact RationalEnclosure.contains_add (ia h.1) (ib h.2)
  | sub a b ia ib =>
    have h := Bool.and_eq_true_iff.mp hcheck
    exact RationalEnclosure.contains_sub (ia h.1) (ib h.2)
  | mul a b ia ib =>
    have h := Bool.and_eq_true_iff.mp hcheck
    exact contains_tightMul (ia h.1) (ib h.2)
  | div a b ia ib =>
    have h := Bool.and_eq_true_iff.mp hcheck
    have hb := Bool.and_eq_true_iff.mp h.2
    have hpos : (0 : ℚ) < (b.enclose env).lower := by simpa using hb.2
    simpa [Expr.enclose, Expr.eval, div_eq_mul_inv] using
      contains_tightMul (ia h.1) (RationalEnclosure.contains_invPositive hpos (ib hb.1))

theorem RoundedLog.sound {r : RoundedLog} {x : ℚ} (h : r.check x = true) :
    (r.lower : ℝ) ≤ Real.log (x : ℝ) ∧ Real.log (x : ℝ) ≤ (r.upper : ℝ) := by
  have hparts := Bool.and_eq_true_iff.mp h
  have he := r.range.sound 10 hparts.1
  have hbounds : r.lower ≤ (r.range.enclosure 10).lower ∧
      (r.range.enclosure 10).upper ≤ r.upper := by simpa using hparts.2
  have hlo : (r.lower : ℝ) ≤ ((r.range.enclosure 10).lower : ℝ) := by exact_mod_cast hbounds.1
  have hhi : ((r.range.enclosure 10).upper : ℝ) ≤ (r.upper : ℝ) := by exact_mod_cast hbounds.2
  exact ⟨hlo.trans he.1, he.2.trans hhi⟩

end CourtadeKumar.LRMidpointReducedCertificate
