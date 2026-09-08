import InformationTheory.CourtadeKumar.AnalyticExtension.CompactADCore
import InformationTheory.CourtadeKumar.IntervalADArithmetic
import InformationTheory.CourtadeKumar.LRCompactVGroupedBilinear
import InformationTheory.CourtadeKumar.LRDeterminantUpperKDyadicOuterRoundingCore
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! Soundness of rounded interval differentiation along an arbitrary affine path.
The three stored derivative bounds are combined with the path's three velocities. -/
namespace CourtadeKumar.LRCompactReducedCertificate

lemma contains_rounded {a : RationalEnclosure} {x : ℝ} (h : a.Contains x) :
    (rounded a).Contains x := by
  constructor
  · exact le_trans (by exact_mod_cast LRUpperKDyadicOuterRounding.roundDown_le bits a.lower) h.1
  · exact le_trans h.2 (by exact_mod_cast LRUpperKDyadicOuterRounding.le_roundUp bits a.upper)

private lemma min4_le {a b c d x y : ℝ} (hx : a ≤ x ∧ x ≤ b) (hy : c ≤ y ∧ y ≤ d) :
    min (min (a*c) (b*c)) (min (a*d) (b*d)) ≤ x*y := by
  simpa [lrCompactVGroupedBilinearReal] using
    (lrCompactVGroupedBilinear_fourCornerMin_le (lambda := 0) (g := 0) (h := 0)
      hx.1 hx.2 hy.1 hy.2)

private lemma neg_minimum (a b : ℝ) : -min a b = max (-a) (-b) := by
  by_cases h : a ≤ b
  · rw [min_eq_left h, max_eq_left (neg_le_neg h)]
  · rw [min_eq_right (le_of_not_ge h), max_eq_right (neg_le_neg (le_of_not_ge h))]

lemma contains_mul4 {a b : RationalEnclosure} {x y : ℝ}
    (hx : a.Contains x) (hy : b.Contains y) : (mul4 a b).Contains (x*y) := by
  constructor
  · simpa [mul4] using min4_le hx hy
  · have h := min4_le (x := -x) ⟨neg_le_neg hx.2, neg_le_neg hx.1⟩ hy
    have h' := neg_le_neg h
    simpa [mul4, neg_minimum, max_comm, neg_mul] using h'

lemma contains_mulI {a b : RationalEnclosure} {x y : ℝ}
    (hx : a.Contains x) (hy : b.Contains y) : (mulI a b).Contains (x*y) :=
  contains_rounded (contains_mul4 hx hy)
lemma contains_addI {a b : RationalEnclosure} {x y : ℝ}
    (hx : a.Contains x) (hy : b.Contains y) : (addI a b).Contains (x+y) :=
  contains_rounded (RationalEnclosure.contains_add hx hy)
lemma contains_subI {a b : RationalEnclosure} {x y : ℝ}
    (hx : a.Contains x) (hy : b.Contains y) : (subI a b).Contains (x-y) :=
  contains_rounded (RationalEnclosure.contains_sub hx hy)
lemma contains_powI {a : RationalEnclosure} {x : ℝ}
    (ha : 0 ≤ a.lower) (hx : a.Contains x) (n : Nat) : (powI a n).Contains (x^n) := by
  apply contains_rounded
  have hlo : (0 : ℝ) ≤ a.lower := by exact_mod_cast ha
  constructor
  · simpa using pow_le_pow_left₀ hlo hx.1 n
  · simpa using pow_le_pow_left₀ (hlo.trans hx.1) hx.2 n

lemma rounded_lower_nonneg {a : RationalEnclosure} (ha : 0 ≤ a.lower) :
    0 ≤ (rounded a).lower := by
  unfold rounded LRUpperKDyadicOuterRounding.outerEnclosure LRUpperKDyadicOuterRounding.roundDown
  exact div_nonneg (by exact_mod_cast (Int.floor_nonneg.mpr
    (mul_nonneg ha (LRUpperKDyadicOuterRounding.scale_pos bits).le)))
    (LRUpperKDyadicOuterRounding.scale_pos bits).le

lemma contains_absBound {a : RationalEnclosure} {x : ℝ} (hx : a.Contains x) :
    |x| ≤ (absBound a : ℝ) := by
  rw [abs_le]
  have hlo : |(a.lower : ℝ)| ≤ (absBound a : ℝ) := by
    exact_mod_cast (le_max_left (abs a.lower) (abs a.upper))
  have hhi : |(a.upper : ℝ)| ≤ (absBound a : ℝ) := by
    exact_mod_cast (le_max_right (abs a.lower) (abs a.upper))
  exact ⟨(neg_le_neg hlo).trans ((neg_abs_le _).trans hx.1), hx.2.trans ((le_abs_self _).trans hhi)⟩

/-- The interval jet encloses a value and three coefficients whose weighted sum
is the derivative along a path. Positivity guards are checked by each operation. -/
def Jet.Models (a : Jet) (f : ℝ → ℝ) (z r v t : ℝ) : Prop :=
  ∃ ds dk dc, a.bounds.Contains (f z) ds dk dc ∧
    HasDerivAt f (ds*r + dk*v + dc*t) z

namespace Jet
variable {a b : Jet} {f g : ℝ → ℝ} {z r v t : ℝ}

lemma models_const (q : ℚ) : (const q).Models (fun _ => (q : ℝ)) z r v t := by
  refine ⟨0,0,0,IntervalAD.contains_const q,?_⟩
  simpa using hasDerivAt_const z (q : ℝ)

lemma models_add (ha : a.Models f z r v t) (hb : b.Models g z r v t) :
    (a.add b).Models (fun x => f x + g x) z r v t := by
  rcases ha with ⟨as,ak,ac,ha,hda⟩; rcases hb with ⟨bs,bk,bc,hb,hdb⟩
  refine ⟨as+bs,ak+bk,ac+bc,⟨contains_addI ha.1 hb.1, contains_addI ha.2.1 hb.2.1,
    contains_addI ha.2.2.1 hb.2.2.1, contains_addI ha.2.2.2 hb.2.2.2⟩,?_⟩
  convert hda.add hdb using 1 <;> ring

lemma models_sub (ha : a.Models f z r v t) (hb : b.Models g z r v t) :
    (a.sub b).Models (fun x => f x - g x) z r v t := by
  rcases ha with ⟨as,ak,ac,ha,hda⟩; rcases hb with ⟨bs,bk,bc,hb,hdb⟩
  refine ⟨as-bs,ak-bk,ac-bc,⟨contains_subI ha.1 hb.1, contains_subI ha.2.1 hb.2.1,
    contains_subI ha.2.2.1 hb.2.2.1, contains_subI ha.2.2.2 hb.2.2.2⟩,?_⟩
  convert hda.sub hdb using 1 <;> ring

lemma models_mul (ha : a.Models f z r v t) (hb : b.Models g z r v t) :
    (a.mul b).Models (fun x => f x * g x) z r v t := by
  rcases ha with ⟨as,ak,ac,ha,hda⟩; rcases hb with ⟨bs,bk,bc,hb,hdb⟩
  refine ⟨as*g z+f z*bs,ak*g z+f z*bk,ac*g z+f z*bc,⟨contains_mulI ha.1 hb.1,
    contains_addI (contains_mulI ha.2.1 hb.1) (contains_mulI ha.1 hb.2.1),
    contains_addI (contains_mulI ha.2.2.1 hb.1) (contains_mulI ha.1 hb.2.2.1),
    contains_addI (contains_mulI ha.2.2.2 hb.1) (contains_mulI ha.1 hb.2.2.2)⟩,?_⟩
  convert hda.mul hdb using 1 <;> ring

lemma models_inv (ha : a.Models f z r v t) (hp : 0 < a.bounds.value.lower) :
    a.inv.Models (fun x => (f x)⁻¹) z r v t := by
  rcases ha with ⟨as,ak,ac,ha,hda⟩
  have hp' : 0 < f z := lt_of_lt_of_le (by exact_mod_cast hp) ha.1.1
  have hv := contains_rounded (RationalEnclosure.contains_invPositive hp ha.1)
  have hnon : 0 ≤ (rounded (RationalEnclosure.invPositive a.bounds.value)).lower := by
    apply rounded_lower_nonneg
    change 0 ≤ a.bounds.value.upper⁻¹
    have hu : (0 : ℝ) < a.bounds.value.upper := hp'.trans_le ha.1.2
    exact inv_nonneg.mpr (by exact_mod_cast hu.le)
  have hslope := RationalEnclosure.contains_neg (contains_powI hnon hv 2)
  refine ⟨-((f z)⁻¹)^2*as,-((f z)⁻¹)^2*ak,-((f z)⁻¹)^2*ac,
    ⟨hv,contains_mulI hslope ha.2.1,contains_mulI hslope ha.2.2.1,
      contains_mulI hslope ha.2.2.2⟩,?_⟩
  convert hda.inv hp'.ne' using 1 <;> simp only [div_eq_mul_inv, inv_pow] <;> ring

lemma models_div (ha : a.Models f z r v t) (hb : b.Models g z r v t)
    (hp : 0 < b.bounds.value.lower) :
    (a.div b).Models (fun x => f x / g x) z r v t := by
  simpa only [div_eq_mul_inv] using models_mul ha (models_inv hb hp)

lemma models_pow (ha : a.Models f z r v t) (hp : 0 ≤ a.bounds.value.lower) (n : Nat) :
    (a.pow n).Models (fun x => f x ^ n) z r v t := by
  rcases ha with ⟨as,ak,ac,ha,hda⟩
  have hslope := contains_mulI (RationalEnclosure.contains_point (n : ℚ))
    (contains_powI hp ha.1 (n-1))
  norm_cast at hslope
  refine ⟨(n:ℝ)*f z^(n-1)*as,(n:ℝ)*f z^(n-1)*ak,(n:ℝ)*f z^(n-1)*ac,
    ⟨contains_powI hp ha.1 n,contains_mulI hslope ha.2.1,
      contains_mulI hslope ha.2.2.1,contains_mulI hslope ha.2.2.2⟩,?_⟩
  convert hda.pow n using 1 <;> ring

lemma models_logWith (ha : a.Models f z r v t) (hp : 0 < a.bounds.value.lower)
    {value : RationalEnclosure} (hv : value.Contains (Real.log (f z))) :
    (a.logWith value).Models (fun x => Real.log (f x)) z r v t := by
  rcases ha with ⟨as,ak,ac,ha,hda⟩
  have hp' : 0 < f z := lt_of_lt_of_le (by exact_mod_cast hp) ha.1.1
  have hslope := contains_rounded (RationalEnclosure.contains_invPositive hp ha.1)
  refine ⟨(f z)⁻¹*as,(f z)⁻¹*ak,(f z)⁻¹*ac,
    ⟨hv,contains_mulI hslope ha.2.1,contains_mulI hslope ha.2.2.1,
      contains_mulI hslope ha.2.2.2⟩,?_⟩
  convert hda.log hp'.ne' using 1 <;> simp only [div_eq_mul_inv] <;> ring

end Jet

noncomputable def Expr.eval (env : Nat → ℝ) : Expr → ℝ
  | .rat q => (q : ℝ)
  | .var i => env i
  | .add a b => a.eval env + b.eval env
  | .sub a b => a.eval env - b.eval env
  | .mul a b => a.eval env * b.eval env
  | .div a b => a.eval env / b.eval env
  | .pow a n => a.eval env ^ n

theorem Expr.models (e : Expr) {env : Nat → Jet} {fs : Nat → ℝ → ℝ} {z r v t : ℝ}
    (henv : ∀ i, (env i).Models (fs i) z r v t)
    (hcheck : (e.enclose env).valid = true) :
    (e.enclose env).Models (fun x => e.eval (fun i => fs i x)) z r v t := by
  induction e with
  | rat q => exact Jet.models_const q
  | var i => exact henv i
  | add a b ia ib =>
    have h := Bool.and_eq_true_iff.mp hcheck
    exact Jet.models_add (ia h.1) (ib h.2)
  | sub a b ia ib =>
    have h := Bool.and_eq_true_iff.mp hcheck
    exact Jet.models_sub (ia h.1) (ib h.2)
  | mul a b ia ib =>
    have h := Bool.and_eq_true_iff.mp hcheck
    exact Jet.models_mul (ia h.1) (ib h.2)
  | div a b ia ib =>
    have h := Bool.and_eq_true_iff.mp hcheck
    have hb := Bool.and_eq_true_iff.mp h.2
    exact Jet.models_div (ia h.1) (ib hb.1) (by simpa using hb.2)
  | pow a n ia =>
    have h := Bool.and_eq_true_iff.mp hcheck
    exact Jet.models_pow (ia h.1) (by simpa using h.2) n

noncomputable def realEnv (R v t B aT au ac L : ℝ) : Nat → ℝ
  | 0 => R | 1 => v | 2 => t | 3 => B
  | 4 => aT | 5 => au | 6 => ac | 7 => L | _ => 0

end CourtadeKumar.LRCompactReducedCertificate
