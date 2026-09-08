import InformationTheory.CourtadeKumar.AnalyticExtension.CompactIntegerCore
import InformationTheory.CourtadeKumar.AnalyticExtension.CompactADSound

namespace CourtadeKumar.LRCompactIntegerCertificate

lemma scale_pos : 0 < scale := by norm_num [scale]
lemma scale_real_pos : (0 : ℝ) < scale := by exact_mod_cast scale_pos
lemma scale_rat_pos : (0 : ℚ) < scale := by exact_mod_cast scale_pos

lemma contains_iff (a : I) (x : ℝ) : a.decode.Contains x ↔
    (a.lower : ℝ) ≤ x * (scale : ℝ) ∧ x * (scale : ℝ) ≤ a.upper := by
  simp only [I.decode, RationalEnclosure.Contains, Rat.cast_div, Rat.cast_intCast,
    div_le_iff₀ scale_real_pos, le_div_iff₀ scale_real_pos]

lemma ediv_real_le (a b : ℤ) (hb : 0 < b) :
    ((a / b : ℤ) : ℝ) ≤ (a : ℝ) / (b : ℝ) := by
  apply (le_div_iff₀ (show (0 : ℝ) < b by exact_mod_cast hb)).mpr
  exact_mod_cast (show a / b * b ≤ a by simpa [mul_comm] using
    (Int.mul_ediv_self_le (x := a) hb.ne'))

lemma le_cdiv_real (a b : ℤ) (hb : 0 < b) :
    (a : ℝ) / (b : ℝ) ≤ (-((-a) / b) : ℤ) := by
  have h := neg_le_neg (ediv_real_le (-a) b hb)
  simpa only [Int.cast_neg, neg_div, neg_neg] using h

lemma contains_fromRat {a : RationalEnclosure} {x : ℝ} (hx : a.Contains x) :
    (fromRat a).decode.Contains x := by
  rw [contains_iff]
  have hl : ((Int.floor (a.lower * (scale : ℚ)) : ℤ) : ℚ) ≤ a.lower * (scale : ℚ) := Int.floor_le _
  have hu : a.upper * (scale : ℚ) ≤ ((Int.ceil (a.upper * (scale : ℚ)) : ℤ) : ℚ) := Int.le_ceil _
  have hlr : ((Int.floor (a.lower * (scale : ℚ)) : ℤ) : ℝ) ≤ (a.lower : ℝ) * (scale : ℝ) := by exact_mod_cast hl
  have hur : (a.upper : ℝ) * (scale : ℝ) ≤ ((Int.ceil (a.upper * (scale : ℚ)) : ℤ) : ℝ) := by exact_mod_cast hu
  exact ⟨hlr.trans (mul_le_mul_of_nonneg_right hx.1 scale_real_pos.le),
    (mul_le_mul_of_nonneg_right hx.2 scale_real_pos.le).trans hur⟩

lemma contains_pointI (q : ℚ) : (pointI q).decode.Contains (q : ℝ) :=
  contains_fromRat (RationalEnclosure.contains_point q)

lemma contains_addBase {a b : I} {x y : ℝ}
    (hx : a.decode.Contains x) (hy : b.decode.Contains y) :
    (addBase a b).decode.Contains (x+y) := by
  rw [contains_iff] at hx hy ⊢
  simpa only [addBase, Int.cast_add, add_mul] using And.intro
    (add_le_add hx.1 hy.1) (add_le_add hx.2 hy.2)

lemma zero_of_contains {a : I} {x : ℝ}
    (h : a.lower = 0 ∧ a.upper = 0) (hx : a.decode.Contains x) : x = 0 := by
  rw [contains_iff] at hx
  simp only [h.1,h.2,Int.cast_zero] at hx
  exact (mul_eq_zero.mp (le_antisymm hx.2 hx.1)).resolve_right scale_real_pos.ne'

lemma contains_zero : (⟨0,0⟩ : I).decode.Contains (0 : ℝ) := by
  rw [contains_iff]
  simp

lemma contains_addI {a b : I} {x y : ℝ}
    (hx : a.decode.Contains x) (hy : b.decode.Contains y) :
    (addI a b).decode.Contains (x+y) := by
  unfold addI
  split_ifs with ha hb
  · simpa only [zero_of_contains ha hx, zero_add] using hy
  · simpa only [zero_of_contains hb hy, add_zero] using hx
  · exact contains_addBase hx hy

lemma contains_subI {a b : I} {x y : ℝ}
    (hx : a.decode.Contains x) (hy : b.decode.Contains y) :
    (subI a b).decode.Contains (x-y) := by
  rw [contains_iff] at hx hy ⊢
  simpa only [subI, Int.cast_sub, sub_mul] using And.intro
    (sub_le_sub hx.1 hy.2) (sub_le_sub hx.2 hy.1)

lemma contains_negI {a : I} {x : ℝ} (hx : a.decode.Contains x) :
    (negI a).decode.Contains (-x) := by
  rw [contains_iff] at hx ⊢
  simpa only [negI, Int.cast_neg, neg_mul] using And.intro
    (neg_le_neg hx.2) (neg_le_neg hx.1)

lemma contains_mulBase {a b : I} {x y : ℝ}
    (hx : a.decode.Contains x) (hy : b.decode.Contains y) :
    (mulBase a b).decode.Contains (x*y) := by
  rw [contains_iff] at hx hy ⊢
  let l := min (min (a.lower*b.lower) (a.upper*b.lower))
    (min (a.lower*b.upper) (a.upper*b.upper))
  let u := max (max (a.lower*b.lower) (a.upper*b.lower))
    (max (a.lower*b.upper) (a.upper*b.upper))
  have hraw := LRCompactReducedCertificate.contains_mul4
    (a := ⟨(a.lower : ℚ), (a.upper : ℚ)⟩)
    (b := ⟨(b.lower : ℚ), (b.upper : ℚ)⟩)
    (x := x * (scale : ℝ)) (y := y * (scale : ℝ))
    (by simpa using hx) (by simpa using hy)
  have hlow : (l : ℝ) ≤ (x * (scale : ℝ)) * (y * (scale : ℝ)) := by
    simpa only [l, LRCompactReducedCertificate.mul4, Rat.cast_min, Rat.cast_mul,
      Rat.cast_intCast, Int.cast_min, Int.cast_mul] using hraw.1
  have hupp : (x * (scale : ℝ)) * (y * (scale : ℝ)) ≤ (u : ℝ) := by
    simpa only [u, LRCompactReducedCertificate.mul4, Rat.cast_max, Rat.cast_mul,
      Rat.cast_intCast, Int.cast_max, Int.cast_mul] using hraw.2
  have hlo := ediv_real_le l scale scale_pos
  have hhi := le_cdiv_real u scale scale_pos
  constructor
  · exact hlo.trans ((div_le_iff₀ scale_real_pos).mpr (by nlinarith [hlow]))
  · exact ((le_div_iff₀ scale_real_pos).mpr (by nlinarith [hupp])).trans hhi

lemma contains_mulI {a b : I} {x y : ℝ}
    (hx : a.decode.Contains x) (hy : b.decode.Contains y) :
    (mulI a b).decode.Contains (x*y) := by
  unfold mulI
  split_ifs with hb ha
  · simpa only [zero_of_contains hb hy, mul_zero] using contains_zero
  · simpa only [zero_of_contains ha hx, zero_mul] using contains_zero
  · exact contains_mulBase hx hy

lemma contains_powI {a : I} {x : ℝ} (hx : a.decode.Contains x) (n : Nat) :
    (powI a n).decode.Contains (x^n) := by
  induction n with
  | zero =>
    rw [powI, contains_iff]
    simp
  | succ n ih =>
    simpa only [powI, pow_succ] using contains_mulI ih hx

lemma contains_invI {a : I} {x : ℝ} (hx : a.decode.Contains x) (hp : 0 < a.lower) :
    (invI a).decode.Contains (x⁻¹) := by
  rw [contains_iff] at hx ⊢
  have hlo : (0 : ℝ) < a.lower := by exact_mod_cast hp
  have hxs : 0 < x * (scale : ℝ) := hlo.trans_le hx.1
  have hxp : 0 < x := (mul_pos_iff_of_pos_right scale_real_pos).mp hxs
  have hupper : (0 : ℝ) < a.upper := hxs.trans_le hx.2
  have hupper' : 0 < a.upper := by exact_mod_cast hupper
  have hl := ediv_real_le (scale^2) a.upper hupper'
  have hu := le_cdiv_real (scale^2) a.lower hp
  have hl' : ((scale^2 : ℤ) : ℝ) / (a.upper : ℝ) ≤ x⁻¹ * (scale : ℝ) := by
    rw [Int.cast_pow, div_le_iff₀ hupper]
    have hh := mul_le_mul_of_nonneg_left hx.2 (mul_nonneg (inv_nonneg.mpr hxp.le) scale_real_pos.le)
    field_simp [hxp.ne'] at hh ⊢
    nlinarith [hh]
  have hu' : x⁻¹ * (scale : ℝ) ≤ ((scale^2 : ℤ) : ℝ) / (a.lower : ℝ) := by
    rw [Int.cast_pow, le_div_iff₀ hlo]
    have hh := mul_le_mul_of_nonneg_left hx.1 (mul_nonneg (inv_nonneg.mpr hxp.le) scale_real_pos.le)
    field_simp [hxp.ne'] at hh ⊢
    nlinarith [hh]
  exact ⟨hl.trans hl', hu'.trans hu⟩


abbrev Jet.Models (a : Jet) (f : ℝ → ℝ) (z r v t : ℝ) : Prop :=
  a.decode.Models f z r v t

lemma Jet.models_fromRat {a : LRCompactReducedCertificate.Jet} {f : ℝ → ℝ}
    {z r v t : ℝ} (ha : a.Models f z r v t) : (Jet.fromRat a).Models f z r v t := by
  rcases ha with ⟨ds,dk,dc,h,hd⟩
  exact ⟨ds,dk,dc,⟨contains_fromRat h.1, contains_fromRat h.2.1,
    contains_fromRat h.2.2.1, contains_fromRat h.2.2.2⟩,hd⟩

namespace Jet
variable {a b : Jet} {f g : ℝ → ℝ} {z r v t : ℝ}

lemma models_const (q : ℚ) : (const q).Models (fun _ => (q : ℝ)) z r v t := by
  refine ⟨0,0,0,⟨contains_pointI q, ?_, ?_, ?_⟩,?_⟩
  · simpa only [Rat.cast_zero] using contains_pointI 0
  · simpa only [Rat.cast_zero] using contains_pointI 0
  · simpa only [Rat.cast_zero] using contains_pointI 0
  · simpa using hasDerivAt_const z (q : ℝ)
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
  have hscaled := (contains_iff a.bounds.value (f z)).mp ha.1
  have hp' : 0 < f z := (mul_pos_iff_of_pos_right scale_real_pos).mp
    (lt_of_lt_of_le (by exact_mod_cast hp) hscaled.1)
  have hv := contains_invI ha.1 hp
  have hslope := contains_negI (contains_powI hv 2)
  refine ⟨-((f z)⁻¹)^2*as,-((f z)⁻¹)^2*ak,-((f z)⁻¹)^2*ac,
    ⟨hv,contains_mulI hslope ha.2.1,contains_mulI hslope ha.2.2.1,
      contains_mulI hslope ha.2.2.2⟩,?_⟩
  convert hda.inv hp'.ne' using 1 <;> simp only [div_eq_mul_inv, inv_pow] <;> ring

lemma models_div (ha : a.Models f z r v t) (hb : b.Models g z r v t)
    (hp : 0 < b.bounds.value.lower) :
    (a.div b).Models (fun x => f x / g x) z r v t := by
  simpa only [div_eq_mul_inv] using models_mul ha (models_inv hb hp)

lemma models_pow (ha : a.Models f z r v t) (n : Nat) :
    (a.pow n).Models (fun x => f x ^ n) z r v t := by
  rcases ha with ⟨as,ak,ac,ha,hda⟩
  have hslope := contains_mulI (contains_pointI (n : ℚ))
    (contains_powI ha.1 (n-1))
  norm_cast at hslope
  refine ⟨(n:ℝ)*f z^(n-1)*as,(n:ℝ)*f z^(n-1)*ak,(n:ℝ)*f z^(n-1)*ac,
    ⟨contains_powI ha.1 n,contains_mulI hslope ha.2.1,
      contains_mulI hslope ha.2.2.1,contains_mulI hslope ha.2.2.2⟩,?_⟩
  convert hda.pow n using 1 <;> ring


end Jet

theorem enclose_models (e : LRCompactReducedCertificate.Expr) {env : Nat → Jet} {fs : Nat → ℝ → ℝ} {z r v t : ℝ}
    (henv : ∀ i, (env i).Models (fs i) z r v t)
    (hcheck : (enclose env e).valid = true) :
    (enclose env e).Models (fun x => e.eval (fun i => fs i x)) z r v t := by
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
    exact Jet.models_pow (ia hcheck) n


end CourtadeKumar.LRCompactIntegerCertificate
