import InformationTheory.CourtadeKumar.AnalyticExtension.CompactModel
import InformationTheory.CourtadeKumar.AnalyticExtension.CompactTangent
import InformationTheory.CourtadeKumar.AnalyticExtension.CompactADSound

/-! Connect the finite expression used by compact certificates to the original V reserve. -/
open Set
open scoped BigOperators
namespace CourtadeKumar.LRCompactReducedCertificate
open LRAnalyticCompact


lemma eval_sumExpr (f : Nat → Expr) (N : Nat) (env : Nat → ℝ) :
    (sumExpr f N).eval env = ∑ j ∈ Finset.range N, (f j).eval env := by
  induction N with
  | zero => simp [sumExpr, Expr.eval]
  | succ n ih => simp only [sumExpr, Expr.eval, Finset.sum_range_succ, ih]

lemma eval_shapeExpr (n : Nat) (R v t B aT au ac L : ℝ) :
    (shapeExpr n).eval (realEnv R v t B aT au ac L) = lrCompactVT v (t^2) n := by
  simp [shapeExpr, Expr.eval, realEnv, lrCompactVT, pow_mul]

lemma eval_channelExpr (n : Nat) (hn : 1 ≤ n) (R v t B aT au ac L : ℝ) :
    (channelExpr n).eval (realEnv R v t B aT au ac L) = channelU R n := by
  rw [channelU_formula R hn]
  simp [channelExpr, Expr.eval, realEnv, Nat.cast_sub hn]

lemma eval_dExpr (M : Nat) (R v t B aT au ac L : ℝ) :
    (dExpr M).eval (realEnv R v t B aT au ac L) = dPartial M (dCoordinate R v t) := by
  simp [dExpr, eval_sumExpr, coordinateExpr, Expr.eval, realEnv, dPartial, dCoordinate]

lemma eval_qExpr (N : Nat) (R v t B aT au ac : ℝ) :
    (qExpr N).eval (realEnv R v t B aT au ac (Real.log 2)) =
    aT*t + au/v + ac - 4*v*t^2/(1+v)*Real.log 2 + restoredHead N R v (t^2) -
      tailDelta N * Real.log 2 := by
  simp [qExpr, Expr.eval, realEnv, eval_sumExpr, restoredHead, restoredTerm,
    channelU_formula, tailDelta, lrLowA, hExpr, channelExpr, shapeExpr, lrCompactVT, pow_mul]

lemma eval_cExpr (N : Nat) (R v t B aT au ac L : ℝ) :
    (cExpr N).eval (realEnv R v t B aT au ac L) =
      ∑ j ∈ Finset.range N, lrCompactVPsiTerm R v (t^2) (j+1) := by
  rw [cExpr, eval_sumExpr]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Expr.eval]
  rw [eval_channelExpr _ (by omega), eval_shapeExpr]
  simp [lrCompactVPsiTerm, lrLowA, lrCompactVC, channelU, gExpr, Expr.eval, realEnv]
  ring

lemma flowB_nonneg {R v t : ℝ} (hR : R ∈ Icc (0 : ℝ) (9/10))
    (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) : 0 ≤ lrFlowB R v t := by
  have hy := squared_shape_bounds hv ht
  have hRy := mul_le_mul_of_nonneg_right (show R ≤ 1 by linarith [hR.2]) hy.1
  have h1 : 0 < 1 - R*(v^2*t^2) := by linarith [hy.2]
  rw [flowB_formula hR.1 ht.1.le]
  have hpos := Real.log_nonneg (by linarith [hv.1] : 1 ≤ 1+v)
  have hneg := Real.log_nonpos h1.le (by nlinarith [mul_nonneg hR.1 hy.1])
  linarith

theorem target_le_reserve (N M : Nat) (hN : 1 ≤ N) {R v t a b aT au ac : ℝ}
    (hR : R ∈ Ioc (0 : ℝ) (9/10)) (hv : v ∈ Ioo (0 : ℝ) 1)
    (hvthird : 1/3 ≤ v) (ht : t ∈ Ioo (0 : ℝ) 1)
    (ha : a ∈ Ioo (-1 : ℝ) 1) (hb : b ∈ Ioo (-1 : ℝ) 1)
    (hat : aT ≤ Real.artanh a + Real.artanh b)
    (hau : au ≤ Real.log (1-b^2)/2) (hac : ac ≤ Real.log (1-a^2)/2) :
    (targetExpr N M).eval (realEnv R v t (lrFlowB R v t) aT au ac (Real.log 2)) ≤
      lrLowVReserve R v t := by
  have hRoo : R ∈ Ioo (0 : ℝ) 1 := ⟨hR.1, by linarith [hR.2]⟩
  have hRcc : R ∈ Icc (0 : ℝ) (9/10) := ⟨hR.1.le,hR.2⟩
  have hs := rational_shape_tangent ha hb hv ht hat hau hac
  have hq := restoredQLower_le hRoo hv hvthird ht hN
  have hq' : (qExpr N).eval (realEnv R v t (lrFlowB R v t) aT au ac (Real.log 2)) ≤
      lrFlowPW R v t - 4*lrWKernel R 1*(v*t^2/(1+v)) := by
    rw [eval_qExpr]
    unfold restoredQLower at hq
    linarith
  have hc := lrCompactVPsiTermHead_le_lrFlowC hRoo hv ht N
  have hc0 : 0 ≤ ∑ j ∈ Finset.range N, lrCompactVPsiTerm R v (t^2) (j+1) := by
    apply Finset.sum_nonneg
    intro j hj
    exact lrCompactVPsiTerm_nonneg ⟨hR.1.le,hRoo.2.le⟩ ⟨hv.1.le,hv.2.le⟩
      ⟨sq_nonneg t, by nlinarith [ht.1,ht.2]⟩ (by omega)
  have hd := dPartial_le_flowD M hRcc hv ht
  have hd0 := dPartial_nonneg M (coordinate_bounds hRcc hv ht).1
  change lrFlowB R v t * (qExpr N).eval (realEnv R v t (lrFlowB R v t) aT au ac (Real.log 2)) +
    (dExpr M).eval (realEnv R v t (lrFlowB R v t) aT au ac (Real.log 2)) *
    (cExpr N).eval (realEnv R v t (lrFlowB R v t) aT au ac (Real.log 2)) ≤ lrLowVReserve R v t
  rw [eval_dExpr, eval_cExpr, lrLowVReserve_eq_compact_grouped (by linarith [hv.1])]
  exact add_le_add (mul_le_mul_of_nonneg_left hq' (flowB_nonneg hRcc hv ht))
    (mul_le_mul hd hc hc0 (hd0.trans hd))

end CourtadeKumar.LRCompactReducedCertificate
