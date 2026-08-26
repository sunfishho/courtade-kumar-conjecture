import InformationTheory.CourtadeKumar.LRSmallVTailAssembly

/-!
# Elementary bounds for the small-odds entry comparison

These estimates replace the infinite coefficient expansion of `ℒ₂` by
two geometric majorants.  The resulting constants are sharp enough on
`v ≤ 1/3`.
-/

open Set

namespace CourtadeKumar

lemma lrL_le_geometric
    {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z < 1) :
    lrL z ≤ z ^ 2 / (2 * (1 - z ^ 2)) := by
  have hzMem : z ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith, hz1⟩
  have hzSq0 : 0 ≤ z ^ 2 := sq_nonneg z
  have hzSq1 : z ^ 2 < 1 := by
    have hprod : 0 < (1 - z) * (1 + z) :=
      mul_pos (sub_pos.mpr hz1) (by linarith)
    nlinarith
  let g : ℕ → ℝ := fun n ↦ (z ^ 2 / 2) * (z ^ 2) ^ n
  have hg : HasSum g (z ^ 2 / (2 * (1 - z ^ 2))) := by
    have hgeom := (hasSum_geometric_of_lt_one hzSq0 hzSq1).mul_left (z ^ 2 / 2)
    simpa [g, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hgeom
  have hL := lrL_hasSum hzMem
  rw [← hL.tsum_eq, ← hg.tsum_eq]
  exact hL.summable.tsum_le_tsum (fun n ↦ by
    have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by
      exact_mod_cast (show 1 ≤ n + 1 by omega)
    have hpow : 0 ≤ z ^ (2 * (n + 1)) := pow_nonneg hz0 _
    have hdiv :
        z ^ (2 * (n + 1)) / (2 * ((n : ℝ) + 1)) ≤
          z ^ (2 * (n + 1)) / 2 := by
      exact div_le_div_of_nonneg_left hpow (by norm_num)
        (by nlinarith : (2 : ℝ) ≤ 2 * ((n : ℝ) + 1))
    calc
      z ^ (2 * (n + 1)) / (2 * ((n : ℝ) + 1))
          ≤ z ^ (2 * (n + 1)) / 2 := hdiv
      _ = g n := by
        dsimp [g]
        rw [show 2 * (n + 1) = 2 + 2 * n by omega, pow_add,
          show z ^ (2 * n) = (z ^ 2) ^ n by rw [← pow_mul]]
        ring) hg.summable

lemma lrLowQ_two_eq
    {ξ : ℝ} (hξ0 : 0 < ξ) (hξ1 : ξ < 1) :
    lrLowQ ξ 2 = lrL (Real.sqrt ξ) -
      ξ * (1 - lrLowAlpha 1) / 2 := by
  have hL := lrL_sqrt_eq_prefix_add_logTail hξ0 hξ1
    (n := 2) (by norm_num)
  unfold lrLowQ
  norm_num at hL ⊢
  rw [hL]
  ring

lemma lrLowRTail_two_le_geometric
    {ξ : ℝ} (hξ0 : 0 ≤ ξ) (hξ1 : ξ < 1) :
    lrLowRTail ξ 2 ≤ ξ ^ 3 / (2 * (1 - ξ)) := by
  let g : ℕ → ℝ := fun k ↦ (ξ ^ 3 / 2) * ξ ^ k
  have hg : HasSum g (ξ ^ 3 / (2 * (1 - ξ))) := by
    have hgeom := (hasSum_geometric_of_lt_one hξ0 hξ1).mul_left (ξ ^ 3 / 2)
    simpa [g, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hgeom
  unfold lrLowRTail
  rw [← hg.tsum_eq]
  exact (summable_lrLowR hξ0 hξ1 2).tsum_le_tsum (fun k ↦ by
    have hden : (0 : ℝ) < k + 3 := by positivity
    have hratio : ((k + 1 : ℕ) : ℝ) / (k + 3) ≤ 1 := by
      rw [div_le_one hden]
      exact_mod_cast (show k + 1 ≤ k + 3 by omega)
    have hpow : 0 ≤ ξ ^ (k + 3) := pow_nonneg hξ0 _
    calc
      ((k + 1 : ℕ) : ℝ) / (k + 2 + 1) * ξ ^ (k + 2 + 1) / 2
          ≤ 1 * ξ ^ (k + 3) / 2 := by
            norm_num only [Nat.cast_add, Nat.cast_one]
            rw [show k + 2 + 1 = k + 3 by omega]
            have hmul := mul_le_mul_of_nonneg_right hratio hpow
            simpa only [Nat.cast_add, Nat.cast_one,
              show (k : ℝ) + 2 + 1 = (k : ℝ) + 3 by ring]
              using div_le_div_of_nonneg_right hmul (by norm_num : (0 : ℝ) ≤ 2)
      _ = g k := by
        dsimp [g]
        rw [show k + 3 = 3 + k by omega, pow_add]
        ring) hg.summable

lemma lrSmallV_alpha_numeric_bounds :
    (227 / 1000 : ℝ) ≤ lrLowAlpha 1 ∧
    lrLowAlpha 1 ≤ 1 / 4 ∧
    (121 / 1000 : ℝ) ≤ lrLowAlpha 2 ∧
    (-106 / 1000 : ℝ) ≤ lrLowAlpha 2 - lrLowAlpha 1 ∧
    lrLowAlpha 2 - lrLowAlpha 1 ≤ (-1 / 10 : ℝ) := by
  have hlog := lr_log_two_millionth_bounds
  norm_num [lrLowAlpha, lrLowCStar, lrLowB, lrLowA] at hlog ⊢
  constructor
  · linarith [hlog.2]
  constructor
  · linarith [hlog.1]
  constructor
  · linarith [hlog.2]
  constructor <;> linarith [hlog.1, hlog.2]

noncomputable def lrSmallVEntryBracket (v x : ℝ) : ℝ :=
  (lrLowAlpha 2 - lrLowAlpha 1 + lrLowAlpha 1 * (v * x) -
      (v ^ 2 * x) * (1 - lrLowAlpha 1) * (1 - v * x)) /
      (1 - v ^ 2 * x) +
    2 * lrLowAlpha 2 * lrFlowBeta v / v

theorem lrSmallVEntryBracket_ge
    {v x : ℝ} (hv0 : 0 < v) (hv : v ≤ 1 / 3)
    (hx : x ∈ Icc (0 : ℝ) 1) :
    (1 / 24 : ℝ) ≤ lrSmallVEntryBracket v x := by
  rcases lrSmallV_alpha_numeric_bounds with
    ⟨ha1Low, ha1High, ha2Low, hdiffLow, hdiffHigh⟩
  let y : ℝ := v * x
  let ξ : ℝ := v ^ 2 * x
  have hy0 : 0 ≤ y := by
    dsimp [y]
    exact mul_nonneg hv0.le hx.1
  have hy : y ≤ 1 / 3 := by
    dsimp [y]
    calc
      v * x ≤ v * 1 := mul_le_mul_of_nonneg_left hx.2 hv0.le
      _ ≤ 1 / 3 := by simpa using hv
  have hξ0 : 0 ≤ ξ := by
    dsimp [ξ]
    exact mul_nonneg (sq_nonneg v) hx.1
  have hξ : ξ ≤ 1 / 9 := by
    have hvSq : v ^ 2 ≤ (1 / 9 : ℝ) := by
      have hprod : 0 ≤ ((1 / 3 : ℝ) - v) * (1 / 3 + v) :=
        mul_nonneg (sub_nonneg.mpr hv) (by linarith)
      nlinarith
    dsimp [ξ]
    exact (mul_le_mul_of_nonneg_left hx.2 (sq_nonneg v)).trans (by simpa using hvSq)
  have hξy : ξ ≤ y / 3 := by
    dsimp [ξ, y]
    have hmul := mul_le_mul_of_nonneg_right hv hx.1
    nlinarith
  have hc1 : 0 ≤ 1 - lrLowAlpha 1 := by linarith
  have honeY : 0 ≤ 1 - y := by linarith
  have honeY_le : 1 - y ≤ 1 := by linarith
  have hcProd : (1 - lrLowAlpha 1) * (1 - y) ≤
      1 - lrLowAlpha 1 :=
    mul_le_of_le_one_right hc1 honeY_le
  have htail : ξ * (1 - lrLowAlpha 1) * (1 - y) ≤
      y / 3 * (1 - lrLowAlpha 1) := by
    calc
      ξ * (1 - lrLowAlpha 1) * (1 - y) =
          ξ * ((1 - lrLowAlpha 1) * (1 - y)) := by ring
      _ ≤ ξ * (1 - lrLowAlpha 1) :=
        mul_le_mul_of_nonneg_left hcProd hξ0
      _ ≤ y / 3 * (1 - lrLowAlpha 1) :=
        mul_le_mul_of_nonneg_right hξy hc1
  have hfactor : (-31 / 1000 : ℝ) ≤
      lrLowAlpha 1 - (1 - lrLowAlpha 1) / 3 := by
    linarith
  have hfactorTerm : (-31 / 3000 : ℝ) ≤
      y * (lrLowAlpha 1 - (1 - lrLowAlpha 1) / 3) := by
    have hfirst := mul_le_mul_of_nonneg_left hfactor hy0
    have hsecond : y * (-31 / 1000 : ℝ) ≥ -31 / 3000 := by
      nlinarith
    nlinarith
  let N : ℝ := lrLowAlpha 2 - lrLowAlpha 1 + lrLowAlpha 1 * y -
    ξ * (1 - lrLowAlpha 1) * (1 - y)
  have hNLow : (-7 / 60 : ℝ) ≤ N := by
    dsimp [N]
    have hmiddle : y * (lrLowAlpha 1 - (1 - lrLowAlpha 1) / 3) ≤
        lrLowAlpha 1 * y -
          ξ * (1 - lrLowAlpha 1) * (1 - y) := by
      nlinarith [htail]
    nlinarith
  have hNHigh : N ≤ 0 := by
    dsimp [N]
    have ha1y : lrLowAlpha 1 * y ≤ 1 / 12 := by
      nlinarith [mul_le_mul ha1High hy hy0 (by norm_num : (0 : ℝ) ≤ 1 / 4)]
    have htail0 : 0 ≤ ξ * (1 - lrLowAlpha 1) * (1 - y) := by positivity
    linarith
  have hden : 0 < 1 - ξ := by linarith
  have hdenLower : (8 / 9 : ℝ) ≤ 1 - ξ := by linarith
  have hNdiv : (-21 / 160 : ℝ) ≤ N / (1 - ξ) := by
    have hmul := mul_le_mul_of_nonpos_left hdenLower hNHigh
    have hscale : (9 / 8 : ℝ) * N * (1 - ξ) ≤ N := by
      calc
        (9 / 8 : ℝ) * N * (1 - ξ) =
            (9 / 8 : ℝ) * (N * (1 - ξ)) := by ring
        _ ≤ (9 / 8 : ℝ) * (N * (8 / 9)) :=
          mul_le_mul_of_nonneg_left hmul (by norm_num)
        _ = N := by ring
    have hratio : (9 / 8 : ℝ) * N ≤ N / (1 - ξ) := by
      rw [le_div_iff₀ hden]
      simpa [mul_assoc] using hscale
    nlinarith
  have hlogLower := Real.one_sub_inv_le_log_of_pos (by linarith : 0 < 1 + v)
  have hbeta : (3 / 4 : ℝ) ≤ lrFlowBeta v / v := by
    have hbasic : v / (1 + v) ≤ lrFlowBeta v := by
      unfold lrFlowBeta
      convert hlogLower using 1
      field_simp [hv0.ne', show 1 + v ≠ 0 by linarith]
      ring
    have hinv : (3 / 4 : ℝ) ≤ 1 / (1 + v) := by
      rw [le_div_iff₀ (by linarith : 0 < 1 + v)]
      linarith
    have hdiv : 1 / (1 + v) ≤ lrFlowBeta v / v := by
      rw [le_div_iff₀ hv0]
      simpa [div_eq_mul_inv, mul_assoc, mul_comm] using hbasic
    exact hinv.trans hdiv
  have hlogTerm : (363 / 2000 : ℝ) ≤
      2 * lrLowAlpha 2 * lrFlowBeta v / v := by
    have hmul := mul_le_mul ha2Low hbeta (by norm_num) (by positivity)
    calc
      (363 / 2000 : ℝ) = 2 * ((121 / 1000 : ℝ) * (3 / 4)) := by norm_num
      _ ≤ 2 * (lrLowAlpha 2 * (lrFlowBeta v / v)) :=
        mul_le_mul_of_nonneg_left hmul (by norm_num)
      _ = 2 * lrLowAlpha 2 * lrFlowBeta v / v := by ring
  unfold lrSmallVEntryBracket
  change (1 / 24 : ℝ) ≤ N / (1 - ξ) +
    2 * lrLowAlpha 2 * lrFlowBeta v / v
  nlinarith

end CourtadeKumar
