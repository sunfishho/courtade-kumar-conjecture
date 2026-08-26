import InformationTheory.CourtadeKumar.LRLowShapeUWPolynomialBridge

/-! Analytic estimates for the uniform `n ≥ 6` part of the low-shape
second scalar. -/

open Set
open scoped BigOperators

namespace CourtadeKumar

noncomputable def lrLowQuarterTail (n : ℕ) : ℝ :=
  1 / (4 * (n : ℝ))

lemma lrLowQuarterTail_nonneg (n : ℕ) : 0 ≤ lrLowQuarterTail n := by
  unfold lrLowQuarterTail
  positivity

lemma lrLowQuarterTail_tendsto_zero :
    Filter.Tendsto lrLowQuarterTail Filter.atTop (nhds 0) := by
  apply squeeze_zero (fun n ↦ lrLowQuarterTail_nonneg n)
    (fun n ↦ ?_) tendsto_one_div_add_atTop_nhds_zero_nat
  cases n with
  | zero => norm_num [lrLowQuarterTail]
  | succ n =>
      unfold lrLowQuarterTail
      norm_num only [Nat.cast_add, Nat.cast_one]
      have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      have hleft : 0 < 4 * ((n : ℝ) + 1) := by positivity
      have hright : 0 < (n : ℝ) + 1 + 1 := by positivity
      rw [div_le_div_iff₀ hleft hright]
      nlinarith

lemma lrLowQuarterTail_diff_nonneg
    {n : ℕ} (hn : 1 ≤ n) :
    0 ≤ lrLowQuarterTail n - lrLowQuarterTail (n + 1) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  unfold lrLowQuarterTail
  norm_num only [Nat.cast_add, Nat.cast_one]
  have h0 : 0 < 4 * (n : ℝ) := by positivity
  have h1 : 0 < 4 * ((n : ℝ) + 1) := by positivity
  rw [sub_nonneg, div_le_div_iff₀ h1 h0]
  nlinarith

lemma lrLowQuarterTail_diff_hasSum
    {n : ℕ} (hn : 1 ≤ n) :
    HasSum (fun k : ℕ ↦
      lrLowQuarterTail (k + n) - lrLowQuarterTail (k + n + 1))
      (lrLowQuarterTail n) := by
  rw [hasSum_iff_tendsto_nat_of_nonneg (fun k ↦
    lrLowQuarterTail_diff_nonneg (n := k + n) (by omega))]
  have hshift : Filter.Tendsto (fun m : ℕ ↦ lrLowQuarterTail (m + n))
      Filter.atTop (nhds 0) :=
    (Filter.tendsto_add_atTop_iff_nat n).2 lrLowQuarterTail_tendsto_zero
  have hconst : Filter.Tendsto (fun _ : ℕ ↦ lrLowQuarterTail n)
      Filter.atTop (nhds (lrLowQuarterTail n)) := tendsto_const_nhds
  have hlimit := hconst.sub hshift
  have hsum (m : ℕ) :
      ∑ k ∈ Finset.range m,
          (lrLowQuarterTail (k + n) - lrLowQuarterTail (k + n + 1)) =
        lrLowQuarterTail n - lrLowQuarterTail (m + n) := by
    simpa [add_assoc, add_comm, add_left_comm] using
      Finset.sum_range_sub' (fun k ↦ lrLowQuarterTail (k + n)) m
  convert hlimit using 1
  · funext m
    exact hsum m
  · simp

lemma lrLowA_le_quarterTail_diff
    {m : ℕ} (hm : 1 ≤ m) :
    lrLowA (m + 1) ≤ lrLowQuarterTail m - lrLowQuarterTail (m + 1) := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  unfold lrLowA lrLowQuarterTail
  norm_num only [Nat.cast_add, Nat.cast_one]
  have h0 : 0 < (m : ℝ) := by positivity
  have h1 : 0 < (m : ℝ) + 1 := by positivity
  have h2 : 0 < 2 * ((m : ℝ) + 1) - 1 := by nlinarith
  field_simp [h0.ne', h1.ne', h2.ne']
  nlinarith

theorem lrLowB_le_quarterTail
    {n : ℕ} (hn : 1 ≤ n) :
    lrLowB n ≤ lrLowQuarterTail n := by
  have hb := lrLowB_hasSum n
  have hq := lrLowQuarterTail_diff_hasSum hn
  rw [← hb.tsum_eq, ← hq.tsum_eq]
  exact hb.summable.tsum_le_tsum (fun k ↦ by
    simpa [add_assoc] using
      lrLowA_le_quarterTail_diff (m := k + n) (by omega)) hq.summable

theorem lrLowB_scaled_le_quarter
    {n : ℕ} (hn : 1 ≤ n) :
    (n : ℝ) * lrLowB n ≤ 1 / 4 := by
  have hnR : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  calc
    (n : ℝ) * lrLowB n ≤ (n : ℝ) * lrLowQuarterTail n :=
      mul_le_mul_of_nonneg_left (lrLowB_le_quarterTail hn) hnR
    _ = 1 / 4 := by
      unfold lrLowQuarterTail
      have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
      field_simp [hn0]

theorem lrLowB_antitone : Antitone lrLowB := by
  apply antitone_nat_of_succ_le
  intro n
  rw [lrLowB_recursion n]
  exact le_add_of_nonneg_left (lrLowA_pos (by omega)).le

lemma lrLowH_monotone
    {xi : ℝ} (hxi : 0 ≤ xi) : Monotone (lrLowH xi) := by
  apply monotone_nat_of_le_succ
  intro n
  unfold lrLowH
  rw [Finset.sum_range_succ]
  exact le_add_of_nonneg_right (pow_nonneg hxi _)

lemma lrL_mono_nonneg
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b < 1) :
    lrL a ≤ lrL b := by
  have hb0 : 0 ≤ b := ha.trans hab
  have hsquare : a ^ 2 ≤ b ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hab) (add_nonneg hb0 ha)]
  have harg : 1 - b ^ 2 ≤ 1 - a ^ 2 := by linarith
  have hargPos : 0 < 1 - b ^ 2 := by
    have hplus : 0 < 1 + b := by linarith
    nlinarith [mul_pos (sub_pos.mpr hb) hplus]
  have hlog := Real.log_le_log hargPos harg
  unfold lrL
  nlinarith

lemma lrLowActualA_mono
    {v q t : ℝ} (hv : 0 < v) (hvq : v ≤ q)
    (ht : t ∈ Ioo (0 : ℝ) 1) (hq : q ≤ 1) :
    lrFlowBeta v + lrL (v * t) ≤ lrFlowBeta q + lrL (q * t) := by
  have hq0 : 0 < q := hv.trans_le hvq
  have hlog : Real.log (1 + v) ≤ Real.log (1 + q) :=
    Real.log_le_log (by linarith [hv]) (by linarith)
  have hvt0 : 0 ≤ v * t := mul_nonneg hv.le ht.1.le
  have hprod : v * t ≤ q * t := mul_le_mul_of_nonneg_right hvq ht.1.le
  have hqt : q * t < 1 := by
    calc
      q * t ≤ 1 * t := mul_le_mul_of_nonneg_right hq ht.1.le
      _ < 1 := by simpa using ht.2
  have hL := lrL_mono_nonneg hvt0 hprod hqt
  simpa [lrFlowBeta] using add_le_add hlog hL

noncomputable def lrLowGShapeTailAux (t A q : ℝ) : ℝ :=
  lrGShape t q - A / q

lemma hasDerivAt_lrLowGShapeTailAux
    {t A q : ℝ} (hq : 0 < q) (ht0 : 0 ≤ t) (htq : t * q < 1) :
    HasDerivAt (lrLowGShapeTailAux t A)
      ((A - (lrFlowBeta q + lrL (q * t))) / q ^ 2) q := by
  have hshape := hasDerivAt_lrGShape hq ht0 htq
  have hquot : HasDerivAt (fun y : ℝ ↦ A / y) (-A / q ^ 2) q := by
    have h := (hasDerivAt_const q A).div (hasDerivAt_id q) hq.ne'
    convert h using 1 <;> simp only [id_eq] <;>
      field_simp [hq.ne'] <;> ring
  have h := hshape.sub hquot
  convert h using 1
  simp only [lrFlowBeta]
  rw [mul_comm t q]
  ring

theorem lrGShape_ge_tail_envelope
    {v t : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1)
    (ht : t ∈ Ioo (0 : ℝ) 1) :
    2 * (Real.log 2 - topPhi t) +
        (1 - v) / v * (lrFlowBeta v + lrL (v * t)) ≤
      lrGShape t v := by
  let A : ℝ := lrFlowBeta v + lrL (v * t)
  have hanti : AntitoneOn (lrLowGShapeTailAux t A) (Icc v 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc v 1)
    · intro q hq
      have hq0 : 0 < q := hv.1.trans_le hq.1
      have htq : t * q < 1 := by
        calc
          t * q ≤ t * 1 := mul_le_mul_of_nonneg_left hq.2 ht.1.le
          _ < 1 := by simpa using ht.2
      exact (hasDerivAt_lrLowGShapeTailAux hq0 ht.1.le htq).continuousAt
        |>.continuousWithinAt
    · intro q hq
      rw [interior_Icc] at hq
      have hq0 : 0 < q := hv.1.trans hq.1
      have htq : t * q < 1 := by
        calc
          t * q ≤ t * 1 := mul_le_mul_of_nonneg_left hq.2.le ht.1.le
          _ < 1 := by simpa using ht.2
      exact (hasDerivAt_lrLowGShapeTailAux hq0 ht.1.le htq).differentiableAt
        |>.differentiableWithinAt
    · intro q hq
      rw [interior_Icc] at hq
      have hq0 : 0 < q := hv.1.trans hq.1
      have htq : t * q < 1 := by
        calc
          t * q ≤ t * 1 := mul_le_mul_of_nonneg_left hq.2.le ht.1.le
          _ < 1 := by simpa using ht.2
      rw [(hasDerivAt_lrLowGShapeTailAux hq0 ht.1.le htq).deriv]
      exact div_nonpos_of_nonpos_of_nonneg
        (sub_nonpos.mpr (show A ≤ lrFlowBeta q + lrL (q * t) by
          dsimp [A]
          exact lrLowActualA_mono hv.1 hq.1.le ht hq.2.le))
        (sq_nonneg q)
  have haux := hanti
    (show v ∈ Icc v 1 from ⟨le_rfl, hv.2.le⟩)
    (show (1 : ℝ) ∈ Icc v 1 from ⟨hv.2.le, le_rfl⟩) hv.2.le
  unfold lrLowGShapeTailAux at haux
  rw [lrGShape_one] at haux
  have hratio : (1 - v) / v * A = A / v - A := by
    field_simp [hv.1.ne']
  change 2 * (Real.log 2 - topPhi t) + (1 - v) / v * A ≤
    lrGShape t v
  rw [hratio]
  linarith

end CourtadeKumar
