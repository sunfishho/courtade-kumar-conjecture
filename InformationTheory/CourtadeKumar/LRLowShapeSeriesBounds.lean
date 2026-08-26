import InformationTheory.CourtadeKumar.LRLowShapeRationalBounds
import InformationTheory.CourtadeKumar.LRAbelBaseSeries

/-! Kernel-checked geometric envelopes for the finite series retained in the
low-shape certificates. -/

open Set
open scoped BigOperators

namespace CourtadeKumar

/-- The exact rational enclosure for `log 2` used in the certificate data. -/
theorem lr_log_two_millionth_bounds :
    (693147 : ℝ) / 1000000 < Real.log 2 ∧
      Real.log 2 < (693148 : ℝ) / 1000000 := by
  constructor
  · have h := Real.log_two_gt_d9
    norm_num at h ⊢
    linarith
  · have h := Real.log_two_lt_d9
    norm_num at h ⊢
    linarith

private lemma lr_phi_coefficient_le_thirteen (n : ℕ) :
    (1 : ℝ) /
        (2 * (n + 13) * (2 * (n + 13) - 1)) ≤
      1 / (2 * 13 * (2 * 13 - 1)) := by
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hden : (0 : ℝ) < 2 * (n + 13) * (2 * (n + 13) - 1) := by
    have hfirst : (0 : ℝ) < 2 * ((n : ℝ) + 13) := by positivity
    have hsecond : (0 : ℝ) < 2 * ((n : ℝ) + 13) - 1 := by
      nlinarith
    exact mul_pos hfirst hsecond
  have hbase : (0 : ℝ) < 2 * 13 * (2 * 13 - 1) := by norm_num
  apply one_div_le_one_div_of_le hbase
  nlinarith

/-- Every finite prefix is a lower bound because the `Φ` coefficients are
nonnegative. -/
theorem topPhi_sqrt_partial_sum_le
    {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (k : ℕ) :
    ∑ n ∈ Finset.range k,
        x ^ (n + 1) /
          (2 * (n + 1) * (2 * (n + 1) - 1)) ≤
      topPhi (Real.sqrt x) := by
  exact sum_le_hasSum (Finset.range k) (fun n _ ↦ by
    apply div_nonneg (pow_nonneg hx.1.le _)
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hfirst : 0 ≤ 2 * ((n : ℝ) + 1) := by positivity
    have hsecond : 0 ≤ 2 * ((n : ℝ) + 1) - 1 := by nlinarith
    exact mul_nonneg hfirst hsecond) (topPhi_sqrt_hasSum hx)

/-- After twelve terms, the positive `Φ` series is bounded by replacing all
remaining coefficients with `a₁₃` and summing a geometric series. -/
theorem topPhi_sqrt_tail_twelve_upper
    {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    topPhi (Real.sqrt x) -
        ∑ n ∈ Finset.range 12,
          x ^ (n + 1) /
            (2 * (n + 1) * (2 * (n + 1) - 1)) ≤
      (1 / (2 * 13 * (2 * 13 - 1)) : ℝ) * x ^ 13 / (1 - x) := by
  have hx : x ∈ Ioo (0 : ℝ) 1 := ⟨hx0, hx1⟩
  let f : ℕ → ℝ := fun n ↦
    x ^ (n + 13) /
      (2 * (n + 13) * (2 * (n + 13) - 1))
  let g : ℕ → ℝ := fun n ↦
    (1 / (2 * 13 * (2 * 13 - 1)) : ℝ) * x ^ 13 * x ^ n
  have hf : HasSum f
      (topPhi (Real.sqrt x) -
        ∑ n ∈ Finset.range 12,
          x ^ (n + 1) /
            (2 * (n + 1) * (2 * (n + 1) - 1))) := by
    convert topPhi_sqrt_tail_hasSum hx 12 using 1
    funext n
    dsimp [f]
    rw [show n + 13 = n + 12 + 1 by omega]
    norm_num only [Nat.cast_add, Nat.cast_ofNat]
    ring
  have hg : HasSum g
      ((1 / (2 * 13 * (2 * 13 - 1)) : ℝ) * x ^ 13 / (1 - x)) := by
    have hgeom := hasSum_geometric_of_lt_one hx0.le hx1
    convert hgeom.mul_left
      ((1 / (2 * 13 * (2 * 13 - 1)) : ℝ) * x ^ 13) using 1 <;>
      simp [g, div_eq_mul_inv] <;> ring
  calc
    topPhi (Real.sqrt x) -
          ∑ n ∈ Finset.range 12,
            x ^ (n + 1) /
              (2 * (n + 1) * (2 * (n + 1) - 1)) =
        ∑' n, f n := hf.tsum_eq.symm
    _ ≤ ∑' n, g n := hf.summable.tsum_le_tsum (fun n ↦ by
      dsimp [f, g]
      have hxpow : 0 ≤ x ^ (n + 13) := pow_nonneg hx0.le _
      have hc := lr_phi_coefficient_le_thirteen n
      calc
        x ^ (n + 13) / (2 * (n + 13) * (2 * (n + 13) - 1)) =
            (1 / (2 * (n + 13) * (2 * (n + 13) - 1))) *
              x ^ (n + 13) := by ring
        _ ≤ (1 / (2 * 13 * (2 * 13 - 1))) * x ^ (n + 13) :=
          mul_le_mul_of_nonneg_right hc hxpow
        _ = (1 / (2 * 13 * (2 * 13 - 1))) * x ^ 13 * x ^ n := by
          rw [show n + 13 = 13 + n by omega, pow_add]
          ring) hg.summable
    _ = (1 / (2 * 13 * (2 * 13 - 1)) : ℝ) * x ^ 13 / (1 - x) :=
      hg.tsum_eq

private lemma lr_L_coefficient_le_thirteen (n : ℕ) :
    (1 : ℝ) / (2 * (n + 13)) ≤ 1 / 26 := by
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hden : (0 : ℝ) < 2 * (n + 13) := by positivity
  apply one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 26)
  nlinarith

/-- Power series for `L (sqrt q)` expressed directly in `q`. -/
theorem lrL_sqrt_hasSum
    {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1) :
    HasSum (fun n : ℕ ↦ q ^ (n + 1) / (2 * (n + 1)))
      (lrL (Real.sqrt q)) := by
  have hsqrt : Real.sqrt q ∈ Ioo (-1 : ℝ) 1 := by
    constructor
    · linarith [Real.sqrt_nonneg q]
    · simpa only [lt_iff_not_ge, Real.one_le_sqrt] using hq.2
  convert lrL_hasSum hsqrt using 1
  funext n
  rw [pow_mul, Real.sq_sqrt hq.1.le]

/-- Every finite prefix is a lower bound for `L (sqrt q)`. -/
theorem lrL_sqrt_partial_sum_le
    {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1) (k : ℕ) :
    ∑ n ∈ Finset.range k, q ^ (n + 1) / (2 * (n + 1)) ≤
      lrL (Real.sqrt q) := by
  exact sum_le_hasSum (Finset.range k) (fun n _ ↦ by
    exact div_nonneg (pow_nonneg hq.1.le _) (by positivity))
      (lrL_sqrt_hasSum hq)

/-- The analogous twelve-term geometric upper envelope for
`L (sqrt q) = ∑ qᵐ/(2m)`. -/
theorem lrL_sqrt_tail_twelve_upper
    {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    lrL (Real.sqrt q) -
        ∑ n ∈ Finset.range 12, q ^ (n + 1) / (2 * (n + 1)) ≤
      q ^ 13 / (26 * (1 - q)) := by
  let f : ℕ → ℝ := fun n ↦ q ^ (n + 13) / (2 * (n + 13))
  let g : ℕ → ℝ := fun n ↦ (1 / 26 : ℝ) * q ^ 13 * q ^ n
  have hfull := lrL_sqrt_hasSum (show q ∈ Ioo (0 : ℝ) 1 from ⟨hq0, hq1⟩)
  have hf : HasSum f
      (lrL (Real.sqrt q) -
        ∑ n ∈ Finset.range 12, q ^ (n + 1) / (2 * (n + 1))) := by
    convert (hasSum_nat_add_iff' 12).2 hfull using 1
    funext n
    dsimp [f]
    rw [show n + 13 = n + 12 + 1 by omega]
    norm_num only [Nat.cast_add, Nat.cast_ofNat]
    ring
  have hg : HasSum g (q ^ 13 / (26 * (1 - q))) := by
    have hgeom := hasSum_geometric_of_lt_one hq0.le hq1
    convert hgeom.mul_left ((1 / 26 : ℝ) * q ^ 13) using 1 <;>
      simp [g, div_eq_mul_inv] <;> field_simp <;> ring
  calc
    lrL (Real.sqrt q) -
          ∑ n ∈ Finset.range 12, q ^ (n + 1) / (2 * (n + 1)) =
        ∑' n, f n := hf.tsum_eq.symm
    _ ≤ ∑' n, g n := hf.summable.tsum_le_tsum (fun n ↦ by
      dsimp [f, g]
      have hqpow : 0 ≤ q ^ (n + 13) := pow_nonneg hq0.le _
      calc
        q ^ (n + 13) / (2 * (n + 13)) =
            (1 / (2 * (n + 13))) * q ^ (n + 13) := by ring
        _ ≤ (1 / 26) * q ^ (n + 13) :=
          mul_le_mul_of_nonneg_right (lr_L_coefficient_le_thirteen n) hqpow
        _ = (1 / 26) * q ^ 13 * q ^ n := by
          rw [show n + 13 = 13 + n by omega, pow_add]
          ring) hg.summable
    _ = q ^ 13 / (26 * (1 - q)) := hg.tsum_eq

end CourtadeKumar
