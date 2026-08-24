import InformationTheory.CourtadeKumar.TopDerivatives
import Mathlib.Analysis.Complex.AbelLimit
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! The absolutely convergent positive power series for the natural-unit
binary entropy defect `topPhi`. -/

open Set
open Filter
open scoped BigOperators

namespace CourtadeKumar

/-- The conventional partial sums of the alternating harmonic series tend to
`log 2`.  We retain the partial-sum formulation because this series is only
conditionally convergent. -/
theorem top_tendsto_alternatingHarmonic :
    Tendsto
      (fun n ↦ ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i / (i + 1))
      atTop (nhds (Real.log 2)) := by
  obtain ⟨l, hl⟩ :
      ∃ l : ℝ, Tendsto
        (fun n ↦ ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i / (i + 1))
        Filter.atTop (nhds l) := by
    apply Antitone.tendsto_alternating_series_of_tendsto_zero
    · exact antitone_iff_forall_lt.mpr fun _ _ _ ↦ by gcongr
    · apply Tendsto.inv_tendsto_atTop
      exact tendsto_atTop_add_const_right Filter.atTop 1 tendsto_natCast_atTop_atTop
  have habel := Real.tendsto_tsum_powerSeries_nhdsWithin_lt hl
  have hseries :
      Filter.Eventually
        (fun x : ℝ ↦
          (∑' n : ℕ, ((-1 : ℝ) ^ n / (n + 1)) * x ^ n) =
            Real.log (1 + x) / x)
        (nhdsWithin 1 (Iio 1)) := by
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with x hx
    have habs : |x| < 1 := by rw [abs_of_pos hx.1]; exact hx.2
    have hx0 : x ≠ 0 := ne_of_gt hx.1
    have hs := Real.hasSum_pow_div_log_of_abs_lt_one (x := -x) (by simpa using habs)
    have hm := hs.mul_left (-x⁻¹)
    calc
      (∑' n : ℕ, ((-1 : ℝ) ^ n / (n + 1)) * x ^ n) =
          ∑' n : ℕ, -x⁻¹ * ((-x) ^ (n + 1) / (n + 1)) := by
            congr with n
            rw [pow_succ, neg_pow]
            field_simp [hx0]
            ring
      _ = -x⁻¹ * -Real.log (1 - -x) := hm.tsum_eq
      _ = Real.log (1 + x) / x := by
        simp only [sub_neg_eq_add]
        field_simp [hx0]
  have hlog :
      Tendsto (fun x : ℝ ↦ Real.log (1 + x) / x)
        (nhdsWithin 1 (Iio 1)) (nhds (Real.log 2)) := by
    have hadd : ContinuousAt (fun x : ℝ ↦ 1 + x) 1 :=
      continuousAt_const.add continuousAt_id
    have hnum : ContinuousAt (fun x : ℝ ↦ Real.log (1 + x)) 1 :=
      hadd.log (by norm_num)
    have hc : ContinuousAt (fun x : ℝ ↦ Real.log (1 + x) / x) 1 := by
      exact hnum.div continuousAt_id (by norm_num)
    convert hc.tendsto.mono_left inf_le_left using 1 <;> norm_num
  have hl' : Tendsto (fun x : ℝ ↦ Real.log (1 + x) / x)
      (nhdsWithin 1 (Iio 1)) (nhds l) :=
    habel.congr' hseries
  have : l = Real.log 2 := tendsto_nhds_unique hl' hlog
  simpa [this] using hl

private lemma top_alternatingHarmonic_pairing (n : ℕ) :
    ∑ i ∈ Finset.range (2 * n), (-1 : ℝ) ^ i / (i + 1) =
      ∑ m ∈ Finset.range n,
        (1 : ℝ) / (2 * (m + 1) * (2 * (m + 1) - 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.mul_succ, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ, ih]
      rw [add_assoc, add_left_cancel_iff]
      push_cast
      rw [Even.neg_one_pow (even_two_mul n),
        Odd.neg_one_pow (odd_two_mul_add_one n)]
      have hn0 : 1 + (n : ℝ) * 2 ≠ 0 := by positivity
      have hn2 : 2 + (n : ℝ) * 2 ≠ 0 := by positivity
      have hp : 2 + (n : ℝ) * 6 + (n : ℝ) ^ 2 * 4 ≠ 0 := by positivity
      have hfrac :
          (2 + (n : ℝ) * 6 + (n : ℝ) ^ 2 * 4)⁻¹ =
            (1 + (n : ℝ) * 2)⁻¹ - (2 + (n : ℝ) * 2)⁻¹ := by
        field_simp [hn0, hn2, hp]
        ring
      convert hfrac.symm using 1 <;> ring

/-- The endpoint coefficient identity
`∑ m≥1, 1 / (2m(2m-1)) = log 2`. -/
theorem top_hasSum_phiCoefficients :
    HasSum (fun n : ℕ ↦
      (1 : ℝ) / (2 * (n + 1) * (2 * (n + 1) - 1))) (Real.log 2) := by
  rw [hasSum_iff_tendsto_nat_of_nonneg (fun n ↦ by
    apply one_div_nonneg.mpr
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hfirst : 0 ≤ 2 * ((n : ℝ) + 1) := by positivity
    have hsecond : 0 ≤ 2 * ((n : ℝ) + 1) - 1 := by nlinarith
    exact mul_nonneg hfirst hsecond)]
  have h := top_tendsto_alternatingHarmonic.comp
    (tendsto_id.nsmul_atTop (by norm_num : 0 < (2 : ℕ)))
  convert h using 1
  funext n
  simpa [two_nsmul] using (top_alternatingHarmonic_pairing n).symm

/-- Removing finitely many terms from the positive endpoint series. -/
theorem top_hasSum_phiCoefficients_tail (k : ℕ) :
    HasSum (fun n : ℕ ↦
      (1 : ℝ) /
        (2 * (n + k + 1) * (2 * (n + k + 1) - 1)))
      (Real.log 2 - ∑ n ∈ Finset.range k,
        (1 : ℝ) / (2 * (n + 1) * (2 * (n + 1) - 1))) := by
  convert (hasSum_nat_add_iff' k).2 top_hasSum_phiCoefficients using 1 <;>
    simp [add_assoc, add_comm]

lemma topPhi_eq_log_formula {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    topPhi x =
      ((1 + x) * Real.log (1 + x) + (1 - x) * Real.log (1 - x)) / 2 := by
  have hp : 0 < 1 + x := by linarith [hx.1]
  have hm : 0 < 1 - x := by linarith [hx.2]
  unfold topPhi
  rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  rw [show 1 - (1 - x) / 2 = (1 + x) / 2 by ring]
  rw [Real.negMulLog_eq_neg]
  change Real.log 2 -
      (-((1 - x) / 2 * Real.log ((1 - x) / 2)) +
        -((1 + x) / 2 * Real.log ((1 + x) / 2))) = _
  rw [Real.log_div hp.ne' (by norm_num : (2 : ℝ) ≠ 0)]
  rw [Real.log_div hm.ne' (by norm_num : (2 : ℝ) ≠ 0)]
  ring

/-- The manuscript series
`topPhi x = ∑ m≥1, x^(2m) / (2m(2m-1))` on the open unit interval.
It is obtained by pairing consecutive terms of two absolutely convergent
logarithm series. -/
theorem topPhi_hasSum {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    HasSum (fun n : ℕ ↦
      x ^ (2 * (n + 1)) /
        (2 * (n + 1) * (2 * (n + 1) - 1))) (topPhi x) := by
  have habs : |x| < 1 := by rw [abs_lt]; exact hx
  let t : ℕ → ℝ := fun n ↦
    -(1 + x) / 2 * ((-x) ^ (n + 1) / (n + 1)) +
      -(1 - x) / 2 * (x ^ (n + 1) / (n + 1))
  have hplus :=
    (Real.hasSum_pow_div_log_of_abs_lt_one (x := -x) (by simpa using habs)).mul_left
      (-(1 + x) / 2)
  have hminus :=
    (Real.hasSum_pow_div_log_of_abs_lt_one (x := x) habs).mul_left
      (-(1 - x) / 2)
  have ht : HasSum t (topPhi x) := by
    have hadd := hplus.add hminus
    convert hadd using 1
    rw [topPhi_eq_log_formula hx]
    simp only [sub_neg_eq_add]
    ring
  have he : Summable (fun n : ℕ ↦ t (2 * n)) :=
    ht.summable.comp_injective (mul_right_injective₀ (two_ne_zero' ℕ))
  have ho : Summable (fun n : ℕ ↦ t (2 * n + 1)) :=
    ht.summable.comp_injective (by
      intro a b h
      change 2 * a + 1 = 2 * b + 1 at h
      exact Nat.mul_left_cancel (by decide) (Nat.add_right_cancel h))
  have heo :
      tsum (fun n : ℕ ↦ t (2 * n)) + tsum (fun n : ℕ ↦ t (2 * n + 1)) =
        topPhi x := by
    exact (HasSum.even_add_odd he.hasSum ho.hasSum).unique ht
  have hpair := he.hasSum.add ho.hasSum
  rw [heo] at hpair
  convert hpair using 1
  funext n
  dsimp [t]
  rw [Odd.neg_pow (⟨n, rfl⟩ : Odd (2 * n + 1)),
    Even.neg_pow (⟨n + 1, by omega⟩ : Even (2 * n + 2))]
  push_cast
  have hn : (1 + (n : ℝ) * 2) ≠ 0 := by positivity
  have hscalar :
      ((n : ℝ) * 6 + (n : ℝ) ^ 2 * 4 + 2) *
          (1 + (n : ℝ) * 2)⁻¹ = 2 + (n : ℝ) * 2 := by
    field_simp [hn]
    ring
  have hn2 : (2 + (n : ℝ) * 2) ≠ 0 := by positivity
  have hp : (2 + (n : ℝ) * 6 + (n : ℝ) ^ 2 * 4) ≠ 0 := by positivity
  have hfrac :
      (2 + (n : ℝ) * 6 + (n : ℝ) ^ 2 * 4)⁻¹ =
        (1 + (n : ℝ) * 2)⁻¹ - (2 + (n : ℝ) * 2)⁻¹ := by
    field_simp [hn, hn2, hp]
    ring
  linear_combination (x ^ 2 * x ^ (n * 2)) * hfrac

/-- The `topPhi` series after the substitution `R = x²`. -/
theorem topPhi_sqrt_hasSum {R : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1) :
    HasSum (fun n : ℕ ↦
      R ^ (n + 1) /
        (2 * (n + 1) * (2 * (n + 1) - 1))) (topPhi (Real.sqrt R)) := by
  have hsqrtlt : Real.sqrt R < 1 := by
    simpa only [lt_iff_not_ge, Real.one_le_sqrt] using hR.2
  have h := topPhi_hasSum
    (show Real.sqrt R ∈ Ioo (-1 : ℝ) 1 from
      ⟨by linarith [Real.sqrt_nonneg R], hsqrtlt⟩)
  convert h using 1
  funext n
  rw [pow_mul, Real.sq_sqrt hR.1.le]

/-- The tail of the `R`-power series for `topPhi (sqrt R)`. -/
theorem topPhi_sqrt_tail_hasSum {R : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1) (k : ℕ) :
    HasSum (fun n : ℕ ↦
      R ^ (n + k + 1) /
        (2 * (n + k + 1) * (2 * (n + k + 1) - 1)))
      (topPhi (Real.sqrt R) - ∑ n ∈ Finset.range k,
        R ^ (n + 1) / (2 * (n + 1) * (2 * (n + 1) - 1))) := by
  convert (hasSum_nat_add_iff' k).2 (topPhi_sqrt_hasSum hR) using 1 <;>
    simp [add_assoc, add_comm]

end CourtadeKumar
