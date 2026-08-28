import InformationTheory.CourtadeKumar.LRDeterminantWronskian

/-!
# Power-series resummation for the determinant Wronskian

This file separates the analytic resummation step from the concrete radial
series.  Once `H`, `H'`, `F`, and `F'` have the stated power series, the
coefficient formula proved in `LRDeterminantWronskian` sums to the desired
Wronskian inequality.
-/

open scoped BigOperators

namespace CourtadeKumar

/-- Coefficients of `H = a + ∑_{j≥1} c_j R^j`. -/
noncomputable def lrWronskianHSeriesCoefficient
    (a : ℝ) (c : ℕ → ℝ) (n : ℕ) : ℝ :=
  if n = 0 then a else c n

/-- Coefficients of `F = ∑_{j≥1} f_j R^j`. -/
noncomputable def lrWronskianFSeriesCoefficient
    (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0 else f n

/-- Coefficients of the formal derivative `H'`. -/
noncomputable def lrWronskianHDerivativeSeriesCoefficient
    (c : ℕ → ℝ) (n : ℕ) : ℝ :=
  ((n + 1 : ℕ) : ℝ) * c (n + 1)

/-- Coefficients of the formal derivative `F'`. -/
noncomputable def lrWronskianFDerivativeSeriesCoefficient
    (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  ((n + 1 : ℕ) : ℝ) * f (n + 1)

/-- The difference of the two Cauchy-product coefficients is exactly the
finite Wronskian coefficient used in the audited proof. -/
theorem lrWronskianConvolutionCoefficient_eq
    (lambda a : ℝ) (c f : ℕ → ℝ) (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1),
        lrWronskianHSeriesCoefficient a c k *
          lrWronskianFDerivativeSeriesCoefficient f (n - k)) -
        lambda * (∑ k ∈ Finset.range (n + 1),
          lrWronskianHDerivativeSeriesCoefficient c k *
            lrWronskianFSeriesCoefficient f (n - k)) =
      lrWronskianCoefficient lambda a c f n := by
  have hHF :
      (∑ k ∈ Finset.range (n + 1),
          lrWronskianHSeriesCoefficient a c k *
            lrWronskianFDerivativeSeriesCoefficient f (n - k)) =
        a * ((n + 1 : ℕ) : ℝ) * f (n + 1) +
          ∑ i ∈ Finset.range n,
            ((n - i : ℕ) : ℝ) * c (i + 1) * f (n - i) := by
    rw [Finset.sum_range_succ']
    have hsum :
        (∑ i ∈ Finset.range n,
            lrWronskianHSeriesCoefficient a c (i + 1) *
              lrWronskianFDerivativeSeriesCoefficient f (n - (i + 1))) =
          ∑ i ∈ Finset.range n,
            ((n - i : ℕ) : ℝ) * c (i + 1) * f (n - i) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hiLt : i < n := Finset.mem_range.mp hi
      have hsub : n - (i + 1) + 1 = n - i := by omega
      simp [lrWronskianHSeriesCoefficient,
        lrWronskianFDerivativeSeriesCoefficient, hsub]
      ring
    rw [hsum]
    simp [lrWronskianHSeriesCoefficient,
      lrWronskianFDerivativeSeriesCoefficient]
    ring
  have hHDF :
      (∑ k ∈ Finset.range (n + 1),
          lrWronskianHDerivativeSeriesCoefficient c k *
            lrWronskianFSeriesCoefficient f (n - k)) =
        ∑ i ∈ Finset.range n,
          ((i + 1 : ℕ) : ℝ) * c (i + 1) * f (n - i) := by
    rw [Finset.sum_range_succ]
    simp [lrWronskianFSeriesCoefficient,
      lrWronskianHDerivativeSeriesCoefficient]
    apply Finset.sum_congr rfl
    intro i hi
    have hiLt : i < n := Finset.mem_range.mp hi
    simp only [Nat.sub_ne_zero_of_lt hiLt, ↓reduceIte]
  rw [hHF, hHDF, Finset.mul_sum]
  unfold lrWronskianCoefficient
  have hsum :
      (∑ i ∈ Finset.range n,
          ((n - i : ℕ) : ℝ) * c (i + 1) * f (n - i)) -
          (∑ i ∈ Finset.range n,
            lambda * (((i + 1 : ℕ) : ℝ) * c (i + 1) * f (n - i))) =
        ∑ i ∈ Finset.range n,
          (((n + 1 : ℕ) : ℝ) -
              (lambda + 1) * ((i + 1 : ℕ) : ℝ)) *
            c (i + 1) * f (n - i) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    have hiLt : i < n := Finset.mem_range.mp hi
    rw [Nat.cast_sub (Nat.le_of_lt hiLt)]
    push_cast
    ring
  calc
    _ = a * ((n + 1 : ℕ) : ℝ) * f (n + 1) +
        ((∑ i ∈ Finset.range n,
            ((n - i : ℕ) : ℝ) * c (i + 1) * f (n - i)) -
          ∑ i ∈ Finset.range n,
            lambda * (((i + 1 : ℕ) : ℝ) * c (i + 1) * f (n - i))) := by ring
    _ = _ := by rw [hsum]

private theorem lrHasSumCauchyConvolution
    {u v : ℕ → ℝ} {U V : ℝ}
    (hu : HasSum u U) (hv : HasSum v V) :
    HasSum (fun n : ℕ =>
      ∑ k ∈ Finset.range (n + 1), u k * v (n - k)) (U * V) := by
  have hp : Summable (fun q : ℕ × ℕ => u q.1 * v q.2) :=
    summable_mul_of_summable_norm hu.summable.norm hv.summable.norm
  have hs : Summable (fun n : ℕ =>
      ∑ k ∈ Finset.range (n + 1), u k * v (n - k)) :=
    summable_sum_mul_range_of_summable_mul hp
  have hvalue := hu.summable.tsum_mul_tsum_eq_tsum_sum_range
    hv.summable hp
  rw [hu.tsum_eq, hv.tsum_eq] at hvalue
  rw [hvalue]
  exact hs.hasSum

/-- Abstract resummation theorem: nonnegative Wronskian coefficients imply
`H F' - lambda H' F ≥ 0` wherever all four power series converge and
`R ≥ 0`. -/
theorem lrWronskian_nonnegative_of_hasSum
    {R lambda a H Hderiv F Fderiv : ℝ} {c f : ℕ → ℝ}
    (hR : 0 ≤ R)
    (hH : HasSum (fun n : ℕ =>
      lrWronskianHSeriesCoefficient a c n * R ^ n) H)
    (hHderiv : HasSum (fun n : ℕ =>
      lrWronskianHDerivativeSeriesCoefficient c n * R ^ n) Hderiv)
    (hF : HasSum (fun n : ℕ =>
      lrWronskianFSeriesCoefficient f n * R ^ n) F)
    (hFderiv : HasSum (fun n : ℕ =>
      lrWronskianFDerivativeSeriesCoefficient f n * R ^ n) Fderiv)
    (hcoeff : ∀ n,
      0 ≤ lrWronskianCoefficient lambda a c f n) :
    0 ≤ H * Fderiv - lambda * Hderiv * F := by
  have hHF := lrHasSumCauchyConvolution hH hFderiv
  have hHderivF := lrHasSumCauchyConvolution hHderiv hF
  have hseries := hHF.sub (hHderivF.mul_left lambda)
  have hwr : HasSum (fun n : ℕ =>
      lrWronskianCoefficient lambda a c f n * R ^ n)
      (H * Fderiv - lambda * Hderiv * F) := by
    convert hseries using 1
    · funext n
      rw [lrLow_cauchy_power_identity, lrLow_cauchy_power_identity]
      rw [← lrWronskianConvolutionCoefficient_eq]
      ring
    · ring
  exact hwr.nonneg (fun n =>
    mul_nonneg (hcoeff n) (pow_nonneg hR n))

end CourtadeKumar
