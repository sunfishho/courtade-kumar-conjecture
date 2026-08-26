import InformationTheory.CourtadeKumar.LRLowShapeSeriesBounds

/-! The sign-explicit reduction of the low-shape midpoint certificate `(U)`
to the two scalar inequalities in the audited proof. -/

open Set
open scoped BigOperators

namespace CourtadeKumar

/-- `Hₙ = ξ + ⋯ + ξⁿ`. -/
def lrLowH (xi : ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, xi ^ (k + 1)

/-- The positive weight multiplying the `j`th tail average in the `B Y₀`
coefficient, with `j = k+1`. -/
noncomputable def lrLowEtaWeight (xi : ℝ) (n k : ℕ) : ℝ :=
  xi ^ (n - (k + 1)) * ((k + 1 : ℕ) : ℝ) /
    (2 * ((n - (k + 1) : ℕ) : ℝ))

/-- The comparison coefficient `Kₙ` from the manuscript. -/
noncomputable def lrLowK (beta xi : ℝ) (b : ℕ → ℝ) (n : ℕ) : ℝ :=
  beta * n +
    ∑ k ∈ Finset.range (n - 1),
      lrLowEtaWeight xi n k * (b (k + 1) / b n)

/-- The coefficient after Abel summation has exposed all terms whose signs
are immediate. -/
noncomputable def lrLowUSignExplicit
    (beta xi : ℝ) (eta r : ℕ → ℝ) (n : ℕ) : ℝ :=
  beta * n * eta n +
    ∑ k ∈ Finset.range (n - 1),
      lrLowEtaWeight xi n k * eta (k + 1) +
    lrLowH xi n / 2 * r n +
    (1 - xi) / 2 *
      ∑ k ∈ Finset.range (n - 1),
        xi ^ (n - (k + 1)) * (k + 1) * (r n - r (k + 1))

lemma lrLowH_nonneg
    {xi : ℝ} (hxi : 0 ≤ xi) (n : ℕ) :
    0 ≤ lrLowH xi n := by
  unfold lrLowH
  exact Finset.sum_nonneg fun k _ ↦ pow_nonneg hxi _

lemma lrLowEtaWeight_nonneg
    {xi : ℝ} (hxi : 0 ≤ xi) {n k : ℕ}
    (hk : k ∈ Finset.range (n - 1)) :
    0 ≤ lrLowEtaWeight xi n k := by
  have hkn : k + 1 < n := by
    have hk' := Finset.mem_range.mp hk
    omega
  unfold lrLowEtaWeight
  exact div_nonneg
    (mul_nonneg (pow_nonneg hxi _) (Nat.cast_nonneg _))
    (mul_nonneg (by norm_num) (Nat.cast_nonneg _))

/-- Tail-average comparison and monotonicity of `r` reduce the full
sign-explicit coefficient to `Kₙ ηₙ + Hₙ rₙ/2`. -/
theorem lrLowUExplicit_ge_reduced
    {beta xi : ℝ} {b eta r : ℕ → ℝ} {n : ℕ}
    (hxi : xi ∈ Icc (0 : ℝ) 1)
    (heta : ∀ k ∈ Finset.range (n - 1),
      b (k + 1) / b n * eta n ≤ eta (k + 1))
    (hr : ∀ k ∈ Finset.range (n - 1), r (k + 1) ≤ r n) :
    lrLowK beta xi b n * eta n + lrLowH xi n / 2 * r n ≤
      lrLowUSignExplicit beta xi eta r n := by
  have hB :
      (∑ k ∈ Finset.range (n - 1),
          lrLowEtaWeight xi n k * (b (k + 1) / b n)) * eta n ≤
        ∑ k ∈ Finset.range (n - 1),
          lrLowEtaWeight xi n k * eta (k + 1) := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro k hk
    calc
      (lrLowEtaWeight xi n k * (b (k + 1) / b n)) * eta n =
          lrLowEtaWeight xi n k *
            (b (k + 1) / b n * eta n) := by ring
      _ ≤ lrLowEtaWeight xi n k * eta (k + 1) :=
        mul_le_mul_of_nonneg_left (heta k hk)
          (lrLowEtaWeight_nonneg hxi.1 hk)
  have hCorrection :
      0 ≤ (1 - xi) / 2 *
        ∑ k ∈ Finset.range (n - 1),
          xi ^ (n - (k + 1)) * (k + 1) * (r n - r (k + 1)) := by
    apply mul_nonneg (div_nonneg (sub_nonneg.mpr hxi.2) (by norm_num))
    apply Finset.sum_nonneg
    intro k hk
    exact mul_nonneg
      (mul_nonneg (pow_nonneg hxi.1 _) (by positivity))
      (sub_nonneg.mpr (hr k hk))
  unfold lrLowK lrLowUSignExplicit
  rw [add_mul]
  nlinarith

/-- The manuscript's sign split: the first scalar inequality is used when
`ηₙ ≥ 0`, and the second when `ηₙ < 0`. -/
theorem lrLowU_reduced_nonneg_of_two_scalars
    {beta A H K eta r : ℝ} {n : ℕ}
    (hH : 0 ≤ H)
    (hKLower : beta * H ≤ K)
    (hKUpper : K ≤ (n : ℝ) * A)
    (hfirst : 0 ≤ r + 2 * beta * eta)
    (hsecond : 0 ≤ H * r + 2 * (n : ℝ) * A * eta) :
    0 ≤ K * eta + H / 2 * r := by
  by_cases heta : 0 ≤ eta
  · have hmargin : 0 ≤ (K - beta * H) * eta :=
      mul_nonneg (sub_nonneg.mpr hKLower) heta
    have hscaled : 0 ≤ H / 2 * (r + 2 * beta * eta) :=
      mul_nonneg (div_nonneg hH (by norm_num)) hfirst
    nlinarith
  · have hetaNeg : eta ≤ 0 := le_of_not_ge heta
    have hmargin : 0 ≤ ((n : ℝ) * A - K) * (-eta) :=
      mul_nonneg (sub_nonneg.mpr hKUpper) (neg_nonneg.mpr hetaNeg)
    have hscaled : 0 ≤
        (H * r + 2 * (n : ℝ) * A * eta) / 2 :=
      div_nonneg hsecond (by norm_num)
    nlinarith

/-- Complete abstract `U` reduction.  Once the tail-average comparisons,
the two bounds on `Kₙ`, and the two scalar certificates are supplied, the
coefficient is nonnegative. -/
theorem lrLowUExplicit_nonneg_of_two_scalars
    {beta A xi : ℝ} {b eta r : ℕ → ℝ} {n : ℕ}
    (hxi : xi ∈ Icc (0 : ℝ) 1)
    (heta : ∀ k ∈ Finset.range (n - 1),
      b (k + 1) / b n * eta n ≤ eta (k + 1))
    (hr : ∀ k ∈ Finset.range (n - 1), r (k + 1) ≤ r n)
    (hKLower : beta * lrLowH xi n ≤ lrLowK beta xi b n)
    (hKUpper : lrLowK beta xi b n ≤ (n : ℝ) * A)
    (hfirst : 0 ≤ r n + 2 * beta * eta n)
    (hsecond : 0 ≤
      lrLowH xi n * r n + 2 * (n : ℝ) * A * eta n) :
    0 ≤ lrLowUSignExplicit beta xi eta r n := by
  have hreduced := lrLowU_reduced_nonneg_of_two_scalars
    (lrLowH_nonneg hxi.1 n) hKLower hKUpper hfirst hsecond
  exact hreduced.trans
    (lrLowUExplicit_ge_reduced hxi heta hr)

end CourtadeKumar
