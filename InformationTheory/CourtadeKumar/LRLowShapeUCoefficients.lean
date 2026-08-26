import InformationTheory.CourtadeKumar.LRLowShapeUClosure

/-! Exact identification of the sign-explicit low-shape `U` coefficients
with the Cauchy-product coefficients of the analytic reserve. -/

open Set
open scoped BigOperators

namespace CourtadeKumar

lemma lrLow_weighted_geometric_identity
    (xi : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    lrLowH xi n + (1 - xi) *
        ∑ k ∈ Finset.range (n - 1),
          xi ^ (n - (k + 1)) * ((k + 1 : ℕ) : ℝ) =
      (n : ℝ) * xi := by
  induction n, hn using Nat.le_induction with
  | base => simp [lrLowH]
  | succ n hn ih =>
      rw [show n + 1 - 1 = n by omega]
      rw [show lrLowH xi (n + 1) = lrLowH xi n + xi ^ (n + 1) by
        unfold lrLowH
        rw [Finset.sum_range_succ]]
      have hsplit :
          ∑ k ∈ Finset.range n,
              xi ^ (n + 1 - (k + 1)) * ((k + 1 : ℕ) : ℝ) =
            xi * ∑ k ∈ Finset.range (n - 1),
                xi ^ (n - (k + 1)) * ((k + 1 : ℕ) : ℝ) + (n : ℝ) * xi := by
        conv_lhs => rw [show n = (n - 1) + 1 by omega, Finset.sum_range_succ]
        congr 1
        · rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k hk
          have hkn : k + 1 < n := by
            have := Finset.mem_range.mp hk
            omega
          simp only [Nat.sub_add_cancel hn]
          rw [show n + 1 - (k + 1) = (n - (k + 1)) + 1 by omega,
            pow_succ']
          ring
        · norm_num [Nat.cast_sub hn]
          ring
      have hgeom :
          (1 - xi) * lrLowH xi n = xi - xi ^ (n + 1) := by
        unfold lrLowH
        rw [show (∑ k ∈ Finset.range n, xi ^ (k + 1)) =
            xi * ∑ k ∈ Finset.range n, xi ^ k by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k hk
          rw [pow_succ']]
        have h := geom_sum_mul_neg xi n
        calc
          (1 - xi) * (xi * ∑ k ∈ Finset.range n, xi ^ k) =
              xi * ((∑ k ∈ Finset.range n, xi ^ k) * (1 - xi)) := by ring
          _ = xi * (1 - xi ^ n) := by rw [h]
          _ = xi - xi ^ (n + 1) := by rw [pow_succ']; ring
      rw [hsplit]
      push_cast
      rw [pow_succ']
      norm_num only [Nat.cast_add, Nat.cast_one] at ih hsplit ⊢
      linear_combination xi * ih + hgeom

noncomputable def lrLowUConvolutionCoeff
    (beta xi : ℝ) (eta r : ℕ → ℝ) (n : ℕ) : ℝ :=
  beta * (n + 1) * eta (n + 1) +
    xi / 2 * (n + 1) * r (n + 1) +
    ∑ k ∈ Finset.range n,
      (xi ^ (k + 1) / (2 * ((k + 1 : ℕ) : ℝ)) *
          ((n - k : ℕ) : ℝ) * eta (n - k) -
        (1 - xi) * xi ^ (k + 1) / 2 *
          ((n - k : ℕ) : ℝ) * r (n - k))

lemma lrLowUConvolutionCoeff_eq_signExplicit
    (beta xi : ℝ) (eta r : ℕ → ℝ) (n : ℕ) :
    lrLowUConvolutionCoeff beta xi eta r n =
      lrLowUSignExplicit beta xi eta r (n + 1) := by
  have hEta :
      ∑ k ∈ Finset.range n,
          xi ^ (k + 1) / (2 * ((k + 1 : ℕ) : ℝ)) *
            ((n - k : ℕ) : ℝ) * eta (n - k) =
        ∑ k ∈ Finset.range n,
          lrLowEtaWeight xi (n + 1) k * eta (k + 1) := by
    rw [← Finset.sum_range_reflect
      (fun k : ℕ ↦ xi ^ (k + 1) / (2 * ((k + 1 : ℕ) : ℝ)) *
        ((n - k : ℕ) : ℝ) * eta (n - k)) n]
    apply Finset.sum_congr rfl
    intro k hk
    have hklt : k < n := Finset.mem_range.mp hk
    unfold lrLowEtaWeight
    rw [show n - 1 - k + 1 = n - k by omega]
    rw [show n + 1 - (k + 1) = n - k by omega]
    rw [show n - (n - 1 - k) = k + 1 by omega]
    norm_num only [Nat.cast_add, Nat.cast_one]
    ring
  have hR :
      ∑ k ∈ Finset.range n,
          xi ^ (k + 1) * ((n - k : ℕ) : ℝ) * r (n - k) =
        ∑ k ∈ Finset.range n,
          xi ^ (n + 1 - (k + 1)) * ((k + 1 : ℕ) : ℝ) * r (k + 1) := by
    rw [← Finset.sum_range_reflect
      (fun k : ℕ ↦ xi ^ (k + 1) * ((n - k : ℕ) : ℝ) * r (n - k)) n]
    apply Finset.sum_congr rfl
    intro k hk
    have hklt : k < n := Finset.mem_range.mp hk
    rw [show n - 1 - k + 1 = n - k by omega]
    rw [show n + 1 - (k + 1) = n - k by omega]
    rw [show n - (n - 1 - k) = k + 1 by omega]
  have hGeom := lrLow_weighted_geometric_identity xi
    (show 1 ≤ n + 1 by omega)
  have hCorrection :
      (1 - xi) / 2 *
          ∑ k ∈ Finset.range n,
            xi ^ (n + 1 - (k + 1)) * ((k + 1 : ℕ) : ℝ) *
              (r (n + 1) - r (k + 1)) =
        (1 - xi) / 2 *
            (∑ k ∈ Finset.range n,
              xi ^ (n + 1 - (k + 1)) * ((k + 1 : ℕ) : ℝ)) * r (n + 1) -
          (1 - xi) / 2 *
            ∑ k ∈ Finset.range n,
              xi ^ (n + 1 - (k + 1)) * ((k + 1 : ℕ) : ℝ) * r (k + 1) := by
    rw [show (∑ k ∈ Finset.range n,
        xi ^ (n + 1 - (k + 1)) * ((k + 1 : ℕ) : ℝ) *
          (r (n + 1) - r (k + 1))) =
        (∑ k ∈ Finset.range n,
          xi ^ (n + 1 - (k + 1)) * ((k + 1 : ℕ) : ℝ)) * r (n + 1) -
        ∑ k ∈ Finset.range n,
          xi ^ (n + 1 - (k + 1)) * ((k + 1 : ℕ) : ℝ) * r (k + 1) by
      rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro k hk
      ring]
    ring
  unfold lrLowUConvolutionCoeff lrLowUSignExplicit
  rw [show n + 1 - 1 = n by omega]
  rw [Finset.sum_sub_distrib, hEta]
  rw [show (∑ k ∈ Finset.range n,
      (1 - xi) * xi ^ (k + 1) / 2 * ((n - k : ℕ) : ℝ) * r (n - k)) =
      (1 - xi) / 2 * ∑ k ∈ Finset.range n,
        xi ^ (k + 1) * ((n - k : ℕ) : ℝ) * r (n - k) by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    ring, hR]
  norm_num only [Nat.cast_add, Nat.cast_one]
  norm_num only [Nat.cast_add, Nat.cast_one] at hCorrection hGeom
  rw [show n + 1 - 1 = n by omega] at hGeom
  rw [hCorrection]
  linear_combination -(r (n + 1) / 2) * hGeom

end CourtadeKumar
