import InformationTheory.CourtadeKumar.TopWBound

/-! Exact algebra behind the ten-term positive tail in the TOP full-cap
certificate. -/

open Set
open scoped BigOperators

namespace CourtadeKumar

/-- The factored form of
`D_n(R) = 1 - (n+1)R^n + nR^(n+1)`. -/
def topDn (R : ℝ) (n : ℕ) : ℝ :=
  (1 - R) ^ 2 *
    ∑ j ∈ Finset.range n, (j + 1 : ℝ) * R ^ j

lemma topDn_div_c_sq {c z : ℝ} (hc : c ≠ 0) (n : ℕ) :
    topDn (topCertR c z) n / c ^ 2 = topCertDnOverC2 c z n := by
  unfold topDn topCertDnOverC2 topCertR
  field_simp [hc]
  ring

private lemma top_geometric_ratio {q : ℝ} (hq : q ≠ 1) (n : ℕ) :
    (1 - q ^ n) / (1 - q) = ∑ k ∈ Finset.range n, q ^ k := by
  rw [div_eq_iff (sub_ne_zero.mpr hq.symm)]
  exact (geom_sum_mul_neg q n).symm

lemma topCertGeometric_div_R9 {c z : ℝ} {n : ℕ}
    (hR : topCertR c z ≠ 0) (hn : n ≤ 10) :
    topCertGeometric c z n / topCertR c z ^ 9 =
      ∑ k ∈ Finset.range n, (z / topCertR c z) ^ k := by
  unfold topCertGeometric
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k hk
  have hklt : k < n := Finset.mem_range.mp hk
  have hk9 : k ≤ 9 := by omega
  rw [div_pow]
  field_simp [hR]
  rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hk9]

/-- The geometric factor in a tail summand, after the square substitution
`q = z / R`, is exactly the factor stored in the polynomial certificate. -/
lemma top_tail_geometric_identity {c z : ℝ} {n : ℕ}
    (hR : topCertR c z ≠ 0) (hq : z / topCertR c z ≠ 1)
    (hn : n ≤ 10) :
    (1 - (z / topCertR c z) ^ n) /
        (1 - z / topCertR c z) =
      topCertGeometric c z n / topCertR c z ^ 9 := by
  rw [top_geometric_ratio hq]
  exact (topCertGeometric_div_R9 hR hn).symm

/-- One summand of the positive tail `E(c,q)` on the cap, expressed in
the square coordinates `(c,z)` with `q = z / R`. -/
noncomputable def topCapETerm (c z : ℝ) (n : ℕ) : ℝ :=
  let R := topCertR c z
  let q := z / R
  ((1 - q ^ n) / (1 - q)) * (topDn R n / c ^ 2) /
    (2 * n * (n + 1) * (2 * n + 1))

noncomputable def topCapE10 (c z : ℝ) : ℝ :=
  ∑ n ∈ Finset.range 10, topCapETerm c z (n + 1)

lemma topCapETerm_eq_certificateTerm {c z : ℝ} {n : ℕ}
    (hc : c ≠ 0) (hR : topCertR c z ≠ 0)
    (hq : z / topCertR c z ≠ 1) (hn : n ≤ 10) :
    topCapETerm c z n =
      ((1 : ℝ) / (2 * n * (n + 1) * (2 * n + 1)) *
        topCertDnOverC2 c z n * topCertGeometric c z n) /
          topCertR c z ^ 9 := by
  unfold topCapETerm
  dsimp only
  rw [top_tail_geometric_identity hR hq hn, topDn_div_c_sq hc]
  ring

/-- The first ten analytic tail summands are exactly the rational function
encoded by `topCertEnum`. -/
theorem topCapE10_eq_certificate {c z : ℝ}
    (hc : c ∈ Ioo (0 : ℝ) 1) (hz : z ∈ Ioo (0 : ℝ) 1) :
    topCapE10 c z = topCertEnum c z / topCertR c z ^ 9 := by
  have hRmem := topCertR_mem_Ioo hc hz
  have hzR : z < topCertR c z := by
    have hc2lt : c ^ 2 < 1 := by nlinarith [hc.1, hc.2]
    have hprod : 0 < (1 - c ^ 2) * (1 - z) :=
      mul_pos (sub_pos.mpr hc2lt) (sub_pos.mpr hz.2)
    unfold topCertR
    nlinarith
  have hq : z / topCertR c z ≠ 1 :=
    ne_of_lt (div_lt_one hRmem.1 |>.2 hzR)
  unfold topCapE10 topCertEnum
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro n hn
  dsimp only
  exact topCapETerm_eq_certificateTerm hc.1.ne' hRmem.1.ne' hq
    (by have := Finset.mem_range.mp hn; omega)

/-- Fully analytic form of the exact finite certificate: both the `w`
polynomial and the encoded ten-term tail have been replaced by their genuine
cap quantities. -/
theorem topFiniteClaim_with_capE10 {c z : ℝ}
    (hc : c ∈ Ioo (0 : ℝ) 1) (hz : z ∈ Ioo (0 : ℝ) 1) :
    (1 : ℝ) / 100 ≤
      (topCertR c z * Real.log 2 - topPhi (Real.sqrt (topCertR c z))) /
          (1 - topCertR c z) +
        Real.log (topCertX c z) / (2 * c ^ 2 * topCapQ c z) +
          topCapE10 c z := by
  apply topFiniteClaim_with_capRatio hc hz
  rw [topCapE10_eq_certificate hc hz]

end CourtadeKumar
