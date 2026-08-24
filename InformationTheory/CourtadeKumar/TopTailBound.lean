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

lemma topDn_eq_closed (R : ℝ) (n : ℕ) :
    topDn R n = 1 - (n + 1) * R ^ n + n * R ^ (n + 1) := by
  induction n with
  | zero => simp [topDn]
  | succ n ih =>
      unfold topDn at ih ⊢
      rw [Finset.sum_range_succ]
      push_cast
      rw [pow_succ R (n + 1)]
      linear_combination ih

lemma topDn_nonneg {R : ℝ} (hR : R ∈ Icc (0 : ℝ) 1) (n : ℕ) :
    0 ≤ topDn R n := by
  unfold topDn
  apply mul_nonneg (sq_nonneg _)
  apply Finset.sum_nonneg
  intro j hj
  exact mul_nonneg (by positivity) (pow_nonneg hR.1 j)

lemma topDn_le_one {R : ℝ} (hR : R ∈ Icc (0 : ℝ) 1) (n : ℕ) :
    topDn R n ≤ 1 := by
  rw [topDn_eq_closed]
  have hp : 0 ≤ R ^ n := pow_nonneg hR.1 n
  have hnterm : 0 ≤ (n : ℝ) * (1 - R) :=
    mul_nonneg (Nat.cast_nonneg n) (sub_nonneg.mpr hR.2)
  have hfactor : 0 ≤ (1 : ℝ) + n * (1 - R) := by linarith
  rw [pow_succ]
  nlinarith [mul_nonneg hp hfactor]

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

lemma topCertZ_lt_R {c z : ℝ}
    (hc : c ∈ Ioo (0 : ℝ) 1) (hz : z ∈ Ioo (0 : ℝ) 1) :
    z < topCertR c z := by
  have hc2lt : c ^ 2 < 1 := by nlinarith [hc.1, hc.2]
  have hprod : 0 < (1 - c ^ 2) * (1 - z) :=
    mul_pos (sub_pos.mpr hc2lt) (sub_pos.mpr hz.2)
  unfold topCertR
  nlinarith

lemma topCapQ_mem_Ioo {c z : ℝ}
    (hc : c ∈ Ioo (0 : ℝ) 1) (hz : z ∈ Ioo (0 : ℝ) 1) :
    topCapQ c z ∈ Ioo (0 : ℝ) 1 := by
  have hR := topCertR_mem_Ioo hc hz
  exact ⟨topCapQ_pos hc hz, by
    unfold topCapQ
    exact (div_lt_one hR.1).2 (topCertZ_lt_R hc hz)⟩

lemma topCapETerm_nonneg {c z : ℝ}
    (hc : c ∈ Ioo (0 : ℝ) 1) (hz : z ∈ Ioo (0 : ℝ) 1) (n : ℕ) :
    0 ≤ topCapETerm c z n := by
  have hR := topCertR_mem_Ioo hc hz
  have hq := topCapQ_mem_Ioo hc hz
  have hqpow : (z / topCertR c z) ^ n ≤ 1 :=
    pow_le_one₀ hq.1.le hq.2.le
  unfold topCapQ at hq
  unfold topCapETerm
  dsimp only
  apply div_nonneg
  · apply mul_nonneg
    · exact div_nonneg (sub_nonneg.mpr hqpow) (sub_nonneg.mpr hq.2.le)
    · exact div_nonneg (topDn_nonneg ⟨hR.1.le, hR.2.le⟩ n) (sq_nonneg c)
  · positivity

lemma topCapE10_nonneg {c z : ℝ}
    (hc : c ∈ Ioo (0 : ℝ) 1) (hz : z ∈ Ioo (0 : ℝ) 1) :
    0 ≤ topCapE10 c z := by
  unfold topCapE10
  exact Finset.sum_nonneg fun n hn ↦ topCapETerm_nonneg hc hz (n + 1)

private lemma topCapETerm_le_pSeries {c z : ℝ}
    (hc : c ∈ Ioo (0 : ℝ) 1) (hz : z ∈ Ioo (0 : ℝ) 1) (n : ℕ) :
    topCapETerm c z (n + 1) ≤
      (1 / ((1 - topCapQ c z) * c ^ 2)) *
        (1 / ((n + 1 : ℝ) ^ 2)) := by
  have hR := topCertR_mem_Ioo hc hz
  have hq := topCapQ_mem_Ioo hc hz
  have hqpow0 : 0 ≤ topCapQ c z ^ (n + 1) := pow_nonneg hq.1.le _
  have hratio_nonneg : 0 ≤
      (1 - topCapQ c z ^ (n + 1)) / (1 - topCapQ c z) :=
    div_nonneg (sub_nonneg.mpr (pow_le_one₀ hq.1.le hq.2.le))
      (sub_nonneg.mpr hq.2.le)
  have hratio :
      (1 - topCapQ c z ^ (n + 1)) / (1 - topCapQ c z) ≤
        1 / (1 - topCapQ c z) := by
    exact div_le_div_of_nonneg_right (by linarith) (sub_nonneg.mpr hq.2.le)
  have hDnonneg : 0 ≤ topDn (topCertR c z) (n + 1) / c ^ 2 :=
    div_nonneg (topDn_nonneg ⟨hR.1.le, hR.2.le⟩ _) (sq_nonneg c)
  have hDone : topDn (topCertR c z) (n + 1) / c ^ 2 ≤ 1 / c ^ 2 :=
    div_le_div_of_nonneg_right (topDn_le_one ⟨hR.1.le, hR.2.le⟩ _)
      (sq_nonneg c)
  have hproduct :
      ((1 - topCapQ c z ^ (n + 1)) / (1 - topCapQ c z)) *
          (topDn (topCertR c z) (n + 1) / c ^ 2) ≤
        1 / ((1 - topCapQ c z) * c ^ 2) := by
    calc
      _ ≤ (1 / (1 - topCapQ c z)) * (1 / c ^ 2) :=
        mul_le_mul hratio hDone hDnonneg
          (one_div_nonneg.mpr (sub_nonneg.mpr hq.2.le))
      _ = _ := by
        field_simp [hc.1.ne', sub_ne_zero.mpr hq.2.ne]
  let m : ℝ := (n : ℝ) + 1
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hm : 1 ≤ m := by dsimp [m]; linarith
  have hm0 : 0 ≤ m := zero_le_one.trans hm
  have hmpos : 0 < m := zero_lt_one.trans_le hm
  have hfirst : m ^ 2 ≤ 2 * m * (m + 1) := by
    rw [pow_two]
    nlinarith [mul_nonneg hm0 hm0]
  have hlast : 1 ≤ 2 * m + 1 := by nlinarith
  have hden : m ^ 2 ≤ 2 * m * (m + 1) * (2 * m + 1) :=
    hfirst.trans (le_mul_of_one_le_right (by positivity) hlast)
  unfold topCapETerm
  dsimp only
  push_cast
  have hratio_nonneg' : 0 ≤
      (1 - (z / topCertR c z) ^ (n + 1)) / (1 - z / topCertR c z) := by
    simpa [topCapQ] using hratio_nonneg
  have hDnonneg' : 0 ≤ topDn (topCertR c z) (n + 1) / c ^ 2 := hDnonneg
  have hproduct' :
      ((1 - (z / topCertR c z) ^ (n + 1)) / (1 - z / topCertR c z)) *
          (topDn (topCertR c z) (n + 1) / c ^ 2) ≤
        1 / ((1 - z / topCertR c z) * c ^ 2) := by
    simpa [topCapQ] using hproduct
  have hKnonneg : 0 ≤ 1 / ((1 - z / topCertR c z) * c ^ 2) := by
    apply one_div_nonneg.mpr
    exact mul_nonneg (sub_nonneg.mpr hq.2.le) (sq_nonneg c)
  change
    (((1 - (z / topCertR c z) ^ (n + 1)) / (1 - z / topCertR c z)) *
      (topDn (topCertR c z) (n + 1) / c ^ 2)) /
        (2 * m * (m + 1) * (2 * m + 1)) ≤ _
  calc
    _ ≤ (1 / ((1 - z / topCertR c z) * c ^ 2)) / m ^ 2 :=
      div_le_div₀ hKnonneg hproduct' (pow_pos hmpos 2) hden
    _ = _ := by simp [topCapQ, m]; ring

theorem summable_topCapETerm {c z : ℝ}
    (hc : c ∈ Ioo (0 : ℝ) 1) (hz : z ∈ Ioo (0 : ℝ) 1) :
    Summable (fun n : ℕ ↦ topCapETerm c z (n + 1)) := by
  apply Summable.of_nonneg_of_le
    (fun n ↦ topCapETerm_nonneg hc hz (n + 1))
    (fun n ↦ topCapETerm_le_pSeries hc hz n)
  have hp : Summable (fun n : ℕ ↦ 1 / ((n + 1 : ℝ) ^ 2)) := by
    simpa using (summable_nat_add_iff 1).2
      (Real.summable_one_div_nat_pow.mpr one_lt_two)
  exact hp.mul_left (1 / ((1 - topCapQ c z) * c ^ 2))

/-- The full nonnegative tail `E(c,q)` after the cap square substitution. -/
noncomputable def topCapETail (c z : ℝ) : ℝ :=
  ∑' n : ℕ, topCapETerm c z (n + 1)

theorem topCapE10_le_tail {c z : ℝ}
    (hc : c ∈ Ioo (0 : ℝ) 1) (hz : z ∈ Ioo (0 : ℝ) 1) :
    topCapE10 c z ≤ topCapETail c z := by
  unfold topCapE10 topCapETail
  exact (summable_topCapETerm hc hz).sum_le_tsum (Finset.range 10)
    (fun n hn ↦ topCapETerm_nonneg hc hz (n + 1))

theorem topCapETail_nonneg {c z : ℝ}
    (hc : c ∈ Ioo (0 : ℝ) 1) (hz : z ∈ Ioo (0 : ℝ) 1) :
    0 ≤ topCapETail c z := by
  unfold topCapETail
  exact tsum_nonneg fun n ↦ topCapETerm_nonneg hc hz (n + 1)

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
  have hzR : z < topCertR c z := topCertZ_lt_R hc hz
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

/-- The exact certificate lower bound with the complete analytic tail. -/
theorem topFiniteClaim_with_capETail {c z : ℝ}
    (hc : c ∈ Ioo (0 : ℝ) 1) (hz : z ∈ Ioo (0 : ℝ) 1) :
    (1 : ℝ) / 100 ≤
      (topCertR c z * Real.log 2 - topPhi (Real.sqrt (topCertR c z))) /
          (1 - topCertR c z) +
        Real.log (topCertX c z) / (2 * c ^ 2 * topCapQ c z) +
          topCapETail c z := by
  have hfinite := topFiniteClaim_with_capE10 hc hz
  have htail := topCapE10_le_tail hc hz
  linarith

end CourtadeKumar
