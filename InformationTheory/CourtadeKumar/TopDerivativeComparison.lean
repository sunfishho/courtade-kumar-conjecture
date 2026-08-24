import InformationTheory.CourtadeKumar.TopMainSum

/-! Comparison of the actual cap derivative with the certified full-tail
lower expression. -/

open Set

namespace CourtadeKumar

noncomputable def topMainTerm (c q : ℝ) (n : ℕ) : ℝ :=
  topMainRawTerm (topCapR c q) q n /
    (2 * c ^ 2 * (1 - q))

lemma topMain_hasSum {c q : ℝ}
    (hc : c ∈ Ioo (0 : ℝ) 1) (hq : q ∈ Ioo (0 : ℝ) 1) :
    HasSum (topMainTerm c q)
      (-Real.log (1 - c ^ 2 * q) / (2 * c ^ 2 * q)) := by
  have h := (topMainRaw_cap_hasSum hc hq).mul_left
    (1 / (2 * c ^ 2 * (1 - q)))
  convert h using 1
  · funext n
    unfold topMainTerm
    ring
  · field_simp [hc.1.ne', hq.1.ne', sub_ne_zero.mpr hq.2.ne']

lemma topCapETerm_capCoordinates {c q : ℝ} (n : ℕ)
    (hc : c ∈ Ioo (0 : ℝ) 1) (hq : q ∈ Ioo (0 : ℝ) 1) :
    topCapETerm c (topCapZeta c q) n =
      ((1 - q ^ n) / (1 - q)) *
        (topDn (topCapR c q) n / c ^ 2) /
          (2 * n * (n + 1) * (2 * n + 1)) := by
  have hRne := (topCapR_mem_Ioo hc hq).1.ne'
  have hzq : topCapZeta c q / topCapR c q = q := by
    unfold topCapZeta
    exact mul_div_cancel_left₀ q hRne
  unfold topCapETerm
  dsimp only
  rw [topCertR_capCoordinates hc hq, hzq]

lemma topB0Term_split {c q : ℝ} (n : ℕ)
    (hc : c ∈ Ioo (0 : ℝ) 1) (hq : q ∈ Ioo (0 : ℝ) 1) :
    (2 / (c ^ 2 * (1 - q))) *
        topB0Term (topCapR c q) q (n + 1) =
      topMainTerm c q n -
        topCapETerm c (topCapZeta c q) (n + 1) := by
  rw [topCapETerm_capCoordinates (n + 1) hc hq]
  unfold topB0Term topMainTerm topMainRawTerm
  push_cast
  have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
  have hn2 : (n : ℝ) + 2 ≠ 0 := by positivity
  have hnodd : 2 * ((n : ℝ) + 2) - 1 ≠ 0 := by
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    nlinarith
  have hthree : 3 + 2 * (n : ℝ) ≠ 0 := by
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    nlinarith
  have hthree' : 3 + (n : ℝ) * 2 ≠ 0 := by
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    nlinarith
  have hdenexact : 2 * ((n : ℝ) + 1 + 1) - 1 ≠ 0 := by
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    nlinarith
  field_simp [hc.1.ne', sub_ne_zero.mpr hq.2.ne', hn1, hn2, hnodd, hthree, hthree']
  field_simp [hdenexact]
  ring

/-- Exact split of the simplified common primitive into the logarithmic
main sum and the complete positive tail. -/
theorem topCapB0_fullTail_identity {c q : ℝ}
    (hc : c ∈ Ioo (0 : ℝ) 1) (hq : q ∈ Ioo (0 : ℝ) 1) :
    2 * topCapB0 c q / (c ^ 2 * (1 - q)) =
      -Real.log (1 - c ^ 2 * q) / (2 * c ^ 2 * q) -
        topCapETail c (topCapZeta c q) := by
  have hB := (hasSum_nat_add_iff' 1).2 (topCapB0_hasSum hc hq)
  have hBshift : HasSum
      (fun n : ℕ ↦ topB0Term (topCapR c q) q (n + 1))
      (topCapB0 c q) := by
    convert hB using 1
    simp [topB0Term, topDn]
  have hBscaled := hBshift.mul_left (2 / (c ^ 2 * (1 - q)))
  have hMain := topMain_hasSum hc hq
  have hE : HasSum
      (fun n : ℕ ↦ topCapETerm c (topCapZeta c q) (n + 1))
      (topCapETail c (topCapZeta c q)) := by
    simpa [topCapETail] using
      (summable_topCapETerm hc (topCapZeta_mem_Ioo hc hq)).hasSum
  have hsplit := hMain.sub hE
  have hfun : (fun n : ℕ ↦
      (2 / (c ^ 2 * (1 - q))) *
        topB0Term (topCapR c q) q (n + 1)) =
      (fun n : ℕ ↦ topMainTerm c q n -
        topCapETerm c (topCapZeta c q) (n + 1)) := by
    funext n
    exact topB0Term_split n hc hq
  rw [hfun] at hBscaled
  have heq := hBscaled.unique hsplit
  convert heq using 1 <;> ring

lemma topChannelP_add_capLog {c q : ℝ}
    (hc : c ∈ Ioo (0 : ℝ) 1) (hq : q ∈ Ioo (0 : ℝ) 1) :
    topChannelP c q +
        Real.log (1 - c ^ 2 * q) / (2 * c ^ 2 * q) =
      Real.log (topCapCrossRatio c q) / (2 * c ^ 2 * q) := by
  have hnum := topCapDen_pos hc hq
  have hden := topCapCrossRatio_den_pos hc hq
  unfold topChannelP topCapCrossRatio
  rw [Real.log_div hnum.ne' hden.ne']
  ring

/-- The actual negative cap derivative dominates the fully analytic
certificate expression. -/
theorem topCapJLower_le_topCapJ {c q : ℝ}
    (hc : c ∈ Ioo (0 : ℝ) 1) (hq : q ∈ Ioo (0 : ℝ) 1) :
    topCapJLower c q ≤ topCapJ c q := by
  have hB := topCapB_le_cB0 hc hq
  have hden : 0 < c ^ 3 * (1 - q) :=
    mul_pos (pow_pos hc.1 3) (sub_pos.mpr hq.2)
  have hdiv :
      2 * topCapB c q / (c ^ 3 * (1 - q)) ≤
        2 * (c * topCapB0 c q) / (c ^ 3 * (1 - q)) := by
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hB (by norm_num)) hden.le
  have hJ := topCapJ_eq_B hc hq
  have htail := topCapB0_fullTail_identity hc hq
  have hscale :
      2 * (c * topCapB0 c q) / (c ^ 3 * (1 - q)) =
        2 * topCapB0 c q / (c ^ 2 * (1 - q)) := by
    field_simp [hc.1.ne', sub_ne_zero.mpr hq.2.ne']
  rw [hscale] at hdiv
  have hcross := topChannelP_add_capLog hc hq
  rw [topCapJLower_eq_crossRatio hc hq]
  calc
    topChannelW (topCapR c q) +
          Real.log (topCapCrossRatio c q) / (2 * c ^ 2 * q) +
        topCapETail c (topCapZeta c q) =
        topChannelW (topCapR c q) +
          (topChannelP c q +
            Real.log (1 - c ^ 2 * q) / (2 * c ^ 2 * q)) +
          topCapETail c (topCapZeta c q) := by rw [hcross]
    _ = topChannelW (topCapR c q) + topChannelP c q -
          2 * topCapB0 c q / (c ^ 2 * (1 - q)) := by
      rw [htail]
      ring
    _ ≤ topChannelW (topCapR c q) + topChannelP c q -
          2 * topCapB c q / (c ^ 3 * (1 - q)) := by
      exact sub_le_sub_left hdiv _
    _ = topCapJ c q := by rw [hJ]; ring

/-- The audited rational certificate therefore supplies the uniform margin
for the actual moving-cap derivative. -/
theorem topCapJ_ge_margin {c q : ℝ}
    (hc : c ∈ Ioo (0 : ℝ) 1) (hq : q ∈ Ioo (0 : ℝ) 1) :
    (1 : ℝ) / 100 ≤ topCapJ c q :=
  (topCapJLower_ge_margin hc hq).trans (topCapJLower_le_topCapJ hc hq)

end CourtadeKumar
