import InformationTheory.CourtadeKumar.LRLowShapeUAssembly
import InformationTheory.CourtadeKumar.BernsteinCertificate

/-! Exact tensor-Bernstein replay of the low-shape `U` first-difference
minorant.  This is the degree `(13,1)` row of the audited certificate table. -/

open Set

namespace CourtadeKumar

noncomputable def lrLowUDifference (v z : ℝ) : ℝ :=
  let x := (17 / 20 : ℝ) * z
  lrLowTailH v - x * (1 + v) -
    2 * lrAtanh5Upper (v / (2 + v)) * x * (1 + v ^ 2) / (1 + v)

noncomputable def lrLowUDifferenceBase (v : ℝ) : ℝ :=
  (1 + v) ^ 2 * (2 + v) ^ 9

def lrLowUDifferenceCoeff (i : Fin 14) (j : Fin 2) : ℚ :=
  ![
    ![(2048 : ℚ), 8064/5],
    ![(38912/13 : ℚ), 2240],
    ![(170240/39 : ℚ), 120736/39],
    ![(908288/143 : ℚ), 9121088/2145],
    ![(1318656/143 : ℚ), 62154992/10725],
    ![(1910016/143 : ℚ), 754796984/96525],
    ![(2760048/143 : ℚ), 335077736/32175],
    ![(3978720/143 : ℚ), 3069766277/225225],
    ![(5721192/143 : ℚ), 7844512717/450450],
    ![(8205624/143 : ℚ), 19364199157/900900],
    ![(11737629/143 : ℚ), 45315675529/1801800],
    ![(1522152/13 : ℚ), 145066255039/5405400],
    ![(2165130/13 : ℚ), 10595863247/450450],
    ![(236196 : ℚ), 331868297/34650]
  ] i j

lemma lrLowUDifferenceCoeff_nonneg (i : Fin 14) (j : Fin 2) :
    0 ≤ lrLowUDifferenceCoeff i j := by
  fin_cases i <;> fin_cases j <;> norm_num [lrLowUDifferenceCoeff]

noncomputable def lrLowUDifferenceRow
    (c₀ c₁ : ℝ) (i : ℕ) (v z : ℝ) : ℝ :=
  (c₀ * (1 - z) + c₁ * z) * bernsteinBasis 13 i v

noncomputable def lrLowUDifferenceBernstein (v z : ℝ) : ℝ :=
  lrLowUDifferenceRow 2048 (8064/5) 0 v z +
  lrLowUDifferenceRow (38912/13) 2240 1 v z +
  lrLowUDifferenceRow (170240/39) (120736/39) 2 v z +
  lrLowUDifferenceRow (908288/143) (9121088/2145) 3 v z +
  lrLowUDifferenceRow (1318656/143) (62154992/10725) 4 v z +
  lrLowUDifferenceRow (1910016/143) (754796984/96525) 5 v z +
  lrLowUDifferenceRow (2760048/143) (335077736/32175) 6 v z +
  lrLowUDifferenceRow (3978720/143) (3069766277/225225) 7 v z +
  lrLowUDifferenceRow (5721192/143) (7844512717/450450) 8 v z +
  lrLowUDifferenceRow (8205624/143) (19364199157/900900) 9 v z +
  lrLowUDifferenceRow (11737629/143) (45315675529/1801800) 10 v z +
  lrLowUDifferenceRow (1522152/13) (145066255039/5405400) 11 v z +
  lrLowUDifferenceRow (2165130/13) (10595863247/450450) 12 v z +
  lrLowUDifferenceRow 236196 (331868297/34650) 13 v z

lemma lrLowUDifferenceRow_nonneg
    {c₀ c₁ v z : ℝ} {i : ℕ} (hc₀ : 0 ≤ c₀) (hc₁ : 0 ≤ c₁)
    (hv : v ∈ Icc (0 : ℝ) 1) (hz : z ∈ Icc (0 : ℝ) 1) :
    0 ≤ lrLowUDifferenceRow c₀ c₁ i v z := by
  unfold lrLowUDifferenceRow
  exact mul_nonneg
    (add_nonneg (mul_nonneg hc₀ (sub_nonneg.mpr hz.2))
      (mul_nonneg hc₁ hz.1))
    (bernsteinBasis_nonneg hv)

lemma lrLowUDifferenceBernstein_nonneg
    {v z : ℝ} (hv : v ∈ Icc (0 : ℝ) 1)
    (hz : z ∈ Icc (0 : ℝ) 1) :
    0 ≤ lrLowUDifferenceBernstein v z := by
  unfold lrLowUDifferenceBernstein
  repeat' apply add_nonneg
  all_goals apply lrLowUDifferenceRow_nonneg (hv := hv) (hz := hz) <;> norm_num

set_option maxHeartbeats 2000000 in
lemma lrLowUDifference_mul_base_eq_bernstein
    {v z : ℝ} (hv : v ∈ Icc (0 : ℝ) 1) :
    lrLowUDifference v z * lrLowUDifferenceBase v =
      lrLowUDifferenceBernstein v z := by
  have h1 : 1 + v ≠ 0 := by linarith [hv.1]
  have h2 : 2 + v ≠ 0 := by linarith [hv.1]
  have h4 : 4 + 4 * v ≠ 0 := by linarith [hv.1]
  have h4' : 4 + v * 4 ≠ 0 := by linarith [hv.1]
  have hy := lrBetaRatio_mem_Icc hv
  have hyden : 1 - (v / (2 + v)) ^ 2 ≠ 0 := by
    nlinarith [hy.1, hy.2]
  have hyidentity : 1 - (v / (2 + v)) ^ 2 =
      (4 + 4 * v) / (2 + v) ^ 2 := by
    field_simp [h2]
    ring
  unfold lrLowUDifference lrLowUDifferenceBase lrLowUDifferenceBernstein
    lrLowUDifferenceRow bernsteinBasis lrLowTailH lrFlowM
    lrAtanh5Upper lrAtanh5
  rw [hyidentity]
  norm_num [Nat.choose]
  field_simp [h1, h2, h4, h4', hyden]
  ring

theorem lrLowUDifference_nonneg
    {v z : ℝ} (hv : v ∈ Icc (0 : ℝ) 1)
    (hz : z ∈ Icc (0 : ℝ) 1) :
    0 ≤ lrLowUDifference v z := by
  have hbase : 0 < lrLowUDifferenceBase v := by
    unfold lrLowUDifferenceBase
    have h1 : 0 < 1 + v := by linarith [hv.1]
    have h2 : 0 < 2 + v := by linarith [hv.1]
    exact mul_pos (pow_pos h1 _) (pow_pos h2 _)
  have hbern := lrLowUDifferenceBernstein_nonneg hv hz
  rw [← lrLowUDifference_mul_base_eq_bernstein hv] at hbern
  exact nonneg_of_mul_nonneg_left hbern hbase

end CourtadeKumar
