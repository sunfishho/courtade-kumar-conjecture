import InformationTheory.CourtadeKumar.TopCertificateExpanded

/-! The exact polynomial numerator in the full-cap TOP certificate. -/

open Set
open scoped BigOperators

namespace CourtadeKumar

def topCertR (c z : ℝ) : ℝ := 1 - c ^ 2 + c ^ 2 * z

def topCertD (c : ℝ) : ℝ := (1 + c) * (2 - c) ^ 2

def topCertB (c z : ℝ) : ℝ := z * c ^ 2 * (3 - c)

def topCertH (c z : ℝ) : ℝ := 2 * topCertD c + topCertB c z

def topCertZDen (c z : ℝ) : ℝ :=
  12 * topCertD c * topCertH c z * (topCertD c + topCertB c z)

def topCertZNum (c z : ℝ) : ℝ :=
  -topCertR c z * (3 - c) *
    (3 * topCertH c z ^ 2 - 2 * topCertB c z ^ 2)

noncomputable def topCertW8 (c z : ℝ) : ℝ :=
  1931 / 10000 * topCertR c z +
  3293 / 30000 * topCertR c z ^ 2 +
  2293 / 30000 * topCertR c z ^ 3 +
  12301 / 210000 * topCertR c z ^ 4 +
  29903 / 630000 * topCertR c z ^ 5 +
  276433 / 6930000 * topCertR c z ^ 6 +
  3098629 / 90090000 * topCertR c z ^ 7 +
  1361627 / 45045000 * topCertR c z ^ 8

/-- The polynomial quotient `D_n(R) / c²`, written without division using
`1 - R = c²(1-z)`. -/
def topCertDnOverC2 (c z : ℝ) (n : ℕ) : ℝ :=
  c ^ 2 * (1 - z) ^ 2 *
    ∑ j ∈ Finset.range n, (j + 1 : ℝ) * topCertR c z ^ j

def topCertGeometric (c z : ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, z ^ k * topCertR c z ^ (9 - k)

noncomputable def topCertEnum (c z : ℝ) : ℝ :=
  ∑ n ∈ Finset.range 10,
    let m := n + 1
    (1 : ℝ) / (2 * m * (m + 1) * (2 * m + 1)) *
      topCertDnOverC2 c z m * topCertGeometric c z m

/-- The exact common-denominator numerator `𝓟(c,z)` from the audited
full-cap Bernstein certificate. -/
noncomputable def topCertificatePolynomial (c z : ℝ) : ℝ :=
  topCertR c z ^ 9 * topCertZDen c z * (topCertW8 c z - 1 / 100) +
    topCertR c z ^ 9 * topCertZNum c z +
    topCertZDen c z * topCertEnum c z

def topCertificateBernsteinEval (c z : ℝ) : ℝ :=
  tensorBernsteinEval 47 60
    (fun i j ↦ (topElevatedBernsteinCoeff i j : ℝ)) c z

lemma topElevatedBernsteinCoeff_cast_nonneg (i : Fin 48) (j : Fin 61) :
    0 ≤ (topElevatedBernsteinCoeff i j : ℝ) := by
  exact_mod_cast topElevatedBernsteinCoeff_nonneg i j

theorem topCertificateBernsteinEval_nonneg {c z : ℝ}
    (hc : c ∈ Icc (0 : ℝ) 1) (hz : z ∈ Icc (0 : ℝ) 1) :
    0 ≤ topCertificateBernsteinEval c z := by
  exact tensorBernsteinEval_nonneg topElevatedBernsteinCoeff_cast_nonneg hc hz

lemma topBernsteinPowerCoeff_cast (a b : ℕ) :
    ((tensorBernsteinPowerCoeff
        (p := fun i j ↦ topElevatedBernsteinCoeff i j) a b : ℚ) : ℝ) =
      tensorBernsteinPowerCoeff
        (p := fun i j ↦ (topElevatedBernsteinCoeff i j : ℝ)) a b := by
  classical
  unfold tensorBernsteinPowerCoeff tensorBernsteinPowerSummand finTableGet
  push_cast
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  by_cases him : i < 48 <;> by_cases hjn : j < 61 <;>
    simp [him, hjn]

def topCertificatePowerDataEval (c z : ℝ) : ℝ :=
  ∑ i ∈ Finset.range 48, ∑ j ∈ Finset.range 61,
    (topCertificatePowerCoeffRatNat i j : ℝ) * c ^ i * z ^ j

theorem topCertificateBernsteinEval_eq_powerDataEval (c z : ℝ) :
    topCertificateBernsteinEval c z = topCertificatePowerDataEval c z := by
  rw [topCertificateBernsteinEval, tensorBernsteinEval_eq_powerEval]
  unfold tensorBernsteinPowerEval topCertificatePowerDataEval
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  have hi' : i < 48 := Finset.mem_range.mp hi
  have hj' : j < 61 := Finset.mem_range.mp hj
  rw [← topBernsteinPowerCoeff_cast,
    topBernsteinPowerCoeff_eq_certificate ⟨i, hi'⟩ ⟨j, hj'⟩]
  simp [topCertificatePowerCoeffRatNat, hi', hj']

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 100000 in
theorem topCertificatePolynomial_eq_powerExpanded (c z : ℝ) :
    topCertificatePolynomial c z = topCertificatePowerExpanded c z := by
  classical
  simp only [topCertificatePolynomial, topCertEnum, topCertGeometric,
    topCertDnOverC2, topCertW8, topCertZNum, topCertZDen, topCertH,
    topCertB, topCertD, topCertR, Finset.sum_range_succ,
    Finset.sum_range_zero]
  unfold topCertificatePowerExpanded
    topCertificatePowerRowExpanded0 topCertificatePowerRowExpanded1
    topCertificatePowerRowExpanded2 topCertificatePowerRowExpanded3
    topCertificatePowerRowExpanded4 topCertificatePowerRowExpanded5
    topCertificatePowerRowExpanded6 topCertificatePowerRowExpanded7
    topCertificatePowerRowExpanded8 topCertificatePowerRowExpanded9
    topCertificatePowerRowExpanded10 topCertificatePowerRowExpanded11
    topCertificatePowerRowExpanded12 topCertificatePowerRowExpanded13
    topCertificatePowerRowExpanded14 topCertificatePowerRowExpanded15
    topCertificatePowerRowExpanded16 topCertificatePowerRowExpanded17
    topCertificatePowerRowExpanded18 topCertificatePowerRowExpanded19
    topCertificatePowerRowExpanded20 topCertificatePowerRowExpanded21
    topCertificatePowerRowExpanded22 topCertificatePowerRowExpanded23
    topCertificatePowerRowExpanded24 topCertificatePowerRowExpanded25
    topCertificatePowerRowExpanded26 topCertificatePowerRowExpanded27
    topCertificatePowerRowExpanded28 topCertificatePowerRowExpanded29
    topCertificatePowerRowExpanded30 topCertificatePowerRowExpanded31
    topCertificatePowerRowExpanded32 topCertificatePowerRowExpanded33
    topCertificatePowerRowExpanded34 topCertificatePowerRowExpanded35
    topCertificatePowerRowExpanded36 topCertificatePowerRowExpanded37
    topCertificatePowerRowExpanded38 topCertificatePowerRowExpanded39
    topCertificatePowerRowExpanded40 topCertificatePowerRowExpanded41
    topCertificatePowerRowExpanded42 topCertificatePowerRowExpanded43
    topCertificatePowerRowExpanded44 topCertificatePowerRowExpanded45
    topCertificatePowerRowExpanded46 topCertificatePowerRowExpanded47
  ring

theorem topCertificatePowerDataEval_eq_powerExpanded (c z : ℝ) :
    topCertificatePowerDataEval c z = topCertificatePowerExpanded c z := by
  unfold topCertificatePowerDataEval
  calc
    _ = ∑ i ∈ Finset.range 48,
          topCertificatePowerRowExpanded i z * c ^ i := by
        apply Finset.sum_congr rfl
        intro i hi
        exact topCertificatePowerRowEval i (Finset.mem_range.mp hi) c z
    _ = _ := (topCertificatePowerExpanded_eq_sum c z).symm

theorem topCertificatePolynomial_eq_powerDataEval (c z : ℝ) :
    topCertificatePolynomial c z = topCertificatePowerDataEval c z :=
  (topCertificatePolynomial_eq_powerExpanded c z).trans
    (topCertificatePowerDataEval_eq_powerExpanded c z).symm

/-- The exact certificate identity, checked through the intermediate
power-basis table rather than one monolithic symbolic expansion. -/
theorem topCertificatePolynomial_eq_bernstein (c z : ℝ) :
    topCertificatePolynomial c z = topCertificateBernsteinEval c z :=
  (topCertificatePolynomial_eq_powerDataEval c z).trans
    (topCertificateBernsteinEval_eq_powerDataEval c z).symm

/-- The audited common-denominator numerator is nonnegative throughout the
closed unit square. -/
theorem topCertificatePolynomial_nonneg {c z : ℝ}
    (hc : c ∈ Icc (0 : ℝ) 1) (hz : z ∈ Icc (0 : ℝ) 1) :
    0 ≤ topCertificatePolynomial c z := by
  rw [topCertificatePolynomial_eq_bernstein]
  exact topCertificateBernsteinEval_nonneg hc hz

end CourtadeKumar
