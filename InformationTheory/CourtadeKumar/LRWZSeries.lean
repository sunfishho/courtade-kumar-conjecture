import InformationTheory.CourtadeKumar.LRWSeries

/-! The nonnegative `z`-power series for the LR derivative kernel. -/

open Set
open scoped BigOperators

namespace CourtadeKumar

/-- The coefficient `w_m` in the audited expansion of `W_R(z)`, indexed
from `m = 1`.  Its first value is zero, so the effective series starts at
`m = 2`. -/
noncomputable def lrWZCoeff (R : ℝ) (m : ℕ) : ℝ :=
  (1 - (m : ℝ) * R ^ (m - 1) + ((m : ℝ) - 1) * R ^ m) /
    (2 * (m : ℝ) * (2 * (m : ℝ) - 1))

/-- Exact finite-sum factorization of the numerator of `w_(n+2)`. -/
lemma lrWZCoeff_numerator_eq (R : ℝ) (n : ℕ) :
    1 - ((n + 2 : ℕ) : ℝ) * R ^ (n + 1) +
        (((n + 2 : ℕ) : ℝ) - 1) * R ^ (n + 2) =
      (1 - R) ^ 2 *
        ∑ k ∈ Finset.range (n + 1), ((k + 1 : ℕ) : ℝ) * R ^ k := by
  induction n with
  | zero => norm_num; ring
  | succ n ih =>
      calc
        1 - (((n + 1) + 2 : ℕ) : ℝ) * R ^ ((n + 1) + 1) +
            ((((n + 1) + 2 : ℕ) : ℝ) - 1) * R ^ ((n + 1) + 2) =
          (1 - ((n + 2 : ℕ) : ℝ) * R ^ (n + 1) +
              (((n + 2 : ℕ) : ℝ) - 1) * R ^ (n + 2)) +
            (1 - R) ^ 2 * (((n + 2 : ℕ) : ℝ) * R ^ (n + 1)) := by
              push_cast
              rw [pow_succ R (n + 1), pow_succ R (n + 2)]
              ring
        _ = (1 - R) ^ 2 *
            (∑ k ∈ Finset.range (n + 1),
                ((k + 1 : ℕ) : ℝ) * R ^ k) +
              (1 - R) ^ 2 * (((n + 2 : ℕ) : ℝ) * R ^ (n + 1)) := by
                rw [ih]
        _ = (1 - R) ^ 2 *
            ∑ k ∈ Finset.range ((n + 1) + 1),
              ((k + 1 : ℕ) : ℝ) * R ^ k := by
                conv_rhs => rw [Finset.sum_range_succ]
                ring

theorem lrWZCoeff_nonneg
    {R : ℝ} (hR : 0 ≤ R) (n : ℕ) :
    0 ≤ lrWZCoeff R (n + 2) := by
  have hsum : 0 ≤
      ∑ k ∈ Finset.range (n + 1), ((k + 1 : ℕ) : ℝ) * R ^ k := by
    positivity
  have hnum : 0 ≤
      1 - ((n + 2 : ℕ) : ℝ) * R ^ (n + 1) +
        (((n + 2 : ℕ) : ℝ) - 1) * R ^ (n + 2) := by
    rw [lrWZCoeff_numerator_eq]
    positivity
  have hden : 0 <
      2 * (((n + 2 : ℕ) : ℝ)) *
        (2 * (((n + 2 : ℕ) : ℝ)) - 1) := by
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    push_cast
    have hn2 : 0 < (n : ℝ) + 2 := by linarith
    have hodd : 0 < 2 * ((n : ℝ) + 2) - 1 := by linarith
    exact mul_pos (mul_pos (by norm_num) hn2) hodd
  unfold lrWZCoeff
  rw [show n + 2 - 1 = n + 1 by omega]
  exact div_nonneg hnum hden.le

@[simp] lemma lrWZCoeff_one (R : ℝ) : lrWZCoeff R 1 = 0 := by
  simp [lrWZCoeff]

lemma lrWZCoeff_eq_seriesTerm (R : ℝ) (n : ℕ) :
    lrWZCoeff R (n + 1) =
      1 / (2 * ((n : ℝ) + 1) * (2 * ((n : ℝ) + 1) - 1)) -
        R ^ (n + 1) /
          (2 * ((n : ℝ) + 1) * (2 * ((n : ℝ) + 1) - 1)) -
        (1 - R) * (R ^ n / (2 * (2 * (n : ℝ) + 1))) := by
  unfold lrWZCoeff
  rw [show n + 1 - 1 = n by omega]
  norm_num only [Nat.cast_add, Nat.cast_one]
  rw [pow_succ R n]
  have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
  have hodd : 2 * ((n : ℝ) + 1) - 1 ≠ 0 := by
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    nlinarith
  have hpsi : 2 * (n : ℝ) + 1 ≠ 0 := by positivity
  have hpsi' : 1 + (n : ℝ) * 2 ≠ 0 := by positivity
  have hoddEq : 2 * ((n : ℝ) + 1) - 1 = 2 * (n : ℝ) + 1 := by ring
  rw [hoddEq]
  field_simp [hn1, hodd, hpsi, hpsi']
  ring

/-- Equation `(lr-W-series)`: the exact `z`-series for the analytic LR
kernel on the regular physical interior. -/
theorem lrWZCoeff_hasSum
    {R z : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1) (hz : z ∈ Ioo (0 : ℝ) 1) :
    HasSum (fun n : ℕ ↦ lrWZCoeff R (n + 2) * z ^ (2 * (n + 2)))
      (lrWKernel R z) := by
  let Q : ℝ := R * z ^ 2
  have hQ : Q ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · dsimp [Q]
      exact mul_pos hR.1 (sq_pos_of_pos hz.1)
    · dsimp [Q]
      have hzsq : z ^ 2 ≤ 1 := pow_le_one₀ hz.1.le hz.2.le
      exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hzsq hR.1.le)
        (by simpa using hR.2)
  have hsqrtQ : Real.sqrt Q ∈ Ioo (-1 : ℝ) 1 := by
    constructor
    · nlinarith [Real.sqrt_pos.2 hQ.1]
    · simpa using (Real.sqrt_lt_sqrt_iff hQ.1.le).2 hQ.2
  have hzOpen : z ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hz.1], hz.2⟩
  have hPhiZ := topPhi_hasSum hzOpen
  have hPhiQ := topPhi_hasSum hsqrtQ
  have hPsi := topPsiDeriv_hasSum hQ
  have hCombined := (hPhiZ.sub hPhiQ).sub
    (hPsi.mul_left ((1 - R) * z ^ 2))
  have hKernel :
      topPhi z - topPhi (Real.sqrt Q) -
          (1 - R) * z ^ 2 * topPsiDeriv Q = lrWKernel R z := by
    rw [← lrWKernel_eq_Psi hR hz.1]
  rw [hKernel] at hCombined
  have hAll : HasSum
      (fun n : ℕ ↦ lrWZCoeff R (n + 1) * z ^ (2 * (n + 1)))
      (lrWKernel R z) := by
    convert hCombined using 1
    funext n
    rw [show Real.sqrt Q ^ (2 * (n + 1)) = Q ^ (n + 1) by
      rw [pow_mul, Real.sq_sqrt hQ.1.le]]
    dsimp [Q]
    rw [show (R * z ^ 2) ^ (n + 1) =
        R ^ (n + 1) * z ^ (2 * (n + 1)) by rw [mul_pow, pow_mul],
      show (R * z ^ 2) ^ n = R ^ n * z ^ (2 * n) by rw [mul_pow, pow_mul]]
    rw [show z ^ (2 * (n + 1)) = z ^ 2 * z ^ (2 * n) by
      rw [← pow_add]
      congr 1
      omega]
    unfold lrWZCoeff
    rw [show n + 1 - 1 = n by omega]
    norm_num only [Nat.cast_add, Nat.cast_one]
    rw [pow_succ R n]
    have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
    have hodd : 2 * ((n : ℝ) + 1) - 1 ≠ 0 := by
      have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      nlinarith
    have hpsi : 2 * (n : ℝ) + 1 ≠ 0 := by positivity
    have hpsi' : 1 + (n : ℝ) * 2 ≠ 0 := by positivity
    have hoddEq : 2 * ((n : ℝ) + 1) - 1 = 2 * (n : ℝ) + 1 := by ring
    rw [hoddEq]
    field_simp [hn1, hodd, hpsi, hpsi']
    ring
  have hTail := (hasSum_nat_add_iff' 1).2 hAll
  simpa using hTail

/-- The endpoint `z = 1` of the same series, needed for the scalar
normalization in the `B` comparison. -/
theorem lrWZCoeff_one_hasSum
    {R : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1) :
    HasSum (fun n : ℕ ↦ lrWZCoeff R (n + 2)) (lrWKernel R 1) := by
  have hPhiOne := top_hasSum_phiCoefficients
  have hPhiR := topPhi_sqrt_hasSum hR
  have hPsi := topPsiDeriv_hasSum hR
  have hCombined := (hPhiOne.sub hPhiR).sub
    (hPsi.mul_left (1 - R))
  have hKernel :
      Real.log 2 - topPhi (Real.sqrt R) -
          (1 - R) * topPsiDeriv R = lrWKernel R 1 := by
    have h := lrWKernel_eq_Psi hR (by norm_num : (0 : ℝ) < 1)
    simpa using h.symm
  rw [hKernel] at hCombined
  have hAll : HasSum (fun n : ℕ ↦ lrWZCoeff R (n + 1))
      (lrWKernel R 1) := by
    convert hCombined using 1
    funext n
    rw [lrWZCoeff_eq_seriesTerm]
  have hTail := (hasSum_nat_add_iff' 1).2 hAll
  simpa using hTail

theorem lrWKernel_nonneg
    {R z : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1) (hz : z ∈ Ioo (0 : ℝ) 1) :
    0 ≤ lrWKernel R z := by
  exact (lrWZCoeff_hasSum hR hz).nonneg
    (fun n ↦ mul_nonneg (lrWZCoeff_nonneg hR.1.le n)
      (pow_nonneg hz.1.le _))

theorem lrWKernel_one_nonneg
    {R : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1) :
    0 ≤ lrWKernel R 1 := by
  exact (lrWZCoeff_one_hasSum hR).nonneg
    (fun n ↦ lrWZCoeff_nonneg hR.1.le n)

end CourtadeKumar
