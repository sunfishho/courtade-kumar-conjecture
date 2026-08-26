import InformationTheory.CourtadeKumar.LRAbelLiftSeries
import InformationTheory.CourtadeKumar.TopB0Series

/-! The analytic `R`-series extension of the LR derivative kernel. -/

open Set

namespace CourtadeKumar

noncomputable def lrWOmega (j : ℕ) (z : ℝ) : ℝ :=
  lrAbelA j * z ^ (2 * j) - lrAbelB j * z ^ (2 * j + 2)

noncomputable def lrWZero (z : ℝ) : ℝ :=
  topPhi z - z ^ 2 / 2

/-- The continuous-at-zero version of `W_R`, defined by the audited power
series.  A later identification theorem relates it to `lrWKernel` for
`0 < R < 1`. -/
noncomputable def lrWExtended (R z : ℝ) : ℝ :=
  lrWZero z + ∑' n : ℕ, lrWOmega (n + 1) z * R ^ (n + 1)

theorem abs_lrWOmega_le_two
    {j : ℕ} (hj : 1 ≤ j) {z : ℝ} (hz : z ∈ Icc (0 : ℝ) 1) :
    |lrWOmega j z| ≤ 2 := by
  have hA := lrAbelA_mem_Icc hj
  have hB := lrAbelB_mem_Icc hj
  have hzEven : z ^ (2 * j) ∈ Icc (0 : ℝ) 1 :=
    ⟨pow_nonneg hz.1 _, pow_le_one₀ hz.1 hz.2⟩
  have hzPlus : z ^ (2 * j + 2) ∈ Icc (0 : ℝ) 1 :=
    ⟨pow_nonneg hz.1 _, pow_le_one₀ hz.1 hz.2⟩
  have hfirst : lrAbelA j * z ^ (2 * j) ∈ Icc (0 : ℝ) 1 := by
    constructor
    · exact mul_nonneg hA.1 hzEven.1
    · nlinarith [mul_le_mul hA.2 hzEven.2 hzEven.1
        (by norm_num : (0 : ℝ) ≤ 1)]
  have hsecond : lrAbelB j * z ^ (2 * j + 2) ∈ Icc (0 : ℝ) 1 := by
    constructor
    · exact mul_nonneg hB.1 hzPlus.1
    · nlinarith [mul_le_mul hB.2 hzPlus.2 hzPlus.1
        (by norm_num : (0 : ℝ) ≤ 1)]
  unfold lrWOmega
  rw [abs_le]
  exact ⟨by linarith [hfirst.1, hsecond.2], by linarith [hfirst.2, hsecond.1]⟩

theorem summable_lrWExtended_tail
    {R z : ℝ} (hR : R ∈ Ico (0 : ℝ) 1) (hz : z ∈ Icc (0 : ℝ) 1) :
    Summable (fun n : ℕ ↦ lrWOmega (n + 1) z * R ^ (n + 1)) := by
  have hgeom : Summable (fun n : ℕ ↦ 2 * R * R ^ n) :=
    (summable_geometric_of_lt_one hR.1 hR.2).mul_left (2 * R)
  apply Summable.of_norm_bounded hgeom
  intro n
  have hpow : 0 ≤ R ^ (n + 1) := pow_nonneg hR.1 _
  calc
    ‖lrWOmega (n + 1) z * R ^ (n + 1)‖ =
        |lrWOmega (n + 1) z| * R ^ (n + 1) := by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hpow]
    _ ≤ 2 * R ^ (n + 1) :=
      mul_le_mul_of_nonneg_right (abs_lrWOmega_le_two (by omega) hz) hpow
    _ = 2 * R * R ^ n := by rw [pow_succ']; ring

lemma lrWExtended_zero (z : ℝ) :
    lrWExtended 0 z = lrWZero z := by
  simp [lrWExtended]

lemma lrWKernel_eq_Psi
    {R z : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1) (hz : 0 < z) :
    lrWKernel R z = topPhi z - topPhi (Real.sqrt (R * z ^ 2)) -
      (1 - R) * z ^ 2 * topPsiDeriv (R * z ^ 2) := by
  have hsqrtR : 0 < Real.sqrt R := Real.sqrt_pos.2 hR.1
  have hsqrtQ : Real.sqrt (R * z ^ 2) = Real.sqrt R * z := by
    rw [Real.sqrt_mul hR.1.le, Real.sqrt_sq_eq_abs, abs_of_pos hz]
  have hPsi : z ^ 2 * topPsiDeriv (R * z ^ 2) =
      z / (2 * Real.sqrt R) * Real.artanh (Real.sqrt R * z) := by
    unfold topPsiDeriv
    rw [hsqrtQ]
    field_simp [hsqrtR.ne', hz.ne']
  unfold lrWKernel
  rw [hsqrtQ]
  rw [show (1 - R) * z ^ 2 * topPsiDeriv (R * z ^ 2) =
    (1 - R) * (z ^ 2 * topPsiDeriv (R * z ^ 2)) by ring, hPsi]
  ring

/-- The three elementary series whose coefficient difference is
`ω_j(z) R^j`. -/
theorem lrWOmega_hasSum
    {R z : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1) (hz : z ∈ Ioc (0 : ℝ) 1) :
    HasSum (fun n : ℕ ↦ lrWOmega (n + 1) z * R ^ (n + 1))
      (-(topPhi (Real.sqrt (R * z ^ 2))) -
        (1 - R) * z ^ 2 * topPsiDeriv (R * z ^ 2) + z ^ 2 / 2) := by
  let Q : ℝ := R * z ^ 2
  have hQ : Q ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · dsimp [Q]
      exact mul_pos hR.1 (sq_pos_of_pos hz.1)
    · dsimp [Q]
      have hzsq : z ^ 2 ≤ 1 := pow_le_one₀ hz.1.le hz.2
      exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hzsq hR.1.le)
        (by simpa using hR.2)
  let psiTerm : ℕ → ℝ := fun n ↦ Q ^ n / (2 * (2 * n + 1))
  let phiTerm : ℕ → ℝ := fun n ↦
    Q ^ (n + 1) / (2 * (n + 1) * (2 * (n + 1) - 1))
  have hPsi : HasSum psiTerm (topPsiDeriv Q) := by
    simpa [psiTerm] using topPsiDeriv_hasSum hQ
  have hPhi : HasSum phiTerm (topPhi (Real.sqrt Q)) := by
    simpa [phiTerm] using topPhi_sqrt_hasSum hQ
  have hFirst : HasSum (fun n : ℕ ↦ R * z ^ 2 * psiTerm n)
      (R * z ^ 2 * topPsiDeriv Q) := hPsi.mul_left (R * z ^ 2)
  have hPsiTail : HasSum (fun n : ℕ ↦ psiTerm (n + 1))
      (topPsiDeriv Q - 1 / 2) := by
    have h := (hasSum_nat_add_iff' 1).2 hPsi
    simpa [psiTerm] using h
  have hThird : HasSum (fun n : ℕ ↦ z ^ 2 * psiTerm (n + 1))
      (z ^ 2 * (topPsiDeriv Q - 1 / 2)) := hPsiTail.mul_left (z ^ 2)
  have hCombined := hFirst.sub hPhi |>.sub hThird
  convert hCombined using 1
  · funext n
    dsimp [lrWOmega, lrAbelA, lrAbelB, psiTerm, phiTerm, Q]
    have hn : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
    have hodd : 0 < 2 * ((n + 1 : ℕ) : ℝ) - 1 := by
      have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      push_cast
      nlinarith
    have hplus : 0 < 2 * ((n + 1 : ℕ) : ℝ) + 1 := by positivity
    norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    rw [show (R * z ^ 2) ^ n = R ^ n * z ^ (2 * n) by
      rw [mul_pow, pow_mul],
      show (R * z ^ 2) ^ (n + 1) = R ^ (n + 1) * z ^ (2 * (n + 1)) by
        rw [mul_pow, pow_mul]]
    rw [show R ^ (n + 1) = R * R ^ n by rw [pow_succ']]
    rw [show z ^ (2 * (n + 1)) = z ^ (2 * n) * z ^ 2 by
      rw [show 2 * (n + 1) = 2 * n + 2 by omega, pow_add],
      show z ^ (2 * (n + 1) + 2) = z ^ (2 * n) * z ^ 4 by
        rw [show 2 * (n + 1) + 2 = 2 * n + 4 by omega, pow_add]]
    have hbase : 1 + (n : ℝ) * 2 ≠ 0 := by positivity
    ring_nf
    field_simp [hbase]
    ring
  · dsimp [Q]
    ring

/-- On the regular physical domain, the analytic series extension is exactly
the derivative kernel originally used in the flow. -/
theorem lrWExtended_eq_lrWKernel
    {R z : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1) (hz : z ∈ Ioc (0 : ℝ) 1) :
    lrWExtended R z = lrWKernel R z := by
  have hseries := lrWOmega_hasSum hR hz
  have hkernel := lrWKernel_eq_Psi hR hz.1
  unfold lrWExtended lrWZero
  rw [hseries.tsum_eq, hkernel]
  ring

end CourtadeKumar
