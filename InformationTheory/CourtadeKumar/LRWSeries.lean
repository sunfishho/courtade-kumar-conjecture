import InformationTheory.CourtadeKumar.LRAbelLiftSeries

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

end CourtadeKumar
