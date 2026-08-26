import InformationTheory.CourtadeKumar.LRScalarComparison

/-! Exact power-series assembly for the audited scalar `K` comparison. -/

open Set

namespace CourtadeKumar

noncomputable def lrBKernelCoeff (R : ℝ) (n : ℕ) : ℝ :=
  R ^ n / 2 * ((1 + R) / (2 * (n : ℝ) + 1) + (1 - R))

noncomputable def lrBLFullCoeff (R : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0 else R ^ n / (2 * (n : ℝ))

noncomputable def lrBCorrectionCoeff (R : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0
  else if n = 1 then R / 2
  else -(1 - R) * R ^ (n - 1) / 2

lemma lrBScalarCoeff_eq_components
    {R : ℝ} (hR : R ≠ 0) (n : ℕ) :
    lrBScalarCoeff R n =
      lrBGamma R * lrBKernelCoeff R n - lrBLFullCoeff R n +
        lrBCorrectionCoeff R n - (if n = 0 then Real.log 2 else 0) := by
  rcases n with _ | n
  · simp [lrBKernelCoeff, lrBLFullCoeff, lrBCorrectionCoeff]
    ring
  rcases n with _ | n
  · simp [lrBKernelCoeff, lrBLFullCoeff, lrBCorrectionCoeff]
    ring
  · rw [lrBScalarCoeff_of_two_le (by omega)]
    simp [lrBKernelCoeff, lrBLFullCoeff, lrBCorrectionCoeff]
    rw [pow_succ R (n + 1)]
    field_simp [hR]
    ring

theorem lrBKernelCoeff_hasSum
    {R y : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1)
    (hy : y ∈ Ioo (0 : ℝ) 1) :
    HasSum (fun n : ℕ ↦ lrBKernelCoeff R n * (y ^ 2) ^ n)
      (lrBKernelK R y) := by
  let Q : ℝ := R * y ^ 2
  have hQ : Q ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · dsimp [Q]
      exact mul_pos hR.1 (sq_pos_of_pos hy.1)
    · dsimp [Q]
      have hySq : y ^ 2 < 1 := by nlinarith [hy.1, hy.2]
      nlinarith [mul_lt_mul_of_pos_left hySq hR.1,
        mul_lt_mul_of_pos_right hR.2 (sq_pos_of_pos hy.1)]
  have hPsi := (topPsiDeriv_hasSum hQ).mul_left (1 + R)
  have hGeom := (hasSum_geometric_of_lt_one hQ.1.le hQ.2).mul_left ((1 - R) / 2)
  have hCombined := hPsi.add hGeom
  convert hCombined using 1
  · funext n
    unfold lrBKernelCoeff
    dsimp [Q]
    rw [mul_pow]
    have hodd : 2 * (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp [hodd]
  · have hsqrtQ : Real.sqrt Q = Real.sqrt R * y := by
      dsimp [Q]
      rw [Real.sqrt_mul hR.1.le, Real.sqrt_sq_eq_abs, abs_of_pos hy.1]
    have hsqrtR := lrB_sqrt_mem_Ioo hR
    have hPsiEq : topPsiDeriv Q =
        Real.artanh (Real.sqrt R * y) / (2 * Real.sqrt R * y) := by
      unfold topPsiDeriv
      rw [hsqrtQ]
      ring
    rw [hPsiEq]
    unfold lrBKernelK
    dsimp [Q]
    field_simp [hsqrtR.1.ne', hy.1.ne', (show 1 - R * y ^ 2 ≠ 0 by
      nlinarith [hQ.2])]

theorem lrBLFullCoeff_hasSum
    {R y : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1)
    (hy : y ∈ Ioo (0 : ℝ) 1) :
    HasSum (fun n : ℕ ↦ lrBLFullCoeff R n * (y ^ 2) ^ n)
      (lrL (Real.sqrt R * y)) := by
  have hsqrtR := lrB_sqrt_mem_Ioo hR
  have hz : Real.sqrt R * y ∈ Ioo (-1 : ℝ) 1 := by
    constructor
    · nlinarith [mul_pos hsqrtR.1 hy.1]
    · nlinarith [mul_lt_mul_of_pos_right hsqrtR.2 hy.1,
        mul_lt_mul_of_pos_left hy.2 hsqrtR.1]
  have hL := lrL_hasSum hz
  rw [← hasSum_nat_add_iff' 1]
  convert hL using 1
  · funext n
    simp [lrBLFullCoeff]
    rw [mul_pow, show Real.sqrt R ^ (2 * (n + 1)) = R ^ (n + 1) by
      rw [pow_mul, Real.sq_sqrt hR.1.le], pow_mul]
    ring
  · simp [lrBLFullCoeff]

theorem lrBCorrectionCoeff_hasSum
    {R X : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1)
    (hX : X ∈ Ioo (0 : ℝ) 1) :
    HasSum (fun n : ℕ ↦ lrBCorrectionCoeff R n * X ^ n)
      (R * X * (1 - X) / (2 * (1 - R * X))) := by
  let Q : ℝ := R * X
  have hQ : Q ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · dsimp [Q]
      exact mul_pos hR.1 hX.1
    · dsimp [Q]
      nlinarith [mul_lt_mul_of_pos_right hR.2 hX.1,
        mul_lt_mul_of_pos_left hX.2 hR.1]
  have hGeom := hasSum_geometric_of_lt_one hQ.1.le hQ.2
  let a : ℕ → ℝ := fun n ↦ R ^ (n + 1) * X ^ (n + 1) / 2
  let b : ℕ → ℝ := fun n ↦ R ^ (n + 1) * X ^ (n + 2) / 2
  have ha : HasSum a (R * X / (2 * (1 - Q))) := by
    convert hGeom.mul_left (R * X / 2) using 1
    · funext n
      dsimp [a, Q]
      rw [mul_pow, pow_succ R n, pow_succ X n]
      ring
    · field_simp [show 1 - Q ≠ 0 by linarith [hQ.2]]
  have hb : HasSum b (R * X ^ 2 / (2 * (1 - Q))) := by
    convert hGeom.mul_left (R * X ^ 2 / 2) using 1
    · funext n
      dsimp [b, Q]
      rw [mul_pow, pow_succ R n,
        show X ^ (n + 2) = X ^ n * X ^ 2 by rw [show n + 2 = n + 2 by rfl, pow_add]]
      ring
    · field_simp [show 1 - Q ≠ 0 by linarith [hQ.2]]
  let A : ℕ → ℝ := fun n ↦ if n = 0 then 0 else R ^ n * X ^ n / 2
  let B : ℕ → ℝ := fun n ↦ if n < 2 then 0 else R ^ (n - 1) * X ^ n / 2
  have hA : HasSum A (R * X / (2 * (1 - Q))) := by
    rw [← hasSum_nat_add_iff' 1]
    simpa [A, a] using ha
  have hB : HasSum B (R * X ^ 2 / (2 * (1 - Q))) := by
    rw [← hasSum_nat_add_iff' 2]
    convert hb using 1
    simp [B, Finset.sum_range_succ]
  have hDiff := hA.sub hB
  convert hDiff using 1
  · funext n
    rcases n with _ | n
    · simp [A, B, lrBCorrectionCoeff]
    rcases n with _ | n
    · simp [A, B, lrBCorrectionCoeff]
      ring
    · simp [A, B, lrBCorrectionCoeff, (show ¬ n + 2 < 2 by omega)]
      rw [pow_succ R (n + 1)]
      ring
  · dsimp [Q]
    field_simp [show 1 - R * X ≠ 0 by linarith [hQ.2]]

theorem lrBScalarCoeff_hasSum
    {R y : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1)
    (hy : y ∈ Ioo (0 : ℝ) 1) :
    HasSum (fun n : ℕ ↦ lrBScalarCoeff R n * (y ^ 2) ^ n)
      (lrBScalarReserve R y) := by
  have hK := (lrBKernelCoeff_hasSum hR hy).mul_left (lrBGamma R)
  have hL := lrBLFullCoeff_hasSum hR hy
  have hX : y ^ 2 ∈ Ioo (0 : ℝ) 1 :=
    ⟨sq_pos_of_pos hy.1, by nlinarith [hy.1, hy.2]⟩
  have hC := lrBCorrectionCoeff_hasSum hR hX
  have hLog : HasSum (fun n : ℕ ↦
      (if n = 0 then Real.log 2 else 0) * (y ^ 2) ^ n) (Real.log 2) := by
    convert hasSum_ite_eq (0 : ℕ) (Real.log 2) using 1
    funext n
    split_ifs with hn
    · subst n
      simp
    · simp
  have h := (hK.sub hL).add hC |>.sub hLog
  convert h using 1
  · funext n
    rw [lrBScalarCoeff_eq_components hR.1.ne' n]
    ring

end CourtadeKumar
