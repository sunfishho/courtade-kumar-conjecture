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
    (hy : y ∈ Ioc (0 : ℝ) 1) :
    HasSum (fun n : ℕ ↦ lrBKernelCoeff R n * (y ^ 2) ^ n)
      (lrBKernelK R y) := by
  let Q : ℝ := R * y ^ 2
  have hQ : Q ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · dsimp [Q]
      exact mul_pos hR.1 (sq_pos_of_pos hy.1)
    · dsimp [Q]
      have hySq : y ^ 2 ≤ 1 := pow_le_one₀ hy.1.le hy.2
      exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hySq hR.1.le)
        (by simpa using hR.2)
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
    (hy : y ∈ Ioc (0 : ℝ) 1) :
    HasSum (fun n : ℕ ↦ lrBLFullCoeff R n * (y ^ 2) ^ n)
      (lrL (Real.sqrt R * y)) := by
  have hsqrtR := lrB_sqrt_mem_Ioo hR
  have hz : Real.sqrt R * y ∈ Ioo (-1 : ℝ) 1 := by
    constructor
    · nlinarith [mul_pos hsqrtR.1 hy.1]
    · calc
        Real.sqrt R * y ≤ Real.sqrt R * 1 :=
          mul_le_mul_of_nonneg_left hy.2 hsqrtR.1.le
        _ < 1 := by simpa using hsqrtR.2
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
    (hX : X ∈ Ioc (0 : ℝ) 1) :
    HasSum (fun n : ℕ ↦ lrBCorrectionCoeff R n * X ^ n)
      (R * X * (1 - X) / (2 * (1 - R * X))) := by
  let Q : ℝ := R * X
  have hQ : Q ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · dsimp [Q]
      exact mul_pos hR.1 hX.1
    · dsimp [Q]
      exact lt_of_le_of_lt
        (mul_le_mul_of_nonneg_left hX.2 hR.1.le) (by simpa using hR.2)
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
    (hy : y ∈ Ioc (0 : ℝ) 1) :
    HasSum (fun n : ℕ ↦ lrBScalarCoeff R n * (y ^ 2) ^ n)
      (lrBScalarReserve R y) := by
  have hK := (lrBKernelCoeff_hasSum hR hy).mul_left (lrBGamma R)
  have hL := lrBLFullCoeff_hasSum hR hy
  have hX : y ^ 2 ∈ Ioc (0 : ℝ) 1 :=
    ⟨sq_pos_of_pos hy.1, pow_le_one₀ hy.1.le hy.2⟩
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

/-- The scalar reserve is nonnegative throughout the closed comparison interval.

The coefficient signs say that the constant and linear coefficients are
nonnegative while every coefficient of degree at least two is nonpositive.
Consequently the series lies above the chord joining its values at `X = 0`
and `X = 1`, where `X = y²`. -/
theorem lrBScalarReserve_nonneg
    {R y : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1)
    (hy : y ∈ Ioc (0 : ℝ) 1) :
    0 ≤ lrBScalarReserve R y := by
  let X : ℝ := y ^ 2
  have hX : X ∈ Ioc (0 : ℝ) 1 := by
    exact ⟨sq_pos_of_pos hy.1, pow_le_one₀ hy.1.le hy.2⟩
  have hY : HasSum (fun n : ℕ ↦ lrBScalarCoeff R n * X ^ n)
      (lrBScalarReserve R y) := by
    simpa [X] using lrBScalarCoeff_hasSum hR hy
  have hOne : HasSum (fun n : ℕ ↦ lrBScalarCoeff R n)
      (lrBScalarReserve R 1) := by
    simpa using lrBScalarCoeff_hasSum hR
      (show (1 : ℝ) ∈ Ioc (0 : ℝ) 1 by norm_num)
  have hDiff := hY.sub (hOne.mul_left X)
  have hTail : HasSum
      (fun n : ℕ ↦
        (lrBScalarCoeff R (n + 1) * X ^ (n + 1) -
          X * lrBScalarCoeff R (n + 1)))
      ((lrBScalarReserve R y - X * lrBScalarReserve R 1) -
        (lrBScalarCoeff R 0 - X * lrBScalarCoeff R 0)) := by
    simpa using (hasSum_nat_add_iff' 1).2 hDiff
  have hTailNonneg :
      0 ≤ (lrBScalarReserve R y - X * lrBScalarReserve R 1) -
        (lrBScalarCoeff R 0 - X * lrBScalarCoeff R 0) := by
    apply hTail.nonneg
    intro n
    rcases n with _ | n
    · simp [mul_assoc, mul_comm]
    · have hcoeff : lrBScalarCoeff R (n + 2) ≤ 0 :=
        lrBScalarCoeff_nonpos_of_two_le hR (by omega)
      have hpow : X ^ (n + 2) ≤ X := by
        simpa using
          (pow_le_pow_of_le_one hX.1.le hX.2 (show 1 ≤ n + 2 by omega))
      have hprod : 0 ≤ lrBScalarCoeff R (n + 2) * (X ^ (n + 2) - X) :=
        mul_nonneg_of_nonpos_of_nonpos hcoeff (sub_nonpos.mpr hpow)
      convert hprod using 1
      ring
  have hChordNonneg :
      0 ≤ X * lrBScalarReserve R 1 +
        lrBScalarCoeff R 0 * (1 - X) := by
    exact add_nonneg
      (mul_nonneg hX.1.le (lrBScalarReserve_one_nonneg hR))
      (mul_nonneg (lrBScalarCoeff_zero_nonneg hR)
        (sub_nonneg.mpr hX.2))
  nlinarith

end CourtadeKumar
