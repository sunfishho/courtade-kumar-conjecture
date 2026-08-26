import InformationTheory.CourtadeKumar.LRBTDerivatives

/-! The `t = 1` endpoint of the audited LR `B` comparison. -/

open Set

namespace CourtadeKumar

noncomputable def lrBH (R v : ℝ) : ℝ :=
  (Real.log (1 + v) + lrL (Real.sqrt R * v)) / v ^ 2 -
    (1 + R) / (2 * Real.sqrt R * v) * Real.artanh (Real.sqrt R * v) -
    4 * lrWKernel R 1 / (1 + v) ^ 2

noncomputable def lrBH0 (v : ℝ) : ℝ :=
  Real.log (1 + v) / v ^ 2 - 1 / 2 -
    4 * (Real.log 2 - 1 / 2) / (1 + v) ^ 2

noncomputable def lrBHAux (R v : ℝ) : ℝ :=
  lrL (Real.sqrt R * v) / v ^ 2 -
    (1 + R) / (2 * Real.sqrt R * v) * Real.artanh (Real.sqrt R * v) +
    1 / 2

noncomputable def lrBHCoeff (R : ℝ) (k : ℕ) : ℝ :=
  R ^ k * ((k : ℝ) + 1 - (k : ℝ) * R) /
    (2 * ((k : ℝ) + 1) * (2 * (k : ℝ) + 1))

theorem lrBHCoeff_nonneg
    {R : ℝ} (hR : R ∈ Icc (0 : ℝ) 1) (k : ℕ) :
    0 ≤ lrBHCoeff R k := by
  unfold lrBHCoeff
  have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
  exact div_nonneg
    (mul_nonneg (pow_nonneg hR.1 _)
      (by nlinarith [mul_le_mul_of_nonneg_left hR.2 hk]))
    (by positivity)

/-- The channel-dependent part of `H_R` has the exact negative power
series `-∑ a_k^* v^(2k)`. -/
theorem lrBHAux_hasSum
    {R v : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1)
    (hv : v ∈ Ioc (0 : ℝ) 1) :
    HasSum (fun n : ℕ ↦
      -lrBHCoeff R (n + 1) * v ^ (2 * (n + 1)))
      (lrBHAux R v) := by
  have hsqrt := lrB_sqrt_mem_Ioo hR
  have hz : Real.sqrt R * v ∈ Ioo (-1 : ℝ) 1 := by
    constructor
    · nlinarith [mul_pos hsqrt.1 hv.1]
    · exact lt_of_le_of_lt
        (mul_le_mul_of_nonneg_left hv.2 hsqrt.1.le) (by simpa using hsqrt.2)
  have hL := (lrL_hasSum hz).mul_left (1 / v ^ 2)
  let Q : ℝ := R * v ^ 2
  have hQ : Q ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · exact mul_pos hR.1 (sq_pos_of_pos hv.1)
    · exact lt_of_le_of_lt
        (mul_le_mul_of_nonneg_left (pow_le_one₀ hv.1.le hv.2) hR.1.le)
        (by simpa using hR.2)
  have hPsi := (topPsiDeriv_hasSum hQ).mul_left (1 + R)
  have hConst : HasSum (fun n : ℕ ↦ if n = 0 then (1 / 2 : ℝ) else 0)
      (1 / 2) := hasSum_ite_eq 0 (1 / 2)
  have hAll := (hL.sub hPsi).add hConst
  have hAll' : HasSum (fun n : ℕ ↦
      R ^ (n + 1) * v ^ (2 * n) / (2 * ((n : ℝ) + 1)) -
        (1 + R) * (R * v ^ 2) ^ n / (2 * (2 * (n : ℝ) + 1)) +
        (if n = 0 then (1 / 2 : ℝ) else 0))
      (lrBHAux R v) := by
    convert hAll using 1
    · funext n
      rw [show (Real.sqrt R * v) ^ (2 * (n + 1)) =
          R ^ (n + 1) * v ^ (2 * (n + 1)) by
        rw [mul_pow, pow_mul, Real.sq_sqrt hR.1.le]]
      rw [show v ^ (2 * (n + 1)) = v ^ (2 * n) * v ^ 2 by
        rw [show 2 * (n + 1) = 2 * n + 2 by omega, pow_add]]
      field_simp [hv.1.ne']
      ring
    · unfold lrBHAux topPsiDeriv
      have hsqrtQ : Real.sqrt Q = Real.sqrt R * v := by
        dsimp [Q]
        rw [Real.sqrt_mul hR.1.le, Real.sqrt_sq_eq_abs, abs_of_pos hv.1]
      rw [hsqrtQ]
      field_simp [hsqrt.1.ne', hv.1.ne']
  have hTail := (hasSum_nat_add_iff' 1).2 hAll'
  convert hTail using 1
  · funext n
    unfold lrBHCoeff
    simp only [Nat.cast_add, Nat.cast_one, if_neg (by omega : n + 1 ≠ 0)]
    rw [mul_pow, pow_mul]
    rw [show R ^ (n + 1 + 1) = R ^ (n + 1) * R by
      rw [show n + 1 + 1 = (n + 1) + 1 by omega, pow_succ]]
    have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
    have hodd : 2 * (n : ℝ) + 3 ≠ 0 := by positivity
    field_simp [hn1, hodd]
    ring
  · norm_num
    ring

lemma lrBHAux_one_eq_W_sub
    {R : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1) :
    lrBHAux R 1 = lrWKernel R 1 - (Real.log 2 - 1 / 2) := by
  have hsqrt := lrB_sqrt_mem_Ioo hR
  have hPhi := mul_artanh_sub_topPhi_eq_lrL
    (show Real.sqrt R ∈ Ioo (-1 : ℝ) 1 from
      ⟨by linarith [hsqrt.1], hsqrt.2⟩)
  unfold lrBHAux lrWKernel
  simp only [mul_one, one_pow, div_one, topPhi_one]
  rw [← hPhi]
  field_simp [hsqrt.1.ne']
  ring_nf
  rw [Real.sq_sqrt hR.1.le]
  ring

lemma lrBH_sub_lrBH0
    {R v : ℝ} (hv : v ≠ 0) :
    lrBH R v - lrBH0 v =
      lrBHAux R v -
        4 / (1 + v) ^ 2 *
          (lrWKernel R 1 - (Real.log 2 - 1 / 2)) := by
  unfold lrBH lrBH0 lrBHAux
  field_simp [hv]
  ring

/-- Exact nonnegative series for `H_R-H_0`. -/
theorem lrBH_sub_lrBH0_hasSum
    {R v : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1)
    (hv : v ∈ Ioc (0 : ℝ) 1) :
    HasSum (fun n : ℕ ↦ lrBHCoeff R (n + 1) *
      (4 / (1 + v) ^ 2 - v ^ (2 * (n + 1))))
      (lrBH R v - lrBH0 v) := by
  have hvOne : (1 : ℝ) ∈ Ioc (0 : ℝ) 1 := by norm_num
  have hV := lrBHAux_hasSum hR hv
  have hOne := lrBHAux_hasSum hR hvOne
  have h := hV.sub (hOne.mul_left (4 / (1 + v) ^ 2))
  convert h using 1
  · funext n
    ring
  · rw [lrBH_sub_lrBH0 hv.1.ne', lrBHAux_one_eq_W_sub hR]

theorem lrBH_sub_lrBH0_nonneg
    {R v : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1)
    (hv : v ∈ Ioc (0 : ℝ) 1) :
    0 ≤ lrBH R v - lrBH0 v := by
  apply (lrBH_sub_lrBH0_hasSum hR hv).nonneg
  intro n
  apply mul_nonneg (lrBHCoeff_nonneg ⟨hR.1.le, hR.2.le⟩ (n + 1))
  have hvpow : v ^ (n + 1) ∈ Icc (0 : ℝ) 1 :=
    ⟨pow_nonneg hv.1.le _, pow_le_one₀ hv.1.le hv.2⟩
  have hfracPos : 0 ≤ 2 / (1 + v) :=
    div_nonneg (by norm_num) (by linarith [hv.1])
  have hfrac : 1 ≤ 2 / (1 + v) := by
    rw [le_div_iff₀ (by linarith [hv.1])]
    linarith [hv.2]
  have hsq : (v ^ (n + 1)) ^ 2 ≤ (2 / (1 + v)) ^ 2 :=
    (sq_le_sq₀ hvpow.1 hfracPos).2 (hvpow.2.trans hfrac)
  rw [show 2 * (n + 1) = (n + 1) * 2 by omega, pow_mul]
  rw [sub_nonneg]
  calc
    (v ^ (n + 1)) ^ 2 ≤ (2 / (1 + v)) ^ 2 := hsq
    _ = 4 / (1 + v) ^ 2 := by
      field_simp [show 1 + v ≠ 0 by linarith [hv.1]]
      ring

end CourtadeKumar
