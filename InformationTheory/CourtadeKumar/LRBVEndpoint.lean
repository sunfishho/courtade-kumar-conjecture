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

noncomputable def lrLogCubicGap (r : ℝ) : ℝ :=
  -Real.log (1 - r) - (r + r ^ 2 / 2 + r ^ 3 / 3)

theorem hasDerivAt_lrLogCubicGap
    {r : ℝ} (hr : r ≠ 1) :
    HasDerivAt lrLogCubicGap (r ^ 3 / (1 - r)) r := by
  have hid := hasDerivAt_id r
  have harg : HasDerivAt (fun x : ℝ ↦ 1 - x) (-1) r := by
    simpa using hid.const_sub 1
  have hlog := harg.log (sub_ne_zero.mpr hr.symm)
  have hpoly : HasDerivAt
      (fun x : ℝ ↦ x + x ^ 2 / 2 + x ^ 3 / 3)
      (1 + r + r ^ 2) r := by
    convert (hid.add ((hid.pow 2).div_const 2)).add ((hid.pow 3).div_const 3)
      using 1
    norm_num
  unfold lrLogCubicGap
  convert hlog.neg.sub hpoly using 1
  field_simp [sub_ne_zero.mpr hr.symm]
  ring

theorem lr_neg_log_one_sub_cubic_lower
    {r : ℝ} (hr : r ∈ Icc (0 : ℝ) (1 / 2)) :
    r + r ^ 2 / 2 + r ^ 3 / 3 ≤ -Real.log (1 - r) := by
  have hmono : MonotoneOn lrLogCubicGap (Icc (0 : ℝ) (1 / 2)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc (0 : ℝ) (1 / 2))
    · intro x hx
      exact (hasDerivAt_lrLogCubicGap (by linarith [hx.2])).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      exact (hasDerivAt_lrLogCubicGap (by linarith [hx.2])).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      rw [(hasDerivAt_lrLogCubicGap (by linarith [hx.2])).deriv]
      exact div_nonneg (pow_nonneg hx.1.le _) (sub_nonneg.mpr (by linarith [hx.2]))
  have h := hmono (show (0 : ℝ) ∈ Icc 0 (1 / 2) by norm_num) hr hr.1
  simpa [lrLogCubicGap] using h

theorem hasDerivAt_lrBH0
    {v : ℝ} (hv : v ≠ 0) (hv1 : v ≠ -1) :
    HasDerivAt lrBH0
      ((v / (1 + v) - 2 * Real.log (1 + v) +
          8 * (Real.log 2 - 1 / 2) * (v / (1 + v)) ^ 3) / v ^ 3) v := by
  have hid := hasDerivAt_id v
  have hplus : HasDerivAt (fun x : ℝ ↦ 1 + x) 1 v := by
    simpa using hid.const_add 1
  have hplusne : 1 + v ≠ 0 := by
    intro h
    apply hv1
    linarith
  have hlog := hplus.log hplusne
  have hsq : HasDerivAt (fun x : ℝ ↦ x ^ 2) (2 * v) v := by
    convert hid.pow 2 using 1
    norm_num
  have hfirst := hlog.div hsq (pow_ne_zero 2 hv)
  have hthirdDen : HasDerivAt (fun x : ℝ ↦ (1 + x) ^ 2)
      (2 * (1 + v)) v := by
    convert hplus.pow 2 using 1
    norm_num
  have hthird := (hasDerivAt_const v (4 * (Real.log 2 - 1 / 2))).div
    hthirdDen (pow_ne_zero 2 hplusne)
  unfold lrBH0
  convert (hfirst.sub_const (1 / 2)).sub hthird using 1
  field_simp [hv, hplusne]
  ring

theorem lrBH0_deriv_nonpos
    {v : ℝ} (hv : v ∈ Ioc (0 : ℝ) 1) :
    ((v / (1 + v) - 2 * Real.log (1 + v) +
        8 * (Real.log 2 - 1 / 2) * (v / (1 + v)) ^ 3) / v ^ 3) ≤ 0 := by
  let r : ℝ := v / (1 + v)
  have hden : 0 < 1 + v := by linarith [hv.1]
  have hr : r ∈ Ioc (0 : ℝ) (1 / 2) := by
    constructor
    · exact div_pos hv.1 hden
    · rw [div_le_iff₀ hden]
      linarith [hv.2]
  have hlogEq : -Real.log (1 - r) = Real.log (1 + v) := by
    have hone : 1 - r = (1 + v)⁻¹ := by
      dsimp [r]
      field_simp [hden.ne']
      ring
    rw [hone, Real.log_inv]
    ring
  have hlog := lr_neg_log_one_sub_cubic_lower
    (show r ∈ Icc (0 : ℝ) (1 / 2) from ⟨hr.1.le, hr.2⟩)
  rw [hlogEq] at hlog
  have hcoeff : 8 * (Real.log 2 - 1 / 2) - 2 / 3 < 4 / 3 := by
    linarith [lr_log_two_lt_three_quarters]
  have hr3 : r ^ 3 ≤ r ^ 2 / 2 := by
    nlinarith [mul_nonneg (sq_nonneg r) (sub_nonneg.mpr hr.2)]
  have hcoeffMul :
      (8 * (Real.log 2 - 1 / 2) - 2 / 3) * r ^ 3 ≤
        (4 / 3) * r ^ 3 :=
    mul_le_mul_of_nonneg_right hcoeff.le (pow_nonneg hr.1.le _)
  have h43 : (4 / 3) * r ^ 3 ≤ (2 / 3) * r ^ 2 := by
    nlinarith
  have htail :
      (8 * (Real.log 2 - 1 / 2) - 2 / 3) * r ^ 3 ≤
        (2 / 3) * r ^ 2 := hcoeffMul.trans h43
  have hlogGap : 0 ≤
      2 * Real.log (1 + v) -
        2 * (r + r ^ 2 / 2 + r ^ 3 / 3) := by
    linarith
  have hnum :
      r - 2 * Real.log (1 + v) +
        8 * (Real.log 2 - 1 / 2) * r ^ 3 ≤ 0 := by
    calc
      r - 2 * Real.log (1 + v) +
          8 * (Real.log 2 - 1 / 2) * r ^ 3 =
        -(2 * Real.log (1 + v) -
            2 * (r + r ^ 2 / 2 + r ^ 3 / 3)) - r - r ^ 2 +
          (8 * (Real.log 2 - 1 / 2) - 2 / 3) * r ^ 3 := by
            ring
      _ ≤ 0 := by linarith [hr.1.le, sq_nonneg r]
  dsimp [r] at hnum ⊢
  exact div_nonpos_of_nonpos_of_nonneg hnum (pow_nonneg hv.1.le _)

theorem lrBH0_nonneg
    {v : ℝ} (hv : v ∈ Ioc (0 : ℝ) 1) :
    0 ≤ lrBH0 v := by
  have hanti : AntitoneOn lrBH0 (Icc v 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc v 1)
    · intro x hx
      exact (hasDerivAt_lrBH0 (by linarith [hv.1, hx.1])
        (by linarith [hv.1, hx.1])).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      exact (hasDerivAt_lrBH0 (by linarith [hv.1, hx.1])
        (by linarith [hv.1, hx.1])).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      have hxPhysical : x ∈ Ioc (0 : ℝ) 1 :=
        ⟨by linarith [hv.1, hx.1], hx.2.le⟩
      rw [(hasDerivAt_lrBH0 hxPhysical.1.ne' (by linarith [hxPhysical.1])).deriv]
      exact lrBH0_deriv_nonpos hxPhysical
  have h := hanti ⟨le_rfl, hv.2⟩ ⟨hv.2, le_rfl⟩ hv.2
  have hOne : lrBH0 1 = 0 := by
    unfold lrBH0
    norm_num
  rw [hOne] at h
  exact h

theorem lrBH_nonneg
    {R v : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1)
    (hv : v ∈ Ioc (0 : ℝ) 1) :
    0 ≤ lrBH R v := by
  linarith [lrBH_sub_lrBH0_nonneg hR hv, lrBH0_nonneg hv]

end CourtadeKumar
