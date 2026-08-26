import InformationTheory.CourtadeKumar.LRNegativeChartClosure

/-! Algebraic assembly of the positive-`J` midpoint chart. -/

open Set

namespace CourtadeKumar

noncomputable def lrFlowCcal (R v t : ℝ) : ℝ :=
  (1 - R) * (v ^ 2 * t ^ 2) / (2 * (1 - R * v ^ 2 * t ^ 2))

noncomputable def lrFlowUReserve (R v t : ℝ) : ℝ :=
  lrFlowB R v t * lrFlowY₀ R v t +
    lrFlowCcal R v t * lrFlowX₀ R v t

lemma lrFlowQWeight_nonneg
    {v t : ℝ} (hv : v ∈ Ioc (0 : ℝ) 1)
    (ht : t ∈ Ioc (0 : ℝ) 1) :
    0 ≤ lrFlowQWeight v t := by
  unfold lrFlowQWeight
  have htSq : t ^ 2 ≤ 1 := by nlinarith [ht.1, ht.2]
  exact add_nonneg (sub_nonneg.mpr hv.2)
    (mul_nonneg
      (div_nonneg (by linarith [hv.1]) (by norm_num))
      (sub_nonneg.mpr htSq))

/-- The radial log increment dominates its terminal tangent. -/
theorem lrFlowCcal_le_lrFlowD
    {R v t : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1)
    (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    lrFlowCcal R v t ≤ lrFlowD R v t := by
  let ξ := v ^ 2 * t ^ 2
  have hxiPos : 0 < ξ := by
    unfold ξ
    exact mul_pos (sq_pos_of_pos hv.1) (sq_pos_of_pos ht.1)
  have hxiLt : ξ < 1 := by
    unfold ξ
    have hvt : v * t < 1 := by
      nlinarith [mul_lt_mul_of_pos_right hv.2 ht.1,
        mul_lt_mul_of_pos_left ht.2 hv.1]
    nlinarith [mul_pos hv.1 ht.1]
  have hdenOne : 0 < 1 - ξ := by linarith
  have hdenR : 0 < 1 - R * ξ := by
    have hmul : R * ξ < 1 := calc
      R * ξ < 1 * ξ := mul_lt_mul_of_pos_right hR.2 hxiPos
      _ < 1 := by simpa using hxiLt
    linarith
  have hlog := Real.log_le_sub_one_of_pos (div_pos hdenOne hdenR)
  rw [Real.log_div hdenOne.ne' hdenR.ne'] at hlog
  have hlogBound :
      (1 - R) * ξ / (1 - R * ξ) ≤
        Real.log (1 - R * ξ) - Real.log (1 - ξ) := by
    have hid :
        (1 - R) * ξ / (1 - R * ξ) =
          1 - (1 - ξ) / (1 - R * ξ) := by
      field_simp [hdenR.ne']
      ring
    rw [hid]
    linarith
  have hshape : Real.sqrt R * v * t ∈ Ioo (-1 : ℝ) 1 := by
    have hsqrt := lrB_sqrt_mem_Ioo hR
    constructor
    · nlinarith [mul_pos (mul_pos hsqrt.1 hv.1) ht.1]
    · have hvt : v * t < 1 := by
        nlinarith [mul_lt_mul_of_pos_right hv.2 ht.1,
          mul_lt_mul_of_pos_left ht.2 hv.1]
      calc
        Real.sqrt R * v * t = Real.sqrt R * (v * t) := by ring
        _ < 1 * (v * t) :=
          mul_lt_mul_of_pos_right hsqrt.2 (mul_pos hv.1 ht.1)
        _ < 1 := by simpa using hvt
  have hsqrtSq : (Real.sqrt R) ^ 2 = R := Real.sq_sqrt hR.1.le
  unfold lrFlowCcal lrFlowD lrFlowA lrFlowB
  rw [show lrFlowBeta v + lrL (v * t) -
      (lrFlowBeta v + lrL (Real.sqrt R * v * t)) =
      lrL (v * t) - lrL (Real.sqrt R * v * t) by ring]
  dsimp [ξ] at hlogBound
  unfold lrL
  rw [show (Real.sqrt R * v * t) ^ 2 = R * ξ by
    unfold ξ
    calc
      (Real.sqrt R * v * t) ^ 2 =
          (Real.sqrt R) ^ 2 * v ^ 2 * t ^ 2 := by ring
      _ = R * (v ^ 2 * t ^ 2) := by rw [hsqrtSq]; ring]
  have hhalf := mul_le_mul_of_nonneg_left hlogBound
    (show 0 ≤ (1 / 2 : ℝ) by norm_num)
  dsimp [ξ] at hhalf ⊢
  have hdenActual : 1 - R * (v ^ 2 * t ^ 2) ≠ 0 := by
    simpa [ξ] using hdenR.ne'
  convert hhalf using 1 <;> field_simp [hdenActual] <;> ring

/-- The exact midpoint certificate `(U)` closes the first half of the
positive chart. -/
theorem lrFlowNumeratorP_halfMidpoint_nonneg_of_U
    {R v t : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1)
    (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1)
    (hJ : 0 < lrFlowJ R v t)
    (hU : 0 ≤ lrFlowUReserve R v t) :
    0 ≤ lrFlowNumeratorP R (lrFlowM v / 2) v t := by
  have hsqrt := lrB_sqrt_mem_Ioo hR
  have hvt : v * t < 1 := by
    nlinarith [mul_lt_mul_of_pos_right hv.2 ht.1,
      mul_lt_mul_of_pos_left ht.2 hv.1]
  have hshape : Real.sqrt R * v * t < 1 := by
    rw [mul_assoc]
    calc
      Real.sqrt R * (v * t) < 1 * (v * t) :=
        mul_lt_mul_of_pos_right hsqrt.2 (mul_pos hv.1 ht.1)
      _ < 1 := by simpa using hvt
  have hB : 0 < lrFlowB R v t := lrFlowB_pos hv.1 ht.1.le hshape
  have hCcal : 0 ≤ lrFlowCcal R v t := by
    unfold lrFlowCcal
    have hden : 0 < 1 - R * v ^ 2 * t ^ 2 := by
      have hsqrtSq : (Real.sqrt R) ^ 2 = R := Real.sq_sqrt hR.1.le
      have hshapeNonneg : 0 ≤ Real.sqrt R * v * t :=
        mul_nonneg (mul_nonneg (Real.sqrt_nonneg R) hv.1.le) ht.1.le
      have hshapeSq : (Real.sqrt R * v * t) ^ 2 < 1 := by
        nlinarith
      rw [show (Real.sqrt R * v * t) ^ 2 =
          (Real.sqrt R) ^ 2 * v ^ 2 * t ^ 2 by ring,
        hsqrtSq] at hshapeSq
      linarith
    exact div_nonneg
      (mul_nonneg (sub_nonneg.mpr hR.2.le)
        (mul_nonneg (sq_nonneg v) (sq_nonneg t)))
      (mul_nonneg (by norm_num) hden.le)
  have hDge := lrFlowCcal_le_lrFlowD hR hv ht
  have hAbel := lrFlow_noise_lift_nonneg hR hv ht
  have hq := lrFlowQWeight_nonneg
    (show v ∈ Ioc (0 : ℝ) 1 from ⟨hv.1, hv.2.le⟩)
    (show t ∈ Ioc (0 : ℝ) 1 from ⟨ht.1, ht.2.le⟩)
  have hZ : 0 ≤ lrFlowZ R v t := by
    have hH : lrFlowH R v t = -lrFlowJ R v t := lrFlowH_eq_negJ R v t
    rw [hH] at hAbel
    nlinarith [mul_nonneg hq hJ.le]
  have hmid := lrFlowNumeratorP_halfMidpoint
    (R := R) (v := v) (t := t) (by linarith [hv.1])
  by_cases hX : 0 ≤ lrFlowX₀ R v t
  · have hDX := mul_le_mul_of_nonneg_right hDge hX
    unfold lrFlowUReserve at hU
    rw [hmid]
    nlinarith
  · have hXnonpos : lrFlowX₀ R v t ≤ 0 := le_of_not_ge hX
    have hratio : lrFlowD R v t / lrFlowB R v t < t ^ 2 := by
      rw [div_lt_iff₀ hB]
      unfold lrFlowJ at hJ
      nlinarith
    have hratioX : t ^ 2 * lrFlowX₀ R v t ≤
        (lrFlowD R v t / lrFlowB R v t) * lrFlowX₀ R v t :=
      mul_le_mul_of_nonpos_right hratio.le hXnonpos
    have hYX : 0 ≤ lrFlowY₀ R v t +
        (lrFlowD R v t / lrFlowB R v t) * lrFlowX₀ R v t := by
      have hidentity := lrFlowY₀_add_t_sq_mul_X₀
        (R := R) (v := v) (t := t) (by linarith [hv.1])
      nlinarith
    have hscaled := mul_nonneg hB.le hYX
    rw [hmid]
    field_simp [hB.ne'] at hscaled
    nlinarith

end CourtadeKumar
