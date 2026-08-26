import InformationTheory.CourtadeKumar.LRScalarSeries
import InformationTheory.CourtadeKumar.LRBernsteinP

/-! Monotonicity in `t` for the audited LR `B` comparison. -/

open Set

namespace CourtadeKumar

/-- The bracket on the right side of equation `(lr-B-t-derivative)`. -/
noncomputable def lrBTDerivativeBracket (R v t : ℝ) : ℝ :=
  lrBGamma R * (lrBKernelK R t + v * lrBKernelK R (v * t)) +
    R * v ^ 2 * lrFlowQWeight v t / (1 - R * v ^ 2 * t ^ 2) -
    (1 + v) * (Real.log (1 + v) + lrL (Real.sqrt R * v * t))

/-- The elementary logarithmic lower bound used after applying the scalar
comparison at `t` and `v t`. -/
theorem lrL_sqrt_mul_sub_lower
    {R v t : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1)
    (hv : v ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    R * t ^ 2 * (1 - v ^ 2) / (2 * (1 - R * v ^ 2 * t ^ 2)) ≤
      lrL (Real.sqrt R * t) - lrL (Real.sqrt R * v * t) := by
  have hsqrtSq : Real.sqrt R ^ 2 = R := Real.sq_sqrt hR.1.le
  have hRt : R * t ^ 2 < 1 := by
    have htSq : t ^ 2 ≤ 1 := pow_le_one₀ ht.1 ht.2
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left htSq hR.1.le)
      (by simpa using hR.2)
  have hRvt : R * v ^ 2 * t ^ 2 < 1 := by
    have hvSq : v ^ 2 ≤ 1 := pow_le_one₀ hv.1 hv.2
    have htSq : t ^ 2 ≤ 1 := pow_le_one₀ ht.1 ht.2
    nlinarith [mul_le_mul hvSq htSq (sq_nonneg t) (by norm_num : (0 : ℝ) ≤ 1),
      mul_lt_mul_of_pos_left hR.2 (by norm_num : (0 : ℝ) < 1)]
  have hA : 0 < 1 - R * t ^ 2 := by linarith
  have hB : 0 < 1 - R * v ^ 2 * t ^ 2 := by linarith
  have hlog := Real.one_sub_inv_le_log_of_pos (div_pos hB hA)
  rw [Real.log_div hB.ne' hA.ne'] at hlog
  unfold lrL
  rw [show (Real.sqrt R * t) ^ 2 = R * t ^ 2 by
      rw [mul_pow, hsqrtSq],
    show (Real.sqrt R * v * t) ^ 2 = R * v ^ 2 * t ^ 2 by
      rw [mul_pow, mul_pow, hsqrtSq]]
  have hratio :
      1 - ((1 - R * v ^ 2 * t ^ 2) / (1 - R * t ^ 2))⁻¹ =
        R * t ^ 2 * (1 - v ^ 2) / (1 - R * v ^ 2 * t ^ 2) := by
    field_simp [hA.ne', hB.ne']
    ring
  rw [hratio] at hlog
  have hhalf := mul_le_mul_of_nonneg_left hlog (by norm_num : (0 : ℝ) ≤ 1 / 2)
  calc
    R * t ^ 2 * (1 - v ^ 2) / (2 * (1 - R * v ^ 2 * t ^ 2)) =
        (1 / 2 : ℝ) *
          (R * t ^ 2 * (1 - v ^ 2) / (1 - R * v ^ 2 * t ^ 2)) := by
            field_simp [hB.ne']
    _ ≤ (1 / 2 : ℝ) *
        (Real.log (1 - R * v ^ 2 * t ^ 2) -
          Real.log (1 - R * t ^ 2)) := hhalf
    _ = -(1 / 2 : ℝ) * Real.log (1 - R * t ^ 2) -
        -(1 / 2 : ℝ) * Real.log (1 - R * v ^ 2 * t ^ 2) := by ring

/-- Exact denominator clearing that exposes the certified Bernstein
polynomial in the `t` derivative. -/
lemma lrBT_remainder_eq_polynomial
    {R v t : ℝ} (hRt : 1 - R * t ^ 2 ≠ 0)
    (hRvt : 1 - R * v ^ 2 * t ^ 2 ≠ 0) :
    R * t ^ 2 * (1 - v ^ 2) / (2 * (1 - R * v ^ 2 * t ^ 2)) +
        R * v ^ 2 * lrFlowQWeight v t / (1 - R * v ^ 2 * t ^ 2) -
        R * t ^ 2 * (1 - t ^ 2) / (2 * (1 - R * t ^ 2)) -
        v * (R * (v * t) ^ 2 * (1 - (v * t) ^ 2) /
          (2 * (1 - R * (v * t) ^ 2))) =
      R * lrBComparisonPolynomial R v (t ^ 2) /
        (2 * (1 - R * t ^ 2) * (1 - R * v ^ 2 * t ^ 2)) := by
  have hRvt' : 1 - R * (v * t) ^ 2 ≠ 0 := by
    convert hRvt using 1
    ring
  have hRvt'' : 1 - R * t ^ 2 * v ^ 2 ≠ 0 := by
    convert hRvt using 1
    ring
  unfold lrFlowQWeight lrBComparisonPolynomial
  field_simp [hRt, hRvt, hRvt', hRvt'']
  ring

/-- Pointwise nonnegativity of the bracket in the audited `t` derivative. -/
theorem lrBTDerivativeBracket_nonneg
    {R v t : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1)
    (hv : v ∈ Ioc (0 : ℝ) 1) (ht : t ∈ Ioc (0 : ℝ) 1) :
    0 ≤ lrBTDerivativeBracket R v t := by
  have hvt : v * t ∈ Ioc (0 : ℝ) 1 := by
    constructor
    · exact mul_pos hv.1 ht.1
    · nlinarith [mul_le_mul hv.2 ht.2 ht.1.le
        (by norm_num : (0 : ℝ) ≤ 1)]
  have hScalarT := lrBScalarReserve_nonneg hR ht
  have hScalarVT := lrBScalarReserve_nonneg hR hvt
  have hL := lrL_sqrt_mul_sub_lower hR
    (show v ∈ Icc (0 : ℝ) 1 from ⟨hv.1.le, hv.2⟩)
    (show t ∈ Icc (0 : ℝ) 1 from ⟨ht.1.le, ht.2⟩)
  have hRt : 0 < 1 - R * t ^ 2 := by
    have htSq : t ^ 2 ≤ 1 := pow_le_one₀ ht.1.le ht.2
    have hmul : R * t ^ 2 ≤ R := by
      simpa using mul_le_mul_of_nonneg_left htSq hR.1.le
    exact sub_pos.mpr (hmul.trans_lt hR.2)
  have hRvt : 0 < 1 - R * v ^ 2 * t ^ 2 := by
    have hvtSq : (v * t) ^ 2 ≤ 1 := pow_le_one₀ hvt.1.le hvt.2
    rw [mul_pow] at hvtSq
    have hmul : R * (v ^ 2 * t ^ 2) ≤ R := by
      simpa using mul_le_mul_of_nonneg_left hvtSq hR.1.le
    exact sub_pos.mpr (by
      calc
        R * v ^ 2 * t ^ 2 = R * (v ^ 2 * t ^ 2) := by ring
        _ ≤ R := hmul
        _ < 1 := hR.2)
  have hPoly : 0 ≤ lrBComparisonPolynomial R v (t ^ 2) :=
    lrBComparisonPolynomial_nonneg
      ⟨hR.1.le, hR.2.le⟩ ⟨hv.1.le, hv.2⟩
      ⟨sq_nonneg t, pow_le_one₀ ht.1.le ht.2⟩
  have hRem : 0 ≤
      R * lrBComparisonPolynomial R v (t ^ 2) /
        (2 * (1 - R * t ^ 2) * (1 - R * v ^ 2 * t ^ 2)) := by
    exact div_nonneg (mul_nonneg hR.1.le hPoly)
      (mul_nonneg (mul_nonneg (by norm_num) hRt.le) hRvt.le)
  have hLog : 0 ≤ Real.log 2 - Real.log (1 + v) := by
    rw [sub_nonneg]
    exact Real.log_le_log (by linarith [hv.1]) (by linarith [hv.2])
  rw [lrBScalarReserve] at hScalarT hScalarVT
  rw [show Real.sqrt R * (v * t) = Real.sqrt R * v * t by ring] at hScalarVT
  rw [lrBTDerivativeBracket]
  have hIdentity := lrBT_remainder_eq_polynomial hRt.ne' hRvt.ne'
  have hScalarVT' := mul_nonneg hv.1.le hScalarVT
  have hLog' := mul_nonneg (by linarith [hv.1] : 0 ≤ 1 + v) hLog
  have hScalarSum : 0 ≤
      lrBGamma R * (lrBKernelK R t + v * lrBKernelK R (v * t)) -
        (lrL (Real.sqrt R * t) + v * lrL (Real.sqrt R * v * t)) +
        R * t ^ 2 * (1 - t ^ 2) / (2 * (1 - R * t ^ 2)) +
        v * (R * (v * t) ^ 2 * (1 - (v * t) ^ 2) /
          (2 * (1 - R * (v * t) ^ 2))) -
        (1 + v) * Real.log 2 := by
    nlinarith
  have hRemainder : 0 ≤
      (lrL (Real.sqrt R * t) - lrL (Real.sqrt R * v * t)) +
        R * v ^ 2 * lrFlowQWeight v t / (1 - R * v ^ 2 * t ^ 2) -
        R * t ^ 2 * (1 - t ^ 2) / (2 * (1 - R * t ^ 2)) -
        v * (R * (v * t) ^ 2 * (1 - (v * t) ^ 2) /
          (2 * (1 - R * (v * t) ^ 2))) := by
    nlinarith
  nlinarith

end CourtadeKumar
