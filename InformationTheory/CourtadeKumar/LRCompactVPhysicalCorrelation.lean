import InformationTheory.CourtadeKumar.LRCompactVReplayLedger

/-!
# Physical correlation in the final compact channel chart

Positive physical slack forces the squared ray coordinate away from one.
This is the analytic input behind the correlated monomial enclosure used for
`R≥17/20`.
-/

open Set

namespace CourtadeKumar

theorem lrCompactV_physical_log_correlation
    {R v x : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1)
    (hv : v ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1)
    (hJ : 0 < lrCompactVJX ⟨R, v, x⟩) :
    (1 - R * (v ^ 2 * x)) ^ 2 <
      (1 + v) ^ 2 * (1 - v ^ 2 * x) := by
  let y := v ^ 2 * x
  let B := lrFlowB R v (Real.sqrt x)
  let A := lrCompactVAX v x
  have hyPos : 0 < y := by
    dsimp [y]
    exact mul_pos (sq_pos_of_pos hv.1) hx.1
  have hyLt : y < 1 := by
    dsimp [y]
    have hvSqLt : v ^ 2 < 1 := by nlinarith [hv.1, hv.2]
    calc
      v ^ 2 * x < 1 * x := mul_lt_mul_of_pos_right hvSqLt hx.1
      _ < 1 := by simpa using hx.2
  have hRyLt : R * y < 1 := by
    calc
      R * y < 1 * y := mul_lt_mul_of_pos_right hR.2 hyPos
      _ < 1 := by simpa using hyLt
  have hBPos : 0 < B := by
    dsimp [B]
    have hsqrt : Real.sqrt x ∈ Ioo (0 : ℝ) 1 := by
      exact ⟨Real.sqrt_pos.2 hx.1,
        by simpa using (Real.sqrt_lt_sqrt_iff hx.1.le).2 hx.2⟩
    apply lrFlowB_pos hv.1 hsqrt.1.le
    have hsqrtR : Real.sqrt R < 1 := by
      simpa using (Real.sqrt_lt_sqrt_iff hR.1.le).2 hR.2
    calc
      Real.sqrt R * v * Real.sqrt x < 1 * v * Real.sqrt x := by
        exact mul_lt_mul_of_pos_right
          (mul_lt_mul_of_pos_right hsqrtR hv.1) hsqrt.1
      _ < 1 := by
        have := mul_lt_mul_of_pos_right hv.2 hsqrt.1
        nlinarith [hsqrt.2]
  have hA_lt_twoB : A < 2 * B := by
    have hJ' : 0 < (1 + x) * B - A := by
      simpa [lrCompactVJX, B, A] using hJ
    have hxFactor : 1 + x < 2 := by nlinarith [hx.2]
    have hprod : (1 + x) * B < 2 * B :=
      mul_lt_mul_of_pos_right hxFactor hBPos
    linarith
  have hsquareX : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt hx.1.le
  have hsquareR : (Real.sqrt R) ^ 2 = R := Real.sq_sqrt hR.1.le
  have hargSquare :
      (Real.sqrt R * v * Real.sqrt x) ^ 2 = R * y := by
    dsimp [y]
    rw [mul_pow, mul_pow, hsquareR, hsquareX]
    ring
  have hBform :
      B = Real.log (1 + v) -
        (1 / 2 : ℝ) * Real.log (1 - R * y) := by
    dsimp [B]
    unfold lrFlowB lrFlowBeta lrL
    rw [hargSquare]
    ring
  have hAform :
      A = Real.log (1 + v) -
        (1 / 2 : ℝ) * Real.log (1 - y) := by
    dsimp [A, y]
    unfold lrCompactVAX
    rfl
  have hlog :
      2 * Real.log (1 - R * y) <
        2 * Real.log (1 + v) + Real.log (1 - y) := by
    rw [hAform, hBform] at hA_lt_twoB
    linarith
  have honeV : 1 + v ≠ 0 := by nlinarith [hv.1]
  have honeY : 1 - y ≠ 0 := by linarith
  have honeRY : 1 - R * y ≠ 0 := by linarith
  have hleftLog :
      Real.log ((1 - R * y) ^ 2) =
        2 * Real.log (1 - R * y) := by
    rw [Real.log_pow]
    norm_num
  have hrightLog :
      Real.log ((1 + v) ^ 2 * (1 - y)) =
        2 * Real.log (1 + v) + Real.log (1 - y) := by
    rw [Real.log_mul (pow_ne_zero 2 honeV) honeY, Real.log_pow]
    norm_num
  have hlog' : Real.log ((1 - R * y) ^ 2) <
      Real.log ((1 + v) ^ 2 * (1 - y)) := by
    rw [hleftLog, hrightLog]
    exact hlog
  have hleftPos : 0 < (1 - R * y) ^ 2 := sq_pos_of_pos (by linarith)
  have hrightPos : 0 < (1 + v) ^ 2 * (1 - y) :=
    mul_pos (sq_pos_of_pos (by linarith [hv.1])) (sub_pos.mpr hyLt)
  have hresult : (1 - R * y) ^ 2 < (1 + v) ^ 2 * (1 - y) := by
    by_contra hnot
    have hge : (1 + v) ^ 2 * (1 - y) ≤ (1 - R * y) ^ 2 :=
      le_of_not_gt hnot
    have hlogLe := Real.log_le_log hrightPos hge
    linarith
  simpa [y] using hresult

theorem lrCompactV_physical_y_upper
    {R v x : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1)
    (hv : v ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1)
    (hJ : 0 < lrCompactVJX ⟨R, v, x⟩) :
    v ^ 2 * x < 1 - (1 - R) ^ 2 / (1 + v) ^ 2 := by
  have hcorr := lrCompactV_physical_log_correlation hR hv hx hJ
  have hyLe : v ^ 2 * x ≤ 1 := by
    have hvSqLe : v ^ 2 ≤ 1 := by nlinarith [hv.1, hv.2]
    nlinarith [mul_le_mul_of_nonneg_right hvSqLe hx.1.le, hx.2.le]
  have hbase : 0 ≤ 1 - R := sub_nonneg.mpr hR.2.le
  have hcompare : (1 - R) ^ 2 ≤ (1 - R * (v ^ 2 * x)) ^ 2 := by
    gcongr
    nlinarith [mul_le_mul_of_nonneg_left hyLe hR.1.le]
  have hstrict : (1 - R) ^ 2 <
      (1 + v) ^ 2 * (1 - v ^ 2 * x) := hcompare.trans_lt hcorr
  have hden : 0 < (1 + v) ^ 2 := sq_pos_of_pos (by linarith [hv.1])
  have hdiv : (1 - R) ^ 2 / (1 + v) ^ 2 < 1 - v ^ 2 * x := by
    rw [div_lt_iff₀ hden]
    simpa [mul_comm] using hstrict
  linarith

end CourtadeKumar
