import InformationTheory.CourtadeKumar.TopB0Series

/-! Closed summation of the main part of the simplified common primitive. -/

open Set Filter
open scoped BigOperators Topology

namespace CourtadeKumar

private lemma sum_range_inv_mul_succ (N : ℕ) :
    ∑ n ∈ Finset.range N,
      (1 : ℝ) / ((n + 1) * (n + 2)) =
        1 - 1 / (N + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      have hN1 : (N : ℝ) + 1 ≠ 0 := by positivity
      have hN2 : (N : ℝ) + 2 ≠ 0 := by positivity
      field_simp [hN1, hN2]
      ring

lemma hasSum_inv_mul_succ :
    HasSum (fun n : ℕ ↦ (1 : ℝ) / ((n + 1) * (n + 2))) 1 := by
  rw [hasSum_iff_tendsto_nat_of_nonneg (fun n ↦ by positivity)]
  have hinv : Tendsto (fun N : ℕ ↦ (1 : ℝ) / (N + 1)) atTop (nhds 0) := by
    have htop : Tendsto (fun N : ℕ ↦ (N : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
    simpa only [one_div] using htop.inv_tendsto_atTop
  convert tendsto_const_nhds.sub hinv using 1
  · funext N
    rw [sum_range_inv_mul_succ]
  · norm_num

private lemma logSeries_hasSum {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasSum (fun n : ℕ ↦ x ^ (n + 1) / (n + 1)) (-Real.log (1 - x)) := by
  exact Real.hasSum_pow_div_log_of_abs_lt_one (by simpa [abs_of_pos hx.1] using hx.2)

private lemma pow_inv_mul_succ_hasSum {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasSum (fun n : ℕ ↦ x ^ (n + 1) / ((n + 1) * (n + 2)))
      (-Real.log (1 - x) -
        (1 / x) * (-Real.log (1 - x) - x)) := by
  have hlog := logSeries_hasSum hx
  have htail := (hasSum_nat_add_iff' 1).2 hlog
  have h := hlog.sub (htail.mul_left (1 / x))
  convert h using 1
  · funext n
    push_cast
    have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
    have hn2 : (n : ℝ) + 2 ≠ 0 := by positivity
    field_simp [hx.1.ne', hn1, hn2]
    ring
  · norm_num

noncomputable def topMainRawTerm (R q : ℝ) (n : ℕ) : ℝ :=
  (1 - q ^ (n + 1)) * topDn R (n + 1) /
    ((n + 1) * (n + 2))

/-- The direct summation formula behind equations (10)--(11), before the
cap substitution is simplified. -/
theorem topMainRaw_hasSum {R q : ℝ}
    (hR : R ∈ Ioo (0 : ℝ) 1) (hq : q ∈ Ioo (0 : ℝ) 1) :
    HasSum (topMainRawTerm R q)
      ((1 / q - 1) *
        (Real.log (1 - R * q) - Real.log (1 - q))) := by
  have hRq : R * q ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · exact mul_pos hR.1 hq.1
    · have h := mul_lt_mul_of_pos_right hR.2 hq.1
      linarith [hq.2]
  have hA1 := hasSum_inv_mul_succ
  have hAq := pow_inv_mul_succ_hasSum hq
  have hlogR := logSeries_hasSum hR
  have hlogRq := logSeries_hasSum hRq
  have htailR := (hasSum_nat_add_iff' 1).2 hlogR
  have htailRq := ((hasSum_nat_add_iff' 1).2 hlogRq).mul_left (1 / q)
  have h := (((hA1.sub hAq).sub hlogR).add hlogRq).add htailR |>.sub htailRq
  convert h using 1
  · funext n
    unfold topMainRawTerm
    rw [topDn_eq_closed]
    push_cast
    have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
    have hn2 : (n : ℝ) + 2 ≠ 0 := by positivity
    field_simp [hq.1.ne', hn1, hn2]
    ring
  · norm_num [Finset.sum_range_succ]
    field_simp [hq.1.ne']
    ring

lemma one_sub_topCapR_mul_q {c q : ℝ}
    (hc : c ∈ Ioo (0 : ℝ) 1) (hq : q ∈ Ioo (0 : ℝ) 1) :
    1 - topCapR c q * q =
      (1 - q) / (1 - c ^ 2 * q) := by
  have hden := (topCapDen_pos hc hq).ne'
  unfold topCapR
  field_simp [hden]
  ring

/-- On the cap, the main series is exactly the logarithmic quantity used in
the derivative lower bound. -/
theorem topMainRaw_cap_hasSum {c q : ℝ}
    (hc : c ∈ Ioo (0 : ℝ) 1) (hq : q ∈ Ioo (0 : ℝ) 1) :
    HasSum (topMainRawTerm (topCapR c q) q)
      (-(1 - q) / q * Real.log (1 - c ^ 2 * q)) := by
  have h := topMainRaw_hasSum (topCapR_mem_Ioo hc hq) hq
  convert h using 1
  have hqsub : 0 < 1 - q := sub_pos.mpr hq.2
  have hden := topCapDen_pos hc hq
  rw [one_sub_topCapR_mul_q hc hq]
  rw [Real.log_div hqsub.ne' hden.ne']
  field_simp [hq.1.ne']
  ring

end CourtadeKumar
