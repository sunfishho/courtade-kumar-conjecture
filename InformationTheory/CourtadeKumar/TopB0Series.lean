import InformationTheory.CourtadeKumar.TopCapPrimitive

/-! Exact positive series for the simplified common primitive `B₀`. -/

open Set
open scoped BigOperators

namespace CourtadeKumar

/-- The derivative series
`Psi'(R) = sum R^n / (2(2n+1))`. -/
theorem topPsiDeriv_hasSum {R : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1) :
    HasSum (fun n : ℕ ↦ R ^ n / (2 * (2 * n + 1))) (topPsiDeriv R) := by
  let x := Real.sqrt R
  let f : ℕ → ℝ := fun n ↦
    (x ^ (n + 1) - (-x) ^ (n + 1)) / (n + 1)
  have hx0 : 0 < x := by simpa [x] using Real.sqrt_pos.2 hR.1
  have hx1 : x < 1 := by
    dsimp [x]
    simpa using (Real.sqrt_lt_sqrt_iff hR.1.le).2 hR.2
  have habs : |x| < 1 := by simpa [abs_of_pos hx0] using hx1
  have hpos := Real.hasSum_pow_div_log_of_abs_lt_one habs
  have hneg := Real.hasSum_pow_div_log_of_abs_lt_one
    (x := -x) (by simpa using habs)
  have hfull : HasSum f (2 * Real.artanh x) := by
    have hsub := hpos.sub hneg
    unfold f
    convert hsub using 1
    · funext n
      ring
    · have hxp : 0 < 1 + x := by linarith
      have hxm : 0 < 1 - x := by linarith
      rw [Real.artanh_eq_half_log ⟨by linarith, hx1.le⟩]
      rw [Real.log_div hxp.ne' hxm.ne']
      ring
  have heSumm : Summable (fun n : ℕ ↦ f (2 * n)) :=
    hfull.summable.comp_injective (mul_right_injective₀ (by norm_num : (2 : ℕ) ≠ 0))
  have ho : HasSum (fun n : ℕ ↦ f (2 * n + 1)) 0 := by
    convert (hasSum_zero : HasSum (fun _ : ℕ ↦ (0 : ℝ)) 0) using 1
    funext n
    unfold f
    have heven : Even (2 * n + 1 + 1 : ℕ) := ⟨n + 1, by omega⟩
    rw [Even.neg_pow heven]
    ring
  have he := heSumm.hasSum
  have heq : (∑' n : ℕ, f (2 * n)) = 2 * Real.artanh x := by
    have hcombined := he.even_add_odd ho
    simpa using hcombined.unique hfull
  have hscaled := (heq ▸ he).mul_left (1 / (4 * x))
  unfold topPsiDeriv
  convert hscaled using 1
  · funext n
    unfold f
    have hodd : Odd (2 * n + 1) := odd_two_mul_add_one n
    rw [Odd.neg_pow hodd]
    have hxSq : x ^ 2 = R := by simpa [x] using Real.sq_sqrt hR.1.le
    have hpow : x ^ (2 * n) = R ^ n := by
      rw [pow_mul, hxSq]
    rw [pow_succ, hpow]
    push_cast
    field_simp [hx0.ne']
    ring
  · dsimp [x] at hx0 ⊢
    field_simp [hx0.ne']
    ring

noncomputable def topWPrimitive (R : ℝ) : ℝ :=
  Real.log 2 - topPhi (Real.sqrt R) - (1 - R) * topPsiDeriv R

noncomputable def topKPrimitive (R q : ℝ) : ℝ :=
  (topPhi (Real.sqrt q) - topPhi (Real.sqrt (R * q))) / q -
    (1 - R) * topPsiDeriv (R * q)

noncomputable def topB0Analytic (R q : ℝ) : ℝ :=
  topWPrimitive R - topKPrimitive R q

lemma topChannelWDeriv_scaled {R : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1) :
    (1 - R) ^ 2 * topChannelWDeriv R = topWPrimitive R := by
  have hs : 1 - R ≠ 0 := by linarith [hR.2]
  unfold topChannelWDeriv topWPrimitive
  field_simp [hs]
  ring

lemma topChannelKDeriv_scaled {R q : ℝ}
    (hR : R ∈ Ioo (0 : ℝ) 1) (hq : q ∈ Ioo (0 : ℝ) 1) :
    (1 - R) ^ 2 * topChannelKDeriv R q = topKPrimitive R q := by
  have hs : 1 - R ≠ 0 := by linarith [hR.2]
  have hqne := hq.1.ne'
  have hsqrtMul : Real.sqrt (R * q) = Real.sqrt R * Real.sqrt q := by
    rw [Real.sqrt_mul hR.1.le]
  have hsqrtRPos := Real.sqrt_pos.2 hR.1
  have hsqrtqPos := Real.sqrt_pos.2 hq.1
  have hA : q * topPsiDeriv (R * q) =
      Real.artanh (Real.sqrt R * Real.sqrt q) *
        (Real.sqrt q / (2 * Real.sqrt R)) := by
    unfold topPsiDeriv
    rw [hsqrtMul]
    field_simp [hsqrtRPos.ne', hsqrtqPos.ne']
    rw [Real.sq_sqrt hq.1.le]
  unfold topChannelKDeriv topKPrimitive
  dsimp only
  rw [← hA, hsqrtMul]
  field_simp [hs, hqne]
  ring

lemma topCapB0_eq_analytic {c q : ℝ}
    (hc : c ∈ Ioo (0 : ℝ) 1) (hq : q ∈ Ioo (0 : ℝ) 1) :
    topCapB0 c q = topB0Analytic (topCapR c q) q := by
  have hR := topCapR_mem_Ioo hc hq
  unfold topCapB0 topB0Analytic
  dsimp only
  rw [mul_sub, topChannelWDeriv_scaled hR,
    topChannelKDeriv_scaled hR hq]

noncomputable def topB0Term (R q : ℝ) (n : ℕ) : ℝ :=
  ((1 : ℝ) /
      (2 * (n + 1) * (2 * (n + 1) - 1))) *
    (1 - q ^ n) * topDn R n

/-- Exact series identity (8) from the full-tail derivative certificate. -/
theorem topB0Analytic_hasSum {R q : ℝ}
    (hR : R ∈ Ioo (0 : ℝ) 1) (hq : q ∈ Ioo (0 : ℝ) 1) :
    HasSum (topB0Term R q) (topB0Analytic R q) := by
  have hRq : R * q ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · exact mul_pos hR.1 hq.1
    · have h := mul_lt_mul_of_pos_right hR.2 hq.1
      linarith [hq.2]
  have hL := top_hasSum_phiCoefficients
  have hPsiR := topPhi_sqrt_hasSum hR
  have hPsiq := topPhi_sqrt_hasSum hq
  have hPsiRq := topPhi_sqrt_hasSum hRq
  have hAR := topPsiDeriv_hasSum hR
  have hARq := topPsiDeriv_hasSum hRq
  have hW := (hL.sub hPsiR).sub (hAR.mul_left (1 - R))
  have hK := ((hPsiq.sub hPsiRq).mul_left (1 / q)).sub
    (hARq.mul_left (1 - R))
  have hB := hW.sub hK
  unfold topB0Analytic topWPrimitive topKPrimitive
  convert hB using 1
  · funext n
    unfold topB0Term
    rw [topDn_eq_closed]
    push_cast
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
    have hnodd : 2 * ((n : ℝ) + 1) - 1 ≠ 0 := by nlinarith
    field_simp [hq.1.ne', hn1, hnodd]
    ring
  · ring

theorem topCapB0_hasSum {c q : ℝ}
    (hc : c ∈ Ioo (0 : ℝ) 1) (hq : q ∈ Ioo (0 : ℝ) 1) :
    HasSum (topB0Term (topCapR c q) q) (topCapB0 c q) := by
  rw [topCapB0_eq_analytic hc hq]
  exact topB0Analytic_hasSum (topCapR_mem_Ioo hc hq) hq

end CourtadeKumar
