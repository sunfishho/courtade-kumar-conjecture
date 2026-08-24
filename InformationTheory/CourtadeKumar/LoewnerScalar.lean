import InformationTheory.CourtadeKumar.RadialChordSlope

/-! Scalar inequalities in the two-by-two Loewner certificate. -/

open Set

namespace CourtadeKumar

noncomputable def loewnerY (p tau : ℝ) : ℝ :=
  (1 - p) ^ 2 - p ^ 2 * tau

noncomputable def loewnerEll (p tau : ℝ) : ℝ :=
  -Real.log (loewnerY p tau)

noncomputable def loewnerDetReserve (p tau : ℝ) : ℝ :=
  loewnerY p tau * loewnerEll p tau *
      ((1 - p) * loewnerEll p tau - p) +
    p ^ 3 * tau * (1 - tau) * (1 - loewnerEll p tau)

noncomputable def loewnerX (p tau : ℝ) : ℝ :=
  p ^ 2 * (1 - tau)

noncomputable def loewnerZ (p tau : ℝ) : ℝ :=
  p * (1 - p) - p ^ 2 * tau

noncomputable def loewnerQ (p tau : ℝ) : ℝ :=
  p ^ 2 * (1 - tau) * (1 - p * (1 + tau))

noncomputable def loewnerC (p tau : ℝ) : ℝ :=
  (1 - 2 * p) * loewnerY p tau + loewnerQ p tau

noncomputable def loewnerR (p tau : ℝ) : ℝ :=
  1 / loewnerX p tau + 1 / loewnerY p tau -
    1 / (loewnerY p tau * loewnerEll p tau)

noncomputable def loewnerLeadingReserve (p tau : ℝ) : ℝ :=
  loewnerR p tau * loewnerZ p tau - 1

theorem loewnerY_mem_Ioo
    {p tau : ℝ}
    (hp : p ∈ Ioc (0 : ℝ) (1 / 2 : ℝ))
    (htau : tau ∈ Ico (0 : ℝ) 1) :
    loewnerY p tau ∈ Ioo (0 : ℝ) 1 := by
  unfold loewnerY
  constructor
  · have hstrict : 0 < p ^ 2 * (1 - tau) :=
      mul_pos (sq_pos_of_pos hp.1) (sub_pos.2 htau.2)
    rw [show (1 - p) ^ 2 - p ^ 2 * tau =
      (1 - 2 * p) + p ^ 2 * (1 - tau) by ring]
    exact add_pos_of_nonneg_of_pos (by linarith [hp.2]) hstrict
  · have hsub : 0 ≤ p ^ 2 * tau := mul_nonneg (sq_nonneg p) htau.1
    have hsquare : (1 - p) ^ 2 < 1 := by
      have htwo : 0 < 2 - p := by linarith [hp.2]
      nlinarith [mul_pos hp.1 htwo]
    exact (sub_le_self _ hsub).trans_lt hsquare

theorem loewnerEll_ge_two_mul
    {p tau : ℝ}
    (hp : p ∈ Ioc (0 : ℝ) (1 / 2 : ℝ))
    (htau : tau ∈ Ico (0 : ℝ) 1) :
    2 * p ≤ loewnerEll p tau := by
  have hY := loewnerY_mem_Ioo hp htau
  have hp1 : 0 < 1 - p := by linarith [hp.2]
  have hYle : loewnerY p tau ≤ (1 - p) ^ 2 := by
    unfold loewnerY
    exact sub_le_self _ (mul_nonneg (sq_nonneg p) htau.1)
  have hlogY : Real.log (loewnerY p tau) ≤ Real.log ((1 - p) ^ 2) :=
    Real.log_le_log hY.1 hYle
  rw [Real.log_pow] at hlogY
  have hlogp : Real.log (1 - p) ≤ -p := by
    have := Real.log_le_sub_one_of_pos hp1
    linarith
  unfold loewnerEll
  calc
    2 * p ≤ -2 * Real.log (1 - p) := by nlinarith
    _ ≤ -Real.log (loewnerY p tau) := by
      convert neg_le_neg hlogY using 1 <;> ring

theorem loewnerMainBracket_nonneg
    {p tau : ℝ}
    (hp : p ∈ Ioc (0 : ℝ) (1 / 2 : ℝ))
    (htau : tau ∈ Ico (0 : ℝ) 1) :
    0 ≤ (1 - p) * loewnerEll p tau - p := by
  have hell := loewnerEll_ge_two_mul hp htau
  have h1p : 0 ≤ 1 - p := by linarith [hp.2]
  have hmul := mul_le_mul_of_nonneg_left hell h1p
  have h12 : 0 ≤ 1 - 2 * p := by linarith [hp.2]
  have hbase : p ≤ (1 - p) * (2 * p) := by
    nlinarith [mul_nonneg hp.1.le h12]
  exact sub_nonneg.2 (hbase.trans hmul)

theorem loewnerMainBracket_pos
    {p tau : ℝ}
    (hp : p ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (htau : tau ∈ Ico (0 : ℝ) 1) :
    0 < (1 - p) * loewnerEll p tau - p := by
  have hell := loewnerEll_ge_two_mul ⟨hp.1, hp.2.le⟩ htau
  have h1p : 0 ≤ 1 - p := by linarith [hp.2]
  have hmul := mul_le_mul_of_nonneg_left hell h1p
  have hbase : p < (1 - p) * (2 * p) := by
    nlinarith [mul_pos hp.1 (sub_pos.2 (by linarith [hp.2] : 0 < 1 - 2 * p))]
  exact sub_pos.2 (hbase.trans_le hmul)

theorem loewnerBraceBase_nonneg
    {p tau : ℝ}
    (hp : p ∈ Ioc (0 : ℝ) (1 / 2 : ℝ))
    (htau : tau ∈ Ico (0 : ℝ) 1) :
    0 ≤ loewnerY p tau * (1 - p) -
      p ^ 3 * tau * (1 - tau) := by
  have h1tau : 0 ≤ 1 - tau := (sub_nonneg.2 htau.2.le)
  have hlast : 0 ≤ 1 - p * (1 + tau) := by
    have : p * (1 + tau) ≤ (1 / 2 : ℝ) * 2 :=
      mul_le_mul hp.2 (by linarith [htau.2]) (by linarith [htau.1]) (by norm_num)
    norm_num at this ⊢
    linarith
  have hdecomp : loewnerY p tau * (1 - p) -
      p ^ 3 * tau * (1 - tau) =
      (1 - p) * (1 - 2 * p) +
        p ^ 2 * (1 - tau) * (1 - p * (1 + tau)) := by
    unfold loewnerY
    ring
  rw [hdecomp]
  exact add_nonneg
    (mul_nonneg (by linarith [hp.2]) (by linarith [hp.2]))
    (mul_nonneg (mul_nonneg (sq_nonneg p) h1tau) hlast)

/-- Determinant reserve (15) in the manuscript's Loewner proof. -/
theorem loewnerDetReserve_nonneg
    {p tau : ℝ}
    (hp : p ∈ Ioc (0 : ℝ) (1 / 2 : ℝ))
    (htau : tau ∈ Ico (0 : ℝ) 1) :
    0 ≤ loewnerDetReserve p tau := by
  have hY := loewnerY_mem_Ioo hp htau
  have hellLower := loewnerEll_ge_two_mul hp htau
  have hell0 : 0 ≤ loewnerEll p tau := (mul_nonneg (by norm_num) hp.1.le).trans hellLower
  have hmain := loewnerMainBracket_nonneg hp htau
  by_cases hell1 : loewnerEll p tau ≤ 1
  · unfold loewnerDetReserve
    exact add_nonneg
      (mul_nonneg (mul_nonneg hY.1.le hell0) hmain)
      (mul_nonneg
        (mul_nonneg (mul_nonneg (pow_nonneg hp.1.le 3) htau.1)
          (sub_nonneg.2 htau.2.le))
        (sub_nonneg.2 hell1))
  · have hell1' : 1 ≤ loewnerEll p tau := le_of_not_ge hell1
    have hbase := loewnerBraceBase_nonneg hp htau
    have hY1p : 0 ≤ loewnerY p tau * (1 - p) :=
      mul_nonneg hY.1.le (by linarith [hp.2])
    have hbrace : 0 ≤ loewnerY p tau * loewnerEll p tau * (1 - p) -
        p ^ 3 * tau * (1 - tau) := by
      have hscale : loewnerY p tau * (1 - p) ≤
          loewnerY p tau * loewnerEll p tau * (1 - p) := by
        calc
          loewnerY p tau * (1 - p) =
              loewnerY p tau * (1 - p) * 1 := by ring
          _ ≤ loewnerY p tau * (1 - p) * loewnerEll p tau :=
            mul_le_mul_of_nonneg_left hell1' hY1p
          _ = loewnerY p tau * loewnerEll p tau * (1 - p) := by ring
      linarith
    have hrewrite : loewnerDetReserve p tau =
        loewnerY p tau * loewnerEll p tau * (1 - 2 * p) +
          (loewnerEll p tau - 1) *
            (loewnerY p tau * loewnerEll p tau * (1 - p) -
              p ^ 3 * tau * (1 - tau)) := by
      unfold loewnerDetReserve
      ring
    rw [hrewrite]
    exact add_nonneg
      (mul_nonneg (mul_nonneg hY.1.le hell0) (by linarith [hp.2]))
      (mul_nonneg (sub_nonneg.2 hell1') hbrace)

/-- The determinant reserve is strict below the centered boundary `p = 1/2`. -/
theorem loewnerDetReserve_pos
    {p tau : ℝ}
    (hp : p ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (htau : tau ∈ Ico (0 : ℝ) 1) :
    0 < loewnerDetReserve p tau := by
  let hp' : p ∈ Ioc (0 : ℝ) (1 / 2 : ℝ) := ⟨hp.1, hp.2.le⟩
  have hY := loewnerY_mem_Ioo hp' htau
  have hellLower := loewnerEll_ge_two_mul hp' htau
  have hell0 : 0 < loewnerEll p tau :=
    (mul_pos (by norm_num) hp.1).trans_le hellLower
  have hmain := loewnerMainBracket_pos hp htau
  by_cases hell1 : loewnerEll p tau ≤ 1
  · unfold loewnerDetReserve
    exact add_pos_of_pos_of_nonneg
      (mul_pos (mul_pos hY.1 hell0) hmain)
      (mul_nonneg
        (mul_nonneg (mul_nonneg (pow_nonneg hp.1.le 3) htau.1)
          (sub_nonneg.2 htau.2.le))
        (sub_nonneg.2 hell1))
  · have hell1' : 1 ≤ loewnerEll p tau := le_of_not_ge hell1
    have hbase := loewnerBraceBase_nonneg hp' htau
    have hY1p : 0 ≤ loewnerY p tau * (1 - p) :=
      mul_nonneg hY.1.le (by linarith [hp.2])
    have hbrace : 0 ≤ loewnerY p tau * loewnerEll p tau * (1 - p) -
        p ^ 3 * tau * (1 - tau) := by
      have hscale : loewnerY p tau * (1 - p) ≤
          loewnerY p tau * loewnerEll p tau * (1 - p) := by
        calc
          loewnerY p tau * (1 - p) =
              loewnerY p tau * (1 - p) * 1 := by ring
          _ ≤ loewnerY p tau * (1 - p) * loewnerEll p tau :=
            mul_le_mul_of_nonneg_left hell1' hY1p
          _ = loewnerY p tau * loewnerEll p tau * (1 - p) := by ring
      linarith
    have hrewrite : loewnerDetReserve p tau =
        loewnerY p tau * loewnerEll p tau * (1 - 2 * p) +
          (loewnerEll p tau - 1) *
            (loewnerY p tau * loewnerEll p tau * (1 - p) -
              p ^ 3 * tau * (1 - tau)) := by
      unfold loewnerDetReserve
      ring
    rw [hrewrite]
    exact add_pos_of_pos_of_nonneg
      (mul_pos (mul_pos hY.1 hell0) (by linarith [hp.2]))
      (mul_nonneg (sub_nonneg.2 hell1') hbrace)

theorem loewnerX_pos
    {p tau : ℝ}
    (hp : p ∈ Ioc (0 : ℝ) (1 / 2 : ℝ))
    (htau : tau ∈ Ico (0 : ℝ) 1) :
    0 < loewnerX p tau := by
  unfold loewnerX
  exact mul_pos (sq_pos_of_pos hp.1) (sub_pos.2 htau.2)

theorem loewnerQ_pos
    {p tau : ℝ}
    (hp : p ∈ Ioc (0 : ℝ) (1 / 2 : ℝ))
    (htau : tau ∈ Ico (0 : ℝ) 1) :
    0 < loewnerQ p tau := by
  have hlast : 0 < 1 - p * (1 + tau) := by
    have hnonneg : 0 ≤ 1 + tau := by linarith [htau.1]
    have hle : p * (1 + tau) ≤ (1 / 2 : ℝ) * (1 + tau) :=
      mul_le_mul_of_nonneg_right hp.2 hnonneg
    have hstrict : p * (1 + tau) < 1 := by
      nlinarith [hle, htau.2]
    exact sub_pos.2 hstrict
  unfold loewnerQ
  exact mul_pos (mul_pos (sq_pos_of_pos hp.1) (sub_pos.2 htau.2)) hlast

theorem loewnerC_pos
    {p tau : ℝ}
    (hp : p ∈ Ioc (0 : ℝ) (1 / 2 : ℝ))
    (htau : tau ∈ Ico (0 : ℝ) 1) :
    0 < loewnerC p tau := by
  unfold loewnerC
  exact add_pos_of_nonneg_of_pos
    (mul_nonneg (by linarith [hp.2]) (loewnerY_mem_Ioo hp htau).1.le)
    (loewnerQ_pos hp htau)

theorem loewner_two_mul_p_C_ge_Q
    {p tau : ℝ}
    (hp : p ∈ Ioc (0 : ℝ) (1 / 2 : ℝ))
    (htau : tau ∈ Ico (0 : ℝ) 1) :
    loewnerQ p tau ≤ 2 * p * loewnerC p tau := by
  have hfactor₁ : 2 * p - 1 ≤ 0 := by linarith [hp.2]
  have hfactor₂ : 0 ≤ p * tau - p + 1 := by
    nlinarith [mul_nonneg hp.1.le (sub_nonneg.2 htau.1)]
  have hfactor₃ : p * tau + 3 * p - 2 ≤ 0 := by
    have hptau : p * tau ≤ p := by
      have hptau' : p * tau ≤ p * 1 :=
        mul_le_mul_of_nonneg_left htau.2.le hp.1.le
      simpa using hptau'
    linarith [hp.2]
  have hprod : 0 ≤ p * (2 * p - 1) *
      (p * tau - p + 1) * (p * tau + 3 * p - 2) := by
    have hneg : 0 ≤ (2 * p - 1) * (p * tau + 3 * p - 2) :=
      mul_nonneg_of_nonpos_of_nonpos hfactor₁ hfactor₃
    nlinarith [mul_nonneg (mul_nonneg hp.1.le hfactor₂) hneg]
  have hid : 2 * p * loewnerC p tau - loewnerQ p tau =
      p * (2 * p - 1) * (p * tau - p + 1) *
        (p * tau + 3 * p - 2) := by
    unfold loewnerC loewnerQ loewnerY
    ring
  rw [← hid] at hprod
  linarith

theorem loewner_ell_C_ge_Q
    {p tau : ℝ}
    (hp : p ∈ Ioc (0 : ℝ) (1 / 2 : ℝ))
    (htau : tau ∈ Ico (0 : ℝ) 1) :
    loewnerQ p tau ≤ loewnerEll p tau * loewnerC p tau := by
  have hell := loewnerEll_ge_two_mul hp htau
  have hC := (loewnerC_pos hp htau).le
  exact (loewner_two_mul_p_C_ge_Q hp htau).trans
    (mul_le_mul_of_nonneg_right hell hC)

theorem loewnerLeadingReserve_eq
    {p tau : ℝ}
    (hp : p ∈ Ioc (0 : ℝ) (1 / 2 : ℝ))
    (htau : tau ∈ Ico (0 : ℝ) 1) :
    loewnerLeadingReserve p tau =
      (loewnerEll p tau * loewnerC p tau - loewnerQ p tau) /
        (loewnerEll p tau * p * (1 - tau) * loewnerY p tau) := by
  have hX := loewnerX_pos hp htau
  have hY := (loewnerY_mem_Ioo hp htau).1
  have hellLower := loewnerEll_ge_two_mul hp htau
  have hell : 0 < loewnerEll p tau :=
    (mul_pos (by norm_num) hp.1).trans_le hellLower
  unfold loewnerLeadingReserve loewnerR
  field_simp [hX.ne', hY.ne', hell.ne', hp.1.ne', (sub_pos.2 htau.2).ne']
  unfold loewnerX loewnerZ loewnerC loewnerQ loewnerY
  ring

theorem loewnerLeadingReserve_nonneg
    {p tau : ℝ}
    (hp : p ∈ Ioc (0 : ℝ) (1 / 2 : ℝ))
    (htau : tau ∈ Ico (0 : ℝ) 1) :
    0 ≤ loewnerLeadingReserve p tau := by
  rw [loewnerLeadingReserve_eq hp htau]
  apply div_nonneg
  · exact sub_nonneg.2 (loewner_ell_C_ge_Q hp htau)
  · have h2p : 0 ≤ 2 * p := mul_nonneg (by norm_num) hp.1.le
    have hell0 : 0 ≤ loewnerEll p tau :=
      h2p.trans (loewnerEll_ge_two_mul hp htau)
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg hell0 hp.1.le)
        (sub_nonneg.2 htau.2.le))
      (loewnerY_mem_Ioo hp htau).1.le

end CourtadeKumar
