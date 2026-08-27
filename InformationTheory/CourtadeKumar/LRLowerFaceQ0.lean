import InformationTheory.CourtadeKumar.LRCertificateOmega

/-!
# Logarithmic core for the small-`k` midpoint face

This introduces the manuscript decomposition
`Q(y) = q₀(y) + r₀(y)` and proves the exact closed form (M22) for the
`q₀` contribution to the noise kernel.  The identities are stated on the
open physical interval, which is the region used by the analytic lower-face
argument.
-/

open Set

namespace CourtadeKumar

noncomputable def lrLowerFaceQ0 (y : ℝ) : ℝ :=
  y / 4 * (Real.log (4 / y) + 1)

noncomputable def lrLowerFaceQ0Prime (y : ℝ) : ℝ :=
  Real.log (4 / y) / 4

noncomputable def lrLowerFaceQ0Second (y : ℝ) : ℝ :=
  -1 / (4 * y)

noncomputable def lrLowerFaceR0 (y : ℝ) : ℝ :=
  lrCertificateQ y - lrLowerFaceQ0 y

noncomputable def lrLowerFaceOmegaQ0 (s y : ℝ) : ℝ :=
  lrLowerFaceQ0 (lrCertificateB s y) - lrLowerFaceQ0 y -
    s * (1 - y) * lrLowerFaceQ0Prime (lrCertificateB s y)

noncomputable def lrLowerFaceOmegaQ0Deriv (s y : ℝ) : ℝ :=
  lrLowerFaceQ0Prime (lrCertificateB s y) - lrLowerFaceQ0Prime y -
    s * (1 - s) * (1 - y) *
      lrLowerFaceQ0Second (lrCertificateB s y)

noncomputable def lrLowerFacePWQ0 (s k chi v : ℝ) : ℝ :=
  lrLowerFaceOmegaQ0 s (chi * (s * k)) +
    lrLowerFaceOmegaQ0 s (s * k) / v

theorem hasDerivAt_lrLowerFaceQ0 {y : ℝ} (hy : 0 < y) :
    HasDerivAt lrLowerFaceQ0 (lrLowerFaceQ0Prime y) y := by
  have hyNe : y ≠ 0 := hy.ne'
  have hquot : HasDerivAt (fun z : ℝ ↦ 4 / z) (-4 / y ^ 2) y := by
    convert (hasDerivAt_const y (4 : ℝ)).div (hasDerivAt_id y) hyNe using 1 <;>
      simp only [id_eq] <;> field_simp [hyNe] <;> ring
  have hquotNe : 4 / y ≠ 0 := div_ne_zero (by norm_num) hyNe
  have hlog := (Real.hasDerivAt_log hquotNe).comp y hquot
  have hfactor := hlog.add_const 1
  have hprod := ((hasDerivAt_id y).div_const 4).mul hfactor
  unfold lrLowerFaceQ0 lrLowerFaceQ0Prime
  convert hprod using 1
  simp only [Function.comp_apply, id_eq, div_eq_mul_inv]
  field_simp [hyNe]
  ring

theorem hasDerivAt_lrLowerFaceQ0Prime {y : ℝ} (hy : 0 < y) :
    HasDerivAt lrLowerFaceQ0Prime (lrLowerFaceQ0Second y) y := by
  have hyNe : y ≠ 0 := hy.ne'
  have hquot : HasDerivAt (fun z : ℝ ↦ 4 / z) (-4 / y ^ 2) y := by
    convert (hasDerivAt_const y (4 : ℝ)).div (hasDerivAt_id y) hyNe using 1 <;>
      simp only [id_eq] <;> field_simp [hyNe] <;> ring
  have hquotNe : 4 / y ≠ 0 := div_ne_zero (by norm_num) hyNe
  have hlog := (Real.hasDerivAt_log hquotNe).comp y hquot
  have hscaled := hlog.div_const 4
  unfold lrLowerFaceQ0Prime lrLowerFaceQ0Second
  convert hscaled using 1
  simp only [Function.comp_apply, id_eq, div_eq_mul_inv]
  field_simp [hyNe]

theorem hasDerivAt_lrLowerFaceOmegaQ0
    {s y : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1)
    (hy : y ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (lrLowerFaceOmegaQ0 s)
      (lrLowerFaceOmegaQ0Deriv s y) y := by
  have hbMem := lrCertificateB_mem_Ioo hs hy
  have hb : HasDerivAt (lrCertificateB s) (1 - s) y := by
    unfold lrCertificateB
    convert (hasDerivAt_const y s).add
      ((hasDerivAt_id y).const_mul (1 - s)) using 1
    ring
  have hqb := (hasDerivAt_lrLowerFaceQ0 hbMem.1).comp y hb
  have hqy := hasDerivAt_lrLowerFaceQ0 hy.1
  have hqpb := (hasDerivAt_lrLowerFaceQ0Prime hbMem.1).comp y hb
  have honeMinusY := (hasDerivAt_const y 1).sub (hasDerivAt_id y)
  have hfactor := ((hasDerivAt_const y s).mul honeMinusY).mul hqpb
  have h := (hqb.sub hqy).sub hfactor
  unfold lrLowerFaceOmegaQ0 lrLowerFaceOmegaQ0Deriv
  convert h using 1 <;>
    simp only [Pi.sub_apply, Pi.mul_apply, Function.comp_apply, id_eq] <;> ring

lemma lrLowerFaceQ0Prime_sub
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    lrLowerFaceQ0Prime a - lrLowerFaceQ0Prime b =
      Real.log (b / a) / 4 := by
  unfold lrLowerFaceQ0Prime
  rw [Real.log_div (by norm_num : (4 : ℝ) ≠ 0) ha.ne',
    Real.log_div (by norm_num : (4 : ℝ) ≠ 0) hb.ne',
    Real.log_div hb.ne' ha.ne']
  ring

/-- Manuscript (M22): exact logarithmic-core noise identity. -/
theorem lrLowerFaceOmegaQ0_eq
    {s y : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1)
    (hy : y ∈ Ioo (0 : ℝ) 1) :
    lrLowerFaceOmegaQ0 s y =
      (1 / 4 : ℝ) *
        (s * (1 - y) + y * Real.log (y / lrCertificateB s y)) := by
  have hb := lrCertificateB_mem_Ioo hs hy
  have h4 : (4 : ℝ) ≠ 0 := by norm_num
  have hyNe := hy.1.ne'
  have hbNe := hb.1.ne'
  unfold lrLowerFaceOmegaQ0 lrLowerFaceQ0 lrLowerFaceQ0Prime
  rw [Real.log_div h4 hbNe, Real.log_div h4 hyNe,
    Real.log_div hyNe hbNe]
  unfold lrCertificateB
  ring

lemma lrLowerFaceB_sub (s y : ℝ) :
    lrCertificateB s y - y = s * (1 - y) := by
  unfold lrCertificateB
  ring

lemma lrLowerFace_y_div_B
    {s y : ℝ} (hb : lrCertificateB s y ≠ 0) :
    y / lrCertificateB s y =
      1 - s * (1 - y) / lrCertificateB s y := by
  have hid : y = lrCertificateB s y - s * (1 - y) := by
    linarith [lrLowerFaceB_sub s y]
  calc
    y / lrCertificateB s y =
        (lrCertificateB s y - s * (1 - y)) /
          lrCertificateB s y :=
      congrArg (fun z : ℝ ↦ z / lrCertificateB s y) hid
    _ = 1 - s * (1 - y) / lrCertificateB s y := by
      field_simp [hb]

lemma lrLowerFaceOmegaQ0Deriv_eq
    {s y : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1)
    (hy : y ∈ Ioo (0 : ℝ) 1) :
    lrLowerFaceOmegaQ0Deriv s y =
      (Real.log (y / lrCertificateB s y) +
        (1 - s) * (s * (1 - y) / lrCertificateB s y)) / 4 := by
  have hb := lrCertificateB_mem_Ioo hs hy
  unfold lrLowerFaceOmegaQ0Deriv lrLowerFaceQ0Second
  rw [lrLowerFaceQ0Prime_sub hb.1 hy.1]
  field_simp [hb.1.ne']
  ring

lemma lrLowerFaceOmegaQ0Deriv_nonpos
    {s y : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1)
    (hy : y ∈ Ioo (0 : ℝ) 1) :
    lrLowerFaceOmegaQ0Deriv s y ≤ 0 := by
  have hb := lrCertificateB_mem_Ioo hs hy
  let u := s * (1 - y) / lrCertificateB s y
  have huPos : 0 < u := by
    unfold u
    exact div_pos (mul_pos hs.1 (sub_pos.mpr hy.2)) hb.1
  have huLt : u < 1 := by
    unfold u
    rw [div_lt_one hb.1]
    linarith [lrLowerFaceB_sub s y, hy.1]
  have hratio : y / lrCertificateB s y = 1 - u := by
    unfold u
    exact lrLowerFace_y_div_B hb.1.ne'
  have hlog := Real.log_le_sub_one_of_pos (show 0 < 1 - u by linarith)
  have hlogU : Real.log (y / lrCertificateB s y) ≤ -u := by
    rw [hratio]
    linarith
  have hscaled : (1 - s) * u ≤ u := by
    nlinarith [mul_nonneg hs.1.le huPos.le]
  rw [lrLowerFaceOmegaQ0Deriv_eq hs hy]
  change (Real.log (y / lrCertificateB s y) + (1 - s) * u) / 4 ≤ 0
  linarith

/-- The logarithmic-core noise contribution decreases with its radial
argument, as used in the lower-face bound (M23). -/
theorem lrLowerFaceOmegaQ0_antitoneOn
    {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    AntitoneOn (lrLowerFaceOmegaQ0 s) (Ioo (0 : ℝ) 1) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ioo (0 : ℝ) 1)
  · intro y hy
    exact (hasDerivAt_lrLowerFaceOmegaQ0 hs hy).continuousAt.continuousWithinAt
  · intro y hy
    rw [interior_Ioo] at hy
    exact (hasDerivAt_lrLowerFaceOmegaQ0 hs hy).differentiableAt
      |>.differentiableWithinAt
  · intro y hy
    rw [interior_Ioo] at hy
    rw [(hasDerivAt_lrLowerFaceOmegaQ0 hs hy).deriv]
    exact lrLowerFaceOmegaQ0Deriv_nonpos hs hy

lemma lrLowerFaceOmegaQ0_nonneg
    {s y : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1)
    (hy : y ∈ Ioo (0 : ℝ) 1) :
    0 ≤ lrLowerFaceOmegaQ0 s y := by
  have hb := lrCertificateB_mem_Ioo hs hy
  have hratioPos : 0 < y / lrCertificateB s y := div_pos hy.1 hb.1
  have hlog := Real.one_sub_inv_le_log_of_pos hratioPos
  have hscaled := mul_le_mul_of_nonneg_left hlog hy.1.le
  have hinv : (y / lrCertificateB s y)⁻¹ =
      lrCertificateB s y / y := by
    rw [inv_div]
  rw [hinv] at hscaled
  have hleft : y * (1 - lrCertificateB s y / y) =
      -s * (1 - y) := by
    field_simp [hy.1.ne']
    linarith [lrLowerFaceB_sub s y]
  rw [hleft] at hscaled
  rw [lrLowerFaceOmegaQ0_eq hs hy]
  nlinarith

lemma lrLowerFaceOmegaQ0_sk_eq
    {s k : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1)
    (hk : 0 < k) (hsk : s * k < 1) :
    lrLowerFaceOmegaQ0 s (s * k) =
      s / 4 *
        (1 - s * k -
          k * Real.log ((1 + (1 - s) * k) / k)) := by
  have he : s * k ∈ Ioo (0 : ℝ) 1 := ⟨mul_pos hs.1 hk, hsk⟩
  have hden : 0 < 1 + (1 - s) * k := by
    have : 0 ≤ (1 - s) * k := mul_nonneg (sub_nonneg.mpr hs.2.le) hk.le
    linarith
  have hb : lrCertificateB s (s * k) =
      s * (1 + (1 - s) * k) := by
    unfold lrCertificateB
    ring
  have hratio : (s * k) / lrCertificateB s (s * k) =
      k / (1 + (1 - s) * k) := by
    rw [hb]
    field_simp [hs.1.ne', hden.ne']
  have hlog :
      Real.log (k / (1 + (1 - s) * k)) =
        -Real.log ((1 + (1 - s) * k) / k) := by
    rw [Real.log_div hk.ne' hden.ne', Real.log_div hden.ne' hk.ne']
    ring
  rw [lrLowerFaceOmegaQ0_eq hs he, hratio, hlog]
  ring

/-- Manuscript (M23), before inserting the numerical bound on
`k log (1 + 1/k)`. -/
theorem lrLowerFacePWQ0_lower
    {s k chi v : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1)
    (hk : 0 < k) (hsk : s * k < 1)
    (hchi : chi ∈ Ioo (0 : ℝ) 1)
    (hv : v ∈ Ioo (0 : ℝ) 1) :
    s / 2 *
        (1 - s * k -
          k * Real.log ((1 + (1 - s) * k) / k)) ≤
      lrLowerFacePWQ0 s k chi v := by
  have he : s * k ∈ Ioo (0 : ℝ) 1 := ⟨mul_pos hs.1 hk, hsk⟩
  have hchie : chi * (s * k) ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · exact mul_pos hchi.1 he.1
    · exact (mul_lt_of_lt_one_left he.1 hchi.2).trans he.2
  have hchieLe : chi * (s * k) ≤ s * k :=
    mul_le_of_le_one_left he.1.le hchi.2.le
  have hfirst := lrLowerFaceOmegaQ0_antitoneOn hs hchie he hchieLe
  have homega := lrLowerFaceOmegaQ0_nonneg hs he
  have hinv : 1 ≤ 1 / v := by
    rw [le_div_iff₀ hv.1]
    simpa using hv.2.le
  have hsecond : lrLowerFaceOmegaQ0 s (s * k) ≤
      lrLowerFaceOmegaQ0 s (s * k) / v := by
    have hmul := mul_le_mul_of_nonneg_right hinv homega
    convert hmul using 1 <;> field_simp [hv.1.ne'] <;> ring
  have htwo :
      s / 2 *
          (1 - s * k -
            k * Real.log ((1 + (1 - s) * k) / k)) =
        2 * lrLowerFaceOmegaQ0 s (s * k) := by
    rw [lrLowerFaceOmegaQ0_sk_eq hs hk hsk]
    ring
  rw [htwo]
  unfold lrLowerFacePWQ0
  linarith

end CourtadeKumar
