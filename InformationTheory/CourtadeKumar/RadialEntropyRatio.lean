import InformationTheory.CourtadeKumar.CenteredEntropyRatio
import InformationTheory.CourtadeKumar.RadialEulerClosedForm
import InformationTheory.CourtadeKumar.RadialPerspectiveUnimodal

/-! Entropy per unit mass along a fixed radial ray. -/

open Filter Set
open scoped NNReal Topology

namespace CourtadeKumar

/-- Entropy per unit mass at radial shape `r` and mass coordinate `z`. -/
noncomputable def radialEntropyRatio (r z : ℝ) : ℝ :=
  radialTriangleEntropy r z / z

lemma radialTriangleEntropy_eq_nat (r z : ℝ) :
    radialTriangleEntropy r z = radialNatEntropy 1 r z / Real.log 2 := by
  unfold radialTriangleEntropy radialNatEntropy binaryEntropyBits
  ring

/-- The derivative of entropy per unit mass is the negative Euler defect. -/
theorem hasDerivAt_radialEntropyRatio
    {r z : ℝ} (hz : z ≠ 0)
    (hminus : (1 - r) * z ∈ Ioo (0 : ℝ) 1)
    (hplus : (1 + r) * z ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (radialEntropyRatio r)
      (-radialEulerDefect 1 r z / (Real.log 2 * z ^ 2)) z := by
  have hnat := hasDerivAt_radialNatEntropy
    (c := (1 : ℝ)) (r := r) (z := z)
    (by simpa using hminus) (by simpa using hplus)
  have hquot := hnat.div (hasDerivAt_id z) hz
  have hscaled := hquot.div_const (Real.log 2)
  convert hscaled using 1
  · funext w
    rw [radialEntropyRatio, radialTriangleEntropy_eq_nat]
    change radialNatEntropy 1 r w / Real.log 2 / w =
      (radialNatEntropy 1 r w / w) / Real.log 2
    ring
  · unfold radialEulerDefect
    simp only [id_eq, mul_one]
    change -(radialNatEntropy 1 r z - z * radialNatEntropyDeriv 1 r z) /
        (Real.log 2 * z ^ 2) =
      (radialNatEntropyDeriv 1 r z * z - radialNatEntropy 1 r z) /
        z ^ 2 / Real.log 2
    field_simp [hz, log_two_ne_zero]
    ring

theorem deriv_radialEntropyRatio_neg
    {r z : ℝ}
    (hr : r ∈ Ioo (0 : ℝ) 1)
    (hz : z ∈ Ioo (0 : ℝ) (1 + r)⁻¹) :
    deriv (radialEntropyRatio r) z < 0 := by
  obtain ⟨_, _, hminus, hplus⟩ :=
    radialEntropyArgs_physical (show (1 : ℝ) ∈ Icc 0 1 by simp) hr hz
  rw [(hasDerivAt_radialEntropyRatio hz.1.ne' hminus hplus).deriv]
  have hdefect : 0 < radialEulerDefect 1 r z :=
    radialEulerDefect_pos (by simpa using hminus) (by simpa using hplus)
  exact div_neg_of_neg_of_pos (neg_neg_of_pos hdefect)
    (mul_pos (Real.log_pos (by norm_num)) (sq_pos_of_pos hz.1))

/-- Entropy per unit mass strictly decreases throughout every physical
interior ray. -/
theorem strictAntiOn_radialEntropyRatio
    {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    StrictAntiOn (radialEntropyRatio r)
      (Ioo (0 : ℝ) (1 + r)⁻¹) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioo (0 : ℝ) (1 + r)⁻¹)
  · intro z hz
    obtain ⟨_, _, hminus, hplus⟩ :=
      radialEntropyArgs_physical (show (1 : ℝ) ∈ Icc 0 1 by simp) hr hz
    exact (hasDerivAt_radialEntropyRatio hz.1.ne' hminus hplus).continuousAt.continuousWithinAt
  · intro z hz
    rw [interior_Ioo] at hz
    exact deriv_radialEntropyRatio_neg hr hz

lemma radialEntropyRatio_half {r : ℝ} (hr : r ≠ 0) :
    radialEntropyRatio r (1 / 2) = 2 * r * centeredEntropyRatio r := by
  rw [radialEntropyRatio, centeredEntropyRatio_eq_radial]
  field_simp [hr]

lemma binaryEntropyBits_div_ge_negLog {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    -Real.log p / Real.log 2 ≤ binaryEntropyBits p / p := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hsecond : 0 ≤ (1 - p) * Real.log (1 - p)⁻¹ := by
    exact mul_nonneg (sub_nonneg.2 hp.2.le)
      (Real.log_nonneg ((one_le_inv₀ (by linarith [hp.2] : 0 < 1 - p)).2
        (by linarith [hp.1])))
  rw [binaryEntropyBits, Real.binEntropy, Real.log_inv p,
    Real.log_inv (1 - p)]
  calc
    -Real.log p / Real.log 2 =
        (p * (-Real.log p)) / Real.log 2 / p := by
          field_simp [hp.1.ne', hlog2.ne']
    _ ≤ (p * (-Real.log p) + (1 - p) * (-Real.log (1 - p))) /
        Real.log 2 / p := by
          have hsecond' : 0 ≤ (1 - p) * (-Real.log (1 - p)) := by
            simpa [Real.log_inv] using hsecond
          gcongr
          · exact hp.1.le
          · linarith
    _ = (p * (-Real.log p) + (1 - p) * (-Real.log (1 - p))) /
        Real.log 2 / p := rfl

theorem tendsto_binaryEntropyBits_div_zero :
    Tendsto (fun p : ℝ ↦ binaryEntropyBits p / p)
      (nhdsWithin (0 : ℝ) (Ioi 0)) atTop := by
  have hlog : Tendsto (fun p : ℝ ↦ -Real.log p / Real.log 2)
      (nhdsWithin (0 : ℝ) (Ioi 0)) atTop :=
    (tendsto_neg_atTop_iff.mpr Real.tendsto_log_nhdsGT_zero).atTop_div_const
      (Real.log_pos (by norm_num))
  refine tendsto_atTop_mono' _ ?_ hlog
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with p hp
  exact binaryEntropyBits_div_ge_negLog hp

lemma tendsto_binaryEntropyBits_scaled_div_zero
    {a : ℝ} (ha : 0 < a) :
    Tendsto (fun z : ℝ ↦ binaryEntropyBits (a * z) / (a * z))
      (nhdsWithin (0 : ℝ) (Ioi 0)) atTop := by
  have hscale : Tendsto (fun z : ℝ ↦ a * z)
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhdsWithin (0 : ℝ) (Ioi 0)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have hcont : ContinuousAt (fun z : ℝ ↦ a * z) 0 := by fun_prop
      simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with z hz
      exact mul_pos ha hz
  exact tendsto_binaryEntropyBits_div_zero.comp hscale

theorem tendsto_radialEntropyRatio_zero
    {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    Tendsto (radialEntropyRatio r)
      (nhdsWithin (0 : ℝ) (Ioi 0)) atTop := by
  let l : Filter ℝ := nhdsWithin (0 : ℝ) (Ioi 0)
  have hm := tendsto_binaryEntropyBits_scaled_div_zero (sub_pos.2 hr.2)
  have hmw : Tendsto
      (fun z : ℝ ↦ (1 - r) / 2 *
        (binaryEntropyBits ((1 - r) * z) / ((1 - r) * z))) l atTop :=
    (tendsto_const_nhds : Tendsto (fun _ : ℝ ↦ (1 - r) / 2) l
      (nhds ((1 - r) / 2))).pos_mul_atTop
        (div_pos (sub_pos.2 hr.2) (by norm_num)) hm
  refine tendsto_atTop_mono' l ?_ hmw
  have hcap0 : 0 < (1 + r)⁻¹ := inv_pos.2 (by linarith [hr.1])
  have hsmall : ∀ᶠ z in l, z < (1 + r)⁻¹ :=
    (eventually_lt_nhds hcap0).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hsmall] with z hz hzcap
  have hargplus : (1 + r) * z ∈ Icc (0 : ℝ) 1 := by
    constructor
    · exact (mul_pos (by linarith [hr.1]) hz).le
    · calc
        (1 + r) * z = z * (1 + r) := mul_comm _ _
        _ ≤ (1 + r)⁻¹ * (1 + r) :=
          mul_le_mul_of_nonneg_right hzcap.le (by linarith [hr.1])
        _ = 1 := inv_mul_cancel₀ (by linarith [hr.1] : 1 + r ≠ 0)
  have hplusNonneg : 0 ≤ binaryEntropyBits ((1 + r) * z) :=
    binaryEntropyBits_nonneg_of_mem_Icc hargplus
  have hdecomp : radialEntropyRatio r z =
      (1 - r) / 2 *
          (binaryEntropyBits ((1 - r) * z) / ((1 - r) * z)) +
        binaryEntropyBits ((1 + r) * z) / (2 * z) := by
    unfold radialEntropyRatio radialTriangleEntropy
    field_simp [(ne_of_gt (show 0 < z from hz)), (sub_pos.2 hr.2).ne']
  rw [hdecomp]
  exact le_add_of_nonneg_right
    (div_nonneg hplusNonneg (mul_nonneg (by norm_num) hz.le))

/-- Every level strictly above the centered endpoint value has a unique
single-ray mass contact before the midpoint. -/
theorem existsUnique_radialEntropyRatio_eq_before_half
    {r t : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1)
    (ht : radialEntropyRatio r (1 / 2) < t) :
    ∃! z : ℝ, z ∈ Ioo (0 : ℝ) (1 / 2) ∧
      radialEntropyRatio r z = t := by
  let l : Filter ℝ := nhdsWithin (0 : ℝ) (Ioi 0)
  have hlarge : ∀ᶠ z in l, t < radialEntropyRatio r z :=
    (tendsto_radialEntropyRatio_zero hr).eventually (eventually_gt_atTop t)
  have hsmall : ∀ᶠ z in l, z < (1 / 2 : ℝ) :=
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2)).filter_mono
      nhdsWithin_le_nhds
  have hpositive : ∀ᶠ z in l, 0 < z := self_mem_nhdsWithin
  obtain ⟨a, ha0, hahalf, hat⟩ :=
    (hpositive.and (hsmall.and hlarge)).exists
  have hhalfcap : (1 / 2 : ℝ) < (1 + r)⁻¹ := by
    rw [inv_eq_one_div, lt_div_iff₀ (by linarith [hr.1] : 0 < 1 + r)]
    nlinarith [hr.2]
  have hcont : ContinuousOn (radialEntropyRatio r) (Icc a (1 / 2)) := by
    intro z hz
    have hzphys : z ∈ Ioo (0 : ℝ) (1 + r)⁻¹ :=
      ⟨ha0.trans_le hz.1, hz.2.trans_lt hhalfcap⟩
    obtain ⟨_, _, hminus, hplus⟩ :=
      radialEntropyArgs_physical (show (1 : ℝ) ∈ Icc 0 1 by simp) hr hzphys
    exact (hasDerivAt_radialEntropyRatio hzphys.1.ne' hminus hplus).continuousAt.continuousWithinAt
  have htmem : t ∈ Icc (radialEntropyRatio r (1 / 2))
      (radialEntropyRatio r a) := ⟨ht.le, hat.le⟩
  obtain ⟨z, hzrange, hzeq⟩ :=
    intermediate_value_Icc' hahalf.le hcont htmem
  have hz0 : 0 < z := ha0.trans_le hzrange.1
  have hzhalf : z < 1 / 2 := by
    rcases hzrange.2.eq_or_lt with h | h
    · rw [h] at hzeq
      linarith
    · exact h
  refine ⟨z, ⟨⟨hz0, hzhalf⟩, hzeq⟩, ?_⟩
  intro w hw
  have hzphys : z ∈ Ioo (0 : ℝ) (1 + r)⁻¹ :=
    ⟨hz0, hzhalf.trans hhalfcap⟩
  have hwphys : w ∈ Ioo (0 : ℝ) (1 + r)⁻¹ :=
    ⟨hw.1.1, hw.1.2.trans hhalfcap⟩
  exact (strictAntiOn_radialEntropyRatio hr).injOn
    hwphys hzphys (hw.2.trans hzeq.symm)

end CourtadeKumar
