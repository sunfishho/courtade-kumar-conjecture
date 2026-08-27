import InformationTheory.CourtadeKumar.LRLowerFaceQ0
import InformationTheory.CourtadeKumar.LRAbelElementaryBounds

/-!
# Rational lower-face bound for the logarithmic core

This proves the elementary monotonicity and logarithm estimates used after
(M23), including `k log ((1+(1-s)k)/k) < 5/12` for `k ≤ 1/4`.
-/

open Set

namespace CourtadeKumar

noncomputable def lrLowerFaceKLog (k : ℝ) : ℝ :=
  k * Real.log (1 + 1 / k)

noncomputable def lrLowerFaceKLogDeriv (k : ℝ) : ℝ :=
  Real.log (1 + 1 / k) - 1 / (1 + k)

theorem hasDerivAt_lrLowerFaceKLog {k : ℝ} (hk : 0 < k) :
    HasDerivAt lrLowerFaceKLog (lrLowerFaceKLogDeriv k) k := by
  have hinv := (hasDerivAt_id k).inv hk.ne'
  have harg := (hasDerivAt_const k 1).add hinv
  have harg' : HasDerivAt (fun x : ℝ ↦ 1 + 1 / x)
      (-1 / k ^ 2) k := by
    simpa only [one_div, Pi.add_apply, id_eq, zero_add] using harg
  have hargPos : 0 < 1 + 1 / k := by positivity
  have hlog := (Real.hasDerivAt_log hargPos.ne').comp k harg'
  have h := (hasDerivAt_id k).mul hlog
  unfold lrLowerFaceKLog lrLowerFaceKLogDeriv
  convert h using 1 <;>
    simp only [Function.comp_apply, id_eq, one_div] <;>
    field_simp [hk.ne'] <;> ring

lemma lrLowerFaceKLogDeriv_nonneg {k : ℝ} (hk : 0 < k) :
    0 ≤ lrLowerFaceKLogDeriv k := by
  have hargPos : 0 < 1 + 1 / k := by positivity
  have hlog := Real.one_sub_inv_le_log_of_pos hargPos
  have hid : 1 - (1 + 1 / k)⁻¹ = 1 / (1 + k) := by
    field_simp [hk.ne', (by linarith : 1 + k ≠ 0)]
    ring
  unfold lrLowerFaceKLogDeriv
  linarith

theorem lrLowerFaceKLog_monotoneOn :
    MonotoneOn lrLowerFaceKLog (Ioi (0 : ℝ)) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ioi (0 : ℝ))
  · intro k hk
    exact (hasDerivAt_lrLowerFaceKLog hk).continuousAt.continuousWithinAt
  · intro k hk
    rw [interior_Ioi] at hk
    exact (hasDerivAt_lrLowerFaceKLog hk).differentiableAt
      |>.differentiableWithinAt
  · intro k hk
    rw [interior_Ioi] at hk
    rw [(hasDerivAt_lrLowerFaceKLog hk).deriv]
    exact lrLowerFaceKLogDeriv_nonneg hk

lemma lrLowerFace_log_five_lt : Real.log 5 < (5 / 3 : ℝ) := by
  have hfiveFourPos : (0 : ℝ) < 5 / 4 := by norm_num
  have hfiveFourNe : (5 / 4 : ℝ) ≠ 1 := by norm_num
  have hquarter : Real.log (5 / 4 : ℝ) < 1 / 4 := by
    have h := Real.log_lt_sub_one_of_pos hfiveFourPos hfiveFourNe
    norm_num at h ⊢
    exact h
  have hlogFour : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num,
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)]
    ring
  have hsplit : Real.log (5 : ℝ) =
      Real.log (5 / 4 : ℝ) + Real.log 4 := by
    rw [← Real.log_mul (by norm_num : (5 / 4 : ℝ) ≠ 0)
      (by norm_num : (4 : ℝ) ≠ 0)]
    norm_num
  rw [hsplit, hlogFour]
  nlinarith [Real.log_two_lt_d9]

/-- The numerical logarithm estimate used in (M23). -/
theorem lrLowerFace_k_log_ratio_lt
    {s k : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (hk : 0 < k) (hkUpper : k ≤ 1 / 4) :
    k * Real.log ((1 + (1 - s) * k) / k) < 5 / 12 := by
  have hnum : 1 + (1 - s) * k ≤ 1 + k := by
    nlinarith [mul_nonneg hs.1 hk.le]
  have harg : (1 + (1 - s) * k) / k ≤ 1 + 1 / k := by
    rw [div_le_iff₀ hk]
    field_simp [hk.ne']
    nlinarith
  have hleftPos : 0 < (1 + (1 - s) * k) / k := by
    exact div_pos (by nlinarith [mul_nonneg (sub_nonneg.mpr hs.2) hk.le]) hk
  have hlog := Real.log_le_log hleftPos harg
  have hscaled := mul_le_mul_of_nonneg_left hlog hk.le
  have hmono := lrLowerFaceKLog_monotoneOn
    (show k ∈ Ioi (0 : ℝ) from hk)
    (show (1 / 4 : ℝ) ∈ Ioi 0 by norm_num) hkUpper
  have hquarter : lrLowerFaceKLog (1 / 4 : ℝ) < 5 / 12 := by
    unfold lrLowerFaceKLog
    norm_num
    nlinarith [lrLowerFace_log_five_lt]
  have hidentify : k * Real.log (1 + 1 / k) = lrLowerFaceKLog k := rfl
  rw [hidentify] at hscaled
  exact hscaled.trans_lt (hmono.trans_lt hquarter)

/-- A fully rational specialization of (M23) on the audited lower face. -/
theorem lrLowerFacePWQ0_rational_lower
    {s k chi v : ℝ} (hs : s ∈ Ioo (0 : ℝ) (1 / 128 : ℝ))
    (hk : 0 < k) (hkUpper : k ≤ 1 / 4)
    (hchi : chi ∈ Ioo (0 : ℝ) 1)
    (hv : v ∈ Ioo (0 : ℝ) 1) :
    s * (893 / 3072 : ℝ) < lrLowerFacePWQ0 s k chi v := by
  have hsUnit : s ∈ Ioo (0 : ℝ) 1 := ⟨hs.1, hs.2.trans (by norm_num)⟩
  have hsk : s * k < 1 := by
    calc
      s * k ≤ s * (1 / 4) := mul_le_mul_of_nonneg_left hkUpper hs.1.le
      _ < 1 := by nlinarith [hs.2]
  have hpw := lrLowerFacePWQ0_lower hsUnit hk hsk hchi hv
  have hskUpper : s * k < 1 / 512 := by
    calc
      s * k ≤ s * (1 / 4) := mul_le_mul_of_nonneg_left hkUpper hs.1.le
      _ < 1 / 512 := by nlinarith [hs.2]
  have hlog := lrLowerFace_k_log_ratio_lt
    (show s ∈ Icc (0 : ℝ) 1 from ⟨hs.1.le, hsUnit.2.le⟩) hk hkUpper
  have hbracket : 893 / 1536 <
      1 - s * k - k * Real.log ((1 + (1 - s) * k) / k) := by
    norm_num at hskUpper hlog ⊢
    linarith
  have hsHalf : 0 < s / 2 := div_pos hs.1 (by norm_num)
  have hscaled := mul_lt_mul_of_pos_left hbracket hsHalf
  calc
    s * (893 / 3072 : ℝ) = (s / 2) * (893 / 1536) := by ring
    _ < (s / 2) *
        (1 - s * k - k * Real.log ((1 + (1 - s) * k) / k)) := hscaled
    _ ≤ lrLowerFacePWQ0 s k chi v := hpw

end CourtadeKumar
