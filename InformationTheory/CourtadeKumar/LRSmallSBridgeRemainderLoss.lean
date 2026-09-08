import InformationTheory.CourtadeKumar.LRSmallSBridgeVLoss

/-!
# Entropy-remainder payment in the small-`s` bridge

This formalizes the scalar envelope and exact rational arithmetic in (M32).
The remaining connection to the full reserve is the exact additive
decomposition already stated in the manuscript.
-/

open Set

namespace CourtadeKumar

noncomputable def lrSmallSBridgeLogEnvelope (s : ℝ) : ℝ :=
  s * (Real.log (1 / s) / 2 + 2 * Real.log 2) *
    (Real.log (1 / s) + 2 * Real.log 2)

noncomputable def lrSmallSBridgeEpsilonR : ℝ := 21483 / 7475200

lemma hasDerivAt_lrSmallSBridgeLog
    {s : ℝ} (hs : 0 < s) :
    HasDerivAt (fun z : ℝ ↦ Real.log (1 / z)) (-1 / s) s := by
  have hsNe := hs.ne'
  have hquot : HasDerivAt (fun z : ℝ ↦ 1 / z) (-1 / s ^ 2) s := by
    convert (hasDerivAt_const s (1 : ℝ)).div (hasDerivAt_id s) hsNe using 1 <;>
      simp only [id_eq] <;> field_simp [hsNe] <;> ring
  have hquotNe : 1 / s ≠ 0 := div_ne_zero (by norm_num) hsNe
  have hlog := (Real.hasDerivAt_log hquotNe).comp s hquot
  convert hlog using 1
  field_simp [hsNe]

lemma hasDerivAt_lrSmallSBridgeLogEnvelope
    {s : ℝ} (hs : 0 < s) :
    let L := Real.log (1 / s)
    HasDerivAt lrSmallSBridgeLogEnvelope
      ((L / 2 + 2 * Real.log 2) * (L + 2 * Real.log 2) -
        (L + 2 * Real.log 2) / 2 -
        (L / 2 + 2 * Real.log 2)) s := by
  let L := Real.log (1 / s)
  change HasDerivAt lrSmallSBridgeLogEnvelope
    ((L / 2 + 2 * Real.log 2) * (L + 2 * Real.log 2) -
      (L + 2 * Real.log 2) / 2 -
      (L / 2 + 2 * Real.log 2)) s
  have hL := hasDerivAt_lrSmallSBridgeLog hs
  have hA := hL.div_const 2 |>.add_const (2 * Real.log 2)
  have hC := hL.add_const (2 * Real.log 2)
  have hprod := (hasDerivAt_id s).mul (hA.mul hC)
  unfold lrSmallSBridgeLogEnvelope
  convert hprod using 1
  · funext x
    simp only [Pi.mul_apply, id_eq]
    ring
  · simp only [Pi.mul_apply, id_eq]
    dsimp [L]
    field_simp [hs.ne']
    ring

lemma lrSmallSBridgeLogEnvelope_monotoneOn :
    MonotoneOn lrSmallSBridgeLogEnvelope (Ioc (0 : ℝ) (1 / 16384)) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ioc (0 : ℝ) (1 / 16384))
  · intro s hs
    exact (hasDerivAt_lrSmallSBridgeLogEnvelope hs.1).continuousAt.continuousWithinAt
  · intro s hs
    rw [interior_Ioc] at hs
    exact (hasDerivAt_lrSmallSBridgeLogEnvelope hs.1).differentiableAt.differentiableWithinAt
  · intro s hs
    rw [interior_Ioc] at hs
    rw [(hasDerivAt_lrSmallSBridgeLogEnvelope hs.1).deriv]
    have hL := lrSmallSBridge_log_lower
      (show s ∈ Ioc (0 : ℝ) (1 / 16384) from ⟨hs.1, hs.2.le⟩)
    have hlogTwo := lr_log_two_millionth_bounds.1
    nlinarith [sq_nonneg (Real.log (1 / s))]

theorem lrSmallSBridgeLogEnvelope_upper
    {s : ℝ} (hs : s ∈ Ioc (0 : ℝ) (1 / 16384)) :
    lrSmallSBridgeLogEnvelope s ≤ 441 / 102400 := by
  have hmono := lrSmallSBridgeLogEnvelope_monotoneOn hs
    (show (1 / 16384 : ℝ) ∈ Ioc (0 : ℝ) (1 / 16384) by norm_num) hs.2
  have hendpoint :
      lrSmallSBridgeLogEnvelope (1 / 16384 : ℝ) =
        (1 / 16384 : ℝ) * (9 * Real.log 2) * (16 * Real.log 2) := by
    unfold lrSmallSBridgeLogEnvelope
    rw [show (1 : ℝ) / (1 / 16384) = 2 ^ 14 by norm_num,
      Real.log_pow]
    norm_num
    ring
  rw [hendpoint] at hmono
  have hlogUpper := lr_log_two_millionth_bounds.2.le
  have hlogNonneg := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  calc
    lrSmallSBridgeLogEnvelope s ≤
        (1 / 16384 : ℝ) * (9 * Real.log 2) * (16 * Real.log 2) := hmono
    _ ≤ 441 / 102400 := by nlinarith [sq_nonneg (Real.log 2)]

lemma lrSmallSBridge_one_add_inv_v_upper
    {s k chi : ℝ}
    (hs : s ∈ Ioc (0 : ℝ) (1 / 16384))
    (hk : k ∈ Icc (1 / 4 : ℝ) 4)
    (hchi : chi ∈ Icc (0 : ℝ) 1) :
    1 + (lrCertificateV ⟨s, k, chi⟩)⁻¹ ≤ (2001 / 1000 : ℝ) := by
  let v := lrCertificateV (⟨s, k, chi⟩ : CertificatePoint)
  have hd := lrSmallSBridge_one_sub_v_le hs hk hchi
  have he := lrSmallSBridgeE_upper hs hk
  have hvLower : (1000 / 1001 : ℝ) ≤ v := by
    change 1 - v ≤ (501 / 1000 : ℝ) * (s * k) at hd
    nlinarith [he.2]
  have hvPos : 0 < v := (by norm_num : (0 : ℝ) < 1000 / 1001).trans_le hvLower
  have hinv : v⁻¹ ≤ (1001 / 1000 : ℝ) := by
    rw [inv_le_iff_one_le_mul₀ hvPos]
    nlinarith [hvLower]
  change 1 + v⁻¹ ≤ (2001 / 1000 : ℝ)
  linarith

/-- Exact rational conclusion of the (M32) envelope payment. -/
theorem lrSmallSBridge_remainder_loss_bound
    {s factor : ℝ}
    (hs : s ∈ Ioc (0 : ℝ) (1 / 16384))
    (hfactor : factor ∈ Icc (0 : ℝ) (2001 / 1000)) :
    factor / 3 * lrSmallSBridgeLogEnvelope s ≤
      lrSmallSBridgeEpsilonR := by
  have henv := lrSmallSBridgeLogEnvelope_upper hs
  have henvNonneg : 0 ≤ lrSmallSBridgeLogEnvelope s := by
    unfold lrSmallSBridgeLogEnvelope
    have hL := lrSmallSBridge_log_lower hs
    have hlogTwo := lr_log_two_millionth_bounds.1.le
    have hA : 0 ≤ Real.log (1 / s) / 2 + 2 * Real.log 2 := by
      nlinarith
    have hC : 0 ≤ Real.log (1 / s) + 2 * Real.log 2 := by
      nlinarith
    exact mul_nonneg (mul_nonneg hs.1.le hA) hC
  calc
    factor / 3 * lrSmallSBridgeLogEnvelope s ≤
        (2001 / 1000 : ℝ) / 3 * lrSmallSBridgeLogEnvelope s := by
      exact mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right hfactor.2 (by norm_num)) henvNonneg
    _ ≤ (2001 / 1000 : ℝ) / 3 * (441 / 102400) := by
      exact mul_le_mul_of_nonneg_left henv (by norm_num)
    _ ≤ lrSmallSBridgeEpsilonR := by
      unfold lrSmallSBridgeEpsilonR
      norm_num

theorem lrSmallSBridge_remainder_loss_coordinate
    {s k chi : ℝ}
    (hs : s ∈ Ioc (0 : ℝ) (1 / 16384))
    (hk : k ∈ Icc (1 / 4 : ℝ) 4)
    (hchi : chi ∈ Icc (0 : ℝ) 1) :
    (1 + (lrCertificateV ⟨s, k, chi⟩)⁻¹) / 3 *
        lrSmallSBridgeLogEnvelope s ≤ lrSmallSBridgeEpsilonR := by
  apply lrSmallSBridge_remainder_loss_bound hs
  constructor
  · have hvNonneg : 0 ≤ lrCertificateV (⟨s, k, chi⟩ : CertificatePoint) := by
      unfold lrCertificateV
      exact Real.sqrt_nonneg _
    positivity
  · exact lrSmallSBridge_one_add_inv_v_upper hs hk hchi

end CourtadeKumar
