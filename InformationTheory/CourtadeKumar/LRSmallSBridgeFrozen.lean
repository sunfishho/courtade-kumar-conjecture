import InformationTheory.CourtadeKumar.LRSmallSBridgeChi

/-!
# Affine reduction for the frozen small-`s` bridge

This file formalizes the exact algebra in (M28)--(M29).  The frozen
normalized reserve is affine in `L = log (1 / s)`, and its slope is exactly
`lrSmallSBridgeLCoeff`.  Combined with the strict positivity theorem for
that coefficient, this reduces every `L ≥ 14 log 2` to the finite endpoint.
-/

open Set

namespace CourtadeKumar

noncomputable def lrSmallSBridgeAR (s k chi : ℝ) : ℝ :=
  (chi * Real.log (1 + (1 - s) * k * chi) +
    Real.log (1 + (1 - s) * k)) / (1 + chi)

noncomputable def lrSmallSBridgeP (s k chi L : ℝ) : ℝ :=
  L + 2 * Real.log 2 + 1 - s - lrSmallSBridgeAR s k chi

noncomputable def lrSmallSBridgeG (k chi L : ℝ) : ℝ :=
  L - Real.log k + 2 * Real.log 2 + 1 - lrSmallSBridgeQChi chi

noncomputable def lrSmallSBridgeS (s k chi L : ℝ) : ℝ :=
  lrSmallSBridgeP s k chi L - lrSmallSBridgeG k chi L

noncomputable def lrSmallSBridgeD (s k : ℝ) : ℝ :=
  Real.log ((1 + (1 - s) * k) / k) / 2

/-- The frozen normalized reserve.  `b` denotes the `L`-independent part
of the exact outer coefficient `B = L/2+b`; its precise formula is irrelevant
for the affine reduction. -/
noncomputable def lrSmallSBridgeFrozen
    (s k chi L b : ℝ) : ℝ :=
  k * (1 + chi) / 4 *
      (lrSmallSBridgeD s k * lrSmallSBridgeP s k chi L +
        (L / 2 + b) * lrSmallSBridgeS s k chi L) +
    ((L / 2 + b) - lrSmallSBridgeD s k) / 4

lemma lrSmallSBridgeS_eq
    (s k chi L : ℝ) :
    lrSmallSBridgeS s k chi L =
      Real.log k - s - lrSmallSBridgeAR s k chi +
        lrSmallSBridgeQChi chi := by
  unfold lrSmallSBridgeS lrSmallSBridgeP lrSmallSBridgeG
  ring

lemma lrSmallSBridge_log_identity
    {s k chi : ℝ}
    (hs : s ∈ Ioc (0 : ℝ) (1 / 16384))
    (hk : k ∈ Icc (1 / 4 : ℝ) 4)
    (hchi : chi ∈ Icc (0 : ℝ) 1) :
    (1 + chi) *
        (2 * lrSmallSBridgeD s k +
          (Real.log k - s - lrSmallSBridgeAR s k chi +
            lrSmallSBridgeQChi chi)) =
      chi * Real.log
          (chi * (1 + (1 - s) * k) /
            (1 + (1 - s) * k * chi)) -
        s * (1 + chi) := by
  have hkPos : 0 < k := (by norm_num : (0 : ℝ) < 1 / 4).trans_le hk.1
  have hR : 0 ≤ 1 - s := by nlinarith [hs.2]
  have houterPos : 0 < 1 + (1 - s) * k := by positivity
  have hinnerPos : 0 < 1 + (1 - s) * k * chi := by
    have hchiNonneg : 0 ≤ chi := hchi.1
    positivity
  have hchiDen : 1 + chi ≠ 0 := by linarith [hchi.1]
  rcases hchi.1.eq_or_lt with rfl | hchiPos
  · unfold lrSmallSBridgeD lrSmallSBridgeAR lrSmallSBridgeQChi
    rw [Real.log_div houterPos.ne' hkPos.ne']
    simp
    ring
  · unfold lrSmallSBridgeD lrSmallSBridgeAR lrSmallSBridgeQChi
    rw [Real.log_div houterPos.ne' hkPos.ne']
    have hnumPos : 0 < chi * (1 + (1 - s) * k) :=
      mul_pos hchiPos houterPos
    have hlogratio :
        Real.log (chi * (1 + (1 - s) * k) /
            (1 + (1 - s) * k * chi)) =
          Real.log chi + Real.log (1 + (1 - s) * k) -
            Real.log (1 + (1 - s) * k * chi) := by
      rw [Real.log_div hnumPos.ne' hinnerPos.ne',
        Real.log_mul hchiPos.ne' houterPos.ne']
    rw [hlogratio]
    field_simp [hchiDen]
    ring

lemma lrSmallSBridge_slope_eq
    {s k chi : ℝ}
    (hs : s ∈ Ioc (0 : ℝ) (1 / 16384))
    (hk : k ∈ Icc (1 / 4 : ℝ) 4)
    (hchi : chi ∈ Icc (0 : ℝ) 1) :
    (1 + k * (1 + chi) *
        (2 * lrSmallSBridgeD s k +
          lrSmallSBridgeS s k chi 0)) / 8 =
      lrSmallSBridgeLCoeff s k chi := by
  rw [lrSmallSBridgeS_eq]
  have hid := lrSmallSBridge_log_identity hs hk hchi
  calc
    (1 + k * (1 + chi) *
        (2 * lrSmallSBridgeD s k +
          (Real.log k - s - lrSmallSBridgeAR s k chi +
            lrSmallSBridgeQChi chi))) / 8 =
        (1 + k * ((1 + chi) *
          (2 * lrSmallSBridgeD s k +
            (Real.log k - s - lrSmallSBridgeAR s k chi +
              lrSmallSBridgeQChi chi)))) / 8 := by ring
    _ = (1 + k *
        (chi * Real.log
          (chi * (1 + (1 - s) * k) /
            (1 + (1 - s) * k * chi)) - s * (1 + chi))) / 8 := by rw [hid]
    _ = lrSmallSBridgeLCoeff s k chi := by
      unfold lrSmallSBridgeLCoeff
      ring

theorem lrSmallSBridgeFrozen_affine
    {s k chi : ℝ}
    (hs : s ∈ Ioc (0 : ℝ) (1 / 16384))
    (hk : k ∈ Icc (1 / 4 : ℝ) 4)
    (hchi : chi ∈ Icc (0 : ℝ) 1)
    (L₁ L₂ b : ℝ) :
    lrSmallSBridgeFrozen s k chi L₂ b =
      lrSmallSBridgeFrozen s k chi L₁ b +
        (L₂ - L₁) * lrSmallSBridgeLCoeff s k chi := by
  have hS : lrSmallSBridgeS s k chi L₂ =
      lrSmallSBridgeS s k chi L₁ := by
    simp only [lrSmallSBridgeS_eq]
  have hp : lrSmallSBridgeP s k chi L₂ =
      lrSmallSBridgeP s k chi L₁ + (L₂ - L₁) := by
    unfold lrSmallSBridgeP
    ring
  have hslope := lrSmallSBridge_slope_eq hs hk hchi
  have hS0 : lrSmallSBridgeS s k chi 0 =
      lrSmallSBridgeS s k chi L₁ := by
    simp only [lrSmallSBridgeS_eq]
  rw [hS0] at hslope
  calc
    lrSmallSBridgeFrozen s k chi L₂ b =
        lrSmallSBridgeFrozen s k chi L₁ b +
          (L₂ - L₁) *
            ((1 + k * (1 + chi) *
              (2 * lrSmallSBridgeD s k +
                lrSmallSBridgeS s k chi L₁)) / 8) := by
      unfold lrSmallSBridgeFrozen
      rw [hS, hp]
      ring
    _ = lrSmallSBridgeFrozen s k chi L₁ b +
        (L₂ - L₁) * lrSmallSBridgeLCoeff s k chi := by
      rw [hslope]

/-- Endpoint reduction used before the exact replay in (M30). -/
theorem lrSmallSBridgeFrozen_endpoint_le
    {s k chi L b : ℝ}
    (hs : s ∈ Ioc (0 : ℝ) (1 / 16384))
    (hk : k ∈ Icc (1 / 4 : ℝ) 4)
    (hchi : chi ∈ Icc (0 : ℝ) 1)
    (hL : 14 * Real.log 2 ≤ L) :
    lrSmallSBridgeFrozen s k chi (14 * Real.log 2) b ≤
      lrSmallSBridgeFrozen s k chi L b := by
  calc
    lrSmallSBridgeFrozen s k chi (14 * Real.log 2) b ≤
        lrSmallSBridgeFrozen s k chi (14 * Real.log 2) b +
          (L - 14 * Real.log 2) * lrSmallSBridgeLCoeff s k chi :=
      le_add_of_nonneg_right
        (mul_nonneg (sub_nonneg.mpr hL)
          (lrSmallSBridgeLCoeff_pos hs hk hchi).le)
    _ = lrSmallSBridgeFrozen s k chi L b :=
      (lrSmallSBridgeFrozen_affine hs hk hchi
        (14 * Real.log 2) L b).symm

end CourtadeKumar
