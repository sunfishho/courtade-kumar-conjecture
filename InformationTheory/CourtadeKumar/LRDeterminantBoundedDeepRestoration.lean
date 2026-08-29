import InformationTheory.CourtadeKumar.LRDeterminantBoundedDeepAssembly
import InformationTheory.CourtadeKumar.LRDeterminantIdealCoreCertificate
import InformationTheory.CourtadeKumar.LRDeterminantLowRatioSmallSAnalytic
import InformationTheory.CourtadeKumar.LRDeterminantLowKTrueChannelRestoration
import InformationTheory.CourtadeKumar.LRSmallSBridgeDecomposition
import InformationTheory.CourtadeKumar.LRSmallSBridgeRemainderIdentification

/-!
# Kernel-only bounded-deep DA3/DA4 restoration

This module records the exact determinant-level `Q = q + r`
decomposition, the four-stage restoration telescope, and the final DA3/DA4
ledger assembly.  Every remaining analytic obligation is exposed as a named
field of `LRBoundedDeepRestorationAnalyticInputs`; none is hidden behind an
unidentified surrogate core.

The module deliberately contains no concrete replay data and no non-kernel
proof shortcut.
-/

open Set

namespace CourtadeKumar

/-! ## Explicit `q` and `r` coordinates -/

noncomputable def lrBoundedDeepQG (point : CertificatePoint) : ℝ :=
  lrSmallSBridgeQ0G point

noncomputable def lrBoundedDeepRG (point : CertificatePoint) : ℝ :=
  lrSmallSBridgeR0G point

noncomputable def lrBoundedDeepQW (point : CertificatePoint) : ℝ :=
  lrLowerFaceOmegaQ0 point.s 0

noncomputable def lrBoundedDeepRW (point : CertificatePoint) : ℝ :=
  lrLowerFaceOmegaR0 point.s 0

noncomputable def lrBoundedDeepQPW (point : CertificatePoint) : ℝ :=
  lrLowerFacePWQ0 point.s point.k point.chi (lrCertificateV point)

noncomputable def lrBoundedDeepRPW (point : CertificatePoint) : ℝ :=
  lrLowerFacePWR0 point.s point.k point.chi (lrCertificateV point)

/-- The `q` part of `Psi`. -/
noncomputable def lrBoundedDeepQPsi (point : CertificatePoint) : ℝ :=
  lrBoundedDeepQG point + lrBoundedDeepQPW point -
    4 * lrBoundedDeepQW point / (1 + lrCertificateV point)

/-- The `r` part of `Psi`. -/
noncomputable def lrBoundedDeepRPsi (point : CertificatePoint) : ℝ :=
  lrBoundedDeepRG point + lrBoundedDeepRPW point -
    4 * lrBoundedDeepRW point / (1 + lrCertificateV point)

/-- The entropy-remainder part of `Psi-G`. -/
noncomputable def lrBoundedDeepROmega (point : CertificatePoint) : ℝ :=
  lrBoundedDeepRPW point -
    4 * lrBoundedDeepRW point / (1 + lrCertificateV point)

theorem lrBoundedDeep_G_eq_q_add_r (point : CertificatePoint) :
    lrCertificateGShape point =
      lrBoundedDeepQG point + lrBoundedDeepRG point := by
  simpa [lrBoundedDeepQG, lrBoundedDeepRG] using
    lrCertificateGShape_eq_smallSBridge_split point

theorem lrBoundedDeep_W_eq_q_add_r (point : CertificatePoint) :
    lrCertificateW point =
      lrBoundedDeepQW point + lrBoundedDeepRW point := by
  simpa [lrBoundedDeepQW, lrBoundedDeepRW] using
    lrCertificateW_eq_smallSBridge_split point

theorem lrBoundedDeep_PW_eq_q_add_r (point : CertificatePoint) :
    lrCertificatePW point =
      lrBoundedDeepQPW point + lrBoundedDeepRPW point := by
  simpa [lrBoundedDeepQPW, lrBoundedDeepRPW] using
    lrCertificatePW_eq_smallSBridge_split point

theorem lrBoundedDeep_Psi_eq_q_add_r (point : CertificatePoint) :
    lrDeterminantPsi point =
      lrBoundedDeepQPsi point + lrBoundedDeepRPsi point := by
  rw [lrDeterminantPsi, lrBoundedDeep_G_eq_q_add_r,
    lrBoundedDeep_PW_eq_q_add_r, lrBoundedDeep_W_eq_q_add_r]
  unfold lrBoundedDeepQPsi lrBoundedDeepRPsi
  ring

theorem lrBoundedDeep_RPsi_eq_RG_add_ROmega
    (point : CertificatePoint) :
    lrBoundedDeepRPsi point =
      lrBoundedDeepRG point + lrBoundedDeepROmega point := by
  unfold lrBoundedDeepRPsi lrBoundedDeepROmega
  ring

/-! ## Exact split of the determinant gap -/

noncomputable def lrBoundedDeepQSquareTarget
    (point : CertificatePoint) : ℝ :=
  lrCertificateG0 (lrCertificateV point) +
    lrLowerFaceQ0 (lrCertificateB point.s (lrCertificateY0 point)) +
    lrLowerFaceQ0 (lrCertificateB point.s (lrCertificateE point)) /
      lrCertificateV point

noncomputable def lrBoundedDeepRSquareTarget
    (point : CertificatePoint) : ℝ :=
  lrLowerFaceR0 (lrCertificateB point.s (lrCertificateY0 point)) +
    lrLowerFaceR0 (lrCertificateB point.s (lrCertificateE point)) /
      lrCertificateV point

noncomputable def lrBoundedDeepQPrefixAtM
    (point : CertificatePoint) : ℝ :=
  point.s *
      (lrCertificateG0 (lrCertificateV point) +
        (1 + 1 / lrCertificateV point) * Real.log 2) +
    4 * (lrLowerFaceQ0 point.s - point.s * Real.log 2) /
      (1 + lrCertificateV point)

noncomputable def lrBoundedDeepRPrefixAtM
    (point : CertificatePoint) : ℝ :=
  4 * lrLowerFaceR0 point.s / (1 + lrCertificateV point)

noncomputable def lrBoundedDeepQGap (point : CertificatePoint) : ℝ :=
  lrBoundedDeepQSquareTarget point - lrBoundedDeepQPrefixAtM point

noncomputable def lrBoundedDeepRGap (point : CertificatePoint) : ℝ :=
  lrBoundedDeepRSquareTarget point - lrBoundedDeepRPrefixAtM point

theorem lrBoundedDeep_squareTarget_eq_q_add_r
    (point : CertificatePoint) :
    lrCertificateSquareTarget point =
      lrBoundedDeepQSquareTarget point +
        lrBoundedDeepRSquareTarget point := by
  unfold lrCertificateSquareTarget lrBoundedDeepQSquareTarget
    lrBoundedDeepRSquareTarget lrLowerFaceR0
  ring

theorem lrBoundedDeep_prefixAtM_eq_q_add_r
    (point : CertificatePoint) :
    lrCertificatePrefixAtM point =
      lrBoundedDeepQPrefixAtM point +
        lrBoundedDeepRPrefixAtM point := by
  unfold lrCertificatePrefixAtM lrBoundedDeepQPrefixAtM
    lrBoundedDeepRPrefixAtM lrLowerFaceR0
  ring

theorem lrBoundedDeep_gap_eq_q_add_r (point : CertificatePoint) :
    lrCertificateGap point =
      lrBoundedDeepQGap point + lrBoundedDeepRGap point := by
  unfold lrCertificateGap lrBoundedDeepQGap lrBoundedDeepRGap
  rw [lrBoundedDeep_squareTarget_eq_q_add_r,
    lrBoundedDeep_prefixAtM_eq_q_add_r]
  ring

theorem lrBoundedDeep_T_eq_q_add_r (point : CertificatePoint) :
    lrDeterminantT point =
      lrBoundedDeepQGap point / lrCertificateR point +
        lrBoundedDeepRGap point / lrCertificateR point := by
  unfold lrDeterminantT
  rw [lrBoundedDeep_gap_eq_q_add_r]
  ring

/-! ## Normalized coordinates and the exact actual determinant split -/

noncomputable def lrBoundedDeepQP (point : CertificatePoint) : ℝ :=
  lrBoundedDeepQPsi point / lrLowKNormalization point

noncomputable def lrBoundedDeepQS (point : CertificatePoint) : ℝ :=
  (lrBoundedDeepQPsi point - lrBoundedDeepQG point) /
    lrLowKNormalization point

noncomputable def lrBoundedDeepQT (point : CertificatePoint) : ℝ :=
  (lrBoundedDeepQGap point / lrCertificateR point) /
    lrLowKNormalization point

noncomputable def lrBoundedDeepRNormalizedG
    (point : CertificatePoint) : ℝ :=
  lrBoundedDeepRG point / lrLowKNormalization point

noncomputable def lrBoundedDeepRNormalizedOmega
    (point : CertificatePoint) : ℝ :=
  lrBoundedDeepROmega point / lrLowKNormalization point

noncomputable def lrBoundedDeepRNormalizedP
    (point : CertificatePoint) : ℝ :=
  lrBoundedDeepRPsi point / lrLowKNormalization point

noncomputable def lrBoundedDeepRNormalizedT
    (point : CertificatePoint) : ℝ :=
  (lrBoundedDeepRGap point / lrCertificateR point) /
    lrLowKNormalization point

theorem lrBoundedDeep_RNormalizedP_eq_G_add_Omega
    (point : CertificatePoint) :
    lrBoundedDeepRNormalizedP point =
      lrBoundedDeepRNormalizedG point +
        lrBoundedDeepRNormalizedOmega point := by
  unfold lrBoundedDeepRNormalizedP lrBoundedDeepRNormalizedG
    lrBoundedDeepRNormalizedOmega
  rw [lrBoundedDeep_RPsi_eq_RG_add_ROmega]
  ring

theorem lrBoundedDeep_normalized_Psi_eq_q_add_r
    (point : CertificatePoint) :
    lrDeterminantPsi point / lrLowKNormalization point =
      lrBoundedDeepQP point + lrBoundedDeepRNormalizedP point := by
  unfold lrBoundedDeepQP lrBoundedDeepRNormalizedP
  rw [lrBoundedDeep_Psi_eq_q_add_r]
  ring

theorem lrBoundedDeep_normalized_Omega_eq_q_add_r
    (point : CertificatePoint) :
    (lrDeterminantPsi point - lrCertificateGShape point) /
        lrLowKNormalization point =
      lrBoundedDeepQS point + lrBoundedDeepRNormalizedOmega point := by
  unfold lrBoundedDeepQS lrBoundedDeepRNormalizedOmega
  rw [lrBoundedDeep_Psi_eq_q_add_r, lrBoundedDeep_G_eq_q_add_r]
  rw [lrBoundedDeep_RPsi_eq_RG_add_ROmega]
  ring

theorem lrBoundedDeep_normalized_T_eq_q_add_r
    (point : CertificatePoint) :
    lrDeterminantT point / lrLowKNormalization point =
      lrBoundedDeepQT point + lrBoundedDeepRNormalizedT point := by
  unfold lrBoundedDeepQT lrBoundedDeepRNormalizedT
  rw [lrBoundedDeep_T_eq_q_add_r]
  ring

/-- The increment-built true-channel coordinates agree with the explicit
`q` coordinates above. -/
def LRBoundedDeepQChannelIdentification
    (point : CertificatePoint) : Prop :=
  lrDA7ChannelP point = lrBoundedDeepQP point ∧
    lrDA7ChannelS point = lrBoundedDeepQS point ∧
    lrDA7ChannelT point = lrBoundedDeepQT point

/-! ## Exact identification of the `q` channel -/

lemma lrDA7LogarithmicQ_eq_lowerFaceQ0 (y : ℝ) :
    lrDA7LogarithmicQ y = lrLowerFaceQ0 y := by
  rfl

lemma lrDA7LogarithmicQPrime_eq_lowerFaceQ0Prime (y : ℝ) :
    lrDA7LogarithmicQPrime y = lrLowerFaceQ0Prime y := by
  rfl

lemma lrDA7LogarithmicOmega_eq_lowerFaceOmegaQ0 (s y : ℝ) :
    lrDA7LogarithmicOmega s y = lrLowerFaceOmegaQ0 s y := by
  rfl

lemma lrDA7FiniteP_eq_smallSBridgeP (point : CertificatePoint) :
    lrDA7FiniteP point =
      lrSmallSBridgeP point.s point.k point.chi
        (Real.log (1 / point.s)) := by
  unfold lrDA7FiniteP lrDA7FiniteA lrSmallSBridgeP lrSmallSBridgeAR
  rfl

lemma lrDA7FiniteG_eq_smallSBridgeG (point : CertificatePoint) :
    lrDA7FiniteG point =
      lrSmallSBridgeG point.k point.chi
        (Real.log (1 / point.s)) := by
  unfold lrDA7FiniteG lrSmallSBridgeG lrLowKIdealQChi
    lrSmallSBridgeQChi
  rfl

lemma lrDA7FiniteS_eq_smallSBridgeS (point : CertificatePoint) :
    lrDA7FiniteS point =
      lrSmallSBridgeS point.s point.k point.chi
        (Real.log (1 / point.s)) := by
  unfold lrDA7FiniteS lrSmallSBridgeS
  rw [lrDA7FiniteP_eq_smallSBridgeP,
    lrDA7FiniteG_eq_smallSBridgeG]

noncomputable def lrBoundedDeepQGFrozen (point : CertificatePoint) : ℝ :=
  lrLowerFaceQ0 (lrCertificateY0 point) +
    lrLowerFaceQ0 (lrCertificateE point)

noncomputable def lrBoundedDeepQOmegaFrozen
    (point : CertificatePoint) : ℝ :=
  lrLowerFacePWQ0 point.s point.k point.chi 1 -
    2 * lrLowerFaceOmegaQ0 point.s 0

noncomputable def lrBoundedDeepQPsiFrozen
    (point : CertificatePoint) : ℝ :=
  lrBoundedDeepQGFrozen point + lrBoundedDeepQOmegaFrozen point

noncomputable def lrBoundedDeepQOmega (point : CertificatePoint) : ℝ :=
  lrBoundedDeepQPW point -
    4 * lrBoundedDeepQW point / (1 + lrCertificateV point)

lemma lrBoundedDeep_k_pos
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point) :
    0 < point.k := by
  have he := hinterior.2.1.1
  unfold lrCertificateE at he
  by_contra hk
  have hkNonpos : point.k ≤ 0 := le_of_not_gt hk
  have hprodNonpos : point.s * point.k ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hinterior.1.1.le hkNonpos
  linarith

lemma lrBoundedDeep_qG_frozen_eq
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point) :
    lrBoundedDeepQGFrozen point =
      lrLowKNormalization point * lrDA7FiniteG point := by
  have h := lrLowRatioQ0G_frozen_eq_of_pos
    hinterior.1.1 (lrBoundedDeep_k_pos hinterior)
    (show point.chi ∈ Icc (0 : ℝ) 1 from
      ⟨hinterior.2.2.1.le, hinterior.2.2.2.le⟩)
  rw [lrDA7FiniteG_eq_smallSBridgeG]
  simpa [lrBoundedDeepQGFrozen, lrLowKNormalization,
    lrCertificateY0, lrCertificateE] using h

lemma lrBoundedDeep_qPW_frozen_eq
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point) :
    lrLowerFacePWQ0 point.s point.k point.chi 1 =
      lrLowKNormalization point * lrDA7FiniteS point + point.s / 2 := by
  have h := lrLowRatioPWQ0_frozen_eq_of_physical
    hinterior.1 (lrBoundedDeep_k_pos hinterior)
    (by simpa [lrCertificateE] using hinterior.2.1.2)
    (show point.chi ∈ Icc (0 : ℝ) 1 from
      ⟨hinterior.2.2.1.le, hinterior.2.2.2.le⟩)
  rw [lrDA7FiniteS_eq_smallSBridgeS]
  simpa [lrLowKNormalization, lrCertificateE] using h

lemma lrBoundedDeep_qOmega_frozen_eq
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point) :
    lrBoundedDeepQOmegaFrozen point =
      lrLowKNormalization point * lrDA7FiniteS point := by
  unfold lrBoundedDeepQOmegaFrozen
  rw [lrBoundedDeep_qPW_frozen_eq hinterior,
    lrLowerFaceOmegaQ0_zero hinterior.1.1]
  ring

lemma lrBoundedDeep_qPsi_frozen_eq
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point) :
    lrBoundedDeepQPsiFrozen point =
      lrLowKNormalization point * lrDA7FiniteP point := by
  unfold lrBoundedDeepQPsiFrozen
  rw [lrBoundedDeep_qG_frozen_eq hinterior,
    lrBoundedDeep_qOmega_frozen_eq hinterior]
  unfold lrDA7FiniteS
  ring

lemma lrBoundedDeep_qG_eq_frozen_add_deltaG
    (point : CertificatePoint) :
    lrBoundedDeepQG point =
      lrBoundedDeepQGFrozen point + lrDA7ChannelDeltaG point := by
  unfold lrBoundedDeepQG lrSmallSBridgeQ0G
    lrBoundedDeepQGFrozen lrDA7ChannelDeltaG
  rw [lrDA7LogarithmicQ_eq_lowerFaceQ0]
  ring

lemma lrBoundedDeep_qOmega_eq_frozen_add_deltaOmega
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point) :
    lrBoundedDeepQOmega point =
      lrBoundedDeepQOmegaFrozen point +
        lrDA7ChannelDeltaOmega point := by
  have hv := lrCertificateV_mem_Ioo hinterior
  have hvPlus : 1 + lrCertificateV point ≠ 0 := by
    linarith [hv.1]
  unfold lrBoundedDeepQOmega lrBoundedDeepQPW lrBoundedDeepQW
    lrBoundedDeepQOmegaFrozen lrLowerFacePWQ0
    lrDA7ChannelDeltaOmega
  simp only [lrDA7LogarithmicOmega_eq_lowerFaceOmegaQ0]
  unfold lrDA7ChannelB lrDA7ChannelKappa lrDA7ChannelD
    lrCertificateE
  field_simp [hv.1.ne', hvPlus]
  ring

lemma lrBoundedDeep_qPsi_eq_frozen_add_deltas
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point) :
    lrBoundedDeepQPsi point =
      lrBoundedDeepQPsiFrozen point +
        lrDA7ChannelDeltaG point + lrDA7ChannelDeltaOmega point := by
  have hsplit : lrBoundedDeepQPsi point =
      lrBoundedDeepQG point + lrBoundedDeepQOmega point := by
    unfold lrBoundedDeepQPsi lrBoundedDeepQOmega
    ring
  rw [hsplit, lrBoundedDeep_qG_eq_frozen_add_deltaG,
    lrBoundedDeep_qOmega_eq_frozen_add_deltaOmega hinterior]
  unfold lrBoundedDeepQPsiFrozen
  ring

lemma lrDA7ChannelP_eq_boundedDeepQP
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point) :
    lrDA7ChannelP point = lrBoundedDeepQP point := by
  have hn := (lrLowKNormalization_pos hinterior).ne'
  unfold lrDA7ChannelP lrBoundedDeepQP
  rw [lrBoundedDeep_qPsi_eq_frozen_add_deltas hinterior,
    lrBoundedDeep_qPsi_frozen_eq hinterior]
  field_simp [hn]
  ring

lemma lrDA7ChannelS_eq_boundedDeepQS
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point) :
    lrDA7ChannelS point = lrBoundedDeepQS point := by
  have hn := (lrLowKNormalization_pos hinterior).ne'
  have hOmega : lrBoundedDeepQPsi point - lrBoundedDeepQG point =
      lrBoundedDeepQOmega point := by
    unfold lrBoundedDeepQPsi lrBoundedDeepQOmega
    ring
  unfold lrDA7ChannelS lrBoundedDeepQS
  rw [hOmega,
    lrBoundedDeep_qOmega_eq_frozen_add_deltaOmega hinterior,
    lrBoundedDeep_qOmega_frozen_eq hinterior]
  field_simp [hn]

noncomputable def lrBoundedDeepQGapFrozen
    (point : CertificatePoint) : ℝ :=
  lrLowerFaceQ0
      (lrCertificateB point.s (lrCertificateY0 point)) +
    lrLowerFaceQ0
      (lrCertificateB point.s (lrCertificateE point)) -
    2 * lrLowerFaceQ0 point.s

/-- One-variable identity behind the frozen tangent coordinate. -/
lemma lrLowerFaceQ0_B_sk_sub
    {s a : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) (ha : 0 < a) :
    lrLowerFaceQ0 (lrCertificateB s (s * a)) -
        lrLowerFaceQ0 s =
      s * (1 - s) * a / 4 *
        (Real.log (1 / s) + 2 * Real.log 2 + 1 -
          lrLowKIdealH (1 + (1 - s) * a)) := by
  have hR : 0 < 1 - s := sub_pos.mpr hs.2
  have hprod : 0 < (1 - s) * a := mul_pos hR ha
  have hz : 1 < 1 + (1 - s) * a := by
    linarith
  have hzPos : 0 < 1 + (1 - s) * a := by
    linarith
  have hb : lrCertificateB s (s * a) =
      s * (1 + (1 - s) * a) := by
    unfold lrCertificateB
    ring
  have hlogInv : Real.log (1 / s) = -Real.log s := by
    rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) hs.1.ne']
    norm_num
  rw [hb]
  unfold lrLowerFaceQ0 lrLowKIdealH
  simp only [if_neg hz.ne']
  rw [Real.log_div (by norm_num : (4 : ℝ) ≠ 0)
        (mul_pos hs.1 hzPos).ne',
      Real.log_mul hs.1.ne' hzPos.ne',
      Real.log_div (by norm_num : (4 : ℝ) ≠ 0) hs.1.ne',
      lrSmallSBridge_log_four, hlogInv]
  field_simp [show 1 + (1 - s) * a - 1 ≠ 0 by nlinarith]
  ring

lemma lrBoundedDeep_qGap_frozen_eq
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point) :
    lrBoundedDeepQGapFrozen point =
      lrCertificateR point * lrLowKNormalization point *
        lrDA7FiniteT point := by
  have hk := lrBoundedDeep_k_pos hinterior
  have hchi := hinterior.2.2.1
  have hInner := lrLowerFaceQ0_B_sk_sub
    (s := point.s) (a := point.k * point.chi)
    hinterior.1 (mul_pos hk hchi)
  have hOuter := lrLowerFaceQ0_B_sk_sub
    (s := point.s) (a := point.k) hinterior.1 hk
  have hy0 : lrCertificateY0 point =
      point.s * (point.k * point.chi) := by
    unfold lrCertificateY0 lrCertificateE
    ring
  have he : lrCertificateE point = point.s * point.k := by
    rfl
  have hzInner :
      1 + (1 - point.s) * (point.k * point.chi) =
        1 + (1 - point.s) * point.k * point.chi := by
    ring
  unfold lrBoundedDeepQGapFrozen
  rw [hy0, he]
  calc
    lrLowerFaceQ0
          (lrCertificateB point.s
            (point.s * (point.k * point.chi))) +
        lrLowerFaceQ0
          (lrCertificateB point.s (point.s * point.k)) -
        2 * lrLowerFaceQ0 point.s =
      (lrLowerFaceQ0
          (lrCertificateB point.s
            (point.s * (point.k * point.chi))) -
          lrLowerFaceQ0 point.s) +
        (lrLowerFaceQ0
          (lrCertificateB point.s (point.s * point.k)) -
          lrLowerFaceQ0 point.s) := by ring
    _ = point.s * (1 - point.s) * (point.k * point.chi) / 4 *
          (Real.log (1 / point.s) + 2 * Real.log 2 + 1 -
            lrLowKIdealH
              (1 + (1 - point.s) * (point.k * point.chi))) +
        point.s * (1 - point.s) * point.k / 4 *
          (Real.log (1 / point.s) + 2 * Real.log 2 + 1 -
            lrLowKIdealH (1 + (1 - point.s) * point.k)) := by
      rw [hInner, hOuter]
    _ = lrCertificateR point * lrLowKNormalization point *
          lrDA7FiniteT point := by
      rw [hzInner]
      unfold lrCertificateR lrLowKNormalization lrCertificateE
        lrDA7FiniteT lrDA7FiniteAH
      field_simp [show 1 + point.chi ≠ 0 by linarith]
      ring

lemma lrBoundedDeep_qGap_eq_frozen_add_deltaT
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point) :
    lrBoundedDeepQGap point =
      lrBoundedDeepQGapFrozen point +
        lrCertificateR point * lrDA7ChannelDeltaT point := by
  have hv := lrCertificateV_mem_Ioo hinterior
  have hvPlus : 1 + lrCertificateV point ≠ 0 := by
    linarith [hv.1]
  have hR : lrCertificateR point ≠ 0 := by
    unfold lrCertificateR
    linarith [hinterior.1.2]
  have hOneSubS : 1 - point.s ≠ 0 := by
    linarith [hinterior.1.2]
  unfold lrBoundedDeepQGap lrBoundedDeepQSquareTarget
    lrBoundedDeepQPrefixAtM lrBoundedDeepQGapFrozen
    lrDA7ChannelDeltaT lrDA7ChannelF0 lrDA7ChannelB
    lrDA7ChannelKappa lrDA7ChannelD
  simp only [lrDA7LogarithmicQ_eq_lowerFaceQ0]
  unfold lrCertificateR
  field_simp [hv.1.ne', hvPlus, hR, hOneSubS]
  ring

lemma lrDA7ChannelT_eq_boundedDeepQT
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point) :
    lrDA7ChannelT point = lrBoundedDeepQT point := by
  have hR : lrCertificateR point ≠ 0 := by
    unfold lrCertificateR
    linarith [hinterior.1.2]
  have hn := (lrLowKNormalization_pos hinterior).ne'
  have hfrozen := lrBoundedDeep_qGap_frozen_eq hinterior
  have hdelta := lrBoundedDeep_qGap_eq_frozen_add_deltaT hinterior
  have hfinite : lrDA7FiniteT point =
      (lrBoundedDeepQGapFrozen point / lrCertificateR point) /
        lrLowKNormalization point := by
    rw [hfrozen]
    field_simp [hR, hn]
  unfold lrDA7ChannelT lrBoundedDeepQT
  rw [hfinite, hdelta]
  field_simp [hR, hn]

theorem lrBoundedDeep_qChannelIdentification
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point) :
    LRBoundedDeepQChannelIdentification point := by
  exact ⟨lrDA7ChannelP_eq_boundedDeepQP hinterior,
    lrDA7ChannelS_eq_boundedDeepQS hinterior,
    lrDA7ChannelT_eq_boundedDeepQT hinterior⟩

/-- The true-channel `q` core with the actual entropy coefficient `c0`. -/
noncomputable def lrBoundedDeepActualCoefficientQCore
    (point : CertificatePoint) : ℝ :=
  lrDeterminantD1 point * lrDA7ChannelP point +
    lrCertificateBFlow point * lrDA7ChannelS point +
    lrDeterminantC0 point * lrDA7ChannelJ1 point *
      lrDA7ChannelT point

/-- The exact normalized `r` contribution to DA1, including the favorable
`4 delta B W` term. -/
noncomputable def lrBoundedDeepRemainderContribution
    (point : CertificatePoint) : ℝ :=
  lrDeterminantD1 point * lrBoundedDeepRNormalizedP point +
    lrCertificateBFlow point * lrBoundedDeepRNormalizedOmega point +
    4 * lrDeterminantDelta point * lrCertificateBFlow point *
        lrCertificateW point / lrLowKNormalization point +
    lrDeterminantC0 point * lrDA7ChannelJ1 point *
      lrBoundedDeepRNormalizedT point

theorem lrBoundedDeep_actual_eq_qCore_add_remainder
    {point : CertificatePoint}
    (hn : lrLowKNormalization point ≠ 0)
    (hidentify : LRBoundedDeepQChannelIdentification point) :
    lrLowKActualNormalized point =
      lrBoundedDeepActualCoefficientQCore point +
        lrBoundedDeepRemainderContribution point := by
  rcases hidentify with ⟨hP, hS, hT⟩
  rw [lrLowKActualNormalized_eq_DA1 hn]
  calc
    (lrDeterminantD1 point * lrDeterminantPsi point +
          lrCertificateBFlow point *
            (lrDeterminantPsi point - lrCertificateGShape point) +
          4 * lrDeterminantDelta point * lrCertificateBFlow point *
            lrCertificateW point +
          lrDeterminantC0 point *
            (lrCertificateBFlow point * lrCertificateX point -
              lrDeterminantD1 point) * lrDeterminantT point) /
        lrLowKNormalization point =
      lrDeterminantD1 point *
          (lrDeterminantPsi point / lrLowKNormalization point) +
        lrCertificateBFlow point *
          ((lrDeterminantPsi point - lrCertificateGShape point) /
            lrLowKNormalization point) +
        4 * lrDeterminantDelta point * lrCertificateBFlow point *
          lrCertificateW point / lrLowKNormalization point +
        lrDeterminantC0 point *
          (lrCertificateBFlow point * lrCertificateX point -
            lrDeterminantD1 point) *
          (lrDeterminantT point / lrLowKNormalization point) := by ring
    _ = lrBoundedDeepActualCoefficientQCore point +
          lrBoundedDeepRemainderContribution point := by
      rw [lrBoundedDeep_normalized_Psi_eq_q_add_r,
        lrBoundedDeep_normalized_Omega_eq_q_add_r,
        lrBoundedDeep_normalized_T_eq_q_add_r, ← hP, ← hS, ← hT]
      unfold lrBoundedDeepActualCoefficientQCore
        lrBoundedDeepRemainderContribution lrDA7ChannelJ1
      ring

theorem lrBoundedDeep_trueQ_sub_actualQCoefficient
    (point : CertificatePoint) :
    lrDA7TrueChannelCore point -
        lrBoundedDeepActualCoefficientQCore point =
      (lrDA7ChannelC0Q point - lrDeterminantC0 point) *
        lrDA7ChannelJ1 point * lrDA7ChannelT point := by
  unfold lrDA7TrueChannelCore lrBoundedDeepActualCoefficientQCore
  ring

theorem lrBoundedDeep_remainderContribution_collected
    (point : CertificatePoint) :
    lrBoundedDeepRemainderContribution point =
      lrDeterminantD1 point * lrBoundedDeepRNormalizedG point +
        (lrDeterminantD1 point + lrCertificateBFlow point) *
          lrBoundedDeepRNormalizedOmega point +
        4 * lrDeterminantDelta point * lrCertificateBFlow point *
          lrCertificateW point / lrLowKNormalization point +
        (lrDeterminantC0 point * lrDA7ChannelJ1 point) *
          lrBoundedDeepRNormalizedT point := by
  rw [lrBoundedDeepRemainderContribution,
    lrBoundedDeep_RNormalizedP_eq_G_add_Omega]
  ring

/-! ## Exact four-stage telescope -/

theorem lrBoundedDeep_four_stage_telescope
    (point : CertificatePoint) :
    lrDeterminantIdealCore (Real.log (1 / point.s)) point.k point.chi -
        lrLowKActualNormalized point =
      (lrDeterminantIdealCore (Real.log (1 / point.s))
          point.k point.chi - lrDA7FiniteFrozenCore point) +
      (lrDA7FiniteFrozenCore point - lrDA7TrueChannelCore point) +
      (lrDA7TrueChannelCore point -
        lrBoundedDeepActualCoefficientQCore point) +
      (lrBoundedDeepActualCoefficientQCore point -
        lrLowKActualNormalized point) := by
  ring

theorem lrBoundedDeep_loss_of_four_stages
    {point : CertificatePoint} {finiteLoss channelLoss
      coefficientLoss directLoss : ℝ}
    (hfinite :
      lrDeterminantIdealCore (Real.log (1 / point.s))
          point.k point.chi - lrDA7FiniteFrozenCore point ≤ finiteLoss)
    (hchannel :
      lrDA7FiniteFrozenCore point - lrDA7TrueChannelCore point ≤ channelLoss)
    (hcoefficient :
      lrDA7TrueChannelCore point -
        lrBoundedDeepActualCoefficientQCore point ≤ coefficientLoss)
    (hdirect :
      lrBoundedDeepActualCoefficientQCore point -
        lrLowKActualNormalized point ≤ directLoss) :
    lrDeterminantIdealCore (Real.log (1 / point.s)) point.k point.chi -
        lrLowKActualNormalized point ≤
      finiteLoss + channelLoss + coefficientLoss + directLoss := by
  rw [lrBoundedDeep_four_stage_telescope]
  linarith

/-! ## Sign-safe direct remainder collector -/

noncomputable def lrBoundedDeepDirectOmegaCost
    (point : CertificatePoint) : ℝ :=
  lrDA7ChannelKappa point * point.s * lrLowerFaceR0Prime point.s /
    lrLowKNormalization point

/-- Minimal sign data which reduce the direct `r` restoration to its one
potentially adverse `Omega_r` term. -/
structure LRBoundedDeepDirectRemainderSigns
    (point : CertificatePoint) : Prop where
  d1_nonneg : 0 ≤ lrDeterminantD1 point
  d1_add_B_nonneg :
    0 ≤ lrDeterminantD1 point + lrCertificateBFlow point
  c0J1_nonneg : 0 ≤ lrDeterminantC0 point * lrDA7ChannelJ1 point
  rG_nonneg : 0 ≤ lrBoundedDeepRNormalizedG point
  rOmega_lower :
    -lrBoundedDeepDirectOmegaCost point ≤
      lrBoundedDeepRNormalizedOmega point
  rT_nonneg : 0 ≤ lrBoundedDeepRNormalizedT point
  favorable_nonneg :
    0 ≤ 4 * lrDeterminantDelta point * lrCertificateBFlow point *
      lrCertificateW point / lrLowKNormalization point

theorem lrBoundedDeep_remainderContribution_lower
    {point : CertificatePoint}
    (hsigns : LRBoundedDeepDirectRemainderSigns point) :
    -(lrDeterminantD1 point + lrCertificateBFlow point) *
        lrBoundedDeepDirectOmegaCost point ≤
      lrBoundedDeepRemainderContribution point := by
  have hDG :
      0 ≤ lrDeterminantD1 point * lrBoundedDeepRNormalizedG point :=
    mul_nonneg hsigns.d1_nonneg hsigns.rG_nonneg
  have hOmega := mul_le_mul_of_nonneg_left hsigns.rOmega_lower
    hsigns.d1_add_B_nonneg
  have hcT :
      0 ≤ (lrDeterminantC0 point * lrDA7ChannelJ1 point) *
        lrBoundedDeepRNormalizedT point :=
    mul_nonneg hsigns.c0J1_nonneg hsigns.rT_nonneg
  have hfavorable := hsigns.favorable_nonneg
  rw [lrBoundedDeep_remainderContribution_collected]
  linarith

theorem lrBoundedDeep_qCore_sub_actual_le_directCost
    {point : CertificatePoint}
    (hn : lrLowKNormalization point ≠ 0)
    (hidentify : LRBoundedDeepQChannelIdentification point)
    (hsigns : LRBoundedDeepDirectRemainderSigns point) :
    lrBoundedDeepActualCoefficientQCore point -
        lrLowKActualNormalized point ≤
      (lrDeterminantD1 point + lrCertificateBFlow point) *
        lrBoundedDeepDirectOmegaCost point := by
  have hactual := lrBoundedDeep_actual_eq_qCore_add_remainder hn hidentify
  have hlower := lrBoundedDeep_remainderContribution_lower hsigns
  rw [hactual]
  linarith

/-! ## Reuse of the true-channel scalar collector -/

noncomputable def lrBoundedDeepLowDeltaGLoss
    (point : CertificatePoint) : ℝ :=
  (51 / 50 : ℝ) * lrCertificateE point *
    (Real.log (1 / point.s) + point.s)

noncomputable def lrBoundedDeepHighDeltaGLoss
    (point : CertificatePoint) : ℝ :=
  lrCertificateE point / 80

noncomputable def lrBoundedDeepDeltaOmegaLoss
    (point : CertificatePoint) : ℝ :=
  (51 / 100 : ℝ) * point.s *
    (Real.log (1 / point.s) + 4 / 5)

noncomputable def lrBoundedDeepDeltaTLoss
    (point : CertificatePoint) : ℝ :=
  lrCertificateE point / 10

noncomputable def lrBoundedDeepChannelCoefficientLoss
    (point : CertificatePoint) : ℝ :=
  (3 / 5 : ℝ) * lrCertificateE point

noncomputable def lrBoundedDeepChannelPointwiseLoss
    (point : CertificatePoint) (deltaGLoss : ℝ) : ℝ :=
  deltaGLoss + lrBoundedDeepDeltaOmegaLoss point +
    lrBoundedDeepDeltaTLoss point +
    lrBoundedDeepChannelCoefficientLoss point

/-- Exact hypotheses consumed by `lrDA7_channel_scalar_core_lower`.  The
three common payments and the band-specific Delta-G payment remain visibly
separate. -/
structure LRBoundedDeepTrueChannelPayments
    (point : CertificatePoint) (deltaGLoss : ℝ) : Prop where
  normalization_ne : lrLowKNormalization point ≠ 0
  B_le_frozen : lrCertificateBFlow point ≤ lrDA7FiniteB point
  frozenS_nonpos : lrDA7FiniteS point ≤ 0
  deltaG :
    -(lrDeterminantD1 point * lrDA7ChannelDeltaG point /
      lrLowKNormalization point) ≤ deltaGLoss
  deltaOmega :
    -((lrDeterminantD1 point + lrCertificateBFlow point) *
      lrDA7ChannelDeltaOmega point / lrLowKNormalization point) ≤
        lrBoundedDeepDeltaOmegaLoss point
  deltaT :
    -(lrDA7ChannelC0Q point * lrDA7ChannelJ1 point *
      lrDA7ChannelDeltaT point / lrLowKNormalization point) ≤
        lrBoundedDeepDeltaTLoss point
  coefficient :
    (lrDA7FiniteC point * lrDA7ChannelJBar point -
        lrDA7ChannelC0Q point * lrDA7ChannelJ1 point) *
      lrDA7FiniteT point ≤ lrBoundedDeepChannelCoefficientLoss point

theorem lrBoundedDeep_trueChannel_loss
    {point : CertificatePoint} {deltaGLoss : ℝ}
    (hpay : LRBoundedDeepTrueChannelPayments point deltaGLoss) :
    lrDA7FiniteFrozenCore point - lrDA7TrueChannelCore point ≤
      lrBoundedDeepChannelPointwiseLoss point deltaGLoss := by
  have hscalar := lrDA7_channel_scalar_core_lower
    (D := lrDeterminantD1 point)
    (Bbar := lrDA7FiniteB point) (B := lrCertificateBFlow point)
    (cbar := lrDA7FiniteC point) (cq := lrDA7ChannelC0Q point)
    (Jbar := lrDA7ChannelJBar point) (J := lrDA7ChannelJ1 point)
    (p := lrDA7FiniteP point) (S := lrDA7FiniteS point)
    (t := lrDA7FiniteT point) (n := lrLowKNormalization point)
    (dG := lrDA7ChannelDeltaG point)
    (dOmega := lrDA7ChannelDeltaOmega point)
    (dT := lrDA7ChannelDeltaT point)
    (lossG := deltaGLoss)
    (lossOmega := lrBoundedDeepDeltaOmegaLoss point)
    (lossT := lrBoundedDeepDeltaTLoss point)
    (lossCoefficient := lrBoundedDeepChannelCoefficientLoss point)
    hpay.normalization_ne hpay.B_le_frozen hpay.frozenS_nonpos
    hpay.deltaG hpay.deltaOmega hpay.deltaT hpay.coefficient
  have hcore :
      lrDA7FiniteFrozenCore point -
          lrBoundedDeepChannelPointwiseLoss point deltaGLoss ≤
        lrDA7TrueChannelCore point := by
    simpa [lrDA7FiniteFrozenCore, lrDA7TrueChannelCore,
      lrDA7ChannelP, lrDA7ChannelS, lrDA7ChannelT,
      lrDA7FiniteC, lrDA7ChannelJBar, lrDA7ChannelJ1,
      lrBoundedDeepChannelPointwiseLoss] using hscalar
  linarith

/-! ## Rational endpoints -/

noncomputable def lrBoundedDeepLowFiniteEndpoint : ℝ :=
  27017301 / 2684354560

noncomputable def lrBoundedDeepHighFiniteEndpoint : ℝ :=
  8656817 / 440401920

noncomputable def lrBoundedDeepLowChannelEndpoint : ℝ :=
  (51 / 50 : ℝ) * (1 / 2 ^ 10) * (49 / 5 + 1 / 2 ^ 14) +
    (51 / 100 : ℝ) * (1 / 2 ^ 14) * (49 / 5 + 4 / 5) +
    1 / 10240 + 3 / 5120

noncomputable def lrBoundedDeepHighChannelEndpoint : ℝ :=
  (1 / 2 ^ 7 : ℝ) / 80 +
    (51 / 100 : ℝ) * (1 / 2 ^ 14) * (49 / 5 + 4 / 5) +
    (1 / 2 ^ 7 : ℝ) / 10 + (3 / 5 : ℝ) * (1 / 2 ^ 7)

noncomputable def lrBoundedDeepEntropyCoefficientEndpoint : ℝ :=
  91 / 40960

noncomputable def lrBoundedDeepDirectRemainderEndpoint : ℝ :=
  1 / 1000000

theorem lrBoundedDeep_low_budget_sum :
    lrBoundedDeepLowFiniteEndpoint + lrBoundedDeepLowChannelEndpoint +
        lrBoundedDeepEntropyCoefficientEndpoint +
        lrBoundedDeepDirectRemainderEndpoint =
      (lrDeterminantLowBandRestorationBudget : ℝ) := by
  norm_num [lrBoundedDeepLowFiniteEndpoint,
    lrBoundedDeepLowChannelEndpoint,
    lrBoundedDeepEntropyCoefficientEndpoint,
    lrBoundedDeepDirectRemainderEndpoint,
    lrDeterminantLowBandRestorationBudget]

theorem lrBoundedDeep_high_budget_sum :
    lrBoundedDeepHighFiniteEndpoint + lrBoundedDeepHighChannelEndpoint +
        lrBoundedDeepEntropyCoefficientEndpoint +
        lrBoundedDeepDirectRemainderEndpoint =
      (lrDeterminantHighBandRestorationBudget : ℝ) := by
  norm_num [lrBoundedDeepHighFiniteEndpoint,
    lrBoundedDeepHighChannelEndpoint,
    lrBoundedDeepEntropyCoefficientEndpoint,
    lrBoundedDeepDirectRemainderEndpoint,
    lrDeterminantHighBandRestorationBudget]

/-! ## Honest analytic frontier -/

/-- Every not-yet-integrated analytic lemma required by the exact scaffold.
The `remainderSigns` and `direct*Endpoint` fields isolate the remaining
determinant-level `Q=q+r` work explicitly. -/
structure LRBoundedDeepRestorationAnalyticInputs : Prop where
  finiteLow : ∀ point : CertificatePoint,
    LRHighShapeInterior point →
    LRHighShapeVRelevant point →
    LRDeterminantBoundedDeepCompactRegion point →
    point.k ≤ 16 →
    lrDeterminantIdealCore (Real.log (1 / point.s))
          point.k point.chi - lrDA7FiniteFrozenCore point ≤
      lrBoundedDeepLowFiniteEndpoint
  finiteHigh : ∀ point : CertificatePoint,
    LRHighShapeInterior point →
    LRHighShapeVRelevant point →
    LRDeterminantBoundedDeepCompactRegion point →
    16 ≤ point.k →
    lrDeterminantIdealCore (Real.log (1 / point.s))
          point.k point.chi - lrDA7FiniteFrozenCore point ≤
      lrBoundedDeepHighFiniteEndpoint
  channelLow : ∀ point : CertificatePoint,
    LRHighShapeInterior point →
    LRHighShapeVRelevant point →
    LRDeterminantBoundedDeepCompactRegion point →
    point.k ≤ 16 →
    LRBoundedDeepTrueChannelPayments point
      (lrBoundedDeepLowDeltaGLoss point)
  channelHigh : ∀ point : CertificatePoint,
    LRHighShapeInterior point →
    LRHighShapeVRelevant point →
    LRDeterminantBoundedDeepCompactRegion point →
    16 ≤ point.k →
    LRBoundedDeepTrueChannelPayments point
      (lrBoundedDeepHighDeltaGLoss point)
  channelLowEndpoint : ∀ point : CertificatePoint,
    LRHighShapeInterior point →
    LRDeterminantBoundedDeepCompactRegion point →
    point.k ≤ 16 →
    lrBoundedDeepChannelPointwiseLoss point
        (lrBoundedDeepLowDeltaGLoss point) ≤
      lrBoundedDeepLowChannelEndpoint
  channelHighEndpoint : ∀ point : CertificatePoint,
    LRHighShapeInterior point →
    LRDeterminantBoundedDeepCompactRegion point →
    16 ≤ point.k →
    lrBoundedDeepChannelPointwiseLoss point
        (lrBoundedDeepHighDeltaGLoss point) ≤
      lrBoundedDeepHighChannelEndpoint
  entropyCoefficient : ∀ point : CertificatePoint,
    LRHighShapeInterior point →
    LRHighShapeVRelevant point →
    LRDeterminantBoundedDeepCompactRegion point →
    lrDA7TrueChannelCore point -
        lrBoundedDeepActualCoefficientQCore point ≤
      lrBoundedDeepEntropyCoefficientEndpoint
  remainderSigns : ∀ point : CertificatePoint,
    LRHighShapeInterior point →
    LRHighShapeVRelevant point →
    LRDeterminantBoundedDeepCompactRegion point →
    LRBoundedDeepDirectRemainderSigns point
  directLowEndpoint : ∀ point : CertificatePoint,
    LRHighShapeInterior point →
    LRDeterminantBoundedDeepCompactRegion point →
    point.k ≤ 16 →
    (lrDeterminantD1 point + lrCertificateBFlow point) *
        lrBoundedDeepDirectOmegaCost point ≤
      lrBoundedDeepDirectRemainderEndpoint
  directHighEndpoint : ∀ point : CertificatePoint,
    LRHighShapeInterior point →
    LRDeterminantBoundedDeepCompactRegion point →
    16 ≤ point.k →
    (lrDeterminantD1 point + lrCertificateBFlow point) *
        lrBoundedDeepDirectOmegaCost point ≤
      lrBoundedDeepDirectRemainderEndpoint

/-- Exact output type consumed by the bounded-deep ideal adapter. -/
structure LRDeterminantBoundedDeepRestorationLosses : Prop where
  low : ∀ point : CertificatePoint,
    LRHighShapeInterior point →
    LRHighShapeVRelevant point →
    LRDeterminantBoundedDeepCompactRegion point →
    point.k ≤ 16 →
    lrDeterminantIdealCore (Real.log (1 / point.s))
          point.k point.chi - lrLowKActualNormalized point ≤
      (lrDeterminantLowBandRestorationBudget : ℝ)
  high : ∀ point : CertificatePoint,
    LRHighShapeInterior point →
    LRHighShapeVRelevant point →
    LRDeterminantBoundedDeepCompactRegion point →
    16 ≤ point.k →
    lrDeterminantIdealCore (Real.log (1 / point.s))
          point.k point.chi - lrLowKActualNormalized point ≤
      (lrDeterminantHighBandRestorationBudget : ℝ)

/-- Kernel-only assembly of the bounded-deep restoration losses from the
named analytic frontier above. -/
theorem lrDeterminantBoundedDeepRestorationLosses_of_analyticInputs
    (inputs : LRBoundedDeepRestorationAnalyticInputs) :
    LRDeterminantBoundedDeepRestorationLosses := by
  constructor
  · intro point hinterior hrelevant hregion hk
    have hfinite := inputs.finiteLow point hinterior hrelevant hregion hk
    have hpayments := inputs.channelLow point hinterior hrelevant hregion hk
    have hchannelRaw := lrBoundedDeep_trueChannel_loss hpayments
    have hchannelEndpoint :=
      inputs.channelLowEndpoint point hinterior hregion hk
    have hchannel :
        lrDA7FiniteFrozenCore point - lrDA7TrueChannelCore point ≤
          lrBoundedDeepLowChannelEndpoint :=
      hchannelRaw.trans hchannelEndpoint
    have hcoefficient :=
      inputs.entropyCoefficient point hinterior hrelevant hregion
    have hidentify := lrBoundedDeep_qChannelIdentification hinterior
    have hsigns := inputs.remainderSigns point hinterior hrelevant hregion
    have hn := (lrLowKNormalization_pos hinterior).ne'
    have hdirectRaw := lrBoundedDeep_qCore_sub_actual_le_directCost
      hn hidentify hsigns
    have hdirectEndpoint :=
      inputs.directLowEndpoint point hinterior hregion hk
    have hdirect :
        lrBoundedDeepActualCoefficientQCore point -
            lrLowKActualNormalized point ≤
          lrBoundedDeepDirectRemainderEndpoint :=
      hdirectRaw.trans hdirectEndpoint
    have hsum := lrBoundedDeep_loss_of_four_stages
      hfinite hchannel hcoefficient hdirect
    calc
      lrDeterminantIdealCore (Real.log (1 / point.s))
            point.k point.chi - lrLowKActualNormalized point ≤
          lrBoundedDeepLowFiniteEndpoint +
            lrBoundedDeepLowChannelEndpoint +
            lrBoundedDeepEntropyCoefficientEndpoint +
            lrBoundedDeepDirectRemainderEndpoint := hsum
      _ = (lrDeterminantLowBandRestorationBudget : ℝ) :=
        lrBoundedDeep_low_budget_sum
  · intro point hinterior hrelevant hregion hk
    have hfinite := inputs.finiteHigh point hinterior hrelevant hregion hk
    have hpayments := inputs.channelHigh point hinterior hrelevant hregion hk
    have hchannelRaw := lrBoundedDeep_trueChannel_loss hpayments
    have hchannelEndpoint :=
      inputs.channelHighEndpoint point hinterior hregion hk
    have hchannel :
        lrDA7FiniteFrozenCore point - lrDA7TrueChannelCore point ≤
          lrBoundedDeepHighChannelEndpoint :=
      hchannelRaw.trans hchannelEndpoint
    have hcoefficient :=
      inputs.entropyCoefficient point hinterior hrelevant hregion
    have hidentify := lrBoundedDeep_qChannelIdentification hinterior
    have hsigns := inputs.remainderSigns point hinterior hrelevant hregion
    have hn := (lrLowKNormalization_pos hinterior).ne'
    have hdirectRaw := lrBoundedDeep_qCore_sub_actual_le_directCost
      hn hidentify hsigns
    have hdirectEndpoint :=
      inputs.directHighEndpoint point hinterior hregion hk
    have hdirect :
        lrBoundedDeepActualCoefficientQCore point -
            lrLowKActualNormalized point ≤
          lrBoundedDeepDirectRemainderEndpoint :=
      hdirectRaw.trans hdirectEndpoint
    have hsum := lrBoundedDeep_loss_of_four_stages
      hfinite hchannel hcoefficient hdirect
    calc
      lrDeterminantIdealCore (Real.log (1 / point.s))
            point.k point.chi - lrLowKActualNormalized point ≤
          lrBoundedDeepHighFiniteEndpoint +
            lrBoundedDeepHighChannelEndpoint +
            lrBoundedDeepEntropyCoefficientEndpoint +
            lrBoundedDeepDirectRemainderEndpoint := hsum
      _ = (lrDeterminantHighBandRestorationBudget : ℝ) :=
        lrBoundedDeep_high_budget_sum

end CourtadeKumar
