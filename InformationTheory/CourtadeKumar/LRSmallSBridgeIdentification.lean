import InformationTheory.CourtadeKumar.LRSmallSBridgeDecomposition
import InformationTheory.CourtadeKumar.LRSmallSBridgeCoreInterval

/-!
# Identification of the small-`s` coordinates

These lemmas identify the exact outer coefficients in the cancellation
coordinates with the `B` and `D` used by the frozen replay.  They also record
the elementary physical ranges needed by both restoration payments.
-/

open Set

namespace CourtadeKumar

lemma lrSmallSBridge_e_mem
    {s k : ℝ} (hs : s ∈ Ioc (0 : ℝ) (1 / 16384))
    (hk : k ∈ Icc (1 / 4 : ℝ) 4) :
    s * k ∈ Ioo (0 : ℝ) 1 := by
  have he := lrSmallSBridgeE_upper hs hk
  exact ⟨he.1, he.2.trans_lt (by norm_num)⟩

lemma lrSmallSBridge_x_pos
    {s k chi : ℝ} (hs : s ∈ Ioc (0 : ℝ) (1 / 16384))
    (hk : k ∈ Icc (1 / 4 : ℝ) 4)
    (hchi : chi ∈ Icc (0 : ℝ) 1) :
    0 < lrCertificateX (⟨s, k, chi⟩ : CertificatePoint) := by
  have he := lrSmallSBridge_e_mem hs hk
  change 0 < 1 - chi * (s * k)
  have hprod : chi * (s * k) ≤ s * k := by
    simpa using mul_le_mul_of_nonneg_right hchi.2 he.1.le
  exact sub_pos.mpr (hprod.trans_lt he.2)

lemma lrSmallSBridge_v_mem
    {s k chi : ℝ} (hs : s ∈ Ioc (0 : ℝ) (1 / 16384))
    (hk : k ∈ Icc (1 / 4 : ℝ) 4)
    (hchi : chi ∈ Icc (0 : ℝ) 1) :
    lrCertificateV (⟨s, k, chi⟩ : CertificatePoint) ∈ Ioc (0 : ℝ) 1 := by
  let point : CertificatePoint := ⟨s, k, chi⟩
  have he := lrSmallSBridge_e_mem hs hk
  have hx := lrSmallSBridge_x_pos hs hk hchi
  have hnumNonneg : 0 ≤ 1 - lrCertificateE point := by
    change 0 ≤ 1 - s * k
    exact sub_nonneg.mpr he.2.le
  have hnumLeX : 1 - lrCertificateE point ≤ lrCertificateX point := by
    change 1 - s * k ≤ 1 - chi * (s * k)
    have hchie : chi * (s * k) ≤ s * k := by
      simpa using mul_le_mul_of_nonneg_right hchi.2 he.1.le
    linarith
  have hradPos : 0 <
      (1 - lrCertificateE point) / lrCertificateX point :=
    div_pos (sub_pos.mpr he.2) hx
  have hradLe :
      (1 - lrCertificateE point) / lrCertificateX point ≤ 1 := by
    rw [div_le_one hx]
    exact hnumLeX
  constructor
  · unfold lrCertificateV
    exact Real.sqrt_pos.2 hradPos
  · unfold lrCertificateV
    nlinarith [Real.sq_sqrt hradPos.le, Real.sqrt_nonneg
      ((1 - lrCertificateE point) / lrCertificateX point)]

lemma lrCertificateD_eq_smallSBridgeD
    {s k chi : ℝ} (hs : s ∈ Ioc (0 : ℝ) (1 / 16384))
    (hk : k ∈ Icc (1 / 4 : ℝ) 4) :
    lrCertificateD (⟨s, k, chi⟩ : CertificatePoint) =
      lrSmallSBridgeD s k := by
  have hsPos := hs.1
  have hkPos : 0 < k := (by norm_num : (0 : ℝ) < 1 / 4).trans_le hk.1
  have hR : 0 ≤ 1 - s := by nlinarith [hs.2]
  have houter : 0 < 1 + (1 - s) * k := by positivity
  have hb : lrCertificateB s (s * k) =
      s * (1 + (1 - s) * k) := by
    unfold lrCertificateB
    ring
  unfold lrCertificateD lrCertificateA lrCertificateAValue
    lrCertificateBFlow lrCertificateBFlowValue lrCertificateE
    lrSmallSBridgeD
  rw [hb, Real.log_mul hsPos.ne' houter.ne',
    Real.log_mul hsPos.ne' hkPos.ne',
    Real.log_div houter.ne' hkPos.ne']
  ring

lemma lrCertificateBFlow_eq_smallSBridgeB
    {s k chi : ℝ} (hs : s ∈ Ioc (0 : ℝ) (1 / 16384))
    (hk : k ∈ Icc (1 / 4 : ℝ) 4) :
    lrCertificateBFlow (⟨s, k, chi⟩ : CertificatePoint) =
      Real.log (1 / s) / 2 +
        lrSmallSBridgeCoreB (⟨s, k, chi⟩ : CertificatePoint) := by
  have hsPos := hs.1
  have hR : 0 ≤ 1 - s := by nlinarith [hs.2]
  have houter : 0 < 1 + (1 - s) * k := by
    have hkNonneg : 0 ≤ k :=
      (by norm_num : (0 : ℝ) ≤ 1 / 4).trans hk.1
    positivity
  have hb : lrCertificateB s (s * k) =
      s * (1 + (1 - s) * k) := by
    unfold lrCertificateB
    ring
  have hlogInv : Real.log (1 / s) = -Real.log s := by
    rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) hsPos.ne']
    norm_num
  unfold lrCertificateBFlow lrCertificateBFlowValue lrCertificateE
    lrSmallSBridgeCoreB
  rw [hb, Real.log_mul hsPos.ne' houter.ne', hlogInv]
  ring

lemma lrCertificateBFlow_nonneg_smallS
    {s k chi : ℝ} (hs : s ∈ Ioc (0 : ℝ) (1 / 16384))
    (hk : k ∈ Icc (1 / 4 : ℝ) 4)
    (hchi : chi ∈ Icc (0 : ℝ) 1) :
    0 ≤ lrCertificateBFlow (⟨s, k, chi⟩ : CertificatePoint) := by
  let point : CertificatePoint := ⟨s, k, chi⟩
  have hv := lrSmallSBridge_v_mem hs hk hchi
  have he := lrSmallSBridge_e_mem hs hk
  have hR : point.s ∈ Ioo (0 : ℝ) 1 :=
    ⟨hs.1, hs.2.trans_lt (by norm_num)⟩
  have hbMem := lrCertificateB_mem_Ioo hR he
  unfold lrCertificateBFlow lrCertificateBFlowValue
  have hlogOne : 0 ≤ Real.log (1 + lrCertificateV point) :=
    (Real.log_pos (by linarith [hv.1])).le
  have hlogB : Real.log (lrCertificateB point.s (lrCertificateE point)) ≤ 0 :=
    Real.log_nonpos hbMem.1.le hbMem.2.le
  linarith

lemma lrSmallSBridge_log_four :
    Real.log (4 : ℝ) = 2 * Real.log 2 := by
  rw [show (4 : ℝ) = 2 * 2 by norm_num,
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
      (by norm_num : (2 : ℝ) ≠ 0)]
  ring

/-- At frozen radial weight `v=1`, the logarithmic part of `G_t` is the
`n g` term in (M28)--(M29). -/
lemma lrSmallSBridgeQ0G_frozen_eq
    {s k chi : ℝ} (hs : s ∈ Ioc (0 : ℝ) (1 / 16384))
    (hk : k ∈ Icc (1 / 4 : ℝ) 4)
    (hchi : chi ∈ Icc (0 : ℝ) 1) :
    lrLowerFaceQ0 (chi * (s * k)) + lrLowerFaceQ0 (s * k) =
      s * k * (1 + chi) / 4 *
        lrSmallSBridgeG k chi (Real.log (1 / s)) := by
  have hsPos := hs.1
  have hkPos : 0 < k := (by norm_num : (0 : ℝ) < 1 / 4).trans_le hk.1
  have hePos : 0 < s * k := mul_pos hsPos hkPos
  have hlogE : Real.log (s * k) = Real.log s + Real.log k :=
    Real.log_mul hsPos.ne' hkPos.ne'
  have hlogInv : Real.log (1 / s) = -Real.log s := by
    rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) hsPos.ne']
    norm_num
  have hlogFour := lrSmallSBridge_log_four
  rcases hchi.1.eq_or_lt with rfl | hchiPos
  · simp only [zero_mul]
    unfold lrLowerFaceQ0 lrSmallSBridgeG lrSmallSBridgeQChi
    rw [Real.log_div (by norm_num : (4 : ℝ) ≠ 0) hePos.ne',
      hlogE, hlogInv, hlogFour]
    norm_num
    field_simp [hsPos.ne', hkPos.ne'] <;>
      (ring_nf; simp [hsPos.ne', hkPos.ne'])
  · have hchiEPos : 0 < chi * (s * k) := mul_pos hchiPos hePos
    have hlogChiE : Real.log (chi * (s * k)) =
        Real.log chi + Real.log s + Real.log k := by
      rw [Real.log_mul hchiPos.ne' hePos.ne', hlogE]
      ring
    unfold lrLowerFaceQ0 lrSmallSBridgeG lrSmallSBridgeQChi
    rw [Real.log_div (by norm_num : (4 : ℝ) ≠ 0) hchiEPos.ne',
      Real.log_div (by norm_num : (4 : ℝ) ≠ 0) hePos.ne',
      hlogChiE, hlogE, hlogInv, hlogFour]
    field_simp [show 1 + chi ≠ 0 by linarith]
    ring

/-- At frozen radial weight `v=1`, the `q₀` noise collection is the
`n S+s/2` term implicit in (M29). -/
lemma lrSmallSBridgePWQ0_frozen_eq
    {s k chi : ℝ} (hs : s ∈ Ioc (0 : ℝ) (1 / 16384))
    (hk : k ∈ Icc (1 / 4 : ℝ) 4)
    (hchi : chi ∈ Icc (0 : ℝ) 1) :
    lrLowerFacePWQ0 s k chi 1 =
      s * k * (1 + chi) / 4 *
          lrSmallSBridgeS s k chi (Real.log (1 / s)) + s / 2 := by
  have hsIoo : s ∈ Ioo (0 : ℝ) 1 :=
    ⟨hs.1, hs.2.trans_lt (by norm_num)⟩
  have hkPos : 0 < k := (by norm_num : (0 : ℝ) < 1 / 4).trans_le hk.1
  have he := lrSmallSBridge_e_mem hs hk
  have houterPos : 0 < 1 + (1 - s) * k := by
    have hR : 0 ≤ 1 - s := hsIoo.2.le |> sub_nonneg.mpr
    positivity
  have hlogOuter :
      Real.log ((1 + (1 - s) * k) / k) =
        Real.log (1 + (1 - s) * k) - Real.log k := by
    rw [Real.log_div houterPos.ne' hkPos.ne']
  rcases hchi.1.eq_or_lt with rfl | hchiPos
  · unfold lrLowerFacePWQ0
    simp only [zero_mul, div_one]
    rw [lrLowerFaceOmegaQ0_zero hs.1,
      lrLowerFaceOmegaQ0_sk_eq hsIoo hkPos he.2, hlogOuter]
    unfold lrSmallSBridgeS lrSmallSBridgeP lrSmallSBridgeG
      lrSmallSBridgeAR lrSmallSBridgeQChi
    simp only [zero_mul, zero_div, zero_add]
    field_simp
    ring
  · have hchiKPos : 0 < chi * k := mul_pos hchiPos hkPos
    have hchiE : chi * (s * k) = s * (chi * k) := by ring
    have hchiELt : s * (chi * k) < 1 := by
      rw [← hchiE]
      exact (mul_le_of_le_one_left he.1.le hchi.2).trans_lt he.2
    have hinnerPos : 0 < 1 + (1 - s) * k * chi := by
      have hR : 0 ≤ 1 - s := sub_nonneg.mpr hsIoo.2.le
      positivity
    have hlogInner :
        Real.log ((1 + (1 - s) * (chi * k)) / (chi * k)) =
          Real.log (1 + (1 - s) * k * chi) -
            Real.log chi - Real.log k := by
      have hinnerEq :
          1 + (1 - s) * (chi * k) = 1 + (1 - s) * k * chi := by ring
      rw [hinnerEq, Real.log_div hinnerPos.ne' hchiKPos.ne',
        Real.log_mul hchiPos.ne' hkPos.ne']
      ring
    unfold lrLowerFacePWQ0
    rw [hchiE,
      lrLowerFaceOmegaQ0_sk_eq hsIoo hchiKPos hchiELt,
      lrLowerFaceOmegaQ0_sk_eq hsIoo hkPos he.2,
      hlogInner, hlogOuter]
    unfold lrSmallSBridgeS lrSmallSBridgeP lrSmallSBridgeG
      lrSmallSBridgeAR lrSmallSBridgeQChi
    field_simp [show 1 + chi ≠ 0 by linarith]
    ring

/-- The frozen abstract channel is exactly `s` times the normalized replay
target.  This closes the algebraic identification behind (M29). -/
theorem lrSmallSBridgeQ0_frozenChannel_eq
    {s k chi : ℝ} (hs : s ∈ Ioc (0 : ℝ) (1 / 16384))
    (hk : k ∈ Icc (1 / 4 : ℝ) 4)
    (hchi : chi ∈ Icc (0 : ℝ) 1) :
    lrSmallSBridgeFrozenChannelReserve
        (lrCertificateD (⟨s, k, chi⟩ : CertificatePoint))
        (lrCertificateBFlow (⟨s, k, chi⟩ : CertificatePoint))
        (lrLowerFaceOmegaQ0 s 0)
        (lrLowerFaceQ0 (chi * (s * k)) + lrLowerFaceQ0 (s * k))
        (lrLowerFacePWQ0 s k chi 1) =
      s * lrSmallSBridgeFrozen s k chi (Real.log (1 / s))
        (lrSmallSBridgeCoreB (⟨s, k, chi⟩ : CertificatePoint)) := by
  rw [lrCertificateD_eq_smallSBridgeD hs hk,
    lrCertificateBFlow_eq_smallSBridgeB hs hk,
    lrLowerFaceOmegaQ0_zero hs.1,
    lrSmallSBridgeQ0G_frozen_eq hs hk hchi,
    lrSmallSBridgePWQ0_frozen_eq hs hk hchi]
  unfold lrSmallSBridgeFrozenChannelReserve lrSmallSBridgeFrozen
    lrSmallSBridgeS
  ring

/-- Exact change in the `q₀` logarithmic collection when restoring the
true radial weight. -/
noncomputable def lrSmallSBridgeQ0DeltaG (point : CertificatePoint) : ℝ :=
  lrCertificateG0 (lrCertificateV point) +
    lrLowerFaceQ0 (lrCertificateE point) *
      (1 / lrCertificateV point - 1)

/-- Exact change in the `q₀` noise collection when restoring the true
radial weight. -/
noncomputable def lrSmallSBridgeQ0DeltaP (point : CertificatePoint) : ℝ :=
  lrLowerFaceOmegaQ0 point.s (lrCertificateE point) *
    (1 / lrCertificateV point - 1)

lemma lrSmallSBridgeQ0G_eq_frozen_add_delta (point : CertificatePoint) :
    lrSmallSBridgeQ0G point =
      (lrLowerFaceQ0 (lrCertificateY0 point) +
        lrLowerFaceQ0 (lrCertificateE point)) +
        lrSmallSBridgeQ0DeltaG point := by
  unfold lrSmallSBridgeQ0G lrSmallSBridgeQ0DeltaG
  ring

lemma lrSmallSBridgePWQ0_eq_frozen_add_delta (point : CertificatePoint) :
    lrLowerFacePWQ0 point.s point.k point.chi (lrCertificateV point) =
      lrLowerFacePWQ0 point.s point.k point.chi 1 +
        lrSmallSBridgeQ0DeltaP point := by
  unfold lrLowerFacePWQ0 lrSmallSBridgeQ0DeltaP lrCertificateE
  ring

/-- A cancellation-safe elementary lower bound for the radial logarithmic
term.  The small-`s` bridge has `v` much closer to one than the stated
range, so this deliberately leaves ample slack. -/
lemma lrCertificateG0_lower_quadratic
    {v : ℝ} (hv : v ∈ Icc (1 / 2 : ℝ) 1) :
    -2 * (1 - v) ^ 2 ≤ lrCertificateG0 v := by
  have hvPos : 0 < v := (by norm_num : (0 : ℝ) < 1 / 2).trans_le hv.1
  have hmeanPos : 0 < (1 + v) / 2 := by positivity
  have hlogMean := Real.one_sub_inv_le_log_of_pos hmeanPos
  have hfactor : 0 ≤ 1 + 1 / v := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hlogMean hfactor
  have hleft :
      (1 + 1 / v) * (1 - ((1 + v) / 2)⁻¹) =
        -(1 - v) / v := by
    field_simp [hvPos.ne', (by linarith : 1 + v ≠ 0)]
    ring
  rw [hleft] at hscaled
  have hlogMeanEq :
      Real.log ((1 + v) / 2) = Real.log (1 + v) - Real.log 2 := by
    rw [Real.log_div (by linarith : 1 + v ≠ 0)
      (by norm_num : (2 : ℝ) ≠ 0)]
  rw [hlogMeanEq] at hscaled
  have hlogV := Real.log_le_sub_one_of_pos hvPos
  have hcore :
      -((1 - v) ^ 2 / v) ≤ lrCertificateG0 v := by
    unfold lrCertificateG0
    have hquot : -(1 - v) / v + (1 - v) =
        -((1 - v) ^ 2 / v) := by
      field_simp [hvPos.ne']
      ring
    rw [← hquot]
    nlinarith
  have hinvLe : 1 / v ≤ 2 := by
    rw [div_le_iff₀ hvPos]
    nlinarith [hv.1]
  have hsquare := mul_le_mul_of_nonneg_left hinvLe (sq_nonneg (1 - v))
  have hloss : -(2 * (1 - v) ^ 2) ≤ -((1 - v) ^ 2 / v) := by
    have : (1 - v) ^ 2 / v ≤ 2 * (1 - v) ^ 2 := by
      calc
        (1 - v) ^ 2 / v = (1 - v) ^ 2 * (1 / v) := by ring
        _ ≤ (1 - v) ^ 2 * 2 := hsquare
        _ = 2 * (1 - v) ^ 2 := by ring
    linarith
  calc
    -2 * (1 - v) ^ 2 = -(2 * (1 - v) ^ 2) := by ring
    _ ≤ lrCertificateG0 v := hloss.trans hcore

lemma lrLowerFaceQ0_nonneg_of_mem
    {y : ℝ} (hy : y ∈ Ioc (0 : ℝ) 1) :
    0 ≤ lrLowerFaceQ0 y := by
  have harg : 1 < 4 / y := by
    rw [lt_div_iff₀ hy.1]
    nlinarith [hy.2]
  have hlog : 0 ≤ Real.log (4 / y) := (Real.log_pos harg).le
  unfold lrLowerFaceQ0
  exact mul_nonneg (div_nonneg hy.1.le (by norm_num)) (by linarith)

lemma lrSmallSBridgeQ0DeltaP_nonneg
    {s k chi : ℝ} (hs : s ∈ Ioc (0 : ℝ) (1 / 16384))
    (hk : k ∈ Icc (1 / 4 : ℝ) 4)
    (hchi : chi ∈ Icc (0 : ℝ) 1) :
    0 ≤ lrSmallSBridgeQ0DeltaP
      (⟨s, k, chi⟩ : CertificatePoint) := by
  have hsIoo : s ∈ Ioo (0 : ℝ) 1 :=
    ⟨hs.1, hs.2.trans_lt (by norm_num)⟩
  have he := lrSmallSBridge_e_mem hs hk
  have hv := lrSmallSBridge_v_mem hs hk hchi
  have homega := lrLowerFaceOmegaQ0_nonneg hsIoo he
  have hinv : 1 ≤ 1 / lrCertificateV
      (⟨s, k, chi⟩ : CertificatePoint) := by
    rw [le_div_iff₀ hv.1]
    simpa using hv.2
  unfold lrSmallSBridgeQ0DeltaP lrCertificateE
  exact mul_nonneg homega (sub_nonneg.mpr hinv)

lemma lrSmallSBridgeQ0DeltaG_lower
    {s k chi : ℝ} (hs : s ∈ Ioc (0 : ℝ) (1 / 16384))
    (hk : k ∈ Icc (1 / 4 : ℝ) 4)
    (hchi : chi ∈ Icc (0 : ℝ) 1) :
    -2 * (1 - lrCertificateV
        (⟨s, k, chi⟩ : CertificatePoint)) ^ 2 ≤
      lrSmallSBridgeQ0DeltaG
        (⟨s, k, chi⟩ : CertificatePoint) := by
  let point : CertificatePoint := ⟨s, k, chi⟩
  have he := lrSmallSBridge_e_mem hs hk
  have hv := lrSmallSBridge_v_mem hs hk hchi
  have hgap := lrSmallSBridge_one_sub_v_le hs hk hchi
  have heUpper := lrSmallSBridgeE_upper hs hk
  have hvHalf : lrCertificateV point ∈ Icc (1 / 2 : ℝ) 1 := by
    constructor
    · change 1 / 2 ≤ lrCertificateV
        (⟨s, k, chi⟩ : CertificatePoint)
      nlinarith [hgap, heUpper.2]
    · exact hv.2
  have hg0 := lrCertificateG0_lower_quadratic hvHalf
  have hq0 : 0 ≤ lrLowerFaceQ0 (lrCertificateE point) := by
    apply lrLowerFaceQ0_nonneg_of_mem
    simpa [point, lrCertificateE] using And.intro he.1 he.2.le
  have hinv : 1 ≤ 1 / lrCertificateV point := by
    rw [le_div_iff₀ hv.1]
    simpa using hv.2
  have hrest : 0 ≤ lrLowerFaceQ0 (lrCertificateE point) *
      (1 / lrCertificateV point - 1) :=
    mul_nonneg hq0 (sub_nonneg.mpr hinv)
  unfold lrSmallSBridgeQ0DeltaG
  exact hg0.trans (le_add_of_nonneg_right hrest)

lemma lrSmallSBridge_shape_correction_nonneg
    {s k chi : ℝ} (hs : s ∈ Ioc (0 : ℝ) (1 / 16384))
    (hk : k ∈ Icc (1 / 4 : ℝ) 4)
    (hchi : chi ∈ Icc (0 : ℝ) 1) :
    0 ≤ 1 - 2 *
      (lrCertificateV (⟨s, k, chi⟩ : CertificatePoint) /
        (1 + lrCertificateV (⟨s, k, chi⟩ : CertificatePoint))) *
      lrCertificateX (⟨s, k, chi⟩ : CertificatePoint) := by
  let point : CertificatePoint := ⟨s, k, chi⟩
  let v := lrCertificateV point
  let x := lrCertificateX point
  have hv := lrSmallSBridge_v_mem hs hk hchi
  have hxPos := lrSmallSBridge_x_pos hs hk hchi
  have he := lrSmallSBridge_e_mem hs hk
  have hv' : v ∈ Ioc (0 : ℝ) 1 := by simpa [v, point] using hv
  have hxLe : x ≤ 1 := by
    unfold x lrCertificateX lrCertificateE point
    exact sub_le_self _ (mul_nonneg hchi.1 he.1.le)
  have hden : 0 < 1 + v := by linarith [hv'.1]
  have hfracNonneg : 0 ≤ 2 * v / (1 + v) :=
    div_nonneg (mul_nonneg (by norm_num) hv'.1.le) hden.le
  have hfracLe : 2 * v / (1 + v) ≤ 1 := by
    rw [div_le_one hden]
    linarith [hv'.2]
  have hmul : (2 * v / (1 + v)) * x ≤ 1 := by
    calc
      (2 * v / (1 + v)) * x ≤ (2 * v / (1 + v)) * 1 :=
        mul_le_mul_of_nonneg_left hxLe hfracNonneg
      _ ≤ 1 := by simpa using hfracLe
  change 0 ≤ 1 - 2 * (v / (1 + v)) * x
  have heq : 2 * (v / (1 + v)) * x =
      (2 * v / (1 + v)) * x := by ring
  rw [heq]
  exact sub_nonneg.mpr hmul

/-- Fully identified form of (M31): restoring the true `q₀` channel from
the frozen replay costs at most `epsilon_v` after normalization by `s`. -/
theorem lrSmallSBridge_q0_restoration_lower
    {s k chi : ℝ} (hs : s ∈ Ioc (0 : ℝ) (1 / 16384))
    (hk : k ∈ Icc (1 / 4 : ℝ) 4)
    (hchi : chi ∈ Icc (0 : ℝ) 1) :
    lrSmallSBridgeFrozen s k chi (Real.log (1 / s))
        (lrSmallSBridgeCoreB (⟨s, k, chi⟩ : CertificatePoint)) -
        lrSmallSBridgeEpsilonV ≤
      lrSmallSBridgeChannelReserve
        (lrCertificateD (⟨s, k, chi⟩ : CertificatePoint))
        (lrCertificateBFlow (⟨s, k, chi⟩ : CertificatePoint))
        (lrCertificateV (⟨s, k, chi⟩ : CertificatePoint))
        (lrCertificateX (⟨s, k, chi⟩ : CertificatePoint))
        (lrLowerFaceOmegaQ0 s 0)
        (lrSmallSBridgeQ0G (⟨s, k, chi⟩ : CertificatePoint))
        (lrLowerFacePWQ0 s k chi
          (lrCertificateV (⟨s, k, chi⟩ : CertificatePoint))) / s := by
  let point : CertificatePoint := ⟨s, k, chi⟩
  let v := lrCertificateV point
  let a := (1 - v) / (1 + v)
  let d := 1 - v
  have hv := lrSmallSBridge_v_mem hs hk hchi
  have hv' : v ∈ Ioc (0 : ℝ) 1 := by simpa [v, point] using hv
  have hvNe : v ≠ -1 := by linarith [hv'.1]
  have hDmem : lrCertificateD point ∈ Icc (0 : ℝ) (5 / 6) := by
    rw [lrCertificateD_eq_smallSBridgeD hs hk]
    exact lrSmallSBridgeD_mem hs hk
  have hB : 0 ≤ lrCertificateBFlow point := by
    simpa [point] using lrCertificateBFlow_nonneg_smallS hs hk hchi
  have hdeltaG : -2 * d ^ 2 ≤ lrSmallSBridgeQ0DeltaG point := by
    simpa [d, v, point] using lrSmallSBridgeQ0DeltaG_lower hs hk hchi
  have hdeltaP : 0 ≤ lrSmallSBridgeQ0DeltaP point := by
    simpa [point] using lrSmallSBridgeQ0DeltaP_nonneg hs hk hchi
  have hshape : 0 ≤ 1 - 2 * (v / (1 + v)) * lrCertificateX point := by
    simpa [v, point] using lrSmallSBridge_shape_correction_nonneg hs hk hchi
  have hnorm := lrSmallSBridgeChannelReserve_normalized_lower
    (s := s) (D := lrCertificateD point)
    (B := lrCertificateBFlow point) (v := v)
    (x := lrCertificateX point)
    (G₀ := lrLowerFaceQ0 (lrCertificateY0 point) +
      lrLowerFaceQ0 (lrCertificateE point))
    (P₀ := lrLowerFacePWQ0 point.s point.k point.chi 1)
    (deltaG := lrSmallSBridgeQ0DeltaG point)
    (deltaP := lrSmallSBridgeQ0DeltaP point)
    (a := a) (d := d) hs.1 hvNe rfl hDmem.1 hB hdeltaG hdeltaP hshape
  rw [← lrSmallSBridgeQ0G_eq_frozen_add_delta point,
    ← lrSmallSBridgePWQ0_eq_frozen_add_delta point] at hnorm
  have hfrozen := lrSmallSBridgeQ0_frozenChannel_eq hs hk hchi
  have hfrozen' :
      lrSmallSBridgeFrozenChannelReserve
          (lrCertificateD point) (lrCertificateBFlow point)
          (lrLowerFaceOmegaQ0 point.s 0)
          (lrLowerFaceQ0 (lrCertificateY0 point) +
            lrLowerFaceQ0 (lrCertificateE point))
          (lrLowerFacePWQ0 point.s point.k point.chi 1) =
        s * lrSmallSBridgeFrozen s k chi (Real.log (1 / s))
          (lrSmallSBridgeCoreB point) := by
    simpa [point, lrCertificateY0, lrCertificateE] using hfrozen
  have homegaZero : lrLowerFaceOmegaQ0 point.s 0 = s / 4 := by
    simpa [point] using lrLowerFaceOmegaQ0_zero hs.1
  have hfrozenQuarter :
      lrSmallSBridgeFrozenChannelReserve
          (lrCertificateD point) (lrCertificateBFlow point) (s / 4)
          (lrLowerFaceQ0 (lrCertificateY0 point) +
            lrLowerFaceQ0 (lrCertificateE point))
          (lrLowerFacePWQ0 point.s point.k point.chi 1) =
        s * lrSmallSBridgeFrozen s k chi (Real.log (1 / s))
          (lrSmallSBridgeCoreB point) := by
    simpa [homegaZero] using hfrozen'
  rw [hfrozenQuarter] at hnorm
  have hd : d ∈ Icc (0 : ℝ) ((501 / 1000) * (s * k)) := by
    constructor
    · unfold d
      exact sub_nonneg.mpr hv'.2
    · simpa [d, v, point] using lrSmallSBridge_one_sub_v_le hs hk hchi
  have ha : a ∈ Icc (0 : ℝ) d := by
    constructor
    · unfold a
      exact div_nonneg (sub_nonneg.mpr hv'.2)
        (by linarith [hv'.1] : 0 ≤ 1 + v)
    · unfold a d
      exact lrSmallSBridge_a_le_d ⟨hv'.1.le, hv'.2⟩
  have hloss := lrSmallSBridge_v_loss_bound hs hk hd ha hDmem
  have hnorm' :
      lrSmallSBridgeFrozen s k chi (Real.log (1 / s))
          (lrSmallSBridgeCoreB point) -
          lrCertificateD point * (2 * d ^ 2 / s + a / 4) ≤
        lrSmallSBridgeChannelReserve
          (lrCertificateD point) (lrCertificateBFlow point)
          v (lrCertificateX point) (lrLowerFaceOmegaQ0 point.s 0)
          (lrSmallSBridgeQ0G point)
          (lrLowerFacePWQ0 point.s point.k point.chi v) / s := by
    simpa [hs.1.ne', homegaZero, v] using hnorm
  change lrSmallSBridgeFrozen s k chi (Real.log (1 / s))
        (lrSmallSBridgeCoreB point) - lrSmallSBridgeEpsilonV ≤ _
  exact (sub_le_sub_left hloss _).trans hnorm'

end CourtadeKumar
