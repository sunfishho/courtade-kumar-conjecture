import InformationTheory.CourtadeKumar.LRSmallSBridgeIdentification
import InformationTheory.CourtadeKumar.LRLowerFaceR0Payment

/-!
# Identification of the small-`s` entropy remainder

This file connects the analytic `r₀` estimates to the two collected channel
coordinates in manuscript (M32).  In particular, the zero-noise term has the
favorable sign, so both coordinates inherit the same lower bound from
`P_{W,r₀}`.
-/

open Set

namespace CourtadeKumar

lemma lrLowerFaceOmegaR0_zero_nonpos
    {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    lrLowerFaceOmegaR0 s 0 ≤ 0 := by
  have htotal := lrCertificateOmega_zero_mem hs
  have hsplit := lrCertificateOmega_eq_lowerFace_split (s := s) (y := 0)
  rw [lrLowerFaceOmegaQ0_zero hs.1] at hsplit
  linarith [htotal.2]

lemma lrLowerFaceR0Prime_nonneg
    {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    0 ≤ lrLowerFaceR0Prime s := by
  have hw := lrLowerFaceOmegaR0_zero_nonpos hs
  have hr := lrLowerFaceR0_nonneg hs
  have hformula : lrLowerFaceOmegaR0 s 0 =
      lrLowerFaceR0 s - s * lrLowerFaceR0Prime s := by
    unfold lrLowerFaceOmegaR0 lrCertificateB
    simp only [mul_zero, sub_zero, add_zero, lrLowerFaceR0_zero]
    ring
  rw [hformula] at hw
  have hprod : 0 ≤ s * lrLowerFaceR0Prime s := by linarith
  exact (mul_nonneg_iff_of_pos_left hs.1).mp hprod

lemma lrLowerFaceR0_nonneg_closed
    {y : ℝ} (hy : y ∈ Ico (0 : ℝ) 1) :
    0 ≤ lrLowerFaceR0 y := by
  rcases hy.1.eq_or_lt with rfl | hyPos
  · simp
  · exact lrLowerFaceR0_nonneg ⟨hyPos, hy.2⟩

lemma lrSmallSBridgeR0G_nonneg
    {s k chi : ℝ} (hs : s ∈ Ioc (0 : ℝ) (1 / 16384))
    (hk : k ∈ Icc (1 / 4 : ℝ) 4)
    (hchi : chi ∈ Icc (0 : ℝ) 1) :
    0 ≤ lrSmallSBridgeR0G (⟨s, k, chi⟩ : CertificatePoint) := by
  have he := lrSmallSBridge_e_mem hs hk
  have hv := lrSmallSBridge_v_mem hs hk hchi
  have hy0 : chi * (s * k) ∈ Ico (0 : ℝ) 1 := by
    constructor
    · exact mul_nonneg hchi.1 he.1.le
    · exact (mul_le_of_le_one_left he.1.le hchi.2).trans_lt he.2
  have hrY := lrLowerFaceR0_nonneg_closed hy0
  have hrE := lrLowerFaceR0_nonneg_closed ⟨he.1.le, he.2⟩
  unfold lrSmallSBridgeR0G lrCertificateY0 lrCertificateE
  exact add_nonneg hrY (div_nonneg hrE hv.1.le)

/-- Both collected remainder coordinates inherit the same `P_{W,r₀}`
lower bound, because `G_{r₀} ≥ 0` and `W_{r₀} ≤ 0`. -/
theorem lrSmallSBridgeR0_coordinates_lower
    {s k chi : ℝ} (hs : s ∈ Ioc (0 : ℝ) (1 / 16384))
    (hk : k ∈ Icc (1 / 4 : ℝ) 4)
    (hchi : chi ∈ Icc (0 : ℝ) 1) :
    let point : CertificatePoint := ⟨s, k, chi⟩
    let loss := (1 + 1 / lrCertificateV point) * s *
      lrLowerFaceR0Prime s
    (-loss ≤ lrSmallSBridgeChannelX
        (lrCertificateV point) (lrLowerFaceOmegaR0 s 0)
        (lrSmallSBridgeR0G point)
        (lrLowerFacePWR0 s k chi (lrCertificateV point)) ∧
      -loss ≤ lrSmallSBridgeChannelY
        (lrCertificateV point) (lrCertificateX point)
        (lrLowerFaceOmegaR0 s 0)
        (lrLowerFacePWR0 s k chi (lrCertificateV point))) := by
  let point : CertificatePoint := ⟨s, k, chi⟩
  let v := lrCertificateV point
  let x := lrCertificateX point
  have hsIoo : s ∈ Ioo (0 : ℝ) 1 :=
    ⟨hs.1, hs.2.trans_lt (by norm_num)⟩
  have hv := lrSmallSBridge_v_mem hs hk hchi
  have hv' : v ∈ Ioc (0 : ℝ) 1 := by simpa [v, point] using hv
  have hx : 0 < x := by
    simpa [x, point] using lrSmallSBridge_x_pos hs hk hchi
  have he := lrSmallSBridge_e_mem hs hk
  have hy0 : chi * (s * k) ∈ Ico (0 : ℝ) 1 := by
    constructor
    · exact mul_nonneg hchi.1 he.1.le
    · exact (mul_le_of_le_one_left he.1.le hchi.2).trans_lt he.2
  have hp := lrLowerFacePWR0_lower hsIoo hv'.1 hy0
    ⟨he.1.le, he.2⟩
  have hg : 0 ≤ lrSmallSBridgeR0G point := by
    simpa [point] using lrSmallSBridgeR0G_nonneg hs hk hchi
  have hw := lrLowerFaceOmegaR0_zero_nonpos hsIoo
  have hden : 0 < 1 + v := by linarith [hv'.1]
  have hm : 0 ≤ v / (1 + v) := div_nonneg hv'.1.le hden.le
  have hfourW : 4 * lrLowerFaceOmegaR0 s 0 / (1 + v) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos
      (by norm_num) hw) hden.le
  have htwoW : 2 * (v / (1 + v)) * lrLowerFaceOmegaR0 s 0 ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (by norm_num) hm) hw
  have hxW : 2 * (v / (1 + v)) * x *
      lrLowerFaceOmegaR0 s 0 ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg (mul_nonneg (by norm_num) hm) hx.le) hw
  dsimp only
  change
    -((1 + 1 / v) * s * lrLowerFaceR0Prime s) ≤
        lrSmallSBridgeChannelX v (lrLowerFaceOmegaR0 s 0)
          (lrSmallSBridgeR0G point) (lrLowerFacePWR0 s k chi v) ∧
      -((1 + 1 / v) * s * lrLowerFaceR0Prime s) ≤
        lrSmallSBridgeChannelY v x (lrLowerFaceOmegaR0 s 0)
          (lrLowerFacePWR0 s k chi v)
  constructor
  · unfold lrSmallSBridgeChannelX
    linarith
  · unfold lrSmallSBridgeChannelY
    linarith

lemma lrSmallSBridge_D_add_B_upper
    {s k chi : ℝ} (hs : s ∈ Ioc (0 : ℝ) (1 / 16384))
    (hk : k ∈ Icc (1 / 4 : ℝ) 4)
    (hchi : chi ∈ Icc (0 : ℝ) 1) :
    lrCertificateD (⟨s, k, chi⟩ : CertificatePoint) +
        lrCertificateBFlow (⟨s, k, chi⟩ : CertificatePoint) ≤
      Real.log (1 / s) / 2 + 2 * Real.log 2 := by
  let point : CertificatePoint := ⟨s, k, chi⟩
  have hv := lrSmallSBridge_v_mem hs hk hchi
  have hkPos : 0 < k := (by norm_num : (0 : ℝ) < 1 / 4).trans_le hk.1
  have hR : 0 ≤ 1 - s := by nlinarith [hs.2]
  have houterPos : 0 < 1 + (1 - s) * k := by positivity
  have honeVPos : 0 < 1 + lrCertificateV point := by
    have : 0 < lrCertificateV point := by simpa [point] using hv.1
    linarith
  have hlogV : Real.log (1 + lrCertificateV point) ≤ Real.log 2 := by
    apply Real.log_le_log honeVPos
    have : lrCertificateV point ≤ 1 := by simpa [point] using hv.2
    linarith
  have hlogQuarter : Real.log (1 / 4 : ℝ) = -2 * Real.log 2 := by
    rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0)
      (by norm_num : (4 : ℝ) ≠ 0), lrSmallSBridge_log_four]
    norm_num
  have hlogKLower : Real.log (1 / 4 : ℝ) ≤ Real.log k := by
    exact Real.log_le_log (by norm_num) hk.1
  have hlogK : -Real.log k / 2 ≤ Real.log 2 := by
    rw [hlogQuarter] at hlogKLower
    linarith
  rw [lrCertificateD_eq_smallSBridgeD hs hk,
    lrCertificateBFlow_eq_smallSBridgeB hs hk]
  unfold lrSmallSBridgeD lrSmallSBridgeCoreB
  rw [Real.log_div houterPos.ne' hkPos.ne']
  change
    (Real.log (1 + (1 - s) * k) - Real.log k) / 2 +
        (Real.log (1 / s) / 2 +
          (Real.log (1 + lrCertificateV point) -
            Real.log (1 + (1 - s) * k) / 2)) ≤ _
  nlinarith

lemma lrSmallSBridge_remainder_analytic_loss_upper
    {s k chi : ℝ} (hs : s ∈ Ioc (0 : ℝ) (1 / 16384))
    (hk : k ∈ Icc (1 / 4 : ℝ) 4)
    (hchi : chi ∈ Icc (0 : ℝ) 1) :
    (lrCertificateD (⟨s, k, chi⟩ : CertificatePoint) +
        lrCertificateBFlow (⟨s, k, chi⟩ : CertificatePoint)) *
      (1 + 1 / lrCertificateV
        (⟨s, k, chi⟩ : CertificatePoint)) *
      lrLowerFaceR0Prime s ≤ lrSmallSBridgeEpsilonR := by
  let point : CertificatePoint := ⟨s, k, chi⟩
  let v := lrCertificateV point
  let factor := 1 + 1 / v
  let L := Real.log (1 / s)
  let A := L / 2 + 2 * Real.log 2
  let C := L + 2 * Real.log 2
  have hsIoo : s ∈ Ioo (0 : ℝ) 1 :=
    ⟨hs.1, hs.2.trans_lt (by norm_num)⟩
  have hv := lrSmallSBridge_v_mem hs hk hchi
  have hv' : v ∈ Ioc (0 : ℝ) 1 := by simpa [v, point] using hv
  have hD := lrSmallSBridgeD_mem hs hk
  have hDnonneg : 0 ≤ lrCertificateD point := by
    rw [lrCertificateD_eq_smallSBridgeD hs hk]
    exact hD.1
  have hBnonneg : 0 ≤ lrCertificateBFlow point := by
    simpa [point] using lrCertificateBFlow_nonneg_smallS hs hk hchi
  have hDBnonneg : 0 ≤ lrCertificateD point +
      lrCertificateBFlow point := add_nonneg hDnonneg hBnonneg
  have hDB := lrSmallSBridge_D_add_B_upper hs hk hchi
  have hDB' : lrCertificateD point + lrCertificateBFlow point ≤ A := by
    simpa [point, A, L] using hDB
  have hL := lrSmallSBridge_log_lower hs
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hA : 0 ≤ A := by
    unfold A L
    nlinarith
  have hC : 0 ≤ C := by
    unfold C L
    nlinarith
  have hfactor : 0 ≤ factor := by
    unfold factor
    exact add_nonneg (by norm_num) (div_nonneg (by norm_num) hv'.1.le)
  have hprimeNonneg := lrLowerFaceR0Prime_nonneg hsIoo
  have hlogInv : Real.log (1 / s) = -Real.log s := by
    rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) hs.1.ne']
    norm_num
  have hlogFourOverS : Real.log (4 / s) = C := by
    unfold C L
    rw [Real.log_div (by norm_num : (4 : ℝ) ≠ 0) hs.1.ne',
      lrSmallSBridge_log_four, hlogInv]
    ring
  have hsSmall : s ∈ Ioo (0 : ℝ) (1 / 16) :=
    ⟨hs.1, hs.2.trans_lt (by norm_num)⟩
  have hprime := lrLowerFaceR0Prime_upper hsSmall
  rw [hlogFourOverS] at hprime
  have hbase :
      (lrCertificateD point + lrCertificateBFlow point) *
          lrLowerFaceR0Prime s ≤ A * (s / 3 * C) :=
    mul_le_mul hDB' hprime hprimeNonneg hA
  have hscaled := mul_le_mul_of_nonneg_left hbase hfactor
  have hpayment := lrSmallSBridge_remainder_loss_coordinate hs hk hchi
  change
    (lrCertificateD point + lrCertificateBFlow point) * factor *
      lrLowerFaceR0Prime s ≤ lrSmallSBridgeEpsilonR
  calc
    (lrCertificateD point + lrCertificateBFlow point) * factor *
        lrLowerFaceR0Prime s =
      factor * ((lrCertificateD point + lrCertificateBFlow point) *
        lrLowerFaceR0Prime s) := by ring
    _ ≤ factor * (A * (s / 3 * C)) := hscaled
    _ = factor / 3 * lrSmallSBridgeLogEnvelope s := by
      unfold lrSmallSBridgeLogEnvelope A C L
      ring
    _ ≤ lrSmallSBridgeEpsilonR := by
      simpa [factor, v, point, one_div] using hpayment

/-- Fully identified form of (M32): the normalized entropy-remainder
channel is bounded below by `-epsilon_r`. -/
theorem lrSmallSBridge_r0_restoration_lower
    {s k chi : ℝ} (hs : s ∈ Ioc (0 : ℝ) (1 / 16384))
    (hk : k ∈ Icc (1 / 4 : ℝ) 4)
    (hchi : chi ∈ Icc (0 : ℝ) 1) :
    -lrSmallSBridgeEpsilonR ≤
      lrSmallSBridgeChannelReserve
        (lrCertificateD (⟨s, k, chi⟩ : CertificatePoint))
        (lrCertificateBFlow (⟨s, k, chi⟩ : CertificatePoint))
        (lrCertificateV (⟨s, k, chi⟩ : CertificatePoint))
        (lrCertificateX (⟨s, k, chi⟩ : CertificatePoint))
        (lrLowerFaceOmegaR0 s 0)
        (lrSmallSBridgeR0G (⟨s, k, chi⟩ : CertificatePoint))
        (lrLowerFacePWR0 s k chi
          (lrCertificateV (⟨s, k, chi⟩ : CertificatePoint))) / s := by
  let point : CertificatePoint := ⟨s, k, chi⟩
  let v := lrCertificateV point
  let loss := (1 + 1 / v) * s * lrLowerFaceR0Prime s
  have hD : 0 ≤ lrCertificateD point := by
    rw [lrCertificateD_eq_smallSBridgeD hs hk]
    exact (lrSmallSBridgeD_mem hs hk).1
  have hB : 0 ≤ lrCertificateBFlow point := by
    simpa [point] using lrCertificateBFlow_nonneg_smallS hs hk hchi
  have hcoords := lrSmallSBridgeR0_coordinates_lower hs hk hchi
  have hcoords' :
      -loss ≤ lrSmallSBridgeChannelX v (lrLowerFaceOmegaR0 s 0)
          (lrSmallSBridgeR0G point) (lrLowerFacePWR0 s k chi v) ∧
        -loss ≤ lrSmallSBridgeChannelY v (lrCertificateX point)
          (lrLowerFaceOmegaR0 s 0) (lrLowerFacePWR0 s k chi v) := by
    simpa [loss, v, point] using hcoords
  have hraw := lrSmallSBridgeChannelReserve_lower_of_coordinates
    hD hB hcoords'.1 hcoords'.2
  have hdiv := div_le_div_of_nonneg_right hraw hs.1.le
  have hnormalized :
      -((lrCertificateD point + lrCertificateBFlow point) *
          (1 + 1 / v) * lrLowerFaceR0Prime s) ≤
        lrSmallSBridgeChannelReserve
          (lrCertificateD point) (lrCertificateBFlow point)
          v (lrCertificateX point) (lrLowerFaceOmegaR0 s 0)
          (lrSmallSBridgeR0G point) (lrLowerFacePWR0 s k chi v) / s := by
    convert hdiv using 1 <;>
      unfold loss <;> field_simp [hs.1.ne'] <;> ring
  have hanalytic := lrSmallSBridge_remainder_analytic_loss_upper hs hk hchi
  have hanalytic' :
      (lrCertificateD point + lrCertificateBFlow point) *
          (1 + 1 / v) * lrLowerFaceR0Prime s ≤
        lrSmallSBridgeEpsilonR := by
    simpa [v, point] using hanalytic
  change -lrSmallSBridgeEpsilonR ≤
    lrSmallSBridgeChannelReserve
      (lrCertificateD point) (lrCertificateBFlow point)
      v (lrCertificateX point) (lrLowerFaceOmegaR0 s 0)
      (lrSmallSBridgeR0G point) (lrLowerFacePWR0 s k chi v) / s
  exact (neg_le_neg hanalytic').trans hnormalized

end CourtadeKumar
