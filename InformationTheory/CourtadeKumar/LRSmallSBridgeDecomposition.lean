import InformationTheory.CourtadeKumar.LRSmallSBridgeAssembly
import InformationTheory.CourtadeKumar.LRHighShapeMidpointEvaluator
import InformationTheory.CourtadeKumar.LRLowerFaceR0

/-!
# Exact channel decomposition for the small-`s` bridge

This file formalizes the algebra behind manuscript (M31)--(M32).  The
midpoint reserve is linear in the channel pieces `G`, `P`, and `W`.  The
first identity compares the true logarithmic channel with the channel in
which `v`, `M`, and `x` are frozen at one.  The second records additivity,
which separates the logarithmic core from the entropy remainder.
-/

namespace CourtadeKumar

noncomputable def lrSmallSBridgeChannelX
    (v W G P : ℝ) : ℝ :=
  G + P - 4 * W / (1 + v) - 2 * (v / (1 + v)) * W

noncomputable def lrSmallSBridgeChannelY
    (v x W P : ℝ) : ℝ :=
  P - 2 * (v / (1 + v)) * x * W

noncomputable def lrSmallSBridgeChannelReserve
    (D B v x W G P : ℝ) : ℝ :=
  D * lrSmallSBridgeChannelX v W G P +
    B * lrSmallSBridgeChannelY v x W P

/-- The exact frozen-channel value used in (M29). -/
noncomputable def lrSmallSBridgeFrozenChannelReserve
    (D B W G P : ℝ) : ℝ :=
  D * (G + P - 3 * W) + B * (P - W)

/-- Exact radial-weight subtraction.  Here `deltaG` and `deltaP` are the
changes in the two positive channel collections, and
`a = (1-v)/(1+v)`. -/
lemma lrSmallSBridgeChannelReserve_sub_frozen
    {D B v x W G₀ P₀ deltaG deltaP a : ℝ}
    (hv : v ≠ -1)
    (ha : a = (1 - v) / (1 + v)) :
    lrSmallSBridgeChannelReserve D B v x W
        (G₀ + deltaG) (P₀ + deltaP) -
        lrSmallSBridgeFrozenChannelReserve D B W G₀ P₀ =
      D * (deltaG + deltaP - a * W) +
        B * (deltaP + (1 - 2 * (v / (1 + v)) * x) * W) := by
  unfold lrSmallSBridgeChannelReserve lrSmallSBridgeChannelX
    lrSmallSBridgeChannelY lrSmallSBridgeFrozenChannelReserve
  have hden : 1 + v ≠ 0 := by
    intro h
    apply hv
    linear_combination h
  rw [ha]
  field_simp [hden] <;> ring

/-- If the only adverse radial term is `deltaG ≥ -2d²`, exact
subtraction costs at most the payment displayed in (M31). -/
theorem lrSmallSBridgeChannelReserve_sub_frozen_lower
    {D B v x W G₀ P₀ deltaG deltaP a d : ℝ}
    (hv : v ≠ -1)
    (ha : a = (1 - v) / (1 + v))
    (hD : 0 ≤ D) (hB : 0 ≤ B) (hW : 0 ≤ W)
    (hdeltaG : -2 * d ^ 2 ≤ deltaG)
    (hdeltaP : 0 ≤ deltaP)
    (hshape : 0 ≤ 1 - 2 * (v / (1 + v)) * x) :
    -D * (2 * d ^ 2 + a * W) ≤
      lrSmallSBridgeChannelReserve D B v x W
          (G₀ + deltaG) (P₀ + deltaP) -
        lrSmallSBridgeFrozenChannelReserve D B W G₀ P₀ := by
  rw [lrSmallSBridgeChannelReserve_sub_frozen hv ha]
  have hDdeltaG : D * (-2 * d ^ 2) ≤ D * deltaG :=
    mul_le_mul_of_nonneg_left hdeltaG hD
  have hDdeltaP : 0 ≤ D * deltaP := mul_nonneg hD hdeltaP
  have hBdeltaP : 0 ≤ B * deltaP := mul_nonneg hB hdeltaP
  have hBshape : 0 ≤ B *
      ((1 - 2 * (v / (1 + v)) * x) * W) :=
    mul_nonneg hB (mul_nonneg hshape hW)
  nlinarith

/-- Normalized form of the preceding subtraction, ready to consume the
rational `epsilon_v` estimate. -/
theorem lrSmallSBridgeChannelReserve_normalized_lower
    {s D B v x G₀ P₀ deltaG deltaP a d : ℝ}
    (hs : 0 < s) (hv : v ≠ -1)
    (ha : a = (1 - v) / (1 + v))
    (hD : 0 ≤ D) (hB : 0 ≤ B)
    (hdeltaG : -2 * d ^ 2 ≤ deltaG)
    (hdeltaP : 0 ≤ deltaP)
    (hshape : 0 ≤ 1 - 2 * (v / (1 + v)) * x) :
    lrSmallSBridgeFrozenChannelReserve D B (s / 4) G₀ P₀ / s -
        D * (2 * d ^ 2 / s + a / 4) ≤
      lrSmallSBridgeChannelReserve D B v x (s / 4)
          (G₀ + deltaG) (P₀ + deltaP) / s := by
  have hraw := lrSmallSBridgeChannelReserve_sub_frozen_lower
    (W := s / 4) (G₀ := G₀) (P₀ := P₀)
      hv ha hD hB (div_nonneg hs.le (by norm_num))
      hdeltaG hdeltaP hshape
  have hdiv := div_le_div_of_nonneg_right hraw hs.le
  have hloss :
      D * (2 * d ^ 2 + a * (s / 4)) / s =
        D * (2 * d ^ 2 / s + a / 4) := by
    field_simp [hs.ne']
  have hnegLoss :
      -D * (2 * d ^ 2 + a * (s / 4)) / s =
        -D * (2 * d ^ 2 / s + a / 4) := by
    calc
      -D * (2 * d ^ 2 + a * (s / 4)) / s =
          -(D * (2 * d ^ 2 + a * (s / 4)) / s) := by ring
      _ = -(D * (2 * d ^ 2 / s + a / 4)) := by rw [hloss]
      _ = -D * (2 * d ^ 2 / s + a / 4) := by ring
  have hdiff :
      (lrSmallSBridgeChannelReserve D B v x (s / 4)
            (G₀ + deltaG) (P₀ + deltaP) -
          lrSmallSBridgeFrozenChannelReserve D B (s / 4) G₀ P₀) / s =
        lrSmallSBridgeChannelReserve D B v x (s / 4)
            (G₀ + deltaG) (P₀ + deltaP) / s -
          lrSmallSBridgeFrozenChannelReserve D B (s / 4) G₀ P₀ / s := by
    ring
  rw [hnegLoss, hdiff] at hdiv
  linarith

/-- The midpoint reserve is exactly additive in channel components. -/
lemma lrSmallSBridgeChannelReserve_add
    {D B v x W₁ W₂ G₁ G₂ P₁ P₂ : ℝ} :
    lrSmallSBridgeChannelReserve D B v x (W₁ + W₂)
        (G₁ + G₂) (P₁ + P₂) =
      lrSmallSBridgeChannelReserve D B v x W₁ G₁ P₁ +
        lrSmallSBridgeChannelReserve D B v x W₂ G₂ P₂ := by
  unfold lrSmallSBridgeChannelReserve lrSmallSBridgeChannelX
    lrSmallSBridgeChannelY
  ring

/-- The abstract channel reserve is the already-defined half-midpoint
numerator.  This is the exact bridge back to the LR flow target. -/
theorem lrCertificateHalfMidpointNumerator_eq_channelReserve
    {point : CertificatePoint}
    (hv : lrCertificateV point ≠ -1) :
    lrCertificateHalfMidpointNumerator point =
      lrSmallSBridgeChannelReserve
        (lrCertificateD point) (lrCertificateBFlow point)
        (lrCertificateV point) (lrCertificateX point)
        (lrCertificateW point) (lrCertificateGShape point)
        (lrCertificatePW point) := by
  unfold lrCertificateHalfMidpointNumerator
    lrSmallSBridgeChannelReserve lrSmallSBridgeChannelX
    lrSmallSBridgeChannelY lrCertificateHalfMidpointBracket
    lrCertificateM lrCertificateD
  have hden : 1 + lrCertificateV point ≠ 0 := by
    intro h
    apply hv
    linear_combination h
  field_simp [hden]
  ring

/-- The logarithmic part of the channel `G` collection. -/
noncomputable def lrSmallSBridgeQ0G (point : CertificatePoint) : ℝ :=
  lrCertificateG0 (lrCertificateV point) +
    lrLowerFaceQ0 (lrCertificateY0 point) +
    lrLowerFaceQ0 (lrCertificateE point) / lrCertificateV point

/-- The entropy-remainder part of the channel `G` collection. -/
noncomputable def lrSmallSBridgeR0G (point : CertificatePoint) : ℝ :=
  lrLowerFaceR0 (lrCertificateY0 point) +
    lrLowerFaceR0 (lrCertificateE point) / lrCertificateV point

lemma lrCertificateGShape_eq_smallSBridge_split
    (point : CertificatePoint) :
    lrCertificateGShape point =
      lrSmallSBridgeQ0G point + lrSmallSBridgeR0G point := by
  unfold lrCertificateGShape lrCertificateGShapeValue
    lrSmallSBridgeQ0G lrSmallSBridgeR0G lrLowerFaceR0
  ring

lemma lrCertificateW_eq_smallSBridge_split
    (point : CertificatePoint) :
    lrCertificateW point =
      lrLowerFaceOmegaQ0 point.s 0 +
        lrLowerFaceOmegaR0 point.s 0 := by
  unfold lrCertificateW
  exact lrCertificateOmega_eq_lowerFace_split

lemma lrCertificatePW_eq_smallSBridge_split
    (point : CertificatePoint) :
    lrCertificatePW point =
      lrLowerFacePWQ0 point.s point.k point.chi
          (lrCertificateV point) +
        lrLowerFacePWR0 point.s point.k point.chi
          (lrCertificateV point) := by
  unfold lrCertificatePW lrCertificateY0 lrCertificateE
  exact lrCertificatePWValue_eq_lowerFace_split

/-- Exact `Q=q₀+r₀` decomposition of the actual half-midpoint target. -/
theorem lrCertificateHalfMidpointNumerator_eq_q0_add_r0
    {point : CertificatePoint}
    (hv : lrCertificateV point ≠ -1) :
    lrCertificateHalfMidpointNumerator point =
      lrSmallSBridgeChannelReserve
          (lrCertificateD point) (lrCertificateBFlow point)
          (lrCertificateV point) (lrCertificateX point)
          (lrLowerFaceOmegaQ0 point.s 0)
          (lrSmallSBridgeQ0G point)
          (lrLowerFacePWQ0 point.s point.k point.chi
            (lrCertificateV point)) +
        lrSmallSBridgeChannelReserve
          (lrCertificateD point) (lrCertificateBFlow point)
          (lrCertificateV point) (lrCertificateX point)
          (lrLowerFaceOmegaR0 point.s 0)
          (lrSmallSBridgeR0G point)
          (lrLowerFacePWR0 point.s point.k point.chi
            (lrCertificateV point)) := by
  rw [lrCertificateHalfMidpointNumerator_eq_channelReserve hv,
    lrCertificateW_eq_smallSBridge_split,
    lrCertificateGShape_eq_smallSBridge_split,
    lrCertificatePW_eq_smallSBridge_split,
    lrSmallSBridgeChannelReserve_add]

/-- A component whose two collected coordinates have the same lower bound
costs at most `(D+B)` times that loss. -/
theorem lrSmallSBridgeChannelReserve_lower_of_coordinates
    {D B v x W G P loss : ℝ}
    (hD : 0 ≤ D) (hB : 0 ≤ B)
    (hX : -loss ≤ lrSmallSBridgeChannelX v W G P)
    (hY : -loss ≤ lrSmallSBridgeChannelY v x W P) :
    -(D + B) * loss ≤
      lrSmallSBridgeChannelReserve D B v x W G P := by
  have hDX := mul_le_mul_of_nonneg_left hX hD
  have hBY := mul_le_mul_of_nonneg_left hY hB
  unfold lrSmallSBridgeChannelReserve
  nlinarith

end CourtadeKumar
