import InformationTheory.CourtadeKumar.LRCompactVWOneSeries

/-!
# Endpoint-tight enclosure for `W_R(1)`

The ordinary compact-`V` Abel enclosure evaluates its upper endpoint over
the complete `R` interval.  On the adjacent high-parameter region this loses
enough correlation between `(1-R)^2` and the Abel head to obscure otherwise
positive terminal values.

The score-series representation shows directly that `R ↦ W_R(1)` is
antitone on `(0,1)`.  Consequently the exact value at `box.sLo` is an upper
bound throughout the box.  We evaluate the existing Abel enclosure on a
degenerate box at that endpoint, while retaining the ordinary box enclosure
for the lower endpoint.  The auxiliary coordinates are fixed at `1/2`; they
do not occur in the Abel computation but make its soundness theorem
applicable at an interior certificate point.
-/

set_option autoImplicit false

open Set

namespace CourtadeKumar

/-- The endpoint kernel decreases with the channel parameter on its open
unit domain.  This proof uses only the positive score series and the
coefficientwise antitonicity of `lrCompactVScore`. -/
theorem lrWKernel_one_antitoneOn_unitInterior :
    AntitoneOn (fun R : ℝ ↦ lrWKernel R 1) (Ioo (0 : ℝ) 1) := by
  intro R hR S hS hRS
  have hRSeries := lrCompactVWOneTerm_hasSum hR
  have hSSeries := lrCompactVWOneTerm_hasSum hS
  change lrWKernel S 1 ≤ lrWKernel R 1
  rw [← hSSeries.tsum_eq, ← hRSeries.tsum_eq]
  exact hSSeries.summable.tsum_le_tsum (fun j ↦ by
    have hscore :=
      (lrCompactVScore_antitoneOn_unit
        (n := j + 1) (by omega))
        ⟨hR.1.le, hR.2.le⟩ ⟨hS.1.le, hS.2.le⟩ hRS
    simpa [lrCompactVWTerm] using
      mul_le_mul_of_nonneg_left hscore
        (lrLowA_pos (show 1 ≤ j + 1 by omega)).le)
    hRSeries.summable

/-- Collapse the channel coordinate to the lower endpoint.  The unused
compact coordinates are fixed at an interior rational point. -/
def lrCompactVWOneLowerEndpointBox
    (box : CertificateBox) : CertificateBox where
  sLo := box.sLo
  sHi := box.sLo
  kLo := 1 / 2
  kHi := 1 / 2
  chiLo := 1 / 2
  chiHi := 1 / 2

/-- Real point represented by `lrCompactVWOneLowerEndpointBox`. -/
noncomputable def lrCompactVWOneLowerEndpointPoint
    (box : CertificateBox) : CertificatePoint where
  s := (box.sLo : ℝ)
  k := 1 / 2
  chi := 1 / 2

theorem lrCompactVWOneLowerEndpointBox_valid
    {box : CertificateBox} (hbox : LRCompactVBoxValid box) :
    LRCompactVBoxValid (lrCompactVWOneLowerEndpointBox box) := by
  rcases hbox with
    ⟨hsLo0, hsLoHi, hsHi1, _, _, _, _, _, _⟩
  exact ⟨hsLo0, le_rfl, hsLoHi.trans hsHi1,
    by norm_num [lrCompactVWOneLowerEndpointBox], le_rfl,
    by norm_num [lrCompactVWOneLowerEndpointBox],
    by norm_num [lrCompactVWOneLowerEndpointBox], le_rfl,
    by norm_num [lrCompactVWOneLowerEndpointBox]⟩

theorem lrCompactVWOneLowerEndpointBox_contains
    (box : CertificateBox) :
    (lrCompactVWOneLowerEndpointBox box).Contains
      (lrCompactVWOneLowerEndpointPoint box) := by
  norm_num [lrCompactVWOneLowerEndpointBox,
    lrCompactVWOneLowerEndpointPoint, CertificateBox.Contains]

theorem lrCompactVWOneLowerEndpointPoint_interior
    {box : CertificateBox} {point : CertificatePoint}
    (hsLo0 : (0 : ℚ) < box.sLo)
    (hpoint : box.Contains point) (hinterior : LRCompactVInterior point) :
    LRCompactVInterior (lrCompactVWOneLowerEndpointPoint box) := by
  have hsLo0Real : (0 : ℝ) < box.sLo := by
    exact_mod_cast hsLo0
  have hsLo1Real : (box.sLo : ℝ) < 1 :=
    hpoint.1.trans_lt hinterior.1.2
  exact ⟨⟨hsLo0Real, hsLo1Real⟩,
    by norm_num [lrCompactVWOneLowerEndpointPoint],
    by norm_num [lrCompactVWOneLowerEndpointPoint]⟩

/-- Abel enclosure evaluated at the exact lower `R` endpoint. -/
def lrCompactVWOneLowerEndpointAbelEnclosure
    (terms J : ℕ) (box : CertificateBox) : RationalEnclosure :=
  lrCompactVWOneEnclosure terms J
    (lrCompactVWOneLowerEndpointBox box)

/-- Keep a sound box-wide lower endpoint and replace the loose box-wide
upper endpoint by the Abel enclosure at `R = box.sLo`.  The reduced terminal
topology instantiates `J = 72`, matching the sharp predictor bound. -/
def lrCompactVWOneEndpointEnclosure
    (terms J : ℕ) (box : CertificateBox) : RationalEnclosure :=
  ⟨(lrCompactVWOneEnclosure terms J box).lower,
    (lrCompactVWOneLowerEndpointAbelEnclosure terms J box).upper⟩

/-- The endpoint-tight enclosure contains `W_R(1)` at every interior point
of a valid compact box whose lower channel endpoint is positive. -/
theorem lrCompactVWOneEndpointEnclosure_sound
    (terms J : ℕ) {box : CertificateBox} {point : CertificatePoint}
    (hbox : LRCompactVBoxValid box) (hsLo0 : (0 : ℚ) < box.sLo)
    (hpoint : box.Contains point) (hinterior : LRCompactVInterior point) :
    (lrCompactVWOneEndpointEnclosure terms J box).Contains
      (lrWKernel point.s 1) := by
  have hboxEnclosure := lrCompactVWOneEnclosure_sound
    terms J hbox hpoint hinterior
  have hEndpointBox := lrCompactVWOneLowerEndpointBox_valid hbox
  have hEndpointContains := lrCompactVWOneLowerEndpointBox_contains box
  have hEndpointInterior :=
    lrCompactVWOneLowerEndpointPoint_interior hsLo0 hpoint hinterior
  have hEndpointEnclosure := lrCompactVWOneEnclosure_sound
    terms J hEndpointBox hEndpointContains hEndpointInterior
  have hEndpointLe :
      lrWKernel point.s 1 ≤ lrWKernel (box.sLo : ℝ) 1 := by
    exact lrWKernel_one_antitoneOn_unitInterior
      hEndpointInterior.1 hinterior.1 hpoint.1
  constructor
  · exact hboxEnclosure.1
  · exact hEndpointLe.trans hEndpointEnclosure.2

end CourtadeKumar
