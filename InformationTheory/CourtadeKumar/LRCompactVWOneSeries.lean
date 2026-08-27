import InformationTheory.CourtadeKumar.LRCompactVBEnclosure
import InformationTheory.CourtadeKumar.LRLowShapeUTail

/-!
# Positive Abel-series enclosure for `W_R(1)`

The endpoint kernel has the cancellation-safe expansion

`W_R(1) = (1-R)² ∑_{j≥1} j b_j R^(j-1)`.

The proved estimate `j b_j ≤ 1/4` yields the geometric tail
`(1-R)R^J/4`.  This is the structured upper bound needed by the compact
leaf correction term.
-/

open Set
open scoped BigOperators

namespace CourtadeKumar

noncomputable def lrCompactVWOneAbelHead
    (J : ℕ) (R : ℝ) : ℝ :=
  (1 - R) ^ 2 *
    ∑ j ∈ Finset.range J,
      ((j + 1 : ℕ) : ℝ) * lrLowB (j + 1) * R ^ j

noncomputable def lrCompactVWOneAbelTail
    (J : ℕ) (R : ℝ) : ℝ :=
  (1 - R) * R ^ J / 4

theorem lrCompactVWOneAbelHead_le
    {R : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1) (J : ℕ) :
    lrCompactVWOneAbelHead J R ≤ lrWKernel R 1 := by
  have hseries := lrLowB_derivative_hasSum hR
  have hhead :
      (∑ j ∈ Finset.range J,
        ((j + 1 : ℕ) : ℝ) * lrLowB (j + 1) * R ^ j) ≤
        lrWKernel R 1 / (1 - R) ^ 2 := by
    rw [← hseries.tsum_eq]
    exact hseries.summable.sum_le_tsum (Finset.range J) (fun j _ ↦ by
      exact mul_nonneg
        (mul_nonneg (by positivity) (lrLowB_pos (j + 1)).le)
        (pow_nonneg hR.1.le _))
  have hsPos : 0 < (1 - R) ^ 2 := sq_pos_of_pos (sub_pos.mpr hR.2)
  unfold lrCompactVWOneAbelHead
  calc
    (1 - R) ^ 2 * ∑ j ∈ Finset.range J,
        ((j + 1 : ℕ) : ℝ) * lrLowB (j + 1) * R ^ j ≤
        (1 - R) ^ 2 * (lrWKernel R 1 / (1 - R) ^ 2) :=
      mul_le_mul_of_nonneg_left hhead hsPos.le
    _ = lrWKernel R 1 := by
      field_simp [sub_ne_zero.mpr hR.2.ne']

theorem lrCompactVWOne_le_AbelHead_add_tail
    {R : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1) (J : ℕ) :
    lrWKernel R 1 ≤
      lrCompactVWOneAbelHead J R + lrCompactVWOneAbelTail J R := by
  let f : ℕ → ℝ := fun j ↦
    ((j + 1 : ℕ) : ℝ) * lrLowB (j + 1) * R ^ j
  have hseries : HasSum f (lrWKernel R 1 / (1 - R) ^ 2) := by
    simpa [f] using lrLowB_derivative_hasSum hR
  have htail : HasSum (fun k : ℕ ↦ f (k + J))
      (lrWKernel R 1 / (1 - R) ^ 2 -
        ∑ j ∈ Finset.range J, f j) :=
    (hasSum_nat_add_iff' J).2 hseries
  let g : ℕ → ℝ := fun k ↦ (1 / 4 : ℝ) * R ^ (k + J)
  have hgeom := hasSum_geometric_of_lt_one hR.1.le hR.2
  have hg : HasSum g ((1 / 4 : ℝ) * R ^ J / (1 - R)) := by
    convert hgeom.mul_left ((1 / 4 : ℝ) * R ^ J) using 1
    · funext k
      dsimp [g]
      rw [pow_add]
      ring
  have hterm : ∀ k, f (k + J) ≤ g k := by
    intro k
    have hscaled := lrLowB_scaled_le_quarter
      (show 1 ≤ k + J + 1 by omega)
    have hpow : 0 ≤ R ^ (k + J) := pow_nonneg hR.1.le _
    dsimp [f, g]
    exact mul_le_mul_of_nonneg_right hscaled hpow
  have htailBound :
      lrWKernel R 1 / (1 - R) ^ 2 -
          ∑ j ∈ Finset.range J, f j ≤
        (1 / 4 : ℝ) * R ^ J / (1 - R) := by
    rw [← htail.tsum_eq, ← hg.tsum_eq]
    exact htail.summable.tsum_le_tsum hterm hg.summable
  have hsPos : 0 < 1 - R := sub_pos.mpr hR.2
  have hsSqPos : 0 < (1 - R) ^ 2 := sq_pos_of_pos hsPos
  have hmul := mul_le_mul_of_nonneg_left htailBound hsSqPos.le
  have hW :
      (1 - R) ^ 2 * (lrWKernel R 1 / (1 - R) ^ 2) =
        lrWKernel R 1 := by field_simp [hsSqPos.ne']
  have htailEq :
      (1 - R) ^ 2 * ((1 / 4 : ℝ) * R ^ J / (1 - R)) =
        (1 - R) * R ^ J / 4 := by
    field_simp [hsPos.ne']
  rw [mul_sub, hW, htailEq] at hmul
  unfold lrCompactVWOneAbelHead lrCompactVWOneAbelTail
  dsimp [f] at hmul ⊢
  linarith

/-- Exact interval for `1-R`. -/
def lrCompactVOneSubREnclosure (box : CertificateBox) :
    RationalEnclosure :=
  RationalEnclosure.sub (RationalEnclosure.point 1) box.sInterval

theorem lrCompactVOneSubREnclosure_sound
    {box : CertificateBox} {point : CertificatePoint}
    (hpoint : box.Contains point) :
    (lrCompactVOneSubREnclosure box).Contains (1 - point.s) := by
  have hone : (RationalEnclosure.point 1).Contains (1 : ℝ) := by
    norm_num [RationalEnclosure.point, RationalEnclosure.Contains]
  exact RationalEnclosure.contains_sub hone ⟨hpoint.1, hpoint.2.1⟩

def lrCompactVWOneAbelTermEnclosure
    (terms : ℕ) (box : CertificateBox) (j : ℕ) :
    RationalEnclosure :=
  RationalEnclosure.scale (j : ℚ) <|
    RationalEnclosure.mul
      (lrCompactVCoefficientTailEnclosure terms j)
      (RationalEnclosure.powNonnegative box.sInterval (j - 1))

theorem lrCompactVWOneAbelTermEnclosure_sound
    (terms : ℕ) {box : CertificateBox} {point : CertificatePoint}
    (hbox : LRCompactVBoxValid box) (hpoint : box.Contains point)
    {j : ℕ} (hj : 1 ≤ j) :
    (lrCompactVWOneAbelTermEnclosure terms box j).Contains
      ((j : ℝ) * lrLowB j * point.s ^ (j - 1)) := by
  have hR : box.sInterval.Contains point.s := ⟨hpoint.1, hpoint.2.1⟩
  have hpow := RationalEnclosure.contains_powNonnegative
    hbox.1 hR (j - 1)
  have hb := lrCompactVCoefficientTailEnclosure_sound terms j
  have hmul := RationalEnclosure.contains_mul hb hpow
  simpa [lrCompactVWOneAbelTermEnclosure, mul_assoc] using
    RationalEnclosure.contains_scale (j : ℚ) hmul

def lrCompactVWOneAbelHeadEnclosure
    (terms J : ℕ) (box : CertificateBox) : RationalEnclosure :=
  let raw := RationalEnclosure.sumRangeOne
    (lrCompactVWOneAbelTermEnclosure terms box) J
  let sSquared := RationalEnclosure.powNonnegative
    (lrCompactVOneSubREnclosure box) 2
  RationalEnclosure.mul sSquared raw

theorem lrCompactVWOneAbelHeadEnclosure_sound
    (terms J : ℕ) {box : CertificateBox} {point : CertificatePoint}
    (hbox : LRCompactVBoxValid box) (hpoint : box.Contains point) :
    (lrCompactVWOneAbelHeadEnclosure terms J box).Contains
      (lrCompactVWOneAbelHead J point.s) := by
  have hraw := RationalEnclosure.contains_sumRangeOne
    (fun j hj ↦ lrCompactVWOneAbelTermEnclosure_sound
      terms hbox hpoint hj) J
  have hs := lrCompactVOneSubREnclosure_sound hpoint
  have hsLower : (0 : ℚ) ≤ (lrCompactVOneSubREnclosure box).lower := by
    simp only [lrCompactVOneSubREnclosure, RationalEnclosure.sub,
      RationalEnclosure.add, RationalEnclosure.neg,
      RationalEnclosure.point, CertificateBox.sInterval]
    simpa [sub_eq_add_neg] using (sub_nonneg.mpr hbox.2.2.1)
  have hsSq := RationalEnclosure.contains_powNonnegative hsLower hs 2
  have hmul := RationalEnclosure.contains_mul hsSq hraw
  simpa [lrCompactVWOneAbelHeadEnclosure, lrCompactVWOneAbelHead,
    mul_assoc] using hmul

/-- Interval for the geometric Abel tail `(1-R)R^J/4`. -/
def lrCompactVWOneAbelTailEnclosure
    (J : ℕ) (box : CertificateBox) : RationalEnclosure :=
  RationalEnclosure.scale (1 / 4) <|
    RationalEnclosure.mul
      (lrCompactVOneSubREnclosure box)
      (RationalEnclosure.powNonnegative box.sInterval J)

theorem lrCompactVWOneAbelTailEnclosure_sound
    (J : ℕ) {box : CertificateBox} {point : CertificatePoint}
    (hbox : LRCompactVBoxValid box) (hpoint : box.Contains point) :
    (lrCompactVWOneAbelTailEnclosure J box).Contains
      (lrCompactVWOneAbelTail J point.s) := by
  have hs := lrCompactVOneSubREnclosure_sound hpoint
  have hR : box.sInterval.Contains point.s := ⟨hpoint.1, hpoint.2.1⟩
  have hpow := RationalEnclosure.contains_powNonnegative hbox.1 hR J
  have hmul := RationalEnclosure.contains_mul hs hpow
  have hscale := RationalEnclosure.contains_scale (1 / 4 : ℚ) hmul
  simpa [lrCompactVWOneAbelTailEnclosure, lrCompactVWOneAbelTail,
    div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hscale

/-- Full endpoint-kernel enclosure with a structured Abel tail. -/
def lrCompactVWOneEnclosure
    (terms J : ℕ) (box : CertificateBox) : RationalEnclosure :=
  let head := lrCompactVWOneAbelHeadEnclosure terms J box
  let tail := lrCompactVWOneAbelTailEnclosure J box
  ⟨head.lower, head.upper + tail.upper⟩

theorem lrCompactVWOneEnclosure_sound
    (terms J : ℕ) {box : CertificateBox} {point : CertificatePoint}
    (hbox : LRCompactVBoxValid box) (hpoint : box.Contains point)
    (hinterior : LRCompactVInterior point) :
    (lrCompactVWOneEnclosure terms J box).Contains
      (lrWKernel point.s 1) := by
  have hhead := lrCompactVWOneAbelHeadEnclosure_sound
    terms J hbox hpoint
  have htail := lrCompactVWOneAbelTailEnclosure_sound J hbox hpoint
  have hlower := lrCompactVWOneAbelHead_le hinterior.1 J
  have hupper := lrCompactVWOne_le_AbelHead_add_tail hinterior.1 J
  constructor
  · exact hhead.1.trans hlower
  · change lrWKernel point.s 1 ≤
      (((lrCompactVWOneAbelHeadEnclosure terms J box).upper +
        (lrCompactVWOneAbelTailEnclosure J box).upper : ℚ) : ℝ)
    norm_num only [Rat.cast_add]
    exact hupper.trans (add_le_add hhead.2 htail.2)

end CourtadeKumar
