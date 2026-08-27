import InformationTheory.CourtadeKumar.IntervalMidpointCertificate

/-!
# Mixed interval/midpoint certificates

Boxes touching `chi = 0` contain the continuous term `chi * log chi`, whose
derivative is unbounded.  The small-`s` replay encloses the complete `chi`
range directly and uses midpoint derivative control only in `s` and `k`.
This file proves that mixed leaf rule once and for all.
-/

namespace CourtadeKumar

/-- Replace only the smooth coordinates by the rational box midpoint. -/
def CertificateBox.anchorSK (box : CertificateBox)
    (point : CertificatePoint) : CertificatePoint :=
  { point with s := box.midpoint.s, k := box.midpoint.k }

lemma CertificateBox.anchorSK_mem
    {box : CertificateBox} {point : CertificatePoint}
    (hpoint : box.Contains point) :
    box.Contains (box.anchorSK point) := by
  have hmid := box.midpoint_mem hpoint
  exact ⟨hmid.1, hmid.2.1, hmid.2.2.1, hmid.2.2.2.1,
    hpoint.2.2.2.2.1, hpoint.2.2.2.2.2⟩

/-- Leaf data for a direct interval enclosure in `chi` and midpoint-form
control in the two smooth coordinates. -/
structure MidpointSKCertificate where
  value : RationalEnclosure
  derivS : RationalEnclosure
  derivK : RationalEnclosure

def MidpointSKCertificate.lowerBound
    (box : CertificateBox) (certificate : MidpointSKCertificate) : ℚ :=
  certificate.value.lower -
    certificate.derivS.maxAbs * RationalEnclosure.radius box.sInterval -
    certificate.derivK.maxAbs * RationalEnclosure.radius box.kInterval

def MidpointSKCertificate.check
    (box : CertificateBox) (certificate : MidpointSKCertificate) : Bool :=
  decide (0 < certificate.lowerBound box)

/-- Soundness of the endpoint leaf rule.  `value` may enclose a whole
`chi` interval; no derivative in that coordinate is assumed. -/
theorem MidpointSKCertificate.sound
    {target : CertificatePoint → ℝ}
    {box : CertificateBox} {certificate : MidpointSKCertificate}
    (hvalue : ∀ point, box.Contains point →
      certificate.value.Contains (target (box.anchorSK point)))
    (hlipschitz : BoxCoordinateLipschitz target box
      certificate.derivS.maxAbs certificate.derivK.maxAbs 0)
    (hcheck : certificate.check box = true)
    {point : CertificatePoint} (hpoint : box.Contains point) :
    0 < target point := by
  let center := box.midpoint
  let afterS : CertificatePoint := { point with s := center.s }
  let anchor : CertificatePoint := box.anchorSK point
  have hcenter := box.midpoint_mem hpoint
  have hafterS : box.Contains afterS := by
    rcases hpoint with ⟨_, _, hkLo, hkHi, hchiLo, hchiHi⟩
    exact ⟨hcenter.1, hcenter.2.1, hkLo, hkHi, hchiLo, hchiHi⟩
  have hanchor : box.Contains anchor := box.anchorSK_mem hpoint
  have hsRadius :
      |point.s - center.s| ≤ (RationalEnclosure.radius box.sInterval : ℝ) :=
    RationalEnclosure.abs_sub_center_le_radius
      (a := box.sInterval) ⟨hpoint.1, hpoint.2.1⟩
  have hkRadius :
      |afterS.k - center.k| ≤ (RationalEnclosure.radius box.kInterval : ℝ) :=
    RationalEnclosure.abs_sub_center_le_radius
      (a := box.kInterval) ⟨hpoint.2.2.1, hpoint.2.2.2.1⟩
  have hs := hlipschitz.s point afterS hpoint hafterS rfl rfl
  have hk : |target afterS - target anchor| ≤
      certificate.derivK.maxAbs * |afterS.k - anchor.k| := by
    apply hlipschitz.k afterS anchor hafterS hanchor
    · rfl
    · rfl
  have hsBound :
      |target point - target afterS| ≤
        (certificate.derivS.maxAbs : ℝ) *
          (RationalEnclosure.radius box.sInterval : ℝ) :=
    hs.trans (mul_le_mul_of_nonneg_left hsRadius
      (by exact_mod_cast certificate.derivS.maxAbs_nonnegative))
  have hkBound :
      |target afterS - target anchor| ≤
        (certificate.derivK.maxAbs : ℝ) *
          (RationalEnclosure.radius box.kInterval : ℝ) := by
    have hanchorK : anchor.k = center.k := rfl
    rw [hanchorK] at hk
    exact hk.trans (mul_le_mul_of_nonneg_left hkRadius
      (by exact_mod_cast certificate.derivK.maxAbs_nonnegative))
  have htotal :
      |target point - target anchor| ≤
        (certificate.derivS.maxAbs : ℝ) *
            (RationalEnclosure.radius box.sInterval : ℝ) +
          (certificate.derivK.maxAbs : ℝ) *
            (RationalEnclosure.radius box.kInterval : ℝ) := by
    calc
      |target point - target anchor| =
          |(target point - target afterS) +
            (target afterS - target anchor)| := by congr 1; ring
      _ ≤ |target point - target afterS| +
          |target afterS - target anchor| := abs_add_le _ _
      _ ≤ _ := add_le_add hsBound hkBound
  have hpositive : (0 : ℚ) < certificate.lowerBound box := by
    simpa [MidpointSKCertificate.check] using hcheck
  have hpositiveReal : (0 : ℝ) <
      (certificate.lowerBound box : ℚ) := by exact_mod_cast hpositive
  have habsLower : -(target point - target anchor) ≤
      |target point - target anchor| := neg_le_abs _
  have hvalueLower : (certificate.value.lower : ℝ) ≤ target anchor :=
    (hvalue point hpoint).1
  norm_num [MidpointSKCertificate.lowerBound] at hpositiveReal
  norm_num at htotal
  linarith

end CourtadeKumar
