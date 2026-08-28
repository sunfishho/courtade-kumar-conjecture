import InformationTheory.CourtadeKumar.IntervalDerivativeCertificate

/-!
# Mixed interval/midpoint certificates

Boxes touching `chi = 0` contain the continuous term `chi * log chi`, whose
derivative is unbounded.  The small-`s` replay encloses the complete `chi`
range directly and uses midpoint derivative control only in `s` and `k`.
This file proves that mixed leaf rule once and for all.
-/

namespace CourtadeKumar

/-- Coordinatewise Lipschitz control in `s` and `k`, restricted to points
whose unchanged `chi` coordinate satisfies `chiGood`.  This is the natural
contract for a box that may touch a nonsmooth `chi` endpoint while the point
being certified remains in the open chart. -/
structure BoxSKCoordinateLipschitzOn
    (target : CertificatePoint → ℝ) (box : CertificateBox)
    (chiGood : ℝ → Prop) (sBound kBound : ℝ) : Prop where
  s : ∀ p q, box.Contains p → box.Contains q → chiGood p.chi →
    p.k = q.k → p.chi = q.chi →
    |target p - target q| ≤ sBound * |p.s - q.s|
  k : ∀ p q, box.Contains p → box.Contains q → chiGood p.chi →
    p.s = q.s → p.chi = q.chi →
    |target p - target q| ≤ kBound * |p.k - q.k|

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

/-- Partial derivative enclosures needed for the two smooth coordinates,
again only at points satisfying an invariant condition on `chi`. -/
structure BoxSKDerivativeEnclosuresOn
    (target : CertificatePoint → ℝ) (box : CertificateBox)
    (certificate : MidpointSKCertificate) (chiGood : ℝ → Prop) where
  partialS : CertificatePoint → ℝ
  partialK : CertificatePoint → ℝ
  derivS : ∀ point, box.Contains point → chiGood point.chi →
    HasDerivAt (fun s ↦ target { point with s := s })
      (partialS point) point.s
  derivK : ∀ point, box.Contains point → chiGood point.chi →
    HasDerivAt (fun k ↦ target { point with k := k })
      (partialK point) point.k
  boundS : ∀ point, box.Contains point →
    certificate.derivS.Contains (partialS point)
  boundK : ∀ point, box.Contains point →
    certificate.derivK.Contains (partialK point)

theorem BoxSKDerivativeEnclosuresOn.toCoordinateLipschitzOn
    {target : CertificatePoint → ℝ} {box : CertificateBox}
    {certificate : MidpointSKCertificate} {chiGood : ℝ → Prop}
    (data : BoxSKDerivativeEnclosuresOn target box certificate chiGood) :
    BoxSKCoordinateLipschitzOn target box chiGood
      certificate.derivS.maxAbs certificate.derivK.maxAbs := by
  constructor
  · intro p q hp hq hgood hk hchi
    let f : ℝ → ℝ := fun s ↦ target { p with s := s }
    let f' : ℝ → ℝ := fun s ↦ data.partialS { p with s := s }
    have hderiv : ∀ s ∈ Set.Icc (box.sLo : ℝ) box.sHi,
        HasDerivWithinAt f (f' s) (Set.Icc (box.sLo : ℝ) box.sHi) s := by
      intro s hs
      have hpoint : box.Contains { p with s := s } :=
        ⟨hs.1, hs.2, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2.1,
          hp.2.2.2.2.2⟩
      simpa [f, f'] using
        (data.derivS { p with s := s } hpoint hgood).hasDerivWithinAt
    have hbound : ∀ s ∈ Set.Icc (box.sLo : ℝ) box.sHi,
        ‖f' s‖ ≤ (certificate.derivS.maxAbs : ℝ) := by
      intro s hs
      have hpoint : box.Contains { p with s := s } :=
        ⟨hs.1, hs.2, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2.1,
          hp.2.2.2.2.2⟩
      simpa [f', Real.norm_eq_abs] using
        RationalEnclosure.abs_le_maxAbs (data.boundS _ hpoint)
    have hmean := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      hderiv hbound (convex_Icc (box.sLo : ℝ) box.sHi)
      ⟨hp.1, hp.2.1⟩ ⟨hq.1, hq.2.1⟩
    have hqPoint : ({ p with s := q.s } : CertificatePoint) = q := by
      cases p
      cases q
      simp_all
    dsimp [f] at hmean
    rw [hqPoint] at hmean
    change |target q - target p| ≤
      (certificate.derivS.maxAbs : ℝ) * |q.s - p.s| at hmean
    simpa [abs_sub_comm] using hmean
  · intro p q hp hq hgood hs hchi
    let f : ℝ → ℝ := fun k ↦ target { p with k := k }
    let f' : ℝ → ℝ := fun k ↦ data.partialK { p with k := k }
    have hderiv : ∀ k ∈ Set.Icc (box.kLo : ℝ) box.kHi,
        HasDerivWithinAt f (f' k) (Set.Icc (box.kLo : ℝ) box.kHi) k := by
      intro k hk
      have hpoint : box.Contains { p with k := k } :=
        ⟨hp.1, hp.2.1, hk.1, hk.2, hp.2.2.2.2.1,
          hp.2.2.2.2.2⟩
      simpa [f, f'] using
        (data.derivK { p with k := k } hpoint hgood).hasDerivWithinAt
    have hbound : ∀ k ∈ Set.Icc (box.kLo : ℝ) box.kHi,
        ‖f' k‖ ≤ (certificate.derivK.maxAbs : ℝ) := by
      intro k hk
      have hpoint : box.Contains { p with k := k } :=
        ⟨hp.1, hp.2.1, hk.1, hk.2, hp.2.2.2.2.1,
          hp.2.2.2.2.2⟩
      simpa [f', Real.norm_eq_abs] using
        RationalEnclosure.abs_le_maxAbs (data.boundK _ hpoint)
    have hmean := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      hderiv hbound (convex_Icc (box.kLo : ℝ) box.kHi)
      ⟨hp.2.2.1, hp.2.2.2.1⟩ ⟨hq.2.2.1, hq.2.2.2.1⟩
    have hqPoint : ({ p with k := q.k } : CertificatePoint) = q := by
      cases p
      cases q
      simp_all
    dsimp [f] at hmean
    rw [hqPoint] at hmean
    change |target q - target p| ≤
      (certificate.derivK.maxAbs : ℝ) * |q.k - p.k| at hmean
    simpa [abs_sub_comm] using hmean

def MidpointSKCertificate.lowerBound
    (box : CertificateBox) (certificate : MidpointSKCertificate) : ℚ :=
  certificate.value.lower -
    certificate.derivS.maxAbs * RationalEnclosure.radius box.sInterval -
    certificate.derivK.maxAbs * RationalEnclosure.radius box.kInterval

def MidpointSKCertificate.check
    (box : CertificateBox) (certificate : MidpointSKCertificate) : Bool :=
  decide (0 < certificate.lowerBound box)

/-- Soundness of the endpoint leaf rule on a `chi`-invariant domain.
`value` may enclose a whole `chi` interval; no derivative in that coordinate
is assumed. -/
theorem MidpointSKCertificate.soundOn
    {target : CertificatePoint → ℝ}
    {chiGood : ℝ → Prop}
    {box : CertificateBox} {certificate : MidpointSKCertificate}
    (hvalue : ∀ point, box.Contains point →
      certificate.value.Contains (target (box.anchorSK point)))
    (hlipschitz : BoxSKCoordinateLipschitzOn target box chiGood
      certificate.derivS.maxAbs certificate.derivK.maxAbs)
    (hcheck : certificate.check box = true)
    {point : CertificatePoint} (hpoint : box.Contains point)
    (hgood : chiGood point.chi) :
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
  have hs := hlipschitz.s point afterS hpoint hafterS hgood rfl rfl
  have hk : |target afterS - target anchor| ≤
      certificate.derivK.maxAbs * |afterS.k - anchor.k| := by
    apply hlipschitz.k afterS anchor hafterS hanchor hgood
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

/-- Unrestricted compatibility wrapper for existing callers. -/
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
  have hrestricted : BoxSKCoordinateLipschitzOn target box
      (fun _ ↦ True) certificate.derivS.maxAbs
        certificate.derivK.maxAbs := by
    constructor
    · intro p q hp hq _ hk hchi
      exact hlipschitz.s p q hp hq hk hchi
    · intro p q hp hq _ hs hchi
      exact hlipschitz.k p q hp hq hs hchi
  exact certificate.soundOn hvalue hrestricted hcheck hpoint trivial

/-- Full endpoint-leaf implication from smooth-coordinate derivative
enclosures on a `chi`-invariant domain. -/
theorem MidpointSKCertificate.soundOn_of_derivativeEnclosures
    {target : CertificatePoint → ℝ} {chiGood : ℝ → Prop}
    {box : CertificateBox} {certificate : MidpointSKCertificate}
    (hvalue : ∀ point, box.Contains point →
      certificate.value.Contains (target (box.anchorSK point)))
    (hderivatives :
      BoxSKDerivativeEnclosuresOn target box certificate chiGood)
    (hcheck : certificate.check box = true)
    {point : CertificatePoint} (hpoint : box.Contains point)
    (hgood : chiGood point.chi) :
    0 < target point :=
  certificate.soundOn hvalue hderivatives.toCoordinateLipschitzOn
    hcheck hpoint hgood

end CourtadeKumar
