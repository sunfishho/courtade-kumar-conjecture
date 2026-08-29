import InformationTheory.CourtadeKumar.IntervalMidpointSKCertificate

/-!
# Three-coordinate midpoint certificates on an open `chi` chart

This module gives the full midpoint rule while requiring derivative
hypotheses only at points whose `chi` coordinate satisfies `chiGood`.  The
only extra analytic assumption is that `chiGood` is preserved on the closed
segment joining the queried `chi` coordinate to the midpoint coordinate.
-/

namespace CourtadeKumar

/-- Coordinatewise Lipschitz control on the part of a box lying in a
`chiGood` chart.  The `s` and `k` moves keep `chi` fixed; the `chi` move has
good endpoints and is later justified by a segment-preservation hypothesis. -/
structure BoxCoordinateLipschitzOn
    (target : CertificatePoint → ℝ) (box : CertificateBox)
    (chiGood : ℝ → Prop) (sBound kBound chiBound : ℝ) : Prop where
  s : ∀ p q, box.Contains p → box.Contains q → chiGood p.chi →
    p.k = q.k → p.chi = q.chi →
    |target p - target q| ≤ sBound * |p.s - q.s|
  k : ∀ p q, box.Contains p → box.Contains q → chiGood p.chi →
    p.s = q.s → p.chi = q.chi →
    |target p - target q| ≤ kBound * |p.k - q.k|
  chi : ∀ p q, box.Contains p → box.Contains q →
    chiGood p.chi → chiGood q.chi →
    p.s = q.s → p.k = q.k →
    |target p - target q| ≤ chiBound * |p.chi - q.chi|

/-- Partial derivative enclosures restricted to the open `chiGood` chart.
The enclosure bounds themselves need no chart hypothesis. -/
structure BoxDerivativeEnclosuresOn
    (target : CertificatePoint → ℝ) (box : CertificateBox)
    (certificate : MidpointCertificate) (chiGood : ℝ → Prop) where
  partialS : CertificatePoint → ℝ
  partialK : CertificatePoint → ℝ
  partialChi : CertificatePoint → ℝ
  derivS : ∀ point, box.Contains point → chiGood point.chi →
    HasDerivAt (fun s ↦ target { point with s := s })
      (partialS point) point.s
  derivK : ∀ point, box.Contains point → chiGood point.chi →
    HasDerivAt (fun k ↦ target { point with k := k })
      (partialK point) point.k
  derivChi : ∀ point, box.Contains point → chiGood point.chi →
    HasDerivAt (fun chi ↦ target { point with chi := chi })
      (partialChi point) point.chi
  boundS : ∀ point, box.Contains point →
    certificate.derivS.Contains (partialS point)
  boundK : ∀ point, box.Contains point →
    certificate.derivK.Contains (partialK point)
  boundChi : ∀ point, box.Contains point →
    certificate.derivChi.Contains (partialChi point)

/-- Restricted derivative enclosures imply coordinatewise Lipschitz bounds.
For the `chi` coordinate, the mean-value interval is exactly the unordered
interval between the two good endpoints, rather than the whole box. -/
theorem BoxDerivativeEnclosuresOn.toCoordinateLipschitzOn
    {target : CertificatePoint → ℝ} {box : CertificateBox}
    {certificate : MidpointCertificate} {chiGood : ℝ → Prop}
    (data : BoxDerivativeEnclosuresOn target box certificate chiGood)
    (chiGood_segment : ∀ {a b x : ℝ}, chiGood a → chiGood b →
      x ∈ Set.uIcc a b → chiGood x) :
    BoxCoordinateLipschitzOn target box chiGood
      certificate.derivS.maxAbs certificate.derivK.maxAbs
      certificate.derivChi.maxAbs := by
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
  · intro p q hp hq hpGood hqGood hs hk
    let f : ℝ → ℝ := fun chi ↦ target { p with chi := chi }
    let f' : ℝ → ℝ := fun chi ↦ data.partialChi { p with chi := chi }
    have hderiv : ∀ chi ∈ Set.uIcc p.chi q.chi,
        HasDerivWithinAt f (f' chi) (Set.uIcc p.chi q.chi) chi := by
      intro chi hchi
      have hchiBox : (box.chiLo : ℝ) ≤ chi ∧ chi ≤ box.chiHi := by
        rcases Set.mem_uIcc.mp hchi with hforward | hbackward
        · exact ⟨hp.2.2.2.2.1.trans hforward.1,
            hforward.2.trans hq.2.2.2.2.2⟩
        · exact ⟨hq.2.2.2.2.1.trans hbackward.1,
            hbackward.2.trans hp.2.2.2.2.2⟩
      have hpoint : box.Contains { p with chi := chi } :=
        ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1,
          hchiBox.1, hchiBox.2⟩
      have hgood : chiGood chi :=
        chiGood_segment hpGood hqGood hchi
      simpa [f, f'] using
        (data.derivChi { p with chi := chi } hpoint hgood).hasDerivWithinAt
    have hbound : ∀ chi ∈ Set.uIcc p.chi q.chi,
        ‖f' chi‖ ≤ (certificate.derivChi.maxAbs : ℝ) := by
      intro chi hchi
      have hchiBox : (box.chiLo : ℝ) ≤ chi ∧ chi ≤ box.chiHi := by
        rcases Set.mem_uIcc.mp hchi with hforward | hbackward
        · exact ⟨hp.2.2.2.2.1.trans hforward.1,
            hforward.2.trans hq.2.2.2.2.2⟩
        · exact ⟨hq.2.2.2.2.1.trans hbackward.1,
            hbackward.2.trans hp.2.2.2.2.2⟩
      have hpoint : box.Contains { p with chi := chi } :=
        ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1,
          hchiBox.1, hchiBox.2⟩
      simpa [f', Real.norm_eq_abs] using
        RationalEnclosure.abs_le_maxAbs (data.boundChi _ hpoint)
    have hmean := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      hderiv hbound (convex_uIcc p.chi q.chi)
      Set.left_mem_uIcc Set.right_mem_uIcc
    have hqPoint : ({ p with chi := q.chi } : CertificatePoint) = q := by
      cases p
      cases q
      simp_all
    dsimp [f] at hmean
    rw [hqPoint] at hmean
    change |target q - target p| ≤
      (certificate.derivChi.maxAbs : ℝ) * |q.chi - p.chi| at hmean
    simpa [abs_sub_comm] using hmean

/-- Soundness of the ordinary three-coordinate midpoint rule on a chart.
The queried point and the box midpoint must lie in `chiGood`. -/
theorem MidpointCertificate.soundOn
    {target : CertificatePoint → ℝ} {chiGood : ℝ → Prop}
    {box : CertificateBox} {certificate : MidpointCertificate}
    (hvalue : certificate.value.Contains (target box.midpoint))
    (hlipschitz : BoxCoordinateLipschitzOn target box chiGood
      certificate.derivS.maxAbs certificate.derivK.maxAbs
      certificate.derivChi.maxAbs)
    (hcheck : certificate.check box = true)
    (hcenterGood : chiGood box.midpoint.chi)
    {point : CertificatePoint} (hpoint : box.Contains point)
    (hgood : chiGood point.chi) :
    0 < target point := by
  let center := box.midpoint
  let afterS : CertificatePoint := { point with s := center.s }
  let afterK : CertificatePoint := { afterS with k := center.k }
  have hcenter : box.Contains center := box.midpoint_mem hpoint
  have hafterS : box.Contains afterS := by
    rcases hpoint with ⟨_, _, hkLo, hkHi, hchiLo, hchiHi⟩
    exact ⟨hcenter.1, hcenter.2.1, hkLo, hkHi, hchiLo, hchiHi⟩
  have hafterK : box.Contains afterK := by
    exact ⟨hcenter.1, hcenter.2.1, hcenter.2.2.1, hcenter.2.2.2.1,
      hpoint.2.2.2.2.1, hpoint.2.2.2.2.2⟩
  have hsRadius :
      |point.s - center.s| ≤ (RationalEnclosure.radius box.sInterval : ℝ) :=
    RationalEnclosure.abs_sub_center_le_radius
      (a := box.sInterval) ⟨hpoint.1, hpoint.2.1⟩
  have hkRadius :
      |afterS.k - center.k| ≤ (RationalEnclosure.radius box.kInterval : ℝ) :=
    RationalEnclosure.abs_sub_center_le_radius
      (a := box.kInterval) ⟨hpoint.2.2.1, hpoint.2.2.2.1⟩
  have hchiRadius :
      |afterK.chi - center.chi| ≤
        (RationalEnclosure.radius box.chiInterval : ℝ) :=
    RationalEnclosure.abs_sub_center_le_radius
      (a := box.chiInterval) ⟨hpoint.2.2.2.2.1, hpoint.2.2.2.2.2⟩
  have hs := hlipschitz.s point afterS hpoint hafterS hgood rfl rfl
  have hk := hlipschitz.k afterS afterK hafterS hafterK hgood rfl rfl
  have hchi := hlipschitz.chi afterK center hafterK hcenter
    hgood hcenterGood rfl rfl
  have hsBound :
      |target point - target afterS| ≤
        (certificate.derivS.maxAbs : ℝ) *
          (RationalEnclosure.radius box.sInterval : ℝ) :=
    hs.trans (mul_le_mul_of_nonneg_left hsRadius
      (by exact_mod_cast certificate.derivS.maxAbs_nonnegative))
  have hkBound :
      |target afterS - target afterK| ≤
        (certificate.derivK.maxAbs : ℝ) *
          (RationalEnclosure.radius box.kInterval : ℝ) :=
    hk.trans (mul_le_mul_of_nonneg_left hkRadius
      (by exact_mod_cast certificate.derivK.maxAbs_nonnegative))
  have hchiBound :
      |target afterK - target center| ≤
        (certificate.derivChi.maxAbs : ℝ) *
          (RationalEnclosure.radius box.chiInterval : ℝ) :=
    hchi.trans (mul_le_mul_of_nonneg_left hchiRadius
      (by exact_mod_cast certificate.derivChi.maxAbs_nonnegative))
  have htotal :
      |target point - target center| ≤
        (certificate.derivS.maxAbs : ℝ) *
            (RationalEnclosure.radius box.sInterval : ℝ) +
          (certificate.derivK.maxAbs : ℝ) *
            (RationalEnclosure.radius box.kInterval : ℝ) +
          (certificate.derivChi.maxAbs : ℝ) *
            (RationalEnclosure.radius box.chiInterval : ℝ) := by
    calc
      |target point - target center| =
          |(target point - target afterS) +
            (target afterS - target afterK) +
            (target afterK - target center)| := by congr 1; ring
      _ ≤ |target point - target afterS| +
          |target afterS - target afterK| +
          |target afterK - target center| := by
            calc
              _ ≤ |(target point - target afterS) +
                    (target afterS - target afterK)| +
                    |target afterK - target center| := abs_add_le _ _
              _ ≤ (|target point - target afterS| +
                    |target afterS - target afterK|) +
                    |target afterK - target center| :=
                  add_le_add (abs_add_le _ _) le_rfl
      _ ≤ _ := add_le_add (add_le_add hsBound hkBound) hchiBound
  have hpositive : (0 : ℚ) < certificate.lowerBound box := by
    simpa [MidpointCertificate.check] using hcheck
  have hpositiveReal : (0 : ℝ) < (certificate.lowerBound box : ℚ) := by
    exact_mod_cast hpositive
  have habsLower : -(target point - target center) ≤
      |target point - target center| := neg_le_abs _
  have hvalueLower : (certificate.value.lower : ℝ) ≤ target center := by
    change (certificate.value.lower : ℝ) ≤ target box.midpoint
    exact hvalue.1
  norm_num [MidpointCertificate.lowerBound] at hpositiveReal
  norm_num at htotal
  linarith

/-- Full chart-restricted midpoint implication from derivative enclosures. -/
theorem MidpointCertificate.soundOn_of_derivativeEnclosures
    {target : CertificatePoint → ℝ} {chiGood : ℝ → Prop}
    {box : CertificateBox} {certificate : MidpointCertificate}
    (hvalue : certificate.value.Contains (target box.midpoint))
    (hderivatives :
      BoxDerivativeEnclosuresOn target box certificate chiGood)
    (chiGood_segment : ∀ {a b x : ℝ}, chiGood a → chiGood b →
      x ∈ Set.uIcc a b → chiGood x)
    (hcheck : certificate.check box = true)
    (hcenterGood : chiGood box.midpoint.chi)
    {point : CertificatePoint} (hpoint : box.Contains point)
    (hgood : chiGood point.chi) :
    0 < target point :=
  certificate.soundOn hvalue
    (hderivatives.toCoordinateLipschitzOn chiGood_segment)
    hcheck hcenterGood hpoint hgood

end CourtadeKumar
