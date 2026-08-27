import InformationTheory.CourtadeKumar.IntervalMidpointCertificate
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Derivative enclosures imply midpoint Lipschitz bounds

This module discharges the analytic mean-value step between verified partial
derivative enclosures and the coordinatewise Lipschitz hypothesis consumed by
`MidpointCertificate.sound`.
-/

open Set

namespace CourtadeKumar

/-- Semantic data certified by interval automatic differentiation on one
box.  The rational enclosures are the data stored in the midpoint leaf. -/
structure BoxDerivativeEnclosures
    (target : CertificatePoint → ℝ) (box : CertificateBox)
    (certificate : MidpointCertificate) where
  partialS : CertificatePoint → ℝ
  partialK : CertificatePoint → ℝ
  partialChi : CertificatePoint → ℝ
  derivS : ∀ point, box.Contains point →
    HasDerivAt (fun s ↦ target { point with s := s }) (partialS point) point.s
  derivK : ∀ point, box.Contains point →
    HasDerivAt (fun k ↦ target { point with k := k }) (partialK point) point.k
  derivChi : ∀ point, box.Contains point →
    HasDerivAt (fun chi ↦ target { point with chi := chi })
      (partialChi point) point.chi
  boundS : ∀ point, box.Contains point →
    certificate.derivS.Contains (partialS point)
  boundK : ∀ point, box.Contains point →
    certificate.derivK.Contains (partialK point)
  boundChi : ∀ point, box.Contains point →
    certificate.derivChi.Contains (partialChi point)

theorem BoxDerivativeEnclosures.toCoordinateLipschitz
    {target : CertificatePoint → ℝ} {box : CertificateBox}
    {certificate : MidpointCertificate}
    (data : BoxDerivativeEnclosures target box certificate) :
    BoxCoordinateLipschitz target box
      certificate.derivS.maxAbs certificate.derivK.maxAbs
      certificate.derivChi.maxAbs := by
  constructor
  · intro p q hp hq hk hchi
    let f : ℝ → ℝ := fun s ↦ target { p with s := s }
    let f' : ℝ → ℝ := fun s ↦ data.partialS { p with s := s }
    have hderiv : ∀ s ∈ Icc (box.sLo : ℝ) box.sHi,
        HasDerivWithinAt f (f' s) (Icc (box.sLo : ℝ) box.sHi) s := by
      intro s hs
      have hpoint : box.Contains { p with s := s } :=
        ⟨hs.1, hs.2, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2.1,
          hp.2.2.2.2.2⟩
      simpa [f, f'] using
        (data.derivS { p with s := s } hpoint).hasDerivWithinAt
    have hbound : ∀ s ∈ Icc (box.sLo : ℝ) box.sHi,
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
  · intro p q hp hq hs hchi
    let f : ℝ → ℝ := fun k ↦ target { p with k := k }
    let f' : ℝ → ℝ := fun k ↦ data.partialK { p with k := k }
    have hderiv : ∀ k ∈ Icc (box.kLo : ℝ) box.kHi,
        HasDerivWithinAt f (f' k) (Icc (box.kLo : ℝ) box.kHi) k := by
      intro k hk
      have hpoint : box.Contains { p with k := k } :=
        ⟨hp.1, hp.2.1, hk.1, hk.2, hp.2.2.2.2.1, hp.2.2.2.2.2⟩
      simpa [f, f'] using
        (data.derivK { p with k := k } hpoint).hasDerivWithinAt
    have hbound : ∀ k ∈ Icc (box.kLo : ℝ) box.kHi,
        ‖f' k‖ ≤ (certificate.derivK.maxAbs : ℝ) := by
      intro k hk
      have hpoint : box.Contains { p with k := k } :=
        ⟨hp.1, hp.2.1, hk.1, hk.2, hp.2.2.2.2.1, hp.2.2.2.2.2⟩
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
  · intro p q hp hq hs hk
    let f : ℝ → ℝ := fun chi ↦ target { p with chi := chi }
    let f' : ℝ → ℝ := fun chi ↦ data.partialChi { p with chi := chi }
    have hderiv : ∀ chi ∈ Icc (box.chiLo : ℝ) box.chiHi,
        HasDerivWithinAt f (f' chi) (Icc (box.chiLo : ℝ) box.chiHi) chi := by
      intro chi hchi
      have hpoint : box.Contains { p with chi := chi } :=
        ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hchi.1, hchi.2⟩
      simpa [f, f'] using
        (data.derivChi { p with chi := chi } hpoint).hasDerivWithinAt
    have hbound : ∀ chi ∈ Icc (box.chiLo : ℝ) box.chiHi,
        ‖f' chi‖ ≤ (certificate.derivChi.maxAbs : ℝ) := by
      intro chi hchi
      have hpoint : box.Contains { p with chi := chi } :=
        ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hchi.1, hchi.2⟩
      simpa [f', Real.norm_eq_abs] using
        RationalEnclosure.abs_le_maxAbs (data.boundChi _ hpoint)
    have hmean := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      hderiv hbound (convex_Icc (box.chiLo : ℝ) box.chiHi)
      ⟨hp.2.2.2.2.1, hp.2.2.2.2.2⟩
      ⟨hq.2.2.2.2.1, hq.2.2.2.2.2⟩
    have hqPoint : ({ p with chi := q.chi } : CertificatePoint) = q := by
      cases p
      cases q
      simp_all
    dsimp [f] at hmean
    rw [hqPoint] at hmean
    change |target q - target p| ≤
      (certificate.derivChi.maxAbs : ℝ) * |q.chi - p.chi| at hmean
    simpa [abs_sub_comm] using hmean

/-- The full midpoint leaf implication from interval value and partial
derivative enclosures. -/
theorem MidpointCertificate.sound_of_derivativeEnclosures
    {target : CertificatePoint → ℝ}
    {box : CertificateBox} {certificate : MidpointCertificate}
    (hvalue : certificate.value.Contains (target box.midpoint))
    (hderivatives : BoxDerivativeEnclosures target box certificate)
    (hcheck : certificate.check box = true)
    {point : CertificatePoint} (hpoint : box.Contains point) :
    0 < target point :=
  certificate.sound hvalue hderivatives.toCoordinateLipschitz hcheck hpoint

end CourtadeKumar
