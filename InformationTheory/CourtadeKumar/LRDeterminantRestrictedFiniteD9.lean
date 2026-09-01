import InformationTheory.CourtadeKumar.LRDeterminantFiniteD9PayloadFree

/-!
# Restricted finite-D9 replay adapters

The final determinant ledger only consumes points with `s < k <= 4`.
These adapters allow generated D9 trees to certify exactly that intersection
instead of replaying the unused historical region above `k = 4`.
-/

namespace CourtadeKumar

/-- A raw D9 tree on any root containing the restricted region supplies the
exact row interface used by `LRDeterminantKLeFourFiniteRegionLedger`. -/
theorem lrDeterminantKLeFourRegionCertificate_of_rawD9Tree
    {root : CertificateBox} {Region : CertificatePoint → Prop}
    (root_contains : ∀ {point : CertificatePoint},
      LRHighShapeInterior point → Region point →
        point.s < point.k → point.k ≤ 4 → root.Contains point)
    (tree : LRFiniteDeterminantRawD9CheckedTree root) :
    ∀ point : CertificatePoint,
      LRHighShapeInterior point →
      LRHighShapeVRelevant point →
      Region point →
      point.s < point.k →
      point.k ≤ 4 →
      LRDeterminantAdmittedTarget point := by
  intro point hinterior hrelevant hregion hK hkFour
  exact lrDeterminantAdmittedTarget_of_D9ReplayTarget hinterior
    (tree.target_nonnegative
      (root_contains hinterior hregion hK hkFour) hrelevant)

/-- The fixed-16 historical root clipped to the only range used by the final
restricted ledger. -/
abbrev lrDeterminantFixed16KLeFourRoot : CertificateBox :=
  lrDeterminantFixed16Root.lower .k 4

theorem lrDeterminantFixed16KLeFourRoot_contains
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hregion : LRDeterminantFixed16Region point)
    (_hK : point.s < point.k) (hkFour : point.k ≤ 4) :
    lrDeterminantFixed16KLeFourRoot.Contains point := by
  rcases lrDeterminantFixed16Root_contains hinterior hregion with
    ⟨hsLo, hsHi, hkLo, _hkHi, hchiLo, hchiHi⟩
  simpa [lrDeterminantFixed16KLeFourRoot, CertificateBox.Contains,
    CertificateBox.lower] using
      And.intro hsLo (And.intro hsHi (And.intro hkLo
        (And.intro hkFour (And.intro hchiLo hchiHi))))

/-- A checked topology on the clipped fixed-16 root closes the corresponding
field of the restricted determinant ledger. -/
theorem lrDeterminantFixed16KLeFourRegion_certificate_of_D9Tree
    (tree : LRFiniteDeterminantRawD9CheckedTree
      lrDeterminantFixed16KLeFourRoot) :
    ∀ point : CertificatePoint,
      LRHighShapeInterior point →
      LRHighShapeVRelevant point →
      LRDeterminantFixed16Region point →
      point.s < point.k →
      point.k ≤ 4 →
      LRDeterminantAdmittedTarget point :=
  lrDeterminantKLeFourRegionCertificate_of_rawD9Tree
    lrDeterminantFixed16KLeFourRoot_contains tree

end CourtadeKumar
