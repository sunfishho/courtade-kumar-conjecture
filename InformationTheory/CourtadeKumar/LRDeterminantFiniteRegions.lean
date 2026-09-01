import InformationTheory.CourtadeKumar.LRDeterminantRegionInterfaces

/-!
# Checked-tree interfaces for the finite determinant ledger

The seven finite rows in the audited determinant decomposition have rational
coordinate bounds.  This module records their exact axis-aligned root hulls and
proves the required containment statements.  The two sloping regions
(`KCorridor` and `UpperK`) additionally use their audited `(s,K,h)` chart,
with `K = k/s` and `h = sqrt chi`; encode/decode is proved exact in Lean.

No concrete tree is accepted here.  Instead, a generic packaged tree contains
its own payload type, executable leaf checker, soundness theorem, certificate,
and a kernel proof that the Boolean traversal returns `true`.  These generic
packages directly enclose the admitted determinant expressions.  The
historical replay data instead encloses sign-equivalent scaled targets `N1`
and `S1/e`; its exact interfaces and positive-factor adapters are provided in
`LRDeterminantFiniteReplayTargets`.
-/

namespace CourtadeKumar

/-! ## Exact rational root hulls -/

/-- Root hull for `2⁻¹⁴ ≤ s ≤ 2⁻⁷`, `1 ≤ k ≤ 32`. -/
def lrDeterminantFixed1To32Root : CertificateBox where
  sLo := 1 / 16384
  sHi := 1 / 128
  kLo := 1
  kHi := 32
  chiLo := 0
  chiHi := 1

/-- Smallest axis-aligned raw `(s,k,chi)` hull of
`2⁻⁷ ≤ s ≤ 2⁻⁶`, `s ≤ k ≤ 128s`.  The audited replay instead uses the exact
`(s,K,h)` root defined below. -/
def lrDeterminantKCorridorRawHull : CertificateBox where
  sLo := 1 / 128
  sHi := 1 / 64
  kLo := 1 / 128
  kHi := 2
  chiLo := 0
  chiHi := 1

/-- Root hull for `2⁻⁷ ≤ s ≤ 2⁻⁶`, `1 ≤ k ≤ 128`. -/
def lrDeterminantFixed1To128Root : CertificateBox where
  sLo := 1 / 128
  sHi := 1 / 64
  kLo := 1
  kHi := 128
  chiLo := 0
  chiHi := 1

/-- Smallest axis-aligned raw `(s,k,chi)` hull of
`2⁻⁶ ≤ s ≤ 2⁻⁵`, `s ≤ k ≤ 4s`.  The audited first-bracket replay instead
uses the exact `(s,K,h)` root defined below. -/
def lrDeterminantUpperKRawHull : CertificateBox where
  sLo := 1 / 64
  sHi := 1 / 32
  kLo := 1 / 64
  kHi := 1 / 8
  chiLo := 0
  chiHi := 1

/-- Exact audited `(s,K,h)` root for the seven corridor trees.  In this root,
the fields called `k` and `chi` by the generic certificate structure store
`K = k/s` and `h = sqrt chi`, respectively. -/
def lrDeterminantKCorridorKChartRoot : CertificateBox where
  sLo := 1 / 128
  sHi := 1 / 64
  kLo := 1
  kHi := 128
  chiLo := 0
  chiHi := 1

/-- Exact audited `(s,K,h)` root for the two upper-corridor first-bracket
trees. -/
def lrDeterminantUpperKKChartRoot : CertificateBox where
  sLo := 1 / 64
  sHi := 1 / 32
  kLo := 1
  kHi := 4
  chiLo := 0
  chiHi := 1

/-- Root hull for `2⁻⁶ ≤ s ≤ 2⁻⁵`, `2⁻⁵ ≤ k ≤ 64`. -/
def lrDeterminantFixed64Root : CertificateBox where
  sLo := 1 / 64
  sHi := 1 / 32
  kLo := 1 / 32
  kHi := 64
  chiLo := 0
  chiHi := 1

/-- Root hull for `2⁻⁵ ≤ s ≤ 2⁻⁴`, `2⁻⁵ ≤ k ≤ 32`. -/
def lrDeterminantFixed32Root : CertificateBox where
  sLo := 1 / 32
  sHi := 1 / 16
  kLo := 1 / 32
  kHi := 32
  chiLo := 0
  chiHi := 1

/-- Root hull for `2⁻⁴ ≤ s ≤ 1/10`, `2⁻⁴ ≤ k ≤ 16`. -/
def lrDeterminantFixed16Root : CertificateBox where
  sLo := 1 / 16
  sHi := 1 / 10
  kLo := 1 / 16
  kHi := 16
  chiLo := 0
  chiHi := 1

/-- The open chart supplies the closed `chi` faces used by every finite root. -/
private theorem lrDeterminant_chi_mem_closed
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point) :
    0 ≤ point.chi ∧ point.chi ≤ 1 :=
  ⟨hinterior.2.2.1.le, hinterior.2.2.2.le⟩

theorem lrDeterminantFixed1To32Root_contains
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hregion : LRDeterminantFixed1To32Region point) :
    lrDeterminantFixed1To32Root.Contains point := by
  rcases hregion with ⟨hsLo, hsHi, hkLo, hkHi⟩
  rcases lrDeterminant_chi_mem_closed hinterior with ⟨hchiLo, hchiHi⟩
  simpa [lrDeterminantFixed1To32Root, CertificateBox.Contains] using
    And.intro hsLo (And.intro hsHi (And.intro hkLo
      (And.intro hkHi (And.intro hchiLo hchiHi))))

theorem lrDeterminantKCorridorRawHull_contains
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hregion : LRDeterminantKCorridorRegion point) :
    lrDeterminantKCorridorRawHull.Contains point := by
  rcases hregion with ⟨hsLo, hsHi, hsk, hkSlope⟩
  have hkLo : (1 / 128 : ℝ) ≤ point.k := hsLo.trans hsk
  have hkHi : point.k ≤ 2 := by
    calc
      point.k ≤ 128 * point.s := hkSlope
      _ ≤ 128 * (1 / 64 : ℝ) :=
        mul_le_mul_of_nonneg_left hsHi (by norm_num)
      _ = 2 := by norm_num
  rcases lrDeterminant_chi_mem_closed hinterior with ⟨hchiLo, hchiHi⟩
  simpa [lrDeterminantKCorridorRawHull, CertificateBox.Contains] using
    And.intro hsLo (And.intro hsHi (And.intro hkLo
      (And.intro hkHi (And.intro hchiLo hchiHi))))

theorem lrDeterminantFixed1To128Root_contains
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hregion : LRDeterminantFixed1To128Region point) :
    lrDeterminantFixed1To128Root.Contains point := by
  rcases hregion with ⟨hsLo, hsHi, hkLo, hkHi⟩
  rcases lrDeterminant_chi_mem_closed hinterior with ⟨hchiLo, hchiHi⟩
  simpa [lrDeterminantFixed1To128Root, CertificateBox.Contains] using
    And.intro hsLo (And.intro hsHi (And.intro hkLo
      (And.intro hkHi (And.intro hchiLo hchiHi))))

theorem lrDeterminantUpperKRawHull_contains
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hregion : LRDeterminantUpperKRegion point) :
    lrDeterminantUpperKRawHull.Contains point := by
  rcases hregion with ⟨hsLo, hsHi, hsk, hkSlope⟩
  have hkLo : (1 / 64 : ℝ) ≤ point.k := hsLo.trans hsk
  have hkHi : point.k ≤ 1 / 8 := by
    calc
      point.k ≤ 4 * point.s := hkSlope
      _ ≤ 4 * (1 / 32 : ℝ) :=
        mul_le_mul_of_nonneg_left hsHi (by norm_num)
      _ = 1 / 8 := by norm_num
  rcases lrDeterminant_chi_mem_closed hinterior with ⟨hchiLo, hchiHi⟩
  simpa [lrDeterminantUpperKRawHull, CertificateBox.Contains] using
    And.intro hsLo (And.intro hsHi (And.intro hkLo
      (And.intro hkHi (And.intro hchiLo hchiHi))))

theorem lrDeterminantFixed64Root_contains
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hregion : LRDeterminantFixed64Region point) :
    lrDeterminantFixed64Root.Contains point := by
  rcases hregion with ⟨hsLo, hsHi, hkLo, hkHi⟩
  rcases lrDeterminant_chi_mem_closed hinterior with ⟨hchiLo, hchiHi⟩
  simpa [lrDeterminantFixed64Root, CertificateBox.Contains] using
    And.intro hsLo (And.intro hsHi (And.intro hkLo
      (And.intro hkHi (And.intro hchiLo hchiHi))))

theorem lrDeterminantFixed32Root_contains
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hregion : LRDeterminantFixed32Region point) :
    lrDeterminantFixed32Root.Contains point := by
  rcases hregion with ⟨hsLo, hsHi, hkLo, hkHi⟩
  rcases lrDeterminant_chi_mem_closed hinterior with ⟨hchiLo, hchiHi⟩
  simpa [lrDeterminantFixed32Root, CertificateBox.Contains] using
    And.intro hsLo (And.intro hsHi (And.intro hkLo
      (And.intro hkHi (And.intro hchiLo hchiHi))))

theorem lrDeterminantFixed16Root_contains
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hregion : LRDeterminantFixed16Region point) :
    lrDeterminantFixed16Root.Contains point := by
  rcases hregion with ⟨hsLo, hsHi, hkLo, hkHi⟩
  rcases lrDeterminant_chi_mem_closed hinterior with ⟨hchiLo, hchiHi⟩
  simpa [lrDeterminantFixed16Root, CertificateBox.Contains] using
    And.intro hsLo (And.intro hsHi (And.intro hkLo
      (And.intro hkHi (And.intro hchiLo hchiHi))))

/-! ## The exact `(s,K,h)` chart used by the two sloping ledgers -/

/-- Decode the audited upper-corridor coordinates
`(s,K,h)` to the raw cancellation coordinates `(s,k,chi)`. -/
def lrDeterminantKChartDecode
    (coordinate : CertificatePoint) : CertificatePoint where
  s := coordinate.s
  k := coordinate.s * coordinate.k
  chi := coordinate.chi ^ 2

/-- Encode an interior raw cancellation point as `(s,K,h)`. -/
noncomputable def lrDeterminantKChartEncode
    (point : CertificatePoint) : CertificatePoint where
  s := point.s
  k := point.k / point.s
  chi := Real.sqrt point.chi

/-- On the open chart, encoding and then decoding is exact. -/
theorem lrDeterminantKChartDecode_encode
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point) :
    lrDeterminantKChartDecode (lrDeterminantKChartEncode point) = point := by
  cases point with
  | mk s k chi =>
      have hsNe : s ≠ 0 := hinterior.1.1.ne'
      have hchi : 0 ≤ chi := hinterior.2.2.1.le
      have hk : s * (k / s) = k := by
        field_simp [hsNe]
      simp [lrDeterminantKChartDecode, lrDeterminantKChartEncode,
        hk, Real.sq_sqrt hchi]

/-- The corridor region is contained exactly in its audited `(s,K,h)` root
after the coordinate change. -/
theorem lrDeterminantKCorridorKChartRoot_contains_encode
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hregion : LRDeterminantKCorridorRegion point) :
    lrDeterminantKCorridorKChartRoot.Contains
      (lrDeterminantKChartEncode point) := by
  rcases hregion with ⟨hsLo, hsHi, hsk, hkSlope⟩
  have hsPos : 0 < point.s := hinterior.1.1
  have hKLo : 1 ≤ point.k / point.s := by
    rw [le_div_iff₀ hsPos]
    simpa using hsk
  have hKHi : point.k / point.s ≤ 128 := by
    rw [div_le_iff₀ hsPos]
    exact hkSlope
  have hchiLo : 0 ≤ point.chi := hinterior.2.2.1.le
  have hchiHi : point.chi ≤ 1 := hinterior.2.2.2.le
  have hsqrtLo : 0 ≤ Real.sqrt point.chi := Real.sqrt_nonneg _
  have hsqrtSq : (Real.sqrt point.chi) ^ 2 = point.chi :=
    Real.sq_sqrt hchiLo
  have hsqrtHi : Real.sqrt point.chi ≤ 1 := by nlinarith
  simpa [lrDeterminantKCorridorKChartRoot,
    lrDeterminantKChartEncode, CertificateBox.Contains] using
    And.intro hsLo (And.intro hsHi (And.intro hKLo
      (And.intro hKHi (And.intro hsqrtLo hsqrtHi))))

/-- The upper-`K` region is contained exactly in its audited `(s,K,h)` root
after the coordinate change. -/
theorem lrDeterminantUpperKKChartRoot_contains_encode
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hregion : LRDeterminantUpperKRegion point) :
    lrDeterminantUpperKKChartRoot.Contains
      (lrDeterminantKChartEncode point) := by
  rcases hregion with ⟨hsLo, hsHi, hsk, hkSlope⟩
  have hsPos : 0 < point.s := hinterior.1.1
  have hKLo : 1 ≤ point.k / point.s := by
    rw [le_div_iff₀ hsPos]
    simpa using hsk
  have hKHi : point.k / point.s ≤ 4 := by
    rw [div_le_iff₀ hsPos]
    exact hkSlope
  have hchiLo : 0 ≤ point.chi := hinterior.2.2.1.le
  have hchiHi : point.chi ≤ 1 := hinterior.2.2.2.le
  have hsqrtLo : 0 ≤ Real.sqrt point.chi := Real.sqrt_nonneg _
  have hsqrtSq : (Real.sqrt point.chi) ^ 2 = point.chi :=
    Real.sq_sqrt hchiLo
  have hsqrtHi : Real.sqrt point.chi ≤ 1 := by nlinarith
  simpa [lrDeterminantUpperKKChartRoot,
    lrDeterminantKChartEncode, CertificateBox.Contains] using
    And.intro hsLo (And.intro hsHi (And.intro hKLo
      (And.intro hKHi (And.intro hsqrtLo hsqrtHi))))

/-! ## Packaged kernel-checked trees -/

/-- Scalar target enclosed by each raw finite determinant row. -/
noncomputable def lrFiniteDeterminantClearedTarget
    (point : CertificatePoint) : ℝ :=
  lrDeterminantClearedSingular
    (lrCertificateBFlow point) (lrDeterminantD1 point)
    (lrCertificateGShape point) (lrDeterminantPsi point)
    (lrDeterminantDelta point) (lrCertificateW point)
    (lrDeterminantC0 point) (lrCertificateX point)
    (lrDeterminantT point)

/-- Scalar target enclosed by the two audited upper-`K` first-bracket rows. -/
noncomputable def lrFiniteDeterminantFirstBracketTarget
    (point : CertificatePoint) : ℝ :=
  lrDeterminantFirstBracket
    (lrCertificateBFlow point) (lrDeterminantD1 point)
    (lrCertificateGShape point) (lrDeterminantPsi point)
    (lrDeterminantDelta point) (lrCertificateW point)

/-- A checked enclosure tree packages all row-specific executable data.
Different finite rows may therefore use different payload types and interval
evaluators while sharing the same structural soundness theorem. -/
structure LRFiniteDeterminantCheckedTree
    (terms : ℕ) (root : CertificateBox)
    (target : CertificatePoint → ℝ) where
  AcceptData : Type
  payloadCheck : CertificateBox → AcceptData → Bool
  enclose : CertificateBox → AcceptData → RationalEnclosure
  encloseSound : CheckedEnclosureLeafEvaluatorSound
    target payloadCheck enclose
  certificate : SubdivisionCertificate AcceptData LRHighShapeVDiscardData
  checked : certificate.check
    (checkedEnclosureLeafAccepts payloadCheck enclose)
    (lrHighShapeVDiscardCheck terms) root = true

namespace LRFiniteDeterminantCheckedTree

/-- A packaged tree proves its scalar target at every relevant point in its
root.  The only executable premise used here is the stored Boolean equality. -/
theorem target_nonnegative
    {terms : ℕ} {root : CertificateBox}
    {target : CertificatePoint → ℝ}
    (tree : LRFiniteDeterminantCheckedTree terms root target)
    {point : CertificatePoint}
    (hpoint : root.Contains point)
    (hrelevant : LRHighShapeVRelevant point) :
    0 ≤ target point := by
  exact subdivisionCertificate_nonnegative_checkedEnclosure
    tree.encloseSound (lrHighShapeVDiscardCheck_sound terms)
    tree.checked point hpoint hrelevant

end LRFiniteDeterminantCheckedTree

/-- A checked tree in the exact audited `(s,K,h)` chart.  Its discard checker
is deliberately packaged abstractly: unlike the raw-chart rows, its soundness
must be proved after decoding the chart point.  This prevents accidental use
of the raw `(s,k,chi)` physical discard checker on transformed coordinates. -/
structure LRFiniteDeterminantKChartCheckedTree
    (root : CertificateBox) (physicalTarget : CertificatePoint → ℝ) where
  AcceptData : Type
  DiscardData : Type
  payloadCheck : CertificateBox → AcceptData → Bool
  enclose : CertificateBox → AcceptData → RationalEnclosure
  discardCheck : CertificateBox → DiscardData → Bool
  encloseSound : CheckedEnclosureLeafEvaluatorSound
    (fun coordinate ↦ physicalTarget (lrDeterminantKChartDecode coordinate))
    payloadCheck enclose
  discardSound : ∀ box data, discardCheck box data = true →
    ∀ coordinate, box.Contains coordinate →
      ¬ LRHighShapeVRelevant (lrDeterminantKChartDecode coordinate)
  certificate : SubdivisionCertificate AcceptData DiscardData
  checked : certificate.check
    (checkedEnclosureLeafAccepts payloadCheck enclose)
    discardCheck root = true

namespace LRFiniteDeterminantKChartCheckedTree

theorem target_nonnegative
    {root : CertificateBox} {physicalTarget : CertificatePoint → ℝ}
    (tree : LRFiniteDeterminantKChartCheckedTree root physicalTarget)
    {coordinate : CertificatePoint}
    (hcoordinate : root.Contains coordinate)
    (hrelevant :
      LRHighShapeVRelevant (lrDeterminantKChartDecode coordinate)) :
    0 ≤ physicalTarget (lrDeterminantKChartDecode coordinate) := by
  exact subdivisionCertificate_nonnegative_checkedEnclosure
    tree.encloseSound tree.discardSound tree.checked coordinate
    hcoordinate hrelevant

end LRFiniteDeterminantKChartCheckedTree

/-- Reusable checked-tree theorem for any raw finite determinant region whose
points are contained in a rational root box. -/
theorem lrFiniteDeterminantClearedRegion_certificate_of_checkedTree
    {terms : ℕ} {root : CertificateBox}
    {Region : CertificatePoint → Prop}
    (root_contains : ∀ {point : CertificatePoint},
      LRHighShapeInterior point → Region point → root.Contains point)
    (tree : LRFiniteDeterminantCheckedTree terms root
      lrFiniteDeterminantClearedTarget) :
    LRDeterminantRegionCertificateTheorem Region := by
  intro point hinterior hrelevant hregion
  right
  have hnonnegative := tree.target_nonnegative
    (root_contains hinterior hregion) hrelevant
  simpa [lrFiniteDeterminantClearedTarget,
    LRDeterminantClearedSingularAt] using hnonnegative

/-- Reusable checked-tree theorem for a finite first-bracket region. -/
theorem lrFiniteDeterminantFirstBracketRegion_certificate_of_checkedTree
    {terms : ℕ} {root : CertificateBox}
    {Region : CertificatePoint → Prop}
    (root_contains : ∀ {point : CertificatePoint},
      LRHighShapeInterior point → Region point → root.Contains point)
    (tree : LRFiniteDeterminantCheckedTree terms root
      lrFiniteDeterminantFirstBracketTarget) :
    LRDeterminantRegionCertificateTheorem Region := by
  intro point hinterior hrelevant hregion
  left
  have hnonnegative := tree.target_nonnegative
    (root_contains hinterior hregion) hrelevant
  simpa [lrFiniteDeterminantFirstBracketTarget,
    LRDeterminantFirstBracketAt] using hnonnegative

/-- Exact-chart counterpart of the raw cleared-target checked-tree theorem. -/
theorem lrFiniteDeterminantClearedRegion_certificate_of_checkedKChartTree
    {root : CertificateBox} {Region : CertificatePoint → Prop}
    (root_contains : ∀ {point : CertificatePoint},
      LRHighShapeInterior point → Region point →
        root.Contains (lrDeterminantKChartEncode point))
    (tree : LRFiniteDeterminantKChartCheckedTree root
      lrFiniteDeterminantClearedTarget) :
    LRDeterminantRegionCertificateTheorem Region := by
  intro point hinterior hrelevant hregion
  have hdecoded := lrDeterminantKChartDecode_encode hinterior
  have hrelevantChart : LRHighShapeVRelevant
      (lrDeterminantKChartDecode (lrDeterminantKChartEncode point)) := by
    rw [hdecoded]
    exact hrelevant
  have hnonnegative := tree.target_nonnegative
    (root_contains hinterior hregion) hrelevantChart
  rw [hdecoded] at hnonnegative
  right
  simpa [lrFiniteDeterminantClearedTarget,
    LRDeterminantClearedSingularAt] using hnonnegative

/-- Exact-chart counterpart for the upper-`K` first-bracket trees. -/
theorem lrFiniteDeterminantFirstBracketRegion_certificate_of_checkedKChartTree
    {root : CertificateBox} {Region : CertificatePoint → Prop}
    (root_contains : ∀ {point : CertificatePoint},
      LRHighShapeInterior point → Region point →
        root.Contains (lrDeterminantKChartEncode point))
    (tree : LRFiniteDeterminantKChartCheckedTree root
      lrFiniteDeterminantFirstBracketTarget) :
    LRDeterminantRegionCertificateTheorem Region := by
  intro point hinterior hrelevant hregion
  have hdecoded := lrDeterminantKChartDecode_encode hinterior
  have hrelevantChart : LRHighShapeVRelevant
      (lrDeterminantKChartDecode (lrDeterminantKChartEncode point)) := by
    rw [hdecoded]
    exact hrelevant
  have hnonnegative := tree.target_nonnegative
    (root_contains hinterior hregion) hrelevantChart
  rw [hdecoded] at hnonnegative
  left
  simpa [lrFiniteDeterminantFirstBracketTarget,
    LRDeterminantFirstBracketAt] using hnonnegative

/-! ## The seven ledger fields -/

theorem lrDeterminantFixed1To32Region_certificate_of_checkedTree
    {terms : ℕ}
    (tree : LRFiniteDeterminantCheckedTree terms
      lrDeterminantFixed1To32Root lrFiniteDeterminantClearedTarget) :
    LRDeterminantRegionCertificateTheorem
      LRDeterminantFixed1To32Region :=
  lrFiniteDeterminantClearedRegion_certificate_of_checkedTree
    lrDeterminantFixed1To32Root_contains tree

theorem lrDeterminantKCorridorRegion_certificate_of_checkedTree
    (tree : LRFiniteDeterminantKChartCheckedTree
      lrDeterminantKCorridorKChartRoot
      lrFiniteDeterminantClearedTarget) :
    LRDeterminantRegionCertificateTheorem
      LRDeterminantKCorridorRegion :=
  lrFiniteDeterminantClearedRegion_certificate_of_checkedKChartTree
    lrDeterminantKCorridorKChartRoot_contains_encode tree

theorem lrDeterminantFixed1To128Region_certificate_of_checkedTree
    {terms : ℕ}
    (tree : LRFiniteDeterminantCheckedTree terms
      lrDeterminantFixed1To128Root lrFiniteDeterminantClearedTarget) :
    LRDeterminantRegionCertificateTheorem
      LRDeterminantFixed1To128Region :=
  lrFiniteDeterminantClearedRegion_certificate_of_checkedTree
    lrDeterminantFixed1To128Root_contains tree

theorem lrDeterminantUpperKRegion_certificate_of_checkedTree
    (tree : LRFiniteDeterminantKChartCheckedTree
      lrDeterminantUpperKKChartRoot
      lrFiniteDeterminantFirstBracketTarget) :
    LRDeterminantRegionCertificateTheorem LRDeterminantUpperKRegion :=
  lrFiniteDeterminantFirstBracketRegion_certificate_of_checkedKChartTree
    lrDeterminantUpperKKChartRoot_contains_encode tree

theorem lrDeterminantFixed64Region_certificate_of_checkedTree
    {terms : ℕ}
    (tree : LRFiniteDeterminantCheckedTree terms
      lrDeterminantFixed64Root lrFiniteDeterminantClearedTarget) :
    LRDeterminantRegionCertificateTheorem LRDeterminantFixed64Region :=
  lrFiniteDeterminantClearedRegion_certificate_of_checkedTree
    lrDeterminantFixed64Root_contains tree

theorem lrDeterminantFixed32Region_certificate_of_checkedTree
    {terms : ℕ}
    (tree : LRFiniteDeterminantCheckedTree terms
      lrDeterminantFixed32Root lrFiniteDeterminantClearedTarget) :
    LRDeterminantRegionCertificateTheorem LRDeterminantFixed32Region :=
  lrFiniteDeterminantClearedRegion_certificate_of_checkedTree
    lrDeterminantFixed32Root_contains tree

theorem lrDeterminantFixed16Region_certificate_of_checkedTree
    {terms : ℕ}
    (tree : LRFiniteDeterminantCheckedTree terms
      lrDeterminantFixed16Root lrFiniteDeterminantClearedTarget) :
    LRDeterminantRegionCertificateTheorem LRDeterminantFixed16Region :=
  lrFiniteDeterminantClearedRegion_certificate_of_checkedTree
    lrDeterminantFixed16Root_contains tree

/-- The seven finite fields of the audited determinant ledger, separated from
the four analytic/direct fields already handled elsewhere. -/
structure LRDeterminantFiniteRegionLedger where
  fixed1To32 :
    LRDeterminantRegionCertificateTheorem LRDeterminantFixed1To32Region
  kCorridor :
    LRDeterminantRegionCertificateTheorem LRDeterminantKCorridorRegion
  fixed1To128 :
    LRDeterminantRegionCertificateTheorem LRDeterminantFixed1To128Region
  upperK : LRDeterminantRegionCertificateTheorem LRDeterminantUpperKRegion
  fixed64 : LRDeterminantRegionCertificateTheorem LRDeterminantFixed64Region
  fixed32 : LRDeterminantRegionCertificateTheorem LRDeterminantFixed32Region
  fixed16 : LRDeterminantRegionCertificateTheorem LRDeterminantFixed16Region

/-- A heterogeneous collection of seven generic direct-enclosure trees.  Each
field carries its own leaf payload type and evaluator; this is not the exact
type of the historical scaled replay data. -/
structure LRDeterminantFiniteCheckedTrees (terms : ℕ) where
  fixed1To32 : LRFiniteDeterminantCheckedTree terms
    lrDeterminantFixed1To32Root lrFiniteDeterminantClearedTarget
  kCorridor : LRFiniteDeterminantKChartCheckedTree
    lrDeterminantKCorridorKChartRoot lrFiniteDeterminantClearedTarget
  fixed1To128 : LRFiniteDeterminantCheckedTree terms
    lrDeterminantFixed1To128Root lrFiniteDeterminantClearedTarget
  upperK : LRFiniteDeterminantKChartCheckedTree
    lrDeterminantUpperKKChartRoot lrFiniteDeterminantFirstBracketTarget
  fixed64 : LRFiniteDeterminantCheckedTree terms
    lrDeterminantFixed64Root lrFiniteDeterminantClearedTarget
  fixed32 : LRFiniteDeterminantCheckedTree terms
    lrDeterminantFixed32Root lrFiniteDeterminantClearedTarget
  fixed16 : LRFiniteDeterminantCheckedTree terms
    lrDeterminantFixed16Root lrFiniteDeterminantClearedTarget

/-- Successful kernel checks for the seven finite root trees yield exactly
the seven finite theorem fields consumed by the global determinant ledger. -/
theorem LRDeterminantFiniteCheckedTrees.toRegionLedger
    {terms : ℕ} (trees : LRDeterminantFiniteCheckedTrees terms) :
    LRDeterminantFiniteRegionLedger where
  fixed1To32 :=
    lrDeterminantFixed1To32Region_certificate_of_checkedTree trees.fixed1To32
  kCorridor :=
    lrDeterminantKCorridorRegion_certificate_of_checkedTree trees.kCorridor
  fixed1To128 :=
    lrDeterminantFixed1To128Region_certificate_of_checkedTree trees.fixed1To128
  upperK :=
    lrDeterminantUpperKRegion_certificate_of_checkedTree trees.upperK
  fixed64 :=
    lrDeterminantFixed64Region_certificate_of_checkedTree trees.fixed64
  fixed32 :=
    lrDeterminantFixed32Region_certificate_of_checkedTree trees.fixed32
  fixed16 :=
    lrDeterminantFixed16Region_certificate_of_checkedTree trees.fixed16

/-- Final assembly hook: once the four non-finite rows and the seven checked
trees are supplied, no further geometric or checker argument remains in the
construction of the complete determinant ledger. -/
theorem lrDeterminantRegionLedger_of_finiteCheckedTrees
    {terms : ℕ}
    (lowRatio : LRDeterminantLowRatioTangentTheorem)
    (deep : LRDeterminantRegionCertificateTheorem LRDeterminantDeepRegion)
    (lowK : LRDeterminantRegionCertificateTheorem LRDeterminantLowKRegion)
    (tail : LRDeterminantRegionCertificateTheorem LRDeterminantTailRegion)
    (trees : LRDeterminantFiniteCheckedTrees terms) :
    LRDeterminantRegionLedger := by
  let finite := trees.toRegionLedger
  exact
    { lowRatio := lowRatio
      deep := deep
      lowK := lowK
      tail := tail
      fixed1To32 := finite.fixed1To32
      kCorridor := finite.kCorridor
      fixed1To128 := finite.fixed1To128
      upperK := finite.upperK
      fixed64 := finite.fixed64
      fixed32 := finite.fixed32
      fixed16 := finite.fixed16 }

end CourtadeKumar
