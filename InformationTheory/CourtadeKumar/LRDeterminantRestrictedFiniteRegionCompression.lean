import InformationTheory.CourtadeKumar.LRDeterminantRestrictedCoreAssembly

/-!
# Exact compression of the restricted finite determinant rows

After the low-ratio branch has supplied `s < k` and the gap-budget tail has
reduced the problem to `k ≤ 4`, the seven historical finite rows have a much
simpler union.  It is exactly

`2^-14 ≤ s ≤ 1/10` and (`2^-7 ≤ s` or `1 ≤ k`).

Thus a new certificate need not reproduce the seven historical coordinate
systems.  This module supplies both a single theorem interface for that exact
union and a lower-risk four-band interface, and proves that either interface
constructs the existing seven-field ledger consumed by the final assembly.
-/

namespace CourtadeKumar

/-! ## The compressed region and its theorem interface -/

/-- Exact union of the seven finite determinant rows once the ambient
restrictions `s < k` and `k ≤ 4` are imposed.  The disjunction removes the
low-`k` hole below `s = 2^-7`, which is already handled by the analytic
low-`k` theorem. -/
def LRDeterminantKLeFourFiniteCompressedRegion
    (point : CertificatePoint) : Prop :=
  1 / 16384 ≤ point.s ∧ point.s ≤ 1 / 10 ∧
    (1 / 128 ≤ point.s ∨ 1 ≤ point.k)

/-- One theorem on the exact compressed union can replace all seven finite
row theorems. -/
def LRDeterminantKLeFourFiniteCompressedCertificateTheorem : Prop :=
  LRDeterminantKLeFourRegionCertificateTheorem
    LRDeterminantKLeFourFiniteCompressedRegion

/-! ## A four-band interface convenient for certificate generation -/

/-- The part below `s = 2^-7`; here the finite union requires `k ≥ 1`. -/
def LRDeterminantFiniteTinyAboveOneRegion
    (point : CertificatePoint) : Prop :=
  1 / 16384 ≤ point.s ∧ point.s ≤ 1 / 128 ∧ 1 ≤ point.k

/-- The complete restricted band `2^-7 ≤ s ≤ 2^-6`. -/
def LRDeterminantFiniteOneTwentyEightToSixtyFourRegion
    (point : CertificatePoint) : Prop :=
  1 / 128 ≤ point.s ∧ point.s ≤ 1 / 64

/-- The complete restricted band `2^-6 ≤ s ≤ 2^-5`. -/
def LRDeterminantFiniteSixtyFourToThirtyTwoRegion
    (point : CertificatePoint) : Prop :=
  1 / 64 ≤ point.s ∧ point.s ≤ 1 / 32

/-- The complete restricted band `2^-5 ≤ s ≤ 1/10`. -/
def LRDeterminantFiniteThirtyTwoToTenRegion
    (point : CertificatePoint) : Prop :=
  1 / 32 ≤ point.s ∧ point.s ≤ 1 / 10

/-- Four merged certificate theorems are enough to populate the seven
historical ledger fields. -/
structure LRDeterminantKLeFourMergedFiniteRegionLedger : Prop where
  tinyAboveOne : LRDeterminantKLeFourRegionCertificateTheorem
    LRDeterminantFiniteTinyAboveOneRegion
  oneTwentyEightToSixtyFour : LRDeterminantKLeFourRegionCertificateTheorem
    LRDeterminantFiniteOneTwentyEightToSixtyFourRegion
  sixtyFourToThirtyTwo : LRDeterminantKLeFourRegionCertificateTheorem
    LRDeterminantFiniteSixtyFourToThirtyTwoRegion
  thirtyTwoToTen : LRDeterminantKLeFourRegionCertificateTheorem
    LRDeterminantFiniteThirtyTwoToTenRegion

/-! ## Exact set-theoretic compression -/

/-- Union of the seven historical finite row predicates. -/
def LRDeterminantFiniteRowsCovered (point : CertificatePoint) : Prop :=
  LRDeterminantFixed1To32Region point ∨
  LRDeterminantKCorridorRegion point ∨
  LRDeterminantFixed1To128Region point ∨
  LRDeterminantUpperKRegion point ∨
  LRDeterminantFixed64Region point ∨
  LRDeterminantFixed32Region point ∨
  LRDeterminantFixed16Region point

/-- Every historical finite row lies in the compressed region. -/
theorem lrDeterminantKLeFourFiniteCompressedRegion_of_rowsCovered
    {point : CertificatePoint}
    (hrows : LRDeterminantFiniteRowsCovered point) :
    LRDeterminantKLeFourFiniteCompressedRegion point := by
  rcases hrows with h | h | h | h | h | h | h
  · rcases h with ⟨hsLo, hsHi, hkLo, _hkHi⟩
    exact ⟨hsLo, hsHi.trans (by norm_num), Or.inr hkLo⟩
  · rcases h with ⟨hsLo, hsHi, _hsk, _hkSlope⟩
    exact ⟨(by norm_num : (1 / 16384 : ℝ) ≤ 1 / 128).trans hsLo,
      hsHi.trans (by norm_num), Or.inl hsLo⟩
  · rcases h with ⟨hsLo, hsHi, _hkLo, _hkHi⟩
    exact ⟨(by norm_num : (1 / 16384 : ℝ) ≤ 1 / 128).trans hsLo,
      hsHi.trans (by norm_num), Or.inl hsLo⟩
  · rcases h with ⟨hsLo, hsHi, _hsk, _hkSlope⟩
    exact ⟨(by norm_num : (1 / 16384 : ℝ) ≤ 1 / 64).trans hsLo,
      hsHi.trans (by norm_num), Or.inl
        ((by norm_num : (1 / 128 : ℝ) ≤ 1 / 64).trans hsLo)⟩
  · rcases h with ⟨hsLo, hsHi, _hkLo, _hkHi⟩
    exact ⟨(by norm_num : (1 / 16384 : ℝ) ≤ 1 / 64).trans hsLo,
      hsHi.trans (by norm_num), Or.inl
        ((by norm_num : (1 / 128 : ℝ) ≤ 1 / 64).trans hsLo)⟩
  · rcases h with ⟨hsLo, hsHi, _hkLo, _hkHi⟩
    exact ⟨(by norm_num : (1 / 16384 : ℝ) ≤ 1 / 32).trans hsLo,
      hsHi.trans (by norm_num), Or.inl
        ((by norm_num : (1 / 128 : ℝ) ≤ 1 / 32).trans hsLo)⟩
  · rcases h with ⟨hsLo, hsHi, _hkLo, _hkHi⟩
    exact ⟨(by norm_num : (1 / 16384 : ℝ) ≤ 1 / 16).trans hsLo,
      hsHi, Or.inl
        ((by norm_num : (1 / 128 : ℝ) ≤ 1 / 16).trans hsLo)⟩

/-- Conversely, on `s < k ≤ 4`, every point of the compressed region lies
in at least one historical finite row.  This proves that the new universal
interface neither adds nor omits any point of the old seven-row union. -/
theorem lrDeterminantFiniteRowsCovered_of_kLeFour_compressedRegion
    {point : CertificatePoint}
    (hcompressed : LRDeterminantKLeFourFiniteCompressedRegion point)
    (hK : point.s < point.k)
    (hkFour : point.k ≤ 4) :
    LRDeterminantFiniteRowsCovered point := by
  rcases hcompressed with ⟨hsDeep, hsTen, hgate⟩
  by_cases hs128 : point.s ≤ 1 / 128
  · rcases hgate with hs128Lower | hkOne
    · have hsEq : point.s = 1 / 128 := le_antisymm hs128 hs128Lower
      by_cases hkOneUpper : point.k ≤ 1
      · exact Or.inr (Or.inl ⟨hs128Lower,
          hsEq.le.trans (by norm_num), hK.le, by
            rw [hsEq]
            norm_num at hkOneUpper ⊢
            exact hkOneUpper⟩)
      · exact Or.inl ⟨hsDeep, hs128,
          (lt_of_not_ge hkOneUpper).le, hkFour.trans (by norm_num)⟩
    · exact Or.inl
        ⟨hsDeep, hs128, hkOne, hkFour.trans (by norm_num)⟩
  · have hs128Strict : 1 / 128 < point.s := lt_of_not_ge hs128
    by_cases hs64 : point.s ≤ 1 / 64
    · by_cases hkSlope : point.k ≤ 128 * point.s
      · exact Or.inr (Or.inl
          ⟨hs128Strict.le, hs64, hK.le, hkSlope⟩)
      · have hkSlopeStrict : 128 * point.s < point.k :=
          lt_of_not_ge hkSlope
        exact Or.inr (Or.inr (Or.inl
          ⟨hs128Strict.le, hs64,
            (by nlinarith : (1 : ℝ) ≤ point.k),
            hkFour.trans (by norm_num)⟩))
    · have hs64Strict : 1 / 64 < point.s := lt_of_not_ge hs64
      by_cases hs32 : point.s ≤ 1 / 32
      · by_cases hkSlope : point.k ≤ 4 * point.s
        · exact Or.inr (Or.inr (Or.inr (Or.inl
            ⟨hs64Strict.le, hs32, hK.le, hkSlope⟩)))
        · have hkSlopeStrict : 4 * point.s < point.k :=
            lt_of_not_ge hkSlope
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
              ⟨hs64Strict.le, hs32,
                (by nlinarith : (1 / 32 : ℝ) ≤ point.k),
                hkFour.trans (by norm_num)⟩))))
      · have hs32Strict : 1 / 32 < point.s := lt_of_not_ge hs32
        by_cases hs16 : point.s ≤ 1 / 16
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
            ⟨hs32Strict.le, hs16, hs32Strict.le.trans hK.le,
              hkFour.trans (by norm_num)⟩)))))
        · have hs16Strict : 1 / 16 < point.s := lt_of_not_ge hs16
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
            ⟨hs16Strict.le, hsTen, hs16Strict.le.trans hK.le,
              hkFour.trans (by norm_num)⟩)))))

/-- The precise equality of the compressed and historical unions under the
two ambient restrictions used by the final tangent assembly. -/
theorem lrDeterminantFiniteRowsCovered_iff_compressedRegion
    {point : CertificatePoint}
    (hK : point.s < point.k)
    (hkFour : point.k ≤ 4) :
    LRDeterminantFiniteRowsCovered point ↔
      LRDeterminantKLeFourFiniteCompressedRegion point := by
  constructor
  · exact lrDeterminantKLeFourFiniteCompressedRegion_of_rowsCovered
  · intro h
    exact lrDeterminantFiniteRowsCovered_of_kLeFour_compressedRegion h hK hkFour

/-! ## Constructors for the existing final-assembly ledger -/

/-- A theorem on the exact compressed union populates all seven historical
fields of the restricted finite ledger. -/
theorem lrDeterminantKLeFourFiniteRegionLedger_of_compressed
    (compressed : LRDeterminantKLeFourFiniteCompressedCertificateTheorem) :
    LRDeterminantKLeFourFiniteRegionLedger := by
  have onRow : ∀ {Region : CertificatePoint → Prop},
      (∀ {point}, Region point → LRDeterminantFiniteRowsCovered point) →
      LRDeterminantKLeFourRegionCertificateTheorem Region := by
    intro Region hrow point hinterior hrelevant hregion hK hkFour
    exact compressed point hinterior hrelevant
      (lrDeterminantKLeFourFiniteCompressedRegion_of_rowsCovered
        (hrow hregion)) hK hkFour
  exact
    { fixed1To32 := onRow (fun h => Or.inl h)
      kCorridor := onRow (fun h => Or.inr (Or.inl h))
      fixed1To128 := onRow (fun h => Or.inr (Or.inr (Or.inl h)))
      upperK := onRow (fun h => Or.inr (Or.inr (Or.inr (Or.inl h))))
      fixed64 := onRow
        (fun h => Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
      fixed32 := onRow
        (fun h => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
      fixed16 := onRow
        (fun h => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))) }

/-- The four merged `s`-bands populate the seven historical finite fields.
This is the recommended low-risk certificate-facing constructor. -/
theorem LRDeterminantKLeFourMergedFiniteRegionLedger.toFiniteRegionLedger
    (merged : LRDeterminantKLeFourMergedFiniteRegionLedger) :
    LRDeterminantKLeFourFiniteRegionLedger where
  fixed1To32 := by
    intro point hinterior hrelevant hregion hK hkFour
    rcases hregion with ⟨hsLo, hsHi, hkLo, _hkHi⟩
    exact merged.tinyAboveOne point hinterior hrelevant
      ⟨hsLo, hsHi, hkLo⟩ hK hkFour
  kCorridor := by
    intro point hinterior hrelevant hregion hK hkFour
    exact merged.oneTwentyEightToSixtyFour point hinterior hrelevant
      ⟨hregion.1, hregion.2.1⟩ hK hkFour
  fixed1To128 := by
    intro point hinterior hrelevant hregion hK hkFour
    exact merged.oneTwentyEightToSixtyFour point hinterior hrelevant
      ⟨hregion.1, hregion.2.1⟩ hK hkFour
  upperK := by
    intro point hinterior hrelevant hregion hK hkFour
    exact merged.sixtyFourToThirtyTwo point hinterior hrelevant
      ⟨hregion.1, hregion.2.1⟩ hK hkFour
  fixed64 := by
    intro point hinterior hrelevant hregion hK hkFour
    exact merged.sixtyFourToThirtyTwo point hinterior hrelevant
      ⟨hregion.1, hregion.2.1⟩ hK hkFour
  fixed32 := by
    intro point hinterior hrelevant hregion hK hkFour
    exact merged.thirtyTwoToTen point hinterior hrelevant
      ⟨hregion.1, hregion.2.1.trans (by norm_num)⟩ hK hkFour
  fixed16 := by
    intro point hinterior hrelevant hregion hK hkFour
    exact merged.thirtyTwoToTen point hinterior hrelevant
      ⟨(by norm_num : (1 / 32 : ℝ) ≤ 1 / 16).trans hregion.1,
        hregion.2.1⟩ hK hkFour

/-- A universal compressed theorem canonically supplies the four-band
interface as well. -/
theorem LRDeterminantKLeFourFiniteCompressedCertificateTheorem.toMergedLedger
    (compressed : LRDeterminantKLeFourFiniteCompressedCertificateTheorem) :
    LRDeterminantKLeFourMergedFiniteRegionLedger where
  tinyAboveOne := by
    intro point hinterior hrelevant hregion hK hkFour
    exact compressed point hinterior hrelevant
      ⟨hregion.1, hregion.2.1.trans (by norm_num), Or.inr hregion.2.2⟩
      hK hkFour
  oneTwentyEightToSixtyFour := by
    intro point hinterior hrelevant hregion hK hkFour
    exact compressed point hinterior hrelevant
      ⟨(by norm_num : (1 / 16384 : ℝ) ≤ 1 / 128).trans hregion.1,
        hregion.2.trans (by norm_num), Or.inl hregion.1⟩ hK hkFour
  sixtyFourToThirtyTwo := by
    intro point hinterior hrelevant hregion hK hkFour
    exact compressed point hinterior hrelevant
      ⟨(by norm_num : (1 / 16384 : ℝ) ≤ 1 / 64).trans hregion.1,
        hregion.2.trans (by norm_num),
        Or.inl ((by norm_num : (1 / 128 : ℝ) ≤ 1 / 64).trans hregion.1)⟩
      hK hkFour
  thirtyTwoToTen := by
    intro point hinterior hrelevant hregion hK hkFour
    exact compressed point hinterior hrelevant
      ⟨(by norm_num : (1 / 16384 : ℝ) ≤ 1 / 32).trans hregion.1,
        hregion.2,
        Or.inl ((by norm_num : (1 / 128 : ℝ) ≤ 1 / 32).trans hregion.1)⟩
      hK hkFour

end CourtadeKumar
