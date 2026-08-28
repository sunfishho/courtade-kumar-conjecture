import InformationTheory.CourtadeKumar.LRHighShapeRelevantKLower

/-!
# Exhaustive region cover for the audited determinant proof

This is the exact geometric decomposition (D12)--(D13) from the audited
assembly, written without divisions.  The inequalities `s ≤ k` and
`k ≤ c * s` are respectively the closed forms of `1 ≤ K = k / s` and
`K ≤ c` on the positive chart.
-/

open Set

namespace CourtadeKumar

def LRDeterminantLowRatioRegion (point : CertificatePoint) : Prop :=
  point.s / 4 < point.k ∧ point.k ≤ point.s

def LRDeterminantDeepRegion (point : CertificatePoint) : Prop :=
  point.s ≤ 1 / 16384 ∧ point.s ≤ point.k

def LRDeterminantLowKRegion (point : CertificatePoint) : Prop :=
  point.s ≤ 1 / 128 ∧ point.s ≤ point.k ∧ point.k ≤ 1

def LRDeterminantTailRegion (point : CertificatePoint) : Prop :=
  point.s ≤ 1 / 128 ∧ 32 ≤ point.k

def LRDeterminantFixed1To32Region (point : CertificatePoint) : Prop :=
  1 / 16384 ≤ point.s ∧ point.s ≤ 1 / 128 ∧
    1 ≤ point.k ∧ point.k ≤ 32

def LRDeterminantKCorridorRegion (point : CertificatePoint) : Prop :=
  1 / 128 ≤ point.s ∧ point.s ≤ 1 / 64 ∧
    point.s ≤ point.k ∧ point.k ≤ 128 * point.s

def LRDeterminantFixed1To128Region (point : CertificatePoint) : Prop :=
  1 / 128 ≤ point.s ∧ point.s ≤ 1 / 64 ∧
    1 ≤ point.k ∧ point.k ≤ 128

def LRDeterminantUpperKRegion (point : CertificatePoint) : Prop :=
  1 / 64 ≤ point.s ∧ point.s ≤ 1 / 32 ∧
    point.s ≤ point.k ∧ point.k ≤ 4 * point.s

def LRDeterminantFixed64Region (point : CertificatePoint) : Prop :=
  1 / 64 ≤ point.s ∧ point.s ≤ 1 / 32 ∧
    1 / 32 ≤ point.k ∧ point.k ≤ 64

def LRDeterminantFixed32Region (point : CertificatePoint) : Prop :=
  1 / 32 ≤ point.s ∧ point.s ≤ 1 / 16 ∧
    1 / 32 ≤ point.k ∧ point.k ≤ 32

def LRDeterminantFixed16Region (point : CertificatePoint) : Prop :=
  1 / 16 ≤ point.s ∧ point.s ≤ 1 / 10 ∧
    1 / 16 ≤ point.k ∧ point.k ≤ 16

/-- Union of the ten determinant regions in the audited assembly. -/
def LRDeterminantCovered (point : CertificatePoint) : Prop :=
  LRDeterminantDeepRegion point ∨
  LRDeterminantLowKRegion point ∨
  LRDeterminantTailRegion point ∨
  LRDeterminantFixed1To32Region point ∨
  LRDeterminantKCorridorRegion point ∨
  LRDeterminantFixed1To128Region point ∨
  LRDeterminantUpperKRegion point ∨
  LRDeterminantFixed64Region point ∨
  LRDeterminantFixed32Region point ∨
  LRDeterminantFixed16Region point

/-- Formula (D13): after the low-ratio branch has been removed, the ten
audited regions exhaust the near-endpoint physical chart. -/
theorem lrHighShape_determinantCovered_of_K_gt_one
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hsUpper : point.s < 1 / 10)
    (hK : point.s < point.k) :
    LRDeterminantCovered point := by
  have hsPos : 0 < point.s := hinterior.1.1
  have hePos : 0 < point.s * point.k := by
    simpa [lrCertificateE] using hinterior.2.1.1
  have hkPos : 0 < point.k :=
    pos_of_mul_pos_left (by simpa [mul_comm] using hePos) hsPos.le
  have heLt : point.s * point.k < 1 := by
    simpa [lrCertificateE] using hinterior.2.1.2
  have upper_of_s_lower {a b : ℝ} (haPos : 0 < a)
      (ha : a ≤ point.s) (hab : a * b = 1) : point.k < b := by
    have hmul : a * point.k ≤ point.s * point.k :=
      mul_le_mul_of_nonneg_right ha hkPos.le
    by_contra hnot
    have hbk : b ≤ point.k := le_of_not_gt hnot
    have habk : a * b ≤ a * point.k :=
      mul_le_mul_of_nonneg_left hbk haPos.le
    linarith
  by_cases hsDeep : point.s ≤ 1 / 16384
  · exact Or.inl ⟨hsDeep, hK.le⟩
  have hsDeepLower : 1 / 16384 ≤ point.s := le_of_lt (lt_of_not_ge hsDeep)
  by_cases hs128 : point.s ≤ 1 / 128
  · by_cases hkOne : point.k ≤ 1
    · exact Or.inr (Or.inl ⟨hs128, hK.le, hkOne⟩)
    · have hkOneLower : 1 ≤ point.k := le_of_lt (lt_of_not_ge hkOne)
      by_cases hkTail : 32 ≤ point.k
      · exact Or.inr (Or.inr (Or.inl ⟨hs128, hkTail⟩))
      · have hk32 : point.k ≤ 32 := le_of_lt (lt_of_not_ge hkTail)
        exact Or.inr (Or.inr (Or.inr (Or.inl
          ⟨hsDeepLower, hs128, hkOneLower, hk32⟩)))
  have hs128Lower : 1 / 128 ≤ point.s := le_of_lt (lt_of_not_ge hs128)
  by_cases hs64 : point.s ≤ 1 / 64
  · by_cases hkOne : point.k ≤ 1
    · have hkKUpper : point.k ≤ 128 * point.s := by nlinarith
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨hs128Lower, hs64, hK.le, hkKUpper⟩))))
    · have hkOneLower : 1 ≤ point.k := le_of_lt (lt_of_not_ge hkOne)
      have hk128 : point.k ≤ 128 := by
        have hlt := upper_of_s_lower (by norm_num) hs128Lower
          (show (1 / 128 : ℝ) * 128 = 1 by norm_num)
        exact hlt.le
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨hs128Lower, hs64, hkOneLower, hk128⟩)))))
  have hs64Lower : 1 / 64 ≤ point.s := le_of_lt (lt_of_not_ge hs64)
  by_cases hs32 : point.s ≤ 1 / 32
  · by_cases hk32Lower : 1 / 32 ≤ point.k
    · have hk64 : point.k ≤ 64 := by
        have hlt := upper_of_s_lower (by norm_num) hs64Lower
          (show (1 / 64 : ℝ) * 64 = 1 by norm_num)
        exact hlt.le
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inl ⟨hs64Lower, hs32, hk32Lower, hk64⟩)))))))
    · have hkSmall : point.k ≤ 1 / 32 :=
        le_of_lt (lt_of_not_ge hk32Lower)
      have hkKUpper : point.k ≤ 4 * point.s := by nlinarith
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl ⟨hs64Lower, hs32, hK.le, hkKUpper⟩))))))
  have hs32Lower : 1 / 32 ≤ point.s := le_of_lt (lt_of_not_ge hs32)
  by_cases hs16 : point.s ≤ 1 / 16
  · have hk32Lower : 1 / 32 ≤ point.k := hs32Lower.trans hK.le
    have hk32 : point.k ≤ 32 := by
      have hlt := upper_of_s_lower (by norm_num) hs32Lower
        (show (1 / 32 : ℝ) * 32 = 1 by norm_num)
      exact hlt.le
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inl
        ⟨hs32Lower, hs16, hk32Lower, hk32⟩))))))))
  have hs16Lower : 1 / 16 ≤ point.s := le_of_lt (lt_of_not_ge hs16)
  have hk16Lower : 1 / 16 ≤ point.k := hs16Lower.trans hK.le
  have hk16 : point.k ≤ 16 := by
    have hlt := upper_of_s_lower (by norm_num) hs16Lower
      (show (1 / 16 : ℝ) * 16 = 1 by norm_num)
    exact hlt.le
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inr (Or.inr (Or.inr
      ⟨hs16Lower, hsUpper.le, hk16Lower, hk16⟩))))))))

/-- The full near-endpoint split used immediately before (D13): relevance
places `K` above `1/4`; the `K ≤ 1` branch is isolated, and every remaining
point belongs to one of the ten audited determinant regions. -/
theorem lrHighShape_lowRatio_or_determinantCovered
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hrelevant : LRHighShapeVRelevant point)
    (hsUpper : point.s < 1 / 10) :
    LRDeterminantLowRatioRegion point ∨ LRDeterminantCovered point := by
  have hkLower :=
    lrCertificate_k_gt_quarter_s_of_relevant hinterior hrelevant
  by_cases hkUpper : point.k ≤ point.s
  · exact Or.inl ⟨hkLower, hkUpper⟩
  · exact Or.inr (lrHighShape_determinantCovered_of_K_gt_one
      hinterior hsUpper (lt_of_not_ge hkUpper))

end CourtadeKumar
