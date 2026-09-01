import InformationTheory.CourtadeKumar.LRCompactVLambdaGroupedCore
import InformationTheory.CourtadeKumar.LRCompactVGroupedBilinear

/-!
# Exact interval lower bound for the grouped compact-`V` fallback

The checker keeps the shared score `w_n(R)` and shape term `T_n(v,x)` in one
separately affine expression.  Each summand is therefore bounded by four
rational corners instead of expanding the cancellation into independently
rounded pieces.

The same recursion also accumulates a lower bound for the endpoint-kernel
head.  Its complement pays the only omitted tail.  This paired pass is the
minimal data needed by the staged grouped leaf; it introduces no additional
transcendental certificate payload.
-/

set_option autoImplicit false

open Set
open scoped BigOperators

namespace CourtadeKumar

/-- Fixed grouped head length chosen at the measured size/runtime knee. -/
def lrCompactVLambdaGroupedHeadN : ℕ := 192

/-- Lower endpoint of `g=4/(1+v)` on a compact box. -/
def lrCompactVLambdaGLoQ (box : CertificateBox) : ℚ :=
  4 / (1 + box.kHi)

/-- Upper endpoint of `h=4vx/(1+v)` on a compact box. -/
def lrCompactVLambdaHHiQ (box : CertificateBox) : ℚ :=
  4 * lrCompactVMxQ box.kHi box.chiHi

/-- Four-corner lower bound for one grouped summand, with the box-wide shape
endpoints already evaluated.  Passing `gLo` and `hHi` explicitly prevents
their rational divisions from being normalized once per series term. -/
def lrCompactVLambdaGroupedTermLowerWith
    (lambda gLo hHi : ℚ) (box : CertificateBox) (n : ℕ) : ℚ :=
  lrLowAQ n *
    lrCompactVGroupedBilinearCornerLower lambda
      (lrCompactVScoreEnclosure box n).lower
      (lrCompactVScoreEnclosure box n).upper
      (lrCompactVTEnclosure box n).lower
      (lrCompactVTEnclosure box n).upper
      gLo hHi

/-- Public one-term wrapper using the canonical box endpoints. -/
def lrCompactVLambdaGroupedTermLower
    (lambda : ℚ) (box : CertificateBox) (n : ℕ) : ℚ :=
  lrCompactVLambdaGroupedTermLowerWith lambda
    (lrCompactVLambdaGLoQ box) (lrCompactVLambdaHHiQ box) box n

/-- Lower bound for the matching endpoint-kernel head summand. -/
def lrCompactVWeightedScoreTermLower
    (box : CertificateBox) (n : ℕ) : ℚ :=
  lrLowAQ n * (lrCompactVScoreEnclosure box n).lower

/-- Paired rational accumulator used by the executable checker. -/
structure LRCompactVLambdaGroupedAccumulator where
  groupedLower : ℚ
  weightedScoreLower : ℚ

/-- Internal one-pass accumulator with the invariant box-wide endpoints
hoisted outside the recursion. -/
def lrCompactVLambdaGroupedAccumulateAux
    (lambda gLo hHi : ℚ) (box : CertificateBox) :
    ℕ → LRCompactVLambdaGroupedAccumulator
  | 0 => ⟨0, 0⟩
  | N + 1 =>
      let previous := lrCompactVLambdaGroupedAccumulateAux
        lambda gLo hHi box N
      { groupedLower := previous.groupedLower +
          lrCompactVLambdaGroupedTermLowerWith
            lambda gLo hHi box (N + 1)
        weightedScoreLower := previous.weightedScoreLower +
          lrCompactVWeightedScoreTermLower box (N + 1) }

/-- One recursive pass computes both finite lower sums. -/
def lrCompactVLambdaGroupedAccumulate
    (lambda : ℚ) (box : CertificateBox) (N : ℕ) :
    LRCompactVLambdaGroupedAccumulator :=
  lrCompactVLambdaGroupedAccumulateAux lambda
    (lrCompactVLambdaGLoQ box) (lrCompactVLambdaHHiQ box) box N

def lrCompactVLambdaGroupedHeadLower
    (N : ℕ) (lambda : ℚ) (box : CertificateBox) : ℚ :=
  (lrCompactVLambdaGroupedAccumulate lambda box N).groupedLower

def lrCompactVWeightedScoreHeadLower
    (N : ℕ) (lambda : ℚ) (box : CertificateBox) : ℚ :=
  (lrCompactVLambdaGroupedAccumulate lambda box N).weightedScoreLower

/-- Upper bound for the omitted endpoint-kernel tail. -/
def lrCompactVLambdaGroupedTailUpper
    (N : ℕ) (lambda : ℚ) (box : CertificateBox)
    (wOne : RationalEnclosure) : ℚ :=
  max 0 (wOne.upper -
    lrCompactVWeightedScoreHeadLower N lambda box)

/-- Complete rational grouped lower bound after paying the omitted tail. -/
def lrCompactVLambdaGroupedFiniteLower
    (N : ℕ) (lambda : ℚ) (box : CertificateBox)
    (wOne : RationalEnclosure) : ℚ :=
  lrCompactVLambdaGroupedHeadLower N lambda box -
    lrCompactVLambdaHHiQ box *
      lrCompactVLambdaGroupedTailUpper N lambda box wOne

theorem lrCompactVLambdaGLoQ_le
    {box : CertificateBox} {point : CertificatePoint}
    (hbox : LRCompactVBoxValid box) (hpoint : box.Contains point) :
    (lrCompactVLambdaGLoQ box : ℝ) ≤ 4 / (1 + point.k) := by
  have hvPoint : (0 : ℝ) ≤ point.k :=
    (by exact_mod_cast hbox.2.2.2.1 : (0 : ℝ) ≤ box.kLo) |>.trans
      hpoint.2.2.1
  have hdenPoint : 0 < 1 + point.k := by linarith
  have hdenHi : 0 < 1 + (box.kHi : ℝ) := by
    linarith [hpoint.2.2.2.1]
  change ((4 / (1 + box.kHi) : ℚ) : ℝ) ≤ 4 / (1 + point.k)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_add, Rat.cast_one]
  exact div_le_div_of_nonneg_left (by norm_num) hdenPoint
    (by linarith [hpoint.2.2.2.1])

theorem lrCompactVLambdaH_le_HHiQ
    {box : CertificateBox} {point : CertificatePoint}
    (hbox : LRCompactVBoxValid box) (hpoint : box.Contains point) :
    4 * lrCompactVMx point.k point.chi ≤
      (lrCompactVLambdaHHiQ box : ℝ) := by
  have hmx := lrCompactVMxEnclosure_sound hbox hpoint
  have hscaled := mul_le_mul_of_nonneg_left hmx.2 (by norm_num : (0 : ℝ) ≤ 4)
  simpa [lrCompactVLambdaHHiQ, lrCompactVMxEnclosure] using hscaled

theorem lrCompactVLambdaGroupedTermLower_le
    {lambda : ℚ} (hlambda : (0 : ℚ) ≤ lambda)
    {box : CertificateBox} {point : CertificatePoint}
    (hbox : LRCompactVBoxValid box) (hpoint : box.Contains point)
    {n : ℕ} (hn : 1 ≤ n) :
    (lrCompactVLambdaGroupedTermLower lambda box n : ℝ) ≤
      lrLowA n *
        lrCompactVLambdaGroup (lambda : ℝ)
          (lrCompactVScore point.s n)
          (lrCompactVT point.k point.chi n)
          (4 / (1 + point.k))
          (4 * lrCompactVMx point.k point.chi) := by
  have hscore := lrCompactVScoreEnclosure_sound hn
    hbox.1 hbox.2.2.1 hpoint
  have hT := lrCompactVTEnclosure_sound (n := n)
    hbox.2.2.2.1 hbox.2.2.2.2.2.2.1 hpoint
  have hcorner := cast_lrCompactVGroupedBilinearCornerLower_le
    (lambda := lambda) (g := lrCompactVLambdaGLoQ box)
    (h := lrCompactVLambdaHHiQ box)
    hscore.1 hscore.2 hT.1 hT.2
  have hRPoint : point.s ∈ Icc (0 : ℝ) 1 :=
    ⟨(by exact_mod_cast hbox.1 : (0 : ℝ) ≤ box.sLo) |>.trans hpoint.1,
      hpoint.2.1.trans (by exact_mod_cast hbox.2.2.1 : (box.sHi : ℝ) ≤ 1)⟩
  have hw0 := lrCompactVScore_nonneg hRPoint.1 hn
  have hw1 := lrCompactVScore_le_one hRPoint hn
  have hlambdaReal : (0 : ℝ) ≤ lambda := by exact_mod_cast hlambda
  have hg := lrCompactVLambdaGLoQ_le hbox hpoint
  have hh := lrCompactVLambdaH_le_HHiQ hbox hpoint
  have hshape :
      lrCompactVGroupedBilinearReal (lambda : ℝ)
          (lrCompactVScore point.s n)
          (lrCompactVT point.k point.chi n)
          (lrCompactVLambdaGLoQ box : ℝ)
          (lrCompactVLambdaHHiQ box : ℝ) ≤
        lrCompactVGroupedBilinearReal (lambda : ℝ)
          (lrCompactVScore point.s n)
          (lrCompactVT point.k point.chi n)
          (4 / (1 + point.k))
          (4 * lrCompactVMx point.k point.chi) := by
    calc
      lrCompactVGroupedBilinearReal (lambda : ℝ)
          (lrCompactVScore point.s n)
          (lrCompactVT point.k point.chi n)
          (lrCompactVLambdaGLoQ box : ℝ)
          (lrCompactVLambdaHHiQ box : ℝ) ≤
        lrCompactVGroupedBilinearReal (lambda : ℝ)
          (lrCompactVScore point.s n)
          (lrCompactVT point.k point.chi n)
          (4 / (1 + point.k))
          (lrCompactVLambdaHHiQ box : ℝ) := by
            unfold lrCompactVGroupedBilinearReal
            exact add_le_add_right
              (mul_le_mul_of_nonneg_left
                (sub_le_sub_right hg _)
                (mul_nonneg hlambdaReal (sub_nonneg.mpr hw1))) _
      _ ≤ lrCompactVGroupedBilinearReal (lambda : ℝ)
          (lrCompactVScore point.s n)
          (lrCompactVT point.k point.chi n)
          (4 / (1 + point.k))
          (4 * lrCompactVMx point.k point.chi) := by
            unfold lrCompactVGroupedBilinearReal
            exact add_le_add_left
              (mul_le_mul_of_nonneg_left
                (sub_le_sub_left hh _ ) hw0) _
  have hgroup := hcorner.trans hshape
  unfold lrCompactVLambdaGroupedTermLower
    lrCompactVLambdaGroupedTermLowerWith
  norm_num only [Rat.cast_mul]
  rw [cast_lrLowAQ]
  exact mul_le_mul_of_nonneg_left
    (by simpa [lrCompactVLambdaGroup,
        lrCompactVGroupedBilinearReal] using hgroup)
    (lrLowA_pos hn).le

theorem lrCompactVWeightedScoreTermLower_le
    {box : CertificateBox} {point : CertificatePoint}
    (hbox : LRCompactVBoxValid box) (hpoint : box.Contains point)
    {n : ℕ} (hn : 1 ≤ n) :
    (lrCompactVWeightedScoreTermLower box n : ℝ) ≤
      lrCompactVWTerm point.s 1 n := by
  have hscore := lrCompactVScoreEnclosure_sound hn
    hbox.1 hbox.2.2.1 hpoint
  unfold lrCompactVWeightedScoreTermLower lrCompactVWTerm
  norm_num only [Rat.cast_mul, one_pow, mul_one]
  rw [cast_lrLowAQ]
  exact mul_le_mul_of_nonneg_left hscore.1 (lrLowA_pos hn).le

theorem lrCompactVLambdaGroupedAccumulate_le
    {lambda : ℚ} (hlambda : (0 : ℚ) ≤ lambda)
    {box : CertificateBox} {point : CertificatePoint}
    (hbox : LRCompactVBoxValid box) (hpoint : box.Contains point) :
    ∀ N,
      ((lrCompactVLambdaGroupedAccumulate lambda box N).groupedLower : ℝ) ≤
          ∑ j ∈ Finset.range N,
            lrLowA (j + 1) *
              lrCompactVLambdaGroup (lambda : ℝ)
                (lrCompactVScore point.s (j + 1))
                (lrCompactVT point.k point.chi (j + 1))
                (4 / (1 + point.k))
                (4 * lrCompactVMx point.k point.chi) ∧
        ((lrCompactVLambdaGroupedAccumulate lambda box N).weightedScoreLower : ℝ) ≤
          ∑ j ∈ Finset.range N,
            lrCompactVWTerm point.s 1 (j + 1)
  | 0 => by simp [lrCompactVLambdaGroupedAccumulate,
      lrCompactVLambdaGroupedAccumulateAux]
  | N + 1 => by
      have ih := lrCompactVLambdaGroupedAccumulate_le
        hlambda hbox hpoint N
      have hgroupTerm := lrCompactVLambdaGroupedTermLower_le
        hlambda hbox hpoint (show 1 ≤ N + 1 by omega)
      have hweightedTerm := lrCompactVWeightedScoreTermLower_le
        hbox hpoint (show 1 ≤ N + 1 by omega)
      constructor
      · change
          (((lrCompactVLambdaGroupedAccumulate lambda box N).groupedLower +
            lrCompactVLambdaGroupedTermLower lambda box (N + 1) : ℚ) : ℝ) ≤ _
        norm_num only [Rat.cast_add]
        rw [Finset.sum_range_succ]
        exact add_le_add ih.1 hgroupTerm
      · change
          (((lrCompactVLambdaGroupedAccumulate lambda box N).weightedScoreLower +
            lrCompactVWeightedScoreTermLower box (N + 1) : ℚ) : ℝ) ≤ _
        norm_num only [Rat.cast_add]
        rw [Finset.sum_range_succ]
        exact add_le_add ih.2 hweightedTerm

theorem lrCompactVLambdaGroupedHeadLower_le
    {N : ℕ} {lambda : ℚ} (hlambda : (0 : ℚ) ≤ lambda)
    {box : CertificateBox} {point : CertificatePoint}
    (hbox : LRCompactVBoxValid box) (hpoint : box.Contains point) :
    (lrCompactVLambdaGroupedHeadLower N lambda box : ℝ) ≤
      lrCompactVLambdaGroupedHead N (lambda : ℝ)
        point.s point.k point.chi := by
  have h := (lrCompactVLambdaGroupedAccumulate_le
    hlambda hbox hpoint N).1
  simpa [lrCompactVLambdaGroupedHeadLower,
    lrCompactVLambdaGroupedHead] using h

theorem lrCompactVWeightedScoreHeadLower_le
    {N : ℕ} {lambda : ℚ} (hlambda : (0 : ℚ) ≤ lambda)
    {box : CertificateBox} {point : CertificatePoint}
    (hbox : LRCompactVBoxValid box) (hpoint : box.Contains point) :
    (lrCompactVWeightedScoreHeadLower N lambda box : ℝ) ≤
      lrCompactVWeightedScoreHead N point.s := by
  have h := (lrCompactVLambdaGroupedAccumulate_le
    hlambda hbox hpoint N).2
  simpa [lrCompactVWeightedScoreHeadLower,
    lrCompactVWeightedScoreHead] using h

theorem lrCompactVLambdaGroupedFiniteLower_le
    {N : ℕ} {lambda : ℚ} (hlambda : (0 : ℚ) ≤ lambda)
    {box : CertificateBox} {point : CertificatePoint}
    (hbox : LRCompactVBoxValid box) (hpoint : box.Contains point)
    (hinterior : LRCompactVInterior point)
    {wOne : RationalEnclosure}
    (hwOne : wOne.Contains (lrWKernel point.s 1)) :
    (lrCompactVLambdaGroupedFiniteLower N lambda box wOne : ℝ) ≤
      lrCompactVLambdaGroupedFinite N (lambda : ℝ)
        point.s point.k point.chi := by
  have hgroup := lrCompactVLambdaGroupedHeadLower_le
    (N := N) hlambda hbox hpoint
  have hweighted := lrCompactVWeightedScoreHeadLower_le
    (N := N) hlambda hbox hpoint
  have hheadW := lrCompactVWeightedScoreHead_le_lrWKernel
    hinterior.1 N
  have htail0 :
      0 ≤ lrWKernel point.s 1 -
        lrCompactVWeightedScoreHead N point.s := by linarith
  have htailRaw :
      lrWKernel point.s 1 - lrCompactVWeightedScoreHead N point.s ≤
        ((wOne.upper -
          lrCompactVWeightedScoreHeadLower N lambda box : ℚ) : ℝ) := by
    norm_num only [Rat.cast_sub]
    linarith [hwOne.2, hweighted]
  have htailUpper :
      lrWKernel point.s 1 - lrCompactVWeightedScoreHead N point.s ≤
        (lrCompactVLambdaGroupedTailUpper
          N lambda box wOne : ℝ) := by
    unfold lrCompactVLambdaGroupedTailUpper
    rw [Rat.cast_max, Rat.cast_zero]
    exact htailRaw.trans (le_max_right _ _)
  have hh := lrCompactVLambdaH_le_HHiQ hbox hpoint
  have hhHi0Q : (0 : ℚ) ≤ lrCompactVLambdaHHiQ box := by
    have hkHi0 : (0 : ℚ) ≤ box.kHi :=
      hbox.2.2.2.1.trans hbox.2.2.2.2.1
    have hchiHi0 : (0 : ℚ) ≤ box.chiHi :=
      hbox.2.2.2.2.2.2.1.trans hbox.2.2.2.2.2.2.2.1
    unfold lrCompactVLambdaHHiQ lrCompactVMxQ
    exact mul_nonneg (by norm_num) <|
      div_nonneg
        (mul_nonneg hkHi0 hchiHi0)
        (by linarith)
  have hhHi0 : (0 : ℝ) ≤ lrCompactVLambdaHHiQ box := by
    exact_mod_cast hhHi0Q
  have htailProduct :
      4 * lrCompactVMx point.k point.chi *
          (lrWKernel point.s 1 -
            lrCompactVWeightedScoreHead N point.s) ≤
        (lrCompactVLambdaHHiQ box : ℝ) *
          (lrCompactVLambdaGroupedTailUpper
            N lambda box wOne : ℝ) :=
    mul_le_mul hh htailUpper htail0 hhHi0
  unfold lrCompactVLambdaGroupedFiniteLower
    lrCompactVLambdaGroupedFinite
  norm_num only [Rat.cast_sub, Rat.cast_mul]
  linarith

end CourtadeKumar
