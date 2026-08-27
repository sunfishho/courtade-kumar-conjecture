import InformationTheory.CourtadeKumar.LRCompactVLeafAssembly
import InformationTheory.CourtadeKumar.ExactLogEnclosure

/-!
# Positive-series enclosure for the compact `P₀` factor

The quantity `P₀=Φ(√x)+Φ(v√x)/v` is evaluated without entropy or
square-root interval nodes.  Its coefficients are positive and its shape
monomials decrease with the index on the unit square.  Consequently a finite
head and the exact scalar coefficient tail `lrLowB N` give a rigorous upper
bound, including at boxes whose upper endpoint is `x=1`.
-/

open Set
open scoped BigOperators

namespace CourtadeKumar

/-- Finite positive head of `P₀`. -/
noncomputable def lrCompactVPZeroHead
    (N : ℕ) (v x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range N,
    lrLowA (j + 1) * lrCompactVT v x (j + 1)

lemma lrCompactVT_succ_le
    {v x : ℝ} (hv : v ∈ Icc (0 : ℝ) 1)
    (hx : x ∈ Icc (0 : ℝ) 1) (n : ℕ) :
    lrCompactVT v x (n + 1) ≤ lrCompactVT v x n := by
  have hxpow : x ^ (n + 1) ≤ x ^ n :=
    pow_le_pow_of_le_one hx.1 hx.2 (by omega)
  have hvpow : v ^ (2 * (n + 1) - 1) ≤ v ^ (2 * n - 1) :=
    pow_le_pow_of_le_one hv.1 hv.2 (by omega)
  unfold lrCompactVT
  exact mul_le_mul hxpow (add_le_add_right hvpow 1)
    (add_nonneg zero_le_one (pow_nonneg hv.1 _)) (pow_nonneg hx.1 _)

theorem lrCompactVT_antitone_index
    {v x : ℝ} (hv : v ∈ Icc (0 : ℝ) 1)
    (hx : x ∈ Icc (0 : ℝ) 1) :
    Antitone (lrCompactVT v x) := by
  exact antitone_nat_of_succ_le (lrCompactVT_succ_le hv hx)

theorem lrCompactVPZero_hasSum
    {v x : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1)
    (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasSum (fun j : ℕ ↦
      lrLowA (j + 1) * lrCompactVT v x (j + 1))
      (lrCompactVPZeroX v x) := by
  have hsqrt : Real.sqrt x ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · exact Real.sqrt_pos.2 hx.1
    · simpa using (Real.sqrt_lt_sqrt_iff hx.1.le).2 hx.2
  have hseries := lrCompactVT_hasSum hv hsqrt
  have hsquare : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt hx.1.le
  simpa [lrCompactVPZeroX, hsquare] using hseries

theorem lrCompactVPZeroHead_le
    {v x : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1)
    (hx : x ∈ Ioo (0 : ℝ) 1) (N : ℕ) :
    lrCompactVPZeroHead N v x ≤ lrCompactVPZeroX v x := by
  have hseries := lrCompactVPZero_hasSum hv hx
  rw [← hseries.tsum_eq]
  unfold lrCompactVPZeroHead
  exact hseries.summable.sum_le_tsum (Finset.range N)
    (fun j _ ↦ mul_nonneg (lrLowA_pos (by omega)).le
      (lrCompactVT_nonneg hv.1.le hx.1.le _))

/-- Tail majorant based on monotonicity of the shape monomials. -/
theorem lrCompactVPZero_le_head_add_tail
    {v x : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1)
    (hx : x ∈ Ioo (0 : ℝ) 1) (N : ℕ) :
    lrCompactVPZeroX v x ≤
      lrCompactVPZeroHead N v x +
        lrLowB N * lrCompactVT v x (N + 1) := by
  let f : ℕ → ℝ := fun j ↦
    lrLowA (j + 1) * lrCompactVT v x (j + 1)
  have hseries : HasSum f (lrCompactVPZeroX v x) := by
    simpa [f] using lrCompactVPZero_hasSum hv hx
  have htail : HasSum (fun j : ℕ ↦ f (j + N))
      (lrCompactVPZeroX v x - ∑ j ∈ Finset.range N, f j) :=
    (hasSum_nat_add_iff' N).2 hseries
  let Tbase := lrCompactVT v x (N + 1)
  have hmajor := (lrLowB_hasSum N).mul_left Tbase
  have hterm : ∀ j : ℕ,
      f (j + N) ≤ Tbase * lrLowA (j + N + 1) := by
    intro j
    have hT : lrCompactVT v x (j + N + 1) ≤ Tbase := by
      dsimp [Tbase]
      exact lrCompactVT_antitone_index
        ⟨hv.1.le, hv.2.le⟩ ⟨hx.1.le, hx.2.le⟩ (by omega)
    have ha : 0 ≤ lrLowA (j + N + 1) :=
      (lrLowA_pos (by omega)).le
    dsimp [f]
    rw [show j + N + 1 = (j + N) + 1 by omega]
    nlinarith
  have htailBound :
      lrCompactVPZeroX v x - ∑ j ∈ Finset.range N, f j ≤
        Tbase * lrLowB N := by
    rw [← htail.tsum_eq, ← hmajor.tsum_eq]
    exact htail.summable.tsum_le_tsum hterm hmajor.summable
  unfold lrCompactVPZeroHead
  dsimp [f, Tbase] at htailBound ⊢
  nlinarith

/-- Enclose the finite head using the tight `T_n` endpoint intervals. -/
def lrCompactVPZeroHeadEnclosure
    (N : ℕ) (box : CertificateBox) : RationalEnclosure :=
  RationalEnclosure.sumRangeOne
    (fun n ↦ RationalEnclosure.scale (lrLowAQ n)
      (lrCompactVTEnclosure box n)) N

theorem lrCompactVPZeroHeadEnclosure_sound
    {N : ℕ} {box : CertificateBox} {point : CertificatePoint}
    (hbox : LRCompactVBoxValid box) (hpoint : box.Contains point) :
    (lrCompactVPZeroHeadEnclosure N box).Contains
      (lrCompactVPZeroHead N point.k point.chi) := by
  unfold lrCompactVPZeroHeadEnclosure lrCompactVPZeroHead
  exact RationalEnclosure.contains_sumRangeOne (fun n hn ↦ by
    have hT := lrCompactVTEnclosure_sound (n := n)
      hbox.2.2.2.1 hbox.2.2.2.2.2.2.1 hpoint
    simpa [mul_assoc] using
      RationalEnclosure.contains_scale (lrLowAQ n) hT) N

/-- Enclosure of `lrLowB N=log(2)-∑_{n≤N}a_n`. -/
def lrCompactVCoefficientTailEnclosure
    (terms N : ℕ) : RationalEnclosure :=
  RationalEnclosure.sub (RationalEnclosure.logTwoEnclosure terms)
    (RationalEnclosure.point
      (∑ j ∈ Finset.range N, lrLowAQ (j + 1)))

theorem lrCompactVCoefficientTailEnclosure_sound
    (terms N : ℕ) :
    (lrCompactVCoefficientTailEnclosure terms N).Contains (lrLowB N) := by
  have hlog := RationalEnclosure.contains_logTwoEnclosure terms
  have hsum :
      (RationalEnclosure.point
        (∑ j ∈ Finset.range N, lrLowAQ (j + 1))).Contains
        (∑ j ∈ Finset.range N, lrLowA (j + 1)) := by
    have heq :
        (((∑ j ∈ Finset.range N, lrLowAQ (j + 1)) : ℚ) : ℝ) =
          ∑ j ∈ Finset.range N, lrLowA (j + 1) := by
      push_cast
      apply Finset.sum_congr rfl
      intro j hj
      simp
    simpa [RationalEnclosure.point, RationalEnclosure.Contains, heq]
  simpa [lrCompactVCoefficientTailEnclosure, lrLowB] using
    RationalEnclosure.contains_sub hlog hsum

/-- Complete `P₀` enclosure: exact finite head plus a positive-series tail
on the upper side, while retaining the finite head as the lower endpoint. -/
def lrCompactVPZeroEnclosure
    (terms N : ℕ) (box : CertificateBox) : RationalEnclosure :=
  let head := lrCompactVPZeroHeadEnclosure N box
  let tail := RationalEnclosure.mul
    (lrCompactVCoefficientTailEnclosure terms N)
    (lrCompactVTEnclosure box (N + 1))
  ⟨head.lower, head.upper + tail.upper⟩

theorem lrCompactVPZeroEnclosure_sound
    (terms N : ℕ) {box : CertificateBox} {point : CertificatePoint}
    (hbox : LRCompactVBoxValid box) (hpoint : box.Contains point)
    (hinterior : LRCompactVInterior point) :
    (lrCompactVPZeroEnclosure terms N box).Contains
      (lrCompactVPZeroX point.k point.chi) := by
  have hhead := lrCompactVPZeroHeadEnclosure_sound
    (N := N) hbox hpoint
  have htailCoeff := lrCompactVCoefficientTailEnclosure_sound terms N
  have htailT := lrCompactVTEnclosure_sound (n := N + 1)
    hbox.2.2.2.1 hbox.2.2.2.2.2.2.1 hpoint
  have htail := RationalEnclosure.contains_mul htailCoeff htailT
  have hlower := lrCompactVPZeroHead_le
    hinterior.2.1 hinterior.2.2 N
  have hupper := lrCompactVPZero_le_head_add_tail
    hinterior.2.1 hinterior.2.2 N
  constructor
  · exact hhead.1.trans hlower
  · change lrCompactVPZeroX point.k point.chi ≤
      (((lrCompactVPZeroHeadEnclosure N box).upper +
        (RationalEnclosure.mul
          (lrCompactVCoefficientTailEnclosure terms N)
          (lrCompactVTEnclosure box (N + 1))).upper : ℚ) : ℝ)
    norm_num only [Rat.cast_add]
    exact hupper.trans (add_le_add hhead.2 htail.2)

end CourtadeKumar
