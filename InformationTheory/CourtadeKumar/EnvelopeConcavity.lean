import InformationTheory.CourtadeKumar.EqualMultiplier

/-! Concavity and two-point majorization tools for the Bellman envelope. -/

open Set
open scoped ENNReal NNReal BigOperators

namespace CourtadeKumar

lemma cubeAverage_mono {n : ℕ} {f g : BitVec n → ℝ}
    (h : ∀ x, f x ≤ g x) : cubeAverage n f ≤ cubeAverage n g := by
  unfold cubeAverage
  apply mul_le_mul_of_nonneg_left
  · exact Finset.sum_le_sum fun x _ ↦ h x
  · positivity

@[simp] lemma cubeAverage_const (n : ℕ) (c : ℝ) :
    cubeAverage n (fun _ ↦ c) = c := by
  unfold cubeAverage
  rw [Finset.sum_const, Finset.card_univ, card_bitVec, nsmul_eq_mul]
  have hpow : (2 ^ n : ℝ) ≠ 0 := by positivity
  field_simp
  norm_cast

lemma cubeAverage_mem_Icc {n : ℕ} {f : BitVec n → ℝ}
    (h : ∀ x, 0 ≤ f x ∧ f x ≤ 1) : cubeAverage n f ∈ Icc (0 : ℝ) 1 := by
  constructor
  · simpa using cubeAverage_mono (f := fun _ ↦ (0 : ℝ)) (g := f) (fun x ↦ (h x).1)
  · simpa using cubeAverage_mono (f := f) (g := fun _ ↦ (1 : ℝ)) (fun x ↦ (h x).2)

/-- A two-point majorization inequality: moving two points farther apart while
preserving their sum can only decrease the sum of a concave function. -/
lemma concaveOn_pair_sum_ge_of_outer
    {f : ℝ → ℝ} (hf : ConcaveOn ℝ (Icc (0 : ℝ) 1) f)
    {c a b d : ℝ}
    (hc : c ∈ Icc (0 : ℝ) 1) (hd : d ∈ Icc (0 : ℝ) 1)
    (hca : c ≤ a) (hcb : c ≤ b) (had : a ≤ d) (hbd : b ≤ d)
    (hsum : a + b = c + d) :
    f c + f d ≤ f a + f b := by
  by_cases hcd : c = d
  · have hac : a = c := le_antisymm (hcd ▸ had) hca
    have hbc : b = c := le_antisymm (hcd ▸ hbd) hcb
    simp [hac, hbc, hcd]
  · have hcdlt : c < d := lt_of_le_of_ne (hca.trans had) hcd
    let t : ℝ := (d - a) / (d - c)
    let u : ℝ := (a - c) / (d - c)
    have hden : d - c ≠ 0 := ne_of_gt (sub_pos.mpr hcdlt)
    have ht : 0 ≤ t := by
      dsimp [t]
      exact div_nonneg (sub_nonneg.mpr had) (sub_nonneg.mpr hcdlt.le)
    have hu : 0 ≤ u := by
      dsimp [u]
      exact div_nonneg (sub_nonneg.mpr hca) (sub_nonneg.mpr hcdlt.le)
    have htu : t + u = 1 := by
      dsimp [t, u]
      field_simp
      ring
    have hatu : t * c + u * d = a := by
      dsimp [t, u]
      field_simp
      ring
    have hbtu : u * c + t * d = b := by
      dsimp [t, u]
      field_simp [hden]
      nlinarith [hsum]
    have haConc := hf.2 hc hd ht hu htu
    have hbConc := hf.2 hc hd hu ht (by linarith [htu])
    simp only [smul_eq_mul, hatu] at haConc
    simp only [smul_eq_mul, hbtu] at hbConc
    calc
      f c + f d = (t + u) * f c + (t + u) * f d := by rw [htu]; ring
      _ = (t * f c + u * f d) + (u * f c + t * f d) := by ring
      _ ≤ f a + f b := add_le_add haConc hbConc

/-- Concavity of the envelope supplies the sorting-dominance hypothesis in
the equal-multiplier reduction. -/
theorem bellmanEnvelopeSortingDominance_of_concave
    (alpha : ℝ≥0)
    (hConcave : ConcaveOn ℝ (Icc (0 : ℝ) 1) (bellmanEnvelope (alpha : ℝ))) :
    BellmanEnvelopeSortingDominance alpha := by
  intro n A B hA hB
  let Amin : BitVec n → ℝ := fun y ↦ min (A y) (B y)
  let Amax : BitVec n → ℝ := fun y ↦ max (A y) (B y)
  have hmin : ∀ y, 0 ≤ Amin y ∧ Amin y ≤ 1 := by
    intro y
    exact ⟨le_min (hA y).1 (hB y).1, (min_le_left _ _).trans (hA y).2⟩
  have hmax : ∀ y, 0 ≤ Amax y ∧ Amax y ≤ 1 := by
    intro y
    exact ⟨(hA y).1.trans (le_max_left _ _), max_le (hA y).2 (hB y).2⟩
  apply concaveOn_pair_sum_ge_of_outer hConcave
      (cubeAverage_mem_Icc hmin) (cubeAverage_mem_Icc hmax)
  · exact cubeAverage_mono fun y ↦ min_le_left (A y) (B y)
  · exact cubeAverage_mono fun y ↦ min_le_right (A y) (B y)
  · exact cubeAverage_mono fun y ↦ le_max_left (A y) (B y)
  · exact cubeAverage_mono fun y ↦ le_max_right (A y) (B y)
  · simpa [Amin, Amax] using (cubeAverage_min_add_max n A B).symm

end CourtadeKumar
