import InformationTheory.CourtadeKumar.BellmanInduction

/-! The ordered equal-multiplier interface and its sorting reduction. -/

open scoped ENNReal NNReal BigOperators

namespace CourtadeKumar

lemma cubeAverage_congr {n : ℕ} {f g : BitVec n → ℝ}
    (h : ∀ x, f x = g x) : cubeAverage n f = cubeAverage n g := by
  unfold cubeAverage
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  exact h x

lemma cubeAverage_add (n : ℕ) (f g : BitVec n → ℝ) :
    cubeAverage n (fun x ↦ f x + g x) = cubeAverage n f + cubeAverage n g := by
  unfold cubeAverage
  rw [Finset.sum_add_distrib]
  ring

lemma cubeAverage_min_add_max (n : ℕ) (A B : BitVec n → ℝ) :
    cubeAverage n (fun y ↦ min (A y) (B y)) +
        cubeAverage n (fun y ↦ max (A y) (B y)) =
      cubeAverage n A + cubeAverage n B := by
  rw [← cubeAverage_add, ← cubeAverage_add]
  apply cubeAverage_congr
  intro y
  exact min_add_max (A y) (B y)

lemma cubeAverage_binaryEntropy_min_add_max
    (n : ℕ) (A B : BitVec n → ℝ) :
    cubeAverage n (fun y ↦ binaryEntropyBits (min (A y) (B y))) +
        cubeAverage n (fun y ↦ binaryEntropyBits (max (A y) (B y))) =
      cubeAverage n (fun y ↦ binaryEntropyBits (A y)) +
        cubeAverage n (fun y ↦ binaryEntropyBits (B y)) := by
  rw [← cubeAverage_add, ← cubeAverage_add]
  apply cubeAverage_congr
  intro y
  rcases le_total (A y) (B y) with h | h
  · simp [min_eq_left h, max_eq_right h]
  · simp [min_eq_right h, max_eq_left h, add_comm]

lemma binaryEntropyPair_swap (alpha : ℝ≥0) (a b : ℝ) :
    binaryEntropyPair alpha a b = binaryEntropyPair alpha b a := by
  unfold binaryEntropyPair
  have h₁ : (1 - (alpha : ℝ)) * b + (alpha : ℝ) * a =
      (alpha : ℝ) * a + (1 - (alpha : ℝ)) * b := by ring
  have h₂ : (alpha : ℝ) * b + (1 - (alpha : ℝ)) * a =
      (1 - (alpha : ℝ)) * a + (alpha : ℝ) * b := by ring
  rw [h₁, h₂]
  ring

lemma cubeAverage_binaryEntropyPair_min_max
    (n : ℕ) (alpha : ℝ≥0) (A B : BitVec n → ℝ) :
    cubeAverage n (fun y ↦
        binaryEntropyPair alpha (min (A y) (B y)) (max (A y) (B y))) =
      cubeAverage n (fun y ↦ binaryEntropyPair alpha (A y) (B y)) := by
  apply cubeAverage_congr
  intro y
  rcases le_total (A y) (B y) with h | h
  · simp [min_eq_left h, max_eq_right h]
  · simp [min_eq_right h, max_eq_left h, binaryEntropyPair_swap]

/-- The manuscript's Bellman assertion, stated for finite cube averages and
ordered pairs.  Its two mean parameters are recovered from the actual pair. -/
def OrderedEqualMultiplierBellmanStep (alpha : ℝ≥0) : Prop :=
  ∀ (n : ℕ) (A B : BitVec n → ℝ),
    (∀ y, 0 ≤ A y ∧ A y ≤ 1) →
    (∀ y, 0 ≤ B y ∧ B y ≤ 1) →
    (∀ y, A y ≤ B y) →
    cubeAverage n (fun y ↦ binaryEntropyBits (A y)) +
        cubeAverage n (fun y ↦ binaryEntropyBits (B y)) ≥
      bellmanEnvelope (alpha : ℝ) (cubeAverage n A) +
        bellmanEnvelope (alpha : ℝ) (cubeAverage n B) →
    cubeAverage n (fun y ↦ binaryEntropyPair alpha (A y) (B y)) ≥
      bellmanEnvelope (alpha : ℝ)
        ((cubeAverage n A + cubeAverage n B) / 2)

/-- Sorting may increase the spread of the two means.  This is the exact
finite form of the concavity/monotonicity consequence used in the manuscript. -/
def BellmanEnvelopeSortingDominance (alpha : ℝ≥0) : Prop :=
  ∀ (n : ℕ) (A B : BitVec n → ℝ),
    bellmanEnvelope (alpha : ℝ) (cubeAverage n A) +
        bellmanEnvelope (alpha : ℝ) (cubeAverage n B) ≥
      bellmanEnvelope (alpha : ℝ)
          (cubeAverage n (fun y ↦ min (A y) (B y))) +
        bellmanEnvelope (alpha : ℝ)
          (cubeAverage n (fun y ↦ max (A y) (B y)))

/-- The ordered equal-multiplier assertion plus the envelope's sorting
dominance imply the exact Bellman step required by Boolean induction. -/
theorem booleanBellmanStep_of_orderedEqualMultiplier
    (alpha : ℝ≥0)
    (hOrdered : OrderedEqualMultiplierBellmanStep alpha)
    (hSort : BellmanEnvelopeSortingDominance alpha) :
    BooleanBellmanStep alpha := by
  intro n A B hA hB hEntA hEntB
  let Amin : BitVec n → ℝ := fun y ↦ min (A y) (B y)
  let Amax : BitVec n → ℝ := fun y ↦ max (A y) (B y)
  have hminus : ∀ y, 0 ≤ Amin y ∧ Amin y ≤ 1 := by
    intro y
    exact ⟨le_min (hA y).1 (hB y).1, (min_le_left _ _).trans (hA y).2⟩
  have hplus : ∀ y, 0 ≤ Amax y ∧ Amax y ≤ 1 := by
    intro y
    exact ⟨(hA y).1.trans (le_max_left _ _), max_le (hA y).2 (hB y).2⟩
  have horder : ∀ y, Amin y ≤ Amax y := by
    intro y
    exact min_le_max
  have hEntropySum :
      cubeAverage n (fun y ↦ binaryEntropyBits (Amin y)) +
          cubeAverage n (fun y ↦ binaryEntropyBits (Amax y)) ≥
        bellmanEnvelope (alpha : ℝ) (cubeAverage n Amin) +
          bellmanEnvelope (alpha : ℝ) (cubeAverage n Amax) := by
    have hOriginal :
        cubeAverage n (fun y ↦ binaryEntropyBits (A y)) +
            cubeAverage n (fun y ↦ binaryEntropyBits (B y)) ≥
          bellmanEnvelope (alpha : ℝ) (cubeAverage n A) +
            bellmanEnvelope (alpha : ℝ) (cubeAverage n B) := by
      linarith
    calc
      cubeAverage n (fun y ↦ binaryEntropyBits (Amin y)) +
          cubeAverage n (fun y ↦ binaryEntropyBits (Amax y)) =
          cubeAverage n (fun y ↦ binaryEntropyBits (A y)) +
            cubeAverage n (fun y ↦ binaryEntropyBits (B y)) := by
              simpa [Amin, Amax] using cubeAverage_binaryEntropy_min_add_max n A B
      _ ≥ bellmanEnvelope (alpha : ℝ) (cubeAverage n A) +
            bellmanEnvelope (alpha : ℝ) (cubeAverage n B) := hOriginal
      _ ≥ bellmanEnvelope (alpha : ℝ) (cubeAverage n Amin) +
            bellmanEnvelope (alpha : ℝ) (cubeAverage n Amax) := by
              simpa [Amin, Amax] using hSort n A B
  have hOrderedResult :=
    hOrdered n Amin Amax hminus hplus horder hEntropySum
  calc
    cubeAverage n (fun y ↦ binaryEntropyPair alpha (A y) (B y)) =
        cubeAverage n (fun y ↦ binaryEntropyPair alpha (Amin y) (Amax y)) := by
          symm
          simpa [Amin, Amax] using cubeAverage_binaryEntropyPair_min_max n alpha A B
    _ ≥ bellmanEnvelope (alpha : ℝ)
          ((cubeAverage n Amin + cubeAverage n Amax) / 2) := hOrderedResult
    _ = bellmanEnvelope (alpha : ℝ)
          ((cubeAverage n A + cubeAverage n B) / 2) := by
            rw [show cubeAverage n Amin + cubeAverage n Amax =
              cubeAverage n A + cubeAverage n B by
                simpa [Amin, Amax] using cubeAverage_min_add_max n A B]

end CourtadeKumar
