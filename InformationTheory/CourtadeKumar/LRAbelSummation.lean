import InformationTheory.CourtadeKumar.LRAbelFirstPrefix

/-! A kernel-checked infinite Abel summation lemma for the LR base reserve. -/

open Set Finset
open scoped BigOperators Topology

namespace CourtadeKumar

/-- The prefix through index `n` of a zero-indexed coefficient sequence. -/
noncomputable def lrSeriesPrefix (c : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), c k

lemma lrSeriesPrefix_zero (c : ℕ → ℝ) :
    lrSeriesPrefix c 0 = c 0 := by
  simp [lrSeriesPrefix]

lemma lrSeriesPrefix_succ_sub (c : ℕ → ℝ) (n : ℕ) :
    lrSeriesPrefix c (n + 1) - lrSeriesPrefix c n = c (n + 1) := by
  unfold lrSeriesPrefix
  rw [show n + 1 + 1 = (n + 1) + 1 by omega, Finset.sum_range_succ]
  ring

/-- Infinite Abel summation, indexed so that `c n` is the coefficient of
`x^(n+1)`.  Summability of the weighted prefix series supplies exactly the
boundary-term convergence needed by the classical argument. -/
theorem lr_hasSum_abel
    (c : ℕ → ℝ) (x A : ℝ)
    (hS : HasSum (fun n : ℕ ↦ lrSeriesPrefix c n * x ^ (n + 1)) A) :
    HasSum (fun n : ℕ ↦ c n * x ^ (n + 1)) ((1 - x) * A) := by
  let b : ℕ → ℝ := fun n ↦
    if n = 0 then 0 else lrSeriesPrefix c (n - 1) * x ^ (n + 1)
  have htail : HasSum (fun n : ℕ ↦ b (n + 1)) (x * A) := by
    convert hS.mul_left x using 1
    funext n
    simp only [b, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte]
    rw [Nat.add_sub_cancel, pow_succ]
    ring
  have hb : HasSum b (x * A) := by
    have h := (hasSum_nat_add_iff (f := b) 1).mp htail
    simpa [b] using h
  have hdiff := hS.sub hb
  convert hdiff using 1
  · funext n
    cases n with
    | zero => simp [b, lrSeriesPrefix_zero]
    | succ n =>
        simp only [b, Nat.succ_ne_zero, ↓reduceIte, Nat.succ_sub_one]
        rw [show c (n + 1) =
          lrSeriesPrefix c (n + 1) - lrSeriesPrefix c n from
            (lrSeriesPrefix_succ_sub c n).symm]
        rw [pow_succ]
        ring
  · ring

/-- Positivity consequence of Abel summation.  This form is designed for
identifying an analytic expression with its coefficient series. -/
theorem lr_abel_sum_nonneg
    (c : ℕ → ℝ) (x A F : ℝ)
    (hx : x ∈ Icc (0 : ℝ) 1)
    (hprefix : ∀ n, 0 ≤ lrSeriesPrefix c n)
    (hS : HasSum (fun n : ℕ ↦ lrSeriesPrefix c n * x ^ (n + 1)) A)
    (hF : HasSum (fun n : ℕ ↦ c n * x ^ (n + 1)) F) :
    0 ≤ F := by
  have hA : 0 ≤ A := by
    rw [← hS.tsum_eq]
    exact tsum_nonneg fun n ↦ mul_nonneg (hprefix n) (pow_nonneg hx.1 _)
  have hEq : F = (1 - x) * A :=
    hF.unique (lr_hasSum_abel c x A hS)
  rw [hEq]
  exact mul_nonneg (sub_nonneg.mpr hx.2) hA

end CourtadeKumar
