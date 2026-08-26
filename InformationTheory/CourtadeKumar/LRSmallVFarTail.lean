import InformationTheory.CourtadeKumar.LRSmallVTailPayment

/-!
# Positivity of the remote small-odds tail

This is the induction in equation (102).  Retaining a single positive
coefficient dominates every remote tail coefficient, uniformly in its
index.
-/

namespace CourtadeKumar

lemma lrSmallV_far_tail_step
    {r : ℕ} (hr : 3 ≤ r)
    (hprev : (3 * (r : ℝ)) / 4 ≤
      lrLowA (r - 1) * 3 ^ (2 * r - 3)) :
    (3 * ((r + 1 : ℕ) : ℝ)) / 4 ≤
      lrLowA ((r + 1) - 1) * 3 ^ (2 * (r + 1) - 3) := by
  rw [show r + 1 - 1 = r by omega,
    show 2 * (r + 1) - 3 = (2 * r - 3) + 2 by omega, pow_add]
  norm_num only [pow_two]
  have hrR : (3 : ℝ) ≤ r := by exact_mod_cast hr
  have hrPos : (0 : ℝ) < r := by linarith
  have hrOnePos : (0 : ℝ) < (r : ℝ) - 1 := by linarith
  have htwoPrev : (0 : ℝ) < 2 * ((r : ℝ) - 1) - 1 := by linarith
  have htwoNow : (0 : ℝ) < 2 * (r : ℝ) - 1 := by linarith
  unfold lrLowA at hprev
  have hcast : ((r - 1 : ℕ) : ℝ) = (r : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ r)]
    norm_num
  rw [hcast] at hprev
  norm_num only [Nat.cast_add]
  have hpoly :
      ((r : ℝ) + 1) * (2 * r - 1) ≤
        9 * (r - 1) * (2 * r - 3) := by
    nlinarith [sq_nonneg ((r : ℝ) - 3)]
  field_simp [hrPos.ne', hrOnePos.ne', htwoPrev.ne'] at hprev
  ring_nf at hprev
  have hpolyScaled := mul_le_mul_of_nonneg_left hpoly
    (show (0 : ℝ) ≤ 6 * r by positivity)
  have hcross :
      3 * ((r : ℝ) + 1) * (2 * r * (2 * r - 1)) ≤
        4 * (3 ^ (2 * r - 3) * 9) := by
    ring_nf at hpolyScaled ⊢
    nlinarith
  unfold lrLowA
  have hden : (0 : ℝ) < 2 * r * (2 * r - 1) := by positivity
  rw [show 1 / (2 * (r : ℝ) * (2 * r - 1)) *
      (3 ^ (2 * r - 3) * 9) =
        (3 ^ (2 * r - 3) * 9) / (2 * r * (2 * r - 1)) by ring]
  rw [le_div_iff₀ hden]
  nlinarith

theorem lrSmallV_far_tail_bound
    {r : ℕ} (hr : 2 ≤ r) :
    (3 * (r : ℝ)) / 4 ≤
      lrLowA (r - 1) * 3 ^ (2 * r - 3) := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
      by_cases hr2 : r = 2
      · subst r
        norm_num [lrLowA]
      by_cases hr3 : r = 3
      · subst r
        norm_num [lrLowA]
      · have hr4 : 4 ≤ r := by omega
        have hprev := ih (r - 1) (by omega) (by omega : 2 ≤ r - 1)
        have hstep := lrSmallV_far_tail_step
          (r := r - 1) (by omega) hprev
        simpa only [Nat.sub_add_cancel (by omega : 1 ≤ r)] using hstep

theorem lrSmallV_far_tail_margin
    {r : ℕ} (hr : 2 ≤ r) :
    (1 / 2 : ℝ) ≤
      1 / 2 - 3 * r / 4 + lrLowA (r - 1) * 3 ^ (2 * r - 3) := by
  linarith [lrSmallV_far_tail_bound hr]

end CourtadeKumar
