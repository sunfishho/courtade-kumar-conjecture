import InformationTheory.CourtadeKumar.LRLowShapeQTail

/-!
# Closed forms for the low-shape tails

These identities split `L(√ξ)` at an arbitrary index and rewrite `R_n` in
terms of the same logarithmic tail.  They are the analytic bridge needed for
the exact formula `ℒ_n - V_* = C_*α_n - δQ_n - G R_n`.
-/

open scoped BigOperators

namespace CourtadeKumar

lemma lrLowRTail_eq_logTail
    {xi : ℝ} (hxi0 : 0 ≤ xi) (hxi1 : xi < 1) (n : ℕ) :
    lrLowRTail xi n =
      (1 / 2 : ℝ) *
        (xi ^ (n + 1) / (1 - xi) -
          (n : ℝ) * lrLowLogTail xi (n + 1)) := by
  let geom : ℕ → ℝ := fun k ↦ xi ^ (k + n + 1)
  let logTerm : ℕ → ℝ := fun k ↦
    xi ^ (k + n + 1) / ((k + n + 1 : ℕ) : ℝ)
  have hgeom : HasSum geom (xi ^ (n + 1) / (1 - xi)) := by
    have h := (hasSum_geometric_of_lt_one hxi0 hxi1).mul_left (xi ^ (n + 1))
    convert h using 1
    funext k
    dsimp [geom]
    rw [show k + n + 1 = (n + 1) + k by omega, pow_add]
  have hlog : Summable logTerm := by
    simpa [logTerm, add_assoc] using
      summable_lrLowLogTail hxi0 hxi1 (show 1 ≤ n + 1 by omega)
  have hterm (k : ℕ) :
      ((k + 1 : ℕ) : ℝ) / (k + n + 1) * xi ^ (k + n + 1) / 2 =
        (1 / 2 : ℝ) * (geom k - (n : ℝ) * logTerm k) := by
    dsimp [geom, logTerm]
    have hden : (0 : ℝ) < ((k + n + 1 : ℕ) : ℝ) := by positivity
    field_simp [hden.ne']
    push_cast
    ring
  unfold lrLowRTail
  calc
    ∑' k : ℕ,
        ((k + 1 : ℕ) : ℝ) / (k + n + 1) * xi ^ (k + n + 1) / 2 =
      ∑' k : ℕ, (1 / 2 : ℝ) * (geom k - (n : ℝ) * logTerm k) :=
        tsum_congr hterm
    _ = (1 / 2 : ℝ) *
        ((∑' k : ℕ, geom k) - (n : ℝ) * (∑' k : ℕ, logTerm k)) := by
      rw [tsum_mul_left, hgeom.summable.tsum_sub (hlog.mul_left (n : ℝ)),
        tsum_mul_left]
    _ = (1 / 2 : ℝ) *
        (xi ^ (n + 1) / (1 - xi) -
          (n : ℝ) * lrLowLogTail xi (n + 1)) := by
      rw [hgeom.tsum_eq]
      rfl

lemma lrL_sqrt_eq_prefix_add_logTail
    {xi : ℝ} (hxi0 : 0 < xi) (hxi1 : xi < 1)
    {n : ℕ} (hn : 1 ≤ n) :
    lrL (Real.sqrt xi) =
      (1 / 2 : ℝ) *
        ((∑ k ∈ Finset.range (n - 1),
          xi ^ (k + 1) / ((k + 1 : ℕ) : ℝ)) +
          lrLowLogTail xi n) := by
  let f : ℕ → ℝ := fun k ↦ xi ^ (k + 1) / (2 * ((k + 1 : ℕ) : ℝ))
  have hf : HasSum f (lrL (Real.sqrt xi)) := by
    simpa [f] using lrL_sqrt_hasSum (show xi ∈ Set.Ioo (0 : ℝ) 1 from ⟨hxi0, hxi1⟩)
  have hsplit := hf.summable.sum_add_tsum_nat_add (n - 1)
  rw [hf.tsum_eq] at hsplit
  rw [← hsplit]
  have htail :
      (∑' k : ℕ, f (k + (n - 1))) =
        (1 / 2 : ℝ) * lrLowLogTail xi n := by
    unfold lrLowLogTail
    rw [← tsum_mul_left]
    apply tsum_congr
    intro k
    dsimp [f]
    have hindex : k + (n - 1) + 1 = k + n := by omega
    rw [hindex]
    ring
  rw [htail]
  dsimp [f]
  rw [mul_add, Finset.mul_sum]
  apply congrArg₂ (fun a b : ℝ ↦ a + b) _ rfl
  apply Finset.sum_congr rfl
  intro k hk
  ring

end CourtadeKumar
