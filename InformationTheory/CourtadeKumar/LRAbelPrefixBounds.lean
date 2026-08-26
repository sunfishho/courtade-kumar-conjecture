import InformationTheory.CourtadeKumar.LRAbelPrefixBrace

/-! Finite logarithmic-prefix bounds in the audited base Abel argument. -/

open Set Finset
open scoped BigOperators

namespace CourtadeKumar

noncomputable def lrAbelLogPrefix (N : ℕ) (v : ℝ) : ℝ :=
  ∑ k ∈ Finset.range N,
    (v ^ 2 * (v ^ 2) ^ k) / (2 * ((k : ℝ) + 1))

lemma lrAbelLogPrefix_nonneg
    {N : ℕ} {v : ℝ} :
    0 ≤ lrAbelLogPrefix N v := by
  unfold lrAbelLogPrefix
  apply Finset.sum_nonneg
  intro k _
  exact div_nonneg
    (mul_nonneg (sq_nonneg v) (pow_nonneg (sq_nonneg v) k))
    (by positivity)

theorem lrAbelLogPrefix_le_geom
    (N : ℕ) (v : ℝ) :
    lrAbelLogPrefix N v ≤
      v ^ 2 / 2 * lrGeomPrefix N (v ^ 2) := by
  unfold lrAbelLogPrefix lrGeomPrefix
  calc
    (∑ k ∈ Finset.range N,
        (v ^ 2 * (v ^ 2) ^ k) / (2 * ((k : ℝ) + 1))) ≤
      ∑ k ∈ Finset.range N, (v ^ 2 * (v ^ 2) ^ k) / 2 := by
        apply Finset.sum_le_sum
        intro k _
        have hnum : 0 ≤ v ^ 2 * (v ^ 2) ^ k :=
          mul_nonneg (sq_nonneg v) (pow_nonneg (sq_nonneg v) k)
        have hk0 : 0 ≤ (k : ℝ) := by positivity
        have hk : 1 ≤ (k : ℝ) + 1 := by linarith
        have hden : 0 < 2 * ((k : ℝ) + 1) := by positivity
        rw [div_le_iff₀ hden]
        nlinarith
    _ = v ^ 2 / 2 * ∑ k ∈ Finset.range N, (v ^ 2) ^ k := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring

theorem lrAbelLogPrefix_le_closed
    (N : ℕ) {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v < 1) :
    lrAbelLogPrefix N v ≤
      v ^ 2 * (1 - v ^ (2 * N)) / (2 * (1 - v ^ 2)) := by
  have hvSqLt : v ^ 2 < 1 := by nlinarith
  have hden : 0 < 1 - v ^ 2 := sub_pos.mpr hvSqLt
  have hgeom := one_sub_mul_lrGeomPrefix N (v ^ 2)
  have hpow : (v ^ 2) ^ N = v ^ (2 * N) := by rw [← pow_mul]
  rw [hpow] at hgeom
  have hgeomClosed :
      lrGeomPrefix N (v ^ 2) = (1 - v ^ (2 * N)) / (1 - v ^ 2) := by
    apply (eq_div_iff hden.ne').2
    nlinarith [hgeom]
  have h := lrAbelLogPrefix_le_geom N v
  rw [hgeomClosed] at h
  calc
    lrAbelLogPrefix N v ≤
        v ^ 2 / 2 * ((1 - v ^ (2 * N)) / (1 - v ^ 2)) := h
    _ = v ^ 2 * (1 - v ^ (2 * N)) / (2 * (1 - v ^ 2)) := by
      field_simp [hden.ne']

end CourtadeKumar
