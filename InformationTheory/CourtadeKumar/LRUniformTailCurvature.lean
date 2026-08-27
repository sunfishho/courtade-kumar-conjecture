import InformationTheory.CourtadeKumar.LRUniformTailChannel
import InformationTheory.CourtadeKumar.LRCertificateQ

/-!
# Entropy curvature bounds for the uniform cancellation tail

This proves manuscript (M17), extending the already formalized Padé
argument for `atanh` from a short interval to the whole unit interval.
-/

open Set

namespace CourtadeKumar

theorem artanh_le_cubicPade_unit
    {u : ℝ} (hu : u ∈ Ico (0 : ℝ) 1) :
    Real.artanh u ≤ u + u ^ 3 / (3 * (1 - u ^ 2)) := by
  have hdomain : ∀ x ∈ Icc (0 : ℝ) u, x ∈ Ioo (-1 : ℝ) 1 := by
    intro x hx
    exact ⟨by linarith [hx.1], hx.2.trans_lt hu.2⟩
  have hmono : MonotoneOn topAtanhPadeGap (Icc (0 : ℝ) u) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 u)
    · intro x hx
      exact (hasDerivAt_topAtanhPadeGap (hdomain x hx)).continuousAt
        |>.continuousWithinAt
    · intro x hx
      have hxin := interior_subset hx
      exact (hasDerivAt_topAtanhPadeGap (hdomain x hxin)).hasDerivWithinAt
    · intro x hx
      exact topAtanhPadeGap_deriv_nonneg
        (hdomain x (interior_subset hx))
  have h0 := hmono (show (0 : ℝ) ∈ Icc 0 u from ⟨le_rfl, hu.1⟩)
    (show u ∈ Icc (0 : ℝ) u from ⟨hu.1, le_rfl⟩) hu.1
  have hgap0 : topAtanhPadeGap 0 = 0 := by
    simp [topAtanhPadeGap]
  rw [hgap0] at h0
  unfold topAtanhPadeGap at h0
  linarith

/-- The missing half of (M17): `-Q''(y) ≥ 1/(6y)`. -/
theorem lrCertificateQSecond_upper_six
    {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    lrCertificateQSecond y ≤ -1 / (6 * y) := by
  let z := Real.sqrt (1 - y)
  have hzPos : 0 < z := Real.sqrt_pos.2 (by linarith [hy.2])
  have hzLt : z < 1 := by
    simpa [z] using
      (Real.sqrt_lt_sqrt_iff (by linarith [hy.2] : 0 ≤ 1 - y)).2
        (by linarith [hy.1] : 1 - y < 1)
  have hzSq : z ^ 2 = 1 - y := by
    dsimp [z]
    exact Real.sq_sqrt (by linarith [hy.2])
  have hyNe : y ≠ 0 := hy.1.ne'
  have hzNe : z ≠ 0 := hzPos.ne'
  have hdenPos : 0 < 4 * z ^ 3 := by positivity
  have hart := artanh_le_cubicPade_unit
    (show z ∈ Ico (0 : ℝ) 1 from ⟨hzPos.le, hzLt⟩)
  have hpadeIdentity :
      z + z ^ 3 / (3 * (1 - z ^ 2)) =
        z * (3 - 2 * z ^ 2) / (3 * (1 - z ^ 2)) := by
    have hbase : 1 - z ^ 2 ≠ 0 := by nlinarith [hzSq, hy.1]
    field_simp [hbase]
    ring
  rw [hpadeIdentity] at hart
  rw [lrCertificateQSecond_eq hy]
  change (Real.artanh z - z / y) / (4 * z ^ 3) ≤ -1 / (6 * y)
  rw [div_le_iff₀ hdenPos]
  have hyEq : y = 1 - z ^ 2 := by linarith [hzSq]
  rw [hyEq]
  have hbasePos : 0 < 1 - z ^ 2 := by linarith [hzSq, hy.1]
  have hthreeBasePos : 0 < 3 * (1 - z ^ 2) :=
    mul_pos (by norm_num) hbasePos
  rw [le_div_iff₀ hthreeBasePos] at hart
  field_simp [hbasePos.ne', hzNe]
  nlinarith [hart]

/-- Manuscript (M17) in its positive-curvature form. -/
theorem lrCertificateQNegativeSecond_mem
    {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    -lrCertificateQSecond y ∈
      Set.Icc (1 / (6 * y)) (1 / (4 * y)) := by
  constructor
  · convert neg_le_neg (lrCertificateQSecond_upper_six hy) using 1 <;>
      ring
  · convert neg_le_neg (lrCertificateQSecond_lower hy) using 1 <;>
      ring

end CourtadeKumar
