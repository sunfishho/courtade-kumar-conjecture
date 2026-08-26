import InformationTheory.CourtadeKumar.LRLowShapeWeightedTails

/-! Assembly of the non-numerical part of the low-shape midpoint
certificate `(U)`. -/

open Set

namespace CourtadeKumar

noncomputable def lrLowEta (v x : ℝ) (j : ℕ) : ℝ :=
  lrLowP v x j - 2 * lrFlowM v * x * lrLowB j

noncomputable def lrLowTailH (v : ℝ) : ℝ :=
  4 / (1 + v) + 2 * lrFlowM v

noncomputable def lrLowR (v x G : ℝ) (j : ℕ) : ℝ :=
  G + lrLowP v x j - lrLowTailH v * lrLowB j

lemma lrLowTailH_ge_three
    {v : ℝ} (hv : v ∈ Icc (0 : ℝ) 1) :
    3 ≤ lrLowTailH v := by
  have hden : 0 < 1 + v := by linarith [hv.1]
  unfold lrLowTailH lrFlowM
  have heq : 4 / (1 + v) + 2 * (v / (1 + v)) =
      (4 + 2 * v) / (1 + v) := by
    field_simp [hden.ne']
  rw [heq, le_div_iff₀ hden]
  nlinarith [hv.2]

lemma lrLowR_step
    {v x G : ℝ} (hv : v ∈ Icc (0 : ℝ) 1)
    (hx : x ∈ Icc (0 : ℝ) 1) (j : ℕ) :
    lrLowR v x G j ≤ lrLowR v x G (j + 1) := by
  have hpRec := lrLowP_recursion hv hx j
  have hbRec := lrLowB_recursion j
  have ha := (lrLowA_pos (by omega : 1 ≤ j + 1)).le
  have hT := lrLowT_le_two hv hx (j + 1)
  have hh := lrLowTailH_ge_three hv
  unfold lrLowR
  have hTh : lrLowT v x (j + 1) ≤ lrLowTailH v :=
    hT.trans (by linarith [hh])
  nlinarith [mul_nonneg ha (sub_nonneg.mpr hTh)]

theorem lrLowR_monotone
    {v x G : ℝ} (hv : v ∈ Icc (0 : ℝ) 1)
    (hx : x ∈ Icc (0 : ℝ) 1) :
    Monotone (lrLowR v x G) := by
  exact monotone_nat_of_le_succ (lrLowR_step hv hx)

lemma lrLowEta_comparison
    {v x : ℝ} (hv : v ∈ Icc (0 : ℝ) 1)
    (hx : x ∈ Icc (0 : ℝ) 1) {j n : ℕ} (hjn : j ≤ n) :
    lrLowB j / lrLowB n * lrLowEta v x n ≤ lrLowEta v x j := by
  simpa [lrLowEta, mul_assoc] using
    (lrLowEta_tail_average hv hx (d := 2 * lrFlowM v * x) hjn)

/-- Once the two exact scalar certificates are known, every sign-explicit
`U` coefficient is nonnegative.  All infinite-tail and `Kₙ` estimates have
already been discharged here. -/
theorem lrLowU_actual_nonneg_of_two_scalars
    {v t G : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1)
    (ht : t ∈ Ioo (0 : ℝ) 1) (n : ℕ)
    (hfirst : 0 ≤
      lrLowR v (t ^ 2) G n +
        2 * lrFlowBeta v * lrLowEta v (t ^ 2) n)
    (hsecond : 0 ≤
      lrLowH (v ^ 2 * t ^ 2) n * lrLowR v (t ^ 2) G n +
        2 * (n : ℝ) * (lrFlowBeta v + lrL (v * t)) *
          lrLowEta v (t ^ 2) n) :
    0 ≤ lrLowUSignExplicit (lrFlowBeta v) (v ^ 2 * t ^ 2)
      (lrLowEta v (t ^ 2)) (lrLowR v (t ^ 2) G) n := by
  have hvClosed : v ∈ Icc (0 : ℝ) 1 := ⟨hv.1.le, hv.2.le⟩
  have hxClosed : t ^ 2 ∈ Icc (0 : ℝ) 1 := by
    constructor
    · positivity
    · nlinarith [mul_nonneg ht.1.le (sub_nonneg.mpr ht.2.le)]
  have hxi : v ^ 2 * t ^ 2 ∈ Icc (0 : ℝ) 1 := by
    have hvSq : v ^ 2 ≤ 1 := by
      nlinarith [mul_nonneg hv.1.le (sub_nonneg.mpr hv.2.le)]
    constructor
    · positivity
    · calc
        v ^ 2 * t ^ 2 ≤ 1 * t ^ 2 :=
          mul_le_mul_of_nonneg_right hvSq (sq_nonneg t)
        _ ≤ 1 := by simpa using hxClosed.2
  have hK := lrLowK_actual_bounds hv ht n
  apply lrLowUExplicit_nonneg_of_two_scalars hxi
  · intro k hk
    exact lrLowEta_comparison hvClosed hxClosed
      (show k + 1 ≤ n by
        have := Finset.mem_range.mp hk
        omega)
  · intro k hk
    exact lrLowR_monotone hvClosed hxClosed
      (show k + 1 ≤ n by
        have := Finset.mem_range.mp hk
        omega)
  · exact hK.1
  · exact hK.2
  · exact hfirst
  · exact hsecond

end CourtadeKumar
