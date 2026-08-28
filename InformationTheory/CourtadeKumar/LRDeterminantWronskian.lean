import InformationTheory.CourtadeKumar.LRDeterminantPositiveFactors
import InformationTheory.CourtadeKumar.LRLowShapeVSeries
import InformationTheory.CourtadeKumar.LRLowShapeUL1Bridge

/-!
# Coefficient Wronskian for the determinant proof

The coefficient Wronskian in the audited proof uses only positivity and
monotonicity of the radial coefficients, together with the bound
`c_j ≤ 1/j`.  This file first isolates that finite coefficient argument in
a reusable kernel-checked theorem.
-/

open scoped BigOperators

namespace CourtadeKumar

/-- The coefficient of `R^n` in `H F' - lambda H' F`, written in the
indexing used by the audited determinant proof. -/
noncomputable def lrWronskianCoefficient
    (lambda a : ℝ) (c f : ℕ → ℝ) (n : ℕ) : ℝ :=
  a * ((n + 1 : ℕ) : ℝ) * f (n + 1) +
    ∑ i ∈ Finset.range n,
      (((n + 1 : ℕ) : ℝ) - (lambda + 1) * ((i + 1 : ℕ) : ℝ)) *
        c (i + 1) * f (n - i)

/-- Abstract finite coefficient estimate behind the manuscript's
coefficient Wronskian lemma. -/
theorem lrWronskianCoefficient_nonnegative
    {lambda a : ℝ} {c f : ℕ → ℝ}
    (hlambda : 0 ≤ lambda) (ha : lambda ≤ a)
    (hfNonnegative : ∀ m, 1 ≤ m → 0 ≤ f m)
    (hfMonotone : ∀ m k, 1 ≤ m → m ≤ k → f m ≤ f k)
    (hcNonnegative : ∀ j, 1 ≤ j → 0 ≤ c j)
    (hcScaled : ∀ j : ℕ, 1 ≤ j → (j : ℝ) * c j ≤ 1)
    (n : ℕ) :
    0 ≤ lrWronskianCoefficient lambda a c f n := by
  have hterm : ∀ i ∈ Finset.range n,
      -lambda * f (n + 1) ≤
        (((n + 1 : ℕ) : ℝ) -
            (lambda + 1) * ((i + 1 : ℕ) : ℝ)) *
          c (i + 1) * f (n - i) := by
    intro i hi
    have hiLt : i < n := Finset.mem_range.mp hi
    have hjPos : 1 ≤ i + 1 := by omega
    have hc0 := hcNonnegative (i + 1) hjPos
    have hc1 := hcScaled (i + 1) hjPos
    let q : ℝ := ((n + 1 : ℕ) : ℝ) -
      (lambda + 1) * ((i + 1 : ℕ) : ℝ)
    have hqLower : -lambda * ((i + 1 : ℕ) : ℝ) ≤ q := by
      dsimp [q]
      have hiCast : ((i : ℕ) : ℝ) < n := by exact_mod_cast hiLt
      norm_num only [Nat.cast_add, Nat.cast_one]
      nlinarith
    have hscaledLower : -lambda ≤
        (-lambda * ((i + 1 : ℕ) : ℝ)) * c (i + 1) := by
      have hmul := mul_le_mul_of_nonneg_left hc1 hlambda
      nlinarith
    have hqcLower : -lambda ≤ q * c (i + 1) := by
      exact hscaledLower.trans
        (mul_le_mul_of_nonneg_right hqLower hc0)
    by_cases hqc : 0 ≤ q * c (i + 1)
    · have hright : 0 ≤ q * c (i + 1) * f (n - i) :=
        mul_nonneg hqc (hfNonnegative _ (by omega))
      have hleft : -lambda * f (n + 1) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hlambda)
          (hfNonnegative _ (by omega))
      simpa [q, mul_assoc] using hleft.trans hright
    · have hqcNonpositive : q * c (i + 1) ≤ 0 := le_of_not_ge hqc
      have hfLe : f (n - i) ≤ f (n + 1) := by
        exact hfMonotone _ _ (by omega) (by omega)
      have hreverse : q * c (i + 1) * f (n + 1) ≤
          q * c (i + 1) * f (n - i) :=
        mul_le_mul_of_nonpos_left hfLe hqcNonpositive
      have hlower := mul_le_mul_of_nonneg_right hqcLower
        (hfNonnegative (n + 1) (by omega))
      simpa [q, mul_assoc] using hlower.trans hreverse
  have hsum :
      ∑ i ∈ Finset.range n, -lambda * f (n + 1) ≤
        ∑ i ∈ Finset.range n,
          (((n + 1 : ℕ) : ℝ) -
              (lambda + 1) * ((i + 1 : ℕ) : ℝ)) *
            c (i + 1) * f (n - i) :=
    Finset.sum_le_sum hterm
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  have hhead : lambda * ((n + 1 : ℕ) : ℝ) * f (n + 1) ≤
      a * ((n + 1 : ℕ) : ℝ) * f (n + 1) := by
    have hscale : 0 ≤ ((n + 1 : ℕ) : ℝ) * f (n + 1) :=
      mul_nonneg (Nat.cast_nonneg _) (hfNonnegative _ (by omega))
    simpa [mul_assoc] using mul_le_mul_of_nonneg_right ha hscale
  have hmargin : 0 ≤ lambda * f (n + 1) :=
    mul_nonneg hlambda (hfNonnegative _ (by omega))
  unfold lrWronskianCoefficient
  norm_num only [Nat.cast_add, Nat.cast_one] at hsum hhead ⊢
  nlinarith

/-- The radial coefficients `c_j=4b_j` of `H_d`. -/
noncomputable def lrDeterminantRadialC (j : ℕ) : ℝ :=
  4 * lrLowB j

/-- The radial coefficients `f_j` of the gap flow `F`. -/
noncomputable def lrDeterminantRadialF
    (v t : ℝ) (j : ℕ) : ℝ :=
  lrGShape t v + lrLowP v (t ^ 2) j -
    4 / (1 + v) * lrLowB j

theorem lrDeterminantRadialC_nonnegative (j : ℕ) :
    0 ≤ lrDeterminantRadialC j := by
  unfold lrDeterminantRadialC
  exact mul_nonneg (by norm_num) (lrLowB_pos j).le

theorem lrDeterminantRadialC_scaled_le_one
    {j : ℕ} (hj : 1 ≤ j) :
    (j : ℝ) * lrDeterminantRadialC j ≤ 1 := by
  have h := lrLowB_scaled_le_quarter hj
  unfold lrDeterminantRadialC
  nlinarith

theorem lrDeterminantRadialF_succ_sub
    {v t : ℝ} (hv : v ∈ Set.Ioo (0 : ℝ) 1)
    (ht : t ∈ Set.Ioo (0 : ℝ) 1) (j : ℕ) :
    lrDeterminantRadialF v t (j + 1) -
        lrDeterminantRadialF v t j =
      lrLowA (j + 1) *
        (4 / (1 + v) - lrLowT v (t ^ 2) (j + 1)) := by
  have hvClosed : v ∈ Set.Icc (0 : ℝ) 1 := ⟨hv.1.le, hv.2.le⟩
  have htClosed : t ^ 2 ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · positivity
    · nlinarith [mul_nonneg ht.1.le (sub_nonneg.mpr ht.2.le)]
  have hp := lrLowP_recursion hvClosed htClosed j
  have hb := lrLowB_recursion j
  unfold lrDeterminantRadialF
  rw [hp, hb]
  ring

theorem lrDeterminantRadialF_monotone
    {v t : ℝ} (hv : v ∈ Set.Ioo (0 : ℝ) 1)
    (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    Monotone (lrDeterminantRadialF v t) := by
  apply monotone_nat_of_le_succ
  intro j
  have hvClosed : v ∈ Set.Icc (0 : ℝ) 1 := ⟨hv.1.le, hv.2.le⟩
  have htClosed : t ^ 2 ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · positivity
    · nlinarith [mul_nonneg ht.1.le (sub_nonneg.mpr ht.2.le)]
  have hT := lrLowT_le_two hvClosed htClosed (j + 1)
  have hden : 0 < 1 + v := by linarith [hv.1]
  have hfour : 2 ≤ 4 / (1 + v) := by
    rw [le_div_iff₀ hden]
    nlinarith [hv.2]
  have hdiff := lrDeterminantRadialF_succ_sub hv ht j
  have ha := (lrLowA_pos (by omega : 1 ≤ j + 1)).le
  nlinarith [mul_nonneg ha (sub_nonneg.mpr (hT.trans hfour))]

theorem lrDeterminantRadialF_one_nonnegative
    {v t : ℝ} (hv : v ∈ Set.Ioo (0 : ℝ) 1)
    (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    0 ≤ lrDeterminantRadialF v t 1 := by
  have hvIoc : v ∈ Set.Ioc (0 : ℝ) 1 := ⟨hv.1, hv.2.le⟩
  have htIoc : t ∈ Set.Ioc (0 : ℝ) 1 := ⟨ht.1, ht.2.le⟩
  have hshape := lrGShape_add_p_one hv htIoc
  have hG := lrG_ge_two_log hvIoc
  have hx : t ^ 2 ≤ 1 := by nlinarith [ht.1, ht.2]
  have hden : 0 < 1 + v := by linarith [hv.1]
  have hlogHalf : 0 ≤ Real.log 2 - 1 / 2 := by
    linarith [Real.log_two_gt_d9]
  have hfirst : t ^ 2 * (1 + v) / 2 ≤ (1 + v) / 2 := by
    have hfactor : 0 ≤ 1 + v := by linarith [hv.1]
    have hmul : t ^ 2 * (1 + v) ≤ 1 * (1 + v) :=
      mul_le_mul_of_nonneg_right hx hfactor
    exact div_le_div_of_nonneg_right (by simpa using hmul) (by norm_num)
  have hlogUpper : 4 * Real.log 2 ≤ 3 := by
    linarith [lr_log_two_lt_three_quarters]
  have hproduct : 0 ≤
      (1 - v) * (3 + v - 4 * Real.log 2) :=
    mul_nonneg (sub_nonneg.mpr hv.2.le) (by nlinarith [hv.1])
  have hconvex :
      (1 + v) / 2 + 4 / (1 + v) * (Real.log 2 - 1 / 2) ≤
        2 * Real.log 2 := by
    refine le_of_mul_le_mul_right ?_ hden
    field_simp [hden.ne']
    nlinarith
  have hcost :
      t ^ 2 * (1 + v) / 2 +
          4 / (1 + v) * (Real.log 2 - 1 / 2) ≤
        2 * Real.log 2 := by
    linarith
  unfold lrDeterminantRadialF
  rw [hshape]
  norm_num [lrLowA, lrLowT, lrLowB]
  nlinarith

theorem lrDeterminantRadialF_nonnegative
    {v t : ℝ} (hv : v ∈ Set.Ioo (0 : ℝ) 1)
    (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    {j : ℕ} (hj : 1 ≤ j) :
    0 ≤ lrDeterminantRadialF v t j := by
  exact (lrDeterminantRadialF_one_nonnegative hv ht).trans
    (lrDeterminantRadialF_monotone hv ht hj)

theorem lrLowHalfSlopeBase_ge_four_log_two
    {v : ℝ} (hv : v ∈ Set.Ioo (0 : ℝ) 1) :
    4 * Real.log 2 ≤ lrLowHalfSlopeBase v := by
  let p := lrFlowM v / 2
  have hM := lrFlowM_mem_Ioc
    (show v ∈ Set.Ioc (0 : ℝ) 1 from ⟨hv.1, hv.2.le⟩)
  have hp : p ∈ Set.Ioc (0 : ℝ) (1 / 4 : ℝ) := by
    dsimp [p]
    constructor
    · exact div_pos hM.1 (by norm_num)
    · linarith [hM.2]
  have honeMinus : 0 < 1 - p := by linarith [hp.2]
  have hlog := Real.log_le_sub_one_of_pos honeMinus
  have hpLog : p ≤ -Real.log (1 - p) := by linarith
  have hlogTwo : Real.log 2 ≤ 1 :=
    lr_log_two_lt_three_quarters.le.trans (by norm_num)
  have hfourLog : 4 * Real.log 2 ≤ 4 := by nlinarith
  have hpSq : 0 ≤ p ^ 2 := sq_nonneg p
  have hscale := mul_le_mul_of_nonneg_right hfourLog hpSq
  have hquarter : 4 * p ^ 2 ≤ p := by
    nlinarith [mul_nonneg hp.1.le (sub_nonneg.mpr hp.2)]
  unfold lrLowHalfSlopeBase
  change 4 * Real.log 2 ≤ -Real.log (1 - p) / p ^ 2
  rw [le_div_iff₀ (sq_pos_of_pos hp.1)]
  exact hscale.trans (hquarter.trans hpLog)

/-- Every coefficient in the audited Wronskian expansion is nonnegative. -/
theorem lrDeterminantWronskianCoefficient_nonnegative
    {v t a : ℝ} (hv : v ∈ Set.Ioo (0 : ℝ) 1)
    (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (ha : 4 * Real.log 2 ≤ a) (n : ℕ) :
    0 ≤ lrWronskianCoefficient (4 * Real.log 2) a
      lrDeterminantRadialC (lrDeterminantRadialF v t) n := by
  apply lrWronskianCoefficient_nonnegative
  · exact mul_nonneg (by norm_num) (Real.log_pos (by norm_num)).le
  · exact ha
  · intro m hm
    exact lrDeterminantRadialF_nonnegative hv ht hm
  · intro m k hm hmk
    exact lrDeterminantRadialF_monotone hv ht hmk
  · intro j _
    exact lrDeterminantRadialC_nonnegative j
  · intro j hj
    exact lrDeterminantRadialC_scaled_le_one hj

/-- The concrete radial coefficient in the determinant Wronskian is
nonnegative for every order. -/
theorem lrDeterminantConcreteWronskianCoefficient_nonnegative
    {v t : ℝ} (hv : v ∈ Set.Ioo (0 : ℝ) 1)
    (ht : t ∈ Set.Ioo (0 : ℝ) 1) (n : ℕ) :
    0 ≤ lrWronskianCoefficient (4 * Real.log 2)
      (lrLowHalfSlopeBase v) lrDeterminantRadialC
      (lrDeterminantRadialF v t) n :=
  lrDeterminantWronskianCoefficient_nonnegative hv ht
    (lrLowHalfSlopeBase_ge_four_log_two hv) n

end CourtadeKumar
