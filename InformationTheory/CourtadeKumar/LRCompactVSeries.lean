import InformationTheory.CourtadeKumar.LRLowShapeTAlgebraCore
import InformationTheory.CourtadeKumar.LRLowShapeSeriesBounds
import InformationTheory.CourtadeKumar.LRLowShapeTailData
import InformationTheory.CourtadeKumar.LRNegativeChartBounds

/-!
# Cancellation-preserving series for the compact high-shape `V` certificate

This file begins the kernel-checked counterpart of equations (M45)--(M50)
in the audited proof.  The basic channel score

`w_n(R) = 1 - n R^(n-1) + (n-1) R^n`

is kept as a single polynomial object.  Its factorization below makes both
its sign and its endpoint orientation transparent, avoiding subtraction of
two separately rounded transcendental quantities in the eventual checker.
-/

open Set
open scoped BigOperators

namespace CourtadeKumar

/-- The exact score multiplying the `n`th positive entropy coefficient. -/
def lrCompactVScore (R : ℝ) (n : ℕ) : ℝ :=
  1 - (n : ℝ) * R ^ (n - 1) + ((n : ℝ) - 1) * R ^ n

/-- The positive factored form of `lrCompactVScore`. -/
def lrCompactVScoreFactored (R : ℝ) (n : ℕ) : ℝ :=
  (1 - R) ^ 2 *
    ∑ j ∈ Finset.range (n - 1), ((j : ℝ) + 1) * R ^ j

lemma lrCompactVScore_zero (R : ℝ) : lrCompactVScore R 0 = 0 := by
  simp [lrCompactVScore]

lemma lrCompactVScore_one (R : ℝ) : lrCompactVScore R 1 = 0 := by
  simp [lrCompactVScore]

lemma lrCompactVScore_succ_succ_sub
    (R : ℝ) (n : ℕ) :
    lrCompactVScore R (n + 2) - lrCompactVScore R (n + 1) =
      ((n : ℝ) + 1) * (1 - R) ^ 2 * R ^ n := by
  unfold lrCompactVScore
  norm_num only [Nat.cast_add, Nat.cast_ofNat]
  rw [show n + 2 - 1 = n + 1 by omega,
    show n + 1 - 1 = n by omega, pow_succ R (n + 1), pow_succ R n]
  ring

theorem lrCompactVScore_eq_factored
    (R : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    lrCompactVScore R n = lrCompactVScoreFactored R n := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  clear hn
  induction m with
  | zero => simp [lrCompactVScoreFactored, lrCompactVScore_one]
  | succ m ih =>
      rw [show 1 + m = m + 1 by omega] at ih
      have hstep := lrCompactVScore_succ_succ_sub R m
      unfold lrCompactVScoreFactored at ih ⊢
      rw [show m + 1 - 1 = m by omega] at ih
      rw [show 1 + (m + 1) - 1 = m + 1 by omega,
        Finset.sum_range_succ]
      rw [mul_add, ← ih]
      have hstep' :
          lrCompactVScore R (1 + (m + 1)) -
              lrCompactVScore R (m + 1) =
            ((m : ℝ) + 1) * (1 - R) ^ 2 * R ^ m := by
        simpa only [show 1 + (m + 1) = m + 2 by omega] using hstep
      nlinarith

theorem lrCompactVScore_nonneg
    {R : ℝ} (hR : 0 ≤ R) {n : ℕ} (hn : 1 ≤ n) :
    0 ≤ lrCompactVScore R n := by
  rw [lrCompactVScore_eq_factored R hn]
  exact mul_nonneg (sq_nonneg (1 - R)) <| Finset.sum_nonneg fun j _ ↦
    mul_nonneg (by positivity) (pow_nonneg hR j)

theorem lrCompactVScore_le_one
    {R : ℝ} (hR : R ∈ Icc (0 : ℝ) 1) {n : ℕ} (hn : 1 ≤ n) :
    lrCompactVScore R n ≤ 1 := by
  unfold lrCompactVScore
  have hpow : 0 ≤ R ^ (n - 1) := pow_nonneg hR.1 _
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hfactor : 0 ≤ (n : ℝ) - ((n : ℝ) - 1) * R := by
    nlinarith [mul_le_mul_of_nonneg_left hR.2 (sub_nonneg.mpr hnR)]
  rw [show R ^ n = R ^ (n - 1) * R by
    nth_rewrite 1 [show n = (n - 1) + 1 by omega]
    exact pow_succ R (n - 1)]
  nlinarith [mul_nonneg hpow hfactor]

theorem hasDerivAt_lrCompactVScore
    (R : ℝ) {n : ℕ} (hn : 2 ≤ n) :
    HasDerivAt (fun q ↦ lrCompactVScore q n)
      (-((n : ℝ) * ((n : ℝ) - 1) * (1 - R) * R ^ (n - 2))) R := by
  have hnOne : 1 ≤ n := hn.trans' (by omega)
  have hpowPred : HasDerivAt (fun q : ℝ ↦ q ^ (n - 1))
      (((n - 1 : ℕ) : ℝ) * R ^ (n - 2)) R := by
    convert (hasDerivAt_id R).pow (n - 1) using 1 <;>
      simp [id_eq, Nat.cast_sub hnOne,
        show n - 1 - 1 = n - 2 by omega]
  have hpow : HasDerivAt (fun q : ℝ ↦ q ^ n)
      (n * R ^ (n - 1)) R := by
    convert (hasDerivAt_id R).pow n using 1 <;> simp [id_eq]
  have hraw := (hasDerivAt_const R 1).sub
    (hpowPred.const_mul (n : ℝ)) |>.add
      (hpow.const_mul ((n : ℝ) - 1))
  unfold lrCompactVScore
  convert hraw using 1
  rw [Nat.cast_sub hnOne, Nat.cast_one,
    show n - 1 = (n - 2) + 1 by omega, pow_succ]
  ring

theorem lrCompactVScore_antitoneOn_unit
    {n : ℕ} (hn : 1 ≤ n) :
    AntitoneOn (fun R ↦ lrCompactVScore R n) (Icc (0 : ℝ) 1) := by
  by_cases hnOne : n = 1
  · subst n
    intro a _ b _ _
    simp [lrCompactVScore_one]
  have hnTwo : 2 ≤ n := by omega
  apply antitoneOn_of_deriv_nonpos (convex_Icc (0 : ℝ) 1)
  · intro R _
    exact (hasDerivAt_lrCompactVScore R hnTwo).continuousAt.continuousWithinAt
  · intro R _
    exact (hasDerivAt_lrCompactVScore R hnTwo).differentiableAt.differentiableWithinAt
  · intro R hR
    rw [(hasDerivAt_lrCompactVScore R hnTwo).deriv]
    rw [interior_Icc] at hR
    have hnNonneg : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hnPred : (0 : ℝ) ≤ (n : ℝ) - 1 := by
      have : (1 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    exact neg_nonpos.mpr <| mul_nonneg
      (mul_nonneg (mul_nonneg hnNonneg hnPred)
        (sub_nonneg.mpr hR.2.le))
      (pow_nonneg hR.1.le _)

theorem lrCompactVScore_monotone_index
    {R : ℝ} (hR : 0 ≤ R) : Monotone (lrCompactVScore R) := by
  apply monotone_nat_of_le_succ
  intro n
  rcases n with _ | n
  · simp [lrCompactVScore_zero, lrCompactVScore_one]
  · have hstep := lrCompactVScore_succ_succ_sub R n
    have hright :
        0 ≤ ((n : ℝ) + 1) * (1 - R) ^ 2 * R ^ n := by positivity
    linarith

/-- The shape monomial `T_n=x^n(1+v^(2n-1))` from (M45). -/
def lrCompactVT (v x : ℝ) (n : ℕ) : ℝ :=
  x ^ n * (1 + v ^ (2 * n - 1))

/-- The complementary coefficient `c_n=4/(1+v)-T_n`. -/
noncomputable def lrCompactVC (v x : ℝ) (n : ℕ) : ℝ :=
  4 / (1 + v) - lrCompactVT v x n

lemma lrCompactVT_nonneg
    {v x : ℝ} (hv : 0 ≤ v) (hx : 0 ≤ x) (n : ℕ) :
    0 ≤ lrCompactVT v x n := by
  exact mul_nonneg (pow_nonneg hx n)
    (add_nonneg zero_le_one (pow_nonneg hv _))

lemma lrCompactVT_mono_v
    {v₁ v₂ x : ℝ} (hv₁ : 0 ≤ v₁) (hv : v₁ ≤ v₂)
    (hx : 0 ≤ x) (n : ℕ) :
    lrCompactVT v₁ x n ≤ lrCompactVT v₂ x n := by
  unfold lrCompactVT
  gcongr

lemma lrCompactVT_mono_x
    {v x₁ x₂ : ℝ} (hv : 0 ≤ v) (hx₁ : 0 ≤ x₁)
    (hx : x₁ ≤ x₂) (n : ℕ) :
    lrCompactVT v x₁ n ≤ lrCompactVT v x₂ n := by
  unfold lrCompactVT
  gcongr

lemma lrCompactVC_antitone_v
    {v₁ v₂ x : ℝ} (hv₁ : 0 ≤ v₁) (hv : v₁ ≤ v₂)
    (hx : 0 ≤ x) (n : ℕ) :
    lrCompactVC v₂ x n ≤ lrCompactVC v₁ x n := by
  unfold lrCompactVC
  have hden₁ : 0 < 1 + v₁ := by linarith
  have hden₂ : 0 < 1 + v₂ := by linarith
  have hfrac : 4 / (1 + v₂) ≤ 4 / (1 + v₁) := by
    exact div_le_div_of_nonneg_left (by norm_num) hden₁ (by linarith)
  have hT := lrCompactVT_mono_v hv₁ hv hx n
  linarith

lemma lrCompactVC_antitone_x
    {v x₁ x₂ : ℝ} (hv : 0 ≤ v) (hx₁ : 0 ≤ x₁)
    (hx : x₁ ≤ x₂) (n : ℕ) :
    lrCompactVC v x₂ n ≤ lrCompactVC v x₁ n := by
  unfold lrCompactVC
  linarith [lrCompactVT_mono_x hv hx₁ hx n]

theorem lrCompactVC_nonneg
    {v x : ℝ} (hv : v ∈ Icc (0 : ℝ) 1)
    (hx : x ∈ Icc (0 : ℝ) 1) (n : ℕ) :
    0 ≤ lrCompactVC v x n := by
  rcases hv with ⟨hv₀, hv₁⟩
  rcases hx with ⟨hx₀, hx₁⟩
  have hden : 0 < 1 + v := by linarith
  have hfrac : (2 : ℝ) ≤ 4 / (1 + v) := by
    rw [le_div_iff₀ hden]
    linarith
  have hxpow : x ^ n ≤ 1 := pow_le_one₀ hx₀ hx₁
  have hvpow : v ^ (2 * n - 1) ≤ 1 := pow_le_one₀ hv₀ hv₁
  have hT : lrCompactVT v x n ≤ 2 := by
    unfold lrCompactVT
    have hsumNonneg : 0 ≤ 1 + v ^ (2 * n - 1) :=
      add_nonneg zero_le_one (pow_nonneg hv₀ _)
    calc
      x ^ n * (1 + v ^ (2 * n - 1)) ≤
          1 * (1 + v ^ (2 * n - 1)) :=
        mul_le_mul_of_nonneg_right hxpow hsumNonneg
      _ ≤ 1 * 2 := mul_le_mul_of_nonneg_left (by linarith) zero_le_one
      _ = 2 := one_mul 2
  unfold lrCompactVC
  linarith

/-- The nonnegative residual `f₀` in the cancellation series (M45). -/
noncomputable def lrCompactVFZero (v : ℝ) : ℝ :=
  lrG v - 4 * Real.log 2 / (1 + v)

theorem hasDerivAt_lrCompactVFZero
    {v : ℝ} (hv : 0 < v) :
    HasDerivAt lrCompactVFZero
      (4 * Real.log 2 / (1 + v) ^ 2 - Real.log (1 + v) / v ^ 2) v := by
  have hden : HasDerivAt (fun q : ℝ ↦ 1 + q) 1 v := by
    convert (hasDerivAt_const v 1).add (hasDerivAt_id v) using 1 <;> ring
  have hdenNe : 1 + v ≠ 0 := by linarith
  have hquot := (hasDerivAt_const v (4 * Real.log 2)).div hden hdenNe
  unfold lrCompactVFZero
  convert (hasDerivAt_lrG hv).sub hquot using 1
  field_simp [hdenNe]
  ring

lemma lrCompactVFZero_deriv_nonpos
    {v : ℝ} (hv : v ∈ Ioc (0 : ℝ) 1) :
    deriv lrCompactVFZero v ≤ 0 := by
  rw [(hasDerivAt_lrCompactVFZero hv.1).deriv]
  have hvPos : 0 < v := hv.1
  have hfactor := lrQ₀LogFactor_ge_four_log_two hv
  have hvSq : 0 < v ^ 2 := sq_pos_of_pos hv.1
  have hdenSq : 0 < (1 + v) ^ 2 :=
    sq_pos_of_pos (by linarith [hvPos] : 0 < 1 + v)
  have hscaled : 4 * Real.log 2 * v ^ 2 ≤
      Real.log (1 + v) * (1 + v) ^ 2 := by
    unfold lrQ₀LogFactor at hfactor
    rw [le_div_iff₀ hvSq] at hfactor
    simpa [mul_comm, mul_left_comm, mul_assoc] using hfactor
  have hquot : 4 * Real.log 2 / (1 + v) ^ 2 ≤
      Real.log (1 + v) / v ^ 2 := by
    rw [div_le_div_iff₀ hdenSq hvSq]
    simpa [mul_comm] using hscaled
  linarith

theorem lrCompactVFZero_nonneg
    {v : ℝ} (hv : v ∈ Ioc (0 : ℝ) 1) :
    0 ≤ lrCompactVFZero v := by
  have hanti : AntitoneOn lrCompactVFZero (Icc v 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc v 1)
    · intro q hq
      exact (hasDerivAt_lrCompactVFZero (hv.1.trans_le hq.1)).continuousAt
        |>.continuousWithinAt
    · intro q hq
      rw [interior_Icc] at hq
      exact (hasDerivAt_lrCompactVFZero (hv.1.trans hq.1)).differentiableAt
        |>.differentiableWithinAt
    · intro q hq
      rw [interior_Icc] at hq
      exact lrCompactVFZero_deriv_nonpos
        ⟨hv.1.trans hq.1, hq.2.le⟩
  have hend : lrCompactVFZero 1 = 0 := by
    unfold lrCompactVFZero lrG
    norm_num
    ring
  have h := hanti ⟨le_rfl, hv.2⟩ ⟨hv.2, le_rfl⟩ hv.2
  rw [hend] at h
  exact h

/-- Positive summand in the cancellation series for `P_W`. -/
noncomputable def lrCompactVPWTerm
    (R v x : ℝ) (n : ℕ) : ℝ :=
  lrLowA n * lrCompactVScore R n * lrCompactVT v x n

/-- Positive summand in the cancellation series for `Ψ`. -/
noncomputable def lrCompactVPsiTerm
    (R v x : ℝ) (n : ℕ) : ℝ :=
  lrLowA n * lrCompactVC v x n * (1 - lrCompactVScore R n)

theorem lrCompactVPWTerm_nonneg
    {R v x : ℝ} (hR : 0 ≤ R) (hv : 0 ≤ v) (hx : 0 ≤ x)
    {n : ℕ} (hn : 1 ≤ n) :
    0 ≤ lrCompactVPWTerm R v x n := by
  unfold lrCompactVPWTerm
  exact mul_nonneg
    (mul_nonneg (lrLowA_pos hn).le (lrCompactVScore_nonneg hR hn))
    (lrCompactVT_nonneg hv hx n)

theorem lrCompactVPsiTerm_nonneg
    {R v x : ℝ} (hR : R ∈ Icc (0 : ℝ) 1)
    (hv : v ∈ Icc (0 : ℝ) 1) (hx : x ∈ Icc (0 : ℝ) 1)
    {n : ℕ} (hn : 1 ≤ n) :
    0 ≤ lrCompactVPsiTerm R v x n := by
  unfold lrCompactVPsiTerm
  exact mul_nonneg
    (mul_nonneg (lrLowA_pos hn).le (lrCompactVC_nonneg hv hx n))
    (sub_nonneg.mpr (lrCompactVScore_le_one hR hn))

noncomputable def lrCompactVPWHead
    (N : ℕ) (R v x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range N, lrCompactVPWTerm R v x (j + 1)

noncomputable def lrCompactVPsiHead
    (N : ℕ) (R v x : ℝ) : ℝ :=
  lrCompactVFZero v +
    ∑ j ∈ Finset.range N, lrCompactVPsiTerm R v x (j + 1)

theorem lrCompactVPWHead_le_of_hasSum
    {R v x PW : ℝ} (hR : 0 ≤ R) (hv : 0 ≤ v) (hx : 0 ≤ x)
    (hseries : HasSum
      (fun j : ℕ ↦ lrCompactVPWTerm R v x (j + 1)) PW)
    (N : ℕ) :
    lrCompactVPWHead N R v x ≤ PW := by
  rw [← hseries.tsum_eq]
  unfold lrCompactVPWHead
  exact hseries.summable.sum_le_tsum (Finset.range N)
    (fun j _ ↦ lrCompactVPWTerm_nonneg hR hv hx (by omega))

theorem lrCompactVPsiHead_le_of_hasSum
    {R v x Psi : ℝ} (hR : R ∈ Icc (0 : ℝ) 1)
    (hv : v ∈ Ioc (0 : ℝ) 1) (hx : x ∈ Icc (0 : ℝ) 1)
    (hseries : HasSum
      (fun j : ℕ ↦ lrCompactVPsiTerm R v x (j + 1))
      (Psi - lrCompactVFZero v)) (N : ℕ) :
    lrCompactVPsiHead N R v x ≤ Psi := by
  have hvClosed : v ∈ Icc (0 : ℝ) 1 := ⟨hv.1.le, hv.2⟩
  have htail :
      ∑ j ∈ Finset.range N, lrCompactVPsiTerm R v x (j + 1) ≤
        Psi - lrCompactVFZero v := by
    rw [← hseries.tsum_eq]
    exact hseries.summable.sum_le_tsum (Finset.range N)
      (fun j _ ↦ lrCompactVPsiTerm_nonneg hR hvClosed hx (by omega))
  unfold lrCompactVPsiHead
  linarith

/-- The positive `n`th score term for a single channel kernel. -/
noncomputable def lrCompactVWTerm
    (R x : ℝ) (n : ℕ) : ℝ :=
  lrLowA n * lrCompactVScore R n * x ^ n

/-- Exact score series for `W_R(z)`.  It is derived from the three positive
series in the analytic definition, then collected coefficientwise before
any interval rounding occurs. -/
theorem lrCompactVWTerm_hasSum
    {R z : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1)
    (hz : z ∈ Ioo (0 : ℝ) 1) :
    HasSum (fun j : ℕ ↦ lrCompactVWTerm R (z ^ 2) (j + 1))
      (lrWKernel R z) := by
  have hx : z ^ 2 ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · exact sq_pos_of_pos hz.1
    · nlinarith [sq_nonneg z, mul_pos hz.1 (sub_pos.mpr hz.2)]
  have hRx : R * z ^ 2 ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · exact mul_pos hR.1 hx.1
    · calc
        R * z ^ 2 < 1 * z ^ 2 := mul_lt_mul_of_pos_right hR.2 hx.1
        _ = z ^ 2 := one_mul _
        _ < 1 := hx.2
  have hPhiX := topPhi_sqrt_hasSum hx
  have hPhiRx := topPhi_sqrt_hasSum hRx
  have hPsiRx := topPsiDeriv_hasSum hRx
  have hcomb := (hPhiX.sub hPhiRx).sub
    (hPsiRx.mul_left ((1 - R) * z ^ 2))
  have hkernel := lrWKernel_eq_Psi hR hz.1
  convert hcomb using 1
  · funext j
    unfold lrCompactVWTerm lrCompactVScore lrLowA
    norm_num only [Nat.cast_add, Nat.cast_one]
    rw [show j + 1 - 1 = j by omega, mul_pow]
    have hj : (0 : ℝ) < (j : ℝ) + 1 := by positivity
    have hj₀ : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have hodd : (0 : ℝ) < 2 * ((j : ℝ) + 1) - 1 := by linarith
    field_simp [hj.ne', hodd.ne']
    rw [pow_succ]
    ring
  · rw [hkernel, Real.sqrt_sq_eq_abs, abs_of_pos hz.1]

/-- The corresponding exact series for the two-ray kernel `P_W`. -/
theorem lrCompactVPWTerm_hasSum
    {R v t : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1)
    (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasSum (fun j : ℕ ↦ lrCompactVPWTerm R v (t ^ 2) (j + 1))
      (lrFlowPW R v t) := by
  have hvt : v * t ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · exact mul_pos hv.1 ht.1
    · calc
        v * t < 1 * t := mul_lt_mul_of_pos_right hv.2 ht.1
        _ < 1 := by simpa using ht.2
  have htSeries := lrCompactVWTerm_hasSum hR ht
  have hvtSeries := (lrCompactVWTerm_hasSum hR hvt).mul_left (1 / v)
  unfold lrFlowPW
  convert htSeries.add hvtSeries using 1
  funext j
  unfold lrCompactVPWTerm lrCompactVWTerm lrCompactVT
  rw [mul_pow v t 2, mul_pow (v ^ 2) (t ^ 2), ← pow_mul]
  rw [← pow_mul v 2 (j + 1)]
  have hvNe : v ≠ 0 := hv.1.ne'
  have hindex : 2 * (j + 1) - 1 + 1 = 2 * (j + 1) := by omega
  rw [show v ^ (2 * (j + 1)) =
      v ^ (2 * (j + 1) - 1) * v by
    rw [← hindex]
    exact pow_succ v (2 * (j + 1) - 1)]
  field_simp [hvNe]
  ring

/-- Finite correction in the tail-enhanced lower bound for `P_W`. -/
noncomputable def lrCompactVPWError
    (N : ℕ) (R v x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range N,
    lrLowA (j + 1) *
      (lrCompactVScore R (N + 1) - lrCompactVScore R (j + 1)) *
      lrCompactVT v x (j + 1)

/-- Tail-enhanced lower bound `w_{N+1} P₀-E_N` from (M47). -/
noncomputable def lrCompactVPWLower
    (N : ℕ) (R v t : ℝ) : ℝ :=
  lrCompactVScore R (N + 1) *
      (topPhi t + topPhi (v * t) / v) -
    lrCompactVPWError N R v (t ^ 2)

/-- Endpoint version of the score series, needed for `W_R(1)`. -/
theorem lrCompactVWOneTerm_hasSum
    {R : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1) :
    HasSum (fun j : ℕ ↦ lrCompactVWTerm R 1 (j + 1))
      (lrWKernel R 1) := by
  have hPhiOne := top_hasSum_phiCoefficients
  have hPhiR := topPhi_sqrt_hasSum hR
  have hPsiR := topPsiDeriv_hasSum hR
  have hcomb := (hPhiOne.sub hPhiR).sub
    (hPsiR.mul_left (1 - R))
  have hkernel := lrWKernel_eq_Psi hR (by norm_num : (0 : ℝ) < 1)
  convert hcomb using 1
  · funext j
    unfold lrCompactVWTerm lrCompactVScore lrLowA
    norm_num only [Nat.cast_add, Nat.cast_one, one_pow]
    rw [show j + 1 - 1 = j by omega]
    have hj : (0 : ℝ) < (j : ℝ) + 1 := by positivity
    have hj₀ : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have hodd : (0 : ℝ) < 2 * ((j : ℝ) + 1) - 1 := by linarith
    field_simp [hj.ne', hodd.ne']
    rw [pow_succ]
    ring
  · rw [hkernel]
    norm_num [topPhi_one]

/-- Exact positive-coefficient series for
`Phi(t) + Phi(vt)/v`. -/
theorem lrCompactVT_hasSum
    {v t : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1)
    (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasSum (fun j : ℕ ↦
      lrLowA (j + 1) * lrCompactVT v (t ^ 2) (j + 1))
      (topPhi t + topPhi (v * t) / v) := by
  have htSq : t ^ 2 ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · exact sq_pos_of_pos ht.1
    · nlinarith [sq_nonneg t, mul_pos ht.1 (sub_pos.mpr ht.2)]
  have hvt : v * t ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · exact mul_pos hv.1 ht.1
    · calc
        v * t < 1 * t := mul_lt_mul_of_pos_right hv.2 ht.1
        _ < 1 := by simpa using ht.2
  have hvtSq : (v * t) ^ 2 ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · exact sq_pos_of_pos hvt.1
    · nlinarith [sq_nonneg (v * t), mul_pos hvt.1 (sub_pos.mpr hvt.2)]
  have htSeries := topPhi_sqrt_hasSum htSq
  have hvtSeries := (topPhi_sqrt_hasSum hvtSq).mul_left (1 / v)
  have hvNe : v ≠ 0 := hv.1.ne'
  convert htSeries.add hvtSeries using 1
  · funext j
    unfold lrLowA lrCompactVT
    norm_num only [Nat.cast_add, Nat.cast_one]
    rw [mul_pow v t 2, mul_pow (v ^ 2) (t ^ 2), ← pow_mul,
      ← pow_mul v 2 (j + 1)]
    have hindex : 2 * (j + 1) - 1 + 1 = 2 * (j + 1) := by omega
    rw [show v ^ (2 * (j + 1)) =
        v ^ (2 * (j + 1) - 1) * v by
      rw [← hindex]
      exact pow_succ v (2 * (j + 1) - 1)]
    field_simp [hvNe]
  · rw [Real.sqrt_sq_eq_abs, abs_of_pos ht.1,
      Real.sqrt_sq_eq_abs, abs_of_pos hvt.1]
    ring

/-- Exact cancellation series for `Ψ=lrFlowC`, equation (M46). -/
theorem lrCompactVPsiTerm_hasSum
    {R v t : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1)
    (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasSum (fun j : ℕ ↦ lrCompactVPsiTerm R v (t ^ 2) (j + 1))
      (lrFlowC R v t - lrCompactVFZero v) := by
  have hA : HasSum (fun j : ℕ ↦ lrLowA (j + 1)) (Real.log 2) := by
    convert top_hasSum_phiCoefficients using 1
    funext j
    unfold lrLowA
    norm_num only [Nat.cast_add, Nat.cast_one]
  have hT := lrCompactVT_hasSum hv ht
  have hW := lrCompactVWOneTerm_hasSum hR
  have hPW := lrCompactVPWTerm_hasSum hR hv ht
  let factor : ℝ := 4 / (1 + v)
  have hcomb := ((hA.mul_left factor).sub hT).sub
    (hW.mul_left factor) |>.add hPW
  have hden : 1 + v ≠ 0 := by linarith [hv.1]
  convert hcomb using 1
  · funext j
    unfold lrCompactVPsiTerm lrCompactVC lrCompactVPWTerm
      lrCompactVWTerm factor
    ring
  · unfold lrFlowC lrCompactVFZero factor
    unfold lrGShape
    field_simp [hden]
    ring

theorem lrCompactVPWLower_le_lrFlowPW
    {R v t : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1)
    (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1)
    (N : ℕ) :
    lrCompactVPWLower N R v t ≤ lrFlowPW R v t := by
  let w := lrCompactVScore R (N + 1)
  let P₀ := topPhi t + topPhi (v * t) / v
  let diff : ℕ → ℝ := fun j ↦
    lrCompactVPWTerm R v (t ^ 2) (j + 1) -
      w * (lrLowA (j + 1) * lrCompactVT v (t ^ 2) (j + 1))
  have hdiff : HasSum diff (lrFlowPW R v t - w * P₀) := by
    exact (lrCompactVPWTerm_hasSum hR hv ht).sub
      ((lrCompactVT_hasSum hv ht).mul_left w)
  have htail := (hasSum_nat_add_iff' N).2 hdiff
  have htailNonneg : 0 ≤
      (lrFlowPW R v t - w * P₀) -
        ∑ j ∈ Finset.range N, diff j := by
    apply htail.nonneg
    intro j
    dsimp [diff, w]
    have hscore : lrCompactVScore R (N + 1) ≤
        lrCompactVScore R (j + N + 1) :=
      lrCompactVScore_monotone_index hR.1.le (by omega)
    have ha : 0 ≤ lrLowA (j + N + 1) :=
      (lrLowA_pos (by omega)).le
    have hT : 0 ≤ lrCompactVT v (t ^ 2) (j + N + 1) :=
      lrCompactVT_nonneg hv.1.le (sq_nonneg t) _
    unfold lrCompactVPWTerm
    nlinarith [mul_nonneg (mul_nonneg ha (sub_nonneg.mpr hscore)) hT]
  have hprefix :
      ∑ j ∈ Finset.range N, diff j =
        -lrCompactVPWError N R v (t ^ 2) := by
    unfold lrCompactVPWError diff w
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    unfold lrCompactVPWTerm
    ring
  unfold lrCompactVPWLower
  dsimp [w, P₀] at htailNonneg
  rw [hprefix] at htailNonneg
  linarith

/-- Positive summand of the truncated lower bound for `D=A-B`. -/
noncomputable def lrCompactVDTerm
    (R y : ℝ) (n : ℕ) : ℝ :=
  (1 - R ^ n) * y ^ n / (2 * (n : ℝ))

noncomputable def lrCompactVDHead
    (N : ℕ) (R y : ℝ) : ℝ :=
  ∑ j ∈ Finset.range N, lrCompactVDTerm R y (j + 1)

theorem lrCompactVDTerm_hasSum
    {R v t : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1)
    (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasSum (fun j : ℕ ↦
      lrCompactVDTerm R ((v * t) ^ 2) (j + 1))
      (lrFlowD R v t) := by
  have hvt : v * t ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · exact mul_pos hv.1 ht.1
    · calc
        v * t < 1 * t := mul_lt_mul_of_pos_right hv.2 ht.1
        _ < 1 := by simpa using ht.2
  have hy : (v * t) ^ 2 ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · exact sq_pos_of_pos hvt.1
    · nlinarith [sq_nonneg (v * t), mul_pos hvt.1 (sub_pos.mpr hvt.2)]
  have hRy : R * (v * t) ^ 2 ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · exact mul_pos hR.1 hy.1
    · calc
        R * (v * t) ^ 2 < 1 * (v * t) ^ 2 :=
          mul_lt_mul_of_pos_right hR.2 hy.1
        _ = (v * t) ^ 2 := one_mul _
        _ < 1 := hy.2
  have hySeries := lrL_sqrt_hasSum hy
  have hRySeries := lrL_sqrt_hasSum hRy
  have hsqrtR : 0 < Real.sqrt R := Real.sqrt_pos.2 hR.1
  have hsqrtMul : Real.sqrt (R * (v * t) ^ 2) =
      Real.sqrt R * (v * t) := by
    rw [Real.sqrt_mul hR.1.le, Real.sqrt_sq_eq_abs, abs_of_pos hvt.1]
  unfold lrFlowD lrFlowA lrFlowB
  convert hySeries.sub hRySeries using 1
  · funext j
    unfold lrCompactVDTerm
    rw [mul_pow]
    norm_num only [Nat.cast_add, Nat.cast_one]
    ring
  · rw [Real.sqrt_sq_eq_abs, abs_of_pos hvt.1, hsqrtMul]
    ring

theorem lrCompactVDHead_le_lrFlowD
    {R v t : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1)
    (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1)
    (N : ℕ) :
    lrCompactVDHead N R ((v * t) ^ 2) ≤ lrFlowD R v t := by
  have hseries := lrCompactVDTerm_hasSum hR hv ht
  rw [← hseries.tsum_eq]
  unfold lrCompactVDHead
  apply hseries.summable.sum_le_tsum (Finset.range N)
  intro j hj
  unfold lrCompactVDTerm
  have hRpow : R ^ (j + 1) ≤ 1 := pow_le_one₀ hR.1.le hR.2.le
  exact div_nonneg
    (mul_nonneg (sub_nonneg.mpr hRpow) (pow_nonneg (sq_nonneg (v * t)) _))
    (by positivity)

theorem lrCompactVDHead_nonneg
    {R y : ℝ} (hR : R ∈ Icc (0 : ℝ) 1) (hy : 0 ≤ y)
    (N : ℕ) :
    0 ≤ lrCompactVDHead N R y := by
  unfold lrCompactVDHead
  apply Finset.sum_nonneg
  intro j hj
  unfold lrCompactVDTerm
  exact div_nonneg
    (mul_nonneg
      (sub_nonneg.mpr (pow_le_one₀ hR.1 hR.2))
      (pow_nonneg hy _))
    (by positivity)

theorem lrCompactVPsiHead_nonneg
    {R v x : ℝ} (hR : R ∈ Icc (0 : ℝ) 1)
    (hv : v ∈ Ioc (0 : ℝ) 1) (hx : x ∈ Icc (0 : ℝ) 1)
    (N : ℕ) :
    0 ≤ lrCompactVPsiHead N R v x := by
  unfold lrCompactVPsiHead
  exact add_nonneg (lrCompactVFZero_nonneg hv) <|
    Finset.sum_nonneg fun j _ ↦
      lrCompactVPsiTerm_nonneg hR ⟨hv.1.le, hv.2⟩ hx (by omega)

/-- Exact finite lower expression before rational interval enclosure. -/
noncomputable def lrCompactVFiniteLower
    (N : ℕ) (R v t : ℝ) : ℝ :=
  lrFlowB R v t *
      (lrCompactVPWLower N R v t -
        4 * lrWKernel R 1 * (v * t ^ 2 / (1 + v))) +
    lrCompactVDHead N R ((v * t) ^ 2) *
      lrCompactVPsiHead N R v (t ^ 2)

/-- Analytic soundness of the finite structured certificate criterion. -/
theorem lrLowVReserve_nonneg_of_compact_finiteLower
    {R v t : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1)
    (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1)
    (N : ℕ) (hlower : 0 ≤ lrCompactVFiniteLower N R v t) :
    0 ≤ lrLowVReserve R v t := by
  have htSq : t ^ 2 ∈ Icc (0 : ℝ) 1 := by
    constructor
    · exact sq_nonneg t
    · nlinarith [mul_nonneg ht.1.le (sub_nonneg.mpr ht.2.le)]
  have hBPos : 0 < lrFlowB R v t := by
    apply lrFlowB_pos hv.1 ht.1.le
    have hsqrtR : Real.sqrt R < 1 := by
      simpa using (Real.sqrt_lt_sqrt_iff hR.1.le).2 hR.2
    calc
      Real.sqrt R * v * t < 1 * v * t := by
        exact mul_lt_mul_of_pos_right
          (mul_lt_mul_of_pos_right hsqrtR hv.1) ht.1
      _ < 1 := by
        have : v * t < 1 := calc
          v * t < 1 * t := mul_lt_mul_of_pos_right hv.2 ht.1
          _ < 1 := by simpa using ht.2
        simpa using this
  have hDHead := lrCompactVDHead_nonneg
    ⟨hR.1.le, hR.2.le⟩ (sq_nonneg (v * t)) N
  have hDLower := lrCompactVDHead_le_lrFlowD hR hv ht N
  have hD : 0 ≤ lrFlowD R v t := hDHead.trans hDLower
  have hPsiHead := lrCompactVPsiHead_nonneg
    ⟨hR.1.le, hR.2.le⟩ ⟨hv.1, hv.2.le⟩ htSq N
  have hPsiLower : lrCompactVPsiHead N R v (t ^ 2) ≤
      lrFlowC R v t :=
    lrCompactVPsiHead_le_of_hasSum
      ⟨hR.1.le, hR.2.le⟩ ⟨hv.1, hv.2.le⟩ htSq
      (lrCompactVPsiTerm_hasSum hR hv ht) N
  have hPWLower := lrCompactVPWLower_le_lrFlowPW hR hv ht N
  have hgroup : lrLowVReserve R v t =
      lrFlowB R v t *
          (lrFlowPW R v t -
            4 * lrWKernel R 1 * (v * t ^ 2 / (1 + v))) +
        lrFlowD R v t * lrFlowC R v t := by
    unfold lrLowVReserve lrLowYTangent lrFlowM
    have hden : 1 + v ≠ 0 := by linarith [hv.1]
    field_simp [hden]
    ring
  have hQ :
      lrCompactVPWLower N R v t -
          4 * lrWKernel R 1 * (v * t ^ 2 / (1 + v)) ≤
        lrFlowPW R v t -
          4 * lrWKernel R 1 * (v * t ^ 2 / (1 + v)) := by
    linarith
  have hBQ := mul_le_mul_of_nonneg_left hQ hBPos.le
  have hDPsi :
      lrCompactVDHead N R ((v * t) ^ 2) *
          lrCompactVPsiHead N R v (t ^ 2) ≤
        lrFlowD R v t * lrFlowC R v t :=
    mul_le_mul hDLower hPsiLower hPsiHead hD
  rw [hgroup]
  unfold lrCompactVFiniteLower at hlower
  nlinarith

theorem lrCompactVPWHead_le_lrFlowPW
    {R v t : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1)
    (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1)
    (N : ℕ) :
    lrCompactVPWHead N R v (t ^ 2) ≤ lrFlowPW R v t := by
  exact lrCompactVPWHead_le_of_hasSum hR.1.le hv.1.le (sq_nonneg t)
    (lrCompactVPWTerm_hasSum hR hv ht) N

theorem lrCompactVPsiHead_le_lrFlowC
    {R v t : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1)
    (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1)
    (N : ℕ) :
    lrCompactVPsiHead N R v (t ^ 2) ≤ lrFlowC R v t := by
  have htSq : t ^ 2 ∈ Icc (0 : ℝ) 1 := by
    constructor
    · exact sq_nonneg t
    · nlinarith [mul_nonneg ht.1.le (sub_nonneg.mpr ht.2.le)]
  exact lrCompactVPsiHead_le_of_hasSum
    ⟨hR.1.le, hR.2.le⟩ ⟨hv.1, hv.2.le⟩ htSq
    (lrCompactVPsiTerm_hasSum hR hv ht) N

theorem lrFlowC_nonneg_of_compact_series
    {R v t : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1)
    (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    0 ≤ lrFlowC R v t := by
  have hhead := lrCompactVPsiHead_le_lrFlowC hR hv ht 0
  have hf₀ := lrCompactVFZero_nonneg
    (show v ∈ Ioc (0 : ℝ) 1 from ⟨hv.1, hv.2.le⟩)
  have hhead' : lrCompactVFZero v ≤ lrFlowC R v t := by
    simpa [lrCompactVPsiHead] using hhead
  exact hf₀.trans hhead'

/-- Cancellation-preserving algebraic form of the `V` reserve used by the
compact checker.  This is the exact real identity underlying (M47). -/
theorem lrLowVReserve_eq_compact_grouped
    {R v t : ℝ} (hv : v ≠ -1) :
    lrLowVReserve R v t =
      lrFlowB R v t *
          (lrFlowPW R v t -
            4 * lrWKernel R 1 * (v * t ^ 2 / (1 + v))) +
        lrFlowD R v t * lrFlowC R v t := by
  unfold lrLowVReserve lrLowYTangent lrFlowM
  have hden : 1 + v ≠ 0 := by
    intro h
    apply hv
    linarith
  field_simp [hden]
  ring

/-- Sign-safe lower-bound assembly used at every compact certificate leaf.
The branch on `qLo` is exactly the `Bσ` choice in (M47). -/
theorem lrLowVReserve_nonneg_of_compact_lowerBounds
    {R v t bLo bHi qLo dLo psiLo : ℝ}
    (hvNe : v ≠ -1)
    (hbLower : bLo ≤ lrFlowB R v t)
    (hbUpper : lrFlowB R v t ≤ bHi)
    (hQ : qLo ≤
      lrFlowPW R v t - 4 * lrWKernel R 1 * (v * t ^ 2 / (1 + v)))
    (hdLower : dLo ≤ lrFlowD R v t)
    (hpsiLo : 0 ≤ psiLo) (hpsiLower : psiLo ≤ lrFlowC R v t)
    (hB : 0 ≤ lrFlowB R v t)
    (hD : 0 ≤ lrFlowD R v t)
    (htotal : 0 ≤
      (if 0 ≤ qLo then bLo else bHi) * qLo + dLo * psiLo) :
    0 ≤ lrLowVReserve R v t := by
  rw [lrLowVReserve_eq_compact_grouped hvNe]
  let Q := lrFlowPW R v t -
    4 * lrWKernel R 1 * (v * t ^ 2 / (1 + v))
  have hBQ : (if 0 ≤ qLo then bLo else bHi) * qLo ≤
      lrFlowB R v t * Q := by
    by_cases hq : 0 ≤ qLo
    · rw [if_pos hq]
      exact (mul_le_mul hbLower hQ hq hB)
    · rw [if_neg hq]
      have hqNeg : qLo < 0 := lt_of_not_ge hq
      calc
        bHi * qLo ≤ lrFlowB R v t * qLo :=
          mul_le_mul_of_nonpos_right hbUpper hqNeg.le
        _ ≤ lrFlowB R v t * Q := mul_le_mul_of_nonneg_left hQ hB
  have hDPsi : dLo * psiLo ≤
      lrFlowD R v t * lrFlowC R v t := by
    exact (mul_le_mul hdLower hpsiLower hpsiLo hD)
  dsimp [Q] at hBQ
  nlinarith

end CourtadeKumar
