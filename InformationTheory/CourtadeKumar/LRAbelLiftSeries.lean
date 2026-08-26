import InformationTheory.CourtadeKumar.LRAbelBaseSeries
import InformationTheory.CourtadeKumar.LRAbelCoefficients

/-! Convergence and positivity of the audited coefficientwise `R`-lift. -/

open Set

namespace CourtadeKumar

lemma lrAbelA_mem_Icc
    {j : ℕ} (hj : 1 ≤ j) : lrAbelA j ∈ Icc (0 : ℝ) 1 := by
  have hjr : 1 ≤ (j : ℝ) := by exact_mod_cast hj
  have hden : 0 < 2 * (j : ℝ) * (2 * (j : ℝ) - 1) := by
    have : 0 < 2 * (j : ℝ) - 1 := by nlinarith
    positivity
  unfold lrAbelA
  constructor
  · exact div_nonneg (by linarith) hden.le
  · rw [div_le_one hden]
    nlinarith

lemma lrAbelB_mem_Icc
    {j : ℕ} (hj : 1 ≤ j) : lrAbelB j ∈ Icc (0 : ℝ) 1 := by
  have hjr : 1 ≤ (j : ℝ) := by exact_mod_cast hj
  have hden : 0 < 2 * (2 * (j : ℝ) + 1) := by positivity
  unfold lrAbelB
  constructor
  · positivity
  · rw [div_le_one hden]
    nlinarith

lemma lrAbelQ_mem_Icc_two
    {v x : ℝ} (hv : v ∈ Icc (0 : ℝ) 1) (hx : x ∈ Icc (0 : ℝ) 1) :
    lrAbelQ v x ∈ Icc (0 : ℝ) 2 := by
  unfold lrAbelQ
  constructor
  · exact add_nonneg (sub_nonneg.mpr hv.2)
      (mul_nonneg (div_nonneg (by linarith [hv.1]) (by norm_num))
        (sub_nonneg.mpr hx.2))
  · have hfirst : 1 - v ≤ 1 := by linarith [hv.1]
    have hhalf : (1 + v) / 2 ≤ 1 := by linarith [hv.2]
    have hhalf0 : 0 ≤ (1 + v) / 2 := by linarith [hv.1]
    have hxsub0 : 0 ≤ 1 - x := sub_nonneg.mpr hx.2
    have hxsub1 : 1 - x ≤ 1 := by linarith [hx.1]
    have hsecond : (1 + v) / 2 * (1 - x) ≤ 1 := by
      nlinarith [mul_le_mul hhalf hxsub1 hxsub0 (by norm_num : (0 : ℝ) ≤ 1)]
    linarith

/-- A deliberately coarse uniform bound, sufficient for geometric
convergence of the lift on `0 ≤ R < 1`. -/
theorem abs_lrAbelC_le
    {j : ℕ} (hj : 1 ≤ j) {v x : ℝ}
    (hv : v ∈ Icc (0 : ℝ) 1) (hx : x ∈ Icc (0 : ℝ) 1) :
    |lrAbelC j v x| ≤ 18 := by
  have hA := lrAbelA_mem_Icc hj
  have hB := lrAbelB_mem_Icc hj
  have hQ := lrAbelQ_mem_Icc_two hv hx
  have hjr : 1 ≤ (j : ℝ) := by exact_mod_cast hj
  have hxj : 0 ≤ x ^ j := pow_nonneg hx.1 _
  have hxj1 : x ^ j ≤ 1 := pow_le_one₀ hx.1 hx.2
  have hvOdd : 0 ≤ v ^ (2 * j - 1) := pow_nonneg hv.1 _
  have hvOdd1 : v ^ (2 * j - 1) ≤ 1 := pow_le_one₀ hv.1 hv.2
  have hvPlus : 0 ≤ v ^ (2 * j + 1) := pow_nonneg hv.1 _
  have hvPlus1 : v ^ (2 * j + 1) ≤ 1 := pow_le_one₀ hv.1 hv.2
  have hvEven : 0 ≤ v ^ (2 * j) := pow_nonneg hv.1 _
  have hvEven1 : v ^ (2 * j) ≤ 1 := pow_le_one₀ hv.1 hv.2
  let U : ℝ := lrAbelA j * (1 + v ^ (2 * j - 1))
  let V : ℝ := lrAbelB j * x * (1 + v ^ (2 * j + 1))
  let T₁ : ℝ := (1 + x) * x ^ j * (U - V)
  let T₂ : ℝ := 4 * x * (lrAbelA j - lrAbelB j)
  let T₃ : ℝ := lrAbelQ v x * (1 + x) * v ^ (2 * j) * x ^ j /
    (2 * (j : ℝ))
  have hU : U ∈ Icc (0 : ℝ) 2 := by
    dsimp [U]
    have hfactor0 : 0 ≤ 1 + v ^ (2 * j - 1) := by linarith
    have hfactor1 : 1 + v ^ (2 * j - 1) ≤ 2 := by linarith
    constructor
    · exact mul_nonneg hA.1 hfactor0
    · nlinarith [mul_le_mul hA.2 hfactor1 hfactor0 (by norm_num : (0 : ℝ) ≤ 1)]
  have hV : V ∈ Icc (0 : ℝ) 2 := by
    dsimp [V]
    have hBx0 : 0 ≤ lrAbelB j * x := mul_nonneg hB.1 hx.1
    have hBx : lrAbelB j * x ≤ 1 := by
      nlinarith [mul_le_mul hB.2 hx.2 hx.1 (by norm_num : (0 : ℝ) ≤ 1)]
    have hfactor0 : 0 ≤ 1 + v ^ (2 * j + 1) := by linarith
    have hfactor1 : 1 + v ^ (2 * j + 1) ≤ 2 := by linarith
    constructor
    · exact mul_nonneg hBx0 hfactor0
    · nlinarith [mul_le_mul hBx hfactor1 hfactor0 (by norm_num : (0 : ℝ) ≤ 1)]
  have hUV : |U - V| ≤ 2 := by rw [abs_le]; exact ⟨by linarith [hU.1, hV.2], by linarith [hU.2, hV.1]⟩
  have hT₁ : |T₁| ≤ 4 := by
    dsimp [T₁]
    rw [abs_mul, abs_mul, abs_of_nonneg (by linarith [hx.1]), abs_of_nonneg hxj]
    have hfactor : (1 + x) * x ^ j ≤ 2 := by
      nlinarith [mul_le_mul (by linarith [hx.2] : 1 + x ≤ 2) hxj1 hxj
        (by norm_num : (0 : ℝ) ≤ 2)]
    nlinarith [mul_le_mul hfactor hUV (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)]
  have hAB : |lrAbelA j - lrAbelB j| ≤ 1 := by
    rw [abs_le]
    exact ⟨by linarith [hA.1, hB.2], by linarith [hA.2, hB.1]⟩
  have hT₂ : |T₂| ≤ 4 := by
    dsimp [T₂]
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num), abs_of_nonneg hx.1]
    nlinarith [mul_le_mul hx.2 hAB (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)]
  have hden : 0 < 2 * (j : ℝ) := by positivity
  have hT₃nonneg : 0 ≤ T₃ := by
    dsimp [T₃]
    exact div_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg hQ.1 (by linarith [hx.1])) hvEven) hxj)
      hden.le
  have hT₃ : |T₃| ≤ 2 := by
    rw [abs_of_nonneg hT₃nonneg]
    dsimp [T₃]
    rw [div_le_iff₀ hden]
    have hplus0 : 0 ≤ 1 + x := by linarith [hx.1]
    have hplus1 : 1 + x ≤ 2 := by linarith [hx.2]
    have hfirst : lrAbelQ v x * (1 + x) ≤ 4 := by
      nlinarith [mul_le_mul hQ.2 hplus1 hplus0 (by norm_num : (0 : ℝ) ≤ 2)]
    have hsecond0 : 0 ≤ v ^ (2 * j) * x ^ j := mul_nonneg hvEven hxj
    have hsecond : v ^ (2 * j) * x ^ j ≤ 1 := by
      nlinarith [mul_le_mul hvEven1 hxj1 hxj (by norm_num : (0 : ℝ) ≤ 1)]
    have hnum : lrAbelQ v x * (1 + x) * v ^ (2 * j) * x ^ j ≤ 4 := by
      nlinarith [mul_le_mul hfirst hsecond hsecond0 (by norm_num : (0 : ℝ) ≤ 4)]
    nlinarith
  have hdecomp : lrAbelC j v x = T₁ - T₂ - T₃ := by
    rfl
  rw [hdecomp]
  calc
    |T₁ - T₂ - T₃| ≤ |T₁| + |T₂| + |T₃| := by
      exact (abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)
    _ ≤ 18 := by linarith

theorem summable_lrAbelLift
    {R v x : ℝ} (hR : R ∈ Ico (0 : ℝ) 1)
    (hv : v ∈ Icc (0 : ℝ) 1) (hx : x ∈ Icc (0 : ℝ) 1) :
    Summable (fun n : ℕ ↦ lrAbelC (n + 1) v x * R ^ (n + 1)) := by
  have hgeom : Summable (fun n : ℕ ↦ 18 * R * R ^ n) :=
    (summable_geometric_of_lt_one hR.1 hR.2).mul_left (18 * R)
  apply Summable.of_norm_bounded hgeom
  intro n
  have hpow : 0 ≤ R ^ (n + 1) := pow_nonneg hR.1 _
  calc
    ‖lrAbelC (n + 1) v x * R ^ (n + 1)‖ =
        |lrAbelC (n + 1) v x| * R ^ (n + 1) := by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hpow]
    _ ≤ 18 * R ^ (n + 1) :=
      mul_le_mul_of_nonneg_right (abs_lrAbelC_le (by omega) hv hx) hpow
    _ = 18 * R * R ^ n := by rw [pow_succ']; ring

/-- Base positivity plus coefficientwise positivity proves positivity of the
whole audited lift series. -/
theorem lrAbelLiftSeries_nonneg
    {R v t : ℝ} (hR : R ∈ Ico (0 : ℝ) 1)
    (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    0 ≤ lrAbelBaseF v t +
      ∑' n : ℕ, lrAbelC (n + 1) v (t ^ 2) * R ^ (n + 1) := by
  have hx : t ^ 2 ∈ Icc (0 : ℝ) 1 := by
    constructor
    · positivity
    · nlinarith [ht.1, ht.2]
  have hs := summable_lrAbelLift hR
    (show v ∈ Icc (0 : ℝ) 1 from ⟨hv.1.le, hv.2.le⟩) hx
  exact add_nonneg (lrAbelBaseF_nonneg hv ht)
    (tsum_nonneg fun n ↦ mul_nonneg
      (lrAbelC_nonneg (by omega)
        (show v ∈ Icc (0 : ℝ) 1 from ⟨hv.1.le, hv.2.le⟩) hx)
      (pow_nonneg hR.1 _))

end CourtadeKumar
