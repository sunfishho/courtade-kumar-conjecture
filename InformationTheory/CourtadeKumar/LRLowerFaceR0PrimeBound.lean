import InformationTheory.CourtadeKumar.LRLowerFaceR0

/-!
# Small-argument bound for the entropy remainder derivative

This proves the exact `p_y` representation and the estimate
`r₀'(y) ≤ y log(4/y)/3` used in (M24).
-/

open Set

namespace CourtadeKumar

noncomputable def lrLowerFaceP (y : ℝ) : ℝ :=
  (1 - Real.sqrt (1 - y)) / 2

lemma lrLowerFaceP_geometry
    {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    let p := lrLowerFaceP y
    let z := Real.sqrt (1 - y)
    p ∈ Ioo (0 : ℝ) (1 / 2) ∧
    1 - 2 * p = z ∧
    y = 4 * p * (1 - p) := by
  let p := lrLowerFaceP y
  let z := Real.sqrt (1 - y)
  have hzPos : 0 < z := Real.sqrt_pos.2 (by linarith [hy.2])
  have hzLt : z < 1 := by
    simpa [z] using
      (Real.sqrt_lt_sqrt_iff (by linarith [hy.2] : 0 ≤ 1 - y)).2
        (by linarith [hy.1] : 1 - y < 1)
  have hzSq : z ^ 2 = 1 - y := by
    dsimp [z]
    exact Real.sq_sqrt (by linarith [hy.2])
  have hpEq : p = (1 - z) / 2 := rfl
  change p ∈ Ioo (0 : ℝ) (1 / 2) ∧
    1 - 2 * p = z ∧ y = 4 * p * (1 - p)
  refine ⟨?_, ?_, ?_⟩
  · rw [hpEq]
    constructor <;> linarith
  · rw [hpEq]
    ring
  · rw [hpEq]
    nlinarith [hzSq]

lemma lrLowerFaceP_bounds
    {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) (1 / 16 : ℝ)) :
    y / 4 ≤ lrLowerFaceP y ∧
      lrLowerFaceP y ≤ y / 3 ∧
      lrLowerFaceP y ≤ 1 / 48 := by
  have hyUnit : y ∈ Ioo (0 : ℝ) 1 := ⟨hy.1, hy.2.trans (by norm_num)⟩
  let p := lrLowerFaceP y
  let z := Real.sqrt (1 - y)
  have hgeom := lrLowerFaceP_geometry hyUnit
  change p ∈ Ioo (0 : ℝ) (1 / 2) ∧
    1 - 2 * p = z ∧ y = 4 * p * (1 - p) at hgeom
  have hp := hgeom.1
  have hzPos : 0 < z := Real.sqrt_pos.2 (by linarith [hy.2])
  have hzLe : z ≤ 1 := by linarith [hgeom.2.1, hp.1]
  have hzHalf : 1 / 2 ≤ z := by
    have hzSq : z ^ 2 = 1 - y := by
      dsimp [z]
      exact Real.sq_sqrt (by linarith [hy.2])
    nlinarith [hy.2]
  have hpFormula : p = y / (2 * (1 + z)) := by
    have hden : 1 + z ≠ 0 := by linarith [hzPos]
    rw [show y = 4 * p * (1 - p) from hgeom.2.2,
      show 1 + z = 2 * (1 - p) by linarith [hgeom.2.1]]
    field_simp [hden, (by linarith [hp.2] : 1 - p ≠ 0)]
    ring
  have hdenUpper : 2 * (1 + z) ≤ 4 := by linarith
  have hdenLower : 3 ≤ 2 * (1 + z) := by linarith
  have hdenPos : 0 < 2 * (1 + z) := by linarith
  have hLower : y / 4 ≤ p := by
    rw [hpFormula]
    rw [div_le_div_iff₀ (by norm_num) hdenPos]
    nlinarith [hy.1]
  have hUpper : p ≤ y / 3 := by
    rw [hpFormula]
    rw [div_le_div_iff₀ hdenPos (by norm_num)]
    nlinarith [hy.1]
  refine ⟨hLower, hUpper, ?_⟩
  exact hUpper.trans (by nlinarith [hy.2])

/-- Exact derivative representation from (DA3h)--(DA3i). -/
lemma lrLowerFaceR0Prime_eq_p
    {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    let p := lrLowerFaceP y
    lrLowerFaceR0Prime y =
      ((1 - p) * Real.log (1 - p) - p * Real.log p) /
        (2 * (1 - 2 * p)) := by
  let p := lrLowerFaceP y
  let z := Real.sqrt (1 - y)
  change lrLowerFaceR0Prime y =
    ((1 - p) * Real.log (1 - p) - p * Real.log p) /
      (2 * (1 - 2 * p))
  have hgeom := lrLowerFaceP_geometry hy
  change p ∈ Ioo (0 : ℝ) (1 / 2) ∧
    1 - 2 * p = z ∧ y = 4 * p * (1 - p) at hgeom
  have hp := hgeom.1
  have hzEq : 1 - 2 * p = z := hgeom.2.1
  have hyEq : y = 4 * p * (1 - p) := hgeom.2.2
  have hzPos : 0 < z := by linarith [hzEq, hp.2]
  have hpOnePos : 0 < 1 - p := sub_pos.mpr (hp.2.trans (by norm_num))
  have hratio : (1 + z) / (1 - z) = (1 - p) / p := by
    rw [← hzEq]
    field_simp [hp.1.ne']
    ring
  have hfour : 4 / y = 1 / (p * (1 - p)) := by
    rw [hyEq]
    field_simp [hp.1.ne', hpOnePos.ne']
  have hzMem : z ∈ Icc (-1 : ℝ) 1 := by
    constructor
    · linarith [hzPos]
    · have hzLt : z < 1 := by linarith [hzEq, hp.1]
      exact hzLt.le
  unfold lrLowerFaceR0Prime lrLowerFaceQ0Prime
  rw [lrCertificateQPrime_eq, Real.artanh_eq_half_log hzMem,
    hratio, hfour, Real.log_div hpOnePos.ne' hp.1.ne',
    Real.log_div (by norm_num : (1 : ℝ) ≠ 0)
      (mul_ne_zero hp.1.ne' hpOnePos.ne'),
    Real.log_mul hp.1.ne' hpOnePos.ne']
  rw [show Real.sqrt (1 - y) = z by rfl, ← hzEq]
  norm_num
  field_simp [(by linarith [hp.2] : 1 - 2 * p ≠ 0)]
  ring

/-- The derivative estimate used in the entropy-remainder payment. -/
theorem lrLowerFaceR0Prime_upper
    {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) (1 / 16 : ℝ)) :
    lrLowerFaceR0Prime y ≤ y / 3 * Real.log (4 / y) := by
  have hyUnit : y ∈ Ioo (0 : ℝ) 1 := ⟨hy.1, hy.2.trans (by norm_num)⟩
  let p := lrLowerFaceP y
  have hgeom := lrLowerFaceP_geometry hyUnit
  change p ∈ Ioo (0 : ℝ) (1 / 2) ∧
    1 - 2 * p = Real.sqrt (1 - y) ∧
      y = 4 * p * (1 - p) at hgeom
  have hp := hgeom.1
  have hpbounds := lrLowerFaceP_bounds hy
  change y / 4 ≤ p ∧ p ≤ y / 3 ∧ p ≤ 1 / 48 at hpbounds
  have hpOnePos : 0 < 1 - p := sub_pos.mpr (hp.2.trans (by norm_num))
  have hlogOne : Real.log (1 - p) ≤ 0 :=
    Real.log_nonpos hpOnePos.le (by linarith [hp.1])
  have hnum :
      (1 - p) * Real.log (1 - p) - p * Real.log p ≤
        p * Real.log (1 / p) := by
    rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) hp.1.ne']
    norm_num
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hpOnePos.le hlogOne]
  have hden : 1 ≤ 2 * (1 - 2 * p) := by
    nlinarith [hpbounds.2.2]
  have hdenPos : 0 < 2 * (1 - 2 * p) := lt_of_lt_of_le zero_lt_one hden
  have hquot :
      ((1 - p) * Real.log (1 - p) - p * Real.log p) /
          (2 * (1 - 2 * p)) ≤ p * Real.log (1 / p) := by
    rw [div_le_iff₀ hdenPos]
    have hprodNonneg : 0 ≤ p * Real.log (1 / p) := by
      exact mul_nonneg hp.1.le (Real.log_nonneg (by
        rw [one_le_div₀ hp.1]
        exact hp.2.le.trans (by norm_num)))
    have hscale := mul_le_mul_of_nonneg_right hden hprodNonneg
    calc
      (1 - p) * Real.log (1 - p) - p * Real.log p ≤
          p * Real.log (1 / p) := hnum
      _ = 1 * (p * Real.log (1 / p)) := by ring
      _ ≤ (2 * (1 - 2 * p)) * (p * Real.log (1 / p)) := hscale
      _ = p * Real.log (1 / p) * (2 * (1 - 2 * p)) := by ring
  have hinvOrder : 1 / p ≤ 4 / y := by
    rw [div_le_div_iff₀ hp.1 hy.1]
    nlinarith [hpbounds.1]
  have hlogOrder := Real.log_le_log (div_pos (by norm_num) hp.1) hinvOrder
  have hlogPos : 0 ≤ Real.log (4 / y) :=
    Real.log_nonneg (by rw [one_le_div₀ hy.1]; linarith [hy.2])
  have hprod : p * Real.log (1 / p) ≤ y / 3 * Real.log (4 / y) := by
    calc
      p * Real.log (1 / p) ≤ p * Real.log (4 / y) :=
        mul_le_mul_of_nonneg_left hlogOrder hp.1.le
      _ ≤ y / 3 * Real.log (4 / y) :=
        mul_le_mul_of_nonneg_right hpbounds.2.1 hlogPos
  rw [show lrLowerFaceR0Prime y =
      ((1 - p) * Real.log (1 - p) - p * Real.log p) /
        (2 * (1 - 2 * p)) by
    simpa [p] using lrLowerFaceR0Prime_eq_p hyUnit]
  exact hquot.trans hprod

end CourtadeKumar
