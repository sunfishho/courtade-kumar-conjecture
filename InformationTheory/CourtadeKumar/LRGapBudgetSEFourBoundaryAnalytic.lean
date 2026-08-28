import InformationTheory.CourtadeKumar.LRHighShapeGapBudget
import InformationTheory.CourtadeKumar.LRSmallSBridgeIdentification

/-!
# Cancellation-safe analytic lower bound on the `e = 4s` boundary

Direct interval evaluation of `lrGapBudgetSEChi s (4 * s) chi` loses the
logarithmic cancellation at `s = 0`.  This file instead splits
`Q = q₀ + r₀`, collects the `q₀` terms exactly, and pays for the convex
remainder `r₀` using its already-proved derivative bound.
-/

open Set

namespace CourtadeKumar
namespace LRGapBudgetSEFourBoundaryAnalytic

noncomputable def x (s chi : ℝ) : ℝ := 1 - 4 * chi * s

noncomputable def v (s chi : ℝ) : ℝ :=
  Real.sqrt ((1 - 4 * s) / x s chi)

noncomputable def leftCoeff (s chi : ℝ) : ℝ :=
  1 + 4 * chi * (1 - s)

noncomputable def rightCoeff (s : ℝ) : ℝ := 5 - 4 * s

noncomputable def slopeCoeff (s chi : ℝ) : ℝ :=
  2 * (2 + v s chi) / (1 + v s chi)

noncomputable def coreCoeff (s chi : ℝ) : ℝ :=
  leftCoeff s chi + rightCoeff s / v s chi - slopeCoeff s chi

noncomputable def logFactor (s chi : ℝ) : ℝ :=
  Real.log 2 + Real.log (1 + v s chi) - Real.log (2 + v s chi)

/-- The normalized elementary minorant to be certified on the small boundary
box.  It has no singular `log s`: the entire remainder payment has already
been bounded by its value at `s = 1/10`. -/
noncomputable def lowerModel (s chi : ℝ) : ℝ :=
  -32 * (1 - s) * s * (1 - chi) ^ 2 /
      (x s chi ^ 2 * (1 + v s chi) ^ 2) -
    (1 + v s chi) / v s chi *
      (Real.log 2 + 2 * logFactor s chi) +
    (1 / 4 : ℝ) *
      (coreCoeff s chi * (Real.log 40 + 1) -
        leftCoeff s chi * Real.log (leftCoeff s chi) -
        rightCoeff s / v s chi * Real.log (rightCoeff s) +
        4 * slopeCoeff s chi * Real.log 2) -
    (2 / 15 : ℝ) * Real.log 40

lemma boundary_B_left (s chi : ℝ) :
    lrCertificateB s (chi * (4 * s)) = s * leftCoeff s chi := by
  unfold lrCertificateB leftCoeff
  ring

lemma boundary_B_right (s : ℝ) :
    lrCertificateB s (4 * s) = s * rightCoeff s := by
  unfold lrCertificateB rightCoeff
  ring

lemma boundary_geometry
    {s chi : ℝ} (hs : s ∈ Ioc (0 : ℝ) (1 / 10 : ℝ))
    (hchi : chi ∈ Icc (0 : ℝ) 1) :
    0 < x s chi ∧ x s chi ≤ 1 ∧
      v s chi ∈ Icc (1 / 2 : ℝ) 1 := by
  have hsFour : 4 * s ≤ 2 / 5 := by nlinarith [hs.2]
  have hprodNonneg : 0 ≤ 4 * chi * s :=
    mul_nonneg (mul_nonneg (by norm_num) hchi.1) hs.1.le
  have hprodLe : 4 * chi * s ≤ 4 * s := by
    nlinarith [mul_le_mul_of_nonneg_right hchi.2 hs.1.le]
  have hxPos : 0 < x s chi := by
    unfold x
    nlinarith
  have hxLe : x s chi ≤ 1 := by
    unfold x
    linarith
  have hnumPos : 0 < 1 - 4 * s := by nlinarith
  have hradPos : 0 < (1 - 4 * s) / x s chi :=
    div_pos hnumPos hxPos
  have hvPos : 0 < v s chi := by
    unfold v
    exact Real.sqrt_pos.2 hradPos
  have hvSq : v s chi ^ 2 = (1 - 4 * s) / x s chi := by
    unfold v
    exact Real.sq_sqrt hradPos.le
  have hnumLeX : 1 - 4 * s ≤ x s chi := by
    unfold x
    nlinarith [mul_nonneg hs.1.le (sub_nonneg.mpr hchi.2)]
  have hradLe : (1 - 4 * s) / x s chi ≤ 1 := by
    rw [div_le_one hxPos]
    exact hnumLeX
  have hvLe : v s chi ≤ 1 := by nlinarith [hvSq]
  have hradQuarter : (1 / 4 : ℝ) ≤ (1 - 4 * s) / x s chi := by
    rw [le_div_iff₀ hxPos]
    have hxQuarter : (1 / 4 : ℝ) * x s chi ≤ 1 / 4 := by
      nlinarith [hxLe]
    nlinarith [hsFour]
  have hvHalf : (1 / 2 : ℝ) ≤ v s chi := by
    nlinarith [hvSq]
  exact ⟨hxPos, hxLe, hvHalf, hvLe⟩

lemma one_sub_v_eq
    {s chi : ℝ} (hs : s ∈ Ioc (0 : ℝ) (1 / 10 : ℝ))
    (hchi : chi ∈ Icc (0 : ℝ) 1) :
    1 - v s chi =
      4 * s * (1 - chi) / (x s chi * (1 + v s chi)) := by
  have hgeom := boundary_geometry hs hchi
  have hxNe := hgeom.1.ne'
  have hvPos : 0 < v s chi :=
    (by norm_num : (0 : ℝ) < 1 / 2).trans_le hgeom.2.2.1
  have hvPlusNe : 1 + v s chi ≠ 0 := by positivity
  have hradPos : 0 < (1 - 4 * s) / x s chi := by
    exact div_pos (by nlinarith [hs.2]) hgeom.1
  have hvSq : v s chi ^ 2 = (1 - 4 * s) / x s chi := by
    unfold v
    exact Real.sq_sqrt hradPos.le
  calc
    1 - v s chi = (1 - v s chi ^ 2) / (1 + v s chi) := by
      field_simp [hvPlusNe]
      ring
    _ = 4 * s * (1 - chi) /
        (x s chi * (1 + v s chi)) := by
      rw [hvSq]
      field_simp [hxNe, hvPlusNe]
      unfold x
      ring

lemma coefficient_bounds
    {s chi : ℝ} (hs : s ∈ Ioc (0 : ℝ) (1 / 10 : ℝ))
    (hchi : chi ∈ Icc (0 : ℝ) 1) :
    0 < leftCoeff s chi ∧ 0 < rightCoeff s ∧
      0 < slopeCoeff s chi ∧ slopeCoeff s chi ≤ 4 ∧
      0 ≤ coreCoeff s chi := by
  have hgeom := boundary_geometry hs hchi
  have hvPos : 0 < v s chi :=
    (by norm_num : (0 : ℝ) < 1 / 2).trans_le hgeom.2.2.1
  have hvLe := hgeom.2.2.2
  have hleft : 0 < leftCoeff s chi := by
    unfold leftCoeff
    have : 0 ≤ 4 * chi * (1 - s) :=
      mul_nonneg (mul_nonneg (by norm_num) hchi.1) (by nlinarith [hs.2])
    linarith
  have hright : 0 < rightCoeff s := by
    unfold rightCoeff
    nlinarith [hs.2]
  have hslopePos : 0 < slopeCoeff s chi := by
    unfold slopeCoeff
    positivity
  have hslopeLe : slopeCoeff s chi ≤ 4 := by
    unfold slopeCoeff
    rw [div_le_iff₀ (by positivity : 0 < 1 + v s chi)]
    nlinarith
  have hrightFour : 4 ≤ rightCoeff s := by
    unfold rightCoeff
    nlinarith [hs.2]
  have hrightDiv : rightCoeff s ≤ rightCoeff s / v s chi := by
    rw [le_div_iff₀ hvPos]
    nlinarith
  have hleftOne : 1 ≤ leftCoeff s chi := by
    unfold leftCoeff
    have : 0 ≤ 4 * chi * (1 - s) :=
      mul_nonneg (mul_nonneg (by norm_num) hchi.1) (by nlinarith [hs.2])
    linarith
  have hcore : 0 ≤ coreCoeff s chi := by
    unfold coreCoeff
    linarith
  exact ⟨hleft, hright, hslopePos, hslopeLe, hcore⟩

lemma lrLowerFaceQ0_mul
    {s a : ℝ} (hs : 0 < s) (ha : 0 < a) :
    lrLowerFaceQ0 (s * a) =
      s * a / 4 * (Real.log (4 / s) - Real.log a + 1) := by
  have hsNe := hs.ne'
  have haNe := ha.ne'
  have hquot : 4 / (s * a) = (4 / s) / a := by
    field_simp [hsNe, haNe]
  unfold lrLowerFaceQ0
  rw [hquot, Real.log_div (div_ne_zero (by norm_num) hsNe) haNe]

lemma q0_collection_eq
    {s a b w A : ℝ} (hs : 0 < s) (ha : 0 < a)
    (hb : 0 < b) (hw : 0 < w) :
    lrLowerFaceQ0 (s * a) + lrLowerFaceQ0 (s * b) / w -
        A * (lrLowerFaceQ0 s - s * Real.log 2) =
      s / 4 *
        ((a + b / w - A) * (Real.log (4 / s) + 1) -
          a * Real.log a - (b / w) * Real.log b +
          4 * A * Real.log 2) := by
  rw [lrLowerFaceQ0_mul hs ha, lrLowerFaceQ0_mul hs hb]
  unfold lrLowerFaceQ0
  field_simp [hw.ne']
  ring

lemma lrLowerFaceR0_convexOn_Icc_zero
    {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    ConvexOn ℝ (Icc (0 : ℝ) s) lrLowerFaceR0 := by
  have hsub : Icc (0 : ℝ) s ⊆ Ico (0 : ℝ) 1 := by
    intro y hy
    exact ⟨hy.1, hy.2.trans_lt hs.2⟩
  apply MonotoneOn.convexOn_of_deriv (convex_Icc (0 : ℝ) s)
  · intro y hy
    rcases hy.1.eq_or_lt with rfl | hyPos
    · exact continuousWithinAt_lrLowerFaceR0_zero.mono hsub
    · exact (hasDerivAt_lrLowerFaceR0
        ⟨hyPos, hy.2.trans_lt hs.2⟩).continuousAt.continuousWithinAt
  · intro y hy
    rw [interior_Icc] at hy
    exact (hasDerivAt_lrLowerFaceR0
      ⟨hy.1, hy.2.trans hs.2⟩).differentiableAt.differentiableWithinAt
  · intro a ha b hb hab
    rw [interior_Icc] at ha hb
    rw [(hasDerivAt_lrLowerFaceR0
        ⟨ha.1, ha.2.trans hs.2⟩).deriv,
      (hasDerivAt_lrLowerFaceR0
        ⟨hb.1, hb.2.trans hs.2⟩).deriv]
    exact lrLowerFaceR0Prime_monotoneOn
      ⟨ha.1, ha.2.trans hs.2⟩ ⟨hb.1, hb.2.trans hs.2⟩ hab

/-- Convexity and `r₀(0)=0` bound the remainder by its right tangent. -/
lemma lrLowerFaceR0_le_mul_prime
    {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    lrLowerFaceR0 s ≤ s * lrLowerFaceR0Prime s := by
  have hslope := (lrLowerFaceR0_convexOn_Icc_zero hs).slope_le_of_hasDerivAt
    (show (0 : ℝ) ∈ Icc (0 : ℝ) s by exact ⟨le_rfl, hs.1.le⟩)
    (show s ∈ Icc (0 : ℝ) s by exact ⟨hs.1.le, le_rfl⟩)
    hs.1 (hasDerivAt_lrLowerFaceR0 hs)
  simp only [slope_def_field, lrLowerFaceR0_zero, sub_zero] at hslope
  simpa [mul_comm] using (div_le_iff₀ hs.1).mp hslope

/-- The elementary `p_y` bounds used in the remainder estimate remain valid
through the entire boundary range `y ≤ 1/10`. -/
lemma lrLowerFaceP_bounds_tenth
    {y : ℝ} (hy : y ∈ Ioc (0 : ℝ) (1 / 10 : ℝ)) :
    y / 4 ≤ lrLowerFaceP y ∧
      lrLowerFaceP y ≤ y / 3 ∧
      lrLowerFaceP y ≤ 1 / 30 := by
  have hyUnit : y ∈ Ioo (0 : ℝ) 1 :=
    ⟨hy.1, hy.2.trans_lt (by norm_num)⟩
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
    rw [hpFormula, div_le_div_iff₀ (by norm_num) hdenPos]
    nlinarith [hy.1]
  have hUpper : p ≤ y / 3 := by
    rw [hpFormula, div_le_div_iff₀ hdenPos (by norm_num)]
    nlinarith [hy.1]
  exact ⟨hLower, hUpper, hUpper.trans (by nlinarith [hy.2])⟩

/-- The derivative payment bound has no genuine `1/16` obstruction; the
same proof works on the full `y ≤ 1/10` boundary interval. -/
lemma lrLowerFaceR0Prime_upper_tenth
    {y : ℝ} (hy : y ∈ Ioc (0 : ℝ) (1 / 10 : ℝ)) :
    lrLowerFaceR0Prime y ≤ y / 3 * Real.log (4 / y) := by
  have hyUnit : y ∈ Ioo (0 : ℝ) 1 :=
    ⟨hy.1, hy.2.trans_lt (by norm_num)⟩
  let p := lrLowerFaceP y
  have hgeom := lrLowerFaceP_geometry hyUnit
  change p ∈ Ioo (0 : ℝ) (1 / 2) ∧
    1 - 2 * p = Real.sqrt (1 - y) ∧
      y = 4 * p * (1 - p) at hgeom
  have hp := hgeom.1
  have hpbounds := lrLowerFaceP_bounds_tenth hy
  change y / 4 ≤ p ∧ p ≤ y / 3 ∧ p ≤ 1 / 30 at hpbounds
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
  have hdenPos : 0 < 2 * (1 - 2 * p) :=
    lt_of_lt_of_le zero_lt_one hden
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
  have hlogOrder := Real.log_le_log
    (div_pos (by norm_num) hp.1) hinvOrder
  have hlogPos : 0 ≤ Real.log (4 / y) :=
    Real.log_nonneg (by rw [one_le_div₀ hy.1]; linarith [hy.2])
  have hprod : p * Real.log (1 / p) ≤
      y / 3 * Real.log (4 / y) := by
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

/-- Endpoint tangent bound for the only residual singular product. -/
lemma mul_log_four_div_le_log40_div10
    {s : ℝ} (hs : s ∈ Ioc (0 : ℝ) (1 / 10 : ℝ)) :
    s * Real.log (4 / s) ≤ Real.log 40 / 10 := by
  have hsNe := hs.1.ne'
  let u : ℝ := 1 / (10 * s)
  have hu : 0 < u := by
    unfold u
    exact one_div_pos.mpr (mul_pos (by norm_num) hs.1)
  have hfactor : 4 / s = 40 * u := by
    unfold u
    field_simp [hsNe]
    ring
  have hlogSplit : Real.log (4 / s) = Real.log 40 + Real.log u := by
    rw [hfactor, Real.log_mul (by norm_num : (40 : ℝ) ≠ 0) hu.ne']
  have hlogU := Real.log_le_sub_one_of_pos hu
  have hlog40 : 1 ≤ Real.log 40 := by
    have hexp : Real.exp 1 < (40 : ℝ) :=
      Real.exp_one_lt_d9.trans (by norm_num)
    exact ((Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 40)).2 hexp).le
  rw [hlogSplit]
  have hscaled := mul_le_mul_of_nonneg_left hlogU hs.1.le
  have huIdentity : s * u = 1 / 10 := by
    unfold u
    field_simp [hsNe]
  rw [mul_sub, mul_one, huIdentity] at hscaled
  have hend := mul_le_mul_of_nonneg_right hs.2 (sub_nonneg.mpr hlog40)
  nlinarith

/-- Uniform normalized payment for `r₀` on `0 < s ≤ 1/10`. -/
lemma remainder_normalized_payment
    {s : ℝ} (hs : s ∈ Ioc (0 : ℝ) (1 / 10 : ℝ)) :
    lrLowerFaceR0 s ≤ s * ((1 / 30 : ℝ) * Real.log 40) := by
  have hsUnit : s ∈ Ioo (0 : ℝ) 1 :=
    ⟨hs.1, hs.2.trans_lt (by norm_num)⟩
  have hconvex := lrLowerFaceR0_le_mul_prime hsUnit
  have hprime := lrLowerFaceR0Prime_upper_tenth hs
  have hscaled := mul_le_mul_of_nonneg_left hprime hs.1.le
  have hlog := mul_log_four_div_le_log40_div10 hs
  calc
    lrLowerFaceR0 s ≤ s * lrLowerFaceR0Prime s := hconvex
    _ ≤ s * (s / 3 * Real.log (4 / s)) := hscaled
    _ = s / 3 * (s * Real.log (4 / s)) := by ring
    _ ≤ s / 3 * (Real.log 40 / 10) := by
      exact mul_le_mul_of_nonneg_left hlog (div_nonneg hs.1.le (by norm_num))
    _ = s * ((1 / 30 : ℝ) * Real.log 40) := by ring

lemma lrCertificateQ_eq_q0_add_r0 (y : ℝ) :
    lrCertificateQ y = lrLowerFaceQ0 y + lrLowerFaceR0 y := by
  unfold lrLowerFaceR0
  ring

lemma boundary_B_mem_Ioo
    {s chi : ℝ} (hs : s ∈ Ioc (0 : ℝ) (1 / 10 : ℝ))
    (hchi : chi ∈ Icc (0 : ℝ) 1) :
    lrCertificateB s (chi * (4 * s)) ∈ Ioo (0 : ℝ) 1 ∧
      lrCertificateB s (4 * s) ∈ Ioo (0 : ℝ) 1 := by
  have hsUnit : s ∈ Ioo (0 : ℝ) 1 :=
    ⟨hs.1, hs.2.trans_lt (by norm_num)⟩
  have hyLeftNonneg : 0 ≤ chi * (4 * s) :=
    mul_nonneg hchi.1 (mul_nonneg (by norm_num) hs.1.le)
  have hyLeftLt : chi * (4 * s) < 1 := by
    have hmul := mul_le_mul_of_nonneg_right hchi.2
      (show 0 ≤ 4 * s from mul_nonneg (by norm_num) hs.1.le)
    nlinarith [hmul, hs.2]
  have hyRight : 4 * s ∈ Ioo (0 : ℝ) 1 := by
    constructor <;> nlinarith [hs.1, hs.2]
  have hB : ∀ y : ℝ, 0 ≤ y → y < 1 →
      lrCertificateB s y ∈ Ioo (0 : ℝ) 1 := by
    intro y hyNonneg hyLt
    unfold lrCertificateB
    have hprodNonneg : 0 ≤ (1 - s) * y :=
      mul_nonneg (by linarith [hsUnit.2]) hyNonneg
    have hgap : 0 < (1 - s) * (1 - y) :=
      mul_pos (sub_pos.mpr hsUnit.2) (sub_pos.mpr hyLt)
    constructor
    · exact add_pos_of_pos_of_nonneg hs.1 hprodNonneg
    · nlinarith
  exact ⟨hB _ hyLeftNonneg hyLeftLt,
    hB _ hyRight.1.le hyRight.2⟩

lemma log40_le_log_four_div
    {s : ℝ} (hs : s ∈ Ioc (0 : ℝ) (1 / 10 : ℝ)) :
    Real.log 40 ≤ Real.log (4 / s) := by
  have harg : (40 : ℝ) ≤ 4 / s := by
    rw [le_div_iff₀ hs.1]
    nlinarith [hs.2]
  exact Real.log_le_log (by norm_num) harg

lemma q0_collection_lower
    {s chi : ℝ} (hs : s ∈ Ioc (0 : ℝ) (1 / 10 : ℝ))
    (hchi : chi ∈ Icc (0 : ℝ) 1) :
    s / 4 *
        (coreCoeff s chi * (Real.log 40 + 1) -
          leftCoeff s chi * Real.log (leftCoeff s chi) -
          rightCoeff s / v s chi * Real.log (rightCoeff s) +
          4 * slopeCoeff s chi * Real.log 2) ≤
      lrLowerFaceQ0 (s * leftCoeff s chi) +
        lrLowerFaceQ0 (s * rightCoeff s) / v s chi -
        slopeCoeff s chi *
          (lrLowerFaceQ0 s - s * Real.log 2) := by
  have hgeom := boundary_geometry hs hchi
  have hcoeff := coefficient_bounds hs hchi
  have hvPos : 0 < v s chi :=
    (by norm_num : (0 : ℝ) < 1 / 2).trans_le hgeom.2.2.1
  have hlog := log40_le_log_four_div hs
  have hcoreLog := mul_le_mul_of_nonneg_left hlog hcoeff.2.2.2.2
  have hinside :
      coreCoeff s chi * (Real.log 40 + 1) -
          leftCoeff s chi * Real.log (leftCoeff s chi) -
          rightCoeff s / v s chi * Real.log (rightCoeff s) +
          4 * slopeCoeff s chi * Real.log 2 ≤
        coreCoeff s chi * (Real.log (4 / s) + 1) -
          leftCoeff s chi * Real.log (leftCoeff s chi) -
          rightCoeff s / v s chi * Real.log (rightCoeff s) +
          4 * slopeCoeff s chi * Real.log 2 := by
    linarith
  have hscaled := mul_le_mul_of_nonneg_left hinside
    (div_nonneg hs.1.le (by norm_num : (0 : ℝ) ≤ 4))
  calc
    s / 4 *
        (coreCoeff s chi * (Real.log 40 + 1) -
          leftCoeff s chi * Real.log (leftCoeff s chi) -
          rightCoeff s / v s chi * Real.log (rightCoeff s) +
          4 * slopeCoeff s chi * Real.log 2) ≤
        s / 4 *
        (coreCoeff s chi * (Real.log (4 / s) + 1) -
          leftCoeff s chi * Real.log (leftCoeff s chi) -
          rightCoeff s / v s chi * Real.log (rightCoeff s) +
          4 * slopeCoeff s chi * Real.log 2) := hscaled
    _ = lrLowerFaceQ0 (s * leftCoeff s chi) +
        lrLowerFaceQ0 (s * rightCoeff s) / v s chi -
        slopeCoeff s chi *
          (lrLowerFaceQ0 s - s * Real.log 2) := by
      symm
      exact q0_collection_eq hs.1 hcoeff.1 hcoeff.2.1 hvPos

lemma remainder_collection_lower
    {s chi : ℝ} (hs : s ∈ Ioc (0 : ℝ) (1 / 10 : ℝ))
    (hchi : chi ∈ Icc (0 : ℝ) 1) :
    -s * ((2 / 15 : ℝ) * Real.log 40) ≤
      lrLowerFaceR0 (s * leftCoeff s chi) +
        lrLowerFaceR0 (s * rightCoeff s) / v s chi -
        slopeCoeff s chi * lrLowerFaceR0 s := by
  have hgeom := boundary_geometry hs hchi
  have hcoeff := coefficient_bounds hs hchi
  have hBmem := boundary_B_mem_Ioo hs hchi
  have hvPos : 0 < v s chi :=
    (by norm_num : (0 : ℝ) < 1 / 2).trans_le hgeom.2.2.1
  have hrLeft : 0 ≤ lrLowerFaceR0 (s * leftCoeff s chi) := by
    rw [← boundary_B_left]
    exact lrLowerFaceR0_nonneg hBmem.1
  have hrRight : 0 ≤ lrLowerFaceR0 (s * rightCoeff s) := by
    rw [← boundary_B_right]
    exact lrLowerFaceR0_nonneg hBmem.2
  have hrRightDiv : 0 ≤ lrLowerFaceR0 (s * rightCoeff s) / v s chi :=
    div_nonneg hrRight hvPos.le
  have hrS : 0 ≤ lrLowerFaceR0 s :=
    lrLowerFaceR0_nonneg ⟨hs.1, hs.2.trans_lt (by norm_num)⟩
  have hA := mul_le_mul_of_nonneg_right hcoeff.2.2.2.1 hrS
  have hrem := remainder_normalized_payment hs
  have hfour := mul_le_mul_of_nonneg_left hrem (by norm_num : (0 : ℝ) ≤ 4)
  have hcost : slopeCoeff s chi * lrLowerFaceR0 s ≤
      s * ((2 / 15 : ℝ) * Real.log 40) := by
    calc
      slopeCoeff s chi * lrLowerFaceR0 s ≤ 4 * lrLowerFaceR0 s := hA
      _ ≤ 4 * (s * ((1 / 30 : ℝ) * Real.log 40)) := hfour
      _ = s * ((2 / 15 : ℝ) * Real.log 40) := by ring
  linarith

lemma g0_collection_lower
    {s chi : ℝ} (hs : s ∈ Ioc (0 : ℝ) (1 / 10 : ℝ))
    (hchi : chi ∈ Icc (0 : ℝ) 1) :
    s * (-32 * (1 - s) * s * (1 - chi) ^ 2 /
        (x s chi ^ 2 * (1 + v s chi) ^ 2)) ≤
      (1 - s) * lrCertificateG0 (v s chi) := by
  have hgeom := boundary_geometry hs hchi
  have hg0 := lrCertificateG0_lower_quadratic hgeom.2.2
  have hvPlusNe : 1 + v s chi ≠ 0 := by
    have : 0 < v s chi :=
      (by norm_num : (0 : ℝ) < 1 / 2).trans_le hgeom.2.2.1
    linarith
  have hsOne : s < 1 := hs.2.trans_lt (by norm_num)
  have hmul := mul_le_mul_of_nonneg_left hg0
    (sub_nonneg.mpr hsOne.le)
  calc
    s * (-32 * (1 - s) * s * (1 - chi) ^ 2 /
        (x s chi ^ 2 * (1 + v s chi) ^ 2)) =
        (1 - s) * (-2 * (1 - v s chi) ^ 2) := by
      rw [one_sub_v_eq hs hchi]
      field_simp [hgeom.1.ne', hvPlusNe]
      ring
    _ ≤ (1 - s) * lrCertificateG0 (v s chi) := hmul

lemma boundary_gap_split (s chi : ℝ) :
    lrGapBudgetSEChi s (4 * s) chi =
      (1 - s) * lrCertificateG0 (v s chi) -
        s * (1 + v s chi) / v s chi *
          (Real.log 2 + 2 * logFactor s chi) +
        (lrLowerFaceQ0 (s * leftCoeff s chi) +
          lrLowerFaceQ0 (s * rightCoeff s) / v s chi -
          slopeCoeff s chi *
            (lrLowerFaceQ0 s - s * Real.log 2)) +
        (lrLowerFaceR0 (s * leftCoeff s chi) +
          lrLowerFaceR0 (s * rightCoeff s) / v s chi -
          slopeCoeff s chi * lrLowerFaceR0 s) := by
  unfold lrGapBudgetSEChi
  dsimp only
  rw [show 1 - chi * (4 * s) = x s chi by unfold x; ring]
  change (1 - s) * lrCertificateG0 (v s chi) +
      lrCertificateQ (lrCertificateB s (chi * (4 * s))) +
      lrCertificateQ (lrCertificateB s (4 * s)) / v s chi -
      s * (1 + v s chi) / v s chi *
        (Real.log 2 + 2 * logFactor s chi) -
      slopeCoeff s chi * (lrCertificateQ s - s * Real.log 2) = _
  rw [boundary_B_left, boundary_B_right,
    lrCertificateQ_eq_q0_add_r0,
    lrCertificateQ_eq_q0_add_r0,
    lrCertificateQ_eq_q0_add_r0]
  ring

/-- The elementary model is a rigorous normalized lower bound for the true
`k=4` gap budget. -/
theorem lowerModel_mul_le_gap
    {s chi : ℝ} (hs : s ∈ Ioc (0 : ℝ) (1 / 10 : ℝ))
    (hchi : chi ∈ Icc (0 : ℝ) 1) :
    s * lowerModel s chi ≤ lrGapBudgetSEChi s (4 * s) chi := by
  have hg0 := g0_collection_lower hs hchi
  have hq0 := q0_collection_lower hs hchi
  have hr0 := remainder_collection_lower hs hchi
  rw [boundary_gap_split]
  unfold lowerModel
  ring_nf at hg0 hq0 hr0 ⊢
  nlinarith

theorem gap_nonnegative_of_lowerModel
    {s chi : ℝ} (hs : s ∈ Ioc (0 : ℝ) (1 / 10 : ℝ))
    (hchi : chi ∈ Icc (0 : ℝ) 1)
    (hlower : 0 ≤ lowerModel s chi) :
    0 ≤ lrGapBudgetSEChi s (4 * s) chi := by
  exact (mul_nonneg hs.1.le hlower).trans (lowerModel_mul_le_gap hs hchi)

end LRGapBudgetSEFourBoundaryAnalytic
end CourtadeKumar
