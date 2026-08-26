import InformationTheory.CourtadeKumar.LRFlowEll

/-! Finite coefficient inequalities in the audited Abel noise lift. -/

open Set Finset
open scoped BigOperators

namespace CourtadeKumar

noncomputable def lrGeomPrefix (n : ℕ) (v : ℝ) : ℝ :=
  ∑ r ∈ Finset.range n, v ^ r

noncomputable def lrAbelD₀ (j : ℕ) (v : ℝ) : ℝ :=
  lrGeomPrefix (2 * j) v -
    ((j : ℝ) - 1) / (2 * (j : ℝ) - 1) *
      lrGeomPrefix (2 * j - 1) v -
    (1 / 2 : ℝ) * v ^ (2 * j)

noncomputable def lrAbelD₁ (j : ℕ) (v : ℝ) : ℝ :=
  let m := 2 * j - 1
  1 / ((m : ℝ) * ((m : ℝ) + 2)) * lrGeomPrefix m v +
    (j : ℝ) / ((m : ℝ) + 2) * v ^ m -
    ((j : ℝ) + 1) / ((m : ℝ) + 2) * v ^ (m + 1)

lemma lrGeomPrefix_nonneg
    {n : ℕ} {v : ℝ} (hv : 0 ≤ v) :
    0 ≤ lrGeomPrefix n v := by
  unfold lrGeomPrefix
  exact Finset.sum_nonneg fun _ _ ↦ pow_nonneg hv _

lemma lrGeomPrefix_ge_card_mul_last
    {m : ℕ} {v : ℝ}
    (hv : v ∈ Icc (0 : ℝ) 1) :
    (m : ℝ) * v ^ (m - 1) ≤ lrGeomPrefix m v := by
  unfold lrGeomPrefix
  calc
    (m : ℝ) * v ^ (m - 1) =
        ∑ _r ∈ Finset.range m, v ^ (m - 1) := by simp
    _ ≤ ∑ r ∈ Finset.range m, v ^ r := by
      apply Finset.sum_le_sum
      intro r hr
      have hrlt : r < m := Finset.mem_range.mp hr
      have hrexp : r ≤ m - 1 := Nat.le_pred_of_lt hrlt
      exact pow_le_pow_of_le_one hv.1 hv.2 hrexp

theorem lrAbelD₀_nonneg
    {j : ℕ} (hj : 1 ≤ j) {v : ℝ}
    (hv : v ∈ Icc (0 : ℝ) 1) :
    0 ≤ lrAbelD₀ j v := by
  let m := 2 * j - 1
  have hmSucc : m + 1 = 2 * j := by dsimp [m]; omega
  have hcoef : ((j : ℝ) - 1) / (2 * (j : ℝ) - 1) ≤ 1 / 2 := by
    have hjReal : 1 ≤ (j : ℝ) := by exact_mod_cast hj
    have hden : 0 < 2 * (j : ℝ) - 1 := by
      nlinarith
    rw [div_le_iff₀ hden]
    nlinarith
  have hS : 0 ≤ lrGeomPrefix m v := lrGeomPrefix_nonneg hv.1
  have hpow : v ^ (m + 1) ≤ v ^ m :=
    pow_le_pow_of_le_one hv.1 hv.2 (Nat.le_succ m)
  unfold lrAbelD₀ lrGeomPrefix
  rw [← hmSucc, Finset.sum_range_succ]
  change 0 ≤
    ((∑ r ∈ Finset.range m, v ^ r) + v ^ m) -
      ((j : ℝ) - 1) / (2 * (j : ℝ) - 1) *
        (∑ r ∈ Finset.range m, v ^ r) -
      (1 / 2 : ℝ) * v ^ (m + 1)
  dsimp [lrGeomPrefix] at hS
  have hcoefTerm : 0 ≤
      ((1 / 2 : ℝ) - ((j : ℝ) - 1) / (2 * (j : ℝ) - 1)) *
        (∑ r ∈ Finset.range m, v ^ r) :=
    mul_nonneg (sub_nonneg.mpr hcoef) hS
  have hpowTerm : 0 ≤ (1 / 2 : ℝ) *
      (v ^ m - v ^ (m + 1)) :=
    mul_nonneg (by norm_num) (sub_nonneg.mpr hpow)
  have hvm : 0 ≤ v ^ m := pow_nonneg hv.1 m
  nlinarith

theorem lrAbelD₁_nonneg
    {j : ℕ} (hj : 1 ≤ j) {v : ℝ}
    (hv : v ∈ Icc (0 : ℝ) 1) :
    0 ≤ lrAbelD₁ j v := by
  let m := 2 * j - 1
  have hmpos : 0 < m := by dsimp [m]; omega
  have hmReal : 0 < (m : ℝ) := by exact_mod_cast hmpos
  have hmTwo : 0 < (m : ℝ) + 2 := by positivity
  have hS := lrGeomPrefix_ge_card_mul_last (m := m) hv
  have hcoef : 0 ≤ 1 / ((m : ℝ) * ((m : ℝ) + 2)) := by positivity
  have hfirst := mul_le_mul_of_nonneg_left hS hcoef
  have hdef : lrAbelD₁ j v =
      1 / ((m : ℝ) * ((m : ℝ) + 2)) * lrGeomPrefix m v +
        (j : ℝ) / ((m : ℝ) + 2) * v ^ m -
        ((j : ℝ) + 1) / ((m : ℝ) + 2) * v ^ (m + 1) := by
    rfl
  rw [hdef]
  have hlower :
      v ^ (m - 1) * (1 - v) * (1 + ((j : ℝ) + 1) * v) /
          ((m : ℝ) + 2) =
        1 / ((m : ℝ) * ((m : ℝ) + 2)) *
            ((m : ℝ) * v ^ (m - 1)) +
          (j : ℝ) / ((m : ℝ) + 2) * v ^ m -
          ((j : ℝ) + 1) / ((m : ℝ) + 2) * v ^ (m + 1) := by
    have hmPow : v ^ m = v ^ (m - 1) * v := by
      conv_lhs => rw [show m = (m - 1) + 1 by omega, pow_succ]
    have hmPowSucc : v ^ (m + 1) = v ^ (m - 1) * v ^ 2 := by
      rw [show m + 1 = (m - 1) + 2 by omega, pow_add]
    rw [hmPow, hmPowSucc]
    field_simp [hmReal.ne', hmTwo.ne']
    ring
  have hresidual : 0 ≤
      v ^ (m - 1) * (1 - v) * (1 + ((j : ℝ) + 1) * v) /
        ((m : ℝ) + 2) := by
    apply div_nonneg
    · exact mul_nonneg
        (mul_nonneg (pow_nonneg hv.1 _) (sub_nonneg.mpr hv.2))
        (add_nonneg zero_le_one (mul_nonneg (by positivity) hv.1))
    · exact hmTwo.le
  rw [hlower] at hresidual
  linarith

noncomputable def lrAbelCOne (j : ℕ) (x : ℝ) : ℝ :=
  x * (1 - x) ^ 2 /
      (2 * (j : ℝ) * (2 * (j : ℝ) - 1) * (2 * (j : ℝ) + 1)) *
    ((2 * (j : ℝ) - 1) * x ^ (j - 1) +
      4 * ∑ r ∈ Finset.range (j - 1), ((r : ℝ) + 1) * x ^ r)

theorem lrAbelCOne_nonneg
    {j : ℕ} (hj : 1 ≤ j) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) :
    0 ≤ lrAbelCOne j x := by
  have hjReal : 1 ≤ (j : ℝ) := by exact_mod_cast hj
  have hjPos : 0 < (j : ℝ) := lt_of_lt_of_le zero_lt_one hjReal
  have hleft : 0 < 2 * (j : ℝ) - 1 := by linarith
  have hright : 0 < 2 * (j : ℝ) + 1 := by linarith
  have hden : 0 <
      2 * (j : ℝ) * (2 * (j : ℝ) - 1) * (2 * (j : ℝ) + 1) := by
    exact mul_pos (mul_pos (mul_pos (by norm_num) hjPos) hleft) hright
  have hsum : 0 ≤
      ∑ r ∈ Finset.range (j - 1), ((r : ℝ) + 1) * x ^ r := by
    apply Finset.sum_nonneg
    intro r _
    exact mul_nonneg (by positivity) (pow_nonneg hx.1 r)
  have hbracket : 0 ≤
      (2 * (j : ℝ) - 1) * x ^ (j - 1) +
        4 * ∑ r ∈ Finset.range (j - 1), ((r : ℝ) + 1) * x ^ r := by
    exact add_nonneg
      (mul_nonneg hleft.le (pow_nonneg hx.1 _))
      (mul_nonneg (by norm_num) hsum)
  unfold lrAbelCOne
  exact mul_nonneg
    (div_nonneg (mul_nonneg hx.1 (sq_nonneg (1 - x))) hden.le)
    hbracket

noncomputable def lrAbelA (j : ℕ) : ℝ :=
  ((j : ℝ) - 1) / (2 * (j : ℝ) * (2 * (j : ℝ) - 1))

noncomputable def lrAbelB (j : ℕ) : ℝ :=
  1 / (2 * (2 * (j : ℝ) + 1))

noncomputable def lrAbelQ (v x : ℝ) : ℝ :=
  (1 - v) + (1 + v) / 2 * (1 - x)

noncomputable def lrAbelC (j : ℕ) (v x : ℝ) : ℝ :=
  (1 + x) * x ^ j *
      (lrAbelA j * (1 + v ^ (2 * j - 1)) -
        lrAbelB j * x * (1 + v ^ (2 * j + 1))) -
    4 * x * (lrAbelA j - lrAbelB j) -
    lrAbelQ v x * (1 + x) * v ^ (2 * j) * x ^ j /
      (2 * (j : ℝ))

lemma one_sub_mul_lrGeomPrefix (n : ℕ) (v : ℝ) :
    (1 - v) * lrGeomPrefix n v = 1 - v ^ n := by
  unfold lrGeomPrefix
  simpa using mul_neg_geom_sum v n

/-- The exact coefficient division in the audited noise lift, before
identifying the endpoint value at `v = 1`. -/
theorem lrAbelC_sub_one
    {j : ℕ} (hj : 1 ≤ j) (v x : ℝ) :
    lrAbelC j v x - lrAbelC j 1 x =
      (1 - v) * (1 + x) * x ^ j *
        (((1 - x) * lrAbelD₀ j v + x * lrAbelD₁ j v) /
          (2 * (j : ℝ))) := by
  have hjReal : 0 < (j : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hj)
  have hjOne : 1 ≤ (j : ℝ) := by exact_mod_cast hj
  have hodd : 2 * (j : ℝ) - 1 ≠ 0 := by nlinarith
  have hplus : 2 * (j : ℝ) + 1 ≠ 0 := by nlinarith
  have hoddNorm : -1 + (j : ℝ) * 2 ≠ 0 := by nlinarith
  have hplusNorm : 1 + (j : ℝ) * 2 ≠ 0 := by nlinarith
  have hcastOdd : ((2 * j - 1 : ℕ) : ℝ) = 2 * (j : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ 2 * j)]
    norm_num
  have hgeom0 := one_sub_mul_lrGeomPrefix (2 * j - 1) v
  have hgeom1 := one_sub_mul_lrGeomPrefix (2 * j) v
  have hpowOdd : v * v ^ (2 * j - 1) = v ^ (2 * j) := by
    rw [← pow_succ']
    congr 1
    omega
  have hoddStep : (1 - v) * v ^ (2 * j - 1) =
      v ^ (2 * j - 1) - v ^ (2 * j) := by
    rw [sub_mul, one_mul, hpowOdd]
  have hoddStepRev : v ^ (2 * j - 1) * (1 - v) =
      v ^ (2 * j - 1) - v ^ (2 * j) := by
    rw [mul_comm, hoddStep]
  have hoddScaled : (j : ℝ) * v ^ (2 * j - 1) * (1 - v) =
      (j : ℝ) * (v ^ (2 * j - 1) - v ^ (2 * j)) := by
    rw [mul_assoc, hoddStepRev]
  have hoddScaled2 :
      (j : ℝ) * v ^ (2 * j - 1) * (2 * (j : ℝ) - 1) * (1 - v) =
        (j : ℝ) * (2 * (j : ℝ) - 1) *
          (v ^ (2 * j - 1) - v ^ (2 * j)) := by
    calc
      _ = (j : ℝ) * (2 * (j : ℝ) - 1) *
          (v ^ (2 * j - 1) * (1 - v)) := by ring
      _ = _ := by rw [hoddStepRev]
  have hpowPlus : v ^ (2 * j + 1) = v * v ^ (2 * j) := by
    rw [pow_succ']
  have hevenStep : (1 - v) * v ^ (2 * j) =
      v ^ (2 * j) - v * v ^ (2 * j) := by ring
  have hevenScaled :
      (2 * (j : ℝ) - 1) * (1 - v) * v ^ (2 * j) =
        (2 * (j : ℝ) - 1) * (v ^ (2 * j) - v * v ^ (2 * j)) := by
    rw [mul_assoc, hevenStep]
  have hevenScaled2 :
      (2 * (j : ℝ) - 1) * (1 - v) * v ^ (2 * j) * ((j : ℝ) + 1) =
        (2 * (j : ℝ) - 1) *
          (v ^ (2 * j) - v * v ^ (2 * j)) * ((j : ℝ) + 1) := by
    rw [hevenScaled]
  have hD0mul :
      (1 - v) * lrAbelD₀ j v =
        (1 - v ^ (2 * j)) -
          ((j : ℝ) - 1) / (2 * (j : ℝ) - 1) *
            (1 - v ^ (2 * j - 1)) -
          (1 / 2 : ℝ) * (1 - v) * v ^ (2 * j) := by
    unfold lrAbelD₀
    calc
      (1 - v) *
          (lrGeomPrefix (2 * j) v -
            ((j : ℝ) - 1) / (2 * (j : ℝ) - 1) *
              lrGeomPrefix (2 * j - 1) v -
            (1 / 2 : ℝ) * v ^ (2 * j)) =
          (1 - v) * lrGeomPrefix (2 * j) v -
            ((j : ℝ) - 1) / (2 * (j : ℝ) - 1) *
              ((1 - v) * lrGeomPrefix (2 * j - 1) v) -
            (1 / 2 : ℝ) * (1 - v) * v ^ (2 * j) := by ring
      _ = _ := by rw [hgeom0, hgeom1]
  have hD1mul :
      (1 - v) * lrAbelD₁ j v =
        1 / ((2 * (j : ℝ) - 1) * (2 * (j : ℝ) + 1)) *
            (1 - v ^ (2 * j - 1)) +
          (j : ℝ) / (2 * (j : ℝ) + 1) *
            (1 - v) * v ^ (2 * j - 1) -
          ((j : ℝ) + 1) / (2 * (j : ℝ) + 1) *
            (1 - v) * v ^ (2 * j) := by
    unfold lrAbelD₁
    dsimp only
    rw [show 2 * j - 1 + 1 = 2 * j by omega, hcastOdd]
    calc
      (1 - v) *
          (1 / ((2 * (j : ℝ) - 1) * (2 * (j : ℝ) - 1 + 2)) *
              lrGeomPrefix (2 * j - 1) v +
            (j : ℝ) / (2 * (j : ℝ) - 1 + 2) * v ^ (2 * j - 1) -
            ((j : ℝ) + 1) / (2 * (j : ℝ) - 1 + 2) * v ^ (2 * j)) =
          1 / ((2 * (j : ℝ) - 1) * (2 * (j : ℝ) + 1)) *
              ((1 - v) * lrGeomPrefix (2 * j - 1) v) +
            (j : ℝ) / (2 * (j : ℝ) + 1) *
              (1 - v) * v ^ (2 * j - 1) -
            ((j : ℝ) + 1) / (2 * (j : ℝ) + 1) *
              (1 - v) * v ^ (2 * j) := by ring
      _ = _ := by rw [hgeom0]
  rw [show
    (1 - v) * (1 + x) * x ^ j *
        (((1 - x) * lrAbelD₀ j v + x * lrAbelD₁ j v) /
          (2 * (j : ℝ))) =
      (1 + x) * x ^ j *
        (((1 - x) * ((1 - v) * lrAbelD₀ j v) +
            x * ((1 - v) * lrAbelD₁ j v)) /
          (2 * (j : ℝ))) by ring]
  rw [hD0mul, hD1mul]
  unfold lrAbelC lrAbelA lrAbelB lrAbelQ
  simp only [one_pow]
  norm_num only [Nat.cast_mul, Nat.cast_ofNat]
  field_simp [hjReal.ne', hodd, hplus, hoddNorm, hplusNorm]
  field_simp [hjReal.ne', hodd, hplus, hoddNorm, hplusNorm]
  rw [hoddScaled2, hevenScaled2, hevenScaled, hpowPlus]
  rw [← hpowOdd]
  ring

lemma lrWeightedGeom_identity (n : ℕ) (x : ℝ) :
    (1 - x) ^ 2 *
        (∑ r ∈ Finset.range n, ((r : ℝ) + 1) * x ^ r) =
      1 - ((n : ℝ) + 1) * x ^ n + (n : ℝ) * x ^ (n + 1) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [Finset.sum_range_succ, mul_add, ih]
      norm_num only [Nat.cast_add, Nat.cast_one]
      rw [show n + 1 + 1 = n + 2 by omega]
      rw [show x ^ (n + 1) = x ^ n * x by rw [pow_succ]]
      rw [show x ^ (n + 2) = x ^ n * x ^ 2 by rw [pow_add]]
      ring

theorem lrAbelC_one_eq_endpoint
    {j : ℕ} (hj : 1 ≤ j) (x : ℝ) :
    lrAbelC j 1 x = lrAbelCOne j x := by
  have hjReal : 0 < (j : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hj)
  have hjOne : 1 ≤ (j : ℝ) := by exact_mod_cast hj
  have hodd : 2 * (j : ℝ) - 1 ≠ 0 := by nlinarith
  have hplus : 2 * (j : ℝ) + 1 ≠ 0 := by nlinarith
  have hsum := lrWeightedGeom_identity (j - 1) x
  have hcastPred : ((j - 1 : ℕ) : ℝ) = (j : ℝ) - 1 := by
    rw [Nat.cast_sub hj]
    norm_num
  have hxPred : x * x ^ (j - 1) = x ^ j := by
    rw [← pow_succ']
    congr 1
    omega
  rw [hcastPred] at hsum
  rw [show j - 1 + 1 = j by omega] at hsum
  have hsum' :
      (1 - x) ^ 2 *
          (∑ r ∈ Finset.range (j - 1), ((r : ℝ) + 1) * x ^ r) =
        1 - (j : ℝ) * x ^ (j - 1) +
          ((j : ℝ) - 1) * x ^ j := by
    convert hsum using 1
    all_goals ring
  have hbracket :
      (1 - x) ^ 2 *
          ((2 * (j : ℝ) - 1) * x ^ (j - 1) +
            4 * ∑ r ∈ Finset.range (j - 1), ((r : ℝ) + 1) * x ^ r) =
        (2 * (j : ℝ) - 1) * (1 - x) ^ 2 * x ^ (j - 1) +
          4 * (1 - (j : ℝ) * x ^ (j - 1) +
            ((j : ℝ) - 1) * x ^ j) := by
    calc
      _ = (2 * (j : ℝ) - 1) * (1 - x) ^ 2 * x ^ (j - 1) +
          4 * ((1 - x) ^ 2 *
            (∑ r ∈ Finset.range (j - 1), ((r : ℝ) + 1) * x ^ r)) := by ring
      _ = _ := by rw [hsum']
  unfold lrAbelC lrAbelA lrAbelB lrAbelQ lrAbelCOne
  simp only [one_pow]
  norm_num only
  field_simp [hjReal.ne', hodd, hplus]
  field_simp [hjReal.ne', hodd, hplus]
  rw [show
    x * (1 - x) ^ 2 *
        ((2 * (j : ℝ) - 1) * x ^ (j - 1) +
          4 * ∑ r ∈ Finset.range (j - 1), ((r : ℝ) + 1) * x ^ r) =
      x * ((1 - x) ^ 2 *
        ((2 * (j : ℝ) - 1) * x ^ (j - 1) +
          4 * ∑ r ∈ Finset.range (j - 1), ((r : ℝ) + 1) * x ^ r)) by ring]
  rw [hbracket]
  rw [← hxPred]
  ring

/-- Every lifted noise coefficient is nonnegative on the physical square. -/
theorem lrAbelC_nonneg
    {j : ℕ} (hj : 1 ≤ j) {v x : ℝ}
    (hv : v ∈ Icc (0 : ℝ) 1) (hx : x ∈ Icc (0 : ℝ) 1) :
    0 ≤ lrAbelC j v x := by
  have hD0 := lrAbelD₀_nonneg hj hv
  have hD1 := lrAbelD₁_nonneg hj hv
  have hcomb : 0 ≤
      (1 - x) * lrAbelD₀ j v + x * lrAbelD₁ j v :=
    add_nonneg
      (mul_nonneg (sub_nonneg.mpr hx.2) hD0)
      (mul_nonneg hx.1 hD1)
  have hjReal : 0 < (j : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hj)
  have hdelta : 0 ≤ lrAbelC j v x - lrAbelC j 1 x := by
    rw [lrAbelC_sub_one hj]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (sub_nonneg.mpr hv.2) (by linarith [hx.1]))
        (pow_nonneg hx.1 j))
      (div_nonneg hcomb (by positivity))
  have hone : 0 ≤ lrAbelC j 1 x := by
    rw [lrAbelC_one_eq_endpoint hj]
    exact lrAbelCOne_nonneg hj hx
  linarith

end CourtadeKumar
