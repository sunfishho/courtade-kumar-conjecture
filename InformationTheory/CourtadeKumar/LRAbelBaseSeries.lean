import InformationTheory.CourtadeKumar.LRAbelBaseCoefficients

/-! Analytic identification of the base Abel coefficient series. -/

open Set

namespace CourtadeKumar

noncomputable def lrAbelBaseE (v t : ℝ) : ℝ :=
  lrL (v * t) - t ^ 2 * Real.log (1 + v)

/-- The simplified manuscript expression `F_v(t²) = Z₀ + qE`. -/
noncomputable def lrAbelBaseF (v t : ℝ) : ℝ :=
  let x := t ^ 2
  let A := (3 - v) / 2
  let B := (1 + v) / 2
  topPhi t + topPhi (v * t) / v +
    x * (lrG v - 4 * (Real.log 2 - 1 / 2) - B) - B * x ^ 2 +
    (A - B * x) * lrAbelBaseE v t

/-- Power series for `L`, obtained directly from the kernel-checked logarithm
series. -/
theorem lrL_hasSum
    {z : ℝ} (hz : z ∈ Ioo (-1 : ℝ) 1) :
    HasSum (fun n : ℕ ↦
      z ^ (2 * (n + 1)) / (2 * ((n : ℝ) + 1))) (lrL z) := by
  have habs : |z ^ 2| < 1 := by
    rw [abs_pow]
    exact pow_lt_one₀ (abs_nonneg z) (by rw [abs_lt]; exact hz) (by norm_num)
  have h := Real.hasSum_pow_div_log_of_abs_lt_one (x := z ^ 2) habs
  have hhalf := h.mul_left (1 / 2 : ℝ)
  convert hhalf using 1
  · funext n
    rw [pow_mul]
    norm_num only [Nat.cast_add, Nat.cast_one]
    have hn : (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp [hn]
  · unfold lrL
    ring

/-- The two `Φ` contributions in the base reserve, expressed as a single
series in `x=t²`. -/
theorem lrAbelBasePhi_one_hasSum
    {v : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1) :
    HasSum (fun n : ℕ ↦
      (1 + v ^ (2 * (n + 1) - 1)) /
        (2 * ((n + 1 : ℕ) : ℝ) *
          (2 * ((n + 1 : ℕ) : ℝ) - 1)))
      (Real.log 2 + topPhi v / v) := by
  have hvMem : v ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hv.1], hv.2⟩
  have h := top_hasSum_phiCoefficients.add
    ((topPhi_hasSum hvMem).mul_left (1 / v))
  convert h using 1
  · funext n
    rw [show 2 * (n + 1) = (2 * (n + 1) - 1) + 1 by omega, pow_succ]
    have hn : (n : ℝ) + 1 ≠ 0 := by positivity
    have hodd : 2 * ((n : ℝ) + 1) - 1 ≠ 0 := by
      have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      nlinarith
    norm_num only [Nat.cast_add, Nat.cast_one]
    field_simp [hv.1.ne', hn, hodd]
    rw [show 2 * (n + 1) - 1 + 1 - 1 = 2 * (n + 1) - 1 by omega]
  · ring

theorem lrAbelBasePhi_hasSum
    {v t : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioc (0 : ℝ) 1)
    (hvt : v * t < 1) :
    HasSum (fun n : ℕ ↦
      (1 + v ^ (2 * (n + 1) - 1)) /
          (2 * ((n + 1 : ℕ) : ℝ) *
            (2 * ((n + 1 : ℕ) : ℝ) - 1)) *
        (t ^ 2) ^ (n + 1))
      (topPhi t + topPhi (v * t) / v) := by
  by_cases htOne : t = 1
  · subst t
    simpa using lrAbelBasePhi_one_hasSum hv
  have htLt : t < 1 := lt_of_le_of_ne ht.2 htOne
  have htMem : t ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [ht.1], htLt⟩
  have hvtMem : v * t ∈ Ioo (-1 : ℝ) 1 :=
    ⟨by nlinarith [mul_pos hv.1 ht.1], hvt⟩
  have h := (topPhi_hasSum htMem).add
    ((topPhi_hasSum hvtMem).mul_left (1 / v))
  convert h using 1
  · funext n
    rw [← pow_mul, mul_pow]
    rw [show 2 * (n + 1) = (2 * (n + 1) - 1) + 1 by omega, pow_succ]
    have hn : (n : ℝ) + 1 ≠ 0 := by positivity
    have hodd : 2 * ((n : ℝ) + 1) - 1 ≠ 0 := by
      have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      nlinarith
    norm_num only [Nat.cast_add, Nat.cast_one]
    field_simp [hv.1.ne', hn, hodd]
    rw [show 2 * (n + 1) - 1 + 1 - 1 = 2 * (n + 1) - 1 by omega,
      pow_succ]
    ring
  · ring

/-- Direct coefficient collection: the explicit audited coefficients sum to
the analytic base reserve `F_v(t²)`. -/
theorem lrAbelExplicitCoeff_hasSum
    {v t : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioc (0 : ℝ) 1) :
    HasSum (fun n : ℕ ↦
      lrAbelExplicitCoeff v n * (t ^ 2) ^ (n + 1))
      (lrAbelBaseF v t) := by
  let x : ℝ := t ^ 2
  let A : ℝ := (3 - v) / 2
  let B : ℝ := (1 + v) / 2
  let a : ℝ := Real.log (1 + v)
  let C : ℝ := lrG v - 4 * (Real.log 2 - 1 / 2) - B
  let p : ℕ → ℝ := fun n ↦
    (1 + v ^ (2 * (n + 1) - 1)) /
      (2 * ((n + 1 : ℕ) : ℝ) * (2 * ((n + 1 : ℕ) : ℝ) - 1)) *
        x ^ (n + 1)
  let ell : ℕ → ℝ := fun n ↦
    v ^ (2 * (n + 1)) / (2 * ((n : ℝ) + 1)) * x ^ (n + 1)
  let shiftedEll : ℕ → ℝ
    | 0 => 0
    | n + 1 => x * ell n
  let correction : ℕ → ℝ := fun n ↦
    (if n = 0 then (C - A * a) * x else 0) +
      (if n = 1 then (-B + B * a) * x ^ 2 else 0)
  have hvt : v * t ∈ Ioo (-1 : ℝ) 1 := by
    constructor
    · nlinarith [mul_pos hv.1 ht.1]
    · calc
        v * t ≤ v * 1 := mul_le_mul_of_nonneg_left ht.2 hv.1.le
        _ < 1 := by simpa using hv.2
  have hp : HasSum p (topPhi t + topPhi (v * t) / v) := by
    simpa [p, x] using lrAbelBasePhi_hasSum hv ht hvt.2
  have hell : HasSum ell (lrL (v * t)) := by
    have h := lrL_hasSum hvt
    convert h using 1
    funext n
    dsimp [ell, x]
    rw [mul_pow, ← pow_mul]
    ring
  have hshift : HasSum shiftedEll (x * lrL (v * t)) := by
    simpa [shiftedEll] using lr_hasSum_power_shift ell x (lrL (v * t)) hell
  have hcorr : HasSum correction
      ((C - A * a) * x + (-B + B * a) * x ^ 2) := by
    have hzero := hasSum_ite_eq (0 : ℕ) ((C - A * a) * x)
    have hone := hasSum_ite_eq (1 : ℕ) ((-B + B * a) * x ^ 2)
    simpa [correction] using hzero.add hone
  have htotal := hp.add (hell.mul_left A) |>.add (hshift.mul_left (-B)) |>.add hcorr
  convert htotal using 1
  · funext n
    change lrAbelExplicitCoeff v n * (t ^ 2) ^ (n + 1) =
      (p n + A * ell n + -B * shiftedEll n) + correction n
    rcases n with (_ | _ | n)
    · simp only [lrAbelExplicitCoeff, p, ell, shiftedEll, correction,
        Nat.cast_zero, zero_add, pow_one, if_pos]
      norm_num [x, A, B, a, C, lrAbelFirstPrefix, lrAbelCStar]
      ring
    · simp only [lrAbelExplicitCoeff, p, ell, shiftedEll, correction,
        if_pos]
      norm_num [x, A, B, a, C]
      ring
    · simp only [lrAbelExplicitCoeff, p, ell, shiftedEll, correction,
        Nat.succ_ne_zero, if_false]
      rw [if_neg (show n + 2 ≠ 1 by omega)]
      dsimp [x, A, B]
      norm_num only [Nat.cast_add, Nat.cast_ofNat]
      rw [show 2 * (n + 2 + 1) - 2 = 2 * (n + 2) by omega]
      simp only [← pow_mul]
      rw [show n + 1 + 1 + 1 = n + 3 by omega,
        show n + 1 + 1 = n + 2 by omega]
      ring_nf
      field_simp
      ring
  · unfold lrAbelBaseF lrAbelBaseE
    dsimp [x, A, B, a, C]
    ring

/-- The coefficients recovered from the positive prefixes therefore have
the analytic base reserve as their sum. -/
theorem lrAbelBaseCoeff_hasSum
    {v t : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioc (0 : ℝ) 1) :
    HasSum (fun n : ℕ ↦
      lrAbelBaseCoeff v n * (t ^ 2) ^ (n + 1))
      (lrAbelBaseF v t) := by
  convert lrAbelExplicitCoeff_hasSum hv ht using 1
  funext n
  rw [lrAbelBaseCoeff_eq_explicit]

theorem summable_lrAbelBaseCoeff
    {v : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1) :
    Summable (lrAbelBaseCoeff v) := by
  have h := lrAbelBaseCoeff_hasSum hv
    (show (1 : ℝ) ∈ Ioc 0 1 by norm_num)
  simpa using h.summable

/-- The positive-prefix series has the convergence required by infinite
Abel summation. -/
theorem summable_lrAbelBasePrefix_mul_pow
    {v t : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    Summable (fun n : ℕ ↦
      lrSeriesPrefix (lrAbelBaseCoeff v) n * (t ^ 2) ^ (n + 1)) := by
  let x : ℝ := t ^ 2
  let c : ℕ → ℝ := lrAbelBaseCoeff v
  have hc : Summable c := by simpa [c] using summable_lrAbelBaseCoeff hv
  let K : ℝ := ∑' n : ℕ, ‖c n‖
  have hK : 0 ≤ K := tsum_nonneg fun _ ↦ norm_nonneg _
  have hprefix : ∀ n : ℕ, ‖lrSeriesPrefix c n‖ ≤ K := by
    intro n
    calc
      ‖lrSeriesPrefix c n‖ = ‖∑ k ∈ Finset.range (n + 1), c k‖ := rfl
      _ ≤ ∑ k ∈ Finset.range (n + 1), ‖c k‖ := norm_sum_le _ _
      _ ≤ K := by
        dsimp [K]
        exact hc.norm.sum_le_tsum (Finset.range (n + 1))
          (fun _ _ ↦ abs_nonneg _)
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hx1 : x < 1 := by
    dsimp [x]
    nlinarith [ht.1, ht.2]
  have hgeom : Summable (fun n : ℕ ↦ K * x * x ^ n) :=
    (summable_geometric_of_lt_one hx0 hx1).mul_left (K * x)
  apply Summable.of_norm_bounded hgeom
  intro n
  have hxpow : 0 ≤ x ^ (n + 1) := pow_nonneg hx0 _
  calc
    ‖lrSeriesPrefix (lrAbelBaseCoeff v) n * (t ^ 2) ^ (n + 1)‖ =
        ‖lrSeriesPrefix c n‖ * x ^ (n + 1) := by
      simp only [c, x, norm_mul, Real.norm_eq_abs, abs_of_nonneg hxpow]
    _ ≤ K * x ^ (n + 1) := mul_le_mul_of_nonneg_right (hprefix n) hxpow
    _ = K * x * x ^ n := by rw [pow_succ']; ring

/-- The audited base reserve is nonnegative in the open physical square. -/
theorem lrAbelBaseF_nonneg
    {v t : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    0 ≤ lrAbelBaseF v t := by
  let x : ℝ := t ^ 2
  let A : ℝ := ∑' n : ℕ,
    lrSeriesPrefix (lrAbelBaseCoeff v) n * x ^ (n + 1)
  have hS : HasSum (fun n : ℕ ↦
      lrSeriesPrefix (lrAbelBaseCoeff v) n * x ^ (n + 1)) A := by
    have hsummable : Summable (fun n : ℕ ↦
        lrSeriesPrefix (lrAbelBaseCoeff v) n * x ^ (n + 1)) := by
      simpa [x] using summable_lrAbelBasePrefix_mul_pow hv ht
    exact hsummable.hasSum
  have hF : HasSum (fun n : ℕ ↦
      lrAbelBaseCoeff v n * x ^ (n + 1)) (lrAbelBaseF v t) := by
    simpa [x] using lrAbelBaseCoeff_hasSum hv
      (show t ∈ Ioc (0 : ℝ) 1 from ⟨ht.1, ht.2.le⟩)
  apply lr_abel_sum_nonneg (lrAbelBaseCoeff v) x A (lrAbelBaseF v t)
    (show x ∈ Icc (0 : ℝ) 1 by
      constructor
      · dsimp [x]; positivity
      · dsimp [x]; nlinarith [ht.1, ht.2])
    (fun n ↦ lrAbelBasePrefix_nonneg
      (show v ∈ Ioc (0 : ℝ) 1 from ⟨hv.1, hv.2.le⟩) n)
    hS hF

end CourtadeKumar
