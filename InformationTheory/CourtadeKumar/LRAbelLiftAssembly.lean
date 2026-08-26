import InformationTheory.CourtadeKumar.LRWSeries
import InformationTheory.CourtadeKumar.LRFlowCharts

/-! Assembly of the coefficientwise Abel lift into the actual LR flow reserve. -/

open Set

namespace CourtadeKumar

noncomputable def lrFlowPWExtended (R v t : ℝ) : ℝ :=
  lrWExtended R t + lrWExtended R (v * t) / v

noncomputable def lrFlowHExtended (R v t : ℝ) : ℝ :=
  let x := t ^ 2
  lrAbelBaseE v t - (1 + x) *
    ∑' n : ℕ, v ^ (2 * (n + 1)) * x ^ (n + 1) /
      (2 * ((n + 1 : ℕ) : ℝ)) * R ^ (n + 1)

noncomputable def lrFlowZExtended (R v t : ℝ) : ℝ :=
  t ^ 2 * lrGShape t v +
    (1 + t ^ 2) * lrFlowPWExtended R v t -
      4 * lrWExtended R 1 * t ^ 2

noncomputable def lrFlowAbelReserveExtended (R v t : ℝ) : ℝ :=
  lrFlowZExtended R v t + lrFlowQWeight v t * lrFlowHExtended R v t

theorem summable_lrFlowHExtended_tail
    {R v t : ℝ} (hR : R ∈ Ico (0 : ℝ) 1)
    (hv : v ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    Summable (fun n : ℕ ↦
      v ^ (2 * (n + 1)) * (t ^ 2) ^ (n + 1) /
        (2 * ((n + 1 : ℕ) : ℝ)) * R ^ (n + 1)) := by
  have hgeom : Summable (fun n : ℕ ↦ R * R ^ n) :=
    (summable_geometric_of_lt_one hR.1 hR.2).mul_left R
  apply Summable.of_norm_bounded hgeom
  intro n
  have hvpow : v ^ (2 * (n + 1)) ∈ Icc (0 : ℝ) 1 :=
    ⟨pow_nonneg hv.1 _, pow_le_one₀ hv.1 hv.2⟩
  have hx : t ^ 2 ∈ Icc (0 : ℝ) 1 :=
    ⟨pow_nonneg ht.1 _, pow_le_one₀ ht.1 ht.2⟩
  have hxpow : (t ^ 2) ^ (n + 1) ∈ Icc (0 : ℝ) 1 :=
    ⟨pow_nonneg hx.1 _, pow_le_one₀ hx.1 hx.2⟩
  have hnum : v ^ (2 * (n + 1)) * (t ^ 2) ^ (n + 1) ∈ Icc (0 : ℝ) 1 := by
    constructor
    · exact mul_nonneg hvpow.1 hxpow.1
    · nlinarith [mul_le_mul hvpow.2 hxpow.2 hxpow.1
        (by norm_num : (0 : ℝ) ≤ 1)]
  have hden : 1 ≤ 2 * ((n + 1 : ℕ) : ℝ) := by
    have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    push_cast
    nlinarith
  have hcoeff :
      v ^ (2 * (n + 1)) * (t ^ 2) ^ (n + 1) /
        (2 * ((n + 1 : ℕ) : ℝ)) ∈ Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg hnum.1 (by positivity)
    · rw [div_le_one (by positivity)]
      exact hnum.2.trans hden
  have hRpow : 0 ≤ R ^ (n + 1) := pow_nonneg hR.1 _
  calc
    ‖v ^ (2 * (n + 1)) * (t ^ 2) ^ (n + 1) /
        (2 * ((n + 1 : ℕ) : ℝ)) * R ^ (n + 1)‖ =
      (v ^ (2 * (n + 1)) * (t ^ 2) ^ (n + 1) /
        (2 * ((n + 1 : ℕ) : ℝ))) * R ^ (n + 1) := by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hcoeff.1 hRpow)]
    _ ≤ R ^ (n + 1) := by
      simpa using mul_le_mul_of_nonneg_right hcoeff.2 hRpow
    _ = R * R ^ n := by rw [pow_succ']

lemma lrFlowPWExtended_zero (v t : ℝ) :
    lrFlowPWExtended 0 v t = lrWZero t + lrWZero (v * t) / v := by
  simp [lrFlowPWExtended, lrWExtended_zero]

lemma lrFlowHExtended_zero (v t : ℝ) :
    lrFlowHExtended 0 v t = lrAbelBaseE v t := by
  simp [lrFlowHExtended]

theorem lrFlowAbelReserveExtended_zero_eq_base
    {v t : ℝ} (hv : 0 < v) :
    lrFlowAbelReserveExtended 0 v t = lrAbelBaseF v t := by
  rw [show lrFlowAbelReserveExtended 0 v t =
      lrFlowZExtended 0 v t + lrFlowQWeight v t * lrFlowHExtended 0 v t by rfl,
    lrFlowHExtended_zero, show lrFlowZExtended 0 v t =
      t ^ 2 * lrGShape t v +
        (1 + t ^ 2) * lrFlowPWExtended 0 v t -
          4 * lrWExtended 0 1 * t ^ 2 by rfl,
    lrFlowPWExtended_zero, lrWExtended_zero]
  unfold lrFlowQWeight lrWZero lrGShape lrAbelBaseF lrAbelBaseE
  dsimp only
  rw [topPhi_one]
  field_simp [hv.ne']
  ring

theorem lrWExtended_tail_hasSum
    {R z : ℝ} (hR : R ∈ Ico (0 : ℝ) 1) (hz : z ∈ Icc (0 : ℝ) 1) :
    HasSum (fun n : ℕ ↦ lrWOmega (n + 1) z * R ^ (n + 1))
      (lrWExtended R z - lrWZero z) := by
  have hs := summable_lrWExtended_tail hR hz
  convert hs.hasSum using 1
  unfold lrWExtended
  ring

theorem lrFlowHExtended_sub_base_hasSum
    {R v t : ℝ} (hR : R ∈ Ico (0 : ℝ) 1)
    (hv : v ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    HasSum (fun n : ℕ ↦
      -(1 + t ^ 2) *
        (v ^ (2 * (n + 1)) * (t ^ 2) ^ (n + 1) /
          (2 * ((n + 1 : ℕ) : ℝ)) * R ^ (n + 1)))
      (lrFlowHExtended R v t - lrAbelBaseE v t) := by
  have hs := summable_lrFlowHExtended_tail hR hv ht
  have h := hs.hasSum.mul_left (-(1 + t ^ 2))
  convert h using 1
  unfold lrFlowHExtended
  dsimp only
  ring

/-- Exact coefficient collection for the full `R`-lift. -/
theorem lrAbelC_hasSum_extended_reserve_sub_base
    {R v t : ℝ} (hR : R ∈ Ico (0 : ℝ) 1)
    (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasSum (fun n : ℕ ↦ lrAbelC (n + 1) v (t ^ 2) * R ^ (n + 1))
      (lrFlowAbelReserveExtended R v t - lrAbelBaseF v t) := by
  have hvClosed : v ∈ Icc (0 : ℝ) 1 := ⟨hv.1.le, hv.2.le⟩
  have htClosed : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2.le⟩
  have hvt : v * t ∈ Icc (0 : ℝ) 1 := by
    constructor
    · exact mul_nonneg hv.1.le ht.1.le
    · nlinarith [mul_le_mul hv.2.le ht.2.le ht.1.le (by norm_num : (0 : ℝ) ≤ 1)]
  have hWt := lrWExtended_tail_hasSum hR htClosed
  have hWvt := lrWExtended_tail_hasSum hR hvt
  have hWone := lrWExtended_tail_hasSum hR
    (show (1 : ℝ) ∈ Icc 0 1 by norm_num)
  have hPW := hWt.add (hWvt.mul_left (1 / v))
  have hZ := (hPW.mul_left (1 + t ^ 2)).sub (hWone.mul_left (4 * t ^ 2))
  have hH := lrFlowHExtended_sub_base_hasSum hR hvClosed htClosed
  have hReserve := hZ.add (hH.mul_left (lrFlowQWeight v t))
  convert hReserve using 1
  · funext n
    have hn : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
    have hvne : v ≠ 0 := hv.1.ne'
    have hvEvenStep : v ^ (2 * (n + 1)) =
        v ^ (2 * (n + 1) - 1) * v := by
      nth_rewrite 1 [show 2 * (n + 1) = (2 * (n + 1) - 1) + 1 by omega]
      exact pow_succ v _
    have hvPlusStep : v ^ (2 * (n + 1) + 2) =
        v ^ (2 * (n + 1) + 1) * v := by
      nth_rewrite 1 [show 2 * (n + 1) + 2 = (2 * (n + 1) + 1) + 1 by omega]
      exact pow_succ v _
    unfold lrAbelC lrWOmega lrAbelA lrAbelB lrAbelQ lrFlowQWeight
    norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    rw [show (v * t) ^ (2 * (n + 1)) =
          v ^ (2 * (n + 1)) * t ^ (2 * (n + 1)) by rw [mul_pow],
      show (v * t) ^ (2 * (n + 1) + 2) =
          v ^ (2 * (n + 1) + 2) * t ^ (2 * (n + 1) + 2) by rw [mul_pow]]
    rw [hvEvenStep, hvPlusStep]
    simp only [one_pow]
    rw [show t ^ (2 * (n + 1)) = (t ^ 2) ^ (n + 1) by rw [pow_mul],
      show t ^ (2 * (n + 1) + 2) = (t ^ 2) ^ (n + 1) * t ^ 2 by
        rw [pow_add, pow_mul]]
    field_simp [hvne, hn.ne']
    ring
  · have hbase := lrFlowAbelReserveExtended_zero_eq_base (v := v) (t := t) hv.1
    unfold lrFlowAbelReserveExtended lrFlowZExtended lrFlowPWExtended at hbase ⊢
    simp only [lrWExtended_zero, lrFlowHExtended_zero] at hbase
    rw [mul_comm v t] at hbase
    rw [← hbase]
    ring

/-- The extended reserve is exactly the positive base plus its convergent
coefficientwise lift. -/
theorem lrFlowAbelReserveExtended_eq_liftSeries
    {R v t : ℝ} (hR : R ∈ Ico (0 : ℝ) 1)
    (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    lrFlowAbelReserveExtended R v t = lrAbelBaseF v t +
      ∑' n : ℕ, lrAbelC (n + 1) v (t ^ 2) * R ^ (n + 1) := by
  have h := lrAbelC_hasSum_extended_reserve_sub_base hR hv ht
  rw [h.tsum_eq]
  ring

theorem lrFlowAbelReserveExtended_nonneg
    {R v t : ℝ} (hR : R ∈ Ico (0 : ℝ) 1)
    (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    0 ≤ lrFlowAbelReserveExtended R v t := by
  rw [lrFlowAbelReserveExtended_eq_liftSeries hR hv ht]
  exact lrAbelLiftSeries_nonneg hR hv ht

theorem lrFlowHLSeries_hasSum
    {R v t : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1)
    (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasSum (fun n : ℕ ↦
      v ^ (2 * (n + 1)) * (t ^ 2) ^ (n + 1) /
        (2 * ((n + 1 : ℕ) : ℝ)) * R ^ (n + 1))
      (lrL (Real.sqrt R * v * t)) := by
  have hsqrt0 : 0 < Real.sqrt R := Real.sqrt_pos.2 hR.1
  have hsqrt1 : Real.sqrt R < 1 := by
    simpa using (Real.sqrt_lt_sqrt_iff hR.1.le).2 hR.2
  have hz : Real.sqrt R * v * t ∈ Ioo (-1 : ℝ) 1 := by
    constructor
    · nlinarith [mul_pos (mul_pos hsqrt0 hv.1) ht.1]
    · have h₁ : Real.sqrt R * v < 1 := by
        nlinarith [mul_lt_mul_of_pos_right hsqrt1 hv.1,
          mul_lt_mul_of_pos_left hv.2 hsqrt0]
      nlinarith [mul_lt_mul_of_pos_right h₁ ht.1, ht.2]
  have h := lrL_hasSum hz
  convert h using 1
  funext n
  rw [mul_pow, mul_pow]
  rw [show Real.sqrt R ^ (2 * (n + 1)) = R ^ (n + 1) by
    rw [pow_mul, Real.sq_sqrt hR.1.le],
    show t ^ (2 * (n + 1)) = (t ^ 2) ^ (n + 1) by rw [pow_mul]]
  norm_num only [Nat.cast_add, Nat.cast_one]
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp [hn]

theorem lrFlowHExtended_eq_lrFlowH
    {R v t : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1)
    (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    lrFlowHExtended R v t = lrFlowH R v t := by
  have hL := lrFlowHLSeries_hasSum hR hv ht
  unfold lrFlowHExtended
  dsimp only
  rw [hL.tsum_eq]
  unfold lrFlowH lrFlowD lrFlowA lrFlowB lrFlowBeta lrAbelBaseE
  ring

theorem lrFlowPWExtended_eq_lrFlowPW
    {R v t : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1)
    (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    lrFlowPWExtended R v t = lrFlowPW R v t := by
  have hvt : v * t ∈ Ioc (0 : ℝ) 1 := by
    constructor
    · exact mul_pos hv.1 ht.1
    · nlinarith [mul_le_mul hv.2.le ht.2.le ht.1.le
        (by norm_num : (0 : ℝ) ≤ 1)]
  unfold lrFlowPWExtended lrFlowPW
  rw [lrWExtended_eq_lrWKernel hR
      (show t ∈ Ioc (0 : ℝ) 1 from ⟨ht.1, ht.2.le⟩),
    lrWExtended_eq_lrWKernel hR hvt]

theorem lrFlowZExtended_eq_lrFlowZ
    {R v t : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1)
    (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    lrFlowZExtended R v t = lrFlowZ R v t := by
  unfold lrFlowZExtended lrFlowZ
  rw [lrFlowPWExtended_eq_lrFlowPW hR hv ht,
    lrWExtended_eq_lrWKernel hR (show (1 : ℝ) ∈ Ioc 0 1 by norm_num)]

theorem lrFlowAbelReserveExtended_eq_actual
    {R v t : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1)
    (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    lrFlowAbelReserveExtended R v t =
      lrFlowZ R v t + lrFlowQWeight v t * lrFlowH R v t := by
  unfold lrFlowAbelReserveExtended
  rw [lrFlowZExtended_eq_lrFlowZ hR hv ht,
    lrFlowHExtended_eq_lrFlowH hR hv ht]

/-- The coefficientwise Abel-lift inequality for the actual LR flow on the
regular physical interior. -/
theorem lrFlow_noise_lift_nonneg
    {R v t : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1)
    (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    0 ≤ lrFlowZ R v t + lrFlowQWeight v t * lrFlowH R v t := by
  rw [← lrFlowAbelReserveExtended_eq_actual hR hv ht]
  exact lrFlowAbelReserveExtended_nonneg
    (show R ∈ Ico (0 : ℝ) 1 from ⟨hR.1.le, hR.2⟩) hv ht

end CourtadeKumar
