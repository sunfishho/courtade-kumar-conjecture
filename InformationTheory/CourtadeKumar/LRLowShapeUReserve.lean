import InformationTheory.CourtadeKumar.LRLowShapeUPSeries
import InformationTheory.CourtadeKumar.LRPositiveChartAssembly

/-!
# The low-shape `U` reserve

This file resums the coefficientwise low-shape certificate and proves that the
analytic reserve `lrFlowUReserve` is nonnegative when `t ^ 2 ≤ 17 / 20`.
-/

open Set
open scoped BigOperators

namespace CourtadeKumar

noncomputable def lrLowBFlowCoeff (beta xi : ℝ) : ℕ → ℝ
  | 0 => beta
  | n + 1 => xi ^ (n + 1) / (2 * ((n + 1 : ℕ) : ℝ))

noncomputable def lrLowCcalCoeff (xi : ℝ) : ℕ → ℝ
  | 0 => xi / 2
  | n + 1 => -(1 - xi) * xi ^ (n + 1) / 2

noncomputable def lrLowYCoeff (v x : ℝ) (n : ℕ) : ℝ :=
  ((n + 1 : ℕ) : ℝ) * lrLowEta v x (n + 1)

noncomputable def lrLowXCoeff (v x G : ℝ) (n : ℕ) : ℝ :=
  ((n + 1 : ℕ) : ℝ) * lrLowR v x G (n + 1)

lemma lrLow_weighted_geometric_hasSum
    {R : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1) :
    HasSum (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ) * R ^ n)
      (1 / (1 - R) ^ 2) := by
  have hnorm : ‖R‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hR.1.le]
    exact hR.2
  have hn := hasSum_coe_mul_geometric_of_norm_lt_one hnorm
  have hg := hasSum_geometric_of_norm_lt_one hnorm
  convert hn.add hg using 1
  · funext n
    norm_num only [Nat.cast_add, Nat.cast_one]
    ring
  · have hden : 1 - R ≠ 0 := sub_ne_zero.mpr hR.2.ne'
    field_simp [hden]
    ring

theorem lrLowBFlowCoeff_hasSum
    {R v t : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1)
    (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasSum (fun n : ℕ ↦
      lrLowBFlowCoeff (lrFlowBeta v) (v ^ 2 * t ^ 2) n * R ^ n)
      (lrFlowB R v t) := by
  have hshape : Real.sqrt R * v * t ∈ Ioo (-1 : ℝ) 1 := by
    have hsqrt := lrB_sqrt_mem_Ioo hR
    constructor
    · nlinarith [mul_pos (mul_pos hsqrt.1 hv.1) ht.1]
    · calc
        Real.sqrt R * v * t = Real.sqrt R * (v * t) := by ring
        _ < 1 * (v * t) :=
          mul_lt_mul_of_pos_right hsqrt.2 (mul_pos hv.1 ht.1)
        _ < 1 := by
          have hvt : v * t < 1 := calc
            v * t < 1 * t := mul_lt_mul_of_pos_right hv.2 ht.1
            _ < 1 := by simpa using ht.2
          simpa using hvt
  have hL := lrL_hasSum hshape
  let tail : ℕ → ℝ := fun n ↦
    (v ^ 2 * t ^ 2) ^ (n + 1) /
      (2 * ((n + 1 : ℕ) : ℝ)) * R ^ (n + 1)
  have htail : HasSum tail (lrL (Real.sqrt R * v * t)) := by
    convert hL using 1
    funext n
    dsimp [tail]
    rw [show (Real.sqrt R * v * t) ^ (2 * (n + 1)) =
        R ^ (n + 1) * (v ^ 2 * t ^ 2) ^ (n + 1) by
      rw [show Real.sqrt R * v * t = Real.sqrt R * (v * t) by ring,
        mul_pow, pow_mul, Real.sq_sqrt hR.1.le, mul_pow, pow_mul]
      ring]
    norm_num only [Nat.cast_add, Nat.cast_one]
    ring
  let b : ℕ → ℝ
    | 0 => lrFlowBeta v
    | n + 1 => tail n
  have hshift : HasSum (fun n : ℕ ↦ b (n + 1))
      (lrL (Real.sqrt R * v * t)) := by simpa [b] using htail
  have hfull := (hasSum_nat_add_iff (f := b) 1).mp hshift
  convert hfull using 1
  · funext n
    rcases n with _ | n
    · simp [b, lrLowBFlowCoeff]
    · simp [b, tail, lrLowBFlowCoeff]
  · simp [b, lrFlowB]
    ring

theorem lrLowCcalCoeff_hasSum
    {R xi : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1)
    (hxi : xi ∈ Ioo (0 : ℝ) 1) :
    HasSum (fun n : ℕ ↦ lrLowCcalCoeff xi n * R ^ n)
      ((1 - R) * xi / (2 * (1 - R * xi))) := by
  have hq : R * xi ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · exact mul_pos hR.1 hxi.1
    · calc
        R * xi < 1 * xi := mul_lt_mul_of_pos_right hR.2 hxi.1
        _ < 1 := by simpa using hxi.2
  have hgeom := hasSum_geometric_of_lt_one hq.1.le hq.2
  let tail : ℕ → ℝ := fun n ↦
    -(1 - xi) * xi ^ (n + 1) / 2 * R ^ (n + 1)
  have htail : HasSum tail
      (-(1 - xi) * (R * xi) / (2 * (1 - R * xi))) := by
    convert hgeom.mul_left (-(1 - xi) * (R * xi) / 2) using 1
    · funext n
      dsimp [tail]
      rw [mul_pow, pow_succ R n, pow_succ xi n]
      ring
    · field_simp [show 1 - R * xi ≠ 0 by linarith [hq.2]]
  let c : ℕ → ℝ
    | 0 => xi / 2
    | n + 1 => tail n
  have hshift : HasSum (fun n : ℕ ↦ c (n + 1))
      (-(1 - xi) * (R * xi) / (2 * (1 - R * xi))) := by
    simpa [c] using htail
  have hfull := (hasSum_nat_add_iff (f := c) 1).mp hshift
  convert hfull using 1
  · funext n
    rcases n with _ | n
    · simp [c, lrLowCcalCoeff]
    · simp [c, tail, lrLowCcalCoeff]
  · simp [c]
    field_simp [show 1 - R * xi ≠ 0 by linarith [hq.2]]
    ring

theorem lrLowYCoeff_hasSum
    {R v t : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1)
    (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasSum (fun n : ℕ ↦ lrLowYCoeff v (t ^ 2) n * R ^ n)
      (lrFlowY₀ R v t / (1 - R) ^ 2) := by
  have hp := lrLowP_derivative_hasSum hR hv ht
  have hb := lrLowB_derivative_hasSum hR
  have h := hp.sub (hb.mul_left (2 * lrFlowM v * t ^ 2))
  convert h using 1
  · funext n
    unfold lrLowYCoeff lrLowEta
    ring
  · unfold lrFlowY₀
    field_simp [show (1 - R) ^ 2 ≠ 0 by
      exact pow_ne_zero 2 (sub_ne_zero.mpr hR.2.ne')]

theorem lrLowXCoeff_hasSum
    {R v t : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1)
    (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasSum (fun n : ℕ ↦
      lrLowXCoeff v (t ^ 2) (lrGShape t v) n * R ^ n)
      (lrFlowX₀ R v t / (1 - R) ^ 2) := by
  have hg := (lrLow_weighted_geometric_hasSum hR).mul_left (lrGShape t v)
  have hp := lrLowP_derivative_hasSum hR hv ht
  have hb := lrLowB_derivative_hasSum hR
  have h := hg.add hp |>.sub (hb.mul_left (lrLowTailH v))
  convert h using 1
  · funext n
    unfold lrLowXCoeff lrLowR
    ring
  · unfold lrFlowX₀ lrFlowC lrLowTailH
    have hdenV : 1 + v ≠ 0 := by linarith [hv.1]
    have hdenR : (1 - R) ^ 2 ≠ 0 :=
      pow_ne_zero 2 (sub_ne_zero.mpr hR.2.ne')
    field_simp [hdenV, hdenR]
    unfold lrFlowM
    field_simp [hdenV]
    ring

lemma lrLowU_productCoeff_identity
    (beta xi R : ℝ) (eta r : ℕ → ℝ) (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1),
        (lrLowBFlowCoeff beta xi k * R ^ k) *
          (((n - k + 1 : ℕ) : ℝ) * eta (n - k + 1) * R ^ (n - k))) +
      (∑ k ∈ Finset.range (n + 1),
        (lrLowCcalCoeff xi k * R ^ k) *
          (((n - k + 1 : ℕ) : ℝ) * r (n - k + 1) * R ^ (n - k))) =
      lrLowUConvolutionCoeff beta xi eta r n * R ^ n := by
  have hBY :
      ∑ k ∈ Finset.range (n + 1),
          (lrLowBFlowCoeff beta xi k * R ^ k) *
            (((n - k + 1 : ℕ) : ℝ) * eta (n - k + 1) * R ^ (n - k)) =
        (beta * (n + 1) * eta (n + 1) +
          ∑ k ∈ Finset.range n,
            xi ^ (k + 1) / (2 * ((k + 1 : ℕ) : ℝ)) *
              ((n - k : ℕ) : ℝ) * eta (n - k)) * R ^ n := by
    rw [Finset.sum_range_succ', add_comm]
    simp only [lrLowBFlowCoeff, pow_zero, mul_one, Nat.sub_zero]
    rw [add_mul, Finset.sum_mul]
    norm_num only [Nat.cast_add, Nat.cast_one]
    congr 1
    · ring
    · apply Finset.sum_congr rfl
      intro k hk
      have hklt : k < n := Finset.mem_range.mp hk
      have hindex : n - (k + 1) + 1 = n - k := by omega
      have hcast : ((n - (k + 1) : ℕ) : ℝ) + 1 = ((n - k : ℕ) : ℝ) := by
        exact_mod_cast hindex
      have hpow : R ^ (k + 1) * R ^ (n - (k + 1)) = R ^ n := by
        rw [← pow_add]
        congr 1
        omega
      rw [hindex, hcast]
      calc
        _ = xi ^ (k + 1) / (2 * (((k : ℕ) : ℝ) + 1)) *
              ((n - k : ℕ) : ℝ) * eta (n - k) *
              (R ^ (k + 1) * R ^ (n - (k + 1))) := by ring
        _ = _ := by rw [hpow]
  have hCX :
      ∑ k ∈ Finset.range (n + 1),
          (lrLowCcalCoeff xi k * R ^ k) *
            (((n - k + 1 : ℕ) : ℝ) * r (n - k + 1) * R ^ (n - k)) =
        (xi / 2 * (n + 1) * r (n + 1) +
          ∑ k ∈ Finset.range n,
            -((1 - xi) * xi ^ (k + 1) / 2 *
              ((n - k : ℕ) : ℝ) * r (n - k))) * R ^ n := by
    rw [Finset.sum_range_succ', add_comm]
    simp only [lrLowCcalCoeff, pow_zero, mul_one, Nat.sub_zero]
    rw [add_mul, Finset.sum_mul]
    norm_num only [Nat.cast_add, Nat.cast_one]
    congr 1
    · ring
    · apply Finset.sum_congr rfl
      intro k hk
      have hklt : k < n := Finset.mem_range.mp hk
      have hindex : n - (k + 1) + 1 = n - k := by omega
      have hcast : ((n - (k + 1) : ℕ) : ℝ) + 1 = ((n - k : ℕ) : ℝ) := by
        exact_mod_cast hindex
      have hpow : R ^ (k + 1) * R ^ (n - (k + 1)) = R ^ n := by
        rw [← pow_add]
        congr 1
        omega
      rw [hindex, hcast]
      calc
        _ = -((1 - xi) * xi ^ (k + 1) / 2 *
              ((n - k : ℕ) : ℝ) * r (n - k)) *
              (R ^ (k + 1) * R ^ (n - (k + 1))) := by ring
        _ = _ := by rw [hpow]
  have hneg :
      (∑ k ∈ Finset.range n,
          -((1 - xi) * xi ^ (k + 1) / 2 *
            ((n - k : ℕ) : ℝ) * r (n - k))) =
        -(∑ k ∈ Finset.range n,
          (1 - xi) * xi ^ (k + 1) / 2 *
            ((n - k : ℕ) : ℝ) * r (n - k)) := by
    rw [Finset.sum_neg_distrib]
  rw [hBY, hCX]
  rw [hneg]
  unfold lrLowUConvolutionCoeff
  rw [Finset.sum_sub_distrib]
  ring

theorem lrLowUReserve_hasSum
    {R v t : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1)
    (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasSum (fun n : ℕ ↦
      lrLowUConvolutionCoeff (lrFlowBeta v) (v ^ 2 * t ^ 2)
        (lrLowEta v (t ^ 2))
        (lrLowR v (t ^ 2) (lrGShape t v)) n * R ^ n)
      (lrFlowUReserve R v t / (1 - R) ^ 2) := by
  let b : ℕ → ℝ := fun n ↦
    lrLowBFlowCoeff (lrFlowBeta v) (v ^ 2 * t ^ 2) n * R ^ n
  let y : ℕ → ℝ := fun n ↦ lrLowYCoeff v (t ^ 2) n * R ^ n
  let c : ℕ → ℝ := fun n ↦ lrLowCcalCoeff (v ^ 2 * t ^ 2) n * R ^ n
  let x : ℕ → ℝ := fun n ↦
    lrLowXCoeff v (t ^ 2) (lrGShape t v) n * R ^ n
  have hb : HasSum b (lrFlowB R v t) := by
    simpa [b] using lrLowBFlowCoeff_hasSum hR hv ht
  have hy : HasSum y (lrFlowY₀ R v t / (1 - R) ^ 2) := by
    simpa [y] using lrLowYCoeff_hasSum hR hv ht
  have hxi : v ^ 2 * t ^ 2 ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · exact mul_pos (sq_pos_of_pos hv.1) (sq_pos_of_pos ht.1)
    · have hvSq : v ^ 2 < 1 := by
        nlinarith [mul_pos (sub_pos.mpr hv.2) (by linarith [hv.1] : 0 < 1 + v)]
      have htSq : t ^ 2 < 1 := by
        nlinarith [mul_pos (sub_pos.mpr ht.2) (by linarith [ht.1] : 0 < 1 + t)]
      calc
        v ^ 2 * t ^ 2 < 1 * t ^ 2 :=
          mul_lt_mul_of_pos_right hvSq (sq_pos_of_pos ht.1)
        _ < 1 := by simpa using htSq
  have hc : HasSum c (lrFlowCcal R v t) := by
    have h := lrLowCcalCoeff_hasSum hR hxi
    convert h using 1
    · unfold lrFlowCcal
      ring
  have hx : HasSum x (lrFlowX₀ R v t / (1 - R) ^ 2) := by
    simpa [x] using lrLowXCoeff_hasSum hR hv ht
  have hbyProd : Summable (fun q : ℕ × ℕ ↦ b q.1 * y q.2) :=
    summable_mul_of_summable_norm hb.summable.norm hy.summable.norm
  have hcxProd : Summable (fun q : ℕ × ℕ ↦ c q.1 * x q.2) :=
    summable_mul_of_summable_norm hc.summable.norm hx.summable.norm
  have hbySumm : Summable (fun n : ℕ ↦
      ∑ k ∈ Finset.range (n + 1), b k * y (n - k)) :=
    summable_sum_mul_range_of_summable_mul hbyProd
  have hcxSumm : Summable (fun n : ℕ ↦
      ∑ k ∈ Finset.range (n + 1), c k * x (n - k)) :=
    summable_sum_mul_range_of_summable_mul hcxProd
  have hbyValue := hb.summable.tsum_mul_tsum_eq_tsum_sum_range
    hy.summable hbyProd
  have hcxValue := hc.summable.tsum_mul_tsum_eq_tsum_sum_range
    hx.summable hcxProd
  rw [hb.tsum_eq, hy.tsum_eq] at hbyValue
  rw [hc.tsum_eq, hx.tsum_eq] at hcxValue
  have hby : HasSum (fun n : ℕ ↦
      ∑ k ∈ Finset.range (n + 1), b k * y (n - k))
      (lrFlowB R v t * (lrFlowY₀ R v t / (1 - R) ^ 2)) := by
    rw [hbyValue]
    exact hbySumm.hasSum
  have hcx : HasSum (fun n : ℕ ↦
      ∑ k ∈ Finset.range (n + 1), c k * x (n - k))
      (lrFlowCcal R v t * (lrFlowX₀ R v t / (1 - R) ^ 2)) := by
    rw [hcxValue]
    exact hcxSumm.hasSum
  have hsum := hby.add hcx
  convert hsum using 1
  · funext n
    dsimp [b, y, c, x, lrLowYCoeff, lrLowXCoeff]
    exact (lrLowU_productCoeff_identity
      (lrFlowBeta v) (v ^ 2 * t ^ 2) R
      (lrLowEta v (t ^ 2))
      (lrLowR v (t ^ 2) (lrGShape t v)) n).symm
  · unfold lrFlowUReserve
    have hden : (1 - R) ^ 2 ≠ 0 :=
      pow_ne_zero 2 (sub_ne_zero.mpr hR.2.ne')
    field_simp [hden]

theorem lrFlowUReserve_nonneg_lowShape
    {R v t : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1)
    (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1)
    (htSq : t ^ 2 ≤ (17 / 20 : ℝ)) :
    0 ≤ lrFlowUReserve R v t := by
  have hsum := lrLowUReserve_hasSum hR hv ht
  have hseries : 0 ≤ lrFlowUReserve R v t / (1 - R) ^ 2 :=
    hsum.nonneg (fun n ↦ mul_nonneg (by
      rw [lrLowUConvolutionCoeff_eq_signExplicit]
      exact lrLowU_actual_nonneg hv ht htSq (by omega))
      (pow_nonneg hR.1.le n))
  have hden : 0 < (1 - R) ^ 2 := sq_pos_of_pos (sub_pos.mpr hR.2)
  have hmul := mul_nonneg hseries hden.le
  rw [div_mul_cancel₀ _ hden.ne'] at hmul
  exact hmul

end CourtadeKumar
