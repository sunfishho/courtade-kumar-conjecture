import InformationTheory.CourtadeKumar.LRNegativeChartClosure

/-! Algebraic assembly of the positive-`J` midpoint chart. -/

open Set

namespace CourtadeKumar

noncomputable def lrFlowCcal (R v t : ℝ) : ℝ :=
  (1 - R) * (v ^ 2 * t ^ 2) / (2 * (1 - R * v ^ 2 * t ^ 2))

noncomputable def lrFlowUReserve (R v t : ℝ) : ℝ :=
  lrFlowB R v t * lrFlowY₀ R v t +
    lrFlowCcal R v t * lrFlowX₀ R v t

noncomputable def lrFlowHalfSlope (R v : ℝ) : ℝ :=
  -lrFlowEllDeriv R (lrFlowM v / 2)

noncomputable def lrFlowTReserve (R v t : ℝ) : ℝ :=
  4 * lrWKernel R 1 * lrFlowJ R v t * lrFlowGap R v t +
    lrFlowHalfSlope R v *
      lrFlowNumeratorP R (lrFlowM v) v t

lemma lrFlowQWeight_nonneg
    {v t : ℝ} (hv : v ∈ Ioc (0 : ℝ) 1)
    (ht : t ∈ Ioc (0 : ℝ) 1) :
    0 ≤ lrFlowQWeight v t := by
  unfold lrFlowQWeight
  have htSq : t ^ 2 ≤ 1 := by nlinarith [ht.1, ht.2]
  exact add_nonneg (sub_nonneg.mpr hv.2)
    (mul_nonneg
      (div_nonneg (by linarith [hv.1]) (by norm_num))
      (sub_nonneg.mpr htSq))

/-- The radial log increment dominates its terminal tangent. -/
theorem lrFlowCcal_le_lrFlowD
    {R v t : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1)
    (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    lrFlowCcal R v t ≤ lrFlowD R v t := by
  let ξ := v ^ 2 * t ^ 2
  have hxiPos : 0 < ξ := by
    unfold ξ
    exact mul_pos (sq_pos_of_pos hv.1) (sq_pos_of_pos ht.1)
  have hxiLt : ξ < 1 := by
    unfold ξ
    have hvt : v * t < 1 := by
      nlinarith [mul_lt_mul_of_pos_right hv.2 ht.1,
        mul_lt_mul_of_pos_left ht.2 hv.1]
    nlinarith [mul_pos hv.1 ht.1]
  have hdenOne : 0 < 1 - ξ := by linarith
  have hdenR : 0 < 1 - R * ξ := by
    have hmul : R * ξ < 1 := calc
      R * ξ < 1 * ξ := mul_lt_mul_of_pos_right hR.2 hxiPos
      _ < 1 := by simpa using hxiLt
    linarith
  have hlog := Real.log_le_sub_one_of_pos (div_pos hdenOne hdenR)
  rw [Real.log_div hdenOne.ne' hdenR.ne'] at hlog
  have hlogBound :
      (1 - R) * ξ / (1 - R * ξ) ≤
        Real.log (1 - R * ξ) - Real.log (1 - ξ) := by
    have hid :
        (1 - R) * ξ / (1 - R * ξ) =
          1 - (1 - ξ) / (1 - R * ξ) := by
      field_simp [hdenR.ne']
      ring
    rw [hid]
    linarith
  have hshape : Real.sqrt R * v * t ∈ Ioo (-1 : ℝ) 1 := by
    have hsqrt := lrB_sqrt_mem_Ioo hR
    constructor
    · nlinarith [mul_pos (mul_pos hsqrt.1 hv.1) ht.1]
    · have hvt : v * t < 1 := by
        nlinarith [mul_lt_mul_of_pos_right hv.2 ht.1,
          mul_lt_mul_of_pos_left ht.2 hv.1]
      calc
        Real.sqrt R * v * t = Real.sqrt R * (v * t) := by ring
        _ < 1 * (v * t) :=
          mul_lt_mul_of_pos_right hsqrt.2 (mul_pos hv.1 ht.1)
        _ < 1 := by simpa using hvt
  have hsqrtSq : (Real.sqrt R) ^ 2 = R := Real.sq_sqrt hR.1.le
  unfold lrFlowCcal lrFlowD lrFlowA lrFlowB
  rw [show lrFlowBeta v + lrL (v * t) -
      (lrFlowBeta v + lrL (Real.sqrt R * v * t)) =
      lrL (v * t) - lrL (Real.sqrt R * v * t) by ring]
  dsimp [ξ] at hlogBound
  unfold lrL
  rw [show (Real.sqrt R * v * t) ^ 2 = R * ξ by
    unfold ξ
    calc
      (Real.sqrt R * v * t) ^ 2 =
          (Real.sqrt R) ^ 2 * v ^ 2 * t ^ 2 := by ring
      _ = R * (v ^ 2 * t ^ 2) := by rw [hsqrtSq]; ring]
  have hhalf := mul_le_mul_of_nonneg_left hlogBound
    (show 0 ≤ (1 / 2 : ℝ) by norm_num)
  dsimp [ξ] at hhalf ⊢
  have hdenActual : 1 - R * (v ^ 2 * t ^ 2) ≠ 0 := by
    simpa [ξ] using hdenR.ne'
  convert hhalf using 1 <;> field_simp [hdenActual] <;> ring

theorem lrWKernel_one_pos
    {R : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1) :
    0 < lrWKernel R 1 := by
  have hsum := lrWZCoeff_one_hasSum hR
  have hnonneg : ∀ n : ℕ, 0 ≤ lrWZCoeff R (n + 2) :=
    fun n ↦ lrWZCoeff_nonneg hR.1.le n
  have hle : lrWZCoeff R 2 ≤ lrWKernel R 1 := by
    rw [← hsum.tsum_eq]
    have h := hsum.summable.sum_le_tsum ({0} : Finset ℕ)
      (fun n _ ↦ hnonneg n)
    simpa using h
  have hcoeff : 0 < lrWZCoeff R 2 := by
    unfold lrWZCoeff
    norm_num
    nlinarith [sq_pos_of_pos (sub_pos.mpr hR.2)]
  exact hcoeff.trans_le hle

lemma lrFlowHalfSlope_pos
    {R v : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1)
    (hv : v ∈ Ioo (0 : ℝ) 1) :
    0 < lrFlowHalfSlope R v := by
  unfold lrFlowHalfSlope
  apply neg_pos.mpr
  apply lrFlowEllDeriv_neg hR
  have hM := lrFlowM_mem_Ioc
    (show v ∈ Ioc (0 : ℝ) 1 from ⟨hv.1, hv.2.le⟩)
  constructor
  · exact div_pos hM.1 (by norm_num)
  · linarith [hM.2]

lemma lrFlowEllDeriv_le_of_le
    {R p q : ℝ} (hR : R ∈ Icc (0 : ℝ) 1)
    (hp : p ∈ Ioc (0 : ℝ) (1 / 2 : ℝ))
    (hq : q ∈ Ioc (0 : ℝ) (1 / 2 : ℝ))
    (hpq : p ≤ q) :
    lrFlowEllDeriv R p ≤ lrFlowEllDeriv R q := by
  have hmono : MonotoneOn (lrFlowEllDeriv R) (Icc p q) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc p q)
    · intro x hx
      exact (hasDerivAt_lrFlowEllDeriv
        (show x ∈ Ioo (0 : ℝ) 1 from
          ⟨lt_of_lt_of_le hp.1 hx.1,
            lt_of_le_of_lt (hx.2.trans hq.2) (by norm_num)⟩)).continuousAt
          |>.continuousWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      exact (hasDerivAt_lrFlowEllDeriv
        (show x ∈ Ioo (0 : ℝ) 1 from
          ⟨lt_trans hp.1 hx.1,
            lt_trans hx.2 (hq.2.trans_lt (by norm_num))⟩)).differentiableAt
          |>.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      rw [(hasDerivAt_lrFlowEllDeriv
        (show x ∈ Ioo (0 : ℝ) 1 from
          ⟨lt_trans hp.1 hx.1,
            lt_trans hx.2 (hq.2.trans_lt (by norm_num))⟩)).deriv]
      exact lrFlowEllDeriv2_nonneg hR
        (show x ∈ Ioc (0 : ℝ) (1 / 2 : ℝ) from
          ⟨lt_trans hp.1 hx.1, (hx.2.le.trans hq.2)⟩)
  exact hmono ⟨le_rfl, hpq⟩ ⟨hpq, le_rfl⟩ hpq

/-- The exact midpoint certificate `(U)` closes the first half of the
positive chart. -/
theorem lrFlowNumeratorP_halfMidpoint_nonneg_of_U
    {R v t : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1)
    (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1)
    (hJ : 0 < lrFlowJ R v t)
    (hU : 0 ≤ lrFlowUReserve R v t) :
    0 ≤ lrFlowNumeratorP R (lrFlowM v / 2) v t := by
  have hsqrt := lrB_sqrt_mem_Ioo hR
  have hvt : v * t < 1 := by
    nlinarith [mul_lt_mul_of_pos_right hv.2 ht.1,
      mul_lt_mul_of_pos_left ht.2 hv.1]
  have hshape : Real.sqrt R * v * t < 1 := by
    rw [mul_assoc]
    calc
      Real.sqrt R * (v * t) < 1 * (v * t) :=
        mul_lt_mul_of_pos_right hsqrt.2 (mul_pos hv.1 ht.1)
      _ < 1 := by simpa using hvt
  have hB : 0 < lrFlowB R v t := lrFlowB_pos hv.1 ht.1.le hshape
  have hCcal : 0 ≤ lrFlowCcal R v t := by
    unfold lrFlowCcal
    have hden : 0 < 1 - R * v ^ 2 * t ^ 2 := by
      have hsqrtSq : (Real.sqrt R) ^ 2 = R := Real.sq_sqrt hR.1.le
      have hshapeNonneg : 0 ≤ Real.sqrt R * v * t :=
        mul_nonneg (mul_nonneg (Real.sqrt_nonneg R) hv.1.le) ht.1.le
      have hshapeSq : (Real.sqrt R * v * t) ^ 2 < 1 := by
        nlinarith
      rw [show (Real.sqrt R * v * t) ^ 2 =
          (Real.sqrt R) ^ 2 * v ^ 2 * t ^ 2 by ring,
        hsqrtSq] at hshapeSq
      linarith
    exact div_nonneg
      (mul_nonneg (sub_nonneg.mpr hR.2.le)
        (mul_nonneg (sq_nonneg v) (sq_nonneg t)))
      (mul_nonneg (by norm_num) hden.le)
  have hDge := lrFlowCcal_le_lrFlowD hR hv ht
  have hAbel := lrFlow_noise_lift_nonneg hR hv ht
  have hq := lrFlowQWeight_nonneg
    (show v ∈ Ioc (0 : ℝ) 1 from ⟨hv.1, hv.2.le⟩)
    (show t ∈ Ioc (0 : ℝ) 1 from ⟨ht.1, ht.2.le⟩)
  have hZ : 0 ≤ lrFlowZ R v t := by
    have hH : lrFlowH R v t = -lrFlowJ R v t := lrFlowH_eq_negJ R v t
    rw [hH] at hAbel
    nlinarith [mul_nonneg hq hJ.le]
  have hmid := lrFlowNumeratorP_halfMidpoint
    (R := R) (v := v) (t := t) (by linarith [hv.1])
  by_cases hX : 0 ≤ lrFlowX₀ R v t
  · have hDX := mul_le_mul_of_nonneg_right hDge hX
    unfold lrFlowUReserve at hU
    rw [hmid]
    nlinarith
  · have hXnonpos : lrFlowX₀ R v t ≤ 0 := le_of_not_ge hX
    have hratio : lrFlowD R v t / lrFlowB R v t < t ^ 2 := by
      rw [div_lt_iff₀ hB]
      unfold lrFlowJ at hJ
      nlinarith
    have hratioX : t ^ 2 * lrFlowX₀ R v t ≤
        (lrFlowD R v t / lrFlowB R v t) * lrFlowX₀ R v t :=
      mul_le_mul_of_nonpos_right hratio.le hXnonpos
    have hYX : 0 ≤ lrFlowY₀ R v t +
        (lrFlowD R v t / lrFlowB R v t) * lrFlowX₀ R v t := by
      have hidentity := lrFlowY₀_add_t_sq_mul_X₀
        (R := R) (v := v) (t := t) (by linarith [hv.1])
      nlinarith
    have hscaled := mul_nonneg hB.le hYX
    rw [hmid]
    field_simp [hB.ne'] at hscaled
    nlinarith

/-- The manuscript's half-midpoint numerator and tangent certificate close
the positive-`J` chart. -/
theorem lrFlowNumeratorP_nonneg_of_J_pos_target_of_halfMidpoint_T
    {R p v t : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1)
    (hp : p ∈ Ioc (0 : ℝ) (1 / 2 : ℝ))
    (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1)
    (htarget : lrPrefixEll R p = lrSquareTarget R v t)
    (hJ : 0 < lrFlowJ R v t)
    (hhalfInput : 0 ≤
      lrFlowNumeratorP R (lrFlowM v / 2) v t)
    (hT : 0 ≤ lrFlowTReserve R v t) :
    0 ≤ lrFlowNumeratorP R p v t := by
  let M := lrFlowM v
  let g := lrFlowGap R v t
  let N : ℝ → ℝ := fun q ↦ lrFlowNumeratorP R q v t
  let k := 4 * lrWKernel R 1 * lrFlowJ R v t
  have hM : M ∈ Ioc (0 : ℝ) (1 / 2 : ℝ) := lrFlowM_mem_Ioc
    (show v ∈ Ioc (0 : ℝ) 1 from ⟨hv.1, hv.2.le⟩)
  have hg : 0 ≤ g := lrFlowGap_nonneg hR hv ht
  have hgapValue : g = lrPrefixEll R p - lrPrefixEll R M := by
    unfold g M lrFlowGap
    rw [htarget]
  have hpM : p ≤ M := by
    by_contra hnot
    have hMp : M < p := lt_of_not_ge hnot
    have hstrict := (strictAntiOn_lrPrefixEll hR) hM hp hMp
    linarith [hgapValue, hg]
  have hW : 0 < lrWKernel R 1 := lrWKernel_one_pos hR
  have hk : 0 < k := by
    unfold k
    positivity
  have hH : lrFlowH R v t = -lrFlowJ R v t := lrFlowH_eq_negJ R v t
  have hAffine (a b : ℝ) : N b - N a = -k * (b - a) := by
    have hsub := lrFlowNumeratorP_sub R a b v t
    unfold N k
    rw [hH] at hsub
    nlinarith
  by_cases hNM : 0 ≤ N M
  · have hmove := hAffine M p
    have hnonnegMove : 0 ≤ k * (M - p) :=
      mul_nonneg hk.le (sub_nonneg.mpr hpM)
    nlinarith
  · have hNMneg : N M < 0 := lt_of_not_ge hNM
    have hhalf : 0 ≤ N (M / 2) := by
      simpa [N, M] using hhalfInput
    have hhalfAffine := hAffine M (M / 2)
    have hhalfValue : N (M / 2) = N M + k * (M / 2) := by
      nlinarith [hhalfAffine]
    let d := -N M / k
    let π := M - d
    have hd : 0 < d := by
      unfold d
      exact div_pos (neg_pos.mpr hNMneg) hk
    have hdHalf : d ≤ M / 2 := by
      have hbound : -N M ≤ k * (M / 2) := by
        nlinarith [hhalf, hhalfValue]
      rw [show d = -N M / k by rfl]
      exact (div_le_iff₀ hk).2 (by nlinarith)
    have hπHalf : M / 2 ≤ π := by
      unfold π
      linarith
    have hπM : π < M := by
      unfold π
      linarith
    have hHalfMem : M / 2 ∈ Ioc (0 : ℝ) (1 / 2 : ℝ) := by
      constructor
      · exact div_pos hM.1 (by norm_num)
      · linarith [hM.2]
    have hπMem : π ∈ Ioc (0 : ℝ) (1 / 2 : ℝ) := by
      constructor
      · exact lt_of_lt_of_le hHalfMem.1 hπHalf
      · exact hπM.le.trans hM.2
    have hmhalf : 0 < lrFlowHalfSlope R v := lrFlowHalfSlope_pos hR hv
    have hgd : lrFlowHalfSlope R v * d ≤ g := by
      unfold lrFlowTReserve at hT
      change 0 ≤ k * g + lrFlowHalfSlope R v * N M at hT
      have hdValue : k * d = -N M := by
        unfold d
        field_simp [hk.ne']
      nlinarith [mul_nonneg hmhalf.le hd.le]
    have hRclosed : R ∈ Icc (0 : ℝ) 1 := ⟨hR.1.le, hR.2.le⟩
    have hderivHalf :
        lrFlowEllDeriv R (M / 2) ≤ lrFlowEllDeriv R π :=
      lrFlowEllDeriv_le_of_le hRclosed hHalfMem hπMem hπHalf
    have hslope := (convexOn_lrPrefixEll hRclosed).le_slope_of_hasDerivAt
      hπMem hM hπM
      (hasDerivAt_lrPrefixEll
        (show π ∈ Ioo (0 : ℝ) 1 from
          ⟨hπMem.1, hπMem.2.trans_lt (by norm_num)⟩))
    have hdist : M - π = d := by unfold π; ring
    rw [slope_def_field, hdist] at hslope
    have hslopeScaled :
        lrFlowEllDeriv R π * d ≤ lrPrefixEll R M - lrPrefixEll R π :=
      (le_div_iff₀ hd).mp hslope
    have hderivScaled := mul_le_mul_of_nonneg_right hderivHalf hd.le
    have hellπ :
        lrPrefixEll R π - lrPrefixEll R M ≤ lrFlowHalfSlope R v * d := by
      unfold lrFlowHalfSlope
      nlinarith
    have hellCompare : lrPrefixEll R π ≤ lrPrefixEll R p := by
      linarith [hgapValue, hgd, hellπ]
    have hpπ : p ≤ π := by
      by_contra hnot
      have hπp : π < p := lt_of_not_ge hnot
      have hstrict := (strictAntiOn_lrPrefixEll hR) hπMem hp hπp
      linarith
    have hmove := hAffine M p
    have hzero : N M + k * (M - π) = 0 := by
      rw [hdist]
      have hdValue : k * d = -N M := by
        unfold d
        field_simp [hk.ne']
      linarith
    have hmoveNonneg : 0 ≤ k * (π - p) :=
      mul_nonneg hk.le (sub_nonneg.mpr hpπ)
    nlinarith

/-- Compatibility wrapper: the older auxiliary `U` reserve implies the
actual half-midpoint numerator used by the manuscript certificate. -/
theorem lrFlowNumeratorP_nonneg_of_J_pos_target_of_U_T
    {R p v t : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1)
    (hp : p ∈ Ioc (0 : ℝ) (1 / 2 : ℝ))
    (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1)
    (htarget : lrPrefixEll R p = lrSquareTarget R v t)
    (hJ : 0 < lrFlowJ R v t)
    (hU : 0 ≤ lrFlowUReserve R v t)
    (hT : 0 ≤ lrFlowTReserve R v t) :
    0 ≤ lrFlowNumeratorP R p v t := by
  have hhalf := lrFlowNumeratorP_halfMidpoint_nonneg_of_U hR hv ht hJ hU
  exact lrFlowNumeratorP_nonneg_of_J_pos_target_of_halfMidpoint_T
    hR hp hv ht htarget hJ hhalf hT

/-- Once `(U)` and `(T)` are certified, all three sign charts combine into
one pointwise flow-numerator theorem. -/
theorem lrFlowNumeratorP_nonneg_target_of_U_T
    {R p v t : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1)
    (hp : p ∈ Ioc (0 : ℝ) (1 / 2 : ℝ))
    (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1)
    (htarget : lrPrefixEll R p = lrSquareTarget R v t)
    (hU : 0 ≤ lrFlowUReserve R v t)
    (hT : 0 ≤ lrFlowTReserve R v t) :
    0 ≤ lrFlowNumeratorP R p v t := by
  rcases lt_trichotomy (lrFlowJ R v t) 0 with hJneg | hJzero | hJpos
  · exact lrFlowNumeratorP_nonneg_of_J_neg_target hR hp hv ht htarget hJneg
  · exact lrFlowNumeratorP_nonneg_of_J_eq_zero_physical hR hv ht hJzero
  · exact lrFlowNumeratorP_nonneg_of_J_pos_target_of_U_T
      hR hp hv ht htarget hJpos hU hT

end CourtadeKumar
