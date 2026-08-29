import InformationTheory.CourtadeKumar.LRDeterminantAnalyticTailPrimitives

/-!
# Thick-reserve lower bound for the determinant proof

This proves the shared assertions of the audited quantitative thick-reserve
lemma.  For `G_t ≥ Q(e)`, the auxiliary gap is antitone in `t`; its endpoint
at `t = 1` is nonnegative because that endpoint is antitone in `v` and
vanishes at `v = 1`.  The second reserve estimate follows from the exact
certificate-coordinate cancellation after bounding `G_t` below by the
midpoint residual `f₀(v)`.
-/

open Set

namespace CourtadeKumar

noncomputable def lrDeterminantThickGap (v t : ℝ) : ℝ :=
  lrG v - Real.log 2 - topPhi t +
    (1 - 1 / v) * topPhi (v * t)

noncomputable def lrDeterminantThickGapOne (v : ℝ) : ℝ :=
  lrDeterminantThickGap v 1

theorem hasDerivAt_lrDeterminantThickGapOne
    {v : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt lrDeterminantThickGapOne
      (-((1 - v ^ 2) * Real.artanh v) / v ^ 2) v := by
  have hvNe := hv.1.ne'
  have hvFull : v ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hv.1], hv.2⟩
  have hG := hasDerivAt_lrG hv.1
  have hcoeff : HasDerivAt (fun x : ℝ ↦ 1 - 1 / x)
      (1 / v ^ 2) v := by
    have hinv := (hasDerivAt_const v (1 : ℝ)).div (hasDerivAt_id v) hvNe
    convert (hasDerivAt_const v 1).sub hinv using 1 <;>
      simp only [id_eq] <;> field_simp [hvNe] <;> ring
  have hphi := hasDerivAt_topPhi hvFull
  have h := (((hG.sub_const (Real.log 2)).sub_const (topPhi 1)).add
    (hcoeff.mul hphi))
  unfold lrDeterminantThickGapOne lrDeterminantThickGap
  convert h using 1
  · funext x
    simp only [Pi.add_apply, Pi.mul_apply, mul_one]
  · rw [topPhi_eq_mul_artanh_add_log hvFull,
      Real.artanh_eq_half_log ⟨hvFull.1.le, hvFull.2.le⟩]
    have hminus : 1 - v ≠ 0 := by linarith [hv.2]
    have hplus : 1 + v ≠ 0 := by linarith [hv.1]
    rw [show 1 - v ^ 2 = (1 - v) * (1 + v) by ring,
      Real.log_mul hminus hplus,
      Real.log_div hplus hminus]
    field_simp [hvNe, hminus, hplus]
    ring

theorem lrDeterminantThickGapOne_nonnegative
    {v : ℝ} (hv : v ∈ Ioc (0 : ℝ) 1) :
    0 ≤ lrDeterminantThickGapOne v := by
  rcases hv.2.eq_or_lt with rfl | hvLt
  · unfold lrDeterminantThickGapOne lrDeterminantThickGap
    rw [lrG_one, topPhi_one]
    norm_num
    convert le_refl (Real.log 2) using 1 <;> ring
  have hanti : AntitoneOn lrDeterminantThickGapOne (Icc v 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc v (1 : ℝ))
    · intro x hx
      have hxPos : 0 < x := hv.1.trans_le hx.1
      have hG := (hasDerivAt_lrG hxPos).continuousAt
      have hcoeff : ContinuousAt (fun y : ℝ ↦ 1 - 1 / y) x :=
        continuousAt_const.sub
          (continuousAt_const.div continuousAt_id hxPos.ne')
      unfold lrDeterminantThickGapOne lrDeterminantThickGap
      simpa only [mul_one] using
        (((hG.sub continuousAt_const).sub continuousAt_const).add
          (hcoeff.mul continuous_topPhi.continuousAt)).continuousWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      have hxMem : x ∈ Ioo (0 : ℝ) 1 :=
        ⟨hv.1.trans hx.1, hx.2⟩
      exact (hasDerivAt_lrDeterminantThickGapOne hxMem).differentiableAt
        |>.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      have hxMem : x ∈ Ioo (0 : ℝ) 1 :=
        ⟨hv.1.trans hx.1, hx.2⟩
      rw [(hasDerivAt_lrDeterminantThickGapOne hxMem).deriv]
      have hart : 0 ≤ Real.artanh x := Real.artanh_nonneg hxMem.1.le
      have hsquare : 0 ≤ 1 - x ^ 2 := by
        have hprod : 0 ≤ (1 - x) * (1 + x) :=
          mul_nonneg (sub_nonneg.mpr hxMem.2.le) (by linarith [hxMem.1])
        nlinarith
      exact div_nonpos_of_nonpos_of_nonneg
        (neg_nonpos.mpr (mul_nonneg hsquare hart))
        (sq_nonneg x)
  have horder := hanti
    (show v ∈ Icc v (1 : ℝ) from ⟨le_rfl, hv.2⟩)
    (show (1 : ℝ) ∈ Icc v 1 from ⟨hv.2, le_rfl⟩) hv.2
  have hone : lrDeterminantThickGapOne 1 = 0 := by
    unfold lrDeterminantThickGapOne lrDeterminantThickGap
    rw [lrG_one, topPhi_one]
    norm_num
    ring
  rwa [hone] at horder

theorem hasDerivAt_lrDeterminantThickGap_t
    {v t : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1)
    (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (lrDeterminantThickGap v)
      (-Real.artanh t - (1 - v) * Real.artanh (v * t)) t := by
  have htFull : t ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [ht.1], ht.2⟩
  have hvt : v * t ∈ Ioo (-1 : ℝ) 1 := by
    constructor
    · nlinarith [mul_pos hv.1 ht.1]
    · calc
        v * t < 1 * t := mul_lt_mul_of_pos_right hv.2 ht.1
        _ < 1 := by simpa using ht.2
  have harg : HasDerivAt (fun x : ℝ ↦ v * x) v t := by
    simpa using (hasDerivAt_id t).const_mul v
  have hphiT := hasDerivAt_topPhi htFull
  have hphiVT := (hasDerivAt_topPhi hvt).comp t harg
  have h := (((hasDerivAt_const t (lrG v)).sub_const (Real.log 2)).sub
    hphiT).add (hphiVT.const_mul (1 - 1 / v))
  unfold lrDeterminantThickGap
  convert h using 1
  field_simp [hv.1.ne']
  ring

theorem lrDeterminantThickGap_nonnegative
    {v t : ℝ} (hv : v ∈ Ioc (0 : ℝ) 1)
    (ht : t ∈ Ioc (0 : ℝ) 1) :
    0 ≤ lrDeterminantThickGap v t := by
  rcases hv.2.eq_or_lt with rfl | hvLt
  · unfold lrDeterminantThickGap
    rw [lrG_one]
    norm_num
    convert topPhi_le_log_two ⟨by linarith [ht.1], ht.2⟩ using 1 <;> ring
  have hvIoo : v ∈ Ioo (0 : ℝ) 1 := ⟨hv.1, hvLt⟩
  have hanti : AntitoneOn (lrDeterminantThickGap v) (Ioc (0 : ℝ) 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ioc (0 : ℝ) 1)
    · intro x hx
      have hvtContinuous : Continuous (fun y : ℝ ↦ topPhi (v * y)) :=
        continuous_topPhi.comp (continuous_const.mul continuous_id)
      unfold lrDeterminantThickGap
      exact (((continuousAt_const.sub continuousAt_const).sub
        continuous_topPhi.continuousAt).add
        (continuousAt_const.mul hvtContinuous.continuousAt)).continuousWithinAt
    · intro x hx
      rw [interior_Ioc] at hx
      exact (hasDerivAt_lrDeterminantThickGap_t hvIoo hx).differentiableAt
        |>.differentiableWithinAt
    · intro x hx
      rw [interior_Ioc] at hx
      rw [(hasDerivAt_lrDeterminantThickGap_t hvIoo hx).deriv]
      have hartX : 0 ≤ Real.artanh x := Real.artanh_nonneg hx.1.le
      have hartVX : 0 ≤ Real.artanh (v * x) :=
        Real.artanh_nonneg (mul_nonneg hv.1.le hx.1.le)
      nlinarith [mul_nonneg (sub_nonneg.mpr hv.2) hartVX]
  have horder := hanti ht
    (show (1 : ℝ) ∈ Ioc (0 : ℝ) 1 by norm_num) ht.2
  have hone := lrDeterminantThickGapOne_nonnegative hv
  change 0 ≤ lrDeterminantThickGap v 1 at hone
  exact hone.trans horder

/-- First assertion of the quantitative thick-reserve lemma. -/
theorem lrCertificateQ_one_sub_sq_le_lrGShape
    {v t : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1)
    (ht : t ∈ Ioo (0 : ℝ) 1) :
    lrCertificateQ (1 - (v * t) ^ 2) ≤ lrGShape t v := by
  have hvtPos : 0 < v * t := mul_pos hv.1 ht.1
  have hvtLt : v * t < 1 := calc
    v * t < 1 * t := mul_lt_mul_of_pos_right hv.2 ht.1
    _ < 1 := by simpa using ht.2
  have hsqrt : Real.sqrt (1 - (1 - (v * t) ^ 2)) = v * t := by
    rw [show 1 - (1 - (v * t) ^ 2) = (v * t) ^ 2 by ring,
      Real.sqrt_sq_eq_abs, abs_of_pos hvtPos]
  have hgap := lrDeterminantThickGap_nonnegative
    (show v ∈ Ioc (0 : ℝ) 1 from ⟨hv.1, hv.2.le⟩)
    (show t ∈ Ioc (0 : ℝ) 1 from ⟨ht.1, ht.2.le⟩)
  have hid : lrDeterminantThickGap v t =
      lrGShape t v - lrCertificateQ (1 - (v * t) ^ 2) := by
    rw [lrCertificateQ_eq, hsqrt]
    unfold lrDeterminantThickGap lrGShape
    field_simp [hv.1.ne']
    ring
  rw [hid] at hgap
  exact sub_nonneg.mp hgap

/-- The series-free form of (DA0a): the TOP contraction energy bounds the
two entropy deficiencies in `G_t` by the midpoint residual `f₀(v)`. -/
theorem lrCompactVFZero_le_lrGShape
    {v t : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1)
    (ht : t ∈ Ioo (0 : ℝ) 1) :
    lrCompactVFZero v ≤ lrGShape t v := by
  have henergy := topEnergy_nonneg
    (show v ∈ Icc (0 : ℝ) 1 from ⟨hv.1.le, hv.2.le⟩)
    (show t ∈ Icc (0 : ℝ) 1 from ⟨ht.1.le, ht.2.le⟩)
  have hphiDiv : topPhi (v * t) / v ≤ v * topPhi t := by
    unfold topEnergy topR at henergy
    rw [div_le_iff₀ hv.1]
    nlinarith
  have hphi := topPhi_le_log_two
    (show t ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [ht.1], ht.2.le⟩)
  have hlog : 0 ≤ Real.log 2 :=
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  have hsum : topPhi t + topPhi (v * t) / v ≤
      (1 + v) * Real.log 2 := by
    nlinarith [mul_nonneg (add_nonneg zero_le_one hv.1.le)
      (sub_nonneg.mpr hphi)]
  have hfactor : (1 + v) * Real.log 2 ≤
      4 * Real.log 2 / (1 + v) := by
    have hden : 0 < 1 + v := by linarith [hv.1]
    rw [le_div_iff₀ hden]
    have hsquare : (1 + v) ^ 2 ≤ 4 := by nlinarith [hv.2]
    nlinarith
  unfold lrCompactVFZero lrGShape
  linarith

/-- Applying noise to either entropy coordinate can only enlarge the square
target. -/
theorem lrCertificateGShape_le_squareTarget
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point) :
    lrCertificateGShape point ≤ lrCertificateSquareTarget point := by
  have hs := hinterior.1
  have he := hinterior.2.1
  have hchi := hinterior.2.2
  have hv := lrCertificateV_mem_Ioo hinterior
  have hy0 : lrCertificateY0 point ∈ Ioo (0 : ℝ) 1 := by
    unfold lrCertificateY0
    constructor
    · exact mul_pos hchi.1 he.1
    · calc
        point.chi * lrCertificateE point <
            1 * lrCertificateE point :=
          mul_lt_mul_of_pos_right hchi.2 he.1
        _ < 1 := by simpa using he.2
  have hby0 := lrCertificateB_mem_Ioo hs hy0
  have hbe := lrCertificateB_mem_Ioo hs he
  have hy0Le : lrCertificateY0 point ≤
      lrCertificateB point.s (lrCertificateY0 point) := by
    unfold lrCertificateB
    nlinarith [mul_nonneg hs.1.le (sub_nonneg.mpr hy0.2.le)]
  have heLe : lrCertificateE point ≤
      lrCertificateB point.s (lrCertificateE point) := by
    unfold lrCertificateB
    nlinarith [mul_nonneg hs.1.le (sub_nonneg.mpr he.2.le)]
  have hqY0 := lrCertificateQ_strictMonoOn.monotoneOn
    hy0 hby0 hy0Le
  have hqE := lrCertificateQ_strictMonoOn.monotoneOn
    he hbe heLe
  have hqEDiv : lrCertificateQ (lrCertificateE point) /
      lrCertificateV point ≤
      lrCertificateQ (lrCertificateB point.s (lrCertificateE point)) /
        lrCertificateV point :=
    (div_le_div_iff_of_pos_right hv.1).2 hqE
  unfold lrCertificateGShape lrCertificateGShapeValue
    lrCertificateSquareTarget
  linarith

/-- Exact cancellation form of the prefix at the midpoint. -/
theorem lrCertificatePrefixAtM_eq_s_mul_fzero_add
    {point : CertificatePoint}
    (hv : 0 < lrCertificateV point) :
    lrCertificatePrefixAtM point =
      point.s * lrCompactVFZero (lrCertificateV point) +
        4 * lrCertificateQ point.s / (1 + lrCertificateV point) := by
  unfold lrCertificatePrefixAtM lrCompactVFZero
  rw [lrCertificateG0_eq_lrG]
  field_simp [hv.ne', (by linarith [hv] : 1 + lrCertificateV point ≠ 0)]
  ring

/-- Exact thick-reserve cancellation before the elementary `v ≥ 1/3`
loss is imposed. -/
theorem lrCertificateGap_thick_lower
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point) :
    lrCertificateR point * lrCertificateGShape point -
        4 * lrCertificateQ point.s / (1 + lrCertificateV point) ≤
      lrCertificateGap point := by
  have hv := lrCertificateV_mem_Ioo hinterior
  have ht := lrCertificateT_mem_Ioo hinterior
  have hSquare := lrCertificateGShape_le_squareTarget hinterior
  have hGf0 : lrCompactVFZero (lrCertificateV point) ≤
      lrCertificateGShape point := by
    rw [lrCertificateGShape_eq_lrGShape hinterior.2.1
      ⟨hinterior.2.2.1.le, hinterior.2.2.2.le⟩]
    exact lrCompactVFZero_le_lrGShape hv ht
  unfold lrCertificateGap
  rw [lrCertificatePrefixAtM_eq_s_mul_fzero_add hv.1]
  unfold lrCertificateR
  nlinarith [mul_nonneg hinterior.1.1.le (sub_nonneg.mpr hGf0)]

/-- Second assertion of the quantitative thick-reserve lemma, with the
geometric lower bound on `v` made explicit. -/
theorem lrDeterminantT_thick_lower_of_v
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hvThird : 1 / 3 ≤ lrCertificateV point) :
    lrCertificateGShape point -
        3 * lrCertificateQ point.s / lrCertificateR point ≤
      lrDeterminantT point := by
  have hv := lrCertificateV_mem_Ioo hinterior
  have hR : 0 < lrCertificateR point := by
    unfold lrCertificateR
    linarith [hinterior.1.2]
  have hQ : 0 ≤ lrCertificateQ point.s :=
    lrCertificateQ_nonneg ⟨hinterior.1.1.le, hinterior.1.2.le⟩
  have hden : 0 < 1 + lrCertificateV point := by linarith [hv.1]
  have hcoeff : 4 / (1 + lrCertificateV point) ≤ 3 := by
    rw [div_le_iff₀ hden]
    linarith
  have hloss : 4 * lrCertificateQ point.s /
      (1 + lrCertificateV point) ≤ 3 * lrCertificateQ point.s := by
    calc
      4 * lrCertificateQ point.s / (1 + lrCertificateV point) =
          (4 / (1 + lrCertificateV point)) *
            lrCertificateQ point.s := by ring
      _ ≤ 3 * lrCertificateQ point.s :=
        mul_le_mul_of_nonneg_right hcoeff hQ
  have hgap := lrCertificateGap_thick_lower hinterior
  have hgap' : lrCertificateR point * lrCertificateGShape point -
      3 * lrCertificateQ point.s ≤ lrCertificateGap point := by
    linarith
  unfold lrDeterminantT
  rw [show lrCertificateGShape point -
      3 * lrCertificateQ point.s / lrCertificateR point =
      (lrCertificateR point * lrCertificateGShape point -
        3 * lrCertificateQ point.s) / lrCertificateR point by
    field_simp [hR.ne']]
  exact (div_le_div_iff_of_pos_right hR).2 hgap'

/-- The third retained physical inequality is exactly the cleared form of
`v ≥ 1/3`. -/
theorem lrCertificateV_one_third_le_of_physical
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hphysical : LRHighShapePhysical point) :
    1 / 3 ≤ lrCertificateV point := by
  have hv := lrCertificateV_mem_Ioo hinterior
  have hxPos : 0 < lrCertificateX point := by
    unfold lrCertificateX
    have hprodLt : point.chi * lrCertificateE point < 1 := by
      calc
        point.chi * lrCertificateE point <
            1 * lrCertificateE point :=
          mul_lt_mul_of_pos_right hinterior.2.2.2 hinterior.2.1.1
        _ < 1 := by simpa using hinterior.2.1.2
    linarith
  have hvSq : lrCertificateV point ^ 2 =
      (1 - lrCertificateE point) / lrCertificateX point := by
    unfold lrCertificateV
    exact Real.sq_sqrt
      (div_nonneg (sub_nonneg.mpr hinterior.2.1.2.le) hxPos.le)
  have hratio : (1 / 9 : ℝ) ≤
      (1 - lrCertificateE point) / lrCertificateX point := by
    rw [le_div_iff₀ hxPos]
    unfold LRHighShapePhysical at hphysical
    unfold lrCertificateX lrCertificateE
    nlinarith [hphysical.2.2]
  rw [← hvSq] at hratio
  by_contra hnot
  have hvLt : lrCertificateV point < 1 / 3 := lt_of_not_ge hnot
  have hfactor :
      (lrCertificateV point - 1 / 3) *
          (lrCertificateV point + 1 / 3) < 0 :=
    mul_neg_of_neg_of_pos (sub_neg.mpr hvLt) (by linarith [hv.1])
  nlinarith

/-- Certificate-coordinate form
`T ≥ G_t - 3 Q(s) / R` on the retained determinant domain. -/
theorem lrDeterminantT_thick_lower
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hrelevant : LRHighShapeVRelevant point) :
    lrCertificateGShape point -
        3 * lrCertificateQ point.s / lrCertificateR point ≤
      lrDeterminantT point :=
  lrDeterminantT_thick_lower_of_v hinterior
    (lrCertificateV_one_third_le_of_physical hinterior hrelevant.1)

/-- Certificate-coordinate form `G_t ≥ Q(e)` used by every determinant
tail bridge. -/
theorem lrCertificateQ_E_le_GShape
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point) :
    lrCertificateQ (lrCertificateE point) ≤
      lrCertificateGShape point := by
  have hv := lrCertificateV_mem_Ioo hinterior
  have ht := lrCertificateT_mem_Ioo hinterior
  have hxPos : 0 < lrCertificateX point := by
    unfold lrCertificateX
    have hprodLt : point.chi * lrCertificateE point < 1 := by
      calc
        point.chi * lrCertificateE point < 1 * lrCertificateE point :=
          mul_lt_mul_of_pos_right hinterior.2.2.2 hinterior.2.1.1
        _ < 1 := by simpa using hinterior.2.1.2
    linarith
  have htSq : lrCertificateT point ^ 2 = lrCertificateX point :=
    Real.sq_sqrt hxPos.le
  have hradPos : 0 <
      (1 - lrCertificateE point) / lrCertificateX point :=
    div_pos (sub_pos.mpr hinterior.2.1.2) hxPos
  have hvSq : lrCertificateV point ^ 2 =
      (1 - lrCertificateE point) / lrCertificateX point :=
    Real.sq_sqrt hradPos.le
  have hvtSq : (lrCertificateV point * lrCertificateT point) ^ 2 =
      1 - lrCertificateE point := by
    rw [mul_pow, hvSq, htSq]
    field_simp [hxPos.ne']
  have heq : lrCertificateE point =
      1 - (lrCertificateV point * lrCertificateT point) ^ 2 := by
    linarith [hvtSq]
  have hbound := lrCertificateQ_one_sub_sq_le_lrGShape hv ht
  rw [← heq] at hbound
  rw [lrCertificateGShape_eq_lrGShape hinterior.2.1
    ⟨hinterior.2.2.1.le, hinterior.2.2.2.le⟩]
  exact hbound

end CourtadeKumar
