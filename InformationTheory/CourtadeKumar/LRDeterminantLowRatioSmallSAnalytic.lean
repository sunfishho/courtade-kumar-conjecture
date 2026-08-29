import InformationTheory.CourtadeKumar.LRDeterminantLowRatio
import InformationTheory.CourtadeKumar.LRSmallSBridgeFrozen
import InformationTheory.CourtadeKumar.LRSmallSBridgeDecomposition
import InformationTheory.CourtadeKumar.LRSmallSBridgeRemainderIdentification

/-!
# Analytic closure of the determinant low-ratio small-`s` strip

This file formalizes the logarithmic-core estimate (M41) in the audited
low-ratio proof.  Here the manuscript's capital coordinate is
`K = point.k / point.s`, so `e = s^2 K`, and

`n = e (1 + chi) / 4`.

The development derives all four elementary estimates on `p`, `p-g`, `D1`,
and `B`, proves the exact rational M41 margin, and proves both audited
restoration payments that turn the frozen logarithmic core into the exact
first bracket (M42).  Its final theorem discharges the public
`LRDeterminantLowRatioSmallSFirstBracketTheorem` input unconditionally.
-/

open Set

namespace CourtadeKumar

noncomputable def lrLowRatioCapitalK (point : CertificatePoint) : ℝ :=
  point.k / point.s

noncomputable def lrLowRatioRho (point : CertificatePoint) : ℝ :=
  -Real.log (lrLowRatioCapitalK point)

noncomputable def lrLowRatioLogScale (point : CertificatePoint) : ℝ :=
  Real.log (1 / point.s)

noncomputable def lrLowRatioP (point : CertificatePoint) : ℝ :=
  lrSmallSBridgeP point.s point.k point.chi (lrLowRatioLogScale point)

noncomputable def lrLowRatioG (point : CertificatePoint) : ℝ :=
  lrSmallSBridgeG point.k point.chi (lrLowRatioLogScale point)

/-- The normalized frozen first bracket in (M41). -/
noncomputable def lrLowRatioFrozenFirstBracketNormalized
    (point : CertificatePoint) : ℝ :=
  lrDeterminantD1 point * lrLowRatioP point +
    lrCertificateBFlow point * (lrLowRatioP point - lrLowRatioG point)

/-- The manuscript normalization `n = K(1+chi)s^2/4 = e(1+chi)/4`. -/
noncomputable def lrLowRatioNormalization
    (point : CertificatePoint) : ℝ :=
  lrCertificateE point * (1 + point.chi) / 4

noncomputable def lrLowRatioExactFirstBracketNormalized
    (point : CertificatePoint) : ℝ :=
  lrDeterminantFirstBracket
      (lrCertificateBFlow point) (lrDeterminantD1 point)
      (lrCertificateGShape point) (lrDeterminantPsi point)
      (lrDeterminantDelta point) (lrCertificateW point) /
    lrLowRatioNormalization point

noncomputable def lrLowRatioEpsilonChannel : ℝ := 13 / 3276800

noncomputable def lrLowRatioEpsilonEntropy : ℝ :=
  7 / 329853488332800

lemma lrLowRatioCapitalK_mem
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hregion : LRDeterminantLowRatioRegion point) :
    lrLowRatioCapitalK point ∈ Ioc (1 / 4 : ℝ) 1 := by
  have hs : 0 < point.s := hinterior.1.1
  constructor
  · unfold lrLowRatioCapitalK
    rw [lt_div_iff₀ hs]
    nlinarith [hregion.1]
  · unfold lrLowRatioCapitalK
    exact (div_le_one hs).2 hregion.2

lemma lrLowRatioRho_nonnegative
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hregion : LRDeterminantLowRatioRegion point) :
    0 ≤ lrLowRatioRho point := by
  have hK := lrLowRatioCapitalK_mem hinterior hregion
  unfold lrLowRatioRho
  exact neg_nonneg.mpr (Real.log_nonpos (by linarith [hK.1]) hK.2)

lemma lrLowRatioRho_lt_two_log_two
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hregion : LRDeterminantLowRatioRegion point) :
    lrLowRatioRho point < 2 * Real.log 2 := by
  have hK := lrLowRatioCapitalK_mem hinterior hregion
  have hquarterPos : (0 : ℝ) < 1 / 4 := by norm_num
  have hlog := Real.strictMonoOn_log
    (show (1 / 4 : ℝ) ∈ Ioi 0 from hquarterPos)
    (show lrLowRatioCapitalK point ∈ Ioi 0 from
      hquarterPos.trans hK.1)
    hK.1
  have hlogQuarter : Real.log (1 / 4 : ℝ) = -2 * Real.log 2 := by
    rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0)
      (by norm_num : (4 : ℝ) ≠ 0),
      show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  unfold lrLowRatioRho
  rw [hlogQuarter] at hlog
  linarith

lemma lrLowRatioE_le_s_sq
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hregion : LRDeterminantLowRatioRegion point) :
    lrCertificateE point ≤ point.s ^ 2 := by
  unfold lrCertificateE
  have h := mul_le_mul_of_nonneg_left hregion.2 hinterior.1.1.le
  nlinarith

/-- In the low-ratio chart the radial square-root moves by at most `e`.
This is stronger than the coarse `d ≤ 2e` used in the audit memo. -/
lemma lrLowRatio_one_sub_v_le_e
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point) :
    1 - lrCertificateV point ≤ lrCertificateE point := by
  let e := lrCertificateE point
  let x := lrCertificateX point
  let v := lrCertificateV point
  have he : e ∈ Ioo (0 : ℝ) 1 := by simpa [e] using hinterior.2.1
  have hxPos : 0 < x := by
    dsimp [x, lrCertificateX]
    have hprod : point.chi * e < 1 := by
      calc
        point.chi * e < 1 * e :=
          mul_lt_mul_of_pos_right hinterior.2.2.2 he.1
        _ = e := one_mul _
        _ < 1 := he.2
    linarith
  have hxLe : x ≤ 1 := by
    dsimp [x, lrCertificateX]
    exact sub_le_self _ (mul_nonneg hinterior.2.2.1.le he.1.le)
  have hradPos : 0 < (1 - e) / x :=
    div_pos (sub_pos.mpr he.2) hxPos
  have hvSq : v ^ 2 = (1 - e) / x := by
    dsimp [v, lrCertificateV]
    exact Real.sq_sqrt hradPos.le
  have hvNonneg : 0 ≤ v := by
    dsimp [v, lrCertificateV]
    exact Real.sqrt_nonneg _
  have hradLower : 1 - e ≤ (1 - e) / x := by
    rw [le_div_iff₀ hxPos]
    exact mul_le_of_le_one_right (sub_nonneg.mpr he.2.le) hxLe
  have hgap : 1 - v ^ 2 ≤ e := by
    rw [hvSq]
    linarith
  dsimp [v, e] at hgap hvNonneg ⊢
  nlinarith [mul_nonneg hvNonneg (sub_nonneg.mpr
    (lrCertificateV_mem_Ioo hinterior).2.le)]

lemma lrLowRatio_v_one_half_le
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hregion : LRDeterminantLowRatioRegion point)
    (hsSmall : point.s ≤ 1 / 16384) :
    1 / 2 ≤ lrCertificateV point := by
  have hd := lrLowRatio_one_sub_v_le_e hinterior
  have he := lrLowRatioE_le_s_sq hinterior hregion
  have hs0 : 0 ≤ point.s := hinterior.1.1.le
  have hsSq : point.s ^ 2 ≤ (1 / 16384 : ℝ) ^ 2 := by
    nlinarith
  nlinarith [hsSq]

noncomputable def lrLowRatioAWeight (point : CertificatePoint) : ℝ :=
  1 / lrCertificateV point - 1

noncomputable def lrLowRatioBWeight (point : CertificatePoint) : ℝ :=
  4 / (1 + lrCertificateV point) - 2

noncomputable def lrLowRatioKappa (point : CertificatePoint) : ℝ :=
  lrLowRatioAWeight point - lrLowRatioBWeight point

lemma lrLowRatio_weight_identities
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point) :
    lrLowRatioAWeight point =
        (1 - lrCertificateV point) / lrCertificateV point ∧
      lrLowRatioBWeight point =
        2 * (1 - lrCertificateV point) /
          (1 + lrCertificateV point) ∧
      lrLowRatioKappa point =
        (1 - lrCertificateV point) ^ 2 /
          (lrCertificateV point * (1 + lrCertificateV point)) := by
  have hv := lrCertificateV_mem_Ioo hinterior
  have hvNe : lrCertificateV point ≠ 0 := hv.1.ne'
  have hvPlus : 1 + lrCertificateV point ≠ 0 := by linarith [hv.1]
  constructor
  · unfold lrLowRatioAWeight
    field_simp [hvNe]
  constructor
  · unfold lrLowRatioBWeight
    field_simp [hvPlus]
    ring
  · unfold lrLowRatioKappa lrLowRatioAWeight lrLowRatioBWeight
    field_simp [hvNe, hvPlus]
    ring

lemma lrLowRatio_weight_bounds
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hregion : LRDeterminantLowRatioRegion point)
    (hsSmall : point.s ≤ 1 / 16384) :
    0 ≤ lrLowRatioAWeight point ∧
      lrLowRatioAWeight point ≤ 4 * lrCertificateE point ∧
      0 ≤ lrLowRatioBWeight point ∧
      lrLowRatioBWeight point ≤ 4 * lrCertificateE point ∧
      0 ≤ lrLowRatioKappa point ∧
      lrLowRatioKappa point ≤ 8 * lrCertificateE point ^ 2 := by
  let v := lrCertificateV point
  let e := lrCertificateE point
  let d := 1 - v
  have hv := lrCertificateV_mem_Ioo hinterior
  have hvHalf : 1 / 2 ≤ v := by
    simpa [v] using lrLowRatio_v_one_half_le hinterior hregion hsSmall
  have hd : d ∈ Icc (0 : ℝ) e := by
    constructor
    · dsimp [d, v]
      linarith [hv.2]
    · simpa [d, v, e] using lrLowRatio_one_sub_v_le_e hinterior
  have he0 : 0 ≤ e := (by simpa [e] using hinterior.2.1.1.le)
  rcases lrLowRatio_weight_identities (point := point) hinterior with
    ⟨haEq, hbEq, hkEq⟩
  have ha0 : 0 ≤ lrLowRatioAWeight point := by
    rw [haEq]
    exact div_nonneg (by simpa [d, v] using hd.1) hv.1.le
  have haUpper : lrLowRatioAWeight point ≤ 4 * e := by
    rw [haEq, div_le_iff₀ hv.1]
    change 1 - v ≤ 4 * e * v
    have hd' : 1 - v ≤ e := by simpa [d] using hd.2
    have hfourv : 1 ≤ 4 * v := by nlinarith [hvHalf]
    have hscaled : e ≤ 4 * e * v := by
      calc
        e = e * 1 := by ring
        _ ≤ e * (4 * v) := mul_le_mul_of_nonneg_left hfourv he0
        _ = 4 * e * v := by ring
    exact hd'.trans hscaled
  have hb0 : 0 ≤ lrLowRatioBWeight point := by
    rw [hbEq]
    exact div_nonneg
      (mul_nonneg (by norm_num) (by simpa [d, v] using hd.1))
      (by linarith [hv.1] : 0 ≤ 1 + v)
  have hbUpper : lrLowRatioBWeight point ≤ 4 * e := by
    rw [hbEq, div_le_iff₀ (by linarith [hv.1] : 0 < 1 + v)]
    change 2 * d ≤ 4 * e * (1 + v)
    nlinarith [hd.2, mul_nonneg he0 hv.1.le]
  have hk0 : 0 ≤ lrLowRatioKappa point := by
    rw [hkEq]
    exact div_nonneg (sq_nonneg (1 - v))
      (mul_nonneg hv.1.le (by linarith [hv.1] : 0 ≤ 1 + v))
  have hkUpper : lrLowRatioKappa point ≤ 8 * e ^ 2 := by
    rw [hkEq, div_le_iff₀
      (mul_pos hv.1 (by linarith [hv.1] : 0 < 1 + v))]
    have hdSq : d ^ 2 ≤ e ^ 2 := by nlinarith [hd.1, hd.2]
    have hvPlusHalf : (3 / 2 : ℝ) ≤ 1 + v := by linarith [hvHalf]
    have hprodLower : (1 / 2 : ℝ) * (3 / 2) ≤ v * (1 + v) :=
      mul_le_mul hvHalf hvPlusHalf (by norm_num) hv.1.le
    have hden : 1 ≤ 8 * (v * (1 + v)) := by
      nlinarith [hprodLower]
    have hscaled := mul_le_mul_of_nonneg_left hden (sq_nonneg e)
    dsimp [d] at hdSq
    nlinarith
  simpa [v, e] using ⟨ha0, haUpper, hb0, hbUpper, hk0, hkUpper⟩

noncomputable def lrLowRatioQ0Omega (point : CertificatePoint) : ℝ :=
  lrLowerFacePWQ0 point.s point.k point.chi (lrCertificateV point) -
    4 * lrLowerFaceOmegaQ0 point.s 0 /
      (1 + lrCertificateV point)

noncomputable def lrLowRatioQ0FrozenOmega
    (point : CertificatePoint) : ℝ :=
  lrLowerFacePWQ0 point.s point.k point.chi 1 -
    2 * lrLowerFaceOmegaQ0 point.s 0

noncomputable def lrLowRatioQ0DeltaOmega
    (point : CertificatePoint) : ℝ :=
  lrLowRatioQ0Omega point - lrLowRatioQ0FrozenOmega point

lemma lrLowRatioQ0DeltaOmega_formula
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point) :
    lrLowRatioQ0DeltaOmega point =
      lrLowRatioBWeight point *
          (lrLowerFaceOmegaQ0 point.s (lrCertificateE point) -
            lrLowerFaceOmegaQ0 point.s 0) +
        lrLowRatioKappa point *
          lrLowerFaceOmegaQ0 point.s (lrCertificateE point) := by
  have hv := lrCertificateV_mem_Ioo hinterior
  have hvNe : lrCertificateV point ≠ 0 := hv.1.ne'
  have hvPlus : 1 + lrCertificateV point ≠ 0 := by linarith [hv.1]
  unfold lrLowRatioQ0DeltaOmega lrLowRatioQ0Omega
    lrLowRatioQ0FrozenOmega lrLowerFacePWQ0
    lrLowRatioKappa lrLowRatioAWeight lrLowRatioBWeight
    lrCertificateE
  field_simp [hvNe, hvPlus]
  ring

lemma lrLowRatio_log_k_identity
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hregion : LRDeterminantLowRatioRegion point) :
    Real.log point.k =
      -lrLowRatioLogScale point - lrLowRatioRho point := by
  have hs : 0 < point.s := hinterior.1.1
  have hK := lrLowRatioCapitalK_mem hinterior hregion
  have hKPos : 0 < lrLowRatioCapitalK point := by linarith [hK.1]
  have hkEq : point.k = point.s * lrLowRatioCapitalK point := by
    unfold lrLowRatioCapitalK
    field_simp [hs.ne']
  have hlogInv : lrLowRatioLogScale point = -Real.log point.s := by
    unfold lrLowRatioLogScale
    rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) hs.ne']
    norm_num
  rw [hkEq, Real.log_mul hs.ne' hKPos.ne', hlogInv]
  unfold lrLowRatioRho
  ring

lemma lrLowRatio_outer_log_upper
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hregion : LRDeterminantLowRatioRegion point) :
    Real.log ((1 + (1 - point.s) * point.k) / point.k) ≤
      lrLowRatioLogScale point + 2 * Real.log 2 + point.s := by
  have hs : point.s ∈ Ioo (0 : ℝ) 1 := hinterior.1
  have hk : 0 < point.k := by linarith [hregion.1, hs.1]
  have hRk : 0 ≤ (1 - point.s) * point.k :=
    mul_nonneg (sub_nonneg.mpr hs.2.le) hk.le
  have hnum : 0 < 1 + (1 - point.s) * point.k := by linarith
  have hlogOne : Real.log (1 + (1 - point.s) * point.k) ≤
      (1 - point.s) * point.k := by
    simpa using Real.log_le_sub_one_of_pos hnum
  have hRkLe : (1 - point.s) * point.k ≤ point.s := by
    have hleK : (1 - point.s) * point.k ≤ point.k := by
      nlinarith [mul_nonneg hs.1.le hk.le]
    exact hleK.trans hregion.2
  have hlogK := lrLowRatio_log_k_identity hinterior hregion
  have hrho := lrLowRatioRho_lt_two_log_two hinterior hregion
  rw [Real.log_div hnum.ne' hk.ne', hlogK]
  linarith

/-- Sharp enough endpoint bound for the only adverse q0 omega difference. -/
lemma lrLowRatioQ0Omega_gap_bound
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hregion : LRDeterminantLowRatioRegion point)
    (hsSmall : point.s ≤ 1 / 16384) :
    0 ≤ lrLowerFaceOmegaQ0 point.s 0 -
        lrLowerFaceOmegaQ0 point.s (lrCertificateE point) ∧
      lrLowerFaceOmegaQ0 point.s 0 -
          lrLowerFaceOmegaQ0 point.s (lrCertificateE point) ≤
        lrCertificateE point / 4 *
          (lrLowRatioLogScale point + 2 * Real.log 2 + 1) := by
  have hs : point.s ∈ Ioo (0 : ℝ) 1 := hinterior.1
  have hk : 0 < point.k := by linarith [hregion.1, hs.1]
  have he : lrCertificateE point ∈ Ioo (0 : ℝ) 1 := hinterior.2.1
  have hsk : point.s * point.k < 1 := by
    simpa [lrCertificateE] using he.2
  let ratio := (1 + (1 - point.s) * point.k) / point.k
  have hratioOne : 1 < ratio := by
    dsimp [ratio]
    rw [lt_div_iff₀ hk]
    have hkOne : point.k < 1 := hregion.2.trans_lt hs.2
    nlinarith [mul_nonneg (sub_nonneg.mpr hs.2.le) hk.le]
  have hlog0 : 0 ≤ Real.log ratio := (Real.log_pos hratioOne).le
  have hlogUpper : Real.log ratio ≤
      lrLowRatioLogScale point + 2 * Real.log 2 + point.s := by
    simpa [ratio] using lrLowRatio_outer_log_upper hinterior hregion
  have hformula :
      lrLowerFaceOmegaQ0 point.s 0 -
          lrLowerFaceOmegaQ0 point.s (lrCertificateE point) =
        lrCertificateE point / 4 * (point.s + Real.log ratio) := by
    rw [show lrCertificateE point = point.s * point.k by rfl,
      lrLowerFaceOmegaQ0_zero hs.1,
      lrLowerFaceOmegaQ0_sk_eq hs hk hsk]
    dsimp [ratio]
    ring
  rw [hformula]
  constructor
  · exact mul_nonneg (div_nonneg he.1.le (by norm_num))
      (add_nonneg hs.1.le hlog0)
  · have hcoef : point.s + Real.log ratio ≤
        lrLowRatioLogScale point + 2 * Real.log 2 + 1 := by
      nlinarith [hlogUpper, hsSmall]
    exact mul_le_mul_of_nonneg_left hcoef
      (div_nonneg he.1.le (by norm_num))

lemma lrLowRatioQ0DeltaG_lower
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hregion : LRDeterminantLowRatioRegion point)
    (hsSmall : point.s ≤ 1 / 16384) :
    -8 * lrCertificateE point ^ 2 ≤
      lrSmallSBridgeQ0DeltaG point := by
  have hv := lrCertificateV_mem_Ioo hinterior
  have hvHalf : lrCertificateV point ∈ Icc (1 / 2 : ℝ) 1 :=
    ⟨lrLowRatio_v_one_half_le hinterior hregion hsSmall, hv.2.le⟩
  have hg0 := lrCertificateG0_lower_quadratic hvHalf
  have he : lrCertificateE point ∈ Ioc (0 : ℝ) 1 :=
    ⟨hinterior.2.1.1, hinterior.2.1.2.le⟩
  have hq0 := lrLowerFaceQ0_nonneg_of_mem he
  have hinv : 1 ≤ 1 / lrCertificateV point := by
    rw [le_div_iff₀ hv.1]
    simpa using hv.2.le
  have hrest : 0 ≤ lrLowerFaceQ0 (lrCertificateE point) *
      (1 / lrCertificateV point - 1) :=
    mul_nonneg hq0 (sub_nonneg.mpr hinv)
  have hd := lrLowRatio_one_sub_v_le_e hinterior
  have he0 := hinterior.2.1.1.le
  have hd0 : 0 ≤ 1 - lrCertificateV point := by linarith [hv.2]
  have hdSq : (1 - lrCertificateV point) ^ 2 ≤
      lrCertificateE point ^ 2 := by nlinarith
  unfold lrSmallSBridgeQ0DeltaG
  nlinarith

lemma lrLowRatioQ0DeltaOmega_lower
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hregion : LRDeterminantLowRatioRegion point)
    (hsSmall : point.s ≤ 1 / 16384) :
    -lrCertificateE point ^ 2 *
        (lrLowRatioLogScale point + 2 * Real.log 2 + 1) ≤
      lrLowRatioQ0DeltaOmega point := by
  have hs : point.s ∈ Ioo (0 : ℝ) 1 := hinterior.1
  have he := hinterior.2.1
  have homega := lrLowerFaceOmegaQ0_nonneg hs he
  have hgap := lrLowRatioQ0Omega_gap_bound hinterior hregion hsSmall
  have hweights := lrLowRatio_weight_bounds hinterior hregion hsSmall
  have hformula := lrLowRatioQ0DeltaOmega_formula
    (point := point) hinterior
  let C := lrLowRatioLogScale point + 2 * Real.log 2 + 1
  have hC : 0 ≤ C := by
    have hLraw := lrSmallSBridge_log_lower
      (show point.s ∈ Ioc (0 : ℝ) (1 / 16384) from
        ⟨hinterior.1.1, hsSmall⟩)
    have hL : 14 * Real.log 2 ≤ lrLowRatioLogScale point := by
      simpa [lrLowRatioLogScale] using hLraw
    dsimp [C]
    nlinarith [Real.log_two_gt_d9]
  have hnegative :
      -lrCertificateE point / 4 * C ≤
        lrLowerFaceOmegaQ0 point.s (lrCertificateE point) -
          lrLowerFaceOmegaQ0 point.s 0 := by
    dsimp [C]
    linarith [hgap.2]
  have hscaled := mul_le_mul_of_nonneg_left hnegative hweights.2.2.1
  have hbUpper := hweights.2.2.2.1
  have hleft :
      lrLowRatioBWeight point * (-lrCertificateE point / 4 * C) ≤
        lrLowRatioBWeight point *
          (lrLowerFaceOmegaQ0 point.s (lrCertificateE point) -
            lrLowerFaceOmegaQ0 point.s 0) := hscaled
  have hbase :
      -lrCertificateE point ^ 2 * C ≤
        lrLowRatioBWeight point * (-lrCertificateE point / 4 * C) := by
    have hEC : 0 ≤ lrCertificateE point / 4 * C :=
      mul_nonneg (div_nonneg he.1.le (by norm_num)) hC
    have hmul := mul_le_mul_of_nonneg_right hbUpper hEC
    nlinarith
  have hkTerm : 0 ≤ lrLowRatioKappa point *
      lrLowerFaceOmegaQ0 point.s (lrCertificateE point) :=
    mul_nonneg hweights.2.2.2.2.1 homega
  rw [hformula]
  exact (hbase.trans hleft).trans (le_add_of_nonneg_right hkTerm)

lemma lrLowRatioAR_nonnegative
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hregion : LRDeterminantLowRatioRegion point) :
    0 ≤ lrSmallSBridgeAR point.s point.k point.chi := by
  have hs : point.s ∈ Ioo (0 : ℝ) 1 := hinterior.1
  have hkPos : 0 < point.k := by
    linarith [hregion.1, hs.1]
  have hchi : point.chi ∈ Icc (0 : ℝ) 1 :=
    ⟨hinterior.2.2.1.le, hinterior.2.2.2.le⟩
  have hR : 0 ≤ 1 - point.s := sub_nonneg.mpr hs.2.le
  have hu : 0 ≤ (1 - point.s) * point.k := mul_nonneg hR hkPos.le
  have huchi : 0 ≤ (1 - point.s) * point.k * point.chi :=
    mul_nonneg hu hchi.1
  have hlogChi : 0 ≤ Real.log
      (1 + (1 - point.s) * point.k * point.chi) :=
    Real.log_nonneg (by linarith)
  have hlogOne : 0 ≤ Real.log (1 + (1 - point.s) * point.k) :=
    Real.log_nonneg (by linarith)
  unfold lrSmallSBridgeAR
  exact div_nonneg
    (add_nonneg (mul_nonneg hchi.1 hlogChi) hlogOne)
    (by linarith [hchi.1])

/-- The elementary `A_R ≤ s` estimate used in the first inequality of
(M41). -/
lemma lrLowRatioAR_le_s
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hregion : LRDeterminantLowRatioRegion point) :
    lrSmallSBridgeAR point.s point.k point.chi ≤ point.s := by
  have hs : point.s ∈ Ioo (0 : ℝ) 1 := hinterior.1
  have hkPos : 0 < point.k := by linarith [hregion.1, hs.1]
  have hchi : point.chi ∈ Icc (0 : ℝ) 1 :=
    ⟨hinterior.2.2.1.le, hinterior.2.2.2.le⟩
  let u := (1 - point.s) * point.k
  have hR : 0 ≤ 1 - point.s := sub_nonneg.mpr hs.2.le
  have hu : 0 ≤ u := by
    dsimp [u]
    exact mul_nonneg hR hkPos.le
  have huLeK : u ≤ point.k := by
    dsimp [u]
    nlinarith [mul_nonneg hs.1.le hkPos.le]
  have huLeS : u ≤ point.s := huLeK.trans hregion.2
  have huchi : 0 ≤ u * point.chi := mul_nonneg hu hchi.1
  have hlogChi : Real.log (1 + u * point.chi) ≤ u * point.chi := by
    simpa using Real.log_le_sub_one_of_pos (by linarith [huchi] :
      0 < 1 + u * point.chi)
  have hlogOne : Real.log (1 + u) ≤ u := by
    simpa using Real.log_le_sub_one_of_pos (by linarith [hu] : 0 < 1 + u)
  have hweighted := mul_le_mul_of_nonneg_left hlogChi hchi.1
  have hchiSq : point.chi ^ 2 ≤ point.chi := by
    nlinarith [mul_nonneg hchi.1 (sub_nonneg.mpr hchi.2)]
  have hnum :
      point.chi * Real.log (1 + u * point.chi) + Real.log (1 + u) ≤
        point.s * (1 + point.chi) := by
    have huChiSq : u * point.chi ^ 2 ≤ u * point.chi :=
      mul_le_mul_of_nonneg_left hchiSq hu
    have huScale : u * (1 + point.chi) ≤
        point.s * (1 + point.chi) :=
      mul_le_mul_of_nonneg_right huLeS (by linarith [hchi.1])
    calc
      point.chi * Real.log (1 + u * point.chi) + Real.log (1 + u) ≤
          point.chi * (u * point.chi) + u :=
        add_le_add hweighted hlogOne
      _ = u * point.chi ^ 2 + u := by ring
      _ ≤ u * point.chi + u := by linarith
      _ = u * (1 + point.chi) := by ring
      _ ≤ point.s * (1 + point.chi) := huScale
  have hden : 0 < 1 + point.chi := by linarith [hchi.1]
  unfold lrSmallSBridgeAR
  dsimp [u] at hnum
  rw [div_le_iff₀ hden]
  exact hnum

lemma lrLowRatioP_lower
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hregion : LRDeterminantLowRatioRegion point) :
    lrLowRatioLogScale point + 2 * Real.log 2 + 1 - 2 * point.s ≤
      lrLowRatioP point := by
  have hAR := lrLowRatioAR_le_s hinterior hregion
  unfold lrLowRatioP lrSmallSBridgeP
  linarith

lemma lrLowRatioP_sub_G_lower
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hregion : LRDeterminantLowRatioRegion point) :
    -lrLowRatioLogScale point - lrLowRatioRho point +
        lrSmallSBridgeQChi point.chi - 2 * point.s ≤
      lrLowRatioP point - lrLowRatioG point := by
  have hAR := lrLowRatioAR_le_s hinterior hregion
  have hlogK := lrLowRatio_log_k_identity hinterior hregion
  change _ ≤ lrSmallSBridgeS point.s point.k point.chi
      (lrLowRatioLogScale point)
  rw [lrSmallSBridgeS_eq, hlogK]
  linarith

lemma lrLowRatioP_sub_G_nonpositive
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hregion : LRDeterminantLowRatioRegion point) :
    lrLowRatioP point - lrLowRatioG point ≤ 0 := by
  have hs : 0 < point.s := hinterior.1.1
  have hkPos : 0 < point.k := by linarith [hregion.1, hs]
  have hkOne : point.k ≤ 1 :=
    hregion.2.trans hinterior.1.2.le
  have hlogK : Real.log point.k ≤ 0 := Real.log_nonpos hkPos.le hkOne
  have hAR := lrLowRatioAR_nonnegative hinterior hregion
  have hchi : point.chi ∈ Icc (0 : ℝ) 1 :=
    ⟨hinterior.2.2.1.le, hinterior.2.2.2.le⟩
  have hq := lrSmallSBridgeQChi_nonpos hchi
  change lrSmallSBridgeS point.s point.k point.chi
      (lrLowRatioLogScale point) ≤ 0
  rw [lrSmallSBridgeS_eq]
  linarith

lemma lrLowRatio_determinantY_formula
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hregion : LRDeterminantLowRatioRegion point) :
    lrDeterminantY point =
      (1 + (1 - point.s) * point.k) / point.k := by
  have hs : 0 < point.s := hinterior.1.1
  have hk : 0 < point.k := by linarith [hregion.1, hs]
  unfold lrDeterminantY lrCertificateB lrCertificateE
  field_simp [hs.ne', hk.ne']

lemma lrLowRatio_D1_lower
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hregion : LRDeterminantLowRatioRegion point) :
    (lrLowRatioLogScale point - Real.log 2 + lrLowRatioRho point) / 2 +
        1 / 3 - point.s / 2 ≤
      lrDeterminantD1 point := by
  let Y := lrDeterminantY point
  have hs : point.s ∈ Ioo (0 : ℝ) 1 := hinterior.1
  have hk : 0 < point.k := by linarith [hregion.1, hs.1]
  have hYFormula : Y =
      (1 + (1 - point.s) * point.k) / point.k := by
    simpa [Y] using lrLowRatio_determinantY_formula hinterior hregion
  have hRk : 0 ≤ (1 - point.s) * point.k :=
    mul_nonneg (sub_nonneg.mpr hs.2.le) hk.le
  have hYPos : 0 < Y := by
    rw [hYFormula]
    exact div_pos (by linarith [hRk]) hk
  have hYInvK : 1 / point.k ≤ Y := by
    rw [hYFormula]
    rw [div_le_div_iff_of_pos_right hk]
    linarith [hRk]
  have hmeanLower : 1 / (2 * point.k) ≤ (1 + Y) / 2 := by
    have h := mul_le_mul_of_nonneg_left hYInvK
      (by norm_num : (0 : ℝ) ≤ 1 / 2)
    calc
      1 / (2 * point.k) = (1 / point.k) * (1 / 2) := by ring
      _ ≤ Y * (1 / 2) := by simpa [mul_comm] using h
      _ ≤ (1 + Y) / 2 := by linarith
  have hbasePos : 0 < 1 / (2 * point.k) := by positivity
  have hlogLower : Real.log (1 / (2 * point.k)) ≤
      Real.log ((1 + Y) / 2) :=
    Real.log_le_log hbasePos hmeanLower
  have hlogK := lrLowRatio_log_k_identity hinterior hregion
  have hlogBase : Real.log (1 / (2 * point.k)) =
      lrLowRatioLogScale point - Real.log 2 + lrLowRatioRho point := by
    rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0)
      (mul_ne_zero (by norm_num) hk.ne'), Real.log_one,
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hk.ne', hlogK]
    ring
  rw [hlogBase] at hlogLower
  have hYLower : 1 / point.s ≤ Y := by
    rw [hYFormula, le_div_iff₀ hk]
    have hkDiv : point.k / point.s ≤ 1 :=
      (div_le_one hs.1).2 hregion.2
    have hrewrite : (1 / point.s) * point.k = point.k / point.s := by ring
    rw [hrewrite]
    linarith [hRk]
  have hsY : 1 ≤ point.s * Y := by
    have h := mul_le_mul_of_nonneg_left hYLower hs.1.le
    calc
      1 = point.s * (1 / point.s) := by field_simp [hs.1.ne']
      _ ≤ point.s * Y := h
  have hden : 0 < 3 * Y + 1 := by linarith [hYPos]
  have hfrac : 1 / 3 - point.s / 2 ≤ (Y - 1) / (3 * Y + 1) := by
    rw [le_div_iff₀ hden]
    nlinarith [hsY, hs.1]
  unfold lrDeterminantD1
  dsimp only
  change _ ≤ (1 / 2 : ℝ) * Real.log ((1 + Y) / 2) +
    (Y - 1) / (3 * Y + 1)
  nlinarith

lemma lrLowRatio_B_upper
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point) :
    lrCertificateBFlow point ≤
      lrLowRatioLogScale point / 2 + Real.log 2 := by
  have hs : point.s ∈ Ioo (0 : ℝ) 1 := hinterior.1
  have he : lrCertificateE point ∈ Ioo (0 : ℝ) 1 := hinterior.2.1
  have hv := lrCertificateV_mem_Ioo hinterior
  have hb := lrCertificateB_mem_Ioo hs he
  have hbLower : point.s ≤
      lrCertificateB point.s (lrCertificateE point) := by
    unfold lrCertificateB
    exact le_add_of_nonneg_right
      (mul_nonneg (sub_nonneg.mpr hs.2.le) he.1.le)
  have hlogV : Real.log (1 + lrCertificateV point) ≤ Real.log 2 := by
    exact Real.log_le_log (by linarith [hv.1]) (by linarith [hv.2])
  have hlogB : Real.log point.s ≤
      Real.log (lrCertificateB point.s (lrCertificateE point)) :=
    Real.log_le_log hs.1 hbLower
  have hlogInv : lrLowRatioLogScale point = -Real.log point.s := by
    unfold lrLowRatioLogScale
    rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) hs.1.ne']
    norm_num
  unfold lrCertificateBFlow lrCertificateBFlowValue
  rw [hlogInv]
  nlinarith

/-- Exact scalar endpoint calculation in (M41).  All arithmetic is proved by
the kernel; no executable decision procedure is used. -/
theorem lrLowRatioM41_scalar
    (s L lam w0 : ℝ)
    (hs0 : 0 ≤ s)
    (hs : s ≤ (1 : ℝ) / 16384)
    (hL : 14 * lam ≤ L)
    (hlam_lo : (2 : ℝ) / 3 < lam)
    (hlam_hi : lam < (7 : ℝ) / 10)
    (hw0 : w0 < (2 : ℝ) / 7) :
    (4977691 : ℝ) / 1843200 <
      L * ((5 : ℝ) / 6 - (lam + w0) / 2 - 5 * s / 2) +
        1 / 3 + lam / 6 - lam ^ 2 - lam * w0 +
        s ^ 2 - 7 * s / 6 - 2 * lam * s := by
  have hlam0 : 0 < lam := by linarith
  have hcoef :
      0 ≤ (5 : ℝ) / 6 - (lam + w0) / 2 - 5 * s / 2 := by
    linarith
  have hLA :
      14 * lam * ((5 : ℝ) / 6 - (lam + w0) / 2 - 5 * s / 2) ≤
        L * ((5 : ℝ) / 6 - (lam + w0) / 2 - 5 * s / 2) :=
    mul_le_mul_of_nonneg_right hL hcoef
  have hlam_sq : lam ^ 2 < (49 : ℝ) / 100 := by
    have hp : 0 < lam * ((7 : ℝ) / 10 - lam) :=
      mul_pos hlam0 (sub_pos.mpr hlam_hi)
    nlinarith
  have hlam_w0 : lam * w0 < (1 : ℝ) / 5 := by
    have hp : 0 < lam * ((2 : ℝ) / 7 - w0) :=
      mul_pos hlam0 (sub_pos.mpr hw0)
    nlinarith
  have hlam_s : lam * s ≤ (7 : ℝ) / 163840 := by
    have hp : 0 ≤ ((7 : ℝ) / 10 - lam) * s :=
      mul_nonneg (sub_nonneg.mpr hlam_hi.le) hs0
    nlinarith
  have hcore :
      (4977691 : ℝ) / 1843200 <
        (71 : ℝ) / 6 * lam + 1 / 3 - 8 * lam ^ 2 -
          8 * (lam * w0) + s ^ 2 - 7 * s / 6 -
          37 * (lam * s) := by
    nlinarith [hlam_sq, hlam_w0, hlam_s, sq_nonneg s]
  nlinarith [hLA, hcore]

/-- Abstract monotonicity step converting the four displayed analytic
inequalities before (M41) into the exact rational margin. -/
lemma lrLowRatioM41_core_of_bounds
    {s L lam rho q D B p g : ℝ}
    (hs0 : 0 ≤ s) (hs : s ≤ (1 : ℝ) / 16384)
    (hL : 14 * lam ≤ L)
    (hlam_lo : (2 : ℝ) / 3 < lam)
    (hlam_hi : lam < (7 : ℝ) / 10)
    (hrho : 0 ≤ rho) (hq : (-2 / 7 : ℝ) < q)
    (hD0 : 0 ≤ D) (_hB0 : 0 ≤ B)
    (hD : (L - lam + rho) / 2 + 1 / 3 - s / 2 ≤ D)
    (hB : B ≤ L / 2 + lam)
    (hp : L + 2 * lam + 1 - 2 * s ≤ p)
    (hS : -L - rho + q - 2 * s ≤ p - g)
    (hSnonpos : p - g ≤ 0) :
    (4977691 : ℝ) / 1843200 < D * p + B * (p - g) := by
  let p0 := L + 2 * lam + 1 - 2 * s
  let S0 := -L - rho + q - 2 * s
  let D0 := (L - lam + rho) / 2 + 1 / 3 - s / 2
  let B0 := L / 2 + lam
  have hlam0 : 0 < lam := by linarith
  have hL0 : 0 < L := by nlinarith
  have hp0 : 0 ≤ p0 := by
    dsimp [p0]
    nlinarith
  have hD00 : 0 ≤ D0 := by
    dsimp [D0]
    nlinarith
  have hB0 : 0 ≤ B0 := by
    dsimp [B0]
    nlinarith
  have hDp : D0 * p0 ≤ D * p := by
    exact mul_le_mul hD hp hp0 hD0
  have hBS0 : B0 * S0 ≤ B * (p - g) := by
    have hleft : B0 * S0 ≤ B0 * (p - g) :=
      mul_le_mul_of_nonneg_left hS hB0
    have hright : B0 * (p - g) ≤ B * (p - g) :=
      mul_le_mul_of_nonpos_right hB hSnonpos
    exact hleft.trans hright
  have hcore : D0 * p0 + B0 * S0 ≤ D * p + B * (p - g) :=
    add_le_add hDp hBS0
  let w0 := -q
  have hw0 : w0 < (2 : ℝ) / 7 := by
    dsimp [w0]
    linarith
  have hscalar := lrLowRatioM41_scalar s L lam w0 hs0 hs hL
    hlam_lo hlam_hi hw0
  have hrhoTerm : 0 ≤ rho * (1 - 2 * s) :=
    mul_nonneg hrho (by nlinarith)
  have hE :
      L * ((5 : ℝ) / 6 - (lam + w0) / 2 - 5 * s / 2) +
          1 / 3 + lam / 6 - lam ^ 2 - lam * w0 +
          s ^ 2 - 7 * s / 6 - 2 * lam * s ≤
        D0 * p0 + B0 * S0 := by
    dsimp [D0, p0, B0, S0, w0]
    nlinarith [hrhoTerm]
  exact hscalar.trans_le (hE.trans hcore)

/-- Fully analytic M41: the frozen logarithmic first bracket exceeds the
audited exact rational margin throughout the low-ratio small-`s` strip. -/
theorem lrLowRatioFrozenFirstBracketNormalized_gt_M41
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hregion : LRDeterminantLowRatioRegion point)
    (hsSmall : point.s ≤ 1 / 16384) :
    (4977691 : ℝ) / 1843200 <
      lrLowRatioFrozenFirstBracketNormalized point := by
  have hs : point.s ∈ Ioc (0 : ℝ) (1 / 16384) :=
    ⟨hinterior.1.1, hsSmall⟩
  have hLraw := lrSmallSBridge_log_lower hs
  have hL : 14 * Real.log 2 ≤ lrLowRatioLogScale point := by
    simpa [lrLowRatioLogScale] using hLraw
  have hchi : point.chi ∈ Icc (0 : ℝ) 1 :=
    ⟨hinterior.2.2.1.le, hinterior.2.2.2.le⟩
  have hq := lrSmallSBridgeQChi_lower hchi
  have hrho := lrLowRatioRho_nonnegative hinterior hregion
  have hD0 := lrDeterminantD1_nonnegative hinterior
  have hB0 := (lrCertificateBFlow_pos hinterior).le
  have hD := lrLowRatio_D1_lower hinterior hregion
  have hB := lrLowRatio_B_upper hinterior
  have hp := lrLowRatioP_lower hinterior hregion
  have hS := lrLowRatioP_sub_G_lower hinterior hregion
  have hSnonpos := lrLowRatioP_sub_G_nonpositive hinterior hregion
  unfold lrLowRatioFrozenFirstBracketNormalized
  exact lrLowRatioM41_core_of_bounds
    hinterior.1.1.le hsSmall hL
    (by
      exact (by norm_num : (2 / 3 : ℝ) < 0.6931471803).trans
        Real.log_two_gt_d9)
    (Real.log_two_lt_d9.trans (by norm_num))
    hrho hq hD0 hB0 hD hB hp hS hSnonpos

lemma lrLowRatioNormalization_pos
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point) :
    0 < lrLowRatioNormalization point := by
  unfold lrLowRatioNormalization
  exact div_pos
    (mul_pos hinterior.2.1.1 (by linarith [hinterior.2.2.1]))
    (by norm_num)

lemma lrLowRatio_log_four_div_split
    {s : ℝ} (hs : 0 < s) :
    Real.log (4 / s) = Real.log (1 / s) + 2 * Real.log 2 := by
  rw [show 4 / s = 4 * (1 / s) by ring,
    Real.log_mul (by norm_num : (4 : ℝ) ≠ 0)
      (one_div_ne_zero hs.ne'),
    show Real.log 4 = 2 * Real.log 2 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num]
  ring

/-- The three endpoint envelopes used in the two M42 restoration budgets. -/
lemma lrLowRatio_smallS_envelopes
    {s : ℝ} (hs : s ∈ Ioc (0 : ℝ) (1 / 16384)) :
    s * (Real.log (1 / s) + 3) <
        (1 / 16384 : ℝ) * (64 / 5) ∧
      s * (Real.log (1 / s) + 11) <
        (1 / 16384 : ℝ) * (104 / 5) ∧
      s * (Real.log (1 / s) + 2 * Real.log 2) <
        (1 / 16384 : ℝ) * (56 / 5) := by
  let s0 : ℝ := 1 / 16384
  let L := Real.log (1 / s)
  let lam := Real.log 2
  have hlogEndpoint : Real.log (4 / s0) = 16 * lam := by
    dsimp [s0, lam]
    rw [show (4 / (1 / 16384 : ℝ)) = 2 ^ 16 by norm_num,
      Real.log_pow]
    norm_num
  have hendpointOne : 1 ≤ Real.log (4 / s0) := by
    rw [hlogEndpoint]
    dsimp [lam]
    nlinarith [Real.log_two_gt_d9]
  have hmul := mul_log_four_div_le_endpoint hs.1
    (by norm_num : (0 : ℝ) < s0) hs.2 hendpointOne
  have hsplit : Real.log (4 / s) = L + 2 * lam := by
    simpa [L, lam] using lrLowRatio_log_four_div_split hs.1
  rw [hsplit, hlogEndpoint] at hmul
  have hlamLo : (2 / 3 : ℝ) < lam := by
    dsimp [lam]
    exact (by norm_num : (2 / 3 : ℝ) < 0.6931471803).trans
      Real.log_two_gt_d9
  have hlamHi : lam < (7 / 10 : ℝ) := by
    dsimp [lam]
    exact Real.log_two_lt_d9.trans (by norm_num)
  have hthreeCoeff : 0 ≤ 3 - 2 * lam := by linarith
  have helevenCoeff : 0 ≤ 11 - 2 * lam := by linarith
  have hthreeLinear : s * (3 - 2 * lam) ≤
      s0 * (3 - 2 * lam) :=
    mul_le_mul_of_nonneg_right hs.2 hthreeCoeff
  have helevenLinear : s * (11 - 2 * lam) ≤
      s0 * (11 - 2 * lam) :=
    mul_le_mul_of_nonneg_right hs.2 helevenCoeff
  have h3 : s * (L + 3) < s0 * (64 / 5) := by
    have hsum : s * (L + 3) ≤ s0 * (14 * lam + 3) := by
      calc
        s * (L + 3) = s * (L + 2 * lam) +
            s * (3 - 2 * lam) := by ring
        _ ≤ s0 * (16 * lam) + s0 * (3 - 2 * lam) :=
          add_le_add hmul hthreeLinear
        _ = s0 * (14 * lam + 3) := by ring
    have hend : s0 * (14 * lam + 3) < s0 * (64 / 5) := by
      exact mul_lt_mul_of_pos_left (by nlinarith) (by norm_num)
    exact hsum.trans_lt hend
  have h11 : s * (L + 11) < s0 * (104 / 5) := by
    have hsum : s * (L + 11) ≤ s0 * (14 * lam + 11) := by
      calc
        s * (L + 11) = s * (L + 2 * lam) +
            s * (11 - 2 * lam) := by ring
        _ ≤ s0 * (16 * lam) + s0 * (11 - 2 * lam) :=
          add_le_add hmul helevenLinear
        _ = s0 * (14 * lam + 11) := by ring
    have hend : s0 * (14 * lam + 11) < s0 * (104 / 5) := by
      exact mul_lt_mul_of_pos_left (by nlinarith) (by norm_num)
    exact hsum.trans_lt hend
  have h2 : s * (L + 2 * lam) < s0 * (56 / 5) := by
    have hend : s0 * (16 * lam) < s0 * (56 / 5) := by
      exact mul_lt_mul_of_pos_left (by nlinarith) (by norm_num)
    exact hmul.trans_lt hend
  simpa only [s0, L, lam] using ⟨h3, h11, h2⟩

lemma lrLowRatio_channel_budget_envelope
    {s : ℝ} (hs : s ∈ Ioc (0 : ℝ) (1 / 16384)) :
    4 * s ^ 2 * (Real.log (1 / s) + 3) *
        (Real.log (1 / s) + 11) < lrLowRatioEpsilonChannel := by
  rcases lrLowRatio_smallS_envelopes hs with ⟨h3, h11, _⟩
  have hL := lrSmallSBridge_log_lower hs
  have h11pos : 0 < s * (Real.log (1 / s) + 11) := by
    exact mul_pos hs.1 (by nlinarith [Real.log_two_gt_d9])
  have h3upperPos : 0 < (1 / 16384 : ℝ) * (64 / 5) := by norm_num
  have hprod := mul_lt_mul_of_pos' h3 h11 h11pos h3upperPos
  unfold lrLowRatioEpsilonChannel
  have hid :
      4 * s ^ 2 * (Real.log (1 / s) + 3) *
          (Real.log (1 / s) + 11) =
        4 * (s * (Real.log (1 / s) + 3)) *
          (s * (Real.log (1 / s) + 11)) := by ring
  rw [hid]
  nlinarith

lemma lrLowRatio_entropy_budget_envelope
    {s : ℝ} (hs : s ∈ Ioc (0 : ℝ) (1 / 16384)) :
    (32 / 3 : ℝ) * (Real.log (1 / s) + 3) * s ^ 4 *
        (Real.log (1 / s) + 2 * Real.log 2) <
      lrLowRatioEpsilonEntropy := by
  rcases lrLowRatio_smallS_envelopes hs with ⟨h3, _, h2⟩
  have hL := lrSmallSBridge_log_lower hs
  have h2pos : 0 <
      s * (Real.log (1 / s) + 2 * Real.log 2) := by
    exact mul_pos hs.1 (by nlinarith [Real.log_two_gt_d9])
  have h3upperPos : 0 < (1 / 16384 : ℝ) * (64 / 5) := by norm_num
  have hprod := mul_lt_mul_of_pos' h3 h2 h2pos h3upperPos
  have hsSq : s ^ 2 ≤ (1 / 16384 : ℝ) ^ 2 := by
    simpa [pow_two] using mul_self_le_mul_self hs.1.le hs.2
  have hscaleFirst := mul_lt_mul_of_pos_left hprod (sq_pos_of_pos hs.1)
  have hupperProductNonneg : 0 ≤
      ((1 / 16384 : ℝ) * (64 / 5)) *
        ((1 / 16384 : ℝ) * (56 / 5)) := by norm_num
  have hscaleSecond :=
    mul_le_mul_of_nonneg_right hsSq hupperProductNonneg
  have hscale :
      s ^ 2 *
          ((s * (Real.log (1 / s) + 3)) *
            (s * (Real.log (1 / s) + 2 * Real.log 2))) <
        (1 / 16384 : ℝ) ^ 2 *
          (((1 / 16384 : ℝ) * (64 / 5)) *
            ((1 / 16384 : ℝ) * (56 / 5))) :=
    hscaleFirst.trans_le hscaleSecond
  unfold lrLowRatioEpsilonEntropy
  have hid :
      (32 / 3 : ℝ) * (Real.log (1 / s) + 3) * s ^ 4 *
          (Real.log (1 / s) + 2 * Real.log 2) =
        (32 / 3 : ℝ) * s ^ 2 *
          ((s * (Real.log (1 / s) + 3)) *
            (s * (Real.log (1 / s) + 2 * Real.log 2))) := by ring
  rw [hid]
  nlinarith

lemma lrLowRatio_M42_payment_arithmetic :
    (27 / 10 : ℝ) <
      4977691 / 1843200 - lrLowRatioEpsilonChannel -
        lrLowRatioEpsilonEntropy := by
  unfold lrLowRatioEpsilonChannel lrLowRatioEpsilonEntropy
  norm_num

/-! ## Exact low-ratio restoration

The published small-`s` bridge assumes the raw coordinate `k` is bounded
away from zero.  In the low-ratio chart it is instead `K = k / s` that is
bounded away from zero.  The next two lemmas repeat only the algebraic
identifications from that bridge, with their actual positivity hypotheses.
They are what permits the M42 restoration argument to be used at `k = s K`.
-/

lemma lrLowRatioQ0G_frozen_eq_of_pos
    {s k chi : ℝ} (hs : 0 < s) (hk : 0 < k)
    (hchi : chi ∈ Icc (0 : ℝ) 1) :
    lrLowerFaceQ0 (chi * (s * k)) + lrLowerFaceQ0 (s * k) =
      s * k * (1 + chi) / 4 *
        lrSmallSBridgeG k chi (Real.log (1 / s)) := by
  have hePos : 0 < s * k := mul_pos hs hk
  have hlogE : Real.log (s * k) = Real.log s + Real.log k :=
    Real.log_mul hs.ne' hk.ne'
  have hlogInv : Real.log (1 / s) = -Real.log s := by
    rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) hs.ne']
    norm_num
  have hlogFour := lrSmallSBridge_log_four
  rcases hchi.1.eq_or_lt with rfl | hchiPos
  · simp only [zero_mul]
    unfold lrLowerFaceQ0 lrSmallSBridgeG lrSmallSBridgeQChi
    rw [Real.log_div (by norm_num : (4 : ℝ) ≠ 0) hePos.ne',
      hlogE, hlogInv, hlogFour]
    norm_num
    field_simp [hs.ne', hk.ne']
    ring_nf
    simp [hs.ne', hk.ne']
  · have hchiEPos : 0 < chi * (s * k) := mul_pos hchiPos hePos
    have hlogChiE : Real.log (chi * (s * k)) =
        Real.log chi + Real.log s + Real.log k := by
      rw [Real.log_mul hchiPos.ne' hePos.ne', hlogE]
      ring
    unfold lrLowerFaceQ0 lrSmallSBridgeG lrSmallSBridgeQChi
    rw [Real.log_div (by norm_num : (4 : ℝ) ≠ 0) hchiEPos.ne',
      Real.log_div (by norm_num : (4 : ℝ) ≠ 0) hePos.ne',
      hlogChiE, hlogE, hlogInv, hlogFour]
    field_simp [show 1 + chi ≠ 0 by linarith]
    ring

lemma lrLowRatioPWQ0_frozen_eq_of_physical
    {s k chi : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) (hk : 0 < k)
    (hsk : s * k < 1) (hchi : chi ∈ Icc (0 : ℝ) 1) :
    lrLowerFacePWQ0 s k chi 1 =
      s * k * (1 + chi) / 4 *
          lrSmallSBridgeS s k chi (Real.log (1 / s)) + s / 2 := by
  have houterPos : 0 < 1 + (1 - s) * k := by
    have hR : 0 ≤ 1 - s := sub_nonneg.mpr hs.2.le
    positivity
  have hlogOuter :
      Real.log ((1 + (1 - s) * k) / k) =
        Real.log (1 + (1 - s) * k) - Real.log k := by
    rw [Real.log_div houterPos.ne' hk.ne']
  rcases hchi.1.eq_or_lt with rfl | hchiPos
  · unfold lrLowerFacePWQ0
    simp only [zero_mul, div_one]
    rw [lrLowerFaceOmegaQ0_zero hs.1,
      lrLowerFaceOmegaQ0_sk_eq hs hk hsk, hlogOuter]
    unfold lrSmallSBridgeS lrSmallSBridgeP lrSmallSBridgeG
      lrSmallSBridgeAR lrSmallSBridgeQChi
    simp only [zero_mul, zero_div, zero_add]
    field_simp
    ring
  · have hchiKPos : 0 < chi * k := mul_pos hchiPos hk
    have hchiE : chi * (s * k) = s * (chi * k) := by ring
    have hchiELt : s * (chi * k) < 1 := by
      rw [← hchiE]
      exact (mul_le_of_le_one_left (mul_pos hs.1 hk).le hchi.2).trans_lt hsk
    have hinnerPos : 0 < 1 + (1 - s) * k * chi := by
      have hR : 0 ≤ 1 - s := sub_nonneg.mpr hs.2.le
      positivity
    have hlogInner :
        Real.log ((1 + (1 - s) * (chi * k)) / (chi * k)) =
          Real.log (1 + (1 - s) * k * chi) -
            Real.log chi - Real.log k := by
      have hinnerEq :
          1 + (1 - s) * (chi * k) = 1 + (1 - s) * k * chi := by ring
      rw [hinnerEq, Real.log_div hinnerPos.ne' hchiKPos.ne',
        Real.log_mul hchiPos.ne' hk.ne']
      ring
    unfold lrLowerFacePWQ0
    rw [hchiE,
      lrLowerFaceOmegaQ0_sk_eq hs hchiKPos hchiELt,
      lrLowerFaceOmegaQ0_sk_eq hs hk hsk,
      hlogInner, hlogOuter]
    unfold lrSmallSBridgeS lrSmallSBridgeP lrSmallSBridgeG
      lrSmallSBridgeAR lrSmallSBridgeQChi
    field_simp [show 1 + chi ≠ 0 by linarith]
    ring

noncomputable def lrLowRatioQ0FrozenG (point : CertificatePoint) : ℝ :=
  lrLowerFaceQ0 (lrCertificateY0 point) +
    lrLowerFaceQ0 (lrCertificateE point)

noncomputable def lrLowRatioR0Omega (point : CertificatePoint) : ℝ :=
  lrLowerFacePWR0 point.s point.k point.chi (lrCertificateV point) -
    4 * lrLowerFaceOmegaR0 point.s 0 /
      (1 + lrCertificateV point)

lemma lrLowRatioQ0FrozenG_eq_normalized
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hregion : LRDeterminantLowRatioRegion point) :
    lrLowRatioQ0FrozenG point =
      lrLowRatioNormalization point * lrLowRatioG point := by
  have hk : 0 < point.k := by
    linarith [hregion.1, hinterior.1.1]
  have h := lrLowRatioQ0G_frozen_eq_of_pos
    hinterior.1.1 hk
    (show point.chi ∈ Icc (0 : ℝ) 1 from
      ⟨hinterior.2.2.1.le, hinterior.2.2.2.le⟩)
  simpa [lrLowRatioQ0FrozenG, lrLowRatioNormalization,
    lrLowRatioG, lrLowRatioLogScale, lrCertificateY0,
    lrCertificateE] using h

lemma lrLowRatioQ0FrozenOmega_eq_normalized
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hregion : LRDeterminantLowRatioRegion point) :
    lrLowRatioQ0FrozenOmega point =
      lrLowRatioNormalization point *
        (lrLowRatioP point - lrLowRatioG point) := by
  have hs : point.s ∈ Ioo (0 : ℝ) 1 := hinterior.1
  have hk : 0 < point.k := by linarith [hregion.1, hs.1]
  have hPW := lrLowRatioPWQ0_frozen_eq_of_physical hs hk
    (by simpa [lrCertificateE] using hinterior.2.1.2)
    (show point.chi ∈ Icc (0 : ℝ) 1 from
      ⟨hinterior.2.2.1.le, hinterior.2.2.2.le⟩)
  have hW := lrLowerFaceOmegaQ0_zero hs.1
  unfold lrLowRatioQ0FrozenOmega
  rw [hPW, hW]
  unfold lrLowRatioNormalization lrLowRatioP lrLowRatioG
    lrLowRatioLogScale lrSmallSBridgeS lrCertificateE
  ring

lemma lrLowRatioQ0G_eq_frozen_add_delta (point : CertificatePoint) :
    lrSmallSBridgeQ0G point =
      lrLowRatioQ0FrozenG point + lrSmallSBridgeQ0DeltaG point := by
  simpa [lrLowRatioQ0FrozenG] using
    lrSmallSBridgeQ0G_eq_frozen_add_delta point

lemma lrLowRatioQ0Omega_eq_frozen_add_delta (point : CertificatePoint) :
    lrLowRatioQ0Omega point =
      lrLowRatioQ0FrozenOmega point + lrLowRatioQ0DeltaOmega point := by
  unfold lrLowRatioQ0DeltaOmega
  ring

lemma lrLowRatio_B_add_D1_upper
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hregion : LRDeterminantLowRatioRegion point)
    (hsSmall : point.s ≤ 1 / 16384) :
    lrCertificateBFlow point + lrDeterminantD1 point ≤
      lrLowRatioLogScale point + 3 := by
  have hD1 := lrDeterminantD1_le_D hinterior
  have hlog := lrLowRatio_outer_log_upper hinterior hregion
  have hY := lrLowRatio_determinantY_formula hinterior hregion
  have hDform := lrCertificateD_eq_half_log_determinantY hinterior
  have hDupper : lrCertificateD point ≤
      (lrLowRatioLogScale point + 2 * Real.log 2 + point.s) / 2 := by
    rw [hDform, hY]
    nlinarith
  have hB := lrLowRatio_B_upper hinterior
  have hlam : Real.log 2 < (7 / 10 : ℝ) :=
    Real.log_two_lt_d9.trans (by norm_num)
  nlinarith

lemma lrLowRatio_D1_upper
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hregion : LRDeterminantLowRatioRegion point)
    (hsSmall : point.s ≤ 1 / 16384) :
    lrDeterminantD1 point ≤ lrLowRatioLogScale point + 3 := by
  have hsum := lrLowRatio_B_add_D1_upper hinterior hregion hsSmall
  have hB := (lrCertificateBFlow_pos hinterior).le
  linarith

lemma lrLowRatioR0G_nonnegative
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point) :
    0 ≤ lrSmallSBridgeR0G point := by
  have he := hinterior.2.1
  have hv := lrCertificateV_mem_Ioo hinterior
  have hchi : point.chi ∈ Icc (0 : ℝ) 1 :=
    ⟨hinterior.2.2.1.le, hinterior.2.2.2.le⟩
  have hy0 : lrCertificateY0 point ∈ Ico (0 : ℝ) 1 := by
    unfold lrCertificateY0
    constructor
    · exact mul_nonneg hchi.1 he.1.le
    · exact (mul_le_of_le_one_left he.1.le hchi.2).trans_lt he.2
  have hrY := lrLowerFaceR0_nonneg_closed hy0
  have hrE := lrLowerFaceR0_nonneg_closed
    (show lrCertificateE point ∈ Ico (0 : ℝ) 1 from ⟨he.1.le, he.2⟩)
  unfold lrSmallSBridgeR0G
  exact add_nonneg hrY (div_nonneg hrE hv.1.le)

lemma lrLowRatioR0Omega_lower
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hregion : LRDeterminantLowRatioRegion point)
    (hsSmall : point.s ≤ 1 / 16384) :
    -lrLowRatioKappa point * point.s * lrLowerFaceR0Prime point.s ≤
      lrLowRatioR0Omega point := by
  let v := lrCertificateV point
  let w := lrLowerFaceOmegaR0 point.s 0
  have hs : point.s ∈ Ioo (0 : ℝ) 1 := hinterior.1
  have he := hinterior.2.1
  have hv := lrCertificateV_mem_Ioo hinterior
  have hchi : point.chi ∈ Icc (0 : ℝ) 1 :=
    ⟨hinterior.2.2.1.le, hinterior.2.2.2.le⟩
  have hy0 : lrCertificateY0 point ∈ Ico (0 : ℝ) 1 := by
    unfold lrCertificateY0
    constructor
    · exact mul_nonneg hchi.1 he.1.le
    · exact (mul_le_of_le_one_left he.1.le hchi.2).trans_lt he.2
  have hmono := lrLowerFaceOmegaR0_monotoneOn_Ico hs
  have hzero : (0 : ℝ) ∈ Ico (0 : ℝ) 1 := ⟨le_rfl, by norm_num⟩
  have hY := hmono hzero hy0 hy0.1
  have hE := hmono hzero
    (show lrCertificateE point ∈ Ico (0 : ℝ) 1 from ⟨he.1.le, he.2⟩)
    he.1.le
  have hEDiv : w / v ≤
      lrLowerFaceOmegaR0 point.s (lrCertificateE point) / v := by
    exact div_le_div_of_nonneg_right (by simpa [w] using hE) hv.1.le
  have hPW : (1 + 1 / v) * w ≤
      lrLowerFacePWR0 point.s point.k point.chi v := by
    unfold lrLowerFacePWR0
    have hadd := add_le_add (by simpa [w] using hY) hEDiv
    convert hadd using 1
    field_simp [hv.1.ne']
    ring
  have hkId := (lrLowRatio_weight_identities hinterior).2.2
  have hcoeff :
      1 + 1 / v - 4 / (1 + v) = lrLowRatioKappa point := by
    rw [hkId]
    dsimp [v]
    field_simp [hv.1.ne', (by linarith [hv.1] : 1 + lrCertificateV point ≠ 0)]
    ring
  have hOmegaBase : lrLowRatioKappa point * w ≤
      lrLowRatioR0Omega point := by
    calc
      lrLowRatioKappa point * w =
          (1 + 1 / v) * w - 4 * w / (1 + v) := by
            rw [← hcoeff]
            ring
      _ ≤ lrLowerFacePWR0 point.s point.k point.chi v -
          4 * w / (1 + v) := sub_le_sub_right hPW _
      _ = lrLowRatioR0Omega point := by
        unfold lrLowRatioR0Omega
        simp only [v, w]
  have hwLower := lrLowerFaceOmegaR0_zero_lower hs
  have hk0 := (lrLowRatio_weight_bounds hinterior hregion hsSmall).2.2.2.2.1
  have hscaled := mul_le_mul_of_nonneg_left hwLower hk0
  have hlower :
      -lrLowRatioKappa point * point.s * lrLowerFaceR0Prime point.s ≤
        lrLowRatioKappa point * w := by
    calc
      -lrLowRatioKappa point * point.s * lrLowerFaceR0Prime point.s =
          lrLowRatioKappa point *
            (-point.s * lrLowerFaceR0Prime point.s) := by ring
      _ ≤ lrLowRatioKappa point * w := hscaled
  exact hlower.trans hOmegaBase

noncomputable def lrLowRatioQ0FirstBracketCore
    (point : CertificatePoint) : ℝ :=
  lrDeterminantD1 point * lrSmallSBridgeQ0G point +
    (lrCertificateBFlow point + lrDeterminantD1 point) *
      lrLowRatioQ0Omega point

noncomputable def lrLowRatioR0FirstBracketCore
    (point : CertificatePoint) : ℝ :=
  lrDeterminantD1 point * lrSmallSBridgeR0G point +
    (lrCertificateBFlow point + lrDeterminantD1 point) *
      lrLowRatioR0Omega point

lemma lrLowRatioQ0FirstBracketCore_eq_frozen_add
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hregion : LRDeterminantLowRatioRegion point) :
    lrLowRatioQ0FirstBracketCore point =
      lrLowRatioNormalization point *
          lrLowRatioFrozenFirstBracketNormalized point +
        lrDeterminantD1 point * lrSmallSBridgeQ0DeltaG point +
        (lrCertificateBFlow point + lrDeterminantD1 point) *
          lrLowRatioQ0DeltaOmega point := by
  unfold lrLowRatioQ0FirstBracketCore
  rw [lrLowRatioQ0G_eq_frozen_add_delta,
    lrLowRatioQ0Omega_eq_frozen_add_delta,
    lrLowRatioQ0FrozenG_eq_normalized hinterior hregion,
    lrLowRatioQ0FrozenOmega_eq_normalized hinterior hregion]
  unfold lrLowRatioFrozenFirstBracketNormalized
  ring

lemma lrLowRatioFirstBracket_eq_q0_add_r0_add_atom
    (point : CertificatePoint) :
    lrDeterminantFirstBracket
        (lrCertificateBFlow point) (lrDeterminantD1 point)
        (lrCertificateGShape point) (lrDeterminantPsi point)
        (lrDeterminantDelta point) (lrCertificateW point) =
      lrLowRatioQ0FirstBracketCore point +
        lrLowRatioR0FirstBracketCore point +
        4 * lrCertificateBFlow point * lrDeterminantDelta point *
          lrCertificateW point := by
  unfold lrDeterminantFirstBracket lrDeterminantPsi
  rw [lrCertificateGShape_eq_smallSBridge_split,
    lrCertificatePW_eq_smallSBridge_split,
    lrCertificateW_eq_smallSBridge_split]
  unfold lrLowRatioQ0FirstBracketCore lrLowRatioR0FirstBracketCore
    lrLowRatioQ0Omega lrLowRatioR0Omega
  ring

lemma lrLowRatio_e_sq_le_four_s_sq_mul_normalization
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hregion : LRDeterminantLowRatioRegion point) :
    lrCertificateE point ^ 2 ≤
      4 * point.s ^ 2 * lrLowRatioNormalization point := by
  have he0 : 0 ≤ lrCertificateE point := hinterior.2.1.1.le
  have hes := lrLowRatioE_le_s_sq hinterior hregion
  have hchi0 : 0 ≤ point.chi := hinterior.2.2.1.le
  have hfirst : lrCertificateE point ^ 2 ≤
      lrCertificateE point * point.s ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_left hes he0
    nlinarith
  have hsecond : lrCertificateE point * point.s ^ 2 ≤
      lrCertificateE point * point.s ^ 2 * (1 + point.chi) := by
    have hextra : 0 ≤
        lrCertificateE point * point.s ^ 2 * point.chi :=
      mul_nonneg (mul_nonneg he0 (sq_nonneg point.s)) hchi0
    nlinarith
  calc
    lrCertificateE point ^ 2 ≤
        lrCertificateE point * point.s ^ 2 := hfirst
    _ ≤ lrCertificateE point * point.s ^ 2 * (1 + point.chi) := hsecond
    _ = 4 * point.s ^ 2 * lrLowRatioNormalization point := by
      unfold lrLowRatioNormalization
      ring

lemma lrLowRatioQ0FirstBracketCore_restoration
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hregion : LRDeterminantLowRatioRegion point)
    (hsSmall : point.s ≤ 1 / 16384) :
    lrLowRatioNormalization point *
        (lrLowRatioFrozenFirstBracketNormalized point -
          lrLowRatioEpsilonChannel) <
      lrLowRatioQ0FirstBracketCore point := by
  let L := lrLowRatioLogScale point
  let A := L + 3
  let C := L + 2 * Real.log 2 + 1
  let e := lrCertificateE point
  let n := lrLowRatioNormalization point
  let D1 := lrDeterminantD1 point
  let B1 := lrCertificateBFlow point + lrDeterminantD1 point
  have hs : point.s ∈ Ioc (0 : ℝ) (1 / 16384) :=
    ⟨hinterior.1.1, hsSmall⟩
  have hLraw := lrSmallSBridge_log_lower hs
  have hL : 14 * Real.log 2 ≤ L := by
    simpa [L, lrLowRatioLogScale] using hLraw
  have hlam0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hA0 : 0 ≤ A := by dsimp [A]; nlinarith
  have hC0 : 0 ≤ C := by dsimp [C]; nlinarith
  have hL11 : 0 ≤ L + 11 := by nlinarith
  have he0 : 0 ≤ e := by simpa [e] using hinterior.2.1.1.le
  have hn0 : 0 < n := by
    simpa [n] using lrLowRatioNormalization_pos hinterior
  have hD0 : 0 ≤ D1 := by
    simpa [D1] using lrDeterminantD1_nonnegative hinterior
  have hB0 : 0 ≤ lrCertificateBFlow point :=
    (lrCertificateBFlow_pos hinterior).le
  have hB10 : 0 ≤ B1 := by dsimp [B1]; linarith
  have hDUpper : D1 ≤ A := by
    simpa [D1, A, L] using
      lrLowRatio_D1_upper hinterior hregion hsSmall
  have hB1Upper : B1 ≤ A := by
    simpa [B1, A, L] using
      lrLowRatio_B_add_D1_upper hinterior hregion hsSmall
  have hdeltaG : -8 * e ^ 2 ≤ lrSmallSBridgeQ0DeltaG point := by
    simpa [e] using lrLowRatioQ0DeltaG_lower hinterior hregion hsSmall
  have hdeltaOmega : -e ^ 2 * C ≤ lrLowRatioQ0DeltaOmega point := by
    simpa [e, C, L] using
      lrLowRatioQ0DeltaOmega_lower hinterior hregion hsSmall
  have hDG : -A * (8 * e ^ 2) ≤
      D1 * lrSmallSBridgeQ0DeltaG point := by
    have hnegative : -8 * e ^ 2 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by norm_num) (sq_nonneg e)
    have hcoeff : A * (-8 * e ^ 2) ≤ D1 * (-8 * e ^ 2) :=
      mul_le_mul_of_nonpos_right hDUpper hnegative
    have hrestore := mul_le_mul_of_nonneg_left hdeltaG hD0
    calc
      -A * (8 * e ^ 2) = A * (-8 * e ^ 2) := by ring
      _ ≤ D1 * (-8 * e ^ 2) := hcoeff
      _ ≤ D1 * lrSmallSBridgeQ0DeltaG point := hrestore
  have hBOmega : -A * (e ^ 2 * C) ≤
      B1 * lrLowRatioQ0DeltaOmega point := by
    have hnegative : -e ^ 2 * C ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg e)) hC0
    have hcoeff : A * (-e ^ 2 * C) ≤ B1 * (-e ^ 2 * C) :=
      mul_le_mul_of_nonpos_right hB1Upper hnegative
    have hrestore := mul_le_mul_of_nonneg_left hdeltaOmega hB10
    calc
      -A * (e ^ 2 * C) = A * (-e ^ 2 * C) := by ring
      _ ≤ B1 * (-e ^ 2 * C) := hcoeff
      _ ≤ B1 * lrLowRatioQ0DeltaOmega point := hrestore
  have hC8 : C + 8 ≤ L + 11 := by
    dsimp [C]
    nlinarith [Real.log_two_lt_d9]
  have hC8nonneg : 0 ≤ C + 8 := by linarith
  have hcostCompare : A * e ^ 2 * (C + 8) ≤
      A * e ^ 2 * (L + 11) :=
    mul_le_mul_of_nonneg_left hC8 (mul_nonneg hA0 (sq_nonneg e))
  have hchanges : -A * e ^ 2 * (L + 11) ≤
      D1 * lrSmallSBridgeQ0DeltaG point +
        B1 * lrLowRatioQ0DeltaOmega point := by
    have hsum : -A * e ^ 2 * (C + 8) ≤
        D1 * lrSmallSBridgeQ0DeltaG point +
          B1 * lrLowRatioQ0DeltaOmega point := by
      nlinarith [hDG, hBOmega]
    nlinarith [hcostCompare]
  have heScale : e ^ 2 ≤ 4 * point.s ^ 2 * n := by
    simpa [e, n] using
      lrLowRatio_e_sq_le_four_s_sq_mul_normalization hinterior hregion
  have hfactor0 : 0 ≤ A * (L + 11) := mul_nonneg hA0 hL11
  have hcostScale : A * e ^ 2 * (L + 11) ≤
      n * (4 * point.s ^ 2 * A * (L + 11)) := by
    have hmul := mul_le_mul_of_nonneg_right heScale hfactor0
    calc
      A * e ^ 2 * (L + 11) = e ^ 2 * (A * (L + 11)) := by ring
      _ ≤ (4 * point.s ^ 2 * n) * (A * (L + 11)) := hmul
      _ = n * (4 * point.s ^ 2 * A * (L + 11)) := by ring
  have hbudget := lrLowRatio_channel_budget_envelope hs
  have hbudget' : 4 * point.s ^ 2 * A * (L + 11) <
      lrLowRatioEpsilonChannel := by
    simpa [A, L, lrLowRatioLogScale] using hbudget
  have hbudgetScaled :
      n * (4 * point.s ^ 2 * A * (L + 11)) <
        n * lrLowRatioEpsilonChannel :=
    mul_lt_mul_of_pos_left hbudget' hn0
  have hcost : A * e ^ 2 * (L + 11) <
      n * lrLowRatioEpsilonChannel :=
    hcostScale.trans_lt hbudgetScaled
  have hexact := lrLowRatioQ0FirstBracketCore_eq_frozen_add
    hinterior hregion
  have hexact' : lrLowRatioQ0FirstBracketCore point =
      n * lrLowRatioFrozenFirstBracketNormalized point +
        D1 * lrSmallSBridgeQ0DeltaG point +
        B1 * lrLowRatioQ0DeltaOmega point := by
    simpa [n, D1, B1] using hexact
  change n *
      (lrLowRatioFrozenFirstBracketNormalized point -
        lrLowRatioEpsilonChannel) < lrLowRatioQ0FirstBracketCore point
  rw [hexact']
  nlinarith

lemma lrLowRatioR0FirstBracketCore_restoration
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hregion : LRDeterminantLowRatioRegion point)
    (hsSmall : point.s ≤ 1 / 16384) :
    -lrLowRatioNormalization point * lrLowRatioEpsilonEntropy <
      lrLowRatioR0FirstBracketCore point := by
  let L := lrLowRatioLogScale point
  let A := L + 3
  let C := L + 2 * Real.log 2
  let e := lrCertificateE point
  let n := lrLowRatioNormalization point
  let D1 := lrDeterminantD1 point
  let B1 := lrCertificateBFlow point + lrDeterminantD1 point
  let kap := lrLowRatioKappa point
  let rp := lrLowerFaceR0Prime point.s
  have hs : point.s ∈ Ioc (0 : ℝ) (1 / 16384) :=
    ⟨hinterior.1.1, hsSmall⟩
  have hs0 : 0 ≤ point.s := hs.1.le
  have hLraw := lrSmallSBridge_log_lower hs
  have hL : 14 * Real.log 2 ≤ L := by
    simpa [L, lrLowRatioLogScale] using hLraw
  have hlam0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hA0 : 0 ≤ A := by dsimp [A]; nlinarith
  have hC0 : 0 ≤ C := by dsimp [C]; nlinarith
  have he0 : 0 ≤ e := by simpa [e] using hinterior.2.1.1.le
  have hn0 : 0 < n := by
    simpa [n] using lrLowRatioNormalization_pos hinterior
  have hD0 : 0 ≤ D1 := by
    simpa [D1] using lrDeterminantD1_nonnegative hinterior
  have hB0 : 0 ≤ lrCertificateBFlow point :=
    (lrCertificateBFlow_pos hinterior).le
  have hB10 : 0 ≤ B1 := by dsimp [B1]; linarith
  have hB1Upper : B1 ≤ A := by
    simpa [B1, A, L] using
      lrLowRatio_B_add_D1_upper hinterior hregion hsSmall
  have hweights := lrLowRatio_weight_bounds hinterior hregion hsSmall
  have hkap0 : 0 ≤ kap := by simpa [kap] using hweights.2.2.2.2.1
  have hkapUpper : kap ≤ 8 * e ^ 2 := by
    simpa [kap, e] using hweights.2.2.2.2.2
  have hrp0 : 0 ≤ rp := by
    simpa [rp] using lrLowerFaceR0Prime_nonneg hinterior.1
  have hsSixteenth : point.s ∈ Ioo (0 : ℝ) (1 / 16) :=
    ⟨hs.1, hs.2.trans_lt (by norm_num)⟩
  have hrpUpper0 := lrLowerFaceR0Prime_upper hsSixteenth
  have hlogSplit := lrLowRatio_log_four_div_split hs.1
  have hrpUpper : rp ≤ point.s / 3 * C := by
    dsimp [rp, C, L]
    unfold lrLowRatioLogScale
    rw [← hlogSplit]
    exact hrpUpper0
  have hrpBound0 : 0 ≤ point.s / 3 * C :=
    mul_nonneg (div_nonneg hs0 (by norm_num)) hC0
  have hGr : 0 ≤ lrSmallSBridgeR0G point :=
    lrLowRatioR0G_nonnegative hinterior
  have hOmega : -kap * point.s * rp ≤ lrLowRatioR0Omega point := by
    simpa [kap, rp] using
      lrLowRatioR0Omega_lower hinterior hregion hsSmall
  have hDGr : 0 ≤ D1 * lrSmallSBridgeR0G point :=
    mul_nonneg hD0 hGr
  have hBOmega := mul_le_mul_of_nonneg_left hOmega hB10
  have hcoreLower : -(B1 * kap * point.s * rp) ≤
      lrLowRatioR0FirstBracketCore point := by
    calc
      -(B1 * kap * point.s * rp) =
          B1 * (-kap * point.s * rp) := by ring
      _ ≤ B1 * lrLowRatioR0Omega point := hBOmega
      _ ≤ D1 * lrSmallSBridgeR0G point +
          B1 * lrLowRatioR0Omega point := le_add_of_nonneg_left hDGr
      _ = lrLowRatioR0FirstBracketCore point := by
        simp [D1, B1, lrLowRatioR0FirstBracketCore]
  have hBK : B1 * kap ≤ A * (8 * e ^ 2) :=
    mul_le_mul hB1Upper hkapUpper hkap0 hA0
  have hBK0 : 0 ≤ B1 * kap := mul_nonneg hB10 hkap0
  have hBKUpper0 : 0 ≤ A * (8 * e ^ 2) :=
    mul_nonneg hA0 (mul_nonneg (by norm_num) (sq_nonneg e))
  have hBKs : B1 * kap * point.s ≤
      A * (8 * e ^ 2) * point.s :=
    mul_le_mul_of_nonneg_right hBK hs0
  have hBKs0 : 0 ≤ B1 * kap * point.s := mul_nonneg hBK0 hs0
  have hBKsUpper0 : 0 ≤ A * (8 * e ^ 2) * point.s :=
    mul_nonneg hBKUpper0 hs0
  have hprimeStep : B1 * kap * point.s * rp ≤
      B1 * kap * point.s * (point.s / 3 * C) :=
    mul_le_mul_of_nonneg_left hrpUpper hBKs0
  have hcoefficientStep :
      B1 * kap * point.s * (point.s / 3 * C) ≤
        A * (8 * e ^ 2) * point.s * (point.s / 3 * C) :=
    mul_le_mul_of_nonneg_right hBKs hrpBound0
  have hcostUpper : B1 * kap * point.s * rp ≤
      (8 / 3 : ℝ) * A * e ^ 2 * point.s ^ 2 * C := by
    calc
      B1 * kap * point.s * rp ≤
          B1 * kap * point.s * (point.s / 3 * C) := hprimeStep
      _ ≤ A * (8 * e ^ 2) * point.s * (point.s / 3 * C) :=
        hcoefficientStep
      _ = (8 / 3 : ℝ) * A * e ^ 2 * point.s ^ 2 * C := by ring
  have heScale : e ^ 2 ≤ 4 * point.s ^ 2 * n := by
    simpa [e, n] using
      lrLowRatio_e_sq_le_four_s_sq_mul_normalization hinterior hregion
  have hfactor0 : 0 ≤ (8 / 3 : ℝ) * A * point.s ^ 2 * C :=
    mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) hA0) (sq_nonneg point.s)) hC0
  have hscale := mul_le_mul_of_nonneg_right heScale hfactor0
  have hrawScale :
      (8 / 3 : ℝ) * A * e ^ 2 * point.s ^ 2 * C ≤
        n * ((32 / 3 : ℝ) * A * point.s ^ 4 * C) := by
    calc
      (8 / 3 : ℝ) * A * e ^ 2 * point.s ^ 2 * C =
          e ^ 2 * ((8 / 3 : ℝ) * A * point.s ^ 2 * C) := by ring
      _ ≤ (4 * point.s ^ 2 * n) *
          ((8 / 3 : ℝ) * A * point.s ^ 2 * C) := hscale
      _ = n * ((32 / 3 : ℝ) * A * point.s ^ 4 * C) := by ring
  have hbudget := lrLowRatio_entropy_budget_envelope hs
  have hbudget' : (32 / 3 : ℝ) * A * point.s ^ 4 * C <
      lrLowRatioEpsilonEntropy := by
    simpa [A, C, L, lrLowRatioLogScale] using hbudget
  have hbudgetScaled :
      n * ((32 / 3 : ℝ) * A * point.s ^ 4 * C) <
        n * lrLowRatioEpsilonEntropy :=
    mul_lt_mul_of_pos_left hbudget' hn0
  have hcost : B1 * kap * point.s * rp <
      n * lrLowRatioEpsilonEntropy :=
    (hcostUpper.trans hrawScale).trans_lt hbudgetScaled
  change -n * lrLowRatioEpsilonEntropy <
    lrLowRatioR0FirstBracketCore point
  nlinarith

/-- Exact analytic restoration statement in (M42): the first bracket,
after normalization by `n`, loses no more than the two displayed audited
payments from the frozen core. -/
def LRDeterminantLowRatioSmallSRestorationTheorem : Prop :=
  ∀ point : CertificatePoint,
    LRHighShapeInterior point →
    LRHighShapeVRelevant point →
    LRDeterminantLowRatioRegion point →
    point.s ≤ 1 / 16384 →
    lrLowRatioFrozenFirstBracketNormalized point -
        lrLowRatioEpsilonChannel - lrLowRatioEpsilonEntropy ≤
      lrLowRatioExactFirstBracketNormalized point

theorem lrDeterminantLowRatioSmallSRestorationTheorem :
    LRDeterminantLowRatioSmallSRestorationTheorem := by
  intro point hinterior _hrelevant hregion hsSmall
  have hq := lrLowRatioQ0FirstBracketCore_restoration
    hinterior hregion hsSmall
  have hr := lrLowRatioR0FirstBracketCore_restoration
    hinterior hregion hsSmall
  have hatom : 0 ≤
      4 * lrCertificateBFlow point * lrDeterminantDelta point *
        lrCertificateW point :=
    mul_nonneg
      (mul_nonneg
        (mul_nonneg (by norm_num) (lrCertificateBFlow_pos hinterior).le)
        (lrDeterminantDelta_nonnegative hinterior))
      (lrCertificateW_pos hinterior).le
  have hsplit := lrLowRatioFirstBracket_eq_q0_add_r0_add_atom point
  have hraw :
      lrLowRatioNormalization point *
          (lrLowRatioFrozenFirstBracketNormalized point -
            lrLowRatioEpsilonChannel - lrLowRatioEpsilonEntropy) <
        lrDeterminantFirstBracket
          (lrCertificateBFlow point) (lrDeterminantD1 point)
          (lrCertificateGShape point) (lrDeterminantPsi point)
          (lrDeterminantDelta point) (lrCertificateW point) := by
    rw [hsplit]
    nlinarith
  have hn := lrLowRatioNormalization_pos hinterior
  have hnormalized :
      lrLowRatioFrozenFirstBracketNormalized point -
          lrLowRatioEpsilonChannel - lrLowRatioEpsilonEntropy <
        lrDeterminantFirstBracket
          (lrCertificateBFlow point) (lrDeterminantD1 point)
          (lrCertificateGShape point) (lrDeterminantPsi point)
          (lrDeterminantDelta point) (lrCertificateW point) /
            lrLowRatioNormalization point := by
    rw [lt_div_iff₀ hn]
    simpa [mul_comm] using hraw
  unfold lrLowRatioExactFirstBracketNormalized
  exact hnormalized.le

/-- The restoration inequality and the analytic M41 margin close the actual
small-`s` first bracket M42. -/
theorem lrDeterminantLowRatioSmallSFirstBracketTheorem_of_restoration
    (hrestoration : LRDeterminantLowRatioSmallSRestorationTheorem) :
    LRDeterminantLowRatioSmallSFirstBracketTheorem := by
  intro point hinterior hrelevant hregion hsSmall
  have hfrozen := lrLowRatioFrozenFirstBracketNormalized_gt_M41
    hinterior hregion hsSmall
  have hrest := hrestoration point hinterior hrelevant hregion hsSmall
  have hnormalized : 0 < lrLowRatioExactFirstBracketNormalized point := by
    have hpay := lrLowRatio_M42_payment_arithmetic
    linarith
  have hn := lrLowRatioNormalization_pos hinterior
  have hraw : 0 < lrDeterminantFirstBracket
      (lrCertificateBFlow point) (lrDeterminantD1 point)
      (lrCertificateGShape point) (lrDeterminantPsi point)
      (lrDeterminantDelta point) (lrCertificateW point) := by
    have hproduct := mul_pos hnormalized hn
    unfold lrLowRatioExactFirstBracketNormalized at hproduct
    rw [div_mul_cancel₀ _ hn.ne'] at hproduct
    exact hproduct
  exact hraw.le

theorem lrDeterminantLowRatioSmallSFirstBracketTheorem :
    LRDeterminantLowRatioSmallSFirstBracketTheorem :=
  lrDeterminantLowRatioSmallSFirstBracketTheorem_of_restoration
    lrDeterminantLowRatioSmallSRestorationTheorem

end CourtadeKumar
