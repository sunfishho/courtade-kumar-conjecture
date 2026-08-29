import InformationTheory.CourtadeKumar.LRDeterminantLowKThin

/-!
# Analytic restoration for the determinant low-`k` bridge

This module starts discharging `LRLowKRestorationCertificate` at
the level of the actual determinant coordinates.  It defines the exact
finite-`s`, frozen-channel (`v = 1`, `Q = q`) core used in DA7 and isolates
the later true-channel and entropy-restoration stages as explicit
obligations.
-/

open Set

namespace CourtadeKumar

/-! ## Exact finite-`s` frozen-channel core -/

noncomputable def lrDA7FiniteA (point : CertificatePoint) : ℝ :=
  (point.chi * Real.log
      (1 + (1 - point.s) * point.k * point.chi) +
    Real.log (1 + (1 - point.s) * point.k)) / (1 + point.chi)

noncomputable def lrDA7FiniteAH (point : CertificatePoint) : ℝ :=
  (point.chi * lrLowKIdealH
      (1 + (1 - point.s) * point.k * point.chi) +
    lrLowKIdealH (1 + (1 - point.s) * point.k)) / (1 + point.chi)

noncomputable def lrDA7FiniteP (point : CertificatePoint) : ℝ :=
  Real.log (1 / point.s) + 2 * Real.log 2 + 1 - point.s -
    lrDA7FiniteA point

noncomputable def lrDA7FiniteG (point : CertificatePoint) : ℝ :=
  Real.log (1 / point.s) - Real.log point.k + 2 * Real.log 2 + 1 -
    lrLowKIdealQChi point.chi

noncomputable def lrDA7FiniteS (point : CertificatePoint) : ℝ :=
  lrDA7FiniteP point - lrDA7FiniteG point

noncomputable def lrDA7FiniteT (point : CertificatePoint) : ℝ :=
  Real.log (1 / point.s) + 2 * Real.log 2 + 1 - lrDA7FiniteAH point

/-- The outer coefficient with the channel weight frozen at `v = 1`. -/
noncomputable def lrDA7FiniteB (point : CertificatePoint) : ℝ :=
  Real.log 2 -
    Real.log (lrCertificateB point.s (lrCertificateE point)) / 2

/-- The coefficient `bar c = (1-s)/(3(L+C))`. -/
noncomputable def lrDA7FiniteC (point : CertificatePoint) : ℝ :=
  (1 - point.s) /
    (3 * (Real.log (1 / point.s) + lrLowKIdealC))

/-- The exact finite-`s`, frozen-channel logarithmic core preceding the
channel and entropy-remainder restorations. -/
noncomputable def lrDA7FiniteFrozenCore (point : CertificatePoint) : ℝ :=
  lrDeterminantD1 point * lrDA7FiniteP point +
    lrDA7FiniteB point * lrDA7FiniteS point +
    lrDA7FiniteC point *
      (lrDA7FiniteB point * lrCertificateX point -
        lrDeterminantD1 point) * lrDA7FiniteT point

/-- DA1 expanded into its four exact normalized summands.  This is the
actual determinant, before introducing any frozen or ideal surrogate. -/
theorem lrLowKActualNormalized_eq_DA1
    {point : CertificatePoint}
    (hn : lrLowKNormalization point ≠ 0) :
    lrLowKActualNormalized point =
      (lrDeterminantD1 point * lrDeterminantPsi point +
          lrCertificateBFlow point *
            (lrDeterminantPsi point - lrCertificateGShape point) +
          4 * lrDeterminantDelta point * lrCertificateBFlow point *
            lrCertificateW point +
          lrDeterminantC0 point *
            (lrCertificateBFlow point * lrCertificateX point -
              lrDeterminantD1 point) * lrDeterminantT point) /
        lrLowKNormalization point := by
  unfold lrLowKActualNormalized lrDeterminantClearedSingular
  field_simp [hn]
  ring

/-- The ideal core rewritten in the coefficient form compared term by term
in DA7a. -/
theorem lrLowKIdealCore_eq_DA7_form
    (L k chi : ℝ) :
    lrLowKIdealCore L k chi =
      lrLowKIdealD k * (L + lrLowKIdealP k chi) +
        (L / 2 + lrLowKIdealBOffset k) * lrLowKIdealS k chi +
        (1 / (3 * (L + lrLowKIdealC))) *
          ((L / 2 + lrLowKIdealBOffset k) - lrLowKIdealD k) *
          (L + lrLowKIdealT k chi) := by
  unfold lrLowKIdealCore
  ring

/-! ## The determinant `D_1` finite-`s` loss -/

noncomputable def lrDA7DModel (Y : ℝ) : ℝ :=
  (1 / 2) * Real.log ((1 + Y) / 2) + (Y - 1) / (3 * Y + 1)

/-- A one-dimensional analytic estimate behind
`D₀-s/2 ≤ D₁ ≤ D₀`. -/
theorem lrDA7DModel_finite_loss
    {Y s : ℝ} (hY : 1 ≤ Y) (hs : 0 ≤ s) :
    lrDA7DModel Y ≤ lrDA7DModel (Y + s) ∧
      lrDA7DModel (Y + s) - s / 2 ≤ lrDA7DModel Y := by
  let a := (1 + Y) / 2
  let b := (1 + (Y + s)) / 2
  have ha : 0 < a := by dsimp [a]; linarith
  have hb : 0 < b := by dsimp [b]; linarith
  have hab : a ≤ b := by dsimp [a, b]; linarith
  have hlogMono : Real.log a ≤ Real.log b :=
    Real.log_le_log ha hab
  have hdenY : 0 < 3 * Y + 1 := by linarith
  have hdenYs : 0 < 3 * (Y + s) + 1 := by linarith
  have hratMono :
      (Y - 1) / (3 * Y + 1) ≤
        (Y + s - 1) / (3 * (Y + s) + 1) := by
    rw [div_le_div_iff₀ hdenY hdenYs]
    nlinarith
  constructor
  · unfold lrDA7DModel
    dsimp [a, b] at hlogMono
    linarith
  · have hratio : 0 < b / a := div_pos hb ha
    have hlogRatio := Real.log_le_sub_one_of_pos hratio
    have hlogEq : Real.log b - Real.log a = Real.log (b / a) := by
      rw [Real.log_div hb.ne' ha.ne']
    have hratioEq : b / a - 1 = s / (1 + Y) := by
      dsimp [a, b]
      field_simp [show 1 + Y ≠ 0 by linarith]
      ring
    have hlogDiff : Real.log b - Real.log a ≤ s / 2 := by
      rw [← hlogEq, hratioEq] at hlogRatio
      have hden : 0 < 1 + Y := by linarith
      have hinv : 1 / (1 + Y) ≤ 1 / 2 := by
        rw [div_le_div_iff₀ hden (by norm_num : (0 : ℝ) < 2)]
        nlinarith
      have hscaled := mul_le_mul_of_nonneg_left hinv hs
      calc
        Real.log b - Real.log a ≤ s / (1 + Y) := hlogRatio
        _ = s * (1 / (1 + Y)) := by ring
        _ ≤ s * (1 / 2) := hscaled
        _ = s / 2 := by ring
    have hratEq :
        (Y + s - 1) / (3 * (Y + s) + 1) -
            (Y - 1) / (3 * Y + 1) =
          4 * s / ((3 * (Y + s) + 1) * (3 * Y + 1)) := by
      field_simp [hdenY.ne', hdenYs.ne']
      ring
    have hdenProduct :
        16 ≤ (3 * (Y + s) + 1) * (3 * Y + 1) := by
      nlinarith [mul_nonneg
        (show 0 ≤ 3 * (Y + s) - 3 by linarith)
        (show 0 ≤ 3 * Y - 3 by linarith)]
    have hratDiff :
        (Y + s - 1) / (3 * (Y + s) + 1) -
            (Y - 1) / (3 * Y + 1) ≤ s / 4 := by
      rw [hratEq]
      rw [div_le_iff₀ (mul_pos hdenYs hdenY)]
      nlinarith
    unfold lrDA7DModel
    dsimp [a, b] at hlogDiff
    linarith

/-- The determinant coordinate `Y` is exactly `1 + 1/k - s`. -/
theorem lrDeterminantY_eq_lowK_coordinate
    {point : CertificatePoint}
    (hs : 0 < point.s) (hk : 0 < point.k) :
    lrDeterminantY point = 1 + 1 / point.k - point.s := by
  unfold lrDeterminantY lrCertificateB lrCertificateE
  field_simp [hs.ne', hk.ne']
  ring

theorem lrLowKIdealD_eq_DModel
    {k : ℝ} (hk : 0 < k) :
    lrLowKIdealD k = lrDA7DModel (1 + 1 / k) := by
  unfold lrLowKIdealD lrDA7DModel
  have hkNe := hk.ne'
  congr 1
  · field_simp [hkNe]
    ring
  · field_simp [hkNe, show 4 * k + 3 ≠ 0 by positivity]
    ring

theorem lrDeterminantD1_eq_DModel
    {point : CertificatePoint}
    (hs : 0 < point.s) (hk : 0 < point.k) :
    lrDeterminantD1 point =
      lrDA7DModel (1 + 1 / point.k - point.s) := by
  unfold lrDeterminantD1 lrDA7DModel
  rw [lrDeterminantY_eq_lowK_coordinate hs hk]

/-- The genuine finite-`s` determinant-coordinate comparison quoted in
DA7a. -/
theorem lrDeterminantD1_lowK_finite_bounds
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hregion : LRDeterminantLowKRegion point) :
    lrLowKIdealD point.k - point.s / 2 ≤ lrDeterminantD1 point ∧
      lrDeterminantD1 point ≤ lrLowKIdealD point.k := by
  have hs := hinterior.1.1
  have hk : 0 < point.k := hs.trans_le hregion.2.1
  have hkOne : point.k ≤ 1 := hregion.2.2
  have hinv : 1 ≤ 1 / point.k := by
    rw [le_div_iff₀ hk]
    simpa using hkOne
  have hY : 1 ≤ 1 + 1 / point.k - point.s := by
    have hsOne : point.s ≤ 1 := hregion.1.trans (by norm_num)
    linarith
  have hmodel := lrDA7DModel_finite_loss hY hs.le
  have hshift :
      1 + 1 / point.k - point.s + point.s = 1 + 1 / point.k := by ring
  rw [hshift] at hmodel
  rw [lrLowKIdealD_eq_DModel hk,
    lrDeterminantD1_eq_DModel hs hk]
  exact ⟨hmodel.2, hmodel.1⟩

/-! ## Algebraic scalar cores and loss -/

noncomputable def lrDA7FiniteSymbolicLoss
    (s e D0 B0 p S t c : ℝ) : ℝ :=
  s * D0 + s / 2 * p + s * B0 + e / 2 * (-S) + e * s / 2 +
    c * (s * (B0 - D0) + e * (B0 + e / 2)) * t

noncomputable def lrDA7IdealScalarCore
    (D0 B0 p S t c : ℝ) : ℝ :=
  D0 * p + B0 * S + c * (B0 - D0) * t

noncomputable def lrDA7FiniteScalarCore
    (D B ps Ss ts cbar x : ℝ) : ℝ :=
  D * ps + B * Ss + cbar * (B * x - D) * ts

/-! ## Coordinate comparisons feeding the finite-`s` collection -/

noncomputable def lrDA7IdealB (point : CertificatePoint) : ℝ :=
  Real.log (1 / point.s) / 2 + lrLowKIdealBOffset point.k

noncomputable def lrDA7IdealPFull (point : CertificatePoint) : ℝ :=
  Real.log (1 / point.s) + lrLowKIdealP point.k point.chi

noncomputable def lrDA7IdealTFull (point : CertificatePoint) : ℝ :=
  Real.log (1 / point.s) + lrLowKIdealT point.k point.chi

noncomputable def lrDA7IdealCStar (point : CertificatePoint) : ℝ :=
  1 / (3 * (Real.log (1 / point.s) + lrLowKIdealC))

theorem lrLowKIdealCore_eq_scalarCore (point : CertificatePoint) :
    lrLowKIdealCore (Real.log (1 / point.s)) point.k point.chi =
      lrDA7IdealScalarCore (lrLowKIdealD point.k) (lrDA7IdealB point)
        (lrDA7IdealPFull point) (lrLowKIdealS point.k point.chi)
        (lrDA7IdealTFull point) (lrDA7IdealCStar point) := by
  unfold lrDA7IdealScalarCore lrDA7IdealB lrDA7IdealPFull
    lrDA7IdealTFull lrDA7IdealCStar lrLowKIdealCore
  ring

theorem lrDA7FiniteFrozenCore_eq_scalarCore (point : CertificatePoint) :
    lrDA7FiniteFrozenCore point =
      lrDA7FiniteScalarCore (lrDeterminantD1 point) (lrDA7FiniteB point)
        (lrDA7FiniteP point) (lrDA7FiniteS point) (lrDA7FiniteT point)
        ((1 - point.s) * lrDA7IdealCStar point)
        (lrCertificateX point) := by
  unfold lrDA7FiniteFrozenCore lrDA7FiniteScalarCore lrDA7FiniteC
    lrDA7IdealCStar
  ring

/-- Freezing the channel weight changes only the outer logarithm. -/
theorem lrDA7FiniteB_eq_actual_add (point : CertificatePoint) :
    lrDA7FiniteB point = lrCertificateBFlow point +
      (Real.log 2 - Real.log (1 + lrCertificateV point)) := by
  unfold lrDA7FiniteB lrCertificateBFlow lrCertificateBFlowValue
  ring

theorem lrDA7FiniteB_actual_le
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point) :
    lrCertificateBFlow point ≤ lrDA7FiniteB point := by
  have hv := lrCertificateV_mem_Ioo hinterior
  have harg : 0 < 1 + lrCertificateV point := by linarith [hv.1]
  have hlog : Real.log (1 + lrCertificateV point) ≤ Real.log 2 := by
    exact Real.log_le_log harg (by linarith [hv.2])
  rw [lrDA7FiniteB_eq_actual_add]
  linarith

theorem lrDA7FiniteB_eq_log_form
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point) :
    lrDA7FiniteB point =
      Real.log (1 / point.s) / 2 + Real.log 2 -
        Real.log (1 + (1 - point.s) * point.k) / 2 := by
  have hs := hinterior.1.1
  have hk : 0 < point.k := by
    have he := hinterior.2.1.1
    unfold lrCertificateE at he
    exact pos_of_mul_pos_left (by simpa [mul_comm] using he) hs.le
  have houter : 0 < 1 + (1 - point.s) * point.k := by
    have hsOne : point.s < 1 := hinterior.1.2
    have hprod : 0 ≤ (1 - point.s) * point.k :=
      mul_nonneg (sub_nonneg.mpr hsOne.le) hk.le
    linarith
  have hb : lrCertificateB point.s (lrCertificateE point) =
      point.s * (1 + (1 - point.s) * point.k) := by
    unfold lrCertificateB lrCertificateE
    ring
  have hlogInv : Real.log (1 / point.s) = -Real.log point.s := by
    rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) hs.ne']
    norm_num
  unfold lrDA7FiniteB
  rw [hb, Real.log_mul hs.ne' houter.ne', hlogInv]
  ring

/-- The exact outer-coefficient interval
`B₀ ≤ bar B ≤ B₀ + e/2`. -/
theorem lrDA7FiniteB_ideal_interval
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point) :
    lrDA7IdealB point ≤ lrDA7FiniteB point ∧
      lrDA7FiniteB point ≤
        lrDA7IdealB point + lrCertificateE point / 2 := by
  have hs := hinterior.1
  have hk : 0 < point.k := by
    have he := hinterior.2.1.1
    unfold lrCertificateE at he
    exact pos_of_mul_pos_left (by simpa [mul_comm] using he) hs.1.le
  let outer := 1 + (1 - point.s) * point.k
  let top := 1 + point.k
  have houter : 0 < outer := by
    dsimp [outer]
    have hprod : 0 ≤ (1 - point.s) * point.k :=
      mul_nonneg (sub_nonneg.mpr hs.2.le) hk.le
    linarith
  have htop : 0 < top := by dsimp [top]; positivity
  have horder : outer ≤ top := by
    dsimp [outer, top]
    nlinarith [mul_nonneg hs.1.le hk.le]
  have hlogOrder : Real.log outer ≤ Real.log top :=
    Real.log_le_log houter horder
  have hratio := Real.log_le_sub_one_of_pos (div_pos htop houter)
  have hlogRatio : Real.log (top / outer) =
      Real.log top - Real.log outer := Real.log_div htop.ne' houter.ne'
  rw [hlogRatio] at hratio
  have hratioSub : top / outer - 1 =
      lrCertificateE point / outer := by
    have hdiff : top - outer = lrCertificateE point := by
      dsimp [top, outer]
      unfold lrCertificateE
      ring
    calc
      top / outer - 1 = (top - outer) / outer := by
        field_simp [houter.ne']
      _ = lrCertificateE point / outer := by rw [hdiff]
  rw [hratioSub] at hratio
  have houterOne : 1 ≤ outer := by
    dsimp [outer]
    exact le_add_of_nonneg_right
      (mul_nonneg (sub_nonneg.mpr hs.2.le) hk.le)
  have heNonnegative : 0 ≤ lrCertificateE point := hinterior.2.1.1.le
  have hfrac : lrCertificateE point / outer ≤
      lrCertificateE point := by
    rw [div_le_iff₀ houter]
    nlinarith [mul_le_mul_of_nonneg_left houterOne heNonnegative]
  rw [lrDA7FiniteB_eq_log_form hinterior]
  unfold lrDA7IdealB lrLowKIdealBOffset
  dsimp [outer, top] at hlogOrder hratio hfrac ⊢
  constructor <;> nlinarith

/-- The frozen physical gap remains positive because freezing `v` only
increases `B`. -/
theorem lrDA7FiniteGap_pos
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hrelevant : LRHighShapeVRelevant point) :
    0 < lrDA7FiniteB point * lrCertificateX point -
      lrDeterminantD1 point := by
  have hB := lrDA7FiniteB_actual_le hinterior
  have hX : 0 < lrCertificateX point := by
    unfold lrCertificateX
    have hprodLt : point.chi * lrCertificateE point < 1 := by
      calc
        point.chi * lrCertificateE point < 1 * lrCertificateE point :=
          mul_lt_mul_of_pos_right hinterior.2.2.2 hinterior.2.1.1
        _ < 1 := by simpa using hinterior.2.1.2
    linarith
  have hscaled := mul_le_mul_of_nonneg_right hB hX.le
  have hactual := lrCertificateBFlow_mul_X_sub_D1_pos hinterior hrelevant
  linarith

theorem lrDA7_x_loss_bounds
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point) :
    0 ≤ 1 - lrCertificateX point ∧
      1 - lrCertificateX point ≤ lrCertificateE point := by
  unfold lrCertificateX
  have hprod := mul_nonneg hinterior.2.2.1.le hinterior.2.1.1.le
  have hupper := mul_le_mul_of_nonneg_right hinterior.2.2.2.le
    hinterior.2.1.1.le
  constructor <;> nlinarith

/-- Decreasing the radial factor from `1` to `1-s` can only decrease the
weighted logarithmic average `A`. -/
theorem lrDA7FiniteA_le_idealA
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point) :
    lrDA7FiniteA point ≤ lrLowKIdealA point.k point.chi := by
  have hs := hinterior.1
  have hk : 0 < point.k := by
    have he := hinterior.2.1.1
    unfold lrCertificateE at he
    exact pos_of_mul_pos_left (by simpa [mul_comm] using he) hs.1.le
  have hchi := hinterior.2.2
  have hR : 0 ≤ 1 - point.s := sub_nonneg.mpr hs.2.le
  have hRle : 1 - point.s ≤ 1 := by linarith [hs.1]
  have hkchi : 0 ≤ point.k * point.chi :=
    mul_nonneg hk.le hchi.1.le
  have hinnerPos : 0 < 1 + (1 - point.s) * point.k * point.chi := by
    have hprod : 0 ≤ (1 - point.s) * point.k * point.chi :=
      mul_nonneg (mul_nonneg hR hk.le) hchi.1.le
    linarith
  have houterPos : 0 < 1 + (1 - point.s) * point.k := by
    have hprod : 0 ≤ (1 - point.s) * point.k := mul_nonneg hR hk.le
    linarith
  have hidealInnerPos : 0 < 1 + point.k * point.chi := by positivity
  have hidealOuterPos : 0 < 1 + point.k := by positivity
  have hinnerOrder :
      1 + (1 - point.s) * point.k * point.chi ≤
        1 + point.k * point.chi := by
    nlinarith [mul_le_mul_of_nonneg_right hRle hkchi]
  have houterOrder :
      1 + (1 - point.s) * point.k ≤ 1 + point.k := by
    nlinarith [mul_le_mul_of_nonneg_right hRle hk.le]
  have hlogInner := Real.log_le_log hinnerPos hinnerOrder
  have hlogOuter := Real.log_le_log houterPos houterOrder
  have hweighted := mul_le_mul_of_nonneg_left hlogInner hchi.1.le
  have hden : 0 < 1 + point.chi := by linarith [hchi.1]
  unfold lrDA7FiniteA lrLowKIdealA
  rw [div_le_div_iff_of_pos_right hden]
  linarith

theorem lrDA7FiniteP_lower
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point) :
    lrDA7IdealPFull point - point.s ≤ lrDA7FiniteP point := by
  have hA := lrDA7FiniteA_le_idealA hinterior
  unfold lrDA7IdealPFull lrLowKIdealP lrDA7FiniteP
  linarith

theorem lrDA7FiniteS_lower
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point) :
    lrLowKIdealS point.k point.chi - point.s ≤
      lrDA7FiniteS point := by
  have hp := lrDA7FiniteP_lower hinterior
  have hg : lrDA7FiniteG point =
      lrDA7IdealPFull point - lrLowKIdealS point.k point.chi := by
    unfold lrDA7FiniteG lrDA7IdealPFull lrLowKIdealP lrLowKIdealS
    ring
  unfold lrDA7FiniteS
  rw [hg]
  linarith

lemma lrDA7IdealQChi_nonpos
    {chi : ℝ} (hchi : chi ∈ Icc (0 : ℝ) 1) :
    lrLowKIdealQChi chi ≤ 0 := by
  rcases hchi.1.eq_or_lt with rfl | hchiPos
  · norm_num [lrLowKIdealQChi]
  · have hlog : Real.log chi ≤ 0 := Real.log_nonpos hchiPos.le hchi.2
    have hnum : chi * Real.log chi ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hchiPos.le hlog
    unfold lrLowKIdealQChi
    exact div_nonpos_of_nonpos_of_nonneg hnum (by linarith [hchi.1])

theorem lrLowKIdealS_nonpos_lowK
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hregion : LRDeterminantLowKRegion point) :
    lrLowKIdealS point.k point.chi ≤ 0 := by
  have hk : 0 < point.k := hinterior.1.1.trans_le hregion.2.1
  have hlogK : Real.log point.k ≤ 0 :=
    Real.log_nonpos hk.le hregion.2.2
  have hq := lrDA7IdealQChi_nonpos
    ⟨hinterior.2.2.1.le, hinterior.2.2.2.le⟩
  have hA : 0 ≤ lrLowKIdealA point.k point.chi := by
    have hchi := hinterior.2.2
    have hinner : 1 ≤ 1 + point.k * point.chi := by
      exact le_add_of_nonneg_right (mul_nonneg hk.le hchi.1.le)
    have houter : 1 ≤ 1 + point.k := by linarith
    have hlogInner := Real.log_nonneg hinner
    have hlogOuter := Real.log_nonneg houter
    unfold lrLowKIdealA
    exact div_nonneg
      (add_nonneg (mul_nonneg hchi.1.le hlogInner) hlogOuter)
      (by linarith [hchi.1])
  unfold lrLowKIdealS
  linarith

theorem lrDA7FiniteS_nonpos_lowK
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hregion : LRDeterminantLowKRegion point) :
    lrDA7FiniteS point ≤ 0 := by
  have hs := hinterior.1
  have hk : 0 < point.k := hs.1.trans_le hregion.2.1
  have hlogK : Real.log point.k ≤ 0 :=
    Real.log_nonpos hk.le hregion.2.2
  have hq := lrDA7IdealQChi_nonpos
    ⟨hinterior.2.2.1.le, hinterior.2.2.2.le⟩
  have hA : 0 ≤ lrDA7FiniteA point := by
    have hchi := hinterior.2.2
    have hR : 0 ≤ 1 - point.s := sub_nonneg.mpr hs.2.le
    have hinner :
        1 ≤ 1 + (1 - point.s) * point.k * point.chi := by
      have hprod : 0 ≤ (1 - point.s) * point.k * point.chi :=
        mul_nonneg (mul_nonneg hR hk.le) hchi.1.le
      linarith
    have houter : 1 ≤ 1 + (1 - point.s) * point.k := by
      have hprod : 0 ≤ (1 - point.s) * point.k := mul_nonneg hR hk.le
      linarith
    have hlogInner := Real.log_nonneg hinner
    have hlogOuter := Real.log_nonneg houter
    unfold lrDA7FiniteA
    exact div_nonneg
      (add_nonneg (mul_nonneg hchi.1.le hlogInner) hlogOuter)
      (by linarith [hchi.1])
  have hformula : lrDA7FiniteS point =
      Real.log point.k + lrLowKIdealQChi point.chi - point.s -
        lrDA7FiniteA point := by
    unfold lrDA7FiniteS lrDA7FiniteP lrDA7FiniteG
    ring
  rw [hformula]
  linarith [hs.1]

/-! The monotonicity of `h(z)=z log z/(z-1)` needed for `t_s ≥ t`. -/

noncomputable def lrDA7HPos (z : ℝ) : ℝ :=
  z * Real.log z / (z - 1)

theorem hasDerivAt_lrDA7HPos
    {z : ℝ} (hz : 1 < z) :
    HasDerivAt lrDA7HPos
      ((z - 1 - Real.log z) / (z - 1) ^ 2) z := by
  have hzPos : 0 < z := zero_lt_one.trans hz
  have hnum := (hasDerivAt_id z).mul (Real.hasDerivAt_log hzPos.ne')
  have hden := (hasDerivAt_id z).sub (hasDerivAt_const z 1)
  have hdenNe : z - 1 ≠ 0 := sub_ne_zero.mpr hz.ne'
  have hquot := hnum.div hden hdenNe
  unfold lrDA7HPos
  convert hquot using 1
  simp only [Pi.mul_apply, Pi.sub_apply, id_eq]
  field_simp [hzPos.ne', hdenNe]
  ring

theorem lrDA7HPos_monotoneOn :
    MonotoneOn lrDA7HPos (Ioi (1 : ℝ)) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ioi (1 : ℝ))
  · intro z hz
    exact (hasDerivAt_lrDA7HPos hz).continuousAt.continuousWithinAt
  · intro z hz
    exact (hasDerivAt_lrDA7HPos (interior_subset hz)).differentiableAt
      |>.differentiableWithinAt
  · intro z hz
    have hz' : 1 < z := interior_subset hz
    rw [(hasDerivAt_lrDA7HPos hz').deriv]
    have hnum : 0 ≤ z - 1 - Real.log z :=
      sub_nonneg.mpr (Real.log_le_sub_one_of_pos (zero_lt_one.trans hz'))
    exact div_nonneg hnum (sq_nonneg (z - 1))

theorem lrLowKIdealH_monotone_Ici :
    MonotoneOn lrLowKIdealH (Ici (1 : ℝ)) := by
  intro a ha b hb hab
  have ha' : 1 ≤ a := ha
  have hb' : 1 ≤ b := hb
  rcases ha'.eq_or_lt with haEq | haStrict
  · subst a
    rcases hb'.eq_or_lt with hbEq | hbStrict
    · subst b
      rfl
    · have hbase := lrLowKIdealH_ge_one
        (t := b - 1) (sub_pos.mpr hbStrict)
      simpa [show 1 + (b - 1) = b by ring, lrLowKIdealH] using hbase
  · have hbStrict : 1 < b := haStrict.trans_le hab
    have hmono := lrDA7HPos_monotoneOn haStrict hbStrict hab
    simpa [lrLowKIdealH, lrDA7HPos, ne_of_gt haStrict,
      ne_of_gt hbStrict] using hmono

theorem lrDA7FiniteAH_le_idealAH
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point) :
    lrDA7FiniteAH point ≤ lrLowKIdealAH point.k point.chi := by
  have hs := hinterior.1
  have hk : 0 < point.k := by
    have he := hinterior.2.1.1
    unfold lrCertificateE at he
    exact pos_of_mul_pos_left (by simpa [mul_comm] using he) hs.1.le
  have hchi := hinterior.2.2
  have hR : 0 ≤ 1 - point.s := sub_nonneg.mpr hs.2.le
  have hRle : 1 - point.s ≤ 1 := by linarith [hs.1]
  have hkchi : 0 ≤ point.k * point.chi :=
    mul_nonneg hk.le hchi.1.le
  have hinnerMem :
      1 + (1 - point.s) * point.k * point.chi ∈ Ici (1 : ℝ) := by
    change 1 ≤ 1 + (1 - point.s) * point.k * point.chi
    have hprod : 0 ≤ (1 - point.s) * point.k * point.chi :=
      mul_nonneg (mul_nonneg hR hk.le) hchi.1.le
    linarith
  have hidealInnerMem : 1 + point.k * point.chi ∈ Ici (1 : ℝ) := by
    change 1 ≤ 1 + point.k * point.chi
    linarith
  have houterMem : 1 + (1 - point.s) * point.k ∈ Ici (1 : ℝ) := by
    change 1 ≤ 1 + (1 - point.s) * point.k
    linarith [mul_nonneg hR hk.le]
  have hidealOuterMem : 1 + point.k ∈ Ici (1 : ℝ) := by
    change 1 ≤ 1 + point.k
    linarith
  have hinnerOrder :
      1 + (1 - point.s) * point.k * point.chi ≤
        1 + point.k * point.chi := by
    nlinarith [mul_le_mul_of_nonneg_right hRle hkchi]
  have houterOrder :
      1 + (1 - point.s) * point.k ≤ 1 + point.k := by
    nlinarith [mul_le_mul_of_nonneg_right hRle hk.le]
  have hHInner := lrLowKIdealH_monotone_Ici
    hinnerMem hidealInnerMem hinnerOrder
  have hHOuter := lrLowKIdealH_monotone_Ici
    houterMem hidealOuterMem houterOrder
  have hweighted := mul_le_mul_of_nonneg_left hHInner hchi.1.le
  have hden : 0 < 1 + point.chi := by linarith [hchi.1]
  unfold lrDA7FiniteAH lrLowKIdealAH
  rw [div_le_div_iff_of_pos_right hden]
  linarith

theorem lrDA7FiniteT_lower
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point) :
    lrDA7IdealTFull point ≤ lrDA7FiniteT point := by
  have hAH := lrDA7FiniteAH_le_idealAH hinterior
  unfold lrDA7IdealTFull lrLowKIdealT lrDA7FiniteT
  linarith

theorem lrDA7IdealB_pos
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hregion : LRDeterminantLowKRegion point) :
    0 < lrDA7IdealB point := by
  have hL := lrLowK_log_scale_ge_L0 hinterior hregion.1
  have hk : 0 < point.k := hinterior.1.1.trans_le hregion.2.1
  have harg : 0 < 1 + point.k := by positivity
  have hlogUpper : Real.log (1 + point.k) ≤ Real.log 2 := by
    exact Real.log_le_log harg (by linarith [hregion.2.2])
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold lrLowKIdealL0 at hL
  unfold lrDA7IdealB lrLowKIdealBOffset
  nlinarith

theorem lrDA7IdealPFull_pos
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hregion : LRDeterminantLowKRegion point) :
    0 < lrDA7IdealPFull point := by
  have hL := lrLowK_log_scale_ge_L0 hinterior hregion.1
  have hk : 0 < point.k := hinterior.1.1.trans_le hregion.2.1
  have hA := lrLowKIdealA_le_log_one_add hk
    ⟨hinterior.2.2.1.le, hinterior.2.2.2.le⟩
  have harg : 0 < 1 + point.k := by positivity
  have hlogUpper : Real.log (1 + point.k) ≤ Real.log 2 := by
    exact Real.log_le_log harg (by linarith [hregion.2.2])
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold lrLowKIdealL0 at hL
  unfold lrDA7IdealPFull lrLowKIdealP
  linarith

theorem lrDA7IdealTFull_pos
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hregion : LRDeterminantLowKRegion point) :
    0 < lrDA7IdealTFull point := by
  have hL := lrLowK_log_scale_ge_L0 hinterior hregion.1
  have hk : 0 < point.k := hinterior.1.1.trans_le hregion.2.1
  have hAH := lrLowKIdealAH_le_one_add_log hk
    ⟨hinterior.2.2.1.le, hinterior.2.2.2.le⟩
  have harg : 0 < 1 + point.k := by positivity
  have hlogUpper : Real.log (1 + point.k) ≤ Real.log 2 := by
    exact Real.log_le_log harg (by linarith [hregion.2.2])
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold lrLowKIdealL0 at hL
  unfold lrDA7IdealTFull lrLowKIdealT
  linarith

theorem lrDA7IdealCStar_nonnegative
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hregion : LRDeterminantLowKRegion point) :
    0 ≤ lrDA7IdealCStar point := by
  have hL := lrLowK_log_scale_ge_L0 hinterior hregion.1
  have hden : 0 < Real.log (1 / point.s) + lrLowKIdealC := by
    linarith [lrLowKIdealL0_add_C_pos]
  unfold lrDA7IdealCStar
  positivity

/-- The still-small finite-coordinate interface.  The determinant `D₁`
bounds, `P` comparison, physical gap, and routine signs are proved above;
only the outer-`B`, `S`, and `T` comparisons remain as visible analytic
fields. -/
structure LRDA7FiniteCoordinateBounds (point : CertificatePoint) : Prop where
  B_lower : lrDA7IdealB point ≤ lrDA7FiniteB point
  B_upper :
    lrDA7FiniteB point ≤ lrDA7IdealB point + lrCertificateE point / 2
  idealS_nonpos : lrLowKIdealS point.k point.chi ≤ 0
  finiteS_nonpos : lrDA7FiniteS point ≤ 0
  finiteT_lower : lrDA7IdealTFull point ≤ lrDA7FiniteT point

theorem lrDA7FiniteCoordinateBounds_proved
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hregion : LRDeterminantLowKRegion point) :
    LRDA7FiniteCoordinateBounds point := by
  have hB := lrDA7FiniteB_ideal_interval hinterior
  exact
    { B_lower := hB.1
      B_upper := hB.2
      idealS_nonpos := lrLowKIdealS_nonpos_lowK hinterior hregion
      finiteS_nonpos := lrDA7FiniteS_nonpos_lowK hinterior hregion
      finiteT_lower := lrDA7FiniteT_lower hinterior }

/-! ## Algebraic collection of the six finite-`s` payments -/

/-- Sign-safe term-by-term collection behind DA7a.  Unlike the endpoint
arithmetic, this theorem proves the actual six-term finite-`s` comparison. -/
theorem lrDA7_finite_scalar_core_lower
    {s e D0 D B0 B p ps S Ss t ts c x : ℝ}
    (hs : 0 ≤ s) (hsOne : s ≤ 1) (he : 0 ≤ e)
    (hD : 0 ≤ D)
    (hDLower : D0 - s / 2 ≤ D) (hDUpper : D ≤ D0)
    (hB0 : 0 ≤ B0) (hB : 0 ≤ B)
    (hBLower : B0 ≤ B) (hBUpper : B ≤ B0 + e / 2)
    (hp : 0 ≤ p) (hps : p - s ≤ ps)
    (hS : S ≤ 0) (hSsLower : S - s ≤ Ss)
    (ht : 0 ≤ t) (hts : t ≤ ts)
    (hc : 0 ≤ c)
    (hxLoss : 0 ≤ 1 - x) (hxLossUpper : 1 - x ≤ e)
    (hgap : 0 ≤ B * x - D) :
    lrDA7IdealScalarCore D0 B0 p S t c -
        lrDA7FiniteSymbolicLoss s e D0 B0 p S t c ≤
      lrDA7FiniteScalarCore D B ps Ss ts ((1 - s) * c) x := by
  have hDdiff : 0 ≤ D0 - D := sub_nonneg.mpr hDUpper
  have hDdiffUpper : D0 - D ≤ s / 2 := by linarith
  have hfirst :
      D0 * p - (s * D0 + s / 2 * p) ≤ D * ps := by
    have hpsScaled := mul_le_mul_of_nonneg_left hps hD
    have haux :
        D0 * p - (s * D0 + s / 2 * p) ≤ D * (p - s) := by
      have hprod : 0 ≤ (s / 2 - (D0 - D)) * p :=
        mul_nonneg (by linarith) hp
      have hcross : 0 ≤ s * (D0 - D) := mul_nonneg hs hDdiff
      nlinarith
    exact haux.trans hpsScaled
  have hBdiff : 0 ≤ B - B0 := sub_nonneg.mpr hBLower
  have hBdiffUpper : B - B0 ≤ e / 2 := by linarith
  have hsecond :
      B0 * S - (s * B0 + e / 2 * (-S) + e * s / 2) ≤ B * Ss := by
    have hSsScaled := mul_le_mul_of_nonneg_left hSsLower hB
    have hSscaled : (e / 2) * S ≤ (B - B0) * S := by
      exact mul_le_mul_of_nonpos_right hBdiffUpper hS
    have hsScaled : s * (B - B0) ≤ s * (e / 2) :=
      mul_le_mul_of_nonneg_left hBdiffUpper hs
    have haux :
        B0 * S - (s * B0 + e / 2 * (-S) + e * s / 2) ≤
          B * (S - s) := by
      nlinarith
    exact haux.trans hSsScaled
  let cost := e * (B0 + e / 2)
  have hcost : 0 ≤ cost := by
    dsimp [cost]
    exact mul_nonneg he (add_nonneg hB0 (div_nonneg he (by norm_num)))
  have hBminusD : B0 - D0 ≤ B - D := by linarith
  have hBx : B * (1 - x) ≤ cost := by
    have hmul := mul_le_mul hBUpper hxLossUpper hxLoss
      (add_nonneg hB0 (div_nonneg he (by norm_num)))
    dsimp [cost]
    nlinarith
  have hgapLower : B0 - D0 - cost ≤ B * x - D := by
    nlinarith [hBminusD, hBx]
  have hcbar : 0 ≤ (1 - s) * c :=
    mul_nonneg (sub_nonneg.mpr hsOne) hc
  have hthirdT :
      (1 - s) * c * (B * x - D) * t ≤
        (1 - s) * c * (B * x - D) * ts :=
    mul_le_mul_of_nonneg_left hts (mul_nonneg hcbar hgap)
  have hgapScaled := mul_le_mul_of_nonneg_left hgapLower hcbar
  have hgapScaledT := mul_le_mul_of_nonneg_right hgapScaled ht
  have hthird :
      c * (B0 - D0) * t -
          c * (s * (B0 - D0) + cost) * t ≤
        (1 - s) * c * (B * x - D) * ts := by
    have hid :
        c * (B0 - D0) * t -
            c * (s * (B0 - D0) + cost) * t ≤
          (1 - s) * c * (B0 - D0 - cost) * t := by
      have hscost : 0 ≤ s * c * cost * t := by positivity
      nlinarith
    exact hid.trans (hgapScaledT.trans hthirdT)
  unfold lrDA7IdealScalarCore lrDA7FiniteSymbolicLoss
    lrDA7FiniteScalarCore
  dsimp [cost] at hthird
  nlinarith

theorem lrDA7_finite_frozen_core_lower_of_coordinateBounds
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hrelevant : LRHighShapeVRelevant point)
    (hregion : LRDeterminantLowKRegion point)
    (hcoord : LRDA7FiniteCoordinateBounds point) :
    lrLowKIdealCore (Real.log (1 / point.s)) point.k point.chi -
        lrDA7FiniteSymbolicLoss point.s (lrCertificateE point)
          (lrLowKIdealD point.k) (lrDA7IdealB point)
          (lrDA7IdealPFull point) (lrLowKIdealS point.k point.chi)
          (lrDA7IdealTFull point) (lrDA7IdealCStar point) ≤
      lrDA7FiniteFrozenCore point := by
  have hD := lrDeterminantD1_lowK_finite_bounds hinterior hregion
  have hx := lrDA7_x_loss_bounds hinterior
  have hBnonnegative : 0 ≤ lrDA7FiniteB point :=
    (lrDA7IdealB_pos hinterior hregion).le.trans hcoord.B_lower
  have hscalar := lrDA7_finite_scalar_core_lower
    (s := point.s) (e := lrCertificateE point)
    (D0 := lrLowKIdealD point.k) (D := lrDeterminantD1 point)
    (B0 := lrDA7IdealB point) (B := lrDA7FiniteB point)
    (p := lrDA7IdealPFull point) (ps := lrDA7FiniteP point)
    (S := lrLowKIdealS point.k point.chi) (Ss := lrDA7FiniteS point)
    (t := lrDA7IdealTFull point) (ts := lrDA7FiniteT point)
    (c := lrDA7IdealCStar point) (x := lrCertificateX point)
    hinterior.1.1.le (hregion.1.trans (by norm_num))
    hinterior.2.1.1.le (lrDeterminantD1_nonnegative hinterior)
    hD.1 hD.2
    (lrDA7IdealB_pos hinterior hregion).le hBnonnegative
    hcoord.B_lower hcoord.B_upper
    (lrDA7IdealPFull_pos hinterior hregion).le
    (lrDA7FiniteP_lower hinterior)
    hcoord.idealS_nonpos (lrDA7FiniteS_lower hinterior)
    (lrDA7IdealTFull_pos hinterior hregion).le hcoord.finiteT_lower
    (lrDA7IdealCStar_nonnegative hinterior hregion)
    hx.1 hx.2 (lrDA7FiniteGap_pos hinterior hrelevant).le
  rw [lrLowKIdealCore_eq_scalarCore,
    lrDA7FiniteFrozenCore_eq_scalarCore]
  exact hscalar

/-- The finite-`s` analytic comparison with all of its coordinate inputs
discharged, expressed before the scalar endpoint envelope proved below. -/
theorem lrDA7_finite_frozen_core_lower
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hrelevant : LRHighShapeVRelevant point)
    (hregion : LRDeterminantLowKRegion point) :
    lrLowKIdealCore (Real.log (1 / point.s)) point.k point.chi -
        lrDA7FiniteSymbolicLoss point.s (lrCertificateE point)
          (lrLowKIdealD point.k) (lrDA7IdealB point)
          (lrDA7IdealPFull point) (lrLowKIdealS point.k point.chi)
          (lrDA7IdealTFull point) (lrDA7IdealCStar point) ≤
      lrDA7FiniteFrozenCore point :=
  lrDA7_finite_frozen_core_lower_of_coordinateBounds hinterior hrelevant
    hregion (lrDA7FiniteCoordinateBounds_proved hinterior hregion)

/-! ## Logarithmic endpoint primitives -/

lemma lrDA7_log_scale_lower
    {s : ℝ} (hs : s ∈ Ioc (0 : ℝ) lrDA7S0) :
    7 * Real.log 2 ≤ Real.log (1 / s) := by
  have harg : (128 : ℝ) ≤ 1 / s := by
    rw [le_div_iff₀ hs.1]
    calc
      128 * s ≤ 128 * lrDA7S0 :=
        mul_le_mul_of_nonneg_left hs.2 (by norm_num)
      _ = 1 := by norm_num [lrDA7S0]
  have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 128) harg
  have hpow : Real.log (128 : ℝ) = 7 * Real.log 2 := by
    rw [show (128 : ℝ) = 2 ^ 7 by norm_num, Real.log_pow]
    norm_num
  rwa [hpow] at hlog

lemma lrDA7_log_scale_ge_LMinus
    {s : ℝ} (hs : s ∈ Ioc (0 : ℝ) lrDA7S0) :
    lrDA7LMinus ≤ Real.log (1 / s) := by
  have hbase := lrDA7_log_scale_lower hs
  exact lrDA7_log_window.1.le.trans hbase

lemma lrDA7_log_scale_pos
    {s : ℝ} (hs : s ∈ Ioc (0 : ℝ) lrDA7S0) :
    0 < Real.log (1 / s) := by
  have hL := lrDA7_log_scale_lower hs
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  linarith

/-- The elementary monotonicity of `s log (1/s)` on the range used in
DA7.  This is the `1/s` analogue of `mul_log_four_div_le_endpoint`. -/
lemma lrDA7_mul_log_inv_le_endpoint
    {s a : ℝ} (hs : 0 < s) (ha : 0 < a) (hsa : s ≤ a)
    (hlog : 1 ≤ Real.log (1 / a)) :
    s * Real.log (1 / s) ≤ a * Real.log (1 / a) := by
  have hsNe := hs.ne'
  have haNe := ha.ne'
  let u : ℝ := a / s
  have hu : 1 ≤ u := by
    unfold u
    rw [le_div_iff₀ hs]
    simpa using hsa
  have huPos : 0 < u := zero_lt_one.trans_le hu
  have hfactor : 1 / s = (1 / a) * u := by
    unfold u
    field_simp [hsNe, haNe]
  have hbasePos : 0 < 1 / a := one_div_pos.mpr ha
  have hlogSplit :
      Real.log (1 / s) = Real.log (1 / a) + Real.log u := by
    rw [hfactor, Real.log_mul hbasePos.ne' huPos.ne']
  have hlogU := Real.log_le_sub_one_of_pos huPos
  have hscaled := mul_le_mul_of_nonneg_left hlogU hs.le
  have hsu : s * u = a := by
    unfold u
    field_simp [hsNe]
  rw [mul_sub, mul_one, hsu] at hscaled
  have hendpoint := mul_le_mul_of_nonneg_right hsa
    (sub_nonneg.mpr hlog)
  rw [hlogSplit]
  nlinarith

lemma lrDA7_s_mul_log_upper
    {s : ℝ} (hs : s ∈ Ioc (0 : ℝ) lrDA7S0) :
    s * Real.log (1 / s) ≤ lrDA7S0 * lrDA7LPlus := by
  have hendpointLog :
      Real.log (1 / lrDA7S0) = 7 * Real.log 2 := by
    dsimp [lrDA7S0]
    rw [show (1 / (1 / 128 : ℝ)) = 2 ^ 7 by norm_num,
      Real.log_pow]
    norm_num
  have hendpointOne : 1 ≤ Real.log (1 / lrDA7S0) := by
    rw [hendpointLog]
    nlinarith [Real.log_two_gt_d9]
  have hmul := lrDA7_mul_log_inv_le_endpoint hs.1
    (show 0 < lrDA7S0 by norm_num [lrDA7S0]) hs.2 hendpointOne
  have hwindow := lrDA7_log_window.2.le
  rw [hendpointLog] at hmul
  have hscaled := mul_le_mul_of_nonneg_left hwindow
    (show 0 ≤ lrDA7S0 by norm_num [lrDA7S0])
  exact hmul.trans hscaled

/-! ## The nonlinear `P_fin` endpoint substitution -/

noncomputable def lrDA7PFinWeight (s : ℝ) : ℝ :=
  s * lrDA7PFin (Real.log (1 / s))

lemma hasDerivAt_lrDA7Log
    {s : ℝ} (hs : 0 < s) :
    HasDerivAt (fun z : ℝ ↦ Real.log (1 / z)) (-1 / s) s := by
  have hsNe := hs.ne'
  have hquot : HasDerivAt (fun z : ℝ ↦ 1 / z) (-1 / s ^ 2) s := by
    convert (hasDerivAt_const s (1 : ℝ)).div (hasDerivAt_id s) hsNe using 1
    all_goals
      simp only [id_eq]
      field_simp [hsNe]
      ring
  have hquotNe : 1 / s ≠ 0 := div_ne_zero (by norm_num) hsNe
  have hlog := (Real.hasDerivAt_log hquotNe).comp s hquot
  convert hlog using 1
  field_simp [hsNe]

lemma hasDerivAt_lrDA7PFinWeight
    {s : ℝ} (hs : 0 < s) :
    HasDerivAt lrDA7PFinWeight
      (lrDA7PFin (Real.log (1 / s)) -
        lrDA7PFinPrime (Real.log (1 / s))) s := by
  let L := Real.log (1 / s)
  have hL := hasDerivAt_lrDA7Log hs
  have hleft := hL.add_const (7 / 5 + lrDA7S0 / 2)
  have hright := hL.add_const (7 / 5)
  have hprod := (hasDerivAt_id s).mul (hleft.mul hright)
  unfold lrDA7PFinWeight lrDA7PFin lrDA7PFinPrime
  convert hprod using 1
  · funext x
    simp only [Pi.mul_apply, id_eq]
    ring
  · simp only [Pi.mul_apply, id_eq]
    field_simp [hs.ne']
    ring

lemma lrDA7PFinWeight_monotoneOn :
    MonotoneOn lrDA7PFinWeight (Ioc (0 : ℝ) lrDA7S0) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ioc (0 : ℝ) lrDA7S0)
  · intro s hs
    exact (hasDerivAt_lrDA7PFinWeight hs.1).continuousAt.continuousWithinAt
  · intro s hs
    rw [interior_Ioc] at hs
    exact (hasDerivAt_lrDA7PFinWeight hs.1).differentiableAt
      |>.differentiableWithinAt
  · intro s hs
    rw [interior_Ioc] at hs
    rw [(hasDerivAt_lrDA7PFinWeight hs.1).deriv]
    exact (lrDA7_endpoint_polynomial_gaps_pos
      (lrDA7_log_scale_ge_LMinus
        (show s ∈ Ioc (0 : ℝ) lrDA7S0 from ⟨hs.1, hs.2.le⟩))).1.le

lemma lrDA7PFin_endpoint_order :
    lrDA7PFin (7 * Real.log 2) ≤ lrDA7PFin lrDA7LPlus := by
  have horder := lrDA7_log_window.2.le
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hsum :
      0 ≤ lrDA7LPlus + 7 * Real.log 2 +
        2 * (7 / 5 : ℝ) + lrDA7S0 / 2 := by
    dsimp [lrDA7LPlus, lrDA7S0]
    nlinarith
  have hprod := mul_nonneg (sub_nonneg.mpr horder) hsum
  unfold lrDA7PFin
  nlinarith

lemma lrDA7_s_mul_PFin_upper
    {s : ℝ} (hs : s ∈ Ioc (0 : ℝ) lrDA7S0) :
    s * lrDA7PFin (Real.log (1 / s)) ≤
      lrDA7S0 * lrDA7PFin lrDA7LPlus := by
  have hmono := lrDA7PFinWeight_monotoneOn hs
    (show lrDA7S0 ∈ Ioc (0 : ℝ) lrDA7S0 by
      norm_num [lrDA7S0]) hs.2
  have hendpointLog :
      Real.log (1 / lrDA7S0) = 7 * Real.log 2 := by
    dsimp [lrDA7S0]
    rw [show (1 / (1 / 128 : ℝ)) = 2 ^ 7 by norm_num,
      Real.log_pow]
    norm_num
  unfold lrDA7PFinWeight at hmono
  rw [hendpointLog] at hmono
  have hscaled := mul_le_mul_of_nonneg_left lrDA7PFin_endpoint_order
    (show 0 ≤ lrDA7S0 by norm_num [lrDA7S0])
  exact hmono.trans hscaled

/-! ## Elementary ideal-coordinate envelopes -/

lemma lrDA7IdealD_upper
    {s k : ℝ} (hs : 0 < s) (hs0 : s ≤ lrDA7S0) (hsk : s ≤ k) :
    lrLowKIdealD k ≤ (Real.log (1 / s) + s) / 2 := by
  have hk : 0 < k := hs.trans_le hsk
  have hdenS : 0 < 2 * s := mul_pos (by norm_num) hs
  have hdenK : 0 < 2 * k := mul_pos (by norm_num) hk
  have hrecip : 1 / (2 * k) ≤ 1 / (2 * s) := by
    exact one_div_le_one_div_of_le hdenS (by nlinarith)
  have hargS : 0 < 1 + 1 / (2 * s) := by positivity
  have hlogOrder :
      Real.log (1 + 1 / (2 * k)) ≤
        Real.log (1 + 1 / (2 * s)) := by
    exact Real.log_le_log (by positivity) (by linarith)
  have hdenRatS : 0 < 4 * s + 3 := by positivity
  have hrat : 1 / (4 * k + 3) ≤ 1 / (4 * s + 3) := by
    exact one_div_le_one_div_of_le hdenRatS (by nlinarith)
  have hratThird : 1 / (4 * s + 3) ≤ (1 / 3 : ℝ) := by
    exact one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 3)
      (by nlinarith)
  have hlogOne : Real.log (1 + 2 * s) ≤ 2 * s := by
    simpa using Real.log_le_sub_one_of_pos (show 0 < 1 + 2 * s by linarith)
  have hsplit :
      Real.log (1 + 1 / (2 * s)) =
        Real.log (1 / s) + Real.log (1 + 2 * s) - Real.log 2 := by
    have hnum : 1 + 2 * s ≠ 0 := (show 0 < 1 + 2 * s by linarith).ne'
    have hsNe := hs.ne'
    have hid : 1 + 1 / (2 * s) = (1 + 2 * s) / (2 * s) := by
      field_simp [hsNe]
      ring
    rw [hid, Real.log_div hnum (mul_ne_zero (by norm_num) hsNe),
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hsNe,
      Real.log_div (by norm_num : (1 : ℝ) ≠ 0) hsNe,
      Real.log_one]
    ring
  have hsmall : s + 2 / 3 ≤ Real.log 2 := by
    dsimp [lrDA7S0] at hs0
    nlinarith [Real.log_two_gt_d9]
  unfold lrLowKIdealD
  rw [hsplit] at hlogOrder
  nlinarith

lemma lrDA7IdealB_upper
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hregion : LRDeterminantLowKRegion point) :
    lrDA7IdealB point ≤
      Real.log (1 / point.s) / 2 + 7 / 10 := by
  have hk : 0 < point.k := hinterior.1.1.trans_le hregion.2.1
  have hlogK : 0 ≤ Real.log (1 + point.k) :=
    Real.log_nonneg (by linarith)
  have hlogTwo : Real.log 2 < (7 / 10 : ℝ) :=
    Real.log_two_lt_d9.trans (by norm_num)
  unfold lrDA7IdealB lrLowKIdealBOffset
  linarith

lemma lrDA7IdealPFull_upper
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hregion : LRDeterminantLowKRegion point) :
    lrDA7IdealPFull point ≤ Real.log (1 / point.s) + 12 / 5 := by
  have hk : 0 < point.k := hinterior.1.1.trans_le hregion.2.1
  have hchi : point.chi ∈ Icc (0 : ℝ) 1 :=
    ⟨hinterior.2.2.1.le, hinterior.2.2.2.le⟩
  have hA : 0 ≤ lrLowKIdealA point.k point.chi := by
    have hinner : 1 ≤ 1 + point.k * point.chi := by
      exact le_add_of_nonneg_right (mul_nonneg hk.le hchi.1)
    have houter : 1 ≤ 1 + point.k := by linarith
    have hlogInner := Real.log_nonneg hinner
    have hlogOuter := Real.log_nonneg houter
    unfold lrLowKIdealA
    exact div_nonneg
      (add_nonneg (mul_nonneg hchi.1 hlogInner) hlogOuter)
      (by linarith [hchi.1])
  have hlogTwo : Real.log 2 < (7 / 10 : ℝ) :=
    Real.log_two_lt_d9.trans (by norm_num)
  unfold lrDA7IdealPFull lrLowKIdealP
  linarith

lemma lrDA7IdealS_abs_upper
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hregion : LRDeterminantLowKRegion point) :
    -lrLowKIdealS point.k point.chi ≤
      Real.log (1 / point.s) + 4 := by
  have hs := hinterior.1.1
  have hk : 0 < point.k := hs.trans_le hregion.2.1
  have hchi : point.chi ∈ Icc (0 : ℝ) 1 :=
    ⟨hinterior.2.2.1.le, hinterior.2.2.2.le⟩
  have hlogs : Real.log point.s ≤ Real.log point.k :=
    Real.log_le_log hs hregion.2.1
  have hlogInv : Real.log (1 / point.s) = -Real.log point.s := by
    rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) hs.ne']
    norm_num
  have hq := lrSmallSBridgeQChi_lower hchi
  have hqDef : lrLowKIdealQChi point.chi =
      lrSmallSBridgeQChi point.chi := by rfl
  have hA := lrLowKIdealA_le_log_one_add hk hchi
  have harg : 0 < 1 + point.k := by positivity
  have hlogOneK : Real.log (1 + point.k) ≤ Real.log 2 :=
    Real.log_le_log harg (by linarith [hregion.2.2])
  have hlogTwo : Real.log 2 < (7 / 10 : ℝ) :=
    Real.log_two_lt_d9.trans (by norm_num)
  unfold lrLowKIdealS
  rw [hqDef, hlogInv]
  linarith

lemma lrDA7IdealTFull_upper
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hregion : LRDeterminantLowKRegion point) :
    lrDA7IdealTFull point ≤ Real.log (1 / point.s) + 7 / 5 := by
  have hk : 0 < point.k := hinterior.1.1.trans_le hregion.2.1
  have hchi : point.chi ∈ Icc (0 : ℝ) 1 :=
    ⟨hinterior.2.2.1.le, hinterior.2.2.2.le⟩
  have hAH := lrLowKIdealAH_ge_one hk hchi
  have hlogTwo : Real.log 2 < (7 / 10 : ℝ) :=
    Real.log_two_lt_d9.trans (by norm_num)
  unfold lrDA7IdealTFull lrLowKIdealT
  linarith

lemma lrDA7IdealC_nonnegative : 0 ≤ lrLowKIdealC := by
  have hlog43 := lrLowK_log_four_thirds_lower
  have hlogTwo : Real.log 2 < (7 / 10 : ℝ) :=
    Real.log_two_lt_d9.trans (by norm_num)
  unfold lrLowKIdealC
  nlinarith

lemma lrDA7IdealCStar_upper
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hregion : LRDeterminantLowKRegion point) :
    lrDA7IdealCStar point ≤
      1 / (3 * Real.log (1 / point.s)) := by
  have hsIoc : point.s ∈ Ioc (0 : ℝ) lrDA7S0 := by
    simpa [lrDA7S0] using And.intro hinterior.1.1 hregion.1
  have hL := lrDA7_log_scale_pos hsIoc
  have hdenL : 0 < 3 * Real.log (1 / point.s) := mul_pos (by norm_num) hL
  have hdenOrder :
      3 * Real.log (1 / point.s) ≤
        3 * (Real.log (1 / point.s) + lrLowKIdealC) := by
    nlinarith [lrDA7IdealC_nonnegative]
  unfold lrDA7IdealCStar
  exact one_div_le_one_div_of_le hdenL hdenOrder

/-! ## Six termwise endpoint bounds -/

lemma lrDA7_finite_term_D_upper
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hregion : LRDeterminantLowKRegion point) :
    point.s * lrLowKIdealD point.k ≤
      lrDA7S0 * (lrDA7LPlus + lrDA7S0) / 2 := by
  have hsIoc : point.s ∈ Ioc (0 : ℝ) lrDA7S0 := by
    simpa [lrDA7S0] using And.intro hinterior.1.1 hregion.1
  have hD := lrDA7IdealD_upper hinterior.1.1 hsIoc.2 hregion.2.1
  have hscaled := mul_le_mul_of_nonneg_left hD hinterior.1.1.le
  have hlog := lrDA7_s_mul_log_upper hsIoc
  have hsSq : point.s ^ 2 ≤ lrDA7S0 ^ 2 := by
    exact pow_le_pow_left₀ hsIoc.1.le hsIoc.2 2
  nlinarith

lemma lrDA7_finite_term_P_upper
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hregion : LRDeterminantLowKRegion point) :
    point.s / 2 * lrDA7IdealPFull point ≤
      lrDA7S0 / 2 * (lrDA7LPlus + 12 / 5) := by
  have hsIoc : point.s ∈ Ioc (0 : ℝ) lrDA7S0 := by
    simpa [lrDA7S0] using And.intro hinterior.1.1 hregion.1
  have hp := lrDA7IdealPFull_upper hinterior hregion
  have hsHalf : 0 ≤ point.s / 2 :=
    div_nonneg hinterior.1.1.le (by norm_num : (0 : ℝ) ≤ 2)
  have hscaled := mul_le_mul_of_nonneg_left hp hsHalf
  have hlog := lrDA7_s_mul_log_upper hsIoc
  have hlinear := mul_le_mul_of_nonneg_right hsIoc.2
    (show (0 : ℝ) ≤ 12 / 5 by norm_num)
  nlinarith

lemma lrDA7_finite_term_B_upper
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hregion : LRDeterminantLowKRegion point) :
    point.s * lrDA7IdealB point ≤
      lrDA7S0 * (lrDA7LPlus / 2 + 7 / 10) := by
  have hsIoc : point.s ∈ Ioc (0 : ℝ) lrDA7S0 := by
    simpa [lrDA7S0] using And.intro hinterior.1.1 hregion.1
  have hB := lrDA7IdealB_upper hinterior hregion
  have hscaled := mul_le_mul_of_nonneg_left hB hinterior.1.1.le
  have hlog := lrDA7_s_mul_log_upper hsIoc
  have hlinear := mul_le_mul_of_nonneg_right hsIoc.2
    (show (0 : ℝ) ≤ 7 / 10 by norm_num)
  nlinarith

lemma lrDA7_finite_term_S_upper
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hregion : LRDeterminantLowKRegion point) :
    lrCertificateE point / 2 *
        (-lrLowKIdealS point.k point.chi) ≤
      lrDA7S0 / 2 * (lrDA7LPlus + 4) := by
  have hsIoc : point.s ∈ Ioc (0 : ℝ) lrDA7S0 := by
    simpa [lrDA7S0] using And.intro hinterior.1.1 hregion.1
  have he : lrCertificateE point ≤ point.s := by
    unfold lrCertificateE
    nlinarith [mul_le_mul_of_nonneg_left hregion.2.2
      hinterior.1.1.le]
  have hSnonneg : 0 ≤ -lrLowKIdealS point.k point.chi := by
    linarith [lrLowKIdealS_nonpos_lowK hinterior hregion]
  have heScaled := mul_le_mul_of_nonneg_right he hSnonneg
  have hS := lrDA7IdealS_abs_upper hinterior hregion
  have hsScaled := mul_le_mul_of_nonneg_left hS hinterior.1.1.le
  have hlog := lrDA7_s_mul_log_upper hsIoc
  have hlinear := mul_le_mul_of_nonneg_right hsIoc.2
    (show (0 : ℝ) ≤ 4 by norm_num)
  nlinarith

lemma lrDA7_finite_term_es_upper
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hregion : LRDeterminantLowKRegion point) :
    lrCertificateE point * point.s / 2 ≤ lrDA7S0 ^ 2 / 2 := by
  have hsIoc : point.s ∈ Ioc (0 : ℝ) lrDA7S0 := by
    simpa [lrDA7S0] using And.intro hinterior.1.1 hregion.1
  have he : lrCertificateE point ≤ point.s := by
    unfold lrCertificateE
    nlinarith [mul_le_mul_of_nonneg_left hregion.2.2
      hinterior.1.1.le]
  have hprod := mul_le_mul_of_nonneg_right he hinterior.1.1.le
  have hsSq : point.s ^ 2 ≤ lrDA7S0 ^ 2 := by
    exact pow_le_pow_left₀ hsIoc.1.le hsIoc.2 2
  nlinarith

lemma lrDA7_finite_term_cubic_upper
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hregion : LRDeterminantLowKRegion point) :
    lrDA7IdealCStar point *
        (point.s * (lrDA7IdealB point - lrLowKIdealD point.k) +
          lrCertificateE point *
            (lrDA7IdealB point + lrCertificateE point / 2)) *
        lrDA7IdealTFull point ≤
      lrDA7S0 / (3 * lrDA7LMinus) *
        (2 * (lrDA7LPlus / 2 + 7 / 10) + lrDA7S0 / 2) *
        (lrDA7LPlus + 7 / 5) := by
  let L := Real.log (1 / point.s)
  let D0 := lrLowKIdealD point.k
  let B0 := lrDA7IdealB point
  let e := lrCertificateE point
  let c := lrDA7IdealCStar point
  let t := lrDA7IdealTFull point
  have hsIoc : point.s ∈ Ioc (0 : ℝ) lrDA7S0 := by
    simpa [lrDA7S0] using And.intro hinterior.1.1 hregion.1
  have hs0 := hsIoc.2
  have hs : 0 ≤ point.s := hsIoc.1.le
  have he0 : 0 ≤ e := by
    dsimp [e]
    exact hinterior.2.1.1.le
  have he : e ≤ point.s := by
    dsimp [e]
    unfold lrCertificateE
    nlinarith [mul_le_mul_of_nonneg_left hregion.2.2 hs]
  have hD0 : 0 ≤ D0 := by
    dsimp [D0]
    exact (lrLowKIdealD_pos
      (hinterior.1.1.trans_le hregion.2.1)).le
  have hB0 : 0 ≤ B0 := by
    dsimp [B0]
    exact (lrDA7IdealB_pos hinterior hregion).le
  have hB0Upper : B0 ≤ L / 2 + 7 / 10 := by
    simpa [B0, L] using lrDA7IdealB_upper hinterior hregion
  have ht0 : 0 ≤ t := by
    dsimp [t]
    exact (lrDA7IdealTFull_pos hinterior hregion).le
  have htUpper : t ≤ L + 7 / 5 := by
    simpa [t, L] using lrDA7IdealTFull_upper hinterior hregion
  have hc0 : 0 ≤ c := by
    dsimp [c]
    exact lrDA7IdealCStar_nonnegative hinterior hregion
  have hcUpper : c ≤ 1 / (3 * L) := by
    simpa [c, L] using lrDA7IdealCStar_upper hinterior hregion
  have hLpos : 0 < L := by
    dsimp [L]
    exact lrDA7_log_scale_pos hsIoc
  have hLminus : lrDA7LMinus ≤ L := by
    dsimp [L]
    exact lrDA7_log_scale_ge_LMinus hsIoc
  have hLminusPos : 0 < lrDA7LMinus := by norm_num [lrDA7LMinus]
  have hbracket :
      point.s * (B0 - D0) + e * (B0 + e / 2) ≤
        point.s * (2 * B0 + point.s / 2) := by
    have hfirst : point.s * (B0 - D0) ≤ point.s * B0 := by
      nlinarith [mul_nonneg hs hD0]
    have hsumNonneg : 0 ≤ B0 + e / 2 :=
      add_nonneg hB0 (div_nonneg he0 (by norm_num))
    have hsecondA := mul_le_mul_of_nonneg_right he hsumNonneg
    have hsecondB :
        point.s * (B0 + e / 2) ≤
          point.s * (B0 + point.s / 2) := by
      exact mul_le_mul_of_nonneg_left (by linarith) hs
    nlinarith
  have hbracketEndpoint :
      point.s * (B0 - D0) + e * (B0 + e / 2) ≤
        point.s * (L + 7 / 5 + lrDA7S0 / 2) := by
    have hinside : 2 * B0 + point.s / 2 ≤
        L + 7 / 5 + lrDA7S0 / 2 := by
      nlinarith
    exact hbracket.trans (mul_le_mul_of_nonneg_left hinside hs)
  have hinsideNonneg : 0 ≤ L + 7 / 5 + lrDA7S0 / 2 := by
    dsimp [lrDA7S0]
    nlinarith
  have htBoundNonneg : 0 ≤ L + 7 / 5 := by nlinarith
  have hfirstScale :
      c * (point.s * (B0 - D0) + e * (B0 + e / 2)) * t ≤
        c * (point.s * (L + 7 / 5 + lrDA7S0 / 2)) * t := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hbracketEndpoint hc0) ht0
  have hsecondScale :
      c * (point.s * (L + 7 / 5 + lrDA7S0 / 2)) * t ≤
        c * (point.s * (L + 7 / 5 + lrDA7S0 / 2)) *
          (L + 7 / 5) := by
    exact mul_le_mul_of_nonneg_left htUpper
      (mul_nonneg hc0 (mul_nonneg hs hinsideNonneg))
  have hthirdScale :
      c * (point.s * (L + 7 / 5 + lrDA7S0 / 2)) *
          (L + 7 / 5) ≤
        (1 / (3 * L)) *
          (point.s * (L + 7 / 5 + lrDA7S0 / 2)) *
          (L + 7 / 5) := by
    have hfactorNonneg :
        0 ≤ point.s * (L + 7 / 5 + lrDA7S0 / 2) *
          (L + 7 / 5) := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hcUpper hfactorNonneg]
  have hdenInv : 1 / (3 * L) ≤ 1 / (3 * lrDA7LMinus) := by
    exact one_div_le_one_div_of_le (mul_pos (by norm_num) hLminusPos)
      (by nlinarith)
  have hfourthScale :
      (1 / (3 * L)) *
          (point.s * (L + 7 / 5 + lrDA7S0 / 2)) *
          (L + 7 / 5) ≤
        (1 / (3 * lrDA7LMinus)) *
          (point.s * (L + 7 / 5 + lrDA7S0 / 2)) *
          (L + 7 / 5) := by
    have hfactorNonneg :
        0 ≤ point.s * (L + 7 / 5 + lrDA7S0 / 2) *
          (L + 7 / 5) := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hdenInv hfactorNonneg]
  have hPFin :
      point.s * (L + 7 / 5 + lrDA7S0 / 2) * (L + 7 / 5) ≤
        lrDA7S0 * lrDA7PFin lrDA7LPlus := by
    have h := lrDA7_s_mul_PFin_upper hsIoc
    simpa [L, lrDA7PFin, mul_assoc] using h
  have hfinalScale := mul_le_mul_of_nonneg_left hPFin
    (show 0 ≤ 1 / (3 * lrDA7LMinus) by positivity)
  calc
    lrDA7IdealCStar point *
          (point.s * (lrDA7IdealB point - lrLowKIdealD point.k) +
            lrCertificateE point *
              (lrDA7IdealB point + lrCertificateE point / 2)) *
          lrDA7IdealTFull point
        ≤ c * (point.s * (L + 7 / 5 + lrDA7S0 / 2)) * t := hfirstScale
    _ ≤ c * (point.s * (L + 7 / 5 + lrDA7S0 / 2)) *
          (L + 7 / 5) := hsecondScale
    _ ≤ (1 / (3 * L)) *
          (point.s * (L + 7 / 5 + lrDA7S0 / 2)) *
          (L + 7 / 5) := hthirdScale
    _ ≤ (1 / (3 * lrDA7LMinus)) *
          (point.s * (L + 7 / 5 + lrDA7S0 / 2)) *
          (L + 7 / 5) := hfourthScale
    _ ≤ (1 / (3 * lrDA7LMinus)) *
          (lrDA7S0 * lrDA7PFin lrDA7LPlus) := by
      simpa [mul_assoc] using hfinalScale
    _ = lrDA7S0 / (3 * lrDA7LMinus) *
          (2 * (lrDA7LPlus / 2 + 7 / 10) + lrDA7S0 / 2) *
          (lrDA7LPlus + 7 / 5) := by
      unfold lrDA7PFin
      ring

/-! ## Complete scalar envelope -/

theorem lrDA7_finite_symbolic_loss_le_endpoint
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hregion : LRDeterminantLowKRegion point) :
    lrDA7FiniteSymbolicLoss point.s (lrCertificateE point)
        (lrLowKIdealD point.k) (lrDA7IdealB point)
        (lrDA7IdealPFull point) (lrLowKIdealS point.k point.chi)
        (lrDA7IdealTFull point) (lrDA7IdealCStar point) ≤
      lrDA7FiniteEndpoint := by
  have hD := lrDA7_finite_term_D_upper hinterior hregion
  have hP := lrDA7_finite_term_P_upper hinterior hregion
  have hB := lrDA7_finite_term_B_upper hinterior hregion
  have hS := lrDA7_finite_term_S_upper hinterior hregion
  have hes := lrDA7_finite_term_es_upper hinterior hregion
  have hc := lrDA7_finite_term_cubic_upper hinterior hregion
  unfold lrDA7FiniteSymbolicLoss lrDA7FiniteEndpoint
  linarith

/-- Once the scalar endpoint envelope is supplied, the complete finite-`s`
row is available in the exact form consumed by the restoration assembly. -/
theorem lrDA7_finite_endpoint_bridge
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hrelevant : LRHighShapeVRelevant point)
    (hregion : LRDeterminantLowKRegion point)
    (henvelope :
      lrDA7FiniteSymbolicLoss point.s (lrCertificateE point)
          (lrLowKIdealD point.k) (lrDA7IdealB point)
          (lrDA7IdealPFull point) (lrLowKIdealS point.k point.chi)
          (lrDA7IdealTFull point) (lrDA7IdealCStar point) ≤
        lrDA7FiniteEndpoint) :
    lrLowKIdealCore (Real.log (1 / point.s)) point.k point.chi -
        lrDA7FiniteEndpoint ≤ lrDA7FiniteFrozenCore point := by
  have hfinite := lrDA7_finite_frozen_core_lower hinterior hrelevant hregion
  linarith

/-- The finite-`s` restoration row with the scalar envelope discharged. -/
theorem lrDA7_finite_endpoint_bridge_proved
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hrelevant : LRHighShapeVRelevant point)
    (hregion : LRDeterminantLowKRegion point) :
    lrLowKIdealCore (Real.log (1 / point.s)) point.k point.chi -
        lrDA7FiniteEndpoint ≤ lrDA7FiniteFrozenCore point := by
  exact lrDA7_finite_endpoint_bridge hinterior hrelevant hregion
    (lrDA7_finite_symbolic_loss_le_endpoint hinterior hregion)

/-! ## Honest remaining restoration interface -/

/-- The three stages which remain after the finite-`s` core.  Future
analytic modules must identify `afterChannel` with the true-`v`, `Q=q`
determinant and `afterEntropyCoefficient` with the coefficient-restored
entropy expression.  The chained inequalities themselves already prevent
either witness from weakening the final claim. -/
structure LRLowKRemainingRestoration (point : CertificatePoint) where
  afterChannel : ℝ
  afterEntropyCoefficient : ℝ
  channel :
    lrDA7FiniteFrozenCore point - lrDA7ChannelEndpoint ≤ afterChannel
  entropyCoefficient :
    afterChannel - lrDA7EntropyEndpoint ≤ afterEntropyCoefficient
  directRemainder :
    afterEntropyCoefficient - lrDA7DirectEndpoint ≤
      lrLowKActualNormalized point

/-- Exact (not merely one-sided) decomposition of the total loss into the
finite, channel, entropy-coefficient, and direct-remainder stages. -/
theorem lrLowK_exact_four_stage_loss_decomposition
    {point : CertificatePoint}
    (h : LRLowKRemainingRestoration point) :
    lrLowKIdealCore (Real.log (1 / point.s)) point.k point.chi -
        lrLowKActualNormalized point =
      (lrLowKIdealCore (Real.log (1 / point.s)) point.k point.chi -
          lrDA7FiniteFrozenCore point) +
        (lrDA7FiniteFrozenCore point - h.afterChannel) +
        (h.afterChannel - h.afterEntropyCoefficient) +
        (h.afterEntropyCoefficient - lrLowKActualNormalized point) := by
  ring

/-- Exact telescoping of the three named post-finite stages. -/
theorem LRLowKRemainingRestoration.total
    {point : CertificatePoint}
    (h : LRLowKRemainingRestoration point) :
    lrDA7FiniteFrozenCore point -
        (lrDA7ChannelEndpoint + lrDA7EntropyEndpoint +
          lrDA7DirectEndpoint) ≤
      lrLowKActualNormalized point := by
  linarith [h.channel, h.entropyCoefficient, h.directRemainder]

/-- Assembly reducing `LRLowKRestorationCertificate` to the genuine
finite-`s` comparison and the three explicitly named remaining stages. -/
theorem lrLowKRestorationCertificate_of_finite_and_remaining
    (finite : ∀ point : CertificatePoint,
      LRHighShapeInterior point →
      LRHighShapeVRelevant point →
      LRDeterminantLowKRegion point →
      lrLowKIdealCore (Real.log (1 / point.s)) point.k point.chi -
          lrDA7FiniteEndpoint ≤ lrDA7FiniteFrozenCore point)
    (remaining : ∀ point : CertificatePoint,
      LRHighShapeInterior point →
      LRHighShapeVRelevant point →
      LRDeterminantLowKRegion point →
      LRLowKRemainingRestoration point) :
    LRLowKRestorationCertificate := by
  intro point hinterior hrelevant hregion
  have hfinite := finite point hinterior hrelevant hregion
  have hremaining :=
    (remaining point hinterior hrelevant hregion).total
  dsimp [lrDA7RestoreEndpoint]
  linarith

/-- With the finite-`s` row now proved, the low-`k` restoration certificate
reduces only to the channel, entropy-coefficient, and direct-remainder
stages. -/
theorem lrLowKRestorationCertificate_of_remaining
    (remaining : ∀ point : CertificatePoint,
      LRHighShapeInterior point →
      LRHighShapeVRelevant point →
      LRDeterminantLowKRegion point →
      LRLowKRemainingRestoration point) :
    LRLowKRestorationCertificate := by
  exact lrLowKRestorationCertificate_of_finite_and_remaining
    (fun point hinterior hrelevant hregion ↦
      lrDA7_finite_endpoint_bridge_proved hinterior hrelevant hregion)
    remaining

end CourtadeKumar
