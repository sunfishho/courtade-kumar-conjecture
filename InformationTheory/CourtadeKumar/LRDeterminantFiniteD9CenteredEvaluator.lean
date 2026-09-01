import InformationTheory.CourtadeKumar.LRDeterminantFiniteD9Evaluator
import InformationTheory.CourtadeKumar.LRHighShapeVCenteredEvaluator

set_option autoImplicit false

/-!
# Centered finite-D9 accepted leaves

The direct finite-D9 evaluator is exact interval AD, but its whole-box value
enclosure can be much wider than its derivative enclosures predict.  This
module separates the two jobs: it evaluates the value on the singleton box
at the rational midpoint and evaluates all three derivatives on the original
box.  The generic checked midpoint theorem then supplies the leaf proof.

Every executable decision remains a `Bool`; the analytic layer below proves
that the derivative fields are the genuine derivatives of the D9 replay
target.  No proof-producing native evaluator is used.
-/

open Set Filter

namespace CourtadeKumar

/-! ## Exact raw-coordinate derivatives -/

/-- Derivative of `Y = b_s(e)/e` along a curve with derivatives `s'`, `e'`. -/
noncomputable def lrFiniteDeterminantD9YDeriv
    (point : CertificatePoint) (s' e' : ℝ) : ℝ :=
  (lrCertificateBDeriv point.s (lrCertificateE point) s' e' *
      lrCertificateE point -
    lrCertificateB point.s (lrCertificateE point) * e') /
    lrCertificateE point ^ 2

/-- Derivative of the scalar logarithmic coefficient `D1(Y)`. -/
noncomputable def lrFiniteDeterminantD9D1Deriv
    (point : CertificatePoint) (s' e' : ℝ) : ℝ :=
  let Y := lrDeterminantY point
  let Y' := lrFiniteDeterminantD9YDeriv point s' e'
  (1 / 2 : ℝ) * ((Y' / 2) / ((1 + Y) / 2)) +
    ((Y' * (3 * Y + 1) - (Y - 1) * (3 * Y')) /
      (3 * Y + 1) ^ 2)

noncomputable def lrFiniteDeterminantD9PsiDeriv
    (point : CertificatePoint) (s' y0' e' v' : ℝ) : ℝ :=
  let g' := lrCertificateGShapeDeriv point y0' e' v'
  let pw' := lrCertificatePWDeriv point s' y0' e' v'
  let w' := lrCertificateOmegaDeriv point.s 0 s' 0
  g' + pw' -
    ((4 * w') * (1 + lrCertificateV point) -
      4 * lrCertificateW point * v') /
      (1 + lrCertificateV point) ^ 2

noncomputable def lrFiniteDeterminantD9DeltaDeriv
    (point : CertificatePoint) (x' v' : ℝ) : ℝ :=
  ((-(v' * lrCertificateX point + lrCertificateV point * x')) *
        (1 + lrCertificateV point) -
      (1 - lrCertificateV point * lrCertificateX point) * v') /
    (1 + lrCertificateV point) ^ 2

noncomputable def lrFiniteDeterminantD9FirstBracketDeriv
    (point : CertificatePoint) (s' y0' e' x' v' : ℝ) : ℝ :=
  let B' := lrCertificateBFlowDeriv point s' e' v'
  let D1' := lrFiniteDeterminantD9D1Deriv point s' e'
  let G' := lrCertificateGShapeDeriv point y0' e' v'
  let Psi' := lrFiniteDeterminantD9PsiDeriv point s' y0' e' v'
  let delta' := lrFiniteDeterminantD9DeltaDeriv point x' v'
  let W' := lrCertificateOmegaDeriv point.s 0 s' 0
  B' *
      (lrDeterminantPsi point - lrCertificateGShape point +
        4 * lrDeterminantDelta point * lrCertificateW point) +
    lrCertificateBFlow point *
      (Psi' - G' +
        4 * (delta' * lrCertificateW point +
          lrDeterminantDelta point * W')) +
    D1' * lrDeterminantPsi point + lrDeterminantD1 point * Psi'

noncomputable def lrFiniteDeterminantD9FactorDeriv
    (point : CertificatePoint) (s' e' x' v' : ℝ) : ℝ :=
  lrCertificateBFlowDeriv point s' e' v' * lrCertificateX point +
    lrCertificateBFlow point * x' -
    lrFiniteDeterminantD9D1Deriv point s' e'

/-- Product-rule derivative of the cancellation form of D9. -/
noncomputable def lrFiniteDeterminantD9CoordinateDeriv
    (point : CertificatePoint) (s' y0' e' x' v' : ℝ) : ℝ :=
  let halfSlope' := lrCertificateHalfSlopeDeriv point s' v'
  let first' := lrFiniteDeterminantD9FirstBracketDeriv
    point s' y0' e' x' v'
  let w' := lrCertificateOmegaDeriv point.s 0 s' 0
  let gap' := lrCertificateGapDeriv point s' y0' e' v'
  let factor' := lrFiniteDeterminantD9FactorDeriv point s' e' x' v'
  let first := lrDeterminantFirstBracket
    (lrCertificateBFlow point) (lrDeterminantD1 point)
    (lrCertificateGShape point) (lrDeterminantPsi point)
    (lrDeterminantDelta point) (lrCertificateW point)
  let factor := lrCertificateBFlow point * lrCertificateX point -
    lrDeterminantD1 point
  3 * (halfSlope' * first + lrCertificateHalfSlope point * first') +
    4 * (w' * lrCertificateGap point * factor +
      lrCertificateW point * gap' * factor +
      lrCertificateW point * lrCertificateGap point * factor')

/-- Exact directional derivative in the raw `(s,k,chi)` coordinates. -/
noncomputable def lrFiniteDeterminantD9RawDeriv
    (point : CertificatePoint) (s' k' chi' : ℝ) : ℝ :=
  let e' := s' * point.k + point.s * k'
  let y0' := chi' * lrCertificateE point + point.chi * e'
  let x' := -(chi' * lrCertificateE point + point.chi * e')
  let v' := lrCertificateVDeriv point e' x'
  lrFiniteDeterminantD9CoordinateDeriv point s' y0' e' x' v'

noncomputable def lrFiniteDeterminantD9DerivS
    (point : CertificatePoint) : ℝ :=
  lrFiniteDeterminantD9RawDeriv point 1 0 0

noncomputable def lrFiniteDeterminantD9DerivK
    (point : CertificatePoint) : ℝ :=
  lrFiniteDeterminantD9RawDeriv point 0 1 0

noncomputable def lrFiniteDeterminantD9DerivChi
    (point : CertificatePoint) : ℝ :=
  lrFiniteDeterminantD9RawDeriv point 0 0 1

/-! ## The centered D9 domain

Unlike the older high-shape midpoint evaluators, the finite-D9 replay target is
regular on the closed upper face `chi = 1`.  On that face the auxiliary
coordinate `v` is exactly `1`; all of the derivatives used below require only
`0 < v`.  Keeping this slightly larger domain local to D9 avoids weakening the
contracts of unrelated evaluators. -/

def LRFiniteDeterminantD9CenteredInterior (point : CertificatePoint) : Prop :=
  point.s ∈ Ioo (0 : ℝ) 1 ∧
    lrCertificateE point ∈ Ioo (0 : ℝ) 1 ∧
    point.chi ∈ Ioc (0 : ℝ) 1

def lrFiniteDeterminantD9CenteredBoxCheck (box : CertificateBox) : Bool :=
  decide (
    (0 : ℚ) < box.sLo ∧ box.sLo ≤ box.sHi ∧ box.sHi < 1 ∧
    (0 : ℚ) < box.kLo ∧ box.kLo ≤ box.kHi ∧
      box.sHi * box.kHi < 1 ∧
    (0 : ℚ) < box.chiLo ∧ box.chiLo ≤ box.chiHi ∧ box.chiHi ≤ 1)

theorem lrFiniteDeterminantD9CenteredBoxCheck_sound {box : CertificateBox}
    (hcheck : lrFiniteDeterminantD9CenteredBoxCheck box = true)
    {point : CertificatePoint} (hpoint : box.Contains point) :
    LRFiniteDeterminantD9CenteredInterior point := by
  have hparts :
      (0 : ℚ) < box.sLo ∧ box.sLo ≤ box.sHi ∧ box.sHi < 1 ∧
      (0 : ℚ) < box.kLo ∧ box.kLo ≤ box.kHi ∧
        box.sHi * box.kHi < 1 ∧
      (0 : ℚ) < box.chiLo ∧ box.chiLo ≤ box.chiHi ∧
        box.chiHi ≤ 1 := by
    simpa [lrFiniteDeterminantD9CenteredBoxCheck] using hcheck
  have hsLo : (0 : ℝ) < box.sLo := by exact_mod_cast hparts.1
  have hsOrder : (box.sLo : ℝ) ≤ box.sHi := by
    exact_mod_cast hparts.2.1
  have hsHi : (box.sHi : ℝ) < 1 := by exact_mod_cast hparts.2.2.1
  have hkLo : (0 : ℝ) < box.kLo := by exact_mod_cast hparts.2.2.2.1
  have hkOrder : (box.kLo : ℝ) ≤ box.kHi := by
    exact_mod_cast hparts.2.2.2.2.1
  have hprodHi : ((box.sHi * box.kHi : ℚ) : ℝ) < 1 := by
    exact_mod_cast hparts.2.2.2.2.2.1
  have hchiLo : (0 : ℝ) < box.chiLo := by
    exact_mod_cast hparts.2.2.2.2.2.2.1
  have hchiHi : (box.chiHi : ℝ) ≤ 1 := by
    exact_mod_cast hparts.2.2.2.2.2.2.2.2
  have hs : point.s ∈ Ioo (0 : ℝ) 1 :=
    ⟨hsLo.trans_le hpoint.1, hpoint.2.1.trans_lt hsHi⟩
  have hkPos : 0 < point.k := hkLo.trans_le hpoint.2.2.1
  have hkHiNonneg : (0 : ℝ) ≤ box.kHi := hkLo.le.trans hkOrder
  have heUpper : lrCertificateE point ≤
      (box.sHi : ℝ) * box.kHi := by
    unfold lrCertificateE
    exact mul_le_mul hpoint.2.1 hpoint.2.2.2.1 hkPos.le
      (hsLo.le.trans hsOrder)
  have he : lrCertificateE point ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · unfold lrCertificateE
      exact mul_pos hs.1 hkPos
    · exact heUpper.trans_lt (by simpa using hprodHi)
  have hchi : point.chi ∈ Ioc (0 : ℝ) 1 :=
    ⟨hchiLo.trans_le hpoint.2.2.2.2.1,
      hpoint.2.2.2.2.2.trans hchiHi⟩
  exact ⟨hs, he, hchi⟩

theorem hasDerivAt_lrCertificateV_curve_Ioc
    {z s' k' chi' : ℝ} {s k chi : ℝ → ℝ}
    (hs : HasDerivAt s s' z) (hk : HasDerivAt k k' z)
    (hchi : HasDerivAt chi chi' z)
    (heMem : lrCertificateE (lrCertificateCurve s k chi z) ∈ Ioo (0 : ℝ) 1)
    (hchiMem : chi z ∈ Ioc (0 : ℝ) 1) :
    let point := lrCertificateCurve s k chi z
    let e' := s' * k z + s z * k'
    let x' := -(chi' * lrCertificateE point + chi z * e')
    HasDerivAt (fun q ↦ lrCertificateV (lrCertificateCurve s k chi q))
      (lrCertificateVDeriv point e' x') z := by
  dsimp only
  let point := lrCertificateCurve s k chi z
  let e' := s' * k z + s z * k'
  let x' := -(chi' * lrCertificateE point + chi z * e')
  have he := hasDerivAt_lrCertificateE_curve (chi := chi) hs hk
  have hx := hasDerivAt_lrCertificateX_curve hs hk hchi
  have hxPos : 0 < lrCertificateX point := by
    change 0 < 1 - chi z *
      lrCertificateE (lrCertificateCurve s k chi z)
    have hprod : chi z * lrCertificateE (lrCertificateCurve s k chi z) < 1 :=
      (mul_le_mul_of_nonneg_right hchiMem.2 heMem.1.le).trans_lt
        (by simpa using heMem.2)
    exact sub_pos.mpr hprod
  have hnum := (hasDerivAt_const z 1).sub he
  have hradRaw := hnum.div hx hxPos.ne'
  have hrad : HasDerivAt
      (fun q ↦ lrCertificateVRadicand (lrCertificateCurve s k chi q))
      (lrCertificateVRadicandDeriv point e' x') z := by
    unfold lrCertificateVRadicand lrCertificateVRadicandDeriv
    convert hradRaw using 1 <;>
      simp only [Pi.sub_apply] <;>
      dsimp [point, e', x', lrCertificateCurve, lrCertificateE,
        lrCertificateX] <;> ring
  have hradPos : 0 < lrCertificateVRadicand point :=
    div_pos (sub_pos.mpr heMem.2) hxPos
  have hsqrt := (Real.hasDerivAt_sqrt hradPos.ne').comp z hrad
  have hsqrtEq : Real.sqrt (lrCertificateVRadicand point) =
      lrCertificateV point := by rfl
  unfold lrCertificateV lrCertificateVDeriv
  convert hsqrt using 1
  rw [hsqrtEq]
  dsimp [point, e', x']
  field_simp

theorem lrCertificateV_pos_of_centeredInterior {point : CertificatePoint}
    (hinterior : LRFiniteDeterminantD9CenteredInterior point) :
    0 < lrCertificateV point := by
  have hxPos : 0 < lrCertificateX point := by
    unfold lrCertificateX
    have hprod : point.chi * lrCertificateE point < 1 :=
      (mul_le_mul_of_nonneg_right hinterior.2.2.2 hinterior.2.1.1.le).trans_lt
        (by simpa using hinterior.2.1.2)
    exact sub_pos.mpr hprod
  unfold lrCertificateV
  exact Real.sqrt_pos.2 (div_pos (sub_pos.mpr hinterior.2.1.2) hxPos)

/-! ## Analytic identification of those derivatives -/

set_option maxHeartbeats 800000 in
theorem hasDerivAt_lrFiniteDeterminantD9ReplayTarget_curve
    {z s' k' chi' : ℝ} {sfun kfun chifun : ℝ → ℝ}
    (hs : HasDerivAt sfun s' z) (hk : HasDerivAt kfun k' z)
    (hchi : HasDerivAt chifun chi' z)
    (hinterior : LRFiniteDeterminantD9CenteredInterior
      (lrCertificateCurve sfun kfun chifun z)) :
    HasDerivAt
      (fun q ↦ lrFiniteDeterminantD9ReplayTarget
        (lrCertificateCurve sfun kfun chifun q))
      (lrFiniteDeterminantD9RawDeriv
        (lrCertificateCurve sfun kfun chifun z) s' k' chi') z := by
  let point := lrCertificateCurve sfun kfun chifun z
  let e' := s' * point.k + point.s * k'
  let y0' := chi' * lrCertificateE point + point.chi * e'
  let x' := -(chi' * lrCertificateE point + point.chi * e')
  let v' := lrCertificateVDeriv point e' x'
  have heRaw := hasDerivAt_lrCertificateE_curve (chi := chifun) hs hk
  have he : HasDerivAt
      (fun q ↦ lrCertificateE (lrCertificateCurve sfun kfun chifun q))
      e' z := by
    simpa [point, e', lrCertificateCurve] using heRaw
  have hxRaw := hasDerivAt_lrCertificateX_curve hs hk hchi
  have hx : HasDerivAt
      (fun q ↦ lrCertificateX (lrCertificateCurve sfun kfun chifun q))
      x' z := by
    simpa [point, e', x', lrCertificateCurve] using hxRaw
  have hvRaw := hasDerivAt_lrCertificateV_curve_Ioc hs hk hchi
    hinterior.2.1 hinterior.2.2
  have hv : HasDerivAt
      (fun q ↦ lrCertificateV (lrCertificateCurve sfun kfun chifun q))
      v' z := by
    simpa [point, e', x', v'] using hvRaw
  have hy0Raw := hchi.mul he
  have hy0 : HasDerivAt
      (fun q ↦ lrCertificateY0
        (lrCertificateCurve sfun kfun chifun q)) y0' z := by
    simpa [lrCertificateY0, point, e', y0', lrCertificateCurve] using
      hy0Raw
  have hy0Mem : lrCertificateY0 point ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · exact mul_pos hinterior.2.2.1 hinterior.2.1.1
    · exact
        (mul_le_mul_of_nonneg_right hinterior.2.2.2
          hinterior.2.1.1.le).trans_lt (by simpa using hinterior.2.1.2)
  have hvPos : 0 < lrCertificateV point :=
    lrCertificateV_pos_of_centeredInterior hinterior
  have hgRaw := hasDerivAt_lrCertificateGShapeValue_along
    hy0 he hv hy0Mem hinterior.2.1 hvPos
  have hg : HasDerivAt
      (fun q ↦ lrCertificateGShape
        (lrCertificateCurve sfun kfun chifun q))
      (lrCertificateGShapeDeriv point y0' e' v') z := by
    simpa [lrCertificateGShape, lrCertificateGShapeDeriv, point] using hgRaw
  have hpwRaw := hasDerivAt_lrCertificatePWValue_along
    hs hy0 he hv hinterior.1 hy0Mem hinterior.2.1 hvPos
  have hpw : HasDerivAt
      (fun q ↦ lrCertificatePW
        (lrCertificateCurve sfun kfun chifun q))
      (lrCertificatePWDeriv point s' y0' e' v') z := by
    simpa [lrCertificatePW, lrCertificatePWDeriv, point] using hpwRaw
  have hwRaw := hasDerivAt_lrCertificateOmega_zero_along
    hs rfl hinterior.1
  have hw : HasDerivAt
      (fun q ↦ lrCertificateW
        (lrCertificateCurve sfun kfun chifun q))
      (lrCertificateOmegaDeriv point.s 0 s' 0) z := by
    simpa [lrCertificateW, point, lrCertificateCurve] using hwRaw
  have hbRaw := hasDerivAt_lrCertificateBFlowValue_along
    hs he hv hinterior.1 hinterior.2.1 hvPos
  have hb : HasDerivAt
      (fun q ↦ lrCertificateBFlow
        (lrCertificateCurve sfun kfun chifun q))
      (lrCertificateBFlowDeriv point s' e' v') z := by
    simpa [lrCertificateBFlow, lrCertificateBFlowDeriv, point] using hbRaw

  have hbY := hasDerivAt_lrCertificateB_along hs he rfl rfl
  have hYRaw := hbY.div he hinterior.2.1.1.ne'
  have hY : HasDerivAt
      (fun q ↦ lrDeterminantY
        (lrCertificateCurve sfun kfun chifun q))
      (lrFiniteDeterminantD9YDeriv point s' e') z := by
    simpa [lrDeterminantY, lrFiniteDeterminantD9YDeriv, point] using hYRaw
  have hYOne : 1 ≤ lrDeterminantY point := by
    unfold lrDeterminantY
    rw [one_le_div₀ hinterior.2.1.1]
    unfold lrCertificateB
    nlinarith [mul_nonneg (sub_nonneg.mpr hinterior.1.2.le)
      hinterior.2.1.1.le,
      mul_nonneg hinterior.1.1.le (sub_nonneg.mpr hinterior.2.1.2.le)]
  have hmeanPos : 0 < (1 + lrDeterminantY point) / 2 := by linarith
  have hthreePos : 0 < 3 * lrDeterminantY point + 1 := by linarith
  have hmean := ((hasDerivAt_const z 1).add hY).div_const 2
  have hlogMean := (Real.hasDerivAt_log hmeanPos.ne').comp z hmean
  have hhalfLog := (hasDerivAt_const z (1 / 2 : ℝ)).mul hlogMean
  have hYMinus := hY.sub_const 1
  have hthree := (hY.mul_const 3).add_const 1
  have hthreeNe : lrDeterminantY point * 3 + 1 ≠ 0 := by linarith
  have hfrac := hYMinus.div hthree hthreeNe
  have hd1Raw := hhalfLog.add hfrac
  have hd1 : HasDerivAt
      (fun q ↦ lrDeterminantD1
        (lrCertificateCurve sfun kfun chifun q))
      (lrFiniteDeterminantD9D1Deriv point s' e') z := by
    unfold lrDeterminantD1 lrFiniteDeterminantD9D1Deriv
    dsimp only
    convert hd1Raw using 1
    · funext q
      simp only [Pi.add_apply, Pi.mul_apply, Pi.div_apply,
        Function.comp_apply]
      ring_nf
    · simp [point]
      field_simp [hmeanPos.ne', hthreePos.ne']

  have honePlusV := (hasDerivAt_const z 1).add hv
  have honePlusVNe : 1 + lrCertificateV point ≠ 0 := by
    linarith
  have hfourWOver := (hw.mul_const 4).div honePlusV honePlusVNe
  have hpsiRaw := (hg.add hpw).sub hfourWOver
  have hpsi : HasDerivAt
      (fun q ↦ lrDeterminantPsi
        (lrCertificateCurve sfun kfun chifun q))
      (lrFiniteDeterminantD9PsiDeriv point s' y0' e' v') z := by
    unfold lrDeterminantPsi lrFiniteDeterminantD9PsiDeriv
    dsimp only
    convert hpsiRaw using 1
    · funext q
      simp only [Pi.add_apply, Pi.sub_apply, Pi.div_apply]
      ring_nf
    · dsimp [point]
      field_simp [honePlusVNe]
      ring
  have hdeltaRaw := ((hasDerivAt_const z 1).sub (hv.mul hx)).div
    honePlusV honePlusVNe
  have hdelta : HasDerivAt
      (fun q ↦ lrDeterminantDelta
        (lrCertificateCurve sfun kfun chifun q))
      (lrFiniteDeterminantD9DeltaDeriv point x' v') z := by
    unfold lrDeterminantDelta lrFiniteDeterminantD9DeltaDeriv
    convert hdeltaRaw using 1 <;> simp [point]
  have hinner := (hpsi.sub hg).add ((hdelta.mul hw).mul_const 4)
  have hfirstRaw := (hb.mul hinner).add (hd1.mul hpsi)
  have hfirst : HasDerivAt
      (fun q ↦ lrDeterminantFirstBracket
        (lrCertificateBFlow (lrCertificateCurve sfun kfun chifun q))
        (lrDeterminantD1 (lrCertificateCurve sfun kfun chifun q))
        (lrCertificateGShape (lrCertificateCurve sfun kfun chifun q))
        (lrDeterminantPsi (lrCertificateCurve sfun kfun chifun q))
        (lrDeterminantDelta (lrCertificateCurve sfun kfun chifun q))
        (lrCertificateW (lrCertificateCurve sfun kfun chifun q)))
      (lrFiniteDeterminantD9FirstBracketDeriv
        point s' y0' e' x' v') z := by
    unfold lrDeterminantFirstBracket
      lrFiniteDeterminantD9FirstBracketDeriv
    dsimp only
    convert hfirstRaw using 1
    · funext q
      simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply]
      ring_nf
    · simp [point]
      ring

  have hSquareRaw := hasDerivAt_lrCertificateSquareTarget_along
    hs hy0 he hv hinterior.1 hy0Mem hinterior.2.1 hvPos
  have hSquare : HasDerivAt
      (fun q ↦ lrCertificateSquareTarget
        (lrCertificateCurve sfun kfun chifun q))
      (lrCertificateSquareTargetDeriv point s' y0' e' v') z := by
    simpa [lrCertificateSquareTarget, point, lrCertificateCurve] using
      hSquareRaw
  have hPrefixRaw := hasDerivAt_lrCertificatePrefixAtM_along
    hs hv hinterior.1 hvPos
  have hPrefix : HasDerivAt
      (fun q ↦ lrCertificatePrefixAtM
        (lrCertificateCurve sfun kfun chifun q))
      (lrCertificatePrefixAtMDeriv point s' v') z := by
    simpa [lrCertificatePrefixAtM, lrCertificatePrefixAtMDeriv,
      point, lrCertificateCurve] using hPrefixRaw
  have hGapRaw := hSquare.sub hPrefix
  have hGap : HasDerivAt
      (fun q ↦ lrCertificateGap
        (lrCertificateCurve sfun kfun chifun q))
      (lrCertificateGapDeriv point s' y0' e' v') z := by
    simpa [lrCertificateGap, lrCertificateGapDeriv] using hGapRaw
  have hHalfRaw := hasDerivAt_lrCertificateHalfSlope_along
    hs hv hinterior.1 hvPos
  have hHalf : HasDerivAt
      (fun q ↦ lrCertificateHalfSlope
        (lrCertificateCurve sfun kfun chifun q))
      (lrCertificateHalfSlopeDeriv point s' v') z := by
    simpa [lrCertificateHalfSlope, point, lrCertificateCurve] using hHalfRaw
  have hfactorRaw := (hb.mul hx).sub hd1
  have hfactor : HasDerivAt
      (fun q ↦
        lrCertificateBFlow (lrCertificateCurve sfun kfun chifun q) *
          lrCertificateX (lrCertificateCurve sfun kfun chifun q) -
        lrDeterminantD1 (lrCertificateCurve sfun kfun chifun q))
      (lrFiniteDeterminantD9FactorDeriv point s' e' x' v') z := by
    unfold lrFiniteDeterminantD9FactorDeriv
    convert hfactorRaw using 1 <;> simp [point] <;> ring
  have hleading := ((hasDerivAt_const z 3).mul hHalf).mul hfirst
  have hcorrection :=
    (((hasDerivAt_const z 4).mul hw).mul hGap).mul hfactor
  have hcancelRaw := hleading.add hcorrection
  have hcancel : HasDerivAt
      (fun q ↦
        3 * lrCertificateHalfSlope
              (lrCertificateCurve sfun kfun chifun q) *
            lrDeterminantFirstBracket
              (lrCertificateBFlow
                (lrCertificateCurve sfun kfun chifun q))
              (lrDeterminantD1
                (lrCertificateCurve sfun kfun chifun q))
              (lrCertificateGShape
                (lrCertificateCurve sfun kfun chifun q))
              (lrDeterminantPsi
                (lrCertificateCurve sfun kfun chifun q))
              (lrDeterminantDelta
                (lrCertificateCurve sfun kfun chifun q))
              (lrCertificateW
                (lrCertificateCurve sfun kfun chifun q)) +
          4 * lrCertificateW (lrCertificateCurve sfun kfun chifun q) *
            lrCertificateGap (lrCertificateCurve sfun kfun chifun q) *
            (lrCertificateBFlow
                (lrCertificateCurve sfun kfun chifun q) *
              lrCertificateX (lrCertificateCurve sfun kfun chifun q) -
              lrDeterminantD1
                (lrCertificateCurve sfun kfun chifun q)))
      (lrFiniteDeterminantD9RawDeriv point s' k' chi') z := by
    unfold lrFiniteDeterminantD9RawDeriv
      lrFiniteDeterminantD9CoordinateDeriv
    dsimp only
    convert hcancelRaw using 1 <;>
      dsimp [point, e', y0', x', v'] <;> ring
  apply hcancel.congr_of_eventuallyEq
  have hsPosEventually : ∀ᶠ q in nhds z, 0 < sfun q :=
    hs.continuousAt.eventually_const_lt hinterior.1.1
  have hsLtEventually : ∀ᶠ q in nhds z, sfun q < 1 :=
    hs.continuousAt.eventually_lt_const hinterior.1.2
  filter_upwards [hsPosEventually, hsLtEventually] with q hsqPos hsqLt
  unfold lrFiniteDeterminantD9ReplayTarget lrDeterminantHd lrDeterminantT
    lrCertificateR
  dsimp [lrCertificateCurve]
  field_simp [hsqPos.ne', (sub_pos.mpr hsqLt).ne']

theorem hasDerivAt_lrFiniteDeterminantD9ReplayTarget_s
    {point : CertificatePoint}
    (hinterior : LRFiniteDeterminantD9CenteredInterior point) :
    HasDerivAt
      (fun s ↦ lrFiniteDeterminantD9ReplayTarget { point with s := s })
      (lrFiniteDeterminantD9DerivS point) point.s := by
  have h := hasDerivAt_lrFiniteDeterminantD9ReplayTarget_curve
    (sfun := fun s ↦ s) (kfun := fun _ ↦ point.k)
    (chifun := fun _ ↦ point.chi)
    (hasDerivAt_id point.s) (hasDerivAt_const point.s point.k)
    (hasDerivAt_const point.s point.chi) hinterior
  simpa [lrFiniteDeterminantD9DerivS, lrCertificateCurve] using h

theorem hasDerivAt_lrFiniteDeterminantD9ReplayTarget_k
    {point : CertificatePoint}
    (hinterior : LRFiniteDeterminantD9CenteredInterior point) :
    HasDerivAt
      (fun k ↦ lrFiniteDeterminantD9ReplayTarget { point with k := k })
      (lrFiniteDeterminantD9DerivK point) point.k := by
  have h := hasDerivAt_lrFiniteDeterminantD9ReplayTarget_curve
    (sfun := fun _ ↦ point.s) (kfun := fun k ↦ k)
    (chifun := fun _ ↦ point.chi)
    (hasDerivAt_const point.k point.s) (hasDerivAt_id point.k)
    (hasDerivAt_const point.k point.chi) hinterior
  simpa [lrFiniteDeterminantD9DerivK, lrCertificateCurve] using h

theorem hasDerivAt_lrFiniteDeterminantD9ReplayTarget_chi
    {point : CertificatePoint}
    (hinterior : LRFiniteDeterminantD9CenteredInterior point) :
    HasDerivAt
      (fun chi ↦ lrFiniteDeterminantD9ReplayTarget
        { point with chi := chi })
      (lrFiniteDeterminantD9DerivChi point) point.chi := by
  have h := hasDerivAt_lrFiniteDeterminantD9ReplayTarget_curve
    (sfun := fun _ ↦ point.s) (kfun := fun _ ↦ point.k)
    (chifun := fun chi ↦ chi)
    (hasDerivAt_const point.chi point.s)
    (hasDerivAt_const point.chi point.k) (hasDerivAt_id point.chi)
    hinterior
  simpa [lrFiniteDeterminantD9DerivChi, lrCertificateCurve] using h

/-! ## Full interval-AD soundness for the existing D9 arithmetic -/

namespace LRFiniteDeterminantD9Certificate

theorem yAD_sound
    {box : CertificateBox} {point : CertificatePoint}
    (hpoint : box.Contains point)
    (hsLower : (0 : ℚ) < (lrCertificateSAD box).value.lower)
    (hkLower : (0 : ℚ) < (lrCertificateKAD box).value.lower) :
    (yAD box).Contains (lrDeterminantY point)
      (lrFiniteDeterminantD9YDeriv point 1
        (lrCertificateEDerivS point))
      (lrFiniteDeterminantD9YDeriv point 0
        (lrCertificateEDerivK point))
      (lrFiniteDeterminantD9YDeriv point 0
        (lrCertificateEDerivChi point)) := by
  have hs := IntervalAD.contains_variableS
    (show box.sInterval.Contains point.s from ⟨hpoint.1, hpoint.2.1⟩)
  have hk := IntervalAD.contains_variableK
    (show box.kInterval.Contains point.k from
      ⟨hpoint.2.2.1, hpoint.2.2.2.1⟩)
  have he := lrCertificateEAD_sound hpoint
  have hnum := IntervalAD.contains_sub
    (IntervalAD.contains_add (IntervalAD.contains_const 1) hk) he
  have hy := IntervalAD.contains_divPositive hkLower hnum hk
  have hsLowerReal : (0 : ℝ) <
      ((lrCertificateSAD box).value.lower : ℝ) := by
    exact_mod_cast hsLower
  have hkLowerReal : (0 : ℝ) <
      ((lrCertificateKAD box).value.lower : ℝ) := by
    exact_mod_cast hkLower
  have hsPos : 0 < point.s := hsLowerReal.trans_le hs.1.1
  have hkPos : 0 < point.k := hkLowerReal.trans_le hk.1.1
  unfold yAD
  dsimp only
  convert hy using 1 <;>
    simp [lrDeterminantY, lrFiniteDeterminantD9YDeriv,
      lrCertificateBDeriv, lrCertificateB, lrCertificateE,
      lrCertificateEDerivS, lrCertificateEDerivK,
      lrCertificateEDerivChi] <;>
    field_simp [hsPos.ne', hkPos.ne'] <;> ring

theorem d1AD_sound
    (terms : ℕ) {box : CertificateBox} {point : CertificatePoint}
    {certificate : LRFiniteDeterminantD9Certificate}
    (hpoint : box.Contains point)
    (hsLower : (0 : ℚ) < (lrCertificateSAD box).value.lower)
    (hkLower : (0 : ℚ) < (lrCertificateKAD box).value.lower)
    (hlog : certificate.logD1Mean.check (d1MeanAD box).value = true)
    (hden : (0 : ℚ) < (d1DenominatorAD box).value.lower) :
    (certificate.d1AD terms box).Contains (lrDeterminantD1 point)
      (lrFiniteDeterminantD9D1Deriv point 1
        (lrCertificateEDerivS point))
      (lrFiniteDeterminantD9D1Deriv point 0
        (lrCertificateEDerivK point))
      (lrFiniteDeterminantD9D1Deriv point 0
        (lrCertificateEDerivChi point)) := by
  have hy := yAD_sound hpoint hsLower hkLower
  have hmean := IntervalAD.contains_mul
    (IntervalAD.contains_add (IntervalAD.contains_const 1) hy)
    (IntervalAD.contains_const (1 / 2))
  have hlogMean := IntervalAD.contains_log terms hlog hmean
  have hdenominator := IntervalAD.contains_add
    (IntervalAD.contains_mul (IntervalAD.contains_const 3) hy)
    (IntervalAD.contains_const 1)
  have hfraction := IntervalAD.contains_divPositive hden
    (IntervalAD.contains_sub hy (IntervalAD.contains_const 1))
    hdenominator
  have hd1 := IntervalAD.contains_add
    (IntervalAD.contains_mul (IntervalAD.contains_const (1 / 2)) hlogMean)
    hfraction
  have hlogParts :
      (0 : ℚ) < (d1MeanAD box).value.lower ∧
      certificate.logD1Mean.lower.check
        (d1MeanAD box).value.lower = true ∧
      certificate.logD1Mean.upper.check
        (d1MeanAD box).value.upper = true := by
    simpa [RationalEnclosure.LogIntervalCertificate.check] using hlog
  have hmeanLowerReal : (0 : ℝ) <
      ((d1MeanAD box).value.lower : ℝ) := by
    exact_mod_cast hlogParts.1
  have hmeanPointPos : 0 < (1 + lrDeterminantY point) / 2 := by
    have hcontained := hmean.1
    have hlower : ((d1MeanAD box).value.lower : ℝ) ≤
        (1 + lrDeterminantY point) / 2 := by
      simpa [d1MeanAD] using hcontained.1
    exact hmeanLowerReal.trans_le hlower
  have hdenLowerReal : (0 : ℝ) <
      ((d1DenominatorAD box).value.lower : ℝ) := by
    exact_mod_cast hden
  have hdenPointPos : 0 < 3 * lrDeterminantY point + 1 := by
    have hcontained := hdenominator.1
    have hlower : ((d1DenominatorAD box).value.lower : ℝ) ≤
        3 * lrDeterminantY point + 1 := by
      simpa [d1DenominatorAD] using hcontained.1
    exact hdenLowerReal.trans_le hlower
  unfold d1AD d1MeanAD d1DenominatorAD
    lrFiniteDeterminantD9D1Deriv lrDeterminantD1
  dsimp only
  convert hd1 using 1 <;>
    field_simp [hmeanPointPos.ne', hdenPointPos.ne'] <;> ring

set_option maxHeartbeats 800000 in
theorem evaluateAD_sound
    (terms : ℕ) {box : CertificateBox} {point : CertificatePoint}
    {certificate : LRFiniteDeterminantD9Certificate}
    (hpoint : box.Contains point)
    (hcheck : certificate.payloadCheck box = true) :
    (certificate.evaluateAD terms box).Contains
      (lrFiniteDeterminantD9ReplayTarget point)
      (lrFiniteDeterminantD9DerivS point)
      (lrFiniteDeterminantD9DerivK point)
      (lrFiniteDeterminantD9DerivChi point) := by
  have hparts :
      certificate.tangent.check box = true ∧
      (0 : ℚ) < (lrCertificateSAD box).value.lower ∧
      (0 : ℚ) < (lrCertificateKAD box).value.lower ∧
      (0 : ℚ) < (lrCertificateRAD box).value.lower ∧
      certificate.logD1Mean.check (d1MeanAD box).value = true ∧
      (0 : ℚ) < (d1DenominatorAD box).value.lower ∧
      (0 : ℚ) < (onePlusVAD box certificate).value.lower := by
    simpa [payloadCheck] using hcheck
  have htangentParts :
      certificate.tangent.base.check box = true ∧
      certificate.tangent.qBY0.check
        (lrCertificateBAD (lrCertificateSAD box)
          (lrCertificateY0AD box)).value = true ∧
      certificate.tangent.qBE.check
        (lrCertificateBAD (lrCertificateSAD box)
          (lrCertificateEAD box)).value = true ∧
      certificate.tangent.qS.check (lrCertificateSAD box).value = true ∧
      certificate.tangent.logTwoPlusV.check
        (IntervalAD.add (IntervalAD.const 2)
          (certificate.tangent.base.kernel.coordinate.vAD box)).value = true ∧
      (0 : ℚ) <
        (certificate.tangent.base.kernel.coordinate.vAD box).value.lower ∧
      (0 : ℚ) < (onePlusVAD box certificate).value.lower ∧
      (0 : ℚ) <
        (IntervalAD.add (IntervalAD.const 2)
          (certificate.tangent.base.kernel.coordinate.vAD box)).value.lower ∧
      (0 : ℚ) <
        (IntervalAD.mul
          (certificate.tangent.base.kernel.coordinate.vAD box)
          (certificate.tangent.base.kernel.coordinate.vAD box)).value.lower := by
    simpa [LRHighShapeTangentCertificate.check, onePlusVAD] using hparts.1
  have hbaseParts :
      certificate.tangent.base.kernel.check box = true ∧
      certificate.tangent.base.gShape.check box
        certificate.tangent.base.kernel.coordinate = true ∧
      certificate.tangent.base.ab.check box
        certificate.tangent.base.kernel.coordinate = true ∧
      (0 : ℚ) < (onePlusVAD box certificate).value.lower ∧
      (0 : ℚ) <
        (LRHighShapeMidpointCertificate.denominatorAD box).value.lower := by
    simpa [LRHighShapeMidpointCertificate.check, onePlusVAD]
      using htangentParts.1
  have hkernelParts :
      certificate.tangent.base.kernel.coordinate.check box = true ∧
      certificate.tangent.base.kernel.omegaZero.check
        (lrCertificateSAD box) = true ∧
      certificate.tangent.base.kernel.omegaY0.check
        (lrCertificateSAD box) (lrCertificateY0AD box) = true ∧
      certificate.tangent.base.kernel.omegaE.check
        (lrCertificateSAD box) (lrCertificateEAD box) = true ∧
      (0 : ℚ) <
        (certificate.tangent.base.kernel.coordinate.vAD box).value.lower := by
    simpa [LRHighShapeKernelCertificate.check] using hbaseParts.1

  have hs := IntervalAD.contains_variableS
    (show box.sInterval.Contains point.s from ⟨hpoint.1, hpoint.2.1⟩)
  have hR := lrCertificateRAD_sound hpoint
  have hx := lrCertificateXAD_sound hpoint
  have hv := certificate.tangent.base.kernel.coordinate.vAD_sound
    hpoint hkernelParts.1
  have hab := certificate.tangent.base.ab.sound terms hpoint
    hbaseParts.2.2.1
  have hg := certificate.tangent.base.gShape.sound terms hpoint
    hbaseParts.2.1
  have hw := certificate.tangent.base.kernel.wAD_sound terms hpoint
    hbaseParts.1
  have hpw := certificate.tangent.base.kernel.pwAD_sound terms hpoint
    hbaseParts.1
  have htangent := certificate.tangent.evaluateAll_sound terms hpoint hparts.1
  have hd1 := certificate.d1AD_sound terms hpoint
    hparts.2.1 hparts.2.2.1 hparts.2.2.2.2.1
    hparts.2.2.2.2.2.1

  have honePlusV := IntervalAD.contains_add
    (IntervalAD.contains_const 1) hv
  have hpsi := IntervalAD.contains_sub
    (IntervalAD.contains_add hg hpw)
    (IntervalAD.contains_divPositive hparts.2.2.2.2.2.2
      (IntervalAD.contains_mul (IntervalAD.contains_const 4) hw)
      honePlusV)
  have hdelta := IntervalAD.contains_divPositive hparts.2.2.2.2.2.2
    (IntervalAD.contains_sub (IntervalAD.contains_const 1)
      (IntervalAD.contains_mul hv hx)) honePlusV
  have hfourDeltaW := IntervalAD.contains_mul
    (IntervalAD.contains_mul (IntervalAD.contains_const 4) hdelta) hw
  have hbase := IntervalAD.contains_add
    (IntervalAD.contains_sub hpsi hg) hfourDeltaW
  have hfirst := IntervalAD.contains_add
    (IntervalAD.contains_mul hab.2.1 hbase)
    (IntervalAD.contains_mul hd1 hpsi)
  have hfactor := IntervalAD.contains_sub
    (IntervalAD.contains_mul hab.2.1 hx) hd1
  have hleading := IntervalAD.contains_mul
    (IntervalAD.contains_mul
      (IntervalAD.contains_const 3) htangent.halfSlope) hfirst
  have hcorrection := IntervalAD.contains_mul
    (IntervalAD.contains_mul
      (IntervalAD.contains_mul
        (IntervalAD.contains_const 4) hw) htangent.gap) hfactor
  have htarget := IntervalAD.contains_add hleading hcorrection

  have honePlusLowerReal : (0 : ℝ) <
      ((onePlusVAD box certificate).value.lower : ℝ) := by
    exact_mod_cast hparts.2.2.2.2.2.2
  have honePlusPointPos : 0 < 1 + lrCertificateV point := by
    simpa [onePlusVAD] using honePlusLowerReal.trans_le honePlusV.1.1
  have honePlusPointNe : 1 + lrCertificateV point ≠ 0 :=
    honePlusPointPos.ne'

  have hcancel : (certificate.evaluateAD terms box).Contains
      (3 * lrCertificateHalfSlope point *
          lrDeterminantFirstBracket
            (lrCertificateBFlow point) (lrDeterminantD1 point)
            (lrCertificateGShape point) (lrDeterminantPsi point)
            (lrDeterminantDelta point) (lrCertificateW point) +
        4 * lrCertificateW point * lrCertificateGap point *
          (lrCertificateBFlow point * lrCertificateX point -
            lrDeterminantD1 point))
      (lrFiniteDeterminantD9DerivS point)
      (lrFiniteDeterminantD9DerivK point)
      (lrFiniteDeterminantD9DerivChi point) := by
    unfold evaluateAD firstBracketAD psiAD deltaAD onePlusVAD
    dsimp only
    convert htarget using 1 <;>
      simp [lrFiniteDeterminantD9DerivS,
        lrFiniteDeterminantD9DerivK,
        lrFiniteDeterminantD9DerivChi,
        lrFiniteDeterminantD9RawDeriv,
        lrFiniteDeterminantD9CoordinateDeriv,
        lrFiniteDeterminantD9FirstBracketDeriv,
        lrFiniteDeterminantD9FactorDeriv,
        lrFiniteDeterminantD9PsiDeriv,
        lrFiniteDeterminantD9DeltaDeriv,
        lrDeterminantFirstBracket, lrDeterminantPsi,
        lrDeterminantDelta,
        lrCertificateGShapeDerivS, lrCertificateGShapeDerivK,
        lrCertificateGShapeDerivChi,
        lrCertificatePWDerivS, lrCertificatePWDerivK,
        lrCertificatePWDerivChi,
        lrCertificateWDerivS, lrCertificateWDerivK,
        lrCertificateWDerivChi,
        lrCertificateY0DerivS, lrCertificateY0DerivK,
        lrCertificateY0DerivChi,
        lrCertificateVDerivS, lrCertificateVDerivK,
        lrCertificateVDerivChi,
        lrCertificateEDerivS, lrCertificateEDerivK,
        lrCertificateEDerivChi,
        lrCertificateXDerivS, lrCertificateXDerivK,
        lrCertificateXDerivChi] <;>
      field_simp [honePlusPointNe] <;> ring

  have hsLowerReal : (0 : ℝ) <
      ((lrCertificateSAD box).value.lower : ℝ) := by
    exact_mod_cast hparts.2.1
  have hRLowerReal : (0 : ℝ) <
      ((lrCertificateRAD box).value.lower : ℝ) := by
    exact_mod_cast hparts.2.2.2.1
  have hsPos : 0 < point.s := hsLowerReal.trans_le hs.1.1
  have hRPos : 0 < lrCertificateR point := hRLowerReal.trans_le hR.1.1
  have htargetEq :
      lrFiniteDeterminantD9ReplayTarget point =
        3 * lrCertificateHalfSlope point *
            lrDeterminantFirstBracket
              (lrCertificateBFlow point) (lrDeterminantD1 point)
              (lrCertificateGShape point) (lrDeterminantPsi point)
              (lrDeterminantDelta point) (lrCertificateW point) +
          4 * lrCertificateW point * lrCertificateGap point *
            (lrCertificateBFlow point * lrCertificateX point -
              lrDeterminantD1 point) := by
    unfold lrFiniteDeterminantD9ReplayTarget lrDeterminantHd lrDeterminantT
    field_simp [hsPos.ne', hRPos.ne']
  rw [htargetEq]
  exact hcancel

end LRFiniteDeterminantD9Certificate

/-! ## Paired singleton-value / whole-box-derivative payload -/

structure LRFiniteDeterminantD9CenteredCertificate where
  center : LRFiniteDeterminantD9Certificate
  derivative : LRFiniteDeterminantD9Certificate

namespace LRFiniteDeterminantD9CenteredCertificate

def auto (sqrtFuel logFuel : ℕ) (box : CertificateBox)
    (derivative : LRFiniteDeterminantD9Certificate :=
      LRFiniteDeterminantD9Certificate.auto sqrtFuel logFuel box) :
    LRFiniteDeterminantD9CenteredCertificate :=
  { center := LRFiniteDeterminantD9Certificate.auto
      sqrtFuel logFuel box.centerBox
    derivative := derivative }

def payloadCheck (box : CertificateBox)
    (certificate : LRFiniteDeterminantD9CenteredCertificate) : Bool :=
  lrFiniteDeterminantD9CenteredBoxCheck box &&
    certificate.center.payloadCheck box.centerBox &&
    certificate.derivative.payloadCheck box

/-- Midpoint data whose value comes from the singleton center evaluation and
whose derivative fields come from an independent whole-box evaluation. -/
def evaluate (terms : ℕ) (box : CertificateBox)
    (certificate : LRFiniteDeterminantD9CenteredCertificate) :
    MidpointCertificate :=
  let centerResult := certificate.center.evaluateAD terms box.centerBox
  let derivativeResult := certificate.derivative.evaluateAD terms box
  { value := centerResult.value
    derivS := derivativeResult.derivS
    derivK := derivativeResult.derivK
    derivChi := derivativeResult.derivChi }

/-- Executable accepted-leaf predicate for an explicit centered payload. -/
def accepts (terms : ℕ) (box : CertificateBox)
    (certificate : LRFiniteDeterminantD9CenteredCertificate) : Bool :=
  checkedMidpointLeafAccepts payloadCheck (evaluate terms) box certificate

/-- Payload-free deterministic accepted-leaf predicate, suitable for a raw
tree whose accepted nodes carry `Unit`. -/
def autoAccepts (terms sqrtFuel logFuel : ℕ)
    (box : CertificateBox) (_unit : Unit) : Bool :=
  accepts terms box (auto sqrtFuel logFuel box)

noncomputable def derivativeEnclosures (terms : ℕ)
    {box : CertificateBox}
    {certificate : LRFiniteDeterminantD9CenteredCertificate}
    (hcheck : certificate.derivative.payloadCheck box = true)
    (hinterior : ∀ point, box.Contains point →
      LRFiniteDeterminantD9CenteredInterior point) :
    BoxDerivativeEnclosures lrFiniteDeterminantD9ReplayTarget box
      (certificate.evaluate terms box) := by
  refine
    { partialS := lrFiniteDeterminantD9DerivS
      partialK := lrFiniteDeterminantD9DerivK
      partialChi := lrFiniteDeterminantD9DerivChi
      derivS := ?_
      derivK := ?_
      derivChi := ?_
      boundS := ?_
      boundK := ?_
      boundChi := ?_ }
  · intro point hpoint
    exact hasDerivAt_lrFiniteDeterminantD9ReplayTarget_s
      (hinterior point hpoint)
  · intro point hpoint
    exact hasDerivAt_lrFiniteDeterminantD9ReplayTarget_k
      (hinterior point hpoint)
  · intro point hpoint
    exact hasDerivAt_lrFiniteDeterminantD9ReplayTarget_chi
      (hinterior point hpoint)
  · intro point hpoint
    have h := certificate.derivative.evaluateAD_sound terms hpoint hcheck
    simpa [evaluate] using h.2.1
  · intro point hpoint
    have h := certificate.derivative.evaluateAD_sound terms hpoint hcheck
    simpa [evaluate] using h.2.2.1
  · intro point hpoint
    have h := certificate.derivative.evaluateAD_sound terms hpoint hcheck
    simpa [evaluate] using h.2.2.2

/-- Kernel-checked semantic contract consumed by the generic midpoint leaf
checker. -/
noncomputable def checkedEvaluatorSound (terms : ℕ) :
    CheckedMidpointLeafEvaluatorSound lrFiniteDeterminantD9ReplayTarget
      payloadCheck (evaluate terms) := by
  constructor
  · intro box certificate hpayload
    have hparts :
        (lrFiniteDeterminantD9CenteredBoxCheck box = true ∧
          certificate.center.payloadCheck box.centerBox = true) ∧
        certificate.derivative.payloadCheck box = true := by
      simpa [payloadCheck] using hpayload
    have hcenter := certificate.center.evaluateAD_sound terms
      box.centerBox_contains_midpoint hparts.1.2
    simpa [evaluate] using hcenter.1
  · intro box certificate hpayload
    have hparts :
        (lrFiniteDeterminantD9CenteredBoxCheck box = true ∧
          certificate.center.payloadCheck box.centerBox = true) ∧
        certificate.derivative.payloadCheck box = true := by
      simpa [payloadCheck] using hpayload
    exact certificate.derivativeEnclosures terms hparts.2
      (fun _point hpoint ↦
        lrFiniteDeterminantD9CenteredBoxCheck_sound hparts.1.1 hpoint)

end LRFiniteDeterminantD9CenteredCertificate

end CourtadeKumar
