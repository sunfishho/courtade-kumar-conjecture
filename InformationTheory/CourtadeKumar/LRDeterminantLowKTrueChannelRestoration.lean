import InformationTheory.CourtadeKumar.LRDeterminantLowKFiniteRestoration
import InformationTheory.CourtadeKumar.LRSmallSBridgeIdentification

/-!
# The true-channel stage of the determinant low-`k` restoration

This file introduces the exact `Q = q` channel coordinates from the audited
DA7 proof and proves the sign-safe algebra which turns its four channel
payments into the `55763 / 819200` channel budget.  The `Delta G` and
`Delta Omega` payments are discharged here.  The strongest public constructor
therefore asks for exactly two remaining pointwise inputs: the scaled
`Delta T` payment and the compensation-coefficient payment.  Both are stated
in the audited true-channel coordinates, so neither can be replaced by an
unrelated witness.
-/

open Set

namespace CourtadeKumar

/-! ## Exact logarithmic model and channel increments -/

/-- The logarithmic entropy model
`q(y) = y/4 * (log (4/y) + 1)` used in DA3 and DA7.  Lean's value
`log 0 = 0` gives this formula its intended continuous value `q(0)=0`. -/
noncomputable def lrDA7LogarithmicQ (y : ℝ) : ℝ :=
  y / 4 * (Real.log (4 / y) + 1)

/-- The derivative of the logarithmic model away from `y = 0`. -/
noncomputable def lrDA7LogarithmicQPrime (y : ℝ) : ℝ :=
  Real.log (4 / y) / 4

/-- The Bregman remainder `omega_{q,s}` in the audited channel formulas. -/
noncomputable def lrDA7LogarithmicOmega (s y : ℝ) : ℝ :=
  lrDA7LogarithmicQ (lrCertificateB s y) - lrDA7LogarithmicQ y -
    s * (1 - y) * lrDA7LogarithmicQPrime (lrCertificateB s y)

noncomputable def lrDA7ChannelD (point : CertificatePoint) : ℝ :=
  1 - lrCertificateV point

noncomputable def lrDA7ChannelB (point : CertificatePoint) : ℝ :=
  4 / (1 + lrCertificateV point) - 2

noncomputable def lrDA7ChannelKappa (point : CertificatePoint) : ℝ :=
  lrDA7ChannelD point ^ 2 /
    (lrCertificateV point * (1 + lrCertificateV point))

/-- The nonnegative channel atom `f_0`, characterized by
`g_0 = f_0 - kappa * log 2`. -/
noncomputable def lrDA7ChannelF0 (point : CertificatePoint) : ℝ :=
  lrCertificateG0 (lrCertificateV point) +
    lrDA7ChannelKappa point * Real.log 2

/-- Exact change of `G_t` from `v = 1` to the true channel, while retaining
the logarithmic model `Q = q`. -/
noncomputable def lrDA7ChannelDeltaG (point : CertificatePoint) : ℝ :=
  lrCertificateG0 (lrCertificateV point) +
    (1 / lrCertificateV point - 1) *
      lrDA7LogarithmicQ (lrCertificateE point)

/-- Exact change of `Omega = Psi - G_t` from `v = 1` to the true channel. -/
noncomputable def lrDA7ChannelDeltaOmega (point : CertificatePoint) : ℝ :=
  lrDA7ChannelB point *
      (lrDA7LogarithmicOmega point.s (lrCertificateE point) -
        lrDA7LogarithmicOmega point.s 0) +
    lrDA7ChannelKappa point *
      lrDA7LogarithmicOmega point.s (lrCertificateE point)

/-- Exact change of the scaled gap `T` from `v = 1` to the true channel. -/
noncomputable def lrDA7ChannelDeltaT (point : CertificatePoint) : ℝ :=
  lrDA7ChannelF0 point +
    (lrDA7ChannelB point *
        (lrDA7LogarithmicQ
            (lrCertificateB point.s (lrCertificateE point)) -
          lrDA7LogarithmicQ point.s) +
      lrDA7ChannelKappa point *
        (lrDA7LogarithmicQ
            (lrCertificateB point.s (lrCertificateE point)) -
          Real.log 2)) /
      lrCertificateR point

/-! ## The exact true-channel `q` core -/

/-- The logarithmic half-slope coefficient
`H_{q,v} = a_h(v) + L - 2 log 2 + 1`. -/
noncomputable def lrDA7ChannelAH (v : ℝ) : ℝ :=
  let p := v / (2 * (1 + v))
  (-Real.log (1 - p)) / p ^ 2

noncomputable def lrDA7ChannelH (point : CertificatePoint) : ℝ :=
  lrDA7ChannelAH (lrCertificateV point) +
    Real.log (1 / point.s) - 2 * Real.log 2 + 1

/-- The compensation coefficient with the true channel but `Q = q`. -/
noncomputable def lrDA7ChannelC0Q (point : CertificatePoint) : ℝ :=
  lrCertificateR point / (3 * lrDA7ChannelH point)

noncomputable def lrDA7ChannelJBar (point : CertificatePoint) : ℝ :=
  lrDA7FiniteB point * lrCertificateX point - lrDeterminantD1 point

noncomputable def lrDA7ChannelJ1 (point : CertificatePoint) : ℝ :=
  lrCertificateBFlow point * lrCertificateX point - lrDeterminantD1 point

/-- `Psi_q / n` at the true channel, expressed by its exact increment from
the finite frozen coordinate. -/
noncomputable def lrDA7ChannelP (point : CertificatePoint) : ℝ :=
  lrDA7FiniteP point +
    (lrDA7ChannelDeltaG point + lrDA7ChannelDeltaOmega point) /
      lrLowKNormalization point

/-- `(Psi_q - G_q) / n` at the true channel. -/
noncomputable def lrDA7ChannelS (point : CertificatePoint) : ℝ :=
  lrDA7FiniteS point +
    lrDA7ChannelDeltaOmega point / lrLowKNormalization point

/-- `T_q / n` at the true channel. -/
noncomputable def lrDA7ChannelT (point : CertificatePoint) : ℝ :=
  lrDA7FiniteT point +
    lrDA7ChannelDeltaT point / lrLowKNormalization point

/-- The exact DA1-style determinant core after restoring the true channel,
but before restoring the entropy remainder `r = Q - q`.  As in the finite
stage, the separately nonnegative `4 delta B W_1` term is omitted. -/
noncomputable def lrDA7TrueChannelCore (point : CertificatePoint) : ℝ :=
  lrDeterminantD1 point * lrDA7ChannelP point +
    lrCertificateBFlow point * lrDA7ChannelS point +
    lrDA7ChannelC0Q point * lrDA7ChannelJ1 point *
      lrDA7ChannelT point

/-! ## Algebraic collection -/

/-- Abstract sign-safe collection behind the true-channel row.  This lemma
contains no analytic estimates: it says exactly how the four payments in
DA7 enter the determinant. -/
theorem lrDA7_channel_scalar_core_lower
    {D Bbar B cbar cq Jbar J p S t n dG dOmega dT
      lossG lossOmega lossT lossCoefficient : ℝ}
    (hn : n ≠ 0) (hB : B ≤ Bbar) (hS : S ≤ 0)
    (hG : -(D * dG / n) ≤ lossG)
    (hOmega : -((D + B) * dOmega / n) ≤ lossOmega)
    (hT : -(cq * J * dT / n) ≤ lossT)
    (hCoefficient : (cbar * Jbar - cq * J) * t ≤ lossCoefficient) :
    D * p + Bbar * S + cbar * Jbar * t -
        (lossG + lossOmega + lossT + lossCoefficient) ≤
      D * (p + (dG + dOmega) / n) +
        B * (S + dOmega / n) +
        cq * J * (t + dT / n) := by
  have hBterm : (Bbar - B) * S ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hB) hS
  have hidentity :
      (D * p + Bbar * S + cbar * Jbar * t -
          (lossG + lossOmega + lossT + lossCoefficient)) -
          (D * (p + (dG + dOmega) / n) +
            B * (S + dOmega / n) +
            cq * J * (t + dT / n)) =
        (Bbar - B) * S +
          ((cbar * Jbar - cq * J) * t - lossCoefficient) +
          (-(D * dG / n) - lossG) +
          (-((D + B) * dOmega / n) - lossOmega) +
          (-(cq * J * dT / n) - lossT) := by
    field_simp [hn]
    ring
  nlinarith

/-- The true outer coefficient is at most its frozen `v = 1` value. -/
theorem lrCertificateBFlow_le_lrDA7FiniteB
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point) :
    lrCertificateBFlow point ≤ lrDA7FiniteB point := by
  have hv := lrCertificateV_mem_Ioo hinterior
  have hlog : Real.log (1 + lrCertificateV point) ≤ Real.log 2 := by
    exact Real.log_le_log (by linarith [hv.1]) (by linarith [hv.2])
  unfold lrCertificateBFlow lrCertificateBFlowValue lrDA7FiniteB
  linarith

/-! ## Physical channel constants -/

lemma lrDA7_channel_e_le_s
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hregion : LRDeterminantLowKRegion point) :
    lrCertificateE point ≤ point.s := by
  unfold lrCertificateE
  nlinarith [mul_le_mul_of_nonneg_left hregion.2.2
    hinterior.1.1.le]

/-- On the low-`k` row the true channel lies in the very short interval
`[127/128,1)`. -/
lemma lrDA7_channel_v_lower
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hregion : LRDeterminantLowKRegion point) :
    (127 / 128 : ℝ) ≤ lrCertificateV point := by
  let e := lrCertificateE point
  let x := lrCertificateX point
  let v := lrCertificateV point
  have he := hinterior.2.1
  have hxPos : 0 < x := by
    dsimp [x]
    unfold lrCertificateX
    have hprod : point.chi * lrCertificateE point < 1 := calc
      point.chi * lrCertificateE point < 1 * lrCertificateE point :=
        mul_lt_mul_of_pos_right hinterior.2.2.2 hinterior.2.1.1
      _ < 1 := by simpa using hinterior.2.1.2
    linarith
  have hxLe : x ≤ 1 := by
    dsimp [x]
    unfold lrCertificateX
    exact sub_le_self _ (mul_nonneg hinterior.2.2.1.le he.1.le)
  have hradPos : 0 < (1 - e) / x := div_pos (sub_pos.mpr he.2) hxPos
  have hvSq : v ^ 2 = (1 - e) / x := by
    dsimp [v]
    unfold lrCertificateV
    exact Real.sq_sqrt hradPos.le
  have hnumLeSq : 1 - e ≤ v ^ 2 := by
    rw [hvSq, le_div_iff₀ hxPos]
    nlinarith [mul_nonneg (sub_nonneg.mpr he.2.le)
      (sub_nonneg.mpr hxLe)]
  have heUpper : e ≤ 1 / 128 := by
    dsimp [e]
    exact (lrDA7_channel_e_le_s hinterior hregion).trans hregion.1
  have hvSqLower : (127 / 128 : ℝ) ≤ v ^ 2 := by
    nlinarith
  have hv := lrCertificateV_mem_Ioo hinterior
  by_contra hnot
  have hvLt : v < 127 / 128 := lt_of_not_ge hnot
  have hvSqLt : v ^ 2 < (127 / 128 : ℝ) ^ 2 :=
    (sq_lt_sq₀ hv.1.le (by norm_num)).2 hvLt
  norm_num at hvSqLower hvSqLt
  nlinarith

/-- The basic rational estimate `(1-v)/e ≤ 128/255`. -/
lemma lrDA7_channel_d_le
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hregion : LRDeterminantLowKRegion point) :
    lrDA7ChannelD point ≤ (128 / 255 : ℝ) * lrCertificateE point := by
  let e := lrCertificateE point
  let v := lrCertificateV point
  have he := hinterior.2.1
  have hv := lrCertificateV_mem_Ioo hinterior
  have hvLower : (127 / 128 : ℝ) ≤ v := by
    simpa [v] using lrDA7_channel_v_lower hinterior hregion
  have hd : 0 ≤ 1 - v := sub_nonneg.mpr hv.2.le
  have hxPos : 0 < lrCertificateX point := by
    unfold lrCertificateX
    have hprod : point.chi * lrCertificateE point < 1 := calc
      point.chi * lrCertificateE point < 1 * lrCertificateE point :=
        mul_lt_mul_of_pos_right hinterior.2.2.2 hinterior.2.1.1
      _ < 1 := by simpa using hinterior.2.1.2
    linarith
  have hradPos : 0 < (1 - e) / lrCertificateX point :=
    div_pos (sub_pos.mpr he.2) hxPos
  have hvSq : v ^ 2 = (1 - e) / lrCertificateX point := by
    dsimp [v]
    unfold lrCertificateV
    exact Real.sq_sqrt hradPos.le
  have hxLe : lrCertificateX point ≤ 1 := by
    unfold lrCertificateX
    exact sub_le_self _ (mul_nonneg hinterior.2.2.1.le he.1.le)
  have hnumLeSq : 1 - e ≤ v ^ 2 := by
    rw [hvSq, le_div_iff₀ hxPos]
    nlinarith [mul_nonneg (sub_nonneg.mpr he.2.le)
      (sub_nonneg.mpr hxLe)]
  have hsqLoss : 1 - v ^ 2 ≤ e := by linarith
  have hfactor : (1 - v) * (1 + v) = 1 - v ^ 2 := by ring
  have hfactorLower : (255 / 128 : ℝ) ≤ 1 + v := by linarith
  have hscaled := mul_le_mul_of_nonneg_left hfactorLower hd
  change 1 - v ≤ (128 / 255 : ℝ) * e
  nlinarith [hscaled, hfactor, hsqLoss]

lemma lrDA7_channel_b_bounds
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hregion : LRDeterminantLowKRegion point) :
    0 ≤ lrDA7ChannelB point ∧
      lrDA7ChannelB point ≤ (51 / 100 : ℝ) * lrCertificateE point := by
  let e := lrCertificateE point
  let v := lrCertificateV point
  have he := hinterior.2.1
  have hv := lrCertificateV_mem_Ioo hinterior
  have hvLower : (127 / 128 : ℝ) ≤ v := by
    simpa [v] using lrDA7_channel_v_lower hinterior hregion
  have hd : 0 ≤ 1 - v := sub_nonneg.mpr hv.2.le
  have hdUpper : 1 - v ≤ (128 / 255 : ℝ) * e := by
    simpa [lrDA7ChannelD, e, v] using
      lrDA7_channel_d_le hinterior hregion
  have hden : 0 < 1 + v := by linarith [hv.1]
  have hbEq : lrDA7ChannelB point = 2 * (1 - v) / (1 + v) := by
    change 4 / (1 + v) - 2 = 2 * (1 - v) / (1 + v)
    field_simp [hden.ne']
    ring
  rw [hbEq]
  constructor
  · exact div_nonneg (mul_nonneg (by norm_num) hd) hden.le
  · rw [div_le_iff₀ hden]
    have hfactor : (255 / 128 : ℝ) ≤ 1 + v := by linarith
    have hfactorScaled := mul_le_mul_of_nonneg_left hfactor he.1.le
    dsimp [e] at hdUpper hfactorScaled ⊢
    nlinarith

lemma lrDA7_channel_kappa_nonnegative
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point) :
    0 ≤ lrDA7ChannelKappa point := by
  have hv := lrCertificateV_mem_Ioo hinterior
  unfold lrDA7ChannelKappa
  exact div_nonneg (sq_nonneg _) (mul_nonneg hv.1.le (by linarith [hv.1]))

/-! ## The first two analytic increments -/

/-- The audited raw estimate `Delta G ≥ -(51/100)e²`. -/
theorem lrDA7_channel_deltaG_lower
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hregion : LRDeterminantLowKRegion point) :
    -(51 / 100 : ℝ) * lrCertificateE point ^ 2 ≤
      lrDA7ChannelDeltaG point := by
  let e := lrCertificateE point
  let v := lrCertificateV point
  let d := 1 - v
  have he := hinterior.2.1
  have hv := lrCertificateV_mem_Ioo hinterior
  have hvLower : (127 / 128 : ℝ) ≤ v := by
    simpa [v] using lrDA7_channel_v_lower hinterior hregion
  have hvHalf : v ∈ Icc (1 / 2 : ℝ) 1 :=
    ⟨by linarith, hv.2.le⟩
  have hg0 : -2 * d ^ 2 ≤ lrCertificateG0 v := by
    simpa [d] using lrCertificateG0_lower_quadratic hvHalf
  have hq : 0 ≤ lrDA7LogarithmicQ e := by
    simpa [lrDA7LogarithmicQ, lrLowerFaceQ0] using
      lrLowerFaceQ0_nonneg_of_mem (show e ∈ Ioc (0 : ℝ) 1 from
        ⟨he.1, he.2.le⟩)
  have hinv : 0 ≤ 1 / v - 1 := by
    rw [sub_nonneg, one_le_div₀ hv.1]
    exact hv.2.le
  have hqTerm : 0 ≤ (1 / v - 1) * lrDA7LogarithmicQ e :=
    mul_nonneg hinv hq
  have hd : 0 ≤ d := by dsimp [d]; linarith [hv.2]
  have hdUpper : d ≤ (128 / 255 : ℝ) * e := by
    simpa [d, e, v, lrDA7ChannelD] using
      lrDA7_channel_d_le hinterior hregion
  have hleftNonneg : 0 ≤ 255 * d := mul_nonneg (by norm_num) hd
  have hscaled : 255 * d ≤ 128 * e := by nlinarith
  have hsquare := mul_self_le_mul_self hleftNonneg hscaled
  have hloss : 2 * d ^ 2 ≤ (51 / 100 : ℝ) * e ^ 2 := by
    nlinarith
  unfold lrDA7ChannelDeltaG
  dsimp [e, v, d] at hg0 hqTerm hloss ⊢
  nlinarith

/-- The audited raw estimate `Delta Omega ≥ -(51/400) e s`. -/
theorem lrDA7_channel_deltaOmega_lower
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hregion : LRDeterminantLowKRegion point) :
    -(51 / 400 : ℝ) * lrCertificateE point * point.s ≤
      lrDA7ChannelDeltaOmega point := by
  let e := lrCertificateE point
  let omegaE := lrDA7LogarithmicOmega point.s e
  let omegaZero := lrDA7LogarithmicOmega point.s 0
  let b := lrDA7ChannelB point
  let kappa := lrDA7ChannelKappa point
  have hs := hinterior.1
  have he := hinterior.2.1
  have homegaE : 0 ≤ omegaE := by
    dsimp [omegaE, e]
    simpa [lrDA7LogarithmicOmega, lrDA7LogarithmicQ,
      lrDA7LogarithmicQPrime, lrLowerFaceOmegaQ0,
      lrLowerFaceQ0, lrLowerFaceQ0Prime] using
      lrLowerFaceOmegaQ0_nonneg hs he
  have homegaZero : omegaZero = point.s / 4 := by
    dsimp [omegaZero]
    simpa [lrDA7LogarithmicOmega, lrDA7LogarithmicQ,
      lrDA7LogarithmicQPrime, lrLowerFaceOmegaQ0,
      lrLowerFaceQ0, lrLowerFaceQ0Prime] using
      lrLowerFaceOmegaQ0_zero hs.1
  have hdiff : -point.s / 4 ≤ omegaE - omegaZero := by
    rw [homegaZero]
    linarith
  have hb := lrDA7_channel_b_bounds hinterior hregion
  have hb0 : 0 ≤ b := by simpa [b] using hb.1
  have hbUpper : b ≤ (51 / 100 : ℝ) * e := by
    simpa [b, e] using hb.2
  have hfirst := mul_le_mul_of_nonneg_left hdiff hb0
  have hsQuarter : 0 ≤ point.s / 4 :=
    div_nonneg hinterior.1.1.le (by norm_num)
  have hweight := mul_le_mul_of_nonneg_right hbUpper hsQuarter
  have hnegative :
      -(51 / 400 : ℝ) * e * point.s ≤ b * (-point.s / 4) := by
    nlinarith
  have hkappa : 0 ≤ kappa := by
    simpa [kappa] using lrDA7_channel_kappa_nonnegative hinterior
  have hkappaTerm : 0 ≤ kappa * omegaE := mul_nonneg hkappa homegaE
  unfold lrDA7ChannelDeltaOmega
  dsimp [e, omegaE, omegaZero, b, kappa] at hfirst hnegative hkappaTerm ⊢
  nlinarith

/-! ## Conversion of the raw increments to their determinant payments -/

theorem lrDA7_channel_deltaG_payment
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hregion : LRDeterminantLowKRegion point) :
    -(lrDeterminantD1 point * lrDA7ChannelDeltaG point /
        lrLowKNormalization point) ≤
      (51 / 50 : ℝ) * point.s *
        (Real.log (1 / point.s) + point.s) := by
  let e := lrCertificateE point
  let D := lrDeterminantD1 point
  let L := Real.log (1 / point.s)
  let n := lrLowKNormalization point
  have hsIoc : point.s ∈ Ioc (0 : ℝ) lrDA7S0 := by
    simpa [lrDA7S0] using And.intro hinterior.1.1 hregion.1
  have hL : 0 < L := by
    dsimp [L]
    exact lrDA7_log_scale_pos hsIoc
  have he := hinterior.2.1
  have heS : e ≤ point.s := by
    simpa [e] using lrDA7_channel_e_le_s hinterior hregion
  have hD0 : 0 ≤ D := by
    dsimp [D]
    exact lrDeterminantD1_nonnegative hinterior
  have hDleIdeal := (lrDeterminantD1_lowK_finite_bounds hinterior hregion).2
  have hIdealUpper :=
    lrDA7IdealD_upper hinterior.1.1 hsIoc.2 hregion.2.1
  have hDUpper : D ≤ (L + point.s) / 2 := by
    dsimp [D, L]
    exact hDleIdeal.trans hIdealUpper
  have hnPos : 0 < n := by
    dsimp [n]
    exact lrLowKNormalization_pos hinterior
  have hnLower : e / 4 ≤ n := by
    dsimp [e, n]
    unfold lrLowKNormalization
    nlinarith [mul_nonneg hinterior.2.1.1.le hinterior.2.2.1.le]
  have hraw := lrDA7_channel_deltaG_lower hinterior hregion
  have hrawScaled := mul_le_mul_of_nonneg_left hraw hD0
  have hleft :
      -(D * lrDA7ChannelDeltaG point) ≤
        (51 / 100 : ℝ) * D * e ^ 2 := by
    dsimp [D, e] at hrawScaled ⊢
    nlinarith
  have heSq : e ^ 2 ≤ point.s * e := by
    nlinarith [mul_nonneg he.1.le (sub_nonneg.mpr heS)]
  have hterm :
      (51 / 100 : ℝ) * D * e ^ 2 ≤
        (51 / 200 : ℝ) * point.s * e * (L + point.s) := by
    have hDe := mul_le_mul_of_nonneg_right hDUpper (sq_nonneg e)
    have hscale := mul_le_mul_of_nonneg_left heSq (by linarith : 0 ≤ L + point.s)
    nlinarith
  let budget := (51 / 50 : ℝ) * point.s * (L + point.s)
  have hbudget : 0 ≤ budget := by
    dsimp [budget]
    exact mul_nonneg
      (mul_nonneg (by norm_num) hinterior.1.1.le)
      (by linarith : 0 ≤ L + point.s)
  have hnScaled := mul_le_mul_of_nonneg_left hnLower hbudget
  have hbudgetEq :
      budget * (e / 4) =
        (51 / 200 : ℝ) * point.s * e * (L + point.s) := by
    dsimp [budget]
    ring
  rw [hbudgetEq] at hnScaled
  change -(D * lrDA7ChannelDeltaG point / n) ≤ budget
  have hnegDiv :
      -(D * lrDA7ChannelDeltaG point / n) =
        (-(D * lrDA7ChannelDeltaG point)) / n := by ring
  rw [hnegDiv]
  apply (div_le_iff₀ hnPos).2
  exact hleft.trans (hterm.trans hnScaled)

theorem lrDA7_channel_deltaOmega_payment
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hregion : LRDeterminantLowKRegion point) :
    -((lrDeterminantD1 point + lrCertificateBFlow point) *
        lrDA7ChannelDeltaOmega point / lrLowKNormalization point) ≤
      (51 / 100 : ℝ) * point.s *
        (Real.log (1 / point.s) + 4 / 5) := by
  let e := lrCertificateE point
  let A := lrDeterminantD1 point + lrCertificateBFlow point
  let L := Real.log (1 / point.s)
  let n := lrLowKNormalization point
  have hsIoc : point.s ∈ Ioc (0 : ℝ) lrDA7S0 := by
    simpa [lrDA7S0] using And.intro hinterior.1.1 hregion.1
  have hL : 0 < L := by
    dsimp [L]
    exact lrDA7_log_scale_pos hsIoc
  have he := hinterior.2.1
  have hA0 : 0 ≤ A := by
    dsimp [A]
    exact add_nonneg (lrDeterminantD1_nonnegative hinterior)
      (lrCertificateBFlow_pos hinterior).le
  have hDleIdeal := (lrDeterminantD1_lowK_finite_bounds hinterior hregion).2
  have hIdealDUpper :=
    lrDA7IdealD_upper hinterior.1.1 hsIoc.2 hregion.2.1
  have hBTrue := lrCertificateBFlow_le_lrDA7FiniteB hinterior
  have hBFinite := (lrDA7FiniteB_ideal_interval hinterior).2
  have hBIdeal := lrDA7IdealB_upper hinterior hregion
  have heS : e ≤ point.s := by
    simpa [e] using lrDA7_channel_e_le_s hinterior hregion
  have hsUpper : point.s ≤ 1 / 128 := by
    simpa [lrDA7S0] using hsIoc.2
  have hAUpper : A ≤ L + 4 / 5 := by
    simp only [A, L, e] at hDleIdeal hIdealDUpper hBTrue hBFinite hBIdeal heS ⊢
    nlinarith [hsUpper]
  have hnPos : 0 < n := by
    dsimp [n]
    exact lrLowKNormalization_pos hinterior
  have hnLower : e / 4 ≤ n := by
    dsimp [e, n]
    unfold lrLowKNormalization
    nlinarith [mul_nonneg hinterior.2.1.1.le hinterior.2.2.1.le]
  have hraw := lrDA7_channel_deltaOmega_lower hinterior hregion
  have hrawScaled := mul_le_mul_of_nonneg_left hraw hA0
  have hleft :
      -(A * lrDA7ChannelDeltaOmega point) ≤
        (51 / 400 : ℝ) * A * e * point.s := by
    dsimp [A, e] at hrawScaled ⊢
    nlinarith
  have hterm :
      (51 / 400 : ℝ) * A * e * point.s ≤
        (51 / 400 : ℝ) * point.s * e * (L + 4 / 5) := by
    have hfactor : 0 ≤ (51 / 400 : ℝ) * e * point.s :=
      mul_nonneg (mul_nonneg (by norm_num) he.1.le) hinterior.1.1.le
    nlinarith [mul_le_mul_of_nonneg_left hAUpper hfactor]
  let budget := (51 / 100 : ℝ) * point.s * (L + 4 / 5)
  have hbudget : 0 ≤ budget := by
    dsimp [budget]
    exact mul_nonneg
      (mul_nonneg (by norm_num) hinterior.1.1.le)
      (by linarith : 0 ≤ L + 4 / 5)
  have hnScaled := mul_le_mul_of_nonneg_left hnLower hbudget
  have hbudgetEq :
      budget * (e / 4) =
        (51 / 400 : ℝ) * point.s * e * (L + 4 / 5) := by
    dsimp [budget]
    ring
  rw [hbudgetEq] at hnScaled
  change -(A * lrDA7ChannelDeltaOmega point / n) ≤ budget
  have hnegDiv :
      -(A * lrDA7ChannelDeltaOmega point / n) =
        (-(A * lrDA7ChannelDeltaOmega point)) / n := by ring
  rw [hnegDiv]
  apply (div_le_iff₀ hnPos).2
  exact hleft.trans (hterm.trans hnScaled)

/-! ## Channel payments and the two remaining inputs -/

/-- A record of the four exact pointwise payments used by the channel-stage
collector.  The public constructor below proves `deltaG` and `deltaOmega` and
asks only for the two still-open `deltaT` and `coefficient` fields. -/
structure LRDA7TrueChannelLossBounds (point : CertificatePoint) : Prop where
  deltaG :
    -(lrDeterminantD1 point * lrDA7ChannelDeltaG point /
        lrLowKNormalization point) ≤
      (51 / 50 : ℝ) * point.s *
        (Real.log (1 / point.s) + point.s)
  deltaOmega :
    -((lrDeterminantD1 point + lrCertificateBFlow point) *
        lrDA7ChannelDeltaOmega point / lrLowKNormalization point) ≤
      (51 / 100 : ℝ) * point.s *
        (Real.log (1 / point.s) + 4 / 5)
  deltaT :
    -(lrDA7ChannelC0Q point * lrDA7ChannelJ1 point *
        lrDA7ChannelDeltaT point / lrLowKNormalization point) ≤
      point.s / 10
  coefficient :
    (lrDA7FiniteC point * lrDA7ChannelJBar point -
        lrDA7ChannelC0Q point * lrDA7ChannelJ1 point) *
        lrDA7FiniteT point ≤
      (7 / 10 : ℝ) * point.s

/-- The `Delta G` and `Delta Omega` fields are now theorems.  Consequently
the channel stage has only the scaled `Delta T` and compensation-coefficient
payments left. -/
theorem lrDA7_true_channel_lossBounds_of_final_two
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hregion : LRDeterminantLowKRegion point)
    (hDeltaT :
      -(lrDA7ChannelC0Q point * lrDA7ChannelJ1 point *
          lrDA7ChannelDeltaT point / lrLowKNormalization point) ≤
        point.s / 10)
    (hCoefficient :
      (lrDA7FiniteC point * lrDA7ChannelJBar point -
          lrDA7ChannelC0Q point * lrDA7ChannelJ1 point) *
          lrDA7FiniteT point ≤
        (7 / 10 : ℝ) * point.s) :
    LRDA7TrueChannelLossBounds point :=
  { deltaG := lrDA7_channel_deltaG_payment hinterior hregion
    deltaOmega := lrDA7_channel_deltaOmega_payment hinterior hregion
    deltaT := hDeltaT
    coefficient := hCoefficient }

noncomputable def lrDA7ChannelPointwiseEndpoint
    (point : CertificatePoint) : ℝ :=
  (51 / 50) * point.s * (Real.log (1 / point.s) + point.s) +
    (51 / 100) * point.s * (Real.log (1 / point.s) + 4 / 5) +
    point.s / 10 + (7 / 10) * point.s

/-- The four pointwise channel inequalities imply the exact true-channel
core comparison before substituting `s = 1/128`. -/
theorem lrDA7_true_channel_core_lower_of_lossBounds
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hregion : LRDeterminantLowKRegion point)
    (hloss : LRDA7TrueChannelLossBounds point) :
    lrDA7FiniteFrozenCore point - lrDA7ChannelPointwiseEndpoint point ≤
      lrDA7TrueChannelCore point := by
  have hscalar := lrDA7_channel_scalar_core_lower
    (D := lrDeterminantD1 point)
    (Bbar := lrDA7FiniteB point) (B := lrCertificateBFlow point)
    (cbar := lrDA7FiniteC point) (cq := lrDA7ChannelC0Q point)
    (Jbar := lrDA7ChannelJBar point) (J := lrDA7ChannelJ1 point)
    (p := lrDA7FiniteP point) (S := lrDA7FiniteS point)
    (t := lrDA7FiniteT point) (n := lrLowKNormalization point)
    (dG := lrDA7ChannelDeltaG point)
    (dOmega := lrDA7ChannelDeltaOmega point)
    (dT := lrDA7ChannelDeltaT point)
    (lossG := (51 / 50 : ℝ) * point.s *
      (Real.log (1 / point.s) + point.s))
    (lossOmega := (51 / 100 : ℝ) * point.s *
      (Real.log (1 / point.s) + 4 / 5))
    (lossT := point.s / 10)
    (lossCoefficient := (7 / 10 : ℝ) * point.s)
    (lrLowKNormalization_pos hinterior).ne'
    (lrCertificateBFlow_le_lrDA7FiniteB hinterior)
    (lrDA7FiniteS_nonpos_lowK hinterior hregion)
    hloss.deltaG hloss.deltaOmega hloss.deltaT hloss.coefficient
  simpa [lrDA7FiniteFrozenCore, lrDA7TrueChannelCore,
    lrDA7ChannelP, lrDA7ChannelS, lrDA7ChannelT,
    lrDA7FiniteC, lrDA7ChannelJBar, lrDA7ChannelJ1,
    lrDA7ChannelPointwiseEndpoint] using hscalar

/-! ## Endpoint substitution -/

theorem lrDA7_channel_pointwise_le_endpoint
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hregion : LRDeterminantLowKRegion point) :
    lrDA7ChannelPointwiseEndpoint point ≤ lrDA7ChannelEndpoint := by
  have hsIoc : point.s ∈ Ioc (0 : ℝ) lrDA7S0 := by
    simpa [lrDA7S0] using And.intro hinterior.1.1 hregion.1
  have hs := hsIoc.1.le
  have hsUpper := hsIoc.2
  have hsL := lrDA7_s_mul_log_upper hsIoc
  have hsSq : point.s ^ 2 ≤ lrDA7S0 ^ 2 := by
    nlinarith [mul_self_le_mul_self hs hsUpper]
  unfold lrDA7ChannelPointwiseEndpoint lrDA7ChannelEndpoint
  nlinarith

/-- Completed channel row from an explicit record of its four payments. -/
theorem lrDA7_true_channel_stage_of_lossBounds
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hregion : LRDeterminantLowKRegion point)
    (hloss : LRDA7TrueChannelLossBounds point) :
    lrDA7FiniteFrozenCore point - lrDA7ChannelEndpoint ≤
      lrDA7TrueChannelCore point := by
  have hcore := lrDA7_true_channel_core_lower_of_lossBounds
    hinterior hregion hloss
  have hendpoint := lrDA7_channel_pointwise_le_endpoint hinterior hregion
  linarith

/-- Strongest public constructor for the true-channel stage.  Its only
unproved inputs are the scaled `Delta T` and compensation-coefficient
inequalities displayed in the theorem statement. -/
theorem lrDA7_true_channel_stage_of_final_two
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hregion : LRDeterminantLowKRegion point)
    (hDeltaT :
      -(lrDA7ChannelC0Q point * lrDA7ChannelJ1 point *
          lrDA7ChannelDeltaT point / lrLowKNormalization point) ≤
        point.s / 10)
    (hCoefficient :
      (lrDA7FiniteC point * lrDA7ChannelJBar point -
          lrDA7ChannelC0Q point * lrDA7ChannelJ1 point) *
          lrDA7FiniteT point ≤
        (7 / 10 : ℝ) * point.s) :
    lrDA7FiniteFrozenCore point - lrDA7ChannelEndpoint ≤
      lrDA7TrueChannelCore point := by
  exact lrDA7_true_channel_stage_of_lossBounds hinterior hregion
    (lrDA7_true_channel_lossBounds_of_final_two hinterior hregion
      hDeltaT hCoefficient)

/-! ## Elementary logarithmic-channel facts -/

/-- The logarithmic model `q` is increasing between positive points below
one.  This local form avoids any endpoint derivative at zero. -/
lemma lrDA7_logarithmicQ_mono
    {a b : ℝ} (ha : 0 < a) (hb : b ≤ 1) (hab : a ≤ b) :
    lrDA7LogarithmicQ a ≤ lrDA7LogarithmicQ b := by
  have hmono : MonotoneOn lrLowerFaceQ0 (Icc a b) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc a b)
    · intro y hy
      have hyPos : 0 < y := ha.trans_le hy.1
      exact (hasDerivAt_lrLowerFaceQ0 hyPos).continuousAt.continuousWithinAt
    · intro y hy
      rw [interior_Icc] at hy
      have hyPos : 0 < y := ha.trans hy.1
      exact (hasDerivAt_lrLowerFaceQ0 hyPos).differentiableAt
        |>.differentiableWithinAt
    · intro y hy
      rw [interior_Icc] at hy
      have hyPos : 0 < y := ha.trans hy.1
      have hyUpper : y ≤ 1 := hy.2.le.trans hb
      rw [(hasDerivAt_lrLowerFaceQ0 hyPos).deriv]
      unfold lrLowerFaceQ0Prime
      have hratio : 1 ≤ 4 / y := by
        rw [le_div_iff₀ hyPos]
        nlinarith
      exact div_nonneg (Real.log_nonneg hratio) (by norm_num)
  have h := hmono ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab
  simpa [lrDA7LogarithmicQ, lrLowerFaceQ0] using h

/-- The channel atom `f₀` is exactly the already-formalized nonnegative
compact-`v` residual. -/
lemma lrDA7_channel_f0_eq_compact
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point) :
    lrDA7ChannelF0 point = lrCompactVFZero (lrCertificateV point) := by
  let v := lrCertificateV point
  have hv := lrCertificateV_mem_Ioo hinterior
  have hvNe : v ≠ 0 := hv.1.ne'
  have hvPlusNe : 1 + v ≠ 0 := by linarith [hv.1]
  unfold lrDA7ChannelF0 lrDA7ChannelKappa lrCompactVFZero
  rw [lrCertificateG0_eq_lrG]
  dsimp [v, lrDA7ChannelD] at hvNe hvPlusNe ⊢
  field_simp [hvNe, hvPlusNe]
  ring_nf

lemma lrDA7_channel_f0_nonnegative
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point) :
    0 ≤ lrDA7ChannelF0 point := by
  rw [lrDA7_channel_f0_eq_compact hinterior]
  exact lrCompactVFZero_nonneg
    ⟨(lrCertificateV_mem_Ioo hinterior).1,
      (lrCertificateV_mem_Ioo hinterior).2.le⟩

/-! ## The radial coefficient `kappa` -/

/-- The low-`k` channel estimate `kappa ≤ e²/7`. -/
lemma lrDA7_channel_kappa_le_seventh
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hregion : LRDeterminantLowKRegion point) :
    lrDA7ChannelKappa point ≤ lrCertificateE point ^ 2 / 7 := by
  let e := lrCertificateE point
  let v := lrCertificateV point
  let d := 1 - v
  have he := hinterior.2.1
  have hv := lrCertificateV_mem_Ioo hinterior
  have hvLower : (127 / 128 : ℝ) ≤ v := by
    simpa [v] using lrDA7_channel_v_lower hinterior hregion
  have hd0 : 0 ≤ d := by dsimp [d]; linarith [hv.2]
  have hdUpper : d ≤ (128 / 255 : ℝ) * e := by
    simpa [d, e, v, lrDA7ChannelD] using
      lrDA7_channel_d_le hinterior hregion
  have hscaled : 255 * d ≤ 128 * e := by nlinarith
  have hscaled0 : 0 ≤ 255 * d := mul_nonneg (by norm_num) hd0
  have hsquare := mul_self_le_mul_self hscaled0 hscaled
  have hdsq : d ^ 2 ≤ (128 / 255 : ℝ) ^ 2 * e ^ 2 := by
    nlinarith
  have hdenLower :
      (127 / 128 : ℝ) * (255 / 128) ≤ v * (1 + v) := by
    exact mul_le_mul hvLower (by linarith : (255 / 128 : ℝ) ≤ 1 + v)
      (by norm_num) hv.1.le
  have hconstant :
      7 * (128 / 255 : ℝ) ^ 2 ≤
        (127 / 128 : ℝ) * (255 / 128) := by
    norm_num
  have hleft := mul_le_mul_of_nonneg_left hdsq (by norm_num : (0 : ℝ) ≤ 7)
  have hconstantScaled :=
    mul_le_mul_of_nonneg_right hconstant (sq_nonneg e)
  have hdenScaled :=
    mul_le_mul_of_nonneg_left hdenLower (sq_nonneg e)
  have hnum : 7 * d ^ 2 ≤ e ^ 2 * (v * (1 + v)) := by
    calc
      7 * d ^ 2 ≤
          (7 * (128 / 255 : ℝ) ^ 2) * e ^ 2 := by
        nlinarith [hleft]
      _ ≤ ((127 / 128 : ℝ) * (255 / 128)) * e ^ 2 :=
        hconstantScaled
      _ ≤ e ^ 2 * (v * (1 + v)) := by
        nlinarith [hdenScaled]
  have hdenPos : 0 < v * (1 + v) :=
    mul_pos hv.1 (by linarith [hv.1])
  unfold lrDA7ChannelKappa
  change d ^ 2 / (v * (1 + v)) ≤ e ^ 2 / 7
  rw [div_le_div_iff₀ hdenPos (by norm_num : (0 : ℝ) < 7)]
  nlinarith [hnum]

/-! ## Raw `Delta T` lower bound -/

/-- All terms in `Delta T` except `-kappa log(2)/R` have the favorable
sign. -/
theorem lrDA7_channel_deltaT_lower
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hregion : LRDeterminantLowKRegion point) :
    -(lrDA7ChannelKappa point * Real.log 2) /
        lrCertificateR point ≤
      lrDA7ChannelDeltaT point := by
  let e := lrCertificateE point
  let R := lrCertificateR point
  let yR := lrCertificateB point.s e
  let b := lrDA7ChannelB point
  let kappa := lrDA7ChannelKappa point
  let f0 := lrDA7ChannelF0 point
  have hs := hinterior.1
  have he := hinterior.2.1
  have hyRMem : yR ∈ Ioo (0 : ℝ) 1 := by
    simpa [yR, e] using lrCertificateB_mem_Ioo hs he
  have hyROrder : point.s ≤ yR := by
    dsimp [yR, e]
    unfold lrCertificateB
    nlinarith [mul_nonneg (sub_nonneg.mpr hs.2.le) he.1.le]
  have hqOrder :
      lrDA7LogarithmicQ point.s ≤ lrDA7LogarithmicQ yR :=
    lrDA7_logarithmicQ_mono hs.1 hyRMem.2.le hyROrder
  have hqYR : 0 ≤ lrDA7LogarithmicQ yR := by
    simpa [lrDA7LogarithmicQ, lrLowerFaceQ0] using
      lrLowerFaceQ0_nonneg_of_mem
        (show yR ∈ Ioc (0 : ℝ) 1 from ⟨hyRMem.1, hyRMem.2.le⟩)
  have hb0 : 0 ≤ b := by
    simpa [b] using (lrDA7_channel_b_bounds hinterior hregion).1
  have hkappa0 : 0 ≤ kappa := by
    simpa [kappa] using lrDA7_channel_kappa_nonnegative hinterior
  have hf0 : 0 ≤ f0 := by
    simpa [f0] using lrDA7_channel_f0_nonnegative hinterior
  have hRPos : 0 < R := by
    dsimp [R]
    unfold lrCertificateR
    linarith [hs.2]
  have hbTerm :
      0 ≤ b *
        (lrDA7LogarithmicQ yR - lrDA7LogarithmicQ point.s) :=
    mul_nonneg hb0 (sub_nonneg.mpr hqOrder)
  have hkappaQTerm :
      0 ≤ kappa * lrDA7LogarithmicQ yR :=
    mul_nonneg hkappa0 hqYR
  have hnumLower :
      -(kappa * Real.log 2) ≤
        b * (lrDA7LogarithmicQ yR - lrDA7LogarithmicQ point.s) +
          kappa * (lrDA7LogarithmicQ yR - Real.log 2) := by
    nlinarith
  have hdivLower :=
    (div_le_div_iff_of_pos_right hRPos).2 hnumLower
  change -(kappa * Real.log 2) / R ≤
    f0 +
      (b * (lrDA7LogarithmicQ yR - lrDA7LogarithmicQ point.s) +
        kappa * (lrDA7LogarithmicQ yR - Real.log 2)) / R
  nlinarith

/-! ## The normalized compensation factor -/

/-- A deliberately coarse lower bound for the logarithmic half-slope atom.
It is far stronger than the `a_h(v) ≥ 2 log 2 - 1` needed below. -/
lemma lrDA7_channel_ah_ge_four
    {v : ℝ} (hv : v ∈ Ioc (0 : ℝ) 1) :
    4 ≤ lrDA7ChannelAH v := by
  let p := v / (2 * (1 + v))
  have hden : 0 < 2 * (1 + v) := by nlinarith [hv.1]
  have hpPos : 0 < p := by
    dsimp [p]
    exact div_pos hv.1 hden
  have hpUpper : p ≤ 1 / 4 := by
    dsimp [p]
    rw [div_le_iff₀ hden]
    nlinarith [hv.2]
  have hOneMinus : 0 < 1 - p := by linarith
  have hlog := Real.log_le_sub_one_of_pos hOneMinus
  have hnum : p ≤ -Real.log (1 - p) := by linarith
  have hpSquare : 4 * p ^ 2 ≤ p := by
    have hscaled := mul_le_mul_of_nonneg_left hpUpper hpPos.le
    nlinarith
  change 4 ≤ (-Real.log (1 - p)) / p ^ 2
  rw [le_div_iff₀ (sq_pos_of_pos hpPos)]
  exact hpSquare.trans hnum

lemma lrDA7_channel_H_ge_log_scale
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point) :
    Real.log (1 / point.s) ≤ lrDA7ChannelH point := by
  have hv := lrCertificateV_mem_Ioo hinterior
  have hAH := lrDA7_channel_ah_ge_four
    (show lrCertificateV point ∈ Ioc (0 : ℝ) 1 from ⟨hv.1, hv.2.le⟩)
  have hlogTwo : Real.log 2 < (7 / 10 : ℝ) :=
    Real.log_two_lt_d9.trans (by norm_num)
  unfold lrDA7ChannelH
  nlinarith

/-- The true outer coefficient has the clean bound
`B ≤ L/2 + log 2`; the nonnegative outer logarithm in the frozen formula
is simply discarded. -/
lemma lrCertificateBFlow_le_log_scale_half_add_log_two
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point) :
    lrCertificateBFlow point ≤
      Real.log (1 / point.s) / 2 + Real.log 2 := by
  have hflow := lrCertificateBFlow_le_lrDA7FiniteB hinterior
  have hs := hinterior.1
  have hk : 0 < point.k := by
    have he := hinterior.2.1.1
    unfold lrCertificateE at he
    exact pos_of_mul_pos_left (by simpa [mul_comm] using he) hs.1.le
  have houter : 1 ≤ 1 + (1 - point.s) * point.k := by
    exact le_add_of_nonneg_right
      (mul_nonneg (sub_nonneg.mpr hs.2.le) hk.le)
  have hlogOuter :
      0 ≤ Real.log (1 + (1 - point.s) * point.k) :=
    Real.log_nonneg houter
  rw [lrDA7FiniteB_eq_log_form hinterior] at hflow
  linarith

lemma lrDA7_channel_j1_le_log_scale_half_add_log_two
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point) :
    lrDA7ChannelJ1 point ≤
      Real.log (1 / point.s) / 2 + Real.log 2 := by
  have hBPos := lrCertificateBFlow_pos hinterior
  have hBUpper :=
    lrCertificateBFlow_le_log_scale_half_add_log_two hinterior
  have hxLe : lrCertificateX point ≤ 1 := by
    unfold lrCertificateX
    exact sub_le_self _
      (mul_nonneg hinterior.2.2.1.le hinterior.2.1.1.le)
  have hBx := mul_le_mul_of_nonneg_left hxLe hBPos.le
  have hD0 := lrDeterminantD1_nonnegative hinterior
  unfold lrDA7ChannelJ1
  linarith

/-- The exact DA7 compensation bound.  Positivity of `J₁` is the only
place where the relevant-channel hypothesis is needed. -/
lemma lrDA7_channel_c0q_mul_j1_bounds
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hrelevant : LRHighShapeVRelevant point)
    (hregion : LRDeterminantLowKRegion point) :
    0 ≤ lrDA7ChannelC0Q point * lrDA7ChannelJ1 point ∧
      lrDA7ChannelC0Q point * lrDA7ChannelJ1 point ≤ 3 / 14 := by
  let L := Real.log (1 / point.s)
  let H := lrDA7ChannelH point
  let R := lrCertificateR point
  let J := lrDA7ChannelJ1 point
  have hsIoc : point.s ∈ Ioc (0 : ℝ) lrDA7S0 := by
    simpa [lrDA7S0] using And.intro hinterior.1.1 hregion.1
  have hLPos : 0 < L := by
    dsimp [L]
    exact lrDA7_log_scale_pos hsIoc
  have hHLower : L ≤ H := by
    simpa [L, H] using lrDA7_channel_H_ge_log_scale hinterior
  have hHPos : 0 < H := hLPos.trans_le hHLower
  have hRPos : 0 < R := by
    dsimp [R]
    unfold lrCertificateR
    linarith [hinterior.1.2]
  have hRLe : R ≤ 1 := by
    dsimp [R]
    unfold lrCertificateR
    linarith [hinterior.1.1]
  have hJPos : 0 < J := by
    simpa [J, lrDA7ChannelJ1] using
      lrCertificateBFlow_mul_X_sub_D1_pos hinterior hrelevant
  have hJUpper : J ≤ L / 2 + Real.log 2 := by
    simpa [J, L] using
      lrDA7_channel_j1_le_log_scale_half_add_log_two hinterior
  have hLBase := lrLowK_log_scale_ge_L0 hinterior hregion.1
  have hSevenLog : 7 * Real.log 2 ≤ L := by
    simpa [L, lrLowKIdealL0] using hLBase
  have hc0Pos : 0 < lrDA7ChannelC0Q point := by
    unfold lrDA7ChannelC0Q
    exact div_pos hRPos (mul_pos (by norm_num) hHPos)
  constructor
  · exact mul_nonneg hc0Pos.le hJPos.le
  · have hRJ : R * J ≤ J := by
      have hscaled := mul_le_mul_of_nonneg_right hRLe hJPos.le
      simpa using hscaled
    unfold lrDA7ChannelC0Q
    rw [div_mul_eq_mul_div, div_le_iff₀ (mul_pos (by norm_num) hHPos)]
    calc
      R * J ≤ J := hRJ
      _ ≤ L / 2 + Real.log 2 := hJUpper
      _ ≤ (9 / 14 : ℝ) * L := by nlinarith
      _ ≤ (9 / 14 : ℝ) * H :=
        mul_le_mul_of_nonneg_left hHLower (by norm_num)
      _ = (3 / 14 : ℝ) * (3 * H) := by ring

/-! ## Sign-safe scalar collection -/

/-- Pure scalar arithmetic for the radial payment.  The strict endpoint
factor from `lrDA7_radial_t_factor_lt_one_tenth` supplies the slack. -/
lemma lrDA7_scaled_deltaT_payment_algebra
    {s e R n kappa logTwo cJ deltaT : ℝ}
    (hs : 0 ≤ s) (he : 0 < e) (heS : e ≤ s)
    (hR : (127 / 128 : ℝ) ≤ R) (hn : e / 4 ≤ n)
    (hkappa0 : 0 ≤ kappa) (hkappa : kappa ≤ e ^ 2 / 7)
    (hlog0 : 0 ≤ logTwo) (hlog : logTwo ≤ 7 / 10)
    (hcJ0 : 0 ≤ cJ) (hcJ : cJ ≤ 3 / 14)
    (hdelta : -(kappa * logTwo) / R ≤ deltaT) :
    -(cJ * deltaT / n) ≤ s / 10 := by
  let A : ℝ := (3 / 14) * (1 / 7) * (7 / 10)
  let C : ℝ := A * (128 / 127)
  have hRPos : 0 < R := (by norm_num : (0 : ℝ) < 127 / 128).trans_le hR
  have hnPos : 0 < n := (div_pos he (by norm_num)).trans_le hn
  have hcKappa :
      cJ * kappa ≤ (3 / 14 : ℝ) * (e ^ 2 / 7) :=
    mul_le_mul hcJ hkappa hkappa0 (by norm_num)
  have hright0 : 0 ≤ (3 / 14 : ℝ) * (e ^ 2 / 7) := by positivity
  have hnumRaw :
      cJ * kappa * logTwo ≤
        (3 / 14 : ℝ) * (e ^ 2 / 7) * (7 / 10) :=
    mul_le_mul hcKappa hlog hlog0 hright0
  have hnum : cJ * kappa * logTwo ≤ A * e ^ 2 := by
    dsimp [A]
    nlinarith [hnumRaw]
  have hC0 : 0 ≤ C := by dsimp [C, A]; norm_num
  have hCsmall : C < 1 / 40 := by
    dsimp [C, A]
    nlinarith [lrDA7_radial_t_factor_lt_one_tenth]
  have hRscaled :=
    mul_le_mul_of_nonneg_left hR (mul_nonneg hC0 (sq_nonneg e))
  have hAR : A * e ^ 2 ≤ C * e ^ 2 * R := by
    calc
      A * e ^ 2 = C * e ^ 2 * (127 / 128) := by
        dsimp [C]
        ring
      _ ≤ C * e ^ 2 * R := hRscaled
  have hdiv : cJ * kappa * logTwo / R ≤ C * e ^ 2 := by
    rw [div_le_iff₀ hRPos]
    exact hnum.trans hAR
  have hCpayment : C * e ^ 2 ≤ e ^ 2 / 40 := by
    have := mul_le_mul_of_nonneg_right hCsmall.le (sq_nonneg e)
    nlinarith
  have heSquare : e ^ 2 ≤ s * e := by
    nlinarith [mul_nonneg he.le (sub_nonneg.mpr heS)]
  have hePayment : e ^ 2 / 40 ≤ s * e / 40 := by
    nlinarith
  have hnPayment : s * e / 40 ≤ s / 10 * n := by
    have hsTen : 0 ≤ s / 10 := div_nonneg hs (by norm_num)
    have hscaled := mul_le_mul_of_nonneg_left hn hsTen
    nlinarith
  have hpositivePayment :
      cJ * kappa * logTwo / R ≤ s / 10 * n :=
    hdiv.trans (hCpayment.trans (hePayment.trans hnPayment))
  have hscaledDelta := mul_le_mul_of_nonneg_left hdelta hcJ0
  have hnegativePayment :
      -(cJ * deltaT) ≤ cJ * kappa * logTwo / R := by
    calc
      -(cJ * deltaT) ≤ -(cJ * (-(kappa * logTwo) / R)) :=
        neg_le_neg hscaledDelta
      _ = cJ * kappa * logTwo / R := by ring
  have hcleared : -(cJ * deltaT) ≤ s / 10 * n :=
    hnegativePayment.trans hpositivePayment
  rw [show -(cJ * deltaT / n) = (-(cJ * deltaT)) / n by ring]
  exact (div_le_iff₀ hnPos).2 hcleared

/-! ## The first remaining true-channel input -/

/-- The scaled `Delta T` input required by
`lrDA7_true_channel_stage_of_final_two`. -/
theorem lrDA7_channel_deltaT_payment
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hrelevant : LRHighShapeVRelevant point)
    (hregion : LRDeterminantLowKRegion point) :
    -(lrDA7ChannelC0Q point * lrDA7ChannelJ1 point *
        lrDA7ChannelDeltaT point / lrLowKNormalization point) ≤
      point.s / 10 := by
  let e := lrCertificateE point
  let R := lrCertificateR point
  let n := lrLowKNormalization point
  let kappa := lrDA7ChannelKappa point
  let cJ := lrDA7ChannelC0Q point * lrDA7ChannelJ1 point
  have he := hinterior.2.1
  have heS : e ≤ point.s := by
    simpa [e] using lrDA7_channel_e_le_s hinterior hregion
  have hRLower : (127 / 128 : ℝ) ≤ R := by
    have hsUpper : point.s ≤ 1 / 128 := by
      simpa [lrDA7S0] using hregion.1
    dsimp [R]
    unfold lrCertificateR
    nlinarith
  have hnLower : e / 4 ≤ n := by
    dsimp [e, n]
    unfold lrLowKNormalization
    nlinarith [mul_nonneg hinterior.2.1.1.le hinterior.2.2.1.le]
  have hkappa0 : 0 ≤ kappa := by
    simpa [kappa] using lrDA7_channel_kappa_nonnegative hinterior
  have hkappaUpper : kappa ≤ e ^ 2 / 7 := by
    simpa [kappa, e] using lrDA7_channel_kappa_le_seventh hinterior hregion
  have hlog0 : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
  have hlogUpper : Real.log 2 ≤ (7 / 10 : ℝ) :=
    (Real.log_two_lt_d9.trans (by norm_num)).le
  have hcJBounds : 0 ≤ cJ ∧ cJ ≤ 3 / 14 := by
    simpa [cJ] using
      lrDA7_channel_c0q_mul_j1_bounds hinterior hrelevant hregion
  have hdelta :
      -(kappa * Real.log 2) / R ≤ lrDA7ChannelDeltaT point := by
    simpa [kappa, R] using lrDA7_channel_deltaT_lower hinterior hregion
  simpa [cJ, e, R, n, kappa] using
    lrDA7_scaled_deltaT_payment_algebra
      hinterior.1.1.le he.1 heS hRLower hnLower
      hkappa0 hkappaUpper hlog0 hlogUpper
      hcJBounds.1 hcJBounds.2 hdelta

/-! ## One-variable half-slope coordinates -/

noncomputable def lrDA7ChannelHalfP (v : ℝ) : ℝ :=
  v / (2 * (1 + v))

noncomputable def lrDA7ChannelAHBase (p : ℝ) : ℝ :=
  -Real.log (1 - p) / p ^ 2

noncomputable def lrDA7ChannelAHBaseDeriv (p : ℝ) : ℝ :=
  (p / (1 - p) + 2 * Real.log (1 - p)) / p ^ 3

noncomputable def lrDA7ChannelAHShifted (p : ℝ) : ℝ :=
  lrDA7ChannelAHBase p + (63 / 4 : ℝ) * p

noncomputable def lrDA7ChannelAHGap (point : CertificatePoint) : ℝ :=
  lrDA7ChannelAH (lrCertificateV point) - 16 * Real.log (4 / 3)

noncomputable def lrDA7ChannelBeta (point : CertificatePoint) : ℝ :=
  Real.log 2 - Real.log (1 + lrCertificateV point)

noncomputable def lrDA7ChannelA (point : CertificatePoint) : ℝ :=
  Real.log (1 / point.s) + lrLowKIdealC

lemma lrDA7ChannelAH_eq_base (v : ℝ) :
    lrDA7ChannelAH v =
      lrDA7ChannelAHBase (lrDA7ChannelHalfP v) := by
  rfl

lemma lrDA7_channel_halfP_bounds
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hregion : LRDeterminantLowKRegion point) :
    (127 / 510 : ℝ) ≤
        lrDA7ChannelHalfP (lrCertificateV point) ∧
      lrDA7ChannelHalfP (lrCertificateV point) ≤ 1 / 4 := by
  let v := lrCertificateV point
  have hv := lrCertificateV_mem_Ioo hinterior
  have hvLower : (127 / 128 : ℝ) ≤ v := by
    simpa [v] using lrDA7_channel_v_lower hinterior hregion
  have hden : 0 < 2 * (1 + v) := by positivity
  unfold lrDA7ChannelHalfP
  dsimp [v] at hv hvLower hden ⊢
  constructor
  · rw [le_div_iff₀ hden]
    nlinarith
  · rw [div_le_iff₀ hden]
    nlinarith [hv.2]

lemma lrDA7ChannelAHBase_quarter :
    lrDA7ChannelAHBase (1 / 4 : ℝ) =
      16 * Real.log (4 / 3) := by
  have hlog : Real.log (3 / 4 : ℝ) = -Real.log (4 / 3) := by
    rw [show (3 / 4 : ℝ) = 1 / (4 / 3) by norm_num,
      Real.log_div (by norm_num : (1 : ℝ) ≠ 0)
        (by norm_num : (4 / 3 : ℝ) ≠ 0), Real.log_one]
    ring
  unfold lrDA7ChannelAHBase
  rw [show (1 : ℝ) - 1 / 4 = 3 / 4 by norm_num, hlog]
  norm_num [div_eq_mul_inv]
  ring

theorem hasDerivAt_lrDA7ChannelAHBase
    {p : ℝ} (hp : 0 < p) (hpOne : p < 1) :
    HasDerivAt lrDA7ChannelAHBase
      (lrDA7ChannelAHBaseDeriv p) p := by
  have hone : HasDerivAt (fun q : ℝ ↦ 1 - q) (-1) p := by
    convert (hasDerivAt_const p 1).sub (hasDerivAt_id p) using 1 <;> ring
  have honeNe : 1 - p ≠ 0 := by linarith
  have hlog := hone.log honeNe
  have hnum : HasDerivAt (fun q : ℝ ↦ -Real.log (1 - q))
      (1 / (1 - p)) p := by
    convert hlog.neg using 1
    field_simp [honeNe]
  have hden : HasDerivAt (fun q : ℝ ↦ q ^ 2) (2 * p) p := by
    convert (hasDerivAt_id p).pow 2 using 1 <;> norm_num
  unfold lrDA7ChannelAHBase lrDA7ChannelAHBaseDeriv
  have hquot := hnum.div hden (pow_ne_zero 2 hp.ne')
  convert hquot using 1 <;>
    field_simp [hp.ne', honeNe] <;> ring

/-! ### Pade-certified lower derivative bound -/

lemma lrDA7_channel_negLog_le_pade
    {p : ℝ} (hp : p ∈ Icc (127 / 510 : ℝ) (1 / 4)) :
    -Real.log (1 - p) ≤
      p * (12 * (1 - p) + p ^ 2) /
        (6 * (1 - p) * (2 - p)) := by
  let z := p / (2 - p)
  have hpPos : 0 < p := (by norm_num : (0 : ℝ) < 127 / 510).trans_le hp.1
  have hpOne : 0 < 1 - p := by linarith [hp.2]
  have hpTwo : 0 < 2 - p := by linarith [hp.2]
  have hzPos : 0 < z := div_pos hpPos hpTwo
  have hzLt : z < 1 := by
    unfold z
    rw [div_lt_one hpTwo]
    linarith [hp.2]
  have hzMem : z ∈ Ico (0 : ℝ) 1 := ⟨hzPos.le, hzLt⟩
  have hzFull : z ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [hzPos], hzLt.le⟩
  have hzRatio : (1 + z) / (1 - z) = 1 / (1 - p) := by
    have hzOne : 1 - z ≠ 0 := by linarith [hzLt]
    rw [div_eq_iff hzOne]
    unfold z
    field_simp [hpTwo.ne', hpOne.ne']
    ring
  have hlogInv : Real.log (1 / (1 - p)) = -Real.log (1 - p) := by
    rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) hpOne.ne',
      Real.log_one]
    ring
  have hart := artanh_le_cubicPade_unit hzMem
  rw [Real.artanh_eq_half_log hzFull, hzRatio, hlogInv] at hart
  have hnegLog : -Real.log (1 - p) ≤
      2 * (z + z ^ 3 / (3 * (1 - z ^ 2))) := by
    nlinarith
  have hbaseFormula :
      1 - z ^ 2 = 4 * (1 - p) / (2 - p) ^ 2 := by
    unfold z
    field_simp [hpTwo.ne']
    ring
  have hPadeFormula :
      2 * (z + z ^ 3 / (3 * (1 - z ^ 2))) =
        p * (12 * (1 - p) + p ^ 2) /
          (6 * (1 - p) * (2 - p)) := by
    rw [hbaseFormula]
    unfold z
    field_simp [hpTwo.ne', hpOne.ne']
    ring
  exact hnegLog.trans_eq hPadeFormula

lemma lrDA7_channel_AHBase_deriv_ge_neg_sixty_three_fourths
    {p : ℝ} (hp : p ∈ Icc (127 / 510 : ℝ) (1 / 4)) :
    -(63 / 4 : ℝ) ≤ deriv lrDA7ChannelAHBase p := by
  have hpPos : 0 < p := (by norm_num : (0 : ℝ) < 127 / 510).trans_le hp.1
  have hpOne : 0 < 1 - p := by linarith [hp.2]
  have hpTwo : 0 < 2 - p := by linarith [hp.2]
  let U := p * (12 * (1 - p) + p ^ 2) /
    (6 * (1 - p) * (2 - p))
  have hPade : -Real.log (1 - p) ≤ U := by
    simpa [U] using lrDA7_channel_negLog_le_pade hp
  have hlogLower : -U ≤ Real.log (1 - p) := by linarith
  let u := 1 / 4 - p
  have hu0 : 0 ≤ u := by dsimp [u]; linarith [hp.2]
  have huUpper : u ≤ 1 / 1020 := by
    dsimp [u]
    nlinarith [hp.1]
  have hu2 : 0 ≤ u ^ 2 := sq_nonneg u
  have hu3 : 0 ≤ u ^ 3 := by positivity
  have hu4 : 0 ≤ u ^ 4 := by positivity
  have hlinear : 0 < (65 / 1024 : ℝ) - (257 / 8) * u := by
    nlinarith [huUpper]
  have hpoly : 0 <
      -6 + 9 * p + (187 / 2) * p ^ 2 -
        (567 / 4) * p ^ 3 + (189 / 4) * p ^ 4 := by
    have hexpand :
        -6 + 9 * p + (187 / 2) * p ^ 2 -
            (567 / 4) * p ^ 3 + (189 / 4) * p ^ 4 =
          65 / 1024 - (257 / 8) * u + (157 / 32) * u ^ 2 +
            (189 / 2) * u ^ 3 + (189 / 4) * u ^ 4 := by
      dsimp [u]
      ring
    rw [hexpand]
    nlinarith
  have hrational : 0 ≤
      p / (1 - p) - 2 * U + (63 / 4 : ℝ) * p ^ 3 := by
    have hidentity :
        p / (1 - p) - 2 * U + (63 / 4 : ℝ) * p ^ 3 =
          p * (-6 + 9 * p + (187 / 2) * p ^ 2 -
              (567 / 4) * p ^ 3 + (189 / 4) * p ^ 4) /
            (3 * (1 - p) * (2 - p)) := by
      dsimp [U]
      field_simp [hpOne.ne', hpTwo.ne']
      ring
    rw [hidentity]
    exact div_nonneg (mul_nonneg hpPos.le hpoly.le)
      (mul_nonneg (mul_nonneg (by norm_num) hpOne.le) hpTwo.le)
  have hnumerator : 0 ≤
      p / (1 - p) + 2 * Real.log (1 - p) +
        (63 / 4 : ℝ) * p ^ 3 := by
    nlinarith
  rw [(hasDerivAt_lrDA7ChannelAHBase hpPos (by linarith [hp.2])).deriv]
  unfold lrDA7ChannelAHBaseDeriv
  rw [le_div_iff₀ (pow_pos hpPos 3)]
  nlinarith

theorem hasDerivAt_lrDA7ChannelAHShifted
    {p : ℝ} (hp : 0 < p) (hpOne : p < 1) :
    HasDerivAt lrDA7ChannelAHShifted
      (lrDA7ChannelAHBaseDeriv p + 63 / 4) p := by
  have hbase := hasDerivAt_lrDA7ChannelAHBase hp hpOne
  have hlinear := (hasDerivAt_id p).const_mul (63 / 4 : ℝ)
  unfold lrDA7ChannelAHShifted
  convert hbase.add hlinear using 1 <;> ring

lemma lrDA7ChannelAHShifted_monotoneOn :
    MonotoneOn lrDA7ChannelAHShifted
      (Icc (127 / 510 : ℝ) (1 / 4)) := by
  apply monotoneOn_of_deriv_nonneg
    (convex_Icc (127 / 510 : ℝ) (1 / 4))
  · intro p hp
    have hpPos : 0 < p :=
      (by norm_num : (0 : ℝ) < 127 / 510).trans_le hp.1
    exact (hasDerivAt_lrDA7ChannelAHShifted hpPos (by linarith [hp.2]))
      |>.continuousAt.continuousWithinAt
  · intro p hp
    rw [interior_Icc] at hp
    have hpPos : 0 < p :=
      (by norm_num : (0 : ℝ) < 127 / 510).trans hp.1
    exact (hasDerivAt_lrDA7ChannelAHShifted hpPos (by linarith [hp.2]))
      |>.differentiableAt.differentiableWithinAt
  · intro p hp
    rw [interior_Icc] at hp
    have hpMem : p ∈ Icc (127 / 510 : ℝ) (1 / 4) :=
      ⟨hp.1.le, hp.2.le⟩
    have hpPos : 0 < p :=
      (by norm_num : (0 : ℝ) < 127 / 510).trans hp.1
    have hder :=
      lrDA7_channel_AHBase_deriv_ge_neg_sixty_three_fourths hpMem
    rw [(hasDerivAt_lrDA7ChannelAHBase hpPos (by linarith [hp.2])).deriv]
      at hder
    rw [(hasDerivAt_lrDA7ChannelAHShifted hpPos
      (by linarith [hp.2])).deriv]
    nlinarith

lemma lrDA7_channel_AHBase_deriv_nonpositive
    {p : ℝ} (hp : p ∈ Icc (127 / 510 : ℝ) (1 / 4)) :
    deriv lrDA7ChannelAHBase p ≤ 0 := by
  have hpPos : 0 < p := (by norm_num : (0 : ℝ) < 127 / 510).trans_le hp.1
  have hpOne : 0 < 1 - p := by linarith [hp.2]
  have hlog := Real.log_le_sub_one_of_pos hpOne
  have hfrac : p / (1 - p) ≤ 2 * p := by
    rw [div_le_iff₀ hpOne]
    nlinarith [hp.2]
  rw [(hasDerivAt_lrDA7ChannelAHBase hpPos (by linarith [hp.2])).deriv]
  unfold lrDA7ChannelAHBaseDeriv
  exact div_nonpos_of_nonpos_of_nonneg (by nlinarith)
    (pow_nonneg hpPos.le 3)

lemma lrDA7ChannelAHBase_antitoneOn :
    AntitoneOn lrDA7ChannelAHBase
      (Icc (127 / 510 : ℝ) (1 / 4)) := by
  apply antitoneOn_of_deriv_nonpos
    (convex_Icc (127 / 510 : ℝ) (1 / 4))
  · intro p hp
    have hpPos : 0 < p :=
      (by norm_num : (0 : ℝ) < 127 / 510).trans_le hp.1
    exact (hasDerivAt_lrDA7ChannelAHBase hpPos (by linarith [hp.2]))
      |>.continuousAt.continuousWithinAt
  · intro p hp
    rw [interior_Icc] at hp
    have hpPos : 0 < p :=
      (by norm_num : (0 : ℝ) < 127 / 510).trans hp.1
    exact (hasDerivAt_lrDA7ChannelAHBase hpPos (by linarith [hp.2]))
      |>.differentiableAt.differentiableWithinAt
  · intro p hp
    rw [interior_Icc] at hp
    exact lrDA7_channel_AHBase_deriv_nonpositive ⟨hp.1.le, hp.2.le⟩

/-! ### The isolated half-slope gap estimate -/

theorem lrDA7_channel_AH_gap_bounds
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hregion : LRDeterminantLowKRegion point) :
    0 ≤ lrDA7ChannelAHGap point ∧
      lrDA7ChannelAHGap point ≤
        (7168 / 7225 : ℝ) * lrCertificateE point := by
  let v := lrCertificateV point
  let p := lrDA7ChannelHalfP v
  let e := lrCertificateE point
  have hv := lrCertificateV_mem_Ioo hinterior
  have hvLower : (127 / 128 : ℝ) ≤ v := by
    simpa [v] using lrDA7_channel_v_lower hinterior hregion
  have hp : p ∈ Icc (127 / 510 : ℝ) (1 / 4) := by
    simpa [p, v] using lrDA7_channel_halfP_bounds hinterior hregion
  have hquarterMem : (1 / 4 : ℝ) ∈
      Icc (127 / 510 : ℝ) (1 / 4) := by norm_num
  have hanti := lrDA7ChannelAHBase_antitoneOn hp hquarterMem hp.2
  have hmono := lrDA7ChannelAHShifted_monotoneOn hp hquarterMem hp.2
  have hbaseQuarter := lrDA7ChannelAHBase_quarter
  have hgapNonnegative : 0 ≤
      lrDA7ChannelAHBase p - 16 * Real.log (4 / 3) := by
    rw [← hbaseQuarter]
    linarith
  have hgapSlope :
      lrDA7ChannelAHBase p - 16 * Real.log (4 / 3) ≤
        (63 / 4 : ℝ) * (1 / 4 - p) := by
    unfold lrDA7ChannelAHShifted at hmono
    rw [hbaseQuarter] at hmono
    linarith
  have hplus : 0 < 1 + v := by linarith [hv.1]
  have hpFormula : 1 / 4 - p = (1 - v) / (4 * (1 + v)) := by
    dsimp [p]
    unfold lrDA7ChannelHalfP
    field_simp [hplus.ne']
    ring
  have hd0 : 0 ≤ 1 - v := sub_nonneg.mpr hv.2.le
  have hdUpper : 1 - v ≤ (128 / 255 : ℝ) * e := by
    simpa [v, e, lrDA7ChannelD] using
      lrDA7_channel_d_le hinterior hregion
  have hinvUpper : 1 / (1 + v) ≤ (128 / 255 : ℝ) := by
    have hdenLower : (255 / 128 : ℝ) ≤ 1 + v := by linarith
    calc
      1 / (1 + v) ≤ 1 / (255 / 128 : ℝ) :=
        one_div_le_one_div_of_le
          (by norm_num : (0 : ℝ) < 255 / 128) hdenLower
      _ = 128 / 255 := by norm_num
  have hratio :
      (1 - v) / (1 + v) ≤
        (128 / 255 : ℝ) ^ 2 * e := by
    calc
      (1 - v) / (1 + v) = (1 - v) * (1 / (1 + v)) := by
        simp only [div_eq_mul_inv, one_mul]
      _ ≤ (1 - v) * (128 / 255 : ℝ) :=
        mul_le_mul_of_nonneg_left hinvUpper hd0
      _ = (128 / 255 : ℝ) * (1 - v) := by ring
      _ ≤ (128 / 255 : ℝ) * ((128 / 255 : ℝ) * e) :=
        mul_le_mul_of_nonneg_left hdUpper (by norm_num)
      _ = (128 / 255 : ℝ) ^ 2 * e := by ring
  have hpLoss :
      1 / 4 - p ≤ (4096 / 65025 : ℝ) * e := by
    rw [hpFormula]
    calc
      (1 - v) / (4 * (1 + v)) =
          (1 / 4 : ℝ) * ((1 - v) / (1 + v)) := by
        field_simp [hplus.ne']
      _ ≤ (1 / 4 : ℝ) * ((128 / 255 : ℝ) ^ 2 * e) :=
        mul_le_mul_of_nonneg_left hratio (by norm_num)
      _ = (4096 / 65025 : ℝ) * e := by ring
  have hgapUpper :
      lrDA7ChannelAHBase p - 16 * Real.log (4 / 3) ≤
        (7168 / 7225 : ℝ) * e := by
    have hscaled := mul_le_mul_of_nonneg_left hpLoss
      (by norm_num : (0 : ℝ) ≤ 63 / 4)
    nlinarith [hgapSlope]
  change 0 ≤ lrDA7ChannelAH (lrCertificateV point) -
      16 * Real.log (4 / 3) ∧
    lrDA7ChannelAH (lrCertificateV point) - 16 * Real.log (4 / 3) ≤
      (7168 / 7225 : ℝ) * lrCertificateE point
  rw [lrDA7ChannelAH_eq_base]
  simpa [p, v, e] using (And.intro hgapNonnegative hgapUpper)

lemma lrDA7_channel_AH_gap_le_e
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hregion : LRDeterminantLowKRegion point) :
    0 ≤ lrDA7ChannelAHGap point ∧
      lrDA7ChannelAHGap point ≤ lrCertificateE point := by
  have hgap := lrDA7_channel_AH_gap_bounds hinterior hregion
  have he0 : 0 ≤ lrCertificateE point := hinterior.2.1.1.le
  constructor
  · exact hgap.1
  · have hfactor : (7168 / 7225 : ℝ) ≤ 1 := by norm_num
    exact hgap.2.trans (by nlinarith)

/-! ## Exact cancellation coordinates -/

lemma lrDA7ChannelH_eq_A_add_gap (point : CertificatePoint) :
    lrDA7ChannelH point =
      lrDA7ChannelA point + lrDA7ChannelAHGap point := by
  unfold lrDA7ChannelH lrDA7ChannelA lrDA7ChannelAHGap lrLowKIdealC
  ring

lemma lrDA7FiniteB_sub_flow_eq_beta (point : CertificatePoint) :
    lrDA7FiniteB point - lrCertificateBFlow point =
      lrDA7ChannelBeta point := by
  unfold lrDA7FiniteB lrCertificateBFlow lrCertificateBFlowValue
    lrDA7ChannelBeta
  ring

lemma lrDA7_channel_Jbar_sub_J1 (point : CertificatePoint) :
    lrDA7ChannelJBar point - lrDA7ChannelJ1 point =
      lrDA7ChannelBeta point * lrCertificateX point := by
  unfold lrDA7ChannelJBar lrDA7ChannelJ1
  rw [show lrDA7FiniteB point =
      lrCertificateBFlow point + lrDA7ChannelBeta point by
    linarith [lrDA7FiniteB_sub_flow_eq_beta point]]
  ring

lemma lrDA7_compensation_cancellation_algebra
    {R A H h beta x Jbar J1 : ℝ}
    (hA : A ≠ 0) (hH : H ≠ 0)
    (hHform : H = A + h)
    (hJform : Jbar - J1 = beta * x) :
    R / (3 * A) * Jbar - R / (3 * H) * J1 =
      R / (3 * H) * (beta * x + h / A * Jbar) := by
  have hJ1 : J1 = Jbar - beta * x := by linarith
  rw [hHform, hJ1]
  have hAH : A + h ≠ 0 := by simpa [hHform] using hH
  field_simp [hA, hAH]
  ring

/-- Exact identity preserving the cancellation between the frozen and true
compensation coefficients. -/
theorem lrDA7_channel_compensation_exact
    {point : CertificatePoint}
    (hA : lrDA7ChannelA point ≠ 0)
    (hH : lrDA7ChannelH point ≠ 0) :
    lrDA7FiniteC point * lrDA7ChannelJBar point -
        lrDA7ChannelC0Q point * lrDA7ChannelJ1 point =
      lrDA7ChannelC0Q point *
        (lrDA7ChannelBeta point * lrCertificateX point +
          lrDA7ChannelAHGap point / lrDA7ChannelA point *
            lrDA7ChannelJBar point) := by
  have h := lrDA7_compensation_cancellation_algebra
    (R := lrCertificateR point)
    (A := lrDA7ChannelA point) (H := lrDA7ChannelH point)
    (h := lrDA7ChannelAHGap point) (beta := lrDA7ChannelBeta point)
    (x := lrCertificateX point) (Jbar := lrDA7ChannelJBar point)
    (J1 := lrDA7ChannelJ1 point) hA hH
    (lrDA7ChannelH_eq_A_add_gap point)
    (lrDA7_channel_Jbar_sub_J1 point)
  simpa [lrDA7FiniteC, lrDA7ChannelC0Q, lrCertificateR,
    lrDA7ChannelA] using h

/-! ## The outer logarithmic increment -/

lemma lrDA7_channel_beta_bounds
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hregion : LRDeterminantLowKRegion point) :
    0 ≤ lrDA7ChannelBeta point ∧
      lrDA7ChannelBeta point ≤
        (51 / 200 : ℝ) * lrCertificateE point := by
  let v := lrCertificateV point
  have hv := lrCertificateV_mem_Ioo hinterior
  have hplus : 0 < 1 + v := by linarith [hv.1]
  have hplusUpper : 1 + v ≤ 2 := by linarith [hv.2]
  have hlogOrder : Real.log (1 + v) ≤ Real.log 2 :=
    Real.log_le_log hplus hplusUpper
  have hratioPos : 0 < 2 / (1 + v) := div_pos (by norm_num) hplus
  have hlogUpper := Real.log_le_sub_one_of_pos hratioPos
  have hlogRatio : Real.log (2 / (1 + v)) =
      Real.log 2 - Real.log (1 + v) :=
    Real.log_div (by norm_num : (2 : ℝ) ≠ 0) hplus.ne'
  rw [hlogRatio] at hlogUpper
  have hratio : 2 / (1 + v) - 1 = lrDA7ChannelB point / 2 := by
    change 2 / (1 + v) - 1 = (4 / (1 + v) - 2) / 2
    field_simp [hplus.ne']
    ring
  rw [hratio] at hlogUpper
  have hb := lrDA7_channel_b_bounds hinterior hregion
  change 0 ≤ Real.log 2 - Real.log (1 + v) ∧
    Real.log 2 - Real.log (1 + v) ≤
      (51 / 200 : ℝ) * lrCertificateE point
  constructor
  · linarith
  · nlinarith [hb.2]

lemma lrDA7_channel_beta_mul_x_upper
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hregion : LRDeterminantLowKRegion point) :
    lrDA7ChannelBeta point * lrCertificateX point ≤
      (51 / 200 : ℝ) * lrCertificateE point := by
  have hbeta := lrDA7_channel_beta_bounds hinterior hregion
  have hxLe : lrCertificateX point ≤ 1 := by
    exact sub_nonneg.mp (lrDA7_x_loss_bounds hinterior).1
  have hscaled := mul_le_mul_of_nonneg_left hxLe hbeta.1
  have hscaled' :
      lrDA7ChannelBeta point * lrCertificateX point ≤
        lrDA7ChannelBeta point := by simpa using hscaled
  exact hscaled'.trans hbeta.2

/-! ## Routine low-`k` coordinate envelopes -/

lemma lrDA7_channel_A_pos
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hregion : LRDeterminantLowKRegion point) :
    0 < lrDA7ChannelA point := by
  have hsIoc : point.s ∈ Ioc (0 : ℝ) lrDA7S0 := by
    simpa [lrDA7S0] using And.intro hinterior.1.1 hregion.1
  have hL := lrDA7_log_scale_pos hsIoc
  unfold lrDA7ChannelA
  linarith [lrDA7IdealC_nonnegative]

lemma lrDA7_channel_ah_ge_four_coefficient
    {v : ℝ} (hv : v ∈ Ioc (0 : ℝ) 1) :
    4 ≤ lrDA7ChannelAH v := by
  let p := v / (2 * (1 + v))
  have hden : 0 < 2 * (1 + v) := by nlinarith [hv.1]
  have hpPos : 0 < p := by
    dsimp [p]
    exact div_pos hv.1 hden
  have hpUpper : p ≤ 1 / 4 := by
    dsimp [p]
    rw [div_le_iff₀ hden]
    nlinarith [hv.2]
  have hOneMinus : 0 < 1 - p := by linarith
  have hlog := Real.log_le_sub_one_of_pos hOneMinus
  have hnum : p ≤ -Real.log (1 - p) := by linarith
  have hpSquare : 4 * p ^ 2 ≤ p := by
    have hscaled := mul_le_mul_of_nonneg_left hpUpper hpPos.le
    nlinarith
  change 4 ≤ (-Real.log (1 - p)) / p ^ 2
  rw [le_div_iff₀ (sq_pos_of_pos hpPos)]
  exact hpSquare.trans hnum

lemma lrDA7_channel_H_ge_log_scale_coefficient
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point) :
    Real.log (1 / point.s) ≤ lrDA7ChannelH point := by
  have hv := lrCertificateV_mem_Ioo hinterior
  have hAH := lrDA7_channel_ah_ge_four_coefficient
    (show lrCertificateV point ∈ Ioc (0 : ℝ) 1 from ⟨hv.1, hv.2.le⟩)
  have hlogTwo : Real.log 2 < (7 / 10 : ℝ) :=
    Real.log_two_lt_d9.trans (by norm_num)
  unfold lrDA7ChannelH
  nlinarith

lemma lrDA7FiniteAH_ge_one
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point) :
    1 ≤ lrDA7FiniteAH point := by
  have hs := hinterior.1
  have hchi := hinterior.2.2
  have hk : 0 < point.k := by
    have he := hinterior.2.1.1
    unfold lrCertificateE at he
    exact pos_of_mul_pos_left (by simpa [mul_comm] using he) hs.1.le
  let zInner := 1 + (1 - point.s) * point.k * point.chi
  let zOuter := 1 + (1 - point.s) * point.k
  have hR : 0 ≤ 1 - point.s := sub_nonneg.mpr hs.2.le
  have hzInner : zInner ∈ Ici (1 : ℝ) := by
    dsimp [zInner]
    exact le_add_of_nonneg_right
      (mul_nonneg (mul_nonneg hR hk.le) hchi.1.le)
  have hzOuter : zOuter ∈ Ici (1 : ℝ) := by
    dsimp [zOuter]
    exact le_add_of_nonneg_right (mul_nonneg hR hk.le)
  have hHInner : 1 ≤ lrLowKIdealH zInner := by
    have hmono := lrLowKIdealH_monotone_Ici
      (show (1 : ℝ) ≤ 1 from le_rfl) hzInner hzInner
    simpa [lrLowKIdealH] using hmono
  have hHOuter : 1 ≤ lrLowKIdealH zOuter := by
    have hmono := lrLowKIdealH_monotone_Ici
      (show (1 : ℝ) ≤ 1 from le_rfl) hzOuter hzOuter
    simpa [lrLowKIdealH] using hmono
  have hweighted := mul_le_mul_of_nonneg_left hHInner hchi.1.le
  have hden : 0 < 1 + point.chi := by linarith [hchi.1]
  unfold lrDA7FiniteAH
  rw [le_div_iff₀ hden]
  dsimp [zInner, zOuter] at hweighted hHOuter ⊢
  nlinarith

lemma lrDA7FiniteT_bounds_lowK
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hregion : LRDeterminantLowKRegion point) :
    0 ≤ lrDA7FiniteT point ∧
      lrDA7FiniteT point ≤ Real.log (1 / point.s) + 7 / 5 := by
  have hlower := lrDA7FiniteT_lower hinterior
  have hidealPos := lrDA7IdealTFull_pos hinterior hregion
  have hAH := lrDA7FiniteAH_ge_one hinterior
  have hlogTwo : 2 * Real.log 2 < (7 / 5 : ℝ) := by
    nlinarith [Real.log_two_lt_d9]
  constructor
  · exact hidealPos.le.trans hlower
  · unfold lrDA7FiniteT
    linarith

lemma lrDA7FiniteB_bounds_lowK
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hregion : LRDeterminantLowKRegion point) :
    0 ≤ lrDA7FiniteB point ∧
      lrDA7FiniteB point ≤
        Real.log (1 / point.s) / 2 + 7 / 10 + 1 / 256 := by
  have hinterval := lrDA7FiniteB_ideal_interval hinterior
  have hidealPos := lrDA7IdealB_pos hinterior hregion
  have hidealUpper := lrDA7IdealB_upper hinterior hregion
  have heS := lrDA7_channel_e_le_s hinterior hregion
  have heUpper : lrCertificateE point ≤ 1 / 128 := heS.trans hregion.1
  constructor
  · exact hidealPos.le.trans hinterval.1
  · nlinarith [hinterval.2, hidealUpper, heUpper]

lemma lrDA7_channel_Jbar_upper
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hregion : LRDeterminantLowKRegion point) :
    lrDA7ChannelJBar point ≤
      Real.log (1 / point.s) / 2 + 7 / 10 + 1 / 256 := by
  have hB := lrDA7FiniteB_bounds_lowK hinterior hregion
  have hxLe : lrCertificateX point ≤ 1 := by
    exact sub_nonneg.mp (lrDA7_x_loss_bounds hinterior).1
  have hBx := mul_le_mul_of_nonneg_left hxLe hB.1
  have hD0 := lrDeterminantD1_nonnegative hinterior
  unfold lrDA7ChannelJBar
  linarith

lemma lrDA7_channel_c0q_mul_finiteT_upper
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hregion : LRDeterminantLowKRegion point) :
    lrDA7ChannelC0Q point * lrDA7FiniteT point ≤
      (Real.log (1 / point.s) + 7 / 5) /
        (3 * Real.log (1 / point.s)) := by
  let L := Real.log (1 / point.s)
  let H := lrDA7ChannelH point
  let R := lrCertificateR point
  let tbar := lrDA7FiniteT point
  have hsIoc : point.s ∈ Ioc (0 : ℝ) lrDA7S0 := by
    simpa [lrDA7S0] using And.intro hinterior.1.1 hregion.1
  have hLPos : 0 < L := by
    dsimp [L]
    exact lrDA7_log_scale_pos hsIoc
  have hHLower : L ≤ H := by
    simpa [L, H] using
      lrDA7_channel_H_ge_log_scale_coefficient hinterior
  have hHPos : 0 < H := hLPos.trans_le hHLower
  have hRPos : 0 < R := by
    dsimp [R]
    unfold lrCertificateR
    linarith [hinterior.1.2]
  have hRLe : R ≤ 1 := by
    dsimp [R]
    unfold lrCertificateR
    linarith [hinterior.1.1]
  have htBounds : 0 ≤ tbar ∧ tbar ≤ L + 7 / 5 := by
    simpa [tbar, L] using lrDA7FiniteT_bounds_lowK hinterior hregion
  have hRt : R * tbar ≤ L + 7 / 5 := by
    have hscaled := mul_le_mul_of_nonneg_right hRLe htBounds.1
    nlinarith
  have hleft := mul_le_mul_of_nonneg_right hRt hLPos.le
  have hright := mul_le_mul_of_nonneg_left hHLower
    (by linarith : 0 ≤ L + 7 / 5)
  unfold lrDA7ChannelC0Q
  change R / (3 * H) * tbar ≤ (L + 7 / 5) / (3 * L)
  rw [div_mul_eq_mul_div,
    div_le_div_iff₀ (mul_pos (by norm_num) hHPos)
      (mul_pos (by norm_num) hLPos)]
  nlinarith

lemma lrDA7_channel_gap_over_A_mul_Jbar_upper
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hregion : LRDeterminantLowKRegion point) :
    lrDA7ChannelAHGap point / lrDA7ChannelA point *
        lrDA7ChannelJBar point ≤
      lrCertificateE point / Real.log (1 / point.s) *
        (Real.log (1 / point.s) / 2 + 7 / 10 + 1 / 256) := by
  let L := Real.log (1 / point.s)
  let A := lrDA7ChannelA point
  let h := lrDA7ChannelAHGap point
  let e := lrCertificateE point
  let Bmax := L / 2 + 7 / 10 + 1 / 256
  have hsIoc : point.s ∈ Ioc (0 : ℝ) lrDA7S0 := by
    simpa [lrDA7S0] using And.intro hinterior.1.1 hregion.1
  have hLPos : 0 < L := by
    dsimp [L]
    exact lrDA7_log_scale_pos hsIoc
  have hAPos : 0 < A := by
    simpa [A] using lrDA7_channel_A_pos hinterior hregion
  have hALower : L ≤ A := by
    dsimp [L, A]
    unfold lrDA7ChannelA
    linarith [lrDA7IdealC_nonnegative]
  have hgap : 0 ≤ h ∧ h ≤ e := by
    simpa [h, e] using lrDA7_channel_AH_gap_le_e hinterior hregion
  have he0 : 0 ≤ e := hinterior.2.1.1.le
  have hdiv0 : 0 ≤ h / A := div_nonneg hgap.1 hAPos.le
  have hdivUpper : h / A ≤ e / L := by
    rw [div_le_div_iff₀ hAPos hLPos]
    have hfirst := mul_le_mul_of_nonneg_right hgap.2 hLPos.le
    have hsecond := mul_le_mul_of_nonneg_left hALower he0
    nlinarith
  have hBmax0 : 0 ≤ Bmax := by
    dsimp [Bmax]
    linarith
  have hJ : lrDA7ChannelJBar point ≤ Bmax := by
    simpa [Bmax, L] using lrDA7_channel_Jbar_upper hinterior hregion
  have hfirst := mul_le_mul_of_nonneg_left hJ hdiv0
  have hsecond := mul_le_mul_of_nonneg_right hdivUpper hBmax0
  simpa [h, A, e, L, Bmax] using hfirst.trans hsecond

lemma lrDA7_channel_compensation_bracket_upper
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hregion : LRDeterminantLowKRegion point) :
    lrDA7ChannelBeta point * lrCertificateX point +
        lrDA7ChannelAHGap point / lrDA7ChannelA point *
          lrDA7ChannelJBar point ≤
      lrCertificateE point *
        (51 / 200 +
          (Real.log (1 / point.s) / 2 + 7 / 10 + 1 / 256) /
            Real.log (1 / point.s)) := by
  have hbeta := lrDA7_channel_beta_mul_x_upper hinterior hregion
  have hgap :=
    lrDA7_channel_gap_over_A_mul_Jbar_upper hinterior hregion
  calc
    lrDA7ChannelBeta point * lrCertificateX point +
          lrDA7ChannelAHGap point / lrDA7ChannelA point *
            lrDA7ChannelJBar point ≤
        (51 / 200 : ℝ) * lrCertificateE point +
          lrCertificateE point / Real.log (1 / point.s) *
            (Real.log (1 / point.s) / 2 + 7 / 10 + 1 / 256) :=
      add_le_add hbeta hgap
    _ = lrCertificateE point *
        (51 / 200 +
          (Real.log (1 / point.s) / 2 + 7 / 10 + 1 / 256) /
            Real.log (1 / point.s)) := by ring

/-! ## Exact rational endpoint -/

theorem lrDA7_coefficient_factor_two_fifths :
    ((lrDA7LMinus + 7 / 5) / (3 * lrDA7LMinus)) *
        (51 / 200 +
          (lrDA7LMinus / 2 + 7 / 10 + 1 / 256) /
            lrDA7LMinus) =
          3119364197 / 8068183200 ∧
      (3119364197 / 8068183200 : ℝ) < 2 / 5 := by
  norm_num [lrDA7LMinus]

lemma lrDA7_coefficient_scalar_factor_le_two_fifths
    {L : ℝ} (hL : lrDA7LMinus ≤ L) :
    ((L + 7 / 5) / (3 * L)) *
        (51 / 200 + (L / 2 + 7 / 10 + 1 / 256) / L) ≤
      (2 / 5 : ℝ) := by
  have hLminusPos : 0 < lrDA7LMinus := by norm_num [lrDA7LMinus]
  have hLPos : 0 < L := hLminusPos.trans_le hL
  have hinv : 1 / L ≤ 1 / lrDA7LMinus :=
    one_div_le_one_div_of_le hLminusPos hL
  let f1 := (L + 7 / 5) / (3 * L)
  let f2 := 51 / 200 + (L / 2 + 7 / 10 + 1 / 256) / L
  let F1 := (lrDA7LMinus + 7 / 5) / (3 * lrDA7LMinus)
  let F2 := 51 / 200 +
    (lrDA7LMinus / 2 + 7 / 10 + 1 / 256) / lrDA7LMinus
  have hf1Form : f1 = 1 / 3 + (7 / 15 : ℝ) * (1 / L) := by
    dsimp [f1]
    field_simp [hLPos.ne']
    ring
  have hF1Form : F1 =
      1 / 3 + (7 / 15 : ℝ) * (1 / lrDA7LMinus) := by
    dsimp [F1]
    field_simp [hLminusPos.ne']
    ring
  have hf2Form : f2 = 151 / 200 +
      (7 / 10 + 1 / 256 : ℝ) * (1 / L) := by
    dsimp [f2]
    field_simp [hLPos.ne']
    ring
  have hF2Form : F2 = 151 / 200 +
      (7 / 10 + 1 / 256 : ℝ) * (1 / lrDA7LMinus) := by
    dsimp [F2]
    field_simp [hLminusPos.ne']
    ring
  have hf1 : f1 ≤ F1 := by
    rw [hf1Form, hF1Form]
    nlinarith
  have hf2 : f2 ≤ F2 := by
    rw [hf2Form, hF2Form]
    nlinarith
  have hf2Nonnegative : 0 ≤ f2 := by
    rw [hf2Form]
    positivity
  have hF1Nonnegative : 0 ≤ F1 := by
    rw [hF1Form]
    positivity
  have hproduct : f1 * f2 ≤ F1 * F2 := calc
    f1 * f2 ≤ F1 * f2 := mul_le_mul_of_nonneg_right hf1 hf2Nonnegative
    _ ≤ F1 * F2 := mul_le_mul_of_nonneg_left hf2 hF1Nonnegative
  have hendpoint := lrDA7_coefficient_factor_two_fifths
  dsimp [f1, f2] at hproduct ⊢
  dsimp [F1, F2] at hproduct
  calc
    ((L + 7 / 5) / (3 * L)) *
          (51 / 200 + (L / 2 + 7 / 10 + 1 / 256) / L) ≤
        ((lrDA7LMinus + 7 / 5) / (3 * lrDA7LMinus)) *
          (51 / 200 +
            (lrDA7LMinus / 2 + 7 / 10 + 1 / 256) /
              lrDA7LMinus) := hproduct
    _ = (3119364197 / 8068183200 : ℝ) := hendpoint.1
    _ ≤ 2 / 5 := hendpoint.2.le

/-! ## Completed compensation payment -/

/-- Stronger form of the remaining compensation-coefficient payment. -/
theorem lrDA7_channel_coefficient_payment_two_fifths
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hregion : LRDeterminantLowKRegion point) :
    (lrDA7FiniteC point * lrDA7ChannelJBar point -
        lrDA7ChannelC0Q point * lrDA7ChannelJ1 point) *
        lrDA7FiniteT point ≤
      (2 / 5 : ℝ) * point.s := by
  let L := Real.log (1 / point.s)
  let e := lrCertificateE point
  let ct := lrDA7ChannelC0Q point * lrDA7FiniteT point
  let bracket := lrDA7ChannelBeta point * lrCertificateX point +
    lrDA7ChannelAHGap point / lrDA7ChannelA point *
      lrDA7ChannelJBar point
  let f1 := (L + 7 / 5) / (3 * L)
  let f2 := 51 / 200 + (L / 2 + 7 / 10 + 1 / 256) / L
  have hsIoc : point.s ∈ Ioc (0 : ℝ) lrDA7S0 := by
    simpa [lrDA7S0] using And.intro hinterior.1.1 hregion.1
  have hLPos : 0 < L := by
    dsimp [L]
    exact lrDA7_log_scale_pos hsIoc
  have hLBase := lrLowK_log_scale_ge_L0 hinterior hregion.1
  have hLminus : lrDA7LMinus ≤ L := by
    have hwindow := lrDA7_log_window.1.le
    dsimp [L]
    unfold lrLowKIdealL0 at hLBase
    exact hwindow.trans hLBase
  have hAPos := lrDA7_channel_A_pos hinterior hregion
  have hHLower : L ≤ lrDA7ChannelH point := by
    simpa [L] using lrDA7_channel_H_ge_log_scale_coefficient hinterior
  have hHPos : 0 < lrDA7ChannelH point := hLPos.trans_le hHLower
  have hexact := lrDA7_channel_compensation_exact hAPos.ne' hHPos.ne'
  have hct : ct ≤ f1 := by
    simpa [ct, f1, L] using
      lrDA7_channel_c0q_mul_finiteT_upper hinterior hregion
  have ht0 := (lrDA7FiniteT_bounds_lowK hinterior hregion).1
  have hRPos : 0 < lrCertificateR point := by
    unfold lrCertificateR
    linarith [hinterior.1.2]
  have hcq0 : 0 ≤ lrDA7ChannelC0Q point := by
    unfold lrDA7ChannelC0Q
    exact div_nonneg hRPos.le (mul_nonneg (by norm_num) hHPos.le)
  have hct0 : 0 ≤ ct := by
    dsimp [ct]
    exact mul_nonneg hcq0 ht0
  have hbracket : bracket ≤ e * f2 := by
    simpa [bracket, e, f2, L] using
      lrDA7_channel_compensation_bracket_upper hinterior hregion
  have he0 : 0 ≤ e := hinterior.2.1.1.le
  have hf1Pos : 0 < f1 := by
    dsimp [f1]
    exact div_pos (by linarith) (mul_pos (by norm_num) hLPos)
  have hf2Nonnegative : 0 ≤ f2 := by
    dsimp [f2]
    exact add_nonneg (by norm_num)
      (div_nonneg (by linarith) hLPos.le)
  have hef2 : 0 ≤ e * f2 := mul_nonneg he0 hf2Nonnegative
  have hfirst : ct * bracket ≤ ct * (e * f2) :=
    mul_le_mul_of_nonneg_left hbracket hct0
  have hsecond : ct * (e * f2) ≤ f1 * (e * f2) :=
    mul_le_mul_of_nonneg_right hct hef2
  have hfactor := lrDA7_coefficient_scalar_factor_le_two_fifths hLminus
  have heS : e ≤ point.s := by
    simpa [e] using lrDA7_channel_e_le_s hinterior hregion
  have hfactor0 : 0 ≤ f1 * f2 :=
    mul_nonneg hf1Pos.le hf2Nonnegative
  calc
    (lrDA7FiniteC point * lrDA7ChannelJBar point -
          lrDA7ChannelC0Q point * lrDA7ChannelJ1 point) *
          lrDA7FiniteT point = ct * bracket := by
        rw [hexact]
        dsimp [ct, bracket]
        ring
    _ ≤ e * (f1 * f2) := by
      calc
        ct * bracket ≤ ct * (e * f2) := hfirst
        _ ≤ f1 * (e * f2) := hsecond
        _ = e * (f1 * f2) := by ring
    _ ≤ point.s * (f1 * f2) :=
      mul_le_mul_of_nonneg_right heS hfactor0
    _ ≤ point.s * (2 / 5) :=
      mul_le_mul_of_nonneg_left
        (by simpa [f1, f2, L] using hfactor) hinterior.1.1.le
    _ = (2 / 5 : ℝ) * point.s := by ring

/-- The exact `7/10` compensation hypothesis requested by the true-channel
collector.  The proof above in fact supplies the stronger coefficient `2/5`. -/
theorem lrDA7_channel_compensation_payment
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hregion : LRDeterminantLowKRegion point) :
    (lrDA7FiniteC point * lrDA7ChannelJBar point -
        lrDA7ChannelC0Q point * lrDA7ChannelJ1 point) *
        lrDA7FiniteT point ≤
      (7 / 10 : ℝ) * point.s := by
  have h :
      (lrDA7FiniteC point * lrDA7ChannelJBar point -
          lrDA7ChannelC0Q point * lrDA7ChannelJ1 point) *
          lrDA7FiniteT point ≤
        (2 / 5 : ℝ) * point.s :=
    lrDA7_channel_coefficient_payment_two_fifths hinterior hregion
  nlinarith [hinterior.1.1]

/-- Once the `Delta T` theorem above is installed, the true-channel stage
reduces to the compensation-coefficient payment alone. -/
theorem lrDA7_true_channel_stage_of_coefficient
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hrelevant : LRHighShapeVRelevant point)
    (hregion : LRDeterminantLowKRegion point)
    (hCoefficient :
      (lrDA7FiniteC point * lrDA7ChannelJBar point -
          lrDA7ChannelC0Q point * lrDA7ChannelJ1 point) *
          lrDA7FiniteT point ≤
        (7 / 10 : ℝ) * point.s) :
    lrDA7FiniteFrozenCore point - lrDA7ChannelEndpoint ≤
      lrDA7TrueChannelCore point := by
  exact lrDA7_true_channel_stage_of_final_two hinterior hregion
    (lrDA7_channel_deltaT_payment hinterior hrelevant hregion)
    hCoefficient

/-- The true-channel restoration is unconditional on the relevant low-`k`
region: the two formerly open payments are supplied by the analytic estimates
above. -/
theorem lrDA7_true_channel_stage_proved
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hrelevant : LRHighShapeVRelevant point)
    (hregion : LRDeterminantLowKRegion point) :
    lrDA7FiniteFrozenCore point - lrDA7ChannelEndpoint ≤
      lrDA7TrueChannelCore point := by
  exact lrDA7_true_channel_stage_of_final_two hinterior hregion
    (lrDA7_channel_deltaT_payment hinterior hrelevant hregion)
    (lrDA7_channel_compensation_payment hinterior hregion)


end CourtadeKumar
