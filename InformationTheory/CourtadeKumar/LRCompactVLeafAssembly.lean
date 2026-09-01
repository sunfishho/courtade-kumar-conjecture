import InformationTheory.CourtadeKumar.LRCompactVIntervalArithmetic

/-!
# Sign-safe assembly of compact `V` interval leaves

This module packages the exact interval components into the grouped lower
bound used by the audited compact certificate.  The delicate product `B*Q`
selects the appropriate endpoint of `B` from the sign of the certified lower
bound for `Q`; the positive `D*Ψ` payment clamps both lower endpoints at zero.

Transcendental enclosures for `B`, `P₀`, and `W_R(1)` remain parameters here.
Later payload checkers may construct them by any kernel-proved method without
changing the sign-sensitive assembly theorem.
-/

namespace CourtadeKumar

namespace RationalEnclosure

/-- The strongest nonnegative lower endpoint justified by an enclosure and
an independent proof that its semantic value is nonnegative. -/
def nonnegativeLower (a : RationalEnclosure) : ℚ := max 0 a.lower

theorem cast_nonnegativeLower_le
    {a : RationalEnclosure} {x : ℝ} (hx : a.Contains x)
    (hx0 : 0 ≤ x) :
    (a.nonnegativeLower : ℝ) ≤ x := by
  change ((max 0 a.lower : ℚ) : ℝ) ≤ x
  rw [Rat.cast_max, Rat.cast_zero]
  exact max_le hx0 hx.1

theorem nonnegativeLower_nonnegative (a : RationalEnclosure) :
    (0 : ℚ) ≤ a.nonnegativeLower :=
  le_max_left _ _

end RationalEnclosure

/-- The grouped correction factor expressed directly in `(R,v,x)`. -/
noncomputable def lrCompactVQX (N : ℕ) (R v x : ℝ) : ℝ :=
  lrCompactVPWLower N R v (Real.sqrt x) -
    4 * lrWKernel R 1 * lrCompactVMx v x

/-- Exact enclosure of `Q` from enclosures of `P₀` and `W_R(1)`. -/
def lrCompactVQEnclosure
    (N : ℕ) (box : CertificateBox)
    (pZero wOne : RationalEnclosure) : RationalEnclosure :=
  RationalEnclosure.sub
    (lrCompactVPWLowerEnclosure N box pZero)
    (RationalEnclosure.scale 4 <|
      RationalEnclosure.mul wOne (lrCompactVMxEnclosure box))

theorem lrCompactVQEnclosure_sound
    {N : ℕ} {box : CertificateBox} {point : CertificatePoint}
    (hbox : LRCompactVBoxValid box) (hpoint : box.Contains point)
    {pZero wOne : RationalEnclosure}
    (hpZero : pZero.Contains (lrCompactVPZeroX point.k point.chi))
    (hwOne : wOne.Contains (lrWKernel point.s 1)) :
    (lrCompactVQEnclosure N box pZero wOne).Contains
      (lrCompactVQX N point.s point.k point.chi) := by
  have hpw := lrCompactVPWLowerEnclosure_sound_sqrt
    (N := N) hbox hpoint hpZero
  have hmx := lrCompactVMxEnclosure_sound hbox hpoint
  have hcorrection := RationalEnclosure.contains_scale (4 : ℚ) <|
    RationalEnclosure.contains_mul hwOne hmx
  simpa [lrCompactVQEnclosure, lrCompactVQX, mul_assoc] using
    RationalEnclosure.contains_sub hpw hcorrection

/-- Endpoint-oriented lower bound for a product `B*Q` when `B≥0`. -/
def lrCompactVSignedProductLower
    (b q : RationalEnclosure) : ℚ :=
  if 0 ≤ q.lower then b.lower * q.lower else b.upper * q.lower

/-- Endpoint-oriented lower bound for `B * Q` when the checker has proved a
scalar lower bound for `Q`, rather than an enclosure of one fixed surrogate.

This form is useful for hybrid certificates: two different analytic
expressions may both be lower bounds for the same exact `Q`, so their maximum
is stronger even though it is not the lower endpoint of an enclosure of
either expression. -/
def lrCompactVSignedProductScalarLower
    (b : RationalEnclosure) (qLower : ℚ) : ℚ :=
  if 0 ≤ qLower then b.lower * qLower else b.upper * qLower

theorem cast_lrCompactVSignedProductScalarLower_le
    {b : RationalEnclosure} {qLower : ℚ} {B Q : ℝ}
    (hB : b.Contains B) (hQLower : (qLower : ℝ) ≤ Q) (hB0 : 0 ≤ B) :
    (lrCompactVSignedProductScalarLower b qLower : ℝ) ≤ B * Q := by
  by_cases hq0 : (0 : ℚ) ≤ qLower
  · rw [lrCompactVSignedProductScalarLower, if_pos hq0]
    norm_num only [Rat.cast_mul]
    have hq0Real : (0 : ℝ) ≤ qLower := by exact_mod_cast hq0
    exact (mul_le_mul hB.1 le_rfl hq0Real hB0).trans
      (mul_le_mul_of_nonneg_left hQLower hB0)
  · rw [lrCompactVSignedProductScalarLower, if_neg hq0]
    norm_num only [Rat.cast_mul]
    have hqNeg : (qLower : ℝ) ≤ 0 := by
      exact_mod_cast (le_of_not_ge hq0)
    have hfirst :
        (b.upper : ℝ) * (qLower : ℝ) ≤ B * (qLower : ℝ) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hB.2) (neg_nonneg.mpr hqNeg)]
    exact hfirst.trans (mul_le_mul_of_nonneg_left hQLower hB0)

theorem cast_lrCompactVSignedProductLower_le
    {b q : RationalEnclosure} {B Q : ℝ}
    (hB : b.Contains B) (hQ : q.Contains Q) (hB0 : 0 ≤ B) :
    (lrCompactVSignedProductLower b q : ℝ) ≤ B * Q := by
  by_cases hq0 : (0 : ℚ) ≤ q.lower
  · rw [lrCompactVSignedProductLower, if_pos hq0]
    norm_num only [Rat.cast_mul]
    have hq0Real : (0 : ℝ) ≤ q.lower := by exact_mod_cast hq0
    exact (mul_le_mul hB.1 le_rfl hq0Real hB0).trans
      (mul_le_mul_of_nonneg_left hQ.1 hB0)
  · rw [lrCompactVSignedProductLower, if_neg hq0]
    norm_num only [Rat.cast_mul]
    have hqNeg : ((q.lower : ℚ) : ℝ) ≤ 0 := by
      exact_mod_cast (le_of_not_ge hq0)
    have hfirst :
        (b.upper : ℝ) * (q.lower : ℝ) ≤
          B * (q.lower : ℝ) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hB.2) (neg_nonneg.mpr hqNeg)]
    exact hfirst.trans (mul_le_mul_of_nonneg_left hQ.1 hB0)

/-- The correction `4 W_R(1) M_x` appearing in the grouped reserve. -/
def lrCompactVCorrectionEnclosure
    (box : CertificateBox) (wOne : RationalEnclosure) :
    RationalEnclosure :=
  RationalEnclosure.scale 4 <|
    RationalEnclosure.mul wOne (lrCompactVMxEnclosure box)

theorem lrCompactVCorrectionEnclosure_sound
    {box : CertificateBox} {point : CertificatePoint}
    (hbox : LRCompactVBoxValid box) (hpoint : box.Contains point)
    {wOne : RationalEnclosure}
    (hwOne : wOne.Contains (lrWKernel point.s 1)) :
    (lrCompactVCorrectionEnclosure box wOne).Contains
      (4 * lrWKernel point.s 1 * lrCompactVMx point.k point.chi) := by
  have hmx := lrCompactVMxEnclosure_sound hbox hpoint
  simpa [lrCompactVCorrectionEnclosure, mul_assoc] using
    (RationalEnclosure.contains_scale (4 : ℚ) <|
      RationalEnclosure.contains_mul hwOne hmx)

/-- Direct-positive-head lower bound for the exact grouped `Q`. -/
def lrCompactVHeadQLower
    (N : ℕ) (box : CertificateBox) (wOne : RationalEnclosure) : ℚ :=
  (lrCompactVPWHeadEnclosure N box).lower -
    (lrCompactVCorrectionEnclosure box wOne).upper

theorem cast_lrCompactVHeadQLower_le
    {N : ℕ} {box : CertificateBox} {point : CertificatePoint}
    (hbox : LRCompactVBoxValid box) (hpoint : box.Contains point)
    (hinterior : LRCompactVInterior point)
    {wOne : RationalEnclosure}
    (hwOne : wOne.Contains (lrWKernel point.s 1)) :
    (lrCompactVHeadQLower N box wOne : ℝ) ≤
      lrFlowPW point.s point.k (Real.sqrt point.chi) -
        4 * lrWKernel point.s 1 * lrCompactVMx point.k point.chi := by
  have ht : Real.sqrt point.chi ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor
    · exact Real.sqrt_pos.2 hinterior.2.2.1
    · simpa using
        (Real.sqrt_lt_sqrt_iff hinterior.2.2.1.le).2 hinterior.2.2.2
  have hhead := lrCompactVPWHeadEnclosure_sound
    (N := N) hbox hpoint
  have hheadFlow := lrCompactVPWHead_le_lrFlowPW
    hinterior.1 hinterior.2.1 ht N
  have hsquare : (Real.sqrt point.chi) ^ 2 = point.chi :=
    Real.sq_sqrt hinterior.2.2.1.le
  rw [hsquare] at hheadFlow
  have hcorrection := lrCompactVCorrectionEnclosure_sound
    hbox hpoint hwOne
  change (((lrCompactVPWHeadEnclosure N box).lower -
    (lrCompactVCorrectionEnclosure box wOne).upper : ℚ) : ℝ) ≤ _
  norm_num only [Rat.cast_sub]
  exact sub_le_sub (hhead.1.trans hheadFlow) hcorrection.2

/-- Maximum of the tail-enhanced and direct-positive-head lower bounds for
the exact grouped `Q`.  This is the executable strengthening that reduced
the audited `[3/4,13/16]` terminal count by more than sixty percent. -/
def lrCompactVHybridQLower
    (N : ℕ) (box : CertificateBox)
    (pZero wOne : RationalEnclosure) : ℚ :=
  max (lrCompactVQEnclosure N box pZero wOne).lower
    (lrCompactVHeadQLower N box wOne)

theorem cast_lrCompactVHybridQLower_le
    {N : ℕ} {box : CertificateBox} {point : CertificatePoint}
    (hbox : LRCompactVBoxValid box) (hpoint : box.Contains point)
    (hinterior : LRCompactVInterior point)
    {pZero wOne : RationalEnclosure}
    (hpZero : pZero.Contains (lrCompactVPZeroX point.k point.chi))
    (hwOne : wOne.Contains (lrWKernel point.s 1)) :
    (lrCompactVHybridQLower N box pZero wOne : ℝ) ≤
      lrFlowPW point.s point.k (Real.sqrt point.chi) -
        4 * lrWKernel point.s 1 * lrCompactVMx point.k point.chi := by
  have ht : Real.sqrt point.chi ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor
    · exact Real.sqrt_pos.2 hinterior.2.2.1
    · simpa using
        (Real.sqrt_lt_sqrt_iff hinterior.2.2.1.le).2 hinterior.2.2.2
  have htailContains := lrCompactVQEnclosure_sound
    (N := N) hbox hpoint hpZero hwOne
  have htailFlow := lrCompactVPWLower_le_lrFlowPW
    hinterior.1 hinterior.2.1 ht N
  have htail :
      ((lrCompactVQEnclosure N box pZero wOne).lower : ℝ) ≤
        lrFlowPW point.s point.k (Real.sqrt point.chi) -
          4 * lrWKernel point.s 1 * lrCompactVMx point.k point.chi := by
    refine htailContains.1.trans ?_
    unfold lrCompactVQX
    exact sub_le_sub_right htailFlow _
  have hhead := cast_lrCompactVHeadQLower_le
    (N := N) hbox hpoint hinterior hwOne
  change ((max (lrCompactVQEnclosure N box pZero wOne).lower
    (lrCompactVHeadQLower N box wOne) : ℚ) : ℝ) ≤ _
  rw [Rat.cast_max]
  exact max_le htail hhead

/-- Fully rational grouped leaf lower bound. -/
def lrCompactVGroupedLower
    (N : ℕ) (box : CertificateBox)
    (b pZero wOne : RationalEnclosure) : ℚ :=
  let q := lrCompactVQEnclosure N box pZero wOne
  lrCompactVSignedProductLower b q +
    (lrCompactVDHeadEnclosure N box).nonnegativeLower *
      (lrCompactVPsiPolynomialHeadEnclosure N box).nonnegativeLower

/-- The semantic grouped expression in compact coordinates. -/
noncomputable def lrCompactVGroupedX
    (N : ℕ) (point : CertificatePoint) : ℝ :=
  lrFlowB point.s point.k (Real.sqrt point.chi) *
      lrCompactVQX N point.s point.k point.chi +
    lrCompactVDHead N point.s (point.k ^ 2 * point.chi) *
      lrCompactVPsiHead N point.s point.k point.chi

theorem cast_lrCompactVGroupedLower_le
    {N : ℕ} {box : CertificateBox} {point : CertificatePoint}
    (hbox : LRCompactVBoxValid box) (hpoint : box.Contains point)
    (hinterior : LRCompactVInterior point)
    {b pZero wOne : RationalEnclosure}
    (hb : b.Contains (lrFlowB point.s point.k (Real.sqrt point.chi)))
    (hpZero : pZero.Contains (lrCompactVPZeroX point.k point.chi))
    (hwOne : wOne.Contains (lrWKernel point.s 1)) :
    (lrCompactVGroupedLower N box b pZero wOne : ℝ) ≤
      lrCompactVGroupedX N point := by
  let B := lrFlowB point.s point.k (Real.sqrt point.chi)
  let q := lrCompactVQEnclosure N box pZero wOne
  let Q := lrCompactVQX N point.s point.k point.chi
  have hsqrtPos : 0 < Real.sqrt point.chi := Real.sqrt_pos.2 hinterior.2.2.1
  have hsqrtLt : Real.sqrt point.chi < 1 := by
    simpa using (Real.sqrt_lt_sqrt_iff hinterior.2.2.1.le).2
      hinterior.2.2.2
  have hBPos : 0 < B := by
    dsimp [B]
    apply lrFlowB_pos hinterior.2.1.1 hsqrtPos.le
    have hsqrtR : Real.sqrt point.s < 1 := by
      simpa using (Real.sqrt_lt_sqrt_iff hinterior.1.1.le).2 hinterior.1.2
    have hvt : point.k * Real.sqrt point.chi < 1 := by
      calc
        point.k * Real.sqrt point.chi < 1 * Real.sqrt point.chi :=
          mul_lt_mul_of_pos_right hinterior.2.1.2 hsqrtPos
        _ < 1 := by simpa using hsqrtLt
    calc
      Real.sqrt point.s * point.k * Real.sqrt point.chi <
          1 * point.k * Real.sqrt point.chi := by
        exact mul_lt_mul_of_pos_right
          (mul_lt_mul_of_pos_right hsqrtR hinterior.2.1.1) hsqrtPos
      _ < 1 := by simpa using hvt
  have hq : q.Contains Q :=
    lrCompactVQEnclosure_sound hbox hpoint hpZero hwOne
  have hsigned :
      (lrCompactVSignedProductLower b q : ℝ) ≤ B * Q :=
    cast_lrCompactVSignedProductLower_le hb hq hBPos.le
  have hD := lrCompactVDHeadEnclosure_sound (N := N) hbox hpoint
  have hD0 := lrCompactVDHead_nonneg
    ⟨hinterior.1.1.le, hinterior.1.2.le⟩
    (mul_nonneg (sq_nonneg point.k) hinterior.2.2.1.le) N
  have hPsiLower := lrCompactVPsiPolynomialHead_lower
    (N := N) hbox hpoint hinterior.2.1.1
  have hPsi0 := lrCompactVPsiHead_nonneg
    ⟨hinterior.1.1.le, hinterior.1.2.le⟩
    ⟨hinterior.2.1.1, hinterior.2.1.2.le⟩
    ⟨hinterior.2.2.1.le, hinterior.2.2.2.le⟩ N
  have hDClamp := RationalEnclosure.cast_nonnegativeLower_le hD hD0
  have hPsiClamp :
      ((lrCompactVPsiPolynomialHeadEnclosure N box).nonnegativeLower : ℝ) ≤
        lrCompactVPsiHead N point.s point.k point.chi := by
    change ((max 0
      (lrCompactVPsiPolynomialHeadEnclosure N box).lower : ℚ) : ℝ) ≤ _
    rw [Rat.cast_max, Rat.cast_zero]
    apply max_le
    · exact hPsi0
    · simpa [RationalEnclosure.nonnegativeLower] using hPsiLower
  have hPsiClamp0 :
      (0 : ℝ) ≤
        (lrCompactVPsiPolynomialHeadEnclosure N box).nonnegativeLower := by
    exact_mod_cast RationalEnclosure.nonnegativeLower_nonnegative
      (lrCompactVPsiPolynomialHeadEnclosure N box)
  have hpayment := mul_le_mul hDClamp hPsiClamp hPsiClamp0 hD0
  unfold lrCompactVGroupedLower lrCompactVGroupedX
  dsimp [B, Q, q] at hsigned hpayment ⊢
  norm_num only [Rat.cast_add, Rat.cast_mul]
  exact add_le_add hsigned hpayment

theorem lrCompactVGroupedX_eq_certificateTarget
    {N : ℕ} {point : CertificatePoint}
    (hpoint : LRCompactVInterior point) :
    lrCompactVGroupedX N point = lrCompactVCertificateTarget N point := by
  have hsquare : (Real.sqrt point.chi) ^ 2 = point.chi :=
    Real.sq_sqrt hpoint.2.2.1.le
  have hvsquare : (point.k * Real.sqrt point.chi) ^ 2 =
      point.k ^ 2 * point.chi := by
    rw [mul_pow, hsquare]
  unfold lrCompactVGroupedX lrCompactVCertificateTarget
    lrCompactVFiniteLower lrCompactVQX lrCompactVMx
  rw [hsquare, hvsquare]

/-- A nonnegative rational grouped leaf proves the exact finite target. -/
theorem lrCompactVCertificateTarget_nonnegative_of_groupedLower
    {N : ℕ} {box : CertificateBox} {point : CertificatePoint}
    (hbox : LRCompactVBoxValid box) (hpoint : box.Contains point)
    (hinterior : LRCompactVInterior point)
    {b pZero wOne : RationalEnclosure}
    (hb : b.Contains (lrFlowB point.s point.k (Real.sqrt point.chi)))
    (hpZero : pZero.Contains (lrCompactVPZeroX point.k point.chi))
    (hwOne : wOne.Contains (lrWKernel point.s 1))
    (hlower : 0 ≤ lrCompactVGroupedLower N box b pZero wOne) :
    0 ≤ lrCompactVCertificateTarget N point := by
  rw [← lrCompactVGroupedX_eq_certificateTarget hinterior]
  have hlowerReal :
      (0 : ℝ) ≤ (lrCompactVGroupedLower N box b pZero wOne : ℝ) := by
    exact_mod_cast hlower
  exact hlowerReal.trans <|
    cast_lrCompactVGroupedLower_le hbox hpoint hinterior hb hpZero hwOne

end CourtadeKumar
