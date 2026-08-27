import InformationTheory.CourtadeKumar.LRCompactVCorrelatedT

/-!
# Correlation-aware compact `V` interval arithmetic

This module inserts the physical-domain monomial enclosure into the two
places where the audited high-channel certificate needs it: the finite
enhanced-`P_W` error and the complementary coefficients in the `Psi` head.
The resulting enclosures are sound only for physical points, as intended.
-/

namespace CourtadeKumar

/-- Enclosure of `4/(1+v)`, decreasing on the positive compact chart. -/
def lrCompactVFourOverOnePlusVEnclosure
    (box : CertificateBox) : RationalEnclosure :=
  ⟨4 / (1 + box.kHi), 4 / (1 + box.kLo)⟩

theorem lrCompactVFourOverOnePlusVEnclosure_sound
    {box : CertificateBox} {point : CertificatePoint}
    (hbox : LRCompactVBoxValid box) (hpoint : box.Contains point) :
    (lrCompactVFourOverOnePlusVEnclosure box).Contains
      (4 / (1 + point.k)) := by
  have hvLo : (0 : ℝ) ≤ box.kLo := by exact_mod_cast hbox.2.2.2.1
  have hvPoint : (0 : ℝ) ≤ point.k := hvLo.trans hpoint.2.2.1
  have hvHi : (0 : ℝ) ≤ box.kHi := hvPoint.trans hpoint.2.2.2.1
  have hdenLo : 0 < 1 + (box.kLo : ℝ) := by linarith
  have hdenPoint : 0 < 1 + point.k := by linarith
  have hdenHi : 0 < 1 + (box.kHi : ℝ) := by linarith
  constructor
  · change ((4 / (1 + box.kHi) : ℚ) : ℝ) ≤ 4 / (1 + point.k)
    norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_add,
      Rat.cast_one]
    exact div_le_div_of_nonneg_left (by norm_num) hdenPoint
      (by linarith [hpoint.2.2.2.1])
  · change 4 / (1 + point.k) ≤ ((4 / (1 + box.kLo) : ℚ) : ℝ)
    norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_add,
      Rat.cast_one]
    exact div_le_div_of_nonneg_left (by norm_num) hdenLo
      (by linarith [hpoint.2.2.1])

/-- Correlation-aware enclosure of `c_n=4/(1+v)-T_n`. -/
def lrCompactVCorrelatedCEnclosure
    (box : CertificateBox) (n : ℕ) : RationalEnclosure :=
  RationalEnclosure.sub (lrCompactVFourOverOnePlusVEnclosure box)
    (lrCompactVCorrelatedTEnclosure box n)

theorem lrCompactVCorrelatedCEnclosure_sound
    {box : CertificateBox} {point : CertificatePoint}
    (hbox : LRCompactVBoxValid box) (hvLo : (0 : ℚ) < box.kLo)
    (hpoint : box.Contains point) (hphysical : LRCompactVPhysical point)
    (n : ℕ) :
    (lrCompactVCorrelatedCEnclosure box n).Contains
      (lrCompactVC point.k point.chi n) := by
  have hfrac := lrCompactVFourOverOnePlusVEnclosure_sound hbox hpoint
  have hT := lrCompactVCorrelatedTEnclosure_sound
    hbox hvLo hpoint hphysical n
  simpa [lrCompactVCorrelatedCEnclosure, lrCompactVC] using
    RationalEnclosure.contains_sub hfrac hT

/-- One correlation-aware summand in the enhanced `P_W` error. -/
def lrCompactVCorrelatedPWErrorTermEnclosure
    (N : ℕ) (box : CertificateBox) (n : ℕ) : RationalEnclosure :=
  RationalEnclosure.scale (lrLowAQ n) <|
    RationalEnclosure.mul
      (RationalEnclosure.sub
        (lrCompactVScoreEnclosure box (N + 1))
        (lrCompactVScoreEnclosure box n))
      (lrCompactVCorrelatedTEnclosure box n)

theorem lrCompactVCorrelatedPWErrorTermEnclosure_sound
    {N : ℕ} {box : CertificateBox} {point : CertificatePoint}
    (hbox : LRCompactVBoxValid box) (hvLo : (0 : ℚ) < box.kLo)
    (hpoint : box.Contains point) (hphysical : LRCompactVPhysical point)
    {n : ℕ} (hn : 1 ≤ n) :
    (lrCompactVCorrelatedPWErrorTermEnclosure N box n).Contains
      (lrLowA n *
        (lrCompactVScore point.s (N + 1) -
          lrCompactVScore point.s n) *
        lrCompactVT point.k point.chi n) := by
  have hscoreN := lrCompactVScoreEnclosure_sound
    (n := N + 1) (by omega) hbox.1 hbox.2.2.1 hpoint
  have hscore := lrCompactVScoreEnclosure_sound hn
    hbox.1 hbox.2.2.1 hpoint
  have hdiff := RationalEnclosure.contains_sub hscoreN hscore
  have hT := lrCompactVCorrelatedTEnclosure_sound
    hbox hvLo hpoint hphysical n
  have hmul := RationalEnclosure.contains_mul hdiff hT
  have hscale := RationalEnclosure.contains_scale (lrLowAQ n) hmul
  simpa [lrCompactVCorrelatedPWErrorTermEnclosure, mul_assoc] using hscale

/-- Correlation-aware enclosure of the complete finite error `E_N`. -/
def lrCompactVCorrelatedPWErrorEnclosure
    (N : ℕ) (box : CertificateBox) : RationalEnclosure :=
  RationalEnclosure.sumRangeOne
    (lrCompactVCorrelatedPWErrorTermEnclosure N box) N

theorem lrCompactVCorrelatedPWErrorEnclosure_sound
    {N : ℕ} {box : CertificateBox} {point : CertificatePoint}
    (hbox : LRCompactVBoxValid box) (hvLo : (0 : ℚ) < box.kLo)
    (hpoint : box.Contains point) (hphysical : LRCompactVPhysical point) :
    (lrCompactVCorrelatedPWErrorEnclosure N box).Contains
      (lrCompactVPWError N point.s point.k point.chi) := by
  unfold lrCompactVCorrelatedPWErrorEnclosure lrCompactVPWError
  exact RationalEnclosure.contains_sumRangeOne
    (fun n hn => lrCompactVCorrelatedPWErrorTermEnclosure_sound
      hbox hvLo hpoint hphysical hn) N

/-- Correlation-aware enhanced lower expression `w_(N+1) P_0-E_N`. -/
def lrCompactVCorrelatedPWLowerEnclosure
    (N : ℕ) (box : CertificateBox) (pZero : RationalEnclosure) :
    RationalEnclosure :=
  RationalEnclosure.sub
    (RationalEnclosure.mul (lrCompactVScoreEnclosure box (N + 1)) pZero)
    (lrCompactVCorrelatedPWErrorEnclosure N box)

theorem lrCompactVCorrelatedPWLowerEnclosure_sound
    {N : ℕ} {box : CertificateBox} {point : CertificatePoint}
    (hbox : LRCompactVBoxValid box) (hvLo : (0 : ℚ) < box.kLo)
    (hpoint : box.Contains point) (hphysical : LRCompactVPhysical point)
    {pZero : RationalEnclosure}
    (hpZero : pZero.Contains (lrCompactVPZeroX point.k point.chi)) :
    (lrCompactVCorrelatedPWLowerEnclosure N box pZero).Contains
      (lrCompactVScore point.s (N + 1) *
          lrCompactVPZeroX point.k point.chi -
        lrCompactVPWError N point.s point.k point.chi) := by
  have hscore := lrCompactVScoreEnclosure_sound
    (n := N + 1) (by omega) hbox.1 hbox.2.2.1 hpoint
  exact RationalEnclosure.contains_sub
    (RationalEnclosure.contains_mul hscore hpZero)
    (lrCompactVCorrelatedPWErrorEnclosure_sound
      hbox hvLo hpoint hphysical)

/-- Correlation-aware finite `Q` enclosure. -/
def lrCompactVCorrelatedQEnclosure
    (N : ℕ) (box : CertificateBox)
    (pZero wOne : RationalEnclosure) : RationalEnclosure :=
  RationalEnclosure.sub
    (lrCompactVCorrelatedPWLowerEnclosure N box pZero)
    (RationalEnclosure.scale 4 <|
      RationalEnclosure.mul wOne (lrCompactVMxEnclosure box))

theorem lrCompactVCorrelatedQEnclosure_sound
    {N : ℕ} {box : CertificateBox} {point : CertificatePoint}
    (hbox : LRCompactVBoxValid box) (hvLo : (0 : ℚ) < box.kLo)
    (hpoint : box.Contains point) (hphysical : LRCompactVPhysical point)
    {pZero wOne : RationalEnclosure}
    (hpZero : pZero.Contains (lrCompactVPZeroX point.k point.chi))
    (hwOne : wOne.Contains (lrWKernel point.s 1)) :
    (lrCompactVCorrelatedQEnclosure N box pZero wOne).Contains
      (lrCompactVQX N point.s point.k point.chi) := by
  have hpw := lrCompactVCorrelatedPWLowerEnclosure_sound
    (N := N) hbox hvLo hpoint hphysical hpZero
  have hmx := lrCompactVMxEnclosure_sound hbox hpoint
  have hcorrection := RationalEnclosure.contains_scale (4 : ℚ) <|
    RationalEnclosure.contains_mul hwOne hmx
  simpa [lrCompactVCorrelatedQEnclosure, lrCompactVQX,
    lrCompactVPWLower, lrCompactVPZeroX, mul_assoc,
    Real.sq_sqrt hphysical.1.2.2.1.le] using
    RationalEnclosure.contains_sub hpw hcorrection

/-- One correlation-aware summand in the finite polynomial `Psi` head. -/
def lrCompactVCorrelatedPsiTermEnclosure
    (box : CertificateBox) (n : ℕ) : RationalEnclosure :=
  RationalEnclosure.scale (lrLowAQ n) <|
    RationalEnclosure.mul (lrCompactVCorrelatedCEnclosure box n) <|
      RationalEnclosure.sub (RationalEnclosure.point 1)
        (lrCompactVScoreEnclosure box n)

theorem lrCompactVCorrelatedPsiTermEnclosure_sound
    {box : CertificateBox} {point : CertificatePoint}
    (hbox : LRCompactVBoxValid box) (hvLo : (0 : ℚ) < box.kLo)
    (hpoint : box.Contains point) (hphysical : LRCompactVPhysical point)
    {n : ℕ} (hn : 1 ≤ n) :
    (lrCompactVCorrelatedPsiTermEnclosure box n).Contains
      (lrCompactVPsiTerm point.s point.k point.chi n) := by
  have hscore := lrCompactVScoreEnclosure_sound hn
    hbox.1 hbox.2.2.1 hpoint
  have hC := lrCompactVCorrelatedCEnclosure_sound
    hbox hvLo hpoint hphysical n
  have hone : (RationalEnclosure.point 1).Contains (1 : ℝ) := by
    norm_num [RationalEnclosure.point, RationalEnclosure.Contains]
  have hcomp := RationalEnclosure.contains_sub hone hscore
  have hmul := RationalEnclosure.contains_mul hC hcomp
  have hscale := RationalEnclosure.contains_scale (lrLowAQ n) hmul
  simpa [lrCompactVCorrelatedPsiTermEnclosure,
    lrCompactVPsiTerm, mul_assoc] using hscale

/-- Correlation-aware finite polynomial lower enclosure for `Psi`. -/
def lrCompactVCorrelatedPsiPolynomialHeadEnclosure
    (N : ℕ) (box : CertificateBox) : RationalEnclosure :=
  RationalEnclosure.sumRangeOne
    (lrCompactVCorrelatedPsiTermEnclosure box) N

theorem lrCompactVCorrelatedPsiPolynomialHeadEnclosure_sound
    {N : ℕ} {box : CertificateBox} {point : CertificatePoint}
    (hbox : LRCompactVBoxValid box) (hvLo : (0 : ℚ) < box.kLo)
    (hpoint : box.Contains point) (hphysical : LRCompactVPhysical point) :
    (lrCompactVCorrelatedPsiPolynomialHeadEnclosure N box).Contains
      (∑ j ∈ Finset.range N,
        lrCompactVPsiTerm point.s point.k point.chi (j + 1)) := by
  unfold lrCompactVCorrelatedPsiPolynomialHeadEnclosure
  exact RationalEnclosure.contains_sumRangeOne
    (fun n hn => lrCompactVCorrelatedPsiTermEnclosure_sound
      hbox hvLo hpoint hphysical hn) N

theorem lrCompactVCorrelatedPsiPolynomialHead_lower
    {N : ℕ} {box : CertificateBox} {point : CertificatePoint}
    (hbox : LRCompactVBoxValid box) (hvLo : (0 : ℚ) < box.kLo)
    (hpoint : box.Contains point) (hphysical : LRCompactVPhysical point) :
    ((lrCompactVCorrelatedPsiPolynomialHeadEnclosure N box).lower : ℝ) ≤
      lrCompactVPsiHead N point.s point.k point.chi := by
  have hcontains := lrCompactVCorrelatedPsiPolynomialHeadEnclosure_sound
    (N := N) hbox hvLo hpoint hphysical
  have hvLe : point.k ≤ 1 :=
    hpoint.2.2.2.1.trans (by exact_mod_cast hbox.2.2.2.2.2.1)
  have hfzero := lrCompactVFZero_nonneg
    (show point.k ∈ Set.Ioc (0 : ℝ) 1 from
      ⟨hphysical.1.2.1.1, hvLe⟩)
  unfold lrCompactVPsiHead
  linarith [hcontains.1]

end CourtadeKumar
