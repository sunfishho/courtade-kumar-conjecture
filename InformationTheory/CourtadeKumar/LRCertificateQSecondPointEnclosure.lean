import InformationTheory.CourtadeKumar.LRCertificateQEnclosure

open Set

namespace CourtadeKumar.LRQSecondPointEnclosure

/-- Algebraic form of `Q''` using only `Q'` and rational operations. -/
lemma qSecond_eq_prime {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    lrCertificateQSecond y =
      (2 * lrCertificateQPrime y - 1 / y) / (4 * (1 - y)) := by
  let z := Real.sqrt (1 - y)
  have hzPos : 0 < z := Real.sqrt_pos.2 (by linarith [hy.2])
  have hzSq : z ^ 2 = 1 - y := by
    dsimp [z]
    exact Real.sq_sqrt (by linarith [hy.2])
  rw [lrCertificateQSecond_eq hy, lrCertificateQPrime_eq]
  change (Real.artanh z - z / y) / (4 * z ^ 3) =
    (2 * (Real.artanh z / (2 * z)) - 1 / y) / (4 * (1 - y))
  rw [← hzSq]
  field_simp [hy.1.ne', hzPos.ne']

def pointCheck (y : ℚ) (certificate : LRQPointCertificate) : Bool :=
  decide (y ∈ Set.Ioo (0 : ℚ) 1) && certificate.primeCheck y

def pointEnclosure (terms : ℕ) (y : ℚ)
    (certificate : LRQPointCertificate) : RationalEnclosure :=
  let numerator := RationalEnclosure.sub
    (RationalEnclosure.scale 2 (certificate.primeEnclosure terms))
    (RationalEnclosure.point (1 / y))
  RationalEnclosure.scale (1 / 4)
    (RationalEnclosure.div numerator
      (RationalEnclosure.point (1 - y)))

theorem pointEnclosure_sound (terms : ℕ) {y : ℚ}
    {certificate : LRQPointCertificate}
    (hcheck : pointCheck y certificate = true) :
    (pointEnclosure terms y certificate).Contains
      (lrCertificateQSecond (y : ℝ)) := by
  have hparts : decide (y ∈ Set.Ioo (0 : ℚ) 1) = true ∧
      certificate.primeCheck y = true := by
    simpa [pointCheck] using hcheck
  have hyRat : y ∈ Set.Ioo (0 : ℚ) 1 := by
    simpa using hparts.1
  have hy : (y : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := by
    exact ⟨by exact_mod_cast hyRat.1, by exact_mod_cast hyRat.2⟩
  have hprime := certificate.prime_sound terms hyRat hparts.2
  have htwo := RationalEnclosure.contains_scale 2 hprime
  have hinv : (RationalEnclosure.point (1 / y)).Contains
      (1 / (y : ℝ)) := by
    simpa using RationalEnclosure.contains_point (1 / y)
  have hnumerator := RationalEnclosure.contains_sub htwo hinv
  have hdenom : (RationalEnclosure.point (1 - y)).Contains
      (1 - (y : ℝ)) := by
    simpa using RationalEnclosure.contains_point (1 - y)
  have hdenomPositive : (0 : ℚ) <
      (RationalEnclosure.point (1 - y)).lower := by
    simpa [RationalEnclosure.point] using sub_pos.mpr hyRat.2
  have hquot := RationalEnclosure.contains_div hdenomPositive
    hnumerator hdenom
  have hscaled := RationalEnclosure.contains_scale (1 / 4) hquot
  rw [qSecond_eq_prime hy]
  convert hscaled using 1
  field_simp [hy.1.ne', sub_ne_zero.mpr hy.2.ne]
  ring

/-- A tighter whole-interval `Q''` enclosure that reuses the checked
interval for `Q'` and the identity from `qSecond_eq_prime`.  Unlike the
universal `[-1/(4*lower),0]` bound, it retains the strong cancellation in
the upper-K derivative calculation. -/
def intervalEnclosure (terms : ℕ) (input : RationalEnclosure)
    (certificate : LRQPrimeIntervalCertificate) : RationalEnclosure :=
  let numerator := RationalEnclosure.sub
    (RationalEnclosure.scale 2 (certificate.enclosure terms))
    (RationalEnclosure.invPositive input)
  let oneMinus := RationalEnclosure.sub (RationalEnclosure.point 1) input
  let denominator := RationalEnclosure.mulNonnegative
    (RationalEnclosure.point 4) oneMinus
  RationalEnclosure.div numerator denominator

theorem intervalEnclosure_sound (terms : ℕ)
    {input : RationalEnclosure}
    {certificate : LRQPrimeIntervalCertificate}
    (hcheck : certificate.check input = true)
    {y : ℝ} (hy : input.Contains y) :
    (intervalEnclosure terms input certificate).Contains
      (lrCertificateQSecond y) := by
  have hraw :
      (decide ((0 : ℚ) < input.lower ∧
          input.lower ≤ input.upper ∧ input.upper < 1) = true ∧
        certificate.lowerEndpoint.primeCheck input.lower = true) ∧
      certificate.upperEndpoint.primeCheck input.upper = true := by
    simpa [LRQPrimeIntervalCertificate.check] using hcheck
  have hdomain : (0 : ℚ) < input.lower ∧
      input.lower ≤ input.upper ∧ input.upper < 1 := by
    simpa using hraw.1.1
  have hyReal : y ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · have hlo : (0 : ℝ) < (input.lower : ℝ) := by
        exact_mod_cast hdomain.1
      exact hlo.trans_le hy.1
    · have hup : (input.upper : ℝ) < 1 := by
        exact_mod_cast hdomain.2.2
      exact hy.2.trans_lt hup
  have hprime := certificate.sound terms hcheck hy
  have htwo := RationalEnclosure.contains_scale 2 hprime
  have hinv := RationalEnclosure.contains_invPositive hdomain.1 hy
  have hnumerator := RationalEnclosure.contains_sub htwo hinv
  let oneMinus := RationalEnclosure.sub (RationalEnclosure.point 1) input
  have honeMinus := RationalEnclosure.contains_sub
    (RationalEnclosure.contains_point 1) hy
  have honeMinusLower : (0 : ℚ) ≤ oneMinus.lower := by
    dsimp [oneMinus]
    simp [RationalEnclosure.sub, RationalEnclosure.add,
      RationalEnclosure.neg, RationalEnclosure.point]
    exact hdomain.2.2.le
  let denominator := RationalEnclosure.mulNonnegative
    (RationalEnclosure.point 4) oneMinus
  have hdenominator := RationalEnclosure.contains_mulNonnegative
    (show (0 : ℚ) ≤ (RationalEnclosure.point 4).lower by
      norm_num [RationalEnclosure.point])
    honeMinusLower (RationalEnclosure.contains_point 4) honeMinus
  have hdenominatorPositive : (0 : ℚ) < denominator.lower := by
    dsimp [denominator, oneMinus]
    simp [RationalEnclosure.mulNonnegative, RationalEnclosure.sub,
      RationalEnclosure.add, RationalEnclosure.neg,
      RationalEnclosure.point]
    exact hdomain.2.2
  have hresult := RationalEnclosure.contains_div hdenominatorPositive
    hnumerator hdenominator
  rw [qSecond_eq_prime hyReal]
  convert hresult using 1 <;>
    simp [intervalEnclosure, oneMinus, denominator] <;>
    field_simp [hyReal.1.ne', sub_ne_zero.mpr hyReal.2.ne] <;> ring

end CourtadeKumar.LRQSecondPointEnclosure
