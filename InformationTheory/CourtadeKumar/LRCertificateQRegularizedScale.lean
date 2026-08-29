import InformationTheory.CourtadeKumar.LRCertificateQEnclosure

/-!
# Sharp endpoint enclosures for the regularized `Q'` scales

This module proves that both

* `y * Q'(y)`, and
* `sqrt y * Q'(y)`

are increasing on `0 <= y < 1`.  It then gives one certificate payload and
two executable interval evaluators which use checked endpoint evaluations.
The lower endpoint is treated exactly when it is zero, so no evaluation of
the singular expression `Q'(0)` is requested.
-/

open Set

namespace CourtadeKumar

noncomputable def lrCertificateQMulPrime (y : ℝ) : ℝ :=
  y * lrCertificateQPrime y

noncomputable def lrCertificateQSqrtMulPrime (y : ℝ) : ℝ :=
  Real.sqrt y * lrCertificateQPrime y

@[simp] lemma lrCertificateQMulPrime_zero :
    lrCertificateQMulPrime 0 = 0 := by
  simp [lrCertificateQMulPrime]

@[simp] lemma lrCertificateQSqrtMulPrime_zero :
    lrCertificateQSqrtMulPrime 0 = 0 := by
  simp [lrCertificateQSqrtMulPrime]

lemma lrCertificateQPrime_two_mul_second_identity
    {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    lrCertificateQPrime y + 2 * y * lrCertificateQSecond y =
      (Real.artanh (Real.sqrt (1 - y)) - Real.sqrt (1 - y)) /
        (2 * Real.sqrt (1 - y) ^ 3) := by
  let z := Real.sqrt (1 - y)
  have hzPos : 0 < z := Real.sqrt_pos.2 (by linarith [hy.2])
  have hzSq : z ^ 2 = 1 - y := by
    dsimp [z]
    exact Real.sq_sqrt (by linarith [hy.2])
  have hyNe : y ≠ 0 := hy.1.ne'
  have hzNe : z ≠ 0 := hzPos.ne'
  rw [lrCertificateQPrime_eq, lrCertificateQSecond_eq hy]
  change Real.artanh z / (2 * z) +
      2 * y * ((Real.artanh z - z / y) / (4 * z ^ 3)) = _
  calc
    _ = (Real.artanh z * (z ^ 2 + y) - z) / (2 * z ^ 3) := by
      field_simp [hyNe, hzNe]
      ring
    _ = (Real.artanh z - z) / (2 * z ^ 3) := by
      have hsum : z ^ 2 + y = 1 := by linarith [hzSq]
      rw [hsum]
      ring

lemma lrCertificateQPrime_two_mul_second_pos
    {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    0 < lrCertificateQPrime y + 2 * y * lrCertificateQSecond y := by
  let z := Real.sqrt (1 - y)
  have hzPos : 0 < z := Real.sqrt_pos.2 (by linarith [hy.2])
  have hzLt : z < 1 := by
    have harg : 1 - y ∈ Ioo (0 : ℝ) 1 :=
      ⟨by linarith [hy.2], by linarith [hy.1]⟩
    simpa [z] using (Real.sqrt_lt_sqrt_iff harg.1.le).2 harg.2
  rw [lrCertificateQPrime_two_mul_second_identity hy]
  exact div_pos (sub_pos.2 (self_lt_artanh ⟨hzPos, hzLt⟩)) (by positivity)

theorem hasDerivAt_lrCertificateQMulPrime
    {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt lrCertificateQMulPrime
      (lrCertificateQPrime y + y * lrCertificateQSecond y) y := by
  unfold lrCertificateQMulPrime
  convert (hasDerivAt_id y).mul (hasDerivAt_lrCertificateQPrime hy) using 1
  simp only [id_eq, one_mul]

lemma lrCertificateQMulPrime_deriv_pos
    {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    0 < lrCertificateQPrime y + y * lrCertificateQSecond y := by
  have htwo := lrCertificateQPrime_two_mul_second_pos hy
  have hsecond : y * lrCertificateQSecond y ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hy.1.le (lrCertificateQSecond_nonpos hy)
  linarith

theorem lrCertificateQMulPrime_strictMonoOn :
    StrictMonoOn lrCertificateQMulPrime (Ioo (0 : ℝ) 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioo (0 : ℝ) 1)
  · intro y hy
    exact (hasDerivAt_lrCertificateQMulPrime hy).continuousAt.continuousWithinAt
  · intro y hy
    rw [interior_Ioo] at hy
    rw [(hasDerivAt_lrCertificateQMulPrime hy).deriv]
    exact lrCertificateQMulPrime_deriv_pos hy

lemma lrCertificateQMulPrime_nonneg
    {y : ℝ} (hy : y ∈ Ico (0 : ℝ) 1) :
    0 ≤ lrCertificateQMulPrime y := by
  rcases eq_or_lt_of_le hy.1 with rfl | hyPos
  · simp
  · exact mul_nonneg hyPos.le
      (lrCertificateQPrime_pos ⟨hyPos, hy.2⟩).le

theorem lrCertificateQMulPrime_monotoneOn :
    MonotoneOn lrCertificateQMulPrime (Ico (0 : ℝ) 1) := by
  intro a ha b hb hab
  rcases eq_or_lt_of_le ha.1 with rfl | haPos
  · simpa using lrCertificateQMulPrime_nonneg hb
  · exact lrCertificateQMulPrime_strictMonoOn.monotoneOn
      ⟨haPos, ha.2⟩ ⟨haPos.trans_le hab, hb.2⟩ hab

theorem hasDerivAt_lrCertificateQSqrtMulPrime
    {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt lrCertificateQSqrtMulPrime
      ((lrCertificateQPrime y + 2 * y * lrCertificateQSecond y) /
        (2 * Real.sqrt y)) y := by
  have hsqrtPos : 0 < Real.sqrt y := Real.sqrt_pos.2 hy.1
  have hsqrtSq : Real.sqrt y ^ 2 = y := Real.sq_sqrt hy.1.le
  unfold lrCertificateQSqrtMulPrime
  convert (Real.hasDerivAt_sqrt hy.1.ne').mul
    (hasDerivAt_lrCertificateQPrime hy) using 1
  field_simp [hsqrtPos.ne']
  rw [hsqrtSq]
  ring

theorem lrCertificateQSqrtMulPrime_strictMonoOn :
    StrictMonoOn lrCertificateQSqrtMulPrime (Ioo (0 : ℝ) 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioo (0 : ℝ) 1)
  · intro y hy
    exact
      (hasDerivAt_lrCertificateQSqrtMulPrime hy).continuousAt.continuousWithinAt
  · intro y hy
    rw [interior_Ioo] at hy
    rw [(hasDerivAt_lrCertificateQSqrtMulPrime hy).deriv]
    exact div_pos (lrCertificateQPrime_two_mul_second_pos hy)
      (mul_pos (by norm_num) (Real.sqrt_pos.2 hy.1))

lemma lrCertificateQSqrtMulPrime_nonneg
    {y : ℝ} (hy : y ∈ Ico (0 : ℝ) 1) :
    0 ≤ lrCertificateQSqrtMulPrime y := by
  rcases eq_or_lt_of_le hy.1 with rfl | hyPos
  · simp
  · exact mul_nonneg (Real.sqrt_nonneg _)
      (lrCertificateQPrime_pos ⟨hyPos, hy.2⟩).le

theorem lrCertificateQSqrtMulPrime_monotoneOn :
    MonotoneOn lrCertificateQSqrtMulPrime (Ico (0 : ℝ) 1) := by
  intro a ha b hb hab
  rcases eq_or_lt_of_le ha.1 with rfl | haPos
  · simpa using lrCertificateQSqrtMulPrime_nonneg hb
  · exact lrCertificateQSqrtMulPrime_strictMonoOn.monotoneOn
      ⟨haPos, ha.2⟩ ⟨haPos.trans_le hab, hb.2⟩ hab

/-! ## Checked rational endpoint evaluator -/

/-- The existing zero-interval payload supplies the upper endpoint data.
Only a derivative and square-root certificate for the lower endpoint are
new.  Those two fields are ignored when the lower endpoint is zero. -/
structure LRQRegularizedScaleCertificate extends LRQZeroIntervalCertificate where
  lower : LRQPointCertificate
  sqrtLower : RationalEnclosure.SqrtCertificate

namespace LRQRegularizedScaleCertificate

def endpointCheck (terms : ℕ) (y : ℚ) (prime : LRQPointCertificate)
    (sqrt : RationalEnclosure.SqrtCertificate) : Bool :=
  prime.primeCheck y &&
    sqrt.check (RationalEnclosure.point y) &&
    decide ((0 : ℚ) ≤ (prime.primeEnclosure terms).lower)

def check (terms : ℕ) (input : RationalEnclosure)
    (certificate : LRQRegularizedScaleCertificate) : Bool :=
  decide (0 ≤ input.lower ∧ input.lower ≤ input.upper ∧ input.upper < 1) &&
    if input.upper = 0 then true
    else endpointCheck terms input.upper certificate.upper certificate.sqrtUpper &&
      if input.lower = 0 then true
      else endpointCheck terms input.lower certificate.lower certificate.sqrtLower

def mulPrimeEndpointEnclosure (terms : ℕ) (y : ℚ)
    (prime : LRQPointCertificate) : RationalEnclosure :=
  RationalEnclosure.mulNonnegative (RationalEnclosure.point y)
    (prime.primeEnclosure terms)

def sqrtMulPrimeEndpointEnclosure (terms : ℕ)
    (prime : LRQPointCertificate)
    (sqrt : RationalEnclosure.SqrtCertificate) : RationalEnclosure :=
  RationalEnclosure.mulNonnegative sqrt.enclosure
    (prime.primeEnclosure terms)

def mulPrimeEnclosure (terms : ℕ) (input : RationalEnclosure)
    (certificate : LRQRegularizedScaleCertificate) : RationalEnclosure :=
  if input.upper = 0 then RationalEnclosure.point 0
  else
    ⟨if input.lower = 0 then 0
      else (mulPrimeEndpointEnclosure terms input.lower certificate.lower).lower,
      (mulPrimeEndpointEnclosure terms input.upper certificate.upper).upper⟩

def sqrtMulPrimeEnclosure (terms : ℕ) (input : RationalEnclosure)
    (certificate : LRQRegularizedScaleCertificate) : RationalEnclosure :=
  if input.upper = 0 then RationalEnclosure.point 0
  else
    ⟨if input.lower = 0 then 0
      else (sqrtMulPrimeEndpointEnclosure terms certificate.lower
        certificate.sqrtLower).lower,
      (sqrtMulPrimeEndpointEnclosure terms certificate.upper
        certificate.sqrtUpper).upper⟩

private theorem endpointCheck_sound (terms : ℕ) {y : ℚ}
    {prime : LRQPointCertificate}
    {sqrt : RationalEnclosure.SqrtCertificate}
    (hy : y ∈ Ioo (0 : ℚ) 1)
    (hcheck : endpointCheck terms y prime sqrt = true) :
    (prime.primeEnclosure terms).Contains (lrCertificateQPrime (y : ℝ)) ∧
      sqrt.enclosure.Contains (Real.sqrt (y : ℝ)) ∧
      (0 : ℚ) ≤ (prime.primeEnclosure terms).lower ∧
      (0 : ℚ) ≤ sqrt.enclosure.lower := by
  have hraw :
      (prime.primeCheck y = true ∧
        sqrt.check (RationalEnclosure.point y) = true) ∧
        decide ((0 : ℚ) ≤ (prime.primeEnclosure terms).lower) = true := by
    simpa [endpointCheck] using hcheck
  have hsqrtData :
      (0 : ℚ) ≤ (RationalEnclosure.point y).lower ∧
      (RationalEnclosure.point y).lower ≤
        (RationalEnclosure.point y).upper ∧
      (0 : ℚ) ≤ sqrt.lower ∧
      sqrt.lower ^ 2 ≤ (RationalEnclosure.point y).lower ∧
      (0 : ℚ) ≤ sqrt.upper ∧
      (RationalEnclosure.point y).upper ≤ sqrt.upper ^ 2 := by
    simpa [RationalEnclosure.SqrtCertificate.check] using hraw.1.2
  refine ⟨prime.prime_sound terms hy hraw.1.1,
    sqrt.sound hraw.1.2 (RationalEnclosure.contains_point y), ?_, ?_⟩
  · simpa using hraw.2
  · exact hsqrtData.2.2.1

private theorem mulPrimeEndpoint_sound (terms : ℕ) {y : ℚ}
    {prime : LRQPointCertificate}
    {sqrt : RationalEnclosure.SqrtCertificate}
    (hy : y ∈ Ioo (0 : ℚ) 1)
    (hcheck : endpointCheck terms y prime sqrt = true) :
    (mulPrimeEndpointEnclosure terms y prime).Contains
      (lrCertificateQMulPrime (y : ℝ)) := by
  have h := endpointCheck_sound terms hy hcheck
  have hyNonneg : (0 : ℚ) ≤ y := hy.1.le
  simpa [mulPrimeEndpointEnclosure, lrCertificateQMulPrime] using
    RationalEnclosure.contains_mulNonnegative hyNonneg h.2.2.1
      (RationalEnclosure.contains_point y) h.1

private theorem sqrtMulPrimeEndpoint_sound (terms : ℕ) {y : ℚ}
    {prime : LRQPointCertificate}
    {sqrt : RationalEnclosure.SqrtCertificate}
    (hy : y ∈ Ioo (0 : ℚ) 1)
    (hcheck : endpointCheck terms y prime sqrt = true) :
    (sqrtMulPrimeEndpointEnclosure terms prime sqrt).Contains
      (lrCertificateQSqrtMulPrime (y : ℝ)) := by
  have h := endpointCheck_sound terms hy hcheck
  simpa [sqrtMulPrimeEndpointEnclosure, lrCertificateQSqrtMulPrime] using
    RationalEnclosure.contains_mulNonnegative h.2.2.2 h.2.2.1 h.2.1 h.1

private theorem check_parts (terms : ℕ) {input : RationalEnclosure}
    {certificate : LRQRegularizedScaleCertificate}
    (hcheck : certificate.check terms input = true) :
    (0 : ℚ) ≤ input.lower ∧ input.lower ≤ input.upper ∧
      input.upper < 1 ∧
      (if input.upper = 0 then True
       else endpointCheck terms input.upper certificate.upper
          certificate.sqrtUpper = true ∧
        (if input.lower = 0 then True
         else endpointCheck terms input.lower certificate.lower
            certificate.sqrtLower = true)) := by
  have hraw :
      decide (0 ≤ input.lower ∧ input.lower ≤ input.upper ∧ input.upper < 1) =
          true ∧
        (if input.upper = 0 then true
         else endpointCheck terms input.upper certificate.upper certificate.sqrtUpper &&
           if input.lower = 0 then true
           else endpointCheck terms input.lower certificate.lower
             certificate.sqrtLower) = true := by
    simpa [check] using hcheck
  have hdomain :
      (0 : ℚ) ≤ input.lower ∧ input.lower ≤ input.upper ∧
        input.upper < 1 := by
    simpa using hraw.1
  refine ⟨hdomain.1, hdomain.2.1, hdomain.2.2, ?_⟩
  by_cases hu0 : input.upper = 0
  · simp [hu0]
  · simp only [hu0, if_false] at hraw ⊢
    have hpair :
        endpointCheck terms input.upper certificate.upper certificate.sqrtUpper =
            true ∧
          (if input.lower = 0 then true
           else endpointCheck terms input.lower certificate.lower
             certificate.sqrtLower) = true := by
      simpa using hraw.2
    refine ⟨hpair.1, ?_⟩
    by_cases hl0 : input.lower = 0
    · simp [hl0]
    · simpa [hl0] using hpair.2

theorem mulPrime_sound (terms : ℕ) {input : RationalEnclosure}
    {certificate : LRQRegularizedScaleCertificate}
    (hcheck : certificate.check terms input = true)
    {y : ℝ} (hy : input.Contains y) :
    (certificate.mulPrimeEnclosure terms input).Contains
      (lrCertificateQMulPrime y) := by
  have hp := check_parts terms hcheck
  by_cases hu0 : input.upper = 0
  · have hy0 : y = 0 := by
      have hlo : (0 : ℝ) ≤ y := by
        have : (0 : ℝ) ≤ (input.lower : ℝ) := by exact_mod_cast hp.1
        exact this.trans hy.1
      have hup : y ≤ 0 := by simpa [hu0] using hy.2
      linarith
    subst y
    simp [mulPrimeEnclosure, hu0, RationalEnclosure.Contains,
      RationalEnclosure.point]
  · have huPos : (0 : ℚ) < input.upper := by
      exact lt_of_le_of_ne (hp.1.trans hp.2.1) (Ne.symm hu0)
    have huMemQ : input.upper ∈ Ioo (0 : ℚ) 1 := ⟨huPos, hp.2.2.1⟩
    have huMem : (input.upper : ℝ) ∈ Ico (0 : ℝ) 1 := by
      constructor
      · exact_mod_cast huPos.le
      · exact_mod_cast hp.2.2.1
    have hyMem : y ∈ Ico (0 : ℝ) 1 := by
      constructor
      · have hlo : (0 : ℝ) ≤ (input.lower : ℝ) := by
          exact_mod_cast hp.1
        exact hlo.trans hy.1
      · exact hy.2.trans_lt huMem.2
    have hpEndpoints :
        endpointCheck terms input.upper certificate.upper certificate.sqrtUpper =
            true ∧
          (if input.lower = 0 then True
           else endpointCheck terms input.lower certificate.lower
             certificate.sqrtLower = true) := by
      simpa [hu0] using hp.2.2.2
    have hupperEndpoint := mulPrimeEndpoint_sound terms huMemQ hpEndpoints.1
    have hmonoUpper : lrCertificateQMulPrime y ≤
        lrCertificateQMulPrime (input.upper : ℝ) :=
      lrCertificateQMulPrime_monotoneOn hyMem huMem hy.2
    by_cases hl0 : input.lower = 0
    · have hlower : 0 ≤ lrCertificateQMulPrime y :=
        lrCertificateQMulPrime_nonneg hyMem
      exact ⟨by
          simpa [mulPrimeEnclosure, hu0, hl0] using hlower,
        by
          simpa [mulPrimeEnclosure, hu0, hl0] using
            hmonoUpper.trans hupperEndpoint.2⟩
    · have hlPos : (0 : ℚ) < input.lower :=
        lt_of_le_of_ne hp.1 (Ne.symm hl0)
      have hlMemQ : input.lower ∈ Ioo (0 : ℚ) 1 :=
        ⟨hlPos, hp.2.1.trans_lt hp.2.2.1⟩
      have hlMem : (input.lower : ℝ) ∈ Ico (0 : ℝ) 1 := by
        constructor
        · exact_mod_cast hlPos.le
        · exact_mod_cast hp.2.1.trans_lt hp.2.2.1
      have hlowerEndpoint := mulPrimeEndpoint_sound terms hlMemQ
        (by simpa [hl0] using hpEndpoints.2)
      have hmonoLower : lrCertificateQMulPrime (input.lower : ℝ) ≤
          lrCertificateQMulPrime y :=
        lrCertificateQMulPrime_monotoneOn hlMem hyMem hy.1
      exact ⟨by
          simpa [mulPrimeEnclosure, hu0, hl0] using
            hlowerEndpoint.1.trans hmonoLower,
        by
          simpa [mulPrimeEnclosure, hu0, hl0] using
            hmonoUpper.trans hupperEndpoint.2⟩

theorem sqrtMulPrime_sound (terms : ℕ) {input : RationalEnclosure}
    {certificate : LRQRegularizedScaleCertificate}
    (hcheck : certificate.check terms input = true)
    {y : ℝ} (hy : input.Contains y) :
    (certificate.sqrtMulPrimeEnclosure terms input).Contains
      (lrCertificateQSqrtMulPrime y) := by
  have hp := check_parts terms hcheck
  by_cases hu0 : input.upper = 0
  · have hy0 : y = 0 := by
      have hlo : (0 : ℝ) ≤ y := by
        have : (0 : ℝ) ≤ (input.lower : ℝ) := by exact_mod_cast hp.1
        exact this.trans hy.1
      have hup : y ≤ 0 := by simpa [hu0] using hy.2
      linarith
    subst y
    simp [sqrtMulPrimeEnclosure, hu0, RationalEnclosure.Contains,
      RationalEnclosure.point]
  · have huPos : (0 : ℚ) < input.upper := by
      exact lt_of_le_of_ne (hp.1.trans hp.2.1) (Ne.symm hu0)
    have huMemQ : input.upper ∈ Ioo (0 : ℚ) 1 := ⟨huPos, hp.2.2.1⟩
    have huMem : (input.upper : ℝ) ∈ Ico (0 : ℝ) 1 := by
      constructor
      · exact_mod_cast huPos.le
      · exact_mod_cast hp.2.2.1
    have hyMem : y ∈ Ico (0 : ℝ) 1 := by
      constructor
      · have hlo : (0 : ℝ) ≤ (input.lower : ℝ) := by
          exact_mod_cast hp.1
        exact hlo.trans hy.1
      · exact hy.2.trans_lt huMem.2
    have hpEndpoints :
        endpointCheck terms input.upper certificate.upper certificate.sqrtUpper =
            true ∧
          (if input.lower = 0 then True
           else endpointCheck terms input.lower certificate.lower
             certificate.sqrtLower = true) := by
      simpa [hu0] using hp.2.2.2
    have hupperEndpoint := sqrtMulPrimeEndpoint_sound terms huMemQ hpEndpoints.1
    have hmonoUpper : lrCertificateQSqrtMulPrime y ≤
        lrCertificateQSqrtMulPrime (input.upper : ℝ) :=
      lrCertificateQSqrtMulPrime_monotoneOn hyMem huMem hy.2
    by_cases hl0 : input.lower = 0
    · have hlower : 0 ≤ lrCertificateQSqrtMulPrime y :=
        lrCertificateQSqrtMulPrime_nonneg hyMem
      exact ⟨by
          simpa [sqrtMulPrimeEnclosure, hu0, hl0] using hlower,
        by
          simpa [sqrtMulPrimeEnclosure, hu0, hl0] using
            hmonoUpper.trans hupperEndpoint.2⟩
    · have hlPos : (0 : ℚ) < input.lower :=
        lt_of_le_of_ne hp.1 (Ne.symm hl0)
      have hlMemQ : input.lower ∈ Ioo (0 : ℚ) 1 :=
        ⟨hlPos, hp.2.1.trans_lt hp.2.2.1⟩
      have hlMem : (input.lower : ℝ) ∈ Ico (0 : ℝ) 1 := by
        constructor
        · exact_mod_cast hlPos.le
        · exact_mod_cast hp.2.1.trans_lt hp.2.2.1
      have hlowerEndpoint := sqrtMulPrimeEndpoint_sound terms hlMemQ
        (by simpa [hl0] using hpEndpoints.2)
      have hmonoLower :
          lrCertificateQSqrtMulPrime (input.lower : ℝ) ≤
            lrCertificateQSqrtMulPrime y :=
        lrCertificateQSqrtMulPrime_monotoneOn hlMem hyMem hy.1
      exact ⟨by
          simpa [sqrtMulPrimeEnclosure, hu0, hl0] using
            hlowerEndpoint.1.trans hmonoLower,
        by
          simpa [sqrtMulPrimeEnclosure, hu0, hl0] using
            hmonoUpper.trans hupperEndpoint.2⟩

end LRQRegularizedScaleCertificate

end CourtadeKumar
