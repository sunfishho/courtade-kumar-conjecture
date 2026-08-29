import InformationTheory.CourtadeKumar.LRCertificateQSecondMonotonicity
import InformationTheory.CourtadeKumar.LRCertificateQSecondPointEnclosure

/-!
# Endpoint-sharp interval enclosure for the LR certificate curvature

Once monotonicity of `lrCertificateQSecond` is available, checked point
enclosures at the two rational endpoints give a sharper whole-interval
enclosure than evaluating its cancellation-prone algebraic formula over the
entire interval at once.
-/

open Set

namespace CourtadeKumar.LRQSharpSecondEnclosure

def enclosure (terms : ℕ) (input : RationalEnclosure)
    (certificate : LRQPrimeIntervalCertificate) : RationalEnclosure :=
  ⟨(LRQSecondPointEnclosure.pointEnclosure terms input.lower
      certificate.lowerEndpoint).lower,
    (LRQSecondPointEnclosure.pointEnclosure terms input.upper
      certificate.upperEndpoint).upper⟩

theorem enclosure_sound (terms : ℕ)
    {input : RationalEnclosure}
    {certificate : LRQPrimeIntervalCertificate}
    (hcheck : certificate.check input = true)
    {y : ℝ} (hy : input.Contains y) :
    (enclosure terms input certificate).Contains
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
  have hlowerMem : input.lower ∈ Ioo (0 : ℚ) 1 :=
    ⟨hdomain.1, hdomain.2.1.trans_lt hdomain.2.2⟩
  have hupperMem : input.upper ∈ Ioo (0 : ℚ) 1 :=
    ⟨hdomain.1.trans_le hdomain.2.1, hdomain.2.2⟩
  have hlowerCheck :
      LRQSecondPointEnclosure.pointCheck input.lower
        certificate.lowerEndpoint = true := by
    simp [LRQSecondPointEnclosure.pointCheck, hlowerMem, hraw.1.2]
  have hupperCheck :
      LRQSecondPointEnclosure.pointCheck input.upper
        certificate.upperEndpoint = true := by
    simp [LRQSecondPointEnclosure.pointCheck, hupperMem, hraw.2]
  have hlowerPoint := LRQSecondPointEnclosure.pointEnclosure_sound terms
    hlowerCheck
  have hupperPoint := LRQSecondPointEnclosure.pointEnclosure_sound terms
    hupperCheck
  have hlowerMemReal : (input.lower : ℝ) ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · exact_mod_cast hlowerMem.1
    · exact_mod_cast hlowerMem.2
  have hupperMemReal : (input.upper : ℝ) ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · exact_mod_cast hupperMem.1
    · exact_mod_cast hupperMem.2
  have hyMem : y ∈ Ioo (0 : ℝ) 1 :=
    ⟨hlowerMemReal.1.trans_le hy.1, hy.2.trans_lt hupperMemReal.2⟩
  have hlowerMono :
      lrCertificateQSecond (input.lower : ℝ) ≤
        lrCertificateQSecond y :=
    lrCertificateQSecond_monotoneOn hlowerMemReal hyMem hy.1
  have hupperMono :
      lrCertificateQSecond y ≤
        lrCertificateQSecond (input.upper : ℝ) :=
    lrCertificateQSecond_monotoneOn hyMem hupperMemReal hy.2
  exact ⟨hlowerPoint.1.trans hlowerMono,
    hupperMono.trans hupperPoint.2⟩

end CourtadeKumar.LRQSharpSecondEnclosure
