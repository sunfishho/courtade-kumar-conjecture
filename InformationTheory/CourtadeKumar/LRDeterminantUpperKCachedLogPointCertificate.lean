import InformationTheory.CourtadeKumar.LRDeterminantUpperKPointSoundCore
import InformationTheory.CourtadeKumar.LRDeterminantUpperKDyadicOuterRoundingCore

/-!
# Point certificates with cached logarithm enclosures

Generated upper-`K` point certificates serialize small dyadic outer bounds for
the two logarithm enclosures used by both `Q` and `Q'`.  Authenticating each
bound once keeps the logarithm series from being recomputed independently by
the two scalar formulas.  The data are still untrusted: generated modules
prove the two relations in `LogValues.Covers` by ordinary kernel reduction and
the verified outward-rounding theorem.
-/

namespace CourtadeKumar
namespace LRUpperKCachedLogPointCertificate

open Set
open LRUpperKMidpointCoarsening

abbrev Values := LRUpperKPointCache.Values
abbrev Sound := LRUpperKPointCache.Sound

abbrev LogValues := LRUpperKCachedLogPointCore.LogValues

/-- Kernel-authenticated outer containment of the logarithm enclosures
computed from a point certificate. -/
structure LogValues.Covers (terms : ℕ) (certificate : LRQPointCertificate)
    (values : LogValues) : Prop where
  lower : LRUpperKMidpointCoarsening.Covers values.lower
    (certificate.logLowerProbability.enclosure terms)
  upper : LRUpperKMidpointCoarsening.Covers values.upper
    (certificate.logUpperProbability.enclosure terms)

abbrev rawValues := LRUpperKCachedLogPointCore.rawValues

abbrev outerValues := LRUpperKCachedLogPointCore.outerValues

/-- Cached outer logarithm values preserve both semantic point enclosures. -/
theorem rawValues_sound (terms : ℕ) {z : ℚ}
    {certificate : LRQPointCertificate} {logs : LogValues}
    (hz : z ∈ Ioo (0 : ℚ) 1)
    (hcheck : certificate.primeCheck z = true)
    (hlogs : logs.Covers terms certificate) :
    Sound terms z (rawValues certificate logs) := by
  have hparts : certificate.check z = true ∧
      (0 : ℚ) < certificate.sqrtEnclosure.lower := by
    simpa [LRQPointCertificate.primeCheck] using hcheck
  have hcheckParts :
      certificate.sqrtOneSub.check (LRQPointCertificate.sqrtInput z) = true ∧
      certificate.logLowerProbability.check
          certificate.lowerProbability = true ∧
      certificate.logUpperProbability.check
          certificate.upperProbability = true := by
    have hraw :
        (certificate.sqrtOneSub.check
              (LRQPointCertificate.sqrtInput z) = true ∧
          certificate.logLowerProbability.check
              certificate.lowerProbability = true) ∧
        certificate.logUpperProbability.check
            certificate.upperProbability = true := by
      simpa [LRQPointCertificate.check] using hparts.1
    exact ⟨hraw.1.1, hraw.1.2, hraw.2⟩
  have hsqrtInput : (LRQPointCertificate.sqrtInput z).Contains
      (1 - (z : ℝ)) := by
    simpa [LRQPointCertificate.sqrtInput] using
      RationalEnclosure.contains_point (1 - z)
  have hsqrt := certificate.sqrtOneSub.sound hcheckParts.1 hsqrtInput
  have hlower : certificate.lowerProbability.Contains
      ((1 - Real.sqrt (1 - (z : ℝ))) / 2) := by
    have hsub := RationalEnclosure.contains_sub
      (RationalEnclosure.contains_point (1 : ℚ)) hsqrt
    have hscale := RationalEnclosure.contains_scale (1 / 2 : ℚ) hsub
    simpa [LRQPointCertificate.lowerProbability,
      LRQPointCertificate.sqrtEnclosure, div_eq_mul_inv, mul_comm] using hscale
  have hupper : certificate.upperProbability.Contains
      ((1 + Real.sqrt (1 - (z : ℝ))) / 2) := by
    have hadd := RationalEnclosure.contains_add
      (RationalEnclosure.contains_point (1 : ℚ)) hsqrt
    have hscale := RationalEnclosure.contains_scale (1 / 2 : ℚ) hadd
    simpa [LRQPointCertificate.upperProbability,
      LRQPointCertificate.sqrtEnclosure, div_eq_mul_inv, mul_comm] using hscale
  have hlogLowerExact := certificate.logLowerProbability.sound terms
    hcheckParts.2.1 hlower
  have hlogUpperExact := certificate.logUpperProbability.sound terms
    hcheckParts.2.2 hupper
  have hlogLower := contains_of_covers hlogs.lower hlogLowerExact
  have hlogUpper := contains_of_covers hlogs.upper hlogUpperExact
  refine { q := ?_, qPrime := ?_ }
  · have hfirst := RationalEnclosure.contains_mul hlower hlogLower
    have hsecond := RationalEnclosure.contains_mul hupper hlogUpper
    have hsum := RationalEnclosure.contains_add hfirst hsecond
    have hneg := RationalEnclosure.contains_neg hsum
    have hidentity :
        -(((1 - Real.sqrt (1 - (z : ℝ))) / 2) *
            Real.log ((1 - Real.sqrt (1 - (z : ℝ))) / 2) +
          ((1 + Real.sqrt (1 - (z : ℝ))) / 2) *
            Real.log ((1 + Real.sqrt (1 - (z : ℝ))) / 2)) =
          lrCertificateQ (z : ℝ) := by
      unfold lrCertificateQ
      rw [topJ_eq_binEntropy, Real.binEntropy, Real.log_inv, Real.log_inv]
      ring_nf
    simpa [rawValues, hidentity] using hneg
  · have hlogDiff := RationalEnclosure.contains_sub hlogUpper hlogLower
    have hquot := RationalEnclosure.contains_div hparts.2 hlogDiff hsqrt
    have hscaled := RationalEnclosure.contains_scale (1 / 4 : ℚ) hquot
    let root := Real.sqrt (1 - (z : ℝ))
    have hrootPos : 0 < root :=
      Real.sqrt_pos.2 (by exact_mod_cast sub_pos.mpr hz.2)
    have hrootLt : root < 1 := by
      have harg : (1 - (z : ℝ)) ∈ Ioo (0 : ℝ) 1 := by
        have hargRat : (1 - z : ℚ) ∈ Ioo 0 1 := by
          constructor <;> linarith [hz.1, hz.2]
        constructor
        · exact_mod_cast hargRat.1
        · exact_mod_cast hargRat.2
      simpa [root] using (Real.sqrt_lt_sqrt_iff harg.1.le).2 harg.2
    have hpNe : (1 - root) / 2 ≠ 0 := by nlinarith
    have hqNe : (1 + root) / 2 ≠ 0 := by nlinarith
    have hlogIdentity :
        Real.log ((1 + root) / 2) - Real.log ((1 - root) / 2) =
          2 * Real.artanh root := by
      rw [Real.artanh_eq_half_log ⟨by linarith, hrootLt.le⟩]
      rw [← Real.log_div hqNe hpNe]
      field_simp
    have hvalue :
        (1 / 4 : ℝ) *
            ((Real.log ((1 + root) / 2) - Real.log ((1 - root) / 2)) /
              root) =
          lrCertificateQPrime (z : ℝ) := by
      rw [lrCertificateQPrime_eq]
      change (1 / 4 : ℝ) *
          ((Real.log ((1 + root) / 2) - Real.log ((1 - root) / 2)) /
            root) = Real.artanh root / (2 * root)
      rw [hlogIdentity]
      field_simp [hrootPos.ne']
      ring
    dsimp [root] at hvalue
    rw [← hvalue]
    simpa [LRUpperKCachedLogPointCore.rawValues] using hscaled

/-- Outward dyadic rounding preserves both semantic point enclosures. -/
theorem outerValues_sound (bits terms : ℕ) {z : ℚ} {values : Values}
    (hvalues : Sound terms z values) :
    Sound terms z (outerValues bits values) := by
  exact
    { q := contains_of_covers
        (LRUpperKDyadicOuterRounding.outerEnclosure_covers bits values.q)
        hvalues.q
      qPrime := contains_of_covers
        (LRUpperKDyadicOuterRounding.outerEnclosure_covers bits values.qPrime)
        hvalues.qPrime }

/-- One-step semantic constructor used by generated literal point entries. -/
theorem sound (bits terms : ℕ) {z : ℚ}
    {certificate : LRQPointCertificate} {logs : LogValues}
    (hz : z ∈ Ioo (0 : ℚ) 1)
    (hcheck : certificate.primeCheck z = true)
    (hlogs : logs.Covers terms certificate) :
    Sound terms z (outerValues bits (rawValues certificate logs)) :=
  outerValues_sound bits terms (rawValues_sound terms hz hcheck hlogs)

end LRUpperKCachedLogPointCertificate
end CourtadeKumar
