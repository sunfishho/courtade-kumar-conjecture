import InformationTheory.CourtadeKumar.ExactSqrtEnclosureCore
import InformationTheory.CourtadeKumar.IntervalSubdivisionCertificate
import Mathlib.Data.Real.Sqrt

/-!
# Kernel-checked square-root enclosures

An external generator may compute integer square-root endpoints, but Lean
trusts only the rational square inequalities checked here.  This keeps the
integer-square-root implementation outside the trusted base.
-/

namespace CourtadeKumar
namespace RationalEnclosure

theorem SqrtCertificate.sound
    {input : RationalEnclosure} {certificate : SqrtCertificate}
    (hcheck : certificate.check input = true) {x : ℝ}
    (hx : input.Contains x) :
    certificate.enclosure.Contains (Real.sqrt x) := by
  have hrat :
      (0 : ℚ) ≤ input.lower ∧ input.lower ≤ input.upper ∧
      0 ≤ certificate.lower ∧ certificate.lower ^ 2 ≤ input.lower ∧
      0 ≤ certificate.upper ∧ input.upper ≤ certificate.upper ^ 2 := by
    simpa [SqrtCertificate.check] using hcheck
  rcases hrat with ⟨hinput0, _, hlower0, hlowerSq, hupper0, hupperSq⟩
  have hinput0Real : (0 : ℝ) ≤ (input.lower : ℝ) := by
    exact_mod_cast hinput0
  have hx0 : (0 : ℝ) ≤ x := hinput0Real.trans hx.1
  have hlower0Real : (0 : ℝ) ≤ (certificate.lower : ℝ) := by
    exact_mod_cast hlower0
  have hupper0Real : (0 : ℝ) ≤ (certificate.upper : ℝ) := by
    exact_mod_cast hupper0
  have hlowerSqReal :
      (certificate.lower : ℝ) ^ 2 ≤ x := by
    calc
      (certificate.lower : ℝ) ^ 2 ≤ (input.lower : ℝ) := by
        exact_mod_cast hlowerSq
      _ ≤ x := hx.1
  have hupperSqReal :
      x ≤ (certificate.upper : ℝ) ^ 2 := by
    calc
      x ≤ (input.upper : ℝ) := hx.2
      _ ≤ (certificate.upper : ℝ) ^ 2 := by
        exact_mod_cast hupperSq
  constructor
  · exact (Real.le_sqrt hlower0Real hx0).2 hlowerSqReal
  · exact (Real.sqrt_le_iff).2 ⟨hupper0Real, hupperSqReal⟩

end RationalEnclosure
end CourtadeKumar
