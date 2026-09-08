import InformationTheory.CourtadeKumar.LRSmallSBridgeCoreIntervalCore

/-!
# Flat topology for the rounded small-s wide-log replay

Generated V2 assemblies name every leaf and internal-node box literally.  This
keeps exact rational arithmetic out of long nested subdivision paths: each
internal theorem checks only the two immediate child bindings, then combines
the already-proved child propositions.

Components expose soundness at their literal root box.  A single equality
transport attaches that root to the corresponding boundary box in an enclosing
topology.
-/

namespace CourtadeKumar
namespace LRSmallSWideLogRoundedFlatTopology

/-- The proposition exported by every rounded leaf and flat component. -/
abbrev Sound (box : CertificateBox) : Prop :=
  ∀ point, box.Contains point →
    (2 / 3 : ℝ) < lrSmallSBridgeCoreTarget point

/-- A small-s root with variable `k` endpoints and the fixed full `chi` range.

Keeping this constructor here lets the final V2 assembly avoid importing the
historical auto-tree solely to name its four top-level boxes.
-/
def rootBox (kLo kHi : ℚ) : CertificateBox :=
  { sLo := 0, sHi := 1 / 16384
    kLo := kLo, kHi := kHi
    chiLo := 0, chiHi := 1 }

/-- Package coordinate-wise interval hypotheses as membership in `rootBox`. -/
theorem rootBox_contains
    {s k chi : ℝ} {kLo kHi : ℚ}
    (hs : s ∈ Set.Icc (0 : ℝ) (1 / 16384))
    (hk : k ∈ Set.Icc (kLo : ℝ) (kHi : ℝ))
    (hchi : chi ∈ Set.Icc (0 : ℝ) 1) :
    (rootBox kLo kHi).Contains ⟨s, k, chi⟩ := by
  have h : (0 : ℝ) ≤ s ∧ s ≤ 1 / 16384 ∧
      (kLo : ℝ) ≤ k ∧ k ≤ (kHi : ℝ) ∧
      (0 : ℝ) ≤ chi ∧ chi ≤ 1 :=
    ⟨hs.1, hs.2, hk.1, hk.2, hchi.1, hchi.2⟩
  simpa [rootBox, CertificateBox.Contains] using h

/-- Combine one literal parent with its two literal children.

The two bindings are intentionally local to this split.  Thus a generated
assembly never normalizes a child through the complete path from a global root.
-/
theorem sound_of_literal_split
    (parent lower upper : CertificateBox)
    (axis : CertificateAxis) (cut : ℚ)
    (lowerBinding : parent.lower axis cut = lower)
    (upperBinding : parent.upper axis cut = upper)
    (lowerSound : Sound lower)
    (upperSound : Sound upper) :
    Sound parent := by
  subst lower
  subst upper
  intro point hpoint
  rcases parent.contains_lower_or_upper hpoint axis cut with hLower | hUpper
  · exact lowerSound point hLower
  · exact upperSound point hUpper

/-- Attach a component's literal root theorem to an enclosing boundary box.

This is the only transport needed at a component boundary; the potentially
long boundary expression occurs in the equality proof, not in any leaf or
internal split theorem.
-/
theorem sound_of_box_eq {source target : CertificateBox}
    (binding : source = target) (sound : Sound target) :
    Sound source := by
  subst target
  exact sound

end LRSmallSWideLogRoundedFlatTopology
end CourtadeKumar
