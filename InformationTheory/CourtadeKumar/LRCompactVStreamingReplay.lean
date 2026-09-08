import InformationTheory.CourtadeKumar.IntervalSubdivisionSearch
import InformationTheory.CourtadeKumar.LRCompactVReplayLedgerSoundAdapter

/-!
# Streaming replay for the eight historical compact-V slabs

These searches use exactly the existing generators' leaf checks, split rule,
parameters, and fuel. Their Boolean results are proved equal to the old
generate-then-check replays. This provides a smaller-memory execution path
for native experiments while preserving the later kernel-replay target.
No concrete slab is assumed to pass in this module.
-/

namespace CourtadeKumar

def lrCompactVSearchConfig (logTerms pZeroTerms wTerms N logFuel : Nat) :
    SubdivisionSearchConfig LRCompactVLeafCertificate LRCompactVDiscardCertificate where
  acceptData := LRCompactVLeafCertificate.auto logFuel
  discardData := LRCompactVDiscardCertificate.auto logFuel
  acceptCheck := LRCompactVLeafCertificate.check logTerms pZeroTerms wTerms N
  discardCheck := LRCompactVDiscardCertificate.check logTerms
  splitAxis := lrCompactVSplitAxis
  splitCut := lrCompactVSplitCut

def lrCompactVFullDSearchConfig (logTerms pZeroTerms wTerms N logFuel : Nat) :
    SubdivisionSearchConfig LRCompactVFullDLeafCertificate LRCompactVDiscardCertificate where
  acceptData := LRCompactVFullDLeafCertificate.auto logFuel
  discardData := LRCompactVDiscardCertificate.auto logFuel
  acceptCheck := LRCompactVFullDLeafCertificate.check logTerms pZeroTerms wTerms N
  discardCheck := LRCompactVDiscardCertificate.check logTerms
  splitAxis := lrCompactVSplitAxis
  splitCut := lrCompactVSplitCut

def lrCompactVCorrelatedSearchConfig (logTerms pZeroTerms wTerms N logFuel : Nat) :
    SubdivisionSearchConfig LRCompactVCorrelatedLeafCertificate LRCompactVDiscardCertificate where
  acceptData := LRCompactVCorrelatedLeafCertificate.auto logFuel
  discardData := LRCompactVDiscardCertificate.auto logFuel
  acceptCheck := LRCompactVCorrelatedLeafCertificate.check logTerms pZeroTerms wTerms N
  discardCheck := LRCompactVDiscardCertificate.check logTerms
  splitAxis := lrCompactVSplitAxis
  splitCut := lrCompactVSplitCut

theorem lrCompactVSearchConfig_generate
    (logTerms pZeroTerms wTerms N logFuel fuel : Nat) (box : CertificateBox) :
    (lrCompactVSearchConfig logTerms pZeroTerms wTerms N logFuel).generate fuel box =
      generateLRCompactVCertificate logTerms pZeroTerms wTerms N logFuel fuel box := by
  induction fuel generalizing box with
  | zero => rfl
  | succ fuel ih =>
      simp only [lrCompactVSearchConfig] at ih
      simp [SubdivisionSearchConfig.generate, lrCompactVSearchConfig,
        generateLRCompactVCertificate, ih]

theorem lrCompactVFullDSearchConfig_generate
    (logTerms pZeroTerms wTerms N logFuel fuel : Nat) (box : CertificateBox) :
    (lrCompactVFullDSearchConfig logTerms pZeroTerms wTerms N logFuel).generate fuel box =
      generateLRCompactVFullDCertificate logTerms pZeroTerms wTerms N logFuel fuel box := by
  induction fuel generalizing box with
  | zero => rfl
  | succ fuel ih =>
      simp only [lrCompactVFullDSearchConfig] at ih
      simp [SubdivisionSearchConfig.generate, lrCompactVFullDSearchConfig,
        generateLRCompactVFullDCertificate, ih]

theorem lrCompactVCorrelatedSearchConfig_generate
    (logTerms pZeroTerms wTerms N logFuel fuel : Nat) (box : CertificateBox) :
    (lrCompactVCorrelatedSearchConfig logTerms pZeroTerms wTerms N logFuel).generate fuel box =
      generateLRCompactVCorrelatedCertificate logTerms pZeroTerms wTerms N logFuel fuel box := by
  induction fuel generalizing box with
  | zero => rfl
  | succ fuel ih =>
      simp only [lrCompactVCorrelatedSearchConfig] at ih
      simp [SubdivisionSearchConfig.generate, lrCompactVCorrelatedSearchConfig,
        generateLRCompactVCorrelatedCertificate, ih]

theorem lrCompactVSearchConfig_check_eq
    (logTerms pZeroTerms wTerms N logFuel fuel : Nat) (box : CertificateBox) :
    (lrCompactVSearchConfig logTerms pZeroTerms wTerms N logFuel).check fuel box =
      (generateLRCompactVCertificate logTerms pZeroTerms wTerms N logFuel fuel box).check
        (LRCompactVLeafCertificate.check logTerms pZeroTerms wTerms N)
        (LRCompactVDiscardCertificate.check logTerms) box := by
  rw [SubdivisionSearchConfig.check_eq_generated_check, lrCompactVSearchConfig_generate]
  rfl

theorem lrCompactVFullDSearchConfig_check_eq
    (logTerms pZeroTerms wTerms N logFuel fuel : Nat) (box : CertificateBox) :
    (lrCompactVFullDSearchConfig logTerms pZeroTerms wTerms N logFuel).check fuel box =
      (generateLRCompactVFullDCertificate logTerms pZeroTerms wTerms N logFuel fuel box).check
        (LRCompactVFullDLeafCertificate.check logTerms pZeroTerms wTerms N)
        (LRCompactVDiscardCertificate.check logTerms) box := by
  rw [SubdivisionSearchConfig.check_eq_generated_check, lrCompactVFullDSearchConfig_generate]
  rfl

theorem lrCompactVCorrelatedSearchConfig_check_eq
    (logTerms pZeroTerms wTerms N logFuel fuel : Nat) (box : CertificateBox) :
    (lrCompactVCorrelatedSearchConfig logTerms pZeroTerms wTerms N logFuel).check fuel box =
      (generateLRCompactVCorrelatedCertificate logTerms pZeroTerms wTerms N logFuel fuel box).check
        (LRCompactVCorrelatedLeafCertificate.check logTerms pZeroTerms wTerms N)
        (LRCompactVDiscardCertificate.check logTerms) box := by
  rw [SubdivisionSearchConfig.check_eq_generated_check, lrCompactVCorrelatedSearchConfig_generate]
  rfl

end CourtadeKumar
