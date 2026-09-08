import InformationTheory.CourtadeKumar.IntervalSubdivisionCertificateCore

/-!
# Streaming checks for deterministic subdivision searches

`check` computes the result of generating a certificate and checking it,
without retaining the entire tree or repeating successful leaf checks.
The equality with the existing certificate checker is proved in Lean.
The same Boolean can be checked by kernel reduction or by `native_decide`;
the structural equivalence itself does not trust native computation.
-/

namespace CourtadeKumar

structure SubdivisionSearchConfig (AcceptData DiscardData : Type) where
  acceptData : CertificateBox → AcceptData
  discardData : CertificateBox → DiscardData
  acceptCheck : CertificateBox → AcceptData → Bool
  discardCheck : CertificateBox → DiscardData → Bool
  splitAxis : CertificateBox → CertificateAxis
  splitCut : CertificateBox → CertificateAxis → ℚ

namespace SubdivisionSearchConfig

variable {AcceptData DiscardData : Type}

/-- The usual candidate tree, including a checked acceptance leaf at zero fuel. -/
def generate (config : SubdivisionSearchConfig AcceptData DiscardData) :
    Nat → CertificateBox → SubdivisionCertificate AcceptData DiscardData
  | 0, box => .accept (config.acceptData box)
  | fuel + 1, box =>
      let discard := config.discardData box
      if config.discardCheck box discard then .discard discard
      else
        let accept := config.acceptData box
        if config.acceptCheck box accept then .accept accept
        else
          let axis := config.splitAxis box
          let cut := config.splitCut box axis
          .split axis cut
            (config.generate fuel (box.lower axis cut))
            (config.generate fuel (box.upper axis cut))

/-- Depth-first replay with memory proportional to search depth.
Exhausting fuel still runs the acceptance checker; it never implies success. -/
def check (config : SubdivisionSearchConfig AcceptData DiscardData) :
    Nat → CertificateBox → Bool
  | 0, box => config.acceptCheck box (config.acceptData box)
  | fuel + 1, box =>
      if config.discardCheck box (config.discardData box) then true
      else if config.acceptCheck box (config.acceptData box) then true
      else
        let axis := config.splitAxis box
        let cut := config.splitCut box axis
        config.check fuel (box.lower axis cut) &&
          config.check fuel (box.upper axis cut)

/-- Streaming changes evaluation cost, not the certificate accepted. -/
theorem check_eq_generated_check
    (config : SubdivisionSearchConfig AcceptData DiscardData)
    (fuel : Nat) (box : CertificateBox) :
    config.check fuel box =
      (config.generate fuel box).check config.acceptCheck config.discardCheck box := by
  induction fuel generalizing box with
  | zero => rfl
  | succ fuel ih =>
      by_cases hd : config.discardCheck box (config.discardData box) = true
      · simp [check, generate, hd, SubdivisionCertificate.check]
      · by_cases ha : config.acceptCheck box (config.acceptData box) = true
        · simp [check, generate, hd, ha, SubdivisionCertificate.check]
        · simp [check, generate, hd, ha, SubdivisionCertificate.check, ih]

end SubdivisionSearchConfig

end CourtadeKumar
