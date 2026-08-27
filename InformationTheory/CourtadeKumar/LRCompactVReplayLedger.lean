import InformationTheory.CourtadeKumar.LRCompactVFullDGeneratedCertificate

/-!
# Compact replay ledger through `R=17/20`

This file records the three Boolean replay obligations corresponding to the
first three audited channel slabs and assembles them into one analytic `V`
theorem.  The obligations are intentionally explicit: no successful replay
is assumed merely because an external script reported one.
-/

namespace CourtadeKumar

def lrCompactVR34Generated := generateLRCompactVCertificate
  34 32 72 32 16 38 lrCompactVR34Root

def lrCompactVR34Replay : Prop :=
  lrCompactVR34Generated.check
    (LRCompactVLeafCertificate.check 34 32 72 32)
    (LRCompactVDiscardCertificate.check 34)
    lrCompactVR34Root = true

def lrCompactVR34R1316Generated := generateLRCompactVFullDCertificate
  34 64 72 64 16 28 lrCompactVR34R1316Root

def lrCompactVR34R1316Replay : Prop :=
  lrCompactVR34R1316Generated.check
    (LRCompactVFullDLeafCertificate.check 34 64 72 64)
    (LRCompactVDiscardCertificate.check 34)
    lrCompactVR34R1316Root = true

def lrCompactVR1316R1720Generated := generateLRCompactVFullDCertificate
  34 48 72 48 16 31 lrCompactVR1316R1720Root

def lrCompactVR1316R1720Replay : Prop :=
  lrCompactVR1316R1720Generated.check
    (LRCompactVFullDLeafCertificate.check 34 48 72 48)
    (LRCompactVDiscardCertificate.check 34)
    lrCompactVR1316R1720Root = true

structure LRCompactVR1720ReplayLedger : Prop where
  r34 : lrCompactVR34Replay
  r34_r1316 : lrCompactVR34R1316Replay
  r1316_r1720 : lrCompactVR1316R1720Replay

theorem LRCompactVR1720ReplayLedger.v_nonnegative
    (ledger : LRCompactVR1720ReplayLedger) :
    ∀ (R v t : ℝ),
      R ∈ Set.Ioo (0 : ℝ) 1 → R ≤ 17 / 20 →
      v ∈ Set.Ioo (0 : ℝ) 1 → 1 / 3 ≤ v →
      t ∈ Set.Ioo (0 : ℝ) 1 → 17 / 20 ≤ t ^ 2 →
      0 < lrFlowJ R v t →
      0 ≤ lrLowVReserve R v t := by
  intro R v t hR hRUpper hv hvLower ht htLower hJ
  by_cases hR34 : R ≤ 3 / 4
  · exact generatedLRCompactVR34_sound
      34 32 72 32 16 38 ledger.r34
      R v t hR hR34 hv hvLower ht htLower hJ
  by_cases hR1316 : R ≤ 13 / 16
  · exact generatedLRCompactVFullDSlab_sound
      34 64 72 64 16 28 (3 / 4) (13 / 16)
      ledger.r34_r1316 R v t hR (by norm_num; linarith)
      (by norm_num at hR1316 ⊢; exact hR1316)
      hv hvLower ht htLower hJ
  · exact generatedLRCompactVFullDSlab_sound
      34 48 72 48 16 31 (13 / 16) (17 / 20)
      ledger.r1316_r1720 R v t hR (by norm_num; linarith)
      (by norm_num at hRUpper ⊢; exact hRUpper)
      hv hvLower ht htLower hJ

end CourtadeKumar
