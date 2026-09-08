import InformationTheory.CourtadeKumar.LRCompactVSoundLedger
import InformationTheory.CourtadeKumar.LRCompactVCorrelatedReplayLedger

/-! Backward-compatible adapter from the historical replay-specific ledger. -/

namespace CourtadeKumar

def LRCompactVR910ReplayLedger.toSoundLedger
    (ledger : LRCompactVR910ReplayLedger) : LRCompactVSoundLedger where
  v_nonnegative := ledger.v_nonnegative

instance : Coe LRCompactVR910ReplayLedger LRCompactVSoundLedger where
  coe := LRCompactVR910ReplayLedger.toSoundLedger

end CourtadeKumar
