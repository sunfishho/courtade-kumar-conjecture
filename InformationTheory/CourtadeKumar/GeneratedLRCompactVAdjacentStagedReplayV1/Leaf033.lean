import InformationTheory.CourtadeKumar.GeneratedLRCompactVAdjacentStagedReplayV1.Config

set_option autoImplicit false

namespace CourtadeKumar
namespace GeneratedLRCompactVAdjacentStagedReplayV1

def leaf033Data : LRCompactVStagedGroupedLeafCertificate :=
  .sameY
    { logOnePlusVHi := { exponent := 0, mantissa := ((251 : ℚ) / 128) }
      headChoice := .n128 }

#kernel_checked_bool leaf033Check
  (leaf033Data.check logTerms pZeroTerms wTerms dTerms directN box_rRLRRRR)

def leaf033Checked : CheckedTree box_rRLRRRR :=
  LRCompactVStagedGroupedCheckedTree.ofAccept
    logTerms pZeroTerms wTerms dTerms directN
    leaf033Data leaf033Check

end GeneratedLRCompactVAdjacentStagedReplayV1
end CourtadeKumar
