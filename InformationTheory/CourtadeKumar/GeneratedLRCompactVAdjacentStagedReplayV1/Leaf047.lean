import InformationTheory.CourtadeKumar.GeneratedLRCompactVAdjacentStagedReplayV1.Config

set_option autoImplicit false

namespace CourtadeKumar
namespace GeneratedLRCompactVAdjacentStagedReplayV1

def leaf047Data : LRCompactVStagedGroupedLeafCertificate :=
  .sameY
    { logOnePlusVHi := { exponent := 0, mantissa := ((503 : ℚ) / 256) }
      headChoice := .n128 }

#kernel_checked_bool leaf047Check
  (leaf047Data.check logTerms pZeroTerms wTerms dTerms directN box_rRRRLRR)

def leaf047Checked : CheckedTree box_rRRRLRR :=
  LRCompactVStagedGroupedCheckedTree.ofAccept
    logTerms pZeroTerms wTerms dTerms directN
    leaf047Data leaf047Check

end GeneratedLRCompactVAdjacentStagedReplayV1
end CourtadeKumar
