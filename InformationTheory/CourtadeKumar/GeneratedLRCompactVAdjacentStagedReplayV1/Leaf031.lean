import InformationTheory.CourtadeKumar.GeneratedLRCompactVAdjacentStagedReplayV1.Config

set_option autoImplicit false

namespace CourtadeKumar
namespace GeneratedLRCompactVAdjacentStagedReplayV1

def leaf031Data : LRCompactVStagedGroupedLeafCertificate :=
  .sameY
    { logOnePlusVHi := { exponent := 0, mantissa := ((251 : ℚ) / 128) }
      headChoice := .n128 }

#kernel_checked_bool leaf031Check
  (leaf031Data.check logTerms pZeroTerms wTerms dTerms directN box_rRLRRLR)

def leaf031Checked : CheckedTree box_rRLRRLR :=
  LRCompactVStagedGroupedCheckedTree.ofAccept
    logTerms pZeroTerms wTerms dTerms directN
    leaf031Data leaf031Check

end GeneratedLRCompactVAdjacentStagedReplayV1
end CourtadeKumar
