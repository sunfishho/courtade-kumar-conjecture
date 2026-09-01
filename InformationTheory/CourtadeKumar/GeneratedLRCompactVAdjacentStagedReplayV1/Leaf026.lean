import InformationTheory.CourtadeKumar.GeneratedLRCompactVAdjacentStagedReplayV1.Config

set_option autoImplicit false

namespace CourtadeKumar
namespace GeneratedLRCompactVAdjacentStagedReplayV1

def leaf026Data : LRCompactVStagedGroupedLeafCertificate :=
  .sameY
    { logOnePlusVHi := { exponent := 0, mantissa := ((251 : ℚ) / 128) }
      headChoice := .n128 }

#kernel_checked_bool leaf026Check
  (leaf026Data.check logTerms pZeroTerms wTerms dTerms directN box_rRLLRRR)

def leaf026Checked : CheckedTree box_rRLLRRR :=
  LRCompactVStagedGroupedCheckedTree.ofAccept
    logTerms pZeroTerms wTerms dTerms directN
    leaf026Data leaf026Check

end GeneratedLRCompactVAdjacentStagedReplayV1
end CourtadeKumar
