import InformationTheory.CourtadeKumar.GeneratedLRCompactVAdjacentStagedReplayV1.Config

set_option autoImplicit false

namespace CourtadeKumar
namespace GeneratedLRCompactVAdjacentStagedReplayV1

def leaf003Data : LRCompactVStagedGroupedLeafCertificate :=
  .sameY
    { logOnePlusVHi := { exponent := 0, mantissa := ((249 : ℚ) / 128) }
      headChoice := .n128 }

#kernel_checked_bool leaf003Check
  (leaf003Data.check logTerms pZeroTerms wTerms dTerms directN box_rLLLRR)

def leaf003Checked : CheckedTree box_rLLLRR :=
  LRCompactVStagedGroupedCheckedTree.ofAccept
    logTerms pZeroTerms wTerms dTerms directN
    leaf003Data leaf003Check

end GeneratedLRCompactVAdjacentStagedReplayV1
end CourtadeKumar
