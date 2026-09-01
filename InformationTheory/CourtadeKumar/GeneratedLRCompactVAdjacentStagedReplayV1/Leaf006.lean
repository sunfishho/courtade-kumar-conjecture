import InformationTheory.CourtadeKumar.GeneratedLRCompactVAdjacentStagedReplayV1.Config

set_option autoImplicit false

namespace CourtadeKumar
namespace GeneratedLRCompactVAdjacentStagedReplayV1

def leaf006Data : LRCompactVStagedGroupedLeafCertificate :=
  .sameY
    { logOnePlusVHi := { exponent := 0, mantissa := ((249 : ℚ) / 128) }
      headChoice := .n128 }

#kernel_checked_bool leaf006Check
  (leaf006Data.check logTerms pZeroTerms wTerms dTerms directN box_rLLRRL)

def leaf006Checked : CheckedTree box_rLLRRL :=
  LRCompactVStagedGroupedCheckedTree.ofAccept
    logTerms pZeroTerms wTerms dTerms directN
    leaf006Data leaf006Check

end GeneratedLRCompactVAdjacentStagedReplayV1
end CourtadeKumar
