import InformationTheory.CourtadeKumar.GeneratedLRCompactVAdjacentStagedReplayV1.Config

set_option autoImplicit false

namespace CourtadeKumar
namespace GeneratedLRCompactVAdjacentStagedReplayV1

def leaf002Data : LRCompactVStagedGroupedLeafCertificate :=
  .sameY
    { logOnePlusVHi := { exponent := 0, mantissa := ((249 : ℚ) / 128) }
      headChoice := .n128 }

#kernel_checked_bool leaf002Check
  (leaf002Data.check logTerms pZeroTerms wTerms dTerms directN box_rLLLRL)

def leaf002Checked : CheckedTree box_rLLLRL :=
  LRCompactVStagedGroupedCheckedTree.ofAccept
    logTerms pZeroTerms wTerms dTerms directN
    leaf002Data leaf002Check

end GeneratedLRCompactVAdjacentStagedReplayV1
end CourtadeKumar
