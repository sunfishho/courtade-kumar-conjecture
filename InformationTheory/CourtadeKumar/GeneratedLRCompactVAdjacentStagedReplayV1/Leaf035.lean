import InformationTheory.CourtadeKumar.GeneratedLRCompactVAdjacentStagedReplayV1.Config

set_option autoImplicit false

namespace CourtadeKumar
namespace GeneratedLRCompactVAdjacentStagedReplayV1

def leaf035Data : LRCompactVStagedGroupedLeafCertificate :=
  .sameY
    { logOnePlusVHi := { exponent := 0, mantissa := ((1005 : ℚ) / 512) }
      headChoice := .n128 }

#kernel_checked_bool leaf035Check
  (leaf035Data.check logTerms pZeroTerms wTerms dTerms directN box_rRRLLLR)

def leaf035Checked : CheckedTree box_rRRLLLR :=
  LRCompactVStagedGroupedCheckedTree.ofAccept
    logTerms pZeroTerms wTerms dTerms directN
    leaf035Data leaf035Check

end GeneratedLRCompactVAdjacentStagedReplayV1
end CourtadeKumar
