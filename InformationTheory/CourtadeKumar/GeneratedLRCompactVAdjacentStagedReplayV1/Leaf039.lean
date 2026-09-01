import InformationTheory.CourtadeKumar.GeneratedLRCompactVAdjacentStagedReplayV1.Config

set_option autoImplicit false

namespace CourtadeKumar
namespace GeneratedLRCompactVAdjacentStagedReplayV1

def leaf039Data : LRCompactVStagedGroupedLeafCertificate :=
  .sameY
    { logOnePlusVHi := { exponent := 0, mantissa := ((1007 : ℚ) / 512) }
      headChoice := .n192 }

#kernel_checked_bool leaf039Check
  (leaf039Data.check logTerms pZeroTerms wTerms dTerms directN box_rRRLRLR)

def leaf039Checked : CheckedTree box_rRRLRLR :=
  LRCompactVStagedGroupedCheckedTree.ofAccept
    logTerms pZeroTerms wTerms dTerms directN
    leaf039Data leaf039Check

end GeneratedLRCompactVAdjacentStagedReplayV1
end CourtadeKumar
