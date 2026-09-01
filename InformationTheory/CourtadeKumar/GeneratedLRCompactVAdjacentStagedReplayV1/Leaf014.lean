import InformationTheory.CourtadeKumar.GeneratedLRCompactVAdjacentStagedReplayV1.Config

set_option autoImplicit false

namespace CourtadeKumar
namespace GeneratedLRCompactVAdjacentStagedReplayV1

def leaf014Data : LRCompactVStagedGroupedLeafCertificate :=
  .sameY
    { logOnePlusVHi := { exponent := 0, mantissa := ((125 : ℚ) / 64) }
      headChoice := .n128 }

#kernel_checked_bool leaf014Check
  (leaf014Data.check logTerms pZeroTerms wTerms dTerms directN box_rLRLRRR)

def leaf014Checked : CheckedTree box_rLRLRRR :=
  LRCompactVStagedGroupedCheckedTree.ofAccept
    logTerms pZeroTerms wTerms dTerms directN
    leaf014Data leaf014Check

end GeneratedLRCompactVAdjacentStagedReplayV1
end CourtadeKumar
