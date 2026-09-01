import InformationTheory.CourtadeKumar.GeneratedLRCompactVAdjacentStagedReplayV1.Config

set_option autoImplicit false

namespace CourtadeKumar
namespace GeneratedLRCompactVAdjacentStagedReplayV1

def leaf007Data : LRCompactVStagedGroupedLeafCertificate :=
  .sameY
    { logOnePlusVHi := { exponent := 0, mantissa := ((249 : ℚ) / 128) }
      headChoice := .n128 }

#kernel_checked_bool leaf007Check
  (leaf007Data.check logTerms pZeroTerms wTerms dTerms directN box_rLLRRR)

def leaf007Checked : CheckedTree box_rLLRRR :=
  LRCompactVStagedGroupedCheckedTree.ofAccept
    logTerms pZeroTerms wTerms dTerms directN
    leaf007Data leaf007Check

end GeneratedLRCompactVAdjacentStagedReplayV1
end CourtadeKumar
