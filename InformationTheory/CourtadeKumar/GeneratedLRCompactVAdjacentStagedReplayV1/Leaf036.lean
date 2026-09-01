import InformationTheory.CourtadeKumar.GeneratedLRCompactVAdjacentStagedReplayV1.Config

set_option autoImplicit false

namespace CourtadeKumar
namespace GeneratedLRCompactVAdjacentStagedReplayV1

def leaf036Data : LRCompactVStagedGroupedLeafCertificate :=
  .sameY
    { logOnePlusVHi := { exponent := 0, mantissa := ((503 : ℚ) / 256) }
      headChoice := .n128 }

#kernel_checked_bool leaf036Check
  (leaf036Data.check logTerms pZeroTerms wTerms dTerms directN box_rRRLLRL)

def leaf036Checked : CheckedTree box_rRRLLRL :=
  LRCompactVStagedGroupedCheckedTree.ofAccept
    logTerms pZeroTerms wTerms dTerms directN
    leaf036Data leaf036Check

end GeneratedLRCompactVAdjacentStagedReplayV1
end CourtadeKumar
