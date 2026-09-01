import InformationTheory.CourtadeKumar.GeneratedLRCompactVAdjacentStagedReplayV1.Config

set_option autoImplicit false

namespace CourtadeKumar
namespace GeneratedLRCompactVAdjacentStagedReplayV1

def leaf049Data : LRCompactVStagedGroupedLeafCertificate :=
  .sameY
    { logOnePlusVHi := { exponent := 0, mantissa := ((2015 : ℚ) / 1024) }
      headChoice := .n128 }

#kernel_checked_bool leaf049Check
  (leaf049Data.check logTerms pZeroTerms wTerms dTerms directN box_rRRRRLRL)

def leaf049Checked : CheckedTree box_rRRRRLRL :=
  LRCompactVStagedGroupedCheckedTree.ofAccept
    logTerms pZeroTerms wTerms dTerms directN
    leaf049Data leaf049Check

end GeneratedLRCompactVAdjacentStagedReplayV1
end CourtadeKumar
