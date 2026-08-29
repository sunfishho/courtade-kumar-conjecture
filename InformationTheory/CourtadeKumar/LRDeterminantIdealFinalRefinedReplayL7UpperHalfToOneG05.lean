import InformationTheory.CourtadeKumar.LRDeterminantIdealFinalRefinedReplayConfig

/-! Generated full-input packed checks for one bounded chunk group. -/

namespace CourtadeKumar.LRIdealFinalRefinedReplayGenerated
namespace L7UpperHalfToOneG05

open LRLowKIdealMeanValue
open LRLowKIdealMeanValuePackedCertificate
open LRIdealCenteredMeanOracle
open LRIdealHistoricalReplayAssembly

def chunk020Path : Path :=
  [{ axis := .chi, branch := .upper }, { axis := .k, branch := .upper }]

def chunk020Packed : String :=
  "hhkMMkMMhMM"

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem chunk020_checked :
    packedCheck (upperAutoOracle lowTerms lowLogFuel)
      (follow lowKUpperHalfToOneRoot chunk020Path) chunk020Packed = true := by
  rfl'

noncomputable def chunk020 :
    CheckedChunk (upperAutoOracle lowTerms lowLogFuel)
      (follow lowKUpperHalfToOneRoot chunk020Path) :=
  PackedCheckedChunk.toCheckedChunk
    ({ packed := chunk020Packed
       checked := chunk020_checked } :
      PackedCheckedChunk (upperAutoOracle lowTerms lowLogFuel)
        (follow lowKUpperHalfToOneRoot chunk020Path))

end L7UpperHalfToOneG05
end CourtadeKumar.LRIdealFinalRefinedReplayGenerated
