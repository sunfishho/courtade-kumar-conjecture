import InformationTheory.CourtadeKumar.LRDeterminantIdealFinalRefinedReplayConfig

/-! Generated full-input packed checks for one bounded chunk group. -/

namespace CourtadeKumar.LRIdealFinalRefinedReplayGenerated
namespace L7MiddleG05

open LRLowKIdealMeanValue
open LRLowKIdealMeanValuePackedCertificate
open LRIdealCenteredMeanOracle
open LRIdealHistoricalReplayAssembly

def chunk020Path : Path :=
  [{ axis := .chi, branch := .upper }, { axis := .k, branch := .lower }, { axis := .k, branch := .upper }]

def chunk020Packed : String :=
  "hkMMkMM"

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem chunk020_checked :
    packedCheck (middleAutoOracle lowTerms lowLogFuel)
      (follow middleRoot chunk020Path) chunk020Packed = true := by
  rfl'

noncomputable def chunk020 :
    CheckedChunk (middleAutoOracle lowTerms lowLogFuel)
      (follow middleRoot chunk020Path) :=
  PackedCheckedChunk.toCheckedChunk
    ({ packed := chunk020Packed
       checked := chunk020_checked } :
      PackedCheckedChunk (middleAutoOracle lowTerms lowLogFuel)
        (follow middleRoot chunk020Path))

def chunk021Path : Path :=
  [{ axis := .chi, branch := .upper }, { axis := .k, branch := .upper }]

def chunk021Packed : String :=
  "khkMMMhhkMMMM"

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem chunk021_checked :
    packedCheck (middleAutoOracle lowTerms lowLogFuel)
      (follow middleRoot chunk021Path) chunk021Packed = true := by
  rfl'

noncomputable def chunk021 :
    CheckedChunk (middleAutoOracle lowTerms lowLogFuel)
      (follow middleRoot chunk021Path) :=
  PackedCheckedChunk.toCheckedChunk
    ({ packed := chunk021Packed
       checked := chunk021_checked } :
      PackedCheckedChunk (middleAutoOracle lowTerms lowLogFuel)
        (follow middleRoot chunk021Path))

end L7MiddleG05
end CourtadeKumar.LRIdealFinalRefinedReplayGenerated
