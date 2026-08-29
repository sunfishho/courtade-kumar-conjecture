import InformationTheory.CourtadeKumar.LRDeterminantIdealFinalRefinedReplayConfig

/-! Generated full-input packed checks for one bounded chunk group. -/

namespace CourtadeKumar.LRIdealFinalRefinedReplayGenerated
namespace L7UpperFiveThirtySecondsToQuarterG02

open LRLowKIdealMeanValue
open LRLowKIdealMeanValuePackedCertificate
open LRIdealCenteredMeanOracle
open LRIdealHistoricalReplayAssembly

def chunk008Path : Path :=
  [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .upper }, { axis := .k, branch := .upper }]

def chunk008Packed : String :=
  "hkhkMMMhMMkMM"

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem chunk008_checked :
    packedCheck (upperAutoOracle lowTerms lowLogFuel)
      (follow lowKUpperFiveThirtySecondsToQuarterRoot chunk008Path) chunk008Packed = true := by
  rfl'

noncomputable def chunk008 :
    CheckedChunk (upperAutoOracle lowTerms lowLogFuel)
      (follow lowKUpperFiveThirtySecondsToQuarterRoot chunk008Path) :=
  PackedCheckedChunk.toCheckedChunk
    ({ packed := chunk008Packed
       checked := chunk008_checked } :
      PackedCheckedChunk (upperAutoOracle lowTerms lowLogFuel)
        (follow lowKUpperFiveThirtySecondsToQuarterRoot chunk008Path))

def chunk009Path : Path :=
  [{ axis := .chi, branch := .upper }]

def chunk009Packed : String :=
  "khhkMMMMhhMMM"

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem chunk009_checked :
    packedCheck (upperAutoOracle lowTerms lowLogFuel)
      (follow lowKUpperFiveThirtySecondsToQuarterRoot chunk009Path) chunk009Packed = true := by
  rfl'

noncomputable def chunk009 :
    CheckedChunk (upperAutoOracle lowTerms lowLogFuel)
      (follow lowKUpperFiveThirtySecondsToQuarterRoot chunk009Path) :=
  PackedCheckedChunk.toCheckedChunk
    ({ packed := chunk009Packed
       checked := chunk009_checked } :
      PackedCheckedChunk (upperAutoOracle lowTerms lowLogFuel)
        (follow lowKUpperFiveThirtySecondsToQuarterRoot chunk009Path))

end L7UpperFiveThirtySecondsToQuarterG02
end CourtadeKumar.LRIdealFinalRefinedReplayGenerated
