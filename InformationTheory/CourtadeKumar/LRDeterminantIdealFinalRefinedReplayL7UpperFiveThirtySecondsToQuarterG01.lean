import InformationTheory.CourtadeKumar.LRDeterminantIdealFinalRefinedReplayConfig

/-! Generated full-input packed checks for one bounded chunk group. -/

namespace CourtadeKumar.LRIdealFinalRefinedReplayGenerated
namespace L7UpperFiveThirtySecondsToQuarterG01

open LRLowKIdealMeanValue
open LRLowKIdealMeanValuePackedCertificate
open LRIdealCenteredMeanOracle
open LRIdealHistoricalReplayAssembly

def chunk004Path : Path :=
  [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .upper }, { axis := .k, branch := .upper }]

def chunk004Packed : String :=
  "khMkMMhMM"

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem chunk004_checked :
    packedCheck (upperAutoOracle lowTerms lowLogFuel)
      (follow lowKUpperFiveThirtySecondsToQuarterRoot chunk004Path) chunk004Packed = true := by
  rfl'

noncomputable def chunk004 :
    CheckedChunk (upperAutoOracle lowTerms lowLogFuel)
      (follow lowKUpperFiveThirtySecondsToQuarterRoot chunk004Path) :=
  PackedCheckedChunk.toCheckedChunk
    ({ packed := chunk004Packed
       checked := chunk004_checked } :
      PackedCheckedChunk (upperAutoOracle lowTerms lowLogFuel)
        (follow lowKUpperFiveThirtySecondsToQuarterRoot chunk004Path))

def chunk005Path : Path :=
  [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .upper }, { axis := .k, branch := .lower }, { axis := .k, branch := .lower }, { axis := .chi, branch := .lower }]

def chunk005Packed : String :=
  "khkhMMMhMMhkMMM"

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem chunk005_checked :
    packedCheck (upperAutoOracle lowTerms lowLogFuel)
      (follow lowKUpperFiveThirtySecondsToQuarterRoot chunk005Path) chunk005Packed = true := by
  rfl'

noncomputable def chunk005 :
    CheckedChunk (upperAutoOracle lowTerms lowLogFuel)
      (follow lowKUpperFiveThirtySecondsToQuarterRoot chunk005Path) :=
  PackedCheckedChunk.toCheckedChunk
    ({ packed := chunk005Packed
       checked := chunk005_checked } :
      PackedCheckedChunk (upperAutoOracle lowTerms lowLogFuel)
        (follow lowKUpperFiveThirtySecondsToQuarterRoot chunk005Path))

def chunk006Path : Path :=
  [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .upper }, { axis := .k, branch := .lower }, { axis := .k, branch := .lower }, { axis := .chi, branch := .upper }]

def chunk006Packed : String :=
  "hkMMM"

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem chunk006_checked :
    packedCheck (upperAutoOracle lowTerms lowLogFuel)
      (follow lowKUpperFiveThirtySecondsToQuarterRoot chunk006Path) chunk006Packed = true := by
  rfl'

noncomputable def chunk006 :
    CheckedChunk (upperAutoOracle lowTerms lowLogFuel)
      (follow lowKUpperFiveThirtySecondsToQuarterRoot chunk006Path) :=
  PackedCheckedChunk.toCheckedChunk
    ({ packed := chunk006Packed
       checked := chunk006_checked } :
      PackedCheckedChunk (upperAutoOracle lowTerms lowLogFuel)
        (follow lowKUpperFiveThirtySecondsToQuarterRoot chunk006Path))

def chunk007Path : Path :=
  [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .upper }, { axis := .k, branch := .lower }, { axis := .k, branch := .upper }]

def chunk007Packed : String :=
  "hhkMMkMMhMM"

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem chunk007_checked :
    packedCheck (upperAutoOracle lowTerms lowLogFuel)
      (follow lowKUpperFiveThirtySecondsToQuarterRoot chunk007Path) chunk007Packed = true := by
  rfl'

noncomputable def chunk007 :
    CheckedChunk (upperAutoOracle lowTerms lowLogFuel)
      (follow lowKUpperFiveThirtySecondsToQuarterRoot chunk007Path) :=
  PackedCheckedChunk.toCheckedChunk
    ({ packed := chunk007Packed
       checked := chunk007_checked } :
      PackedCheckedChunk (upperAutoOracle lowTerms lowLogFuel)
        (follow lowKUpperFiveThirtySecondsToQuarterRoot chunk007Path))

end L7UpperFiveThirtySecondsToQuarterG01
end CourtadeKumar.LRIdealFinalRefinedReplayGenerated
