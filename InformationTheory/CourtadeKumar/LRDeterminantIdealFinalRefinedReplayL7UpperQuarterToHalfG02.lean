import InformationTheory.CourtadeKumar.LRDeterminantIdealFinalRefinedReplayConfig

/-! Generated full-input packed checks for one bounded chunk group. -/

namespace CourtadeKumar.LRIdealFinalRefinedReplayGenerated
namespace L7UpperQuarterToHalfG02

open LRLowKIdealMeanValue
open LRLowKIdealMeanValuePackedCertificate
open LRIdealCenteredMeanOracle
open LRIdealHistoricalReplayAssembly

def chunk008Path : Path :=
  [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .upper }, { axis := .k, branch := .upper }]

def chunk008Packed : String :=
  "hkhMMhMMkMM"

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem chunk008_checked :
    packedCheck (upperAutoOracle lowTerms lowLogFuel)
      (follow lowKUpperQuarterToHalfRoot chunk008Path) chunk008Packed = true := by
  rfl'

noncomputable def chunk008 :
    CheckedChunk (upperAutoOracle lowTerms lowLogFuel)
      (follow lowKUpperQuarterToHalfRoot chunk008Path) :=
  PackedCheckedChunk.toCheckedChunk
    ({ packed := chunk008Packed
       checked := chunk008_checked } :
      PackedCheckedChunk (upperAutoOracle lowTerms lowLogFuel)
        (follow lowKUpperQuarterToHalfRoot chunk008Path))

def chunk009Path : Path :=
  [{ axis := .chi, branch := .upper }, { axis := .k, branch := .lower }]

def chunk009Packed : String :=
  "hkhMMhMMkMM"

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem chunk009_checked :
    packedCheck (upperAutoOracle lowTerms lowLogFuel)
      (follow lowKUpperQuarterToHalfRoot chunk009Path) chunk009Packed = true := by
  rfl'

noncomputable def chunk009 :
    CheckedChunk (upperAutoOracle lowTerms lowLogFuel)
      (follow lowKUpperQuarterToHalfRoot chunk009Path) :=
  PackedCheckedChunk.toCheckedChunk
    ({ packed := chunk009Packed
       checked := chunk009_checked } :
      PackedCheckedChunk (upperAutoOracle lowTerms lowLogFuel)
        (follow lowKUpperQuarterToHalfRoot chunk009Path))

def chunk010Path : Path :=
  [{ axis := .chi, branch := .upper }, { axis := .k, branch := .upper }]

def chunk010Packed : String :=
  "hhkMMMM"

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem chunk010_checked :
    packedCheck (upperAutoOracle lowTerms lowLogFuel)
      (follow lowKUpperQuarterToHalfRoot chunk010Path) chunk010Packed = true := by
  rfl'

noncomputable def chunk010 :
    CheckedChunk (upperAutoOracle lowTerms lowLogFuel)
      (follow lowKUpperQuarterToHalfRoot chunk010Path) :=
  PackedCheckedChunk.toCheckedChunk
    ({ packed := chunk010Packed
       checked := chunk010_checked } :
      PackedCheckedChunk (upperAutoOracle lowTerms lowLogFuel)
        (follow lowKUpperQuarterToHalfRoot chunk010Path))

end L7UpperQuarterToHalfG02
end CourtadeKumar.LRIdealFinalRefinedReplayGenerated
