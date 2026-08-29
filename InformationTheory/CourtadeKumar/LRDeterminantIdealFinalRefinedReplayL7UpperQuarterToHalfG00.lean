import InformationTheory.CourtadeKumar.LRDeterminantIdealFinalRefinedReplayConfig

/-! Generated full-input packed checks for one bounded chunk group. -/

namespace CourtadeKumar.LRIdealFinalRefinedReplayGenerated
namespace L7UpperQuarterToHalfG00

open LRLowKIdealMeanValue
open LRLowKIdealMeanValuePackedCertificate
open LRIdealCenteredMeanOracle
open LRIdealHistoricalReplayAssembly

def chunk000Path : Path :=
  [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }]

def chunk000Packed : String :=
  "kkkNNkNNkNN"

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem chunk000_checked :
    packedCheck (upperAutoOracle lowTerms lowLogFuel)
      (follow lowKUpperQuarterToHalfRoot chunk000Path) chunk000Packed = true := by
  rfl'

noncomputable def chunk000 :
    CheckedChunk (upperAutoOracle lowTerms lowLogFuel)
      (follow lowKUpperQuarterToHalfRoot chunk000Path) :=
  PackedCheckedChunk.toCheckedChunk
    ({ packed := chunk000Packed
       checked := chunk000_checked } :
      PackedCheckedChunk (upperAutoOracle lowTerms lowLogFuel)
        (follow lowKUpperQuarterToHalfRoot chunk000Path))

def chunk001Path : Path :=
  [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .upper }]

def chunk001Packed : String :=
  "kkMMM"

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem chunk001_checked :
    packedCheck (upperAutoOracle lowTerms lowLogFuel)
      (follow lowKUpperQuarterToHalfRoot chunk001Path) chunk001Packed = true := by
  rfl'

noncomputable def chunk001 :
    CheckedChunk (upperAutoOracle lowTerms lowLogFuel)
      (follow lowKUpperQuarterToHalfRoot chunk001Path) :=
  PackedCheckedChunk.toCheckedChunk
    ({ packed := chunk001Packed
       checked := chunk001_checked } :
      PackedCheckedChunk (upperAutoOracle lowTerms lowLogFuel)
        (follow lowKUpperQuarterToHalfRoot chunk001Path))

def chunk002Path : Path :=
  [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .upper }]

def chunk002Packed : String :=
  "kkMMM"

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem chunk002_checked :
    packedCheck (upperAutoOracle lowTerms lowLogFuel)
      (follow lowKUpperQuarterToHalfRoot chunk002Path) chunk002Packed = true := by
  rfl'

noncomputable def chunk002 :
    CheckedChunk (upperAutoOracle lowTerms lowLogFuel)
      (follow lowKUpperQuarterToHalfRoot chunk002Path) :=
  PackedCheckedChunk.toCheckedChunk
    ({ packed := chunk002Packed
       checked := chunk002_checked } :
      PackedCheckedChunk (upperAutoOracle lowTerms lowLogFuel)
        (follow lowKUpperQuarterToHalfRoot chunk002Path))

def chunk003Path : Path :=
  [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .upper }]

def chunk003Packed : String :=
  "kkMMkMM"

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem chunk003_checked :
    packedCheck (upperAutoOracle lowTerms lowLogFuel)
      (follow lowKUpperQuarterToHalfRoot chunk003Path) chunk003Packed = true := by
  rfl'

noncomputable def chunk003 :
    CheckedChunk (upperAutoOracle lowTerms lowLogFuel)
      (follow lowKUpperQuarterToHalfRoot chunk003Path) :=
  PackedCheckedChunk.toCheckedChunk
    ({ packed := chunk003Packed
       checked := chunk003_checked } :
      PackedCheckedChunk (upperAutoOracle lowTerms lowLogFuel)
        (follow lowKUpperQuarterToHalfRoot chunk003Path))

end L7UpperQuarterToHalfG00
end CourtadeKumar.LRIdealFinalRefinedReplayGenerated
