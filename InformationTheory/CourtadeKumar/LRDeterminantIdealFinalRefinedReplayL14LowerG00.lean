import InformationTheory.CourtadeKumar.LRDeterminantIdealFinalRefinedReplayConfig

/-! Generated full-input packed checks for one bounded chunk group. -/

namespace CourtadeKumar.LRIdealFinalRefinedReplayGenerated
namespace L14LowerG00

open LRLowKIdealMeanValue
open LRLowKIdealMeanValuePackedCertificate
open LRIdealCenteredMeanOracle
open LRIdealHistoricalReplayAssembly

def chunk000Path : Path :=
  [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .k, branch := .lower }]

def chunk000Packed : String :=
  "kkkNNkNNkNN"

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem chunk000_checked :
    packedCheck (restrictedAutoOracle restrictedTerms restrictedLogFuel)
      (follow restrictedLowerRoot chunk000Path) chunk000Packed = true := by
  rfl'

noncomputable def chunk000 :
    CheckedChunk (restrictedAutoOracle restrictedTerms restrictedLogFuel)
      (follow restrictedLowerRoot chunk000Path) :=
  PackedCheckedChunk.toCheckedChunk
    ({ packed := chunk000Packed
       checked := chunk000_checked } :
      PackedCheckedChunk (restrictedAutoOracle restrictedTerms restrictedLogFuel)
        (follow restrictedLowerRoot chunk000Path))

def chunk001Path : Path :=
  [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .k, branch := .upper }]

def chunk001Packed : String :=
  "kkNNkNN"

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem chunk001_checked :
    packedCheck (restrictedAutoOracle restrictedTerms restrictedLogFuel)
      (follow restrictedLowerRoot chunk001Path) chunk001Packed = true := by
  rfl'

noncomputable def chunk001 :
    CheckedChunk (restrictedAutoOracle restrictedTerms restrictedLogFuel)
      (follow restrictedLowerRoot chunk001Path) :=
  PackedCheckedChunk.toCheckedChunk
    ({ packed := chunk001Packed
       checked := chunk001_checked } :
      PackedCheckedChunk (restrictedAutoOracle restrictedTerms restrictedLogFuel)
        (follow restrictedLowerRoot chunk001Path))

def chunk002Path : Path :=
  [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .upper }]

def chunk002Packed : String :=
  "kkMMM"

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem chunk002_checked :
    packedCheck (restrictedAutoOracle restrictedTerms restrictedLogFuel)
      (follow restrictedLowerRoot chunk002Path) chunk002Packed = true := by
  rfl'

noncomputable def chunk002 :
    CheckedChunk (restrictedAutoOracle restrictedTerms restrictedLogFuel)
      (follow restrictedLowerRoot chunk002Path) :=
  PackedCheckedChunk.toCheckedChunk
    ({ packed := chunk002Packed
       checked := chunk002_checked } :
      PackedCheckedChunk (restrictedAutoOracle restrictedTerms restrictedLogFuel)
        (follow restrictedLowerRoot chunk002Path))

def chunk003Path : Path :=
  [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .upper }]

def chunk003Packed : String :=
  "kkMMkMM"

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem chunk003_checked :
    packedCheck (restrictedAutoOracle restrictedTerms restrictedLogFuel)
      (follow restrictedLowerRoot chunk003Path) chunk003Packed = true := by
  rfl'

noncomputable def chunk003 :
    CheckedChunk (restrictedAutoOracle restrictedTerms restrictedLogFuel)
      (follow restrictedLowerRoot chunk003Path) :=
  PackedCheckedChunk.toCheckedChunk
    ({ packed := chunk003Packed
       checked := chunk003_checked } :
      PackedCheckedChunk (restrictedAutoOracle restrictedTerms restrictedLogFuel)
        (follow restrictedLowerRoot chunk003Path))

end L14LowerG00
end CourtadeKumar.LRIdealFinalRefinedReplayGenerated
