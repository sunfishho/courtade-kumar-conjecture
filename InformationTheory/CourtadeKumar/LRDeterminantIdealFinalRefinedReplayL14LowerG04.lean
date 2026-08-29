import InformationTheory.CourtadeKumar.LRDeterminantIdealFinalRefinedReplayConfig

/-! Generated full-input packed checks for one bounded chunk group. -/

namespace CourtadeKumar.LRIdealFinalRefinedReplayGenerated
namespace L14LowerG04

open LRLowKIdealMeanValue
open LRLowKIdealMeanValuePackedCertificate
open LRIdealCenteredMeanOracle
open LRIdealHistoricalReplayAssembly

def chunk016Path : Path :=
  [{ axis := .chi, branch := .upper }, { axis := .k, branch := .lower }]

def chunk016Packed : String :=
  "hkhkMMMhMMkhMMM"

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem chunk016_checked :
    packedCheck (restrictedAutoOracle restrictedTerms restrictedLogFuel)
      (follow restrictedLowerRoot chunk016Path) chunk016Packed = true := by
  rfl'

noncomputable def chunk016 :
    CheckedChunk (restrictedAutoOracle restrictedTerms restrictedLogFuel)
      (follow restrictedLowerRoot chunk016Path) :=
  PackedCheckedChunk.toCheckedChunk
    ({ packed := chunk016Packed
       checked := chunk016_checked } :
      PackedCheckedChunk (restrictedAutoOracle restrictedTerms restrictedLogFuel)
        (follow restrictedLowerRoot chunk016Path))

def chunk017Path : Path :=
  [{ axis := .chi, branch := .upper }, { axis := .k, branch := .upper }]

def chunk017Packed : String :=
  "hhkMMkMMhMM"

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem chunk017_checked :
    packedCheck (restrictedAutoOracle restrictedTerms restrictedLogFuel)
      (follow restrictedLowerRoot chunk017Path) chunk017Packed = true := by
  rfl'

noncomputable def chunk017 :
    CheckedChunk (restrictedAutoOracle restrictedTerms restrictedLogFuel)
      (follow restrictedLowerRoot chunk017Path) :=
  PackedCheckedChunk.toCheckedChunk
    ({ packed := chunk017Packed
       checked := chunk017_checked } :
      PackedCheckedChunk (restrictedAutoOracle restrictedTerms restrictedLogFuel)
        (follow restrictedLowerRoot chunk017Path))

end L14LowerG04
end CourtadeKumar.LRIdealFinalRefinedReplayGenerated
