import InformationTheory.CourtadeKumar.LRDeterminantIdealFinalRefinedReplayConfig

/-! Generated full-input packed checks for one bounded chunk group. -/

namespace CourtadeKumar.LRIdealFinalRefinedReplayGenerated
namespace L7MiddleG04

open LRLowKIdealMeanValue
open LRLowKIdealMeanValuePackedCertificate
open LRIdealCenteredMeanOracle
open LRIdealHistoricalReplayAssembly

def chunk016Path : Path :=
  [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .upper }, { axis := .k, branch := .upper }, { axis := .k, branch := .upper }, { axis := .chi, branch := .lower }, { axis := .k, branch := .lower }]

def chunk016Packed : String :=
  "hkMMkMM"

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem chunk016_checked :
    packedCheck (middleAutoOracle lowTerms lowLogFuel)
      (follow middleRoot chunk016Path) chunk016Packed = true := by
  rfl'

noncomputable def chunk016 :
    CheckedChunk (middleAutoOracle lowTerms lowLogFuel)
      (follow middleRoot chunk016Path) :=
  PackedCheckedChunk.toCheckedChunk
    ({ packed := chunk016Packed
       checked := chunk016_checked } :
      PackedCheckedChunk (middleAutoOracle lowTerms lowLogFuel)
        (follow middleRoot chunk016Path))

def chunk017Path : Path :=
  [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .upper }, { axis := .k, branch := .upper }, { axis := .k, branch := .upper }, { axis := .chi, branch := .lower }, { axis := .k, branch := .upper }]

def chunk017Packed : String :=
  "hkhMMhkMMMkMhMM"

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem chunk017_checked :
    packedCheck (middleAutoOracle lowTerms lowLogFuel)
      (follow middleRoot chunk017Path) chunk017Packed = true := by
  rfl'

noncomputable def chunk017 :
    CheckedChunk (middleAutoOracle lowTerms lowLogFuel)
      (follow middleRoot chunk017Path) :=
  PackedCheckedChunk.toCheckedChunk
    ({ packed := chunk017Packed
       checked := chunk017_checked } :
      PackedCheckedChunk (middleAutoOracle lowTerms lowLogFuel)
        (follow middleRoot chunk017Path))

def chunk018Path : Path :=
  [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .upper }, { axis := .k, branch := .upper }, { axis := .k, branch := .upper }, { axis := .chi, branch := .upper }]

def chunk018Packed : String :=
  "khMMhMM"

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem chunk018_checked :
    packedCheck (middleAutoOracle lowTerms lowLogFuel)
      (follow middleRoot chunk018Path) chunk018Packed = true := by
  rfl'

noncomputable def chunk018 :
    CheckedChunk (middleAutoOracle lowTerms lowLogFuel)
      (follow middleRoot chunk018Path) :=
  PackedCheckedChunk.toCheckedChunk
    ({ packed := chunk018Packed
       checked := chunk018_checked } :
      PackedCheckedChunk (middleAutoOracle lowTerms lowLogFuel)
        (follow middleRoot chunk018Path))

def chunk019Path : Path :=
  [{ axis := .chi, branch := .upper }, { axis := .k, branch := .lower }, { axis := .k, branch := .lower }]

def chunk019Packed : String :=
  "kkhhMMMhMMhkMMM"

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem chunk019_checked :
    packedCheck (middleAutoOracle lowTerms lowLogFuel)
      (follow middleRoot chunk019Path) chunk019Packed = true := by
  rfl'

noncomputable def chunk019 :
    CheckedChunk (middleAutoOracle lowTerms lowLogFuel)
      (follow middleRoot chunk019Path) :=
  PackedCheckedChunk.toCheckedChunk
    ({ packed := chunk019Packed
       checked := chunk019_checked } :
      PackedCheckedChunk (middleAutoOracle lowTerms lowLogFuel)
        (follow middleRoot chunk019Path))

end L7MiddleG04
end CourtadeKumar.LRIdealFinalRefinedReplayGenerated
