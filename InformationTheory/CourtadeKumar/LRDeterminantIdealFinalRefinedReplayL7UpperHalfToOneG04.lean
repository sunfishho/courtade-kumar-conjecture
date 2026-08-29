import InformationTheory.CourtadeKumar.LRDeterminantIdealFinalRefinedReplayConfig

/-! Generated full-input packed checks for one bounded chunk group. -/

namespace CourtadeKumar.LRIdealFinalRefinedReplayGenerated
namespace L7UpperHalfToOneG04

open LRLowKIdealMeanValue
open LRLowKIdealMeanValuePackedCertificate
open LRIdealCenteredMeanOracle
open LRIdealHistoricalReplayAssembly

def chunk016Path : Path :=
  [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .upper }, { axis := .k, branch := .upper }, { axis := .chi, branch := .lower }, { axis := .k, branch := .upper }, { axis := .chi, branch := .lower }]

def chunk016Packed : String :=
  "khkMMMhkMMM"

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem chunk016_checked :
    packedCheck (upperAutoOracle lowTerms lowLogFuel)
      (follow lowKUpperHalfToOneRoot chunk016Path) chunk016Packed = true := by
  rfl'

noncomputable def chunk016 :
    CheckedChunk (upperAutoOracle lowTerms lowLogFuel)
      (follow lowKUpperHalfToOneRoot chunk016Path) :=
  PackedCheckedChunk.toCheckedChunk
    ({ packed := chunk016Packed
       checked := chunk016_checked } :
      PackedCheckedChunk (upperAutoOracle lowTerms lowLogFuel)
        (follow lowKUpperHalfToOneRoot chunk016Path))

def chunk017Path : Path :=
  [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .upper }, { axis := .k, branch := .upper }, { axis := .chi, branch := .lower }, { axis := .k, branch := .upper }, { axis := .chi, branch := .upper }]

def chunk017Packed : String :=
  "kMhMM"

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem chunk017_checked :
    packedCheck (upperAutoOracle lowTerms lowLogFuel)
      (follow lowKUpperHalfToOneRoot chunk017Path) chunk017Packed = true := by
  rfl'

noncomputable def chunk017 :
    CheckedChunk (upperAutoOracle lowTerms lowLogFuel)
      (follow lowKUpperHalfToOneRoot chunk017Path) :=
  PackedCheckedChunk.toCheckedChunk
    ({ packed := chunk017Packed
       checked := chunk017_checked } :
      PackedCheckedChunk (upperAutoOracle lowTerms lowLogFuel)
        (follow lowKUpperHalfToOneRoot chunk017Path))

def chunk018Path : Path :=
  [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .upper }, { axis := .k, branch := .upper }, { axis := .chi, branch := .upper }]

def chunk018Packed : String :=
  "khkMMMhkMMM"

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem chunk018_checked :
    packedCheck (upperAutoOracle lowTerms lowLogFuel)
      (follow lowKUpperHalfToOneRoot chunk018Path) chunk018Packed = true := by
  rfl'

noncomputable def chunk018 :
    CheckedChunk (upperAutoOracle lowTerms lowLogFuel)
      (follow lowKUpperHalfToOneRoot chunk018Path) :=
  PackedCheckedChunk.toCheckedChunk
    ({ packed := chunk018Packed
       checked := chunk018_checked } :
      PackedCheckedChunk (upperAutoOracle lowTerms lowLogFuel)
        (follow lowKUpperHalfToOneRoot chunk018Path))

def chunk019Path : Path :=
  [{ axis := .chi, branch := .upper }, { axis := .k, branch := .lower }]

def chunk019Packed : String :=
  "hkhkMMMhMMkMM"

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem chunk019_checked :
    packedCheck (upperAutoOracle lowTerms lowLogFuel)
      (follow lowKUpperHalfToOneRoot chunk019Path) chunk019Packed = true := by
  rfl'

noncomputable def chunk019 :
    CheckedChunk (upperAutoOracle lowTerms lowLogFuel)
      (follow lowKUpperHalfToOneRoot chunk019Path) :=
  PackedCheckedChunk.toCheckedChunk
    ({ packed := chunk019Packed
       checked := chunk019_checked } :
      PackedCheckedChunk (upperAutoOracle lowTerms lowLogFuel)
        (follow lowKUpperHalfToOneRoot chunk019Path))

end L7UpperHalfToOneG04
end CourtadeKumar.LRIdealFinalRefinedReplayGenerated
