import InformationTheory.CourtadeKumar.LRDeterminantIdealFinalRefinedReplayConfig

/-! Generated full-input packed checks for one bounded chunk group. -/

namespace CourtadeKumar.LRIdealFinalRefinedReplayGenerated
namespace L7MiddleG01

open LRLowKIdealMeanValue
open LRLowKIdealMeanValuePackedCertificate
open LRIdealCenteredMeanOracle
open LRIdealHistoricalReplayAssembly

def chunk004Path : Path :=
  [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .upper }, { axis := .k, branch := .lower }]

def chunk004Packed : String :=
  "kkkMMkMMkMM"

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem chunk004_checked :
    packedCheck (middleAutoOracle lowTerms lowLogFuel)
      (follow middleRoot chunk004Path) chunk004Packed = true := by
  rfl'

noncomputable def chunk004 :
    CheckedChunk (middleAutoOracle lowTerms lowLogFuel)
      (follow middleRoot chunk004Path) :=
  PackedCheckedChunk.toCheckedChunk
    ({ packed := chunk004Packed
       checked := chunk004_checked } :
      PackedCheckedChunk (middleAutoOracle lowTerms lowLogFuel)
        (follow middleRoot chunk004Path))

def chunk005Path : Path :=
  [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .upper }, { axis := .k, branch := .upper }]

def chunk005Packed : String :=
  "kkMMkMM"

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem chunk005_checked :
    packedCheck (middleAutoOracle lowTerms lowLogFuel)
      (follow middleRoot chunk005Path) chunk005Packed = true := by
  rfl'

noncomputable def chunk005 :
    CheckedChunk (middleAutoOracle lowTerms lowLogFuel)
      (follow middleRoot chunk005Path) :=
  PackedCheckedChunk.toCheckedChunk
    ({ packed := chunk005Packed
       checked := chunk005_checked } :
      PackedCheckedChunk (middleAutoOracle lowTerms lowLogFuel)
        (follow middleRoot chunk005Path))

def chunk006Path : Path :=
  [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .upper }, { axis := .k, branch := .lower }, { axis := .k, branch := .lower }, { axis := .k, branch := .lower }]

def chunk006Packed : String :=
  "kkhMMhMMkhMMhMM"

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem chunk006_checked :
    packedCheck (middleAutoOracle lowTerms lowLogFuel)
      (follow middleRoot chunk006Path) chunk006Packed = true := by
  rfl'

noncomputable def chunk006 :
    CheckedChunk (middleAutoOracle lowTerms lowLogFuel)
      (follow middleRoot chunk006Path) :=
  PackedCheckedChunk.toCheckedChunk
    ({ packed := chunk006Packed
       checked := chunk006_checked } :
      PackedCheckedChunk (middleAutoOracle lowTerms lowLogFuel)
        (follow middleRoot chunk006Path))

def chunk007Path : Path :=
  [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .upper }, { axis := .k, branch := .lower }, { axis := .k, branch := .lower }, { axis := .k, branch := .upper }]

def chunk007Packed : String :=
  "khMMhMM"

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem chunk007_checked :
    packedCheck (middleAutoOracle lowTerms lowLogFuel)
      (follow middleRoot chunk007Path) chunk007Packed = true := by
  rfl'

noncomputable def chunk007 :
    CheckedChunk (middleAutoOracle lowTerms lowLogFuel)
      (follow middleRoot chunk007Path) :=
  PackedCheckedChunk.toCheckedChunk
    ({ packed := chunk007Packed
       checked := chunk007_checked } :
      PackedCheckedChunk (middleAutoOracle lowTerms lowLogFuel)
        (follow middleRoot chunk007Path))

end L7MiddleG01
end CourtadeKumar.LRIdealFinalRefinedReplayGenerated
