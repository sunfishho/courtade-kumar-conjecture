import InformationTheory.CourtadeKumar.LRDeterminantIdealFinalRefinedReplayConfig

/-! Generated full-input packed checks for one bounded chunk group. -/

namespace CourtadeKumar.LRIdealFinalRefinedReplayGenerated
namespace L14LowerG01

open LRLowKIdealMeanValue
open LRLowKIdealMeanValuePackedCertificate
open LRIdealCenteredMeanOracle
open LRIdealHistoricalReplayAssembly

def chunk004Path : Path :=
  [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .upper }, { axis := .k, branch := .lower }]

def chunk004Packed : String :=
  "khkMMkMMhMkMM"

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem chunk004_checked :
    packedCheck (restrictedAutoOracle restrictedTerms restrictedLogFuel)
      (follow restrictedLowerRoot chunk004Path) chunk004Packed = true := by
  rfl'

noncomputable def chunk004 :
    CheckedChunk (restrictedAutoOracle restrictedTerms restrictedLogFuel)
      (follow restrictedLowerRoot chunk004Path) :=
  PackedCheckedChunk.toCheckedChunk
    ({ packed := chunk004Packed
       checked := chunk004_checked } :
      PackedCheckedChunk (restrictedAutoOracle restrictedTerms restrictedLogFuel)
        (follow restrictedLowerRoot chunk004Path))

def chunk005Path : Path :=
  [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .upper }, { axis := .k, branch := .upper }]

def chunk005Packed : String :=
  "khMMhMM"

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem chunk005_checked :
    packedCheck (restrictedAutoOracle restrictedTerms restrictedLogFuel)
      (follow restrictedLowerRoot chunk005Path) chunk005Packed = true := by
  rfl'

noncomputable def chunk005 :
    CheckedChunk (restrictedAutoOracle restrictedTerms restrictedLogFuel)
      (follow restrictedLowerRoot chunk005Path) :=
  PackedCheckedChunk.toCheckedChunk
    ({ packed := chunk005Packed
       checked := chunk005_checked } :
      PackedCheckedChunk (restrictedAutoOracle restrictedTerms restrictedLogFuel)
        (follow restrictedLowerRoot chunk005Path))

def chunk006Path : Path :=
  [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .upper }, { axis := .k, branch := .lower }, { axis := .k, branch := .lower }, { axis := .chi, branch := .lower }]

def chunk006Packed : String :=
  "khMkMMhMM"

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem chunk006_checked :
    packedCheck (restrictedAutoOracle restrictedTerms restrictedLogFuel)
      (follow restrictedLowerRoot chunk006Path) chunk006Packed = true := by
  rfl'

noncomputable def chunk006 :
    CheckedChunk (restrictedAutoOracle restrictedTerms restrictedLogFuel)
      (follow restrictedLowerRoot chunk006Path) :=
  PackedCheckedChunk.toCheckedChunk
    ({ packed := chunk006Packed
       checked := chunk006_checked } :
      PackedCheckedChunk (restrictedAutoOracle restrictedTerms restrictedLogFuel)
        (follow restrictedLowerRoot chunk006Path))

def chunk007Path : Path :=
  [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .upper }, { axis := .k, branch := .lower }, { axis := .k, branch := .lower }, { axis := .chi, branch := .upper }]

def chunk007Packed : String :=
  "kkhMMMkMM"

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem chunk007_checked :
    packedCheck (restrictedAutoOracle restrictedTerms restrictedLogFuel)
      (follow restrictedLowerRoot chunk007Path) chunk007Packed = true := by
  rfl'

noncomputable def chunk007 :
    CheckedChunk (restrictedAutoOracle restrictedTerms restrictedLogFuel)
      (follow restrictedLowerRoot chunk007Path) :=
  PackedCheckedChunk.toCheckedChunk
    ({ packed := chunk007Packed
       checked := chunk007_checked } :
      PackedCheckedChunk (restrictedAutoOracle restrictedTerms restrictedLogFuel)
        (follow restrictedLowerRoot chunk007Path))

end L14LowerG01
end CourtadeKumar.LRIdealFinalRefinedReplayGenerated
