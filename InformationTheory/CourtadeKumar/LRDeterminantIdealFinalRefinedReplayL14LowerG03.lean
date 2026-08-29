import InformationTheory.CourtadeKumar.LRDeterminantIdealFinalRefinedReplayConfig

/-! Generated full-input packed checks for one bounded chunk group. -/

namespace CourtadeKumar.LRIdealFinalRefinedReplayGenerated
namespace L14LowerG03

open LRLowKIdealMeanValue
open LRLowKIdealMeanValuePackedCertificate
open LRIdealCenteredMeanOracle
open LRIdealHistoricalReplayAssembly

def chunk012Path : Path :=
  [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .upper }, { axis := .k, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .k, branch := .upper }]

def chunk012Packed : String :=
  "hkMMkMM"

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem chunk012_checked :
    packedCheck (restrictedAutoOracle restrictedTerms restrictedLogFuel)
      (follow restrictedLowerRoot chunk012Path) chunk012Packed = true := by
  rfl'

noncomputable def chunk012 :
    CheckedChunk (restrictedAutoOracle restrictedTerms restrictedLogFuel)
      (follow restrictedLowerRoot chunk012Path) :=
  PackedCheckedChunk.toCheckedChunk
    ({ packed := chunk012Packed
       checked := chunk012_checked } :
      PackedCheckedChunk (restrictedAutoOracle restrictedTerms restrictedLogFuel)
        (follow restrictedLowerRoot chunk012Path))

def chunk013Path : Path :=
  [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .upper }, { axis := .k, branch := .lower }, { axis := .chi, branch := .upper }]

def chunk013Packed : String :=
  "khkMMMhMM"

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem chunk013_checked :
    packedCheck (restrictedAutoOracle restrictedTerms restrictedLogFuel)
      (follow restrictedLowerRoot chunk013Path) chunk013Packed = true := by
  rfl'

noncomputable def chunk013 :
    CheckedChunk (restrictedAutoOracle restrictedTerms restrictedLogFuel)
      (follow restrictedLowerRoot chunk013Path) :=
  PackedCheckedChunk.toCheckedChunk
    ({ packed := chunk013Packed
       checked := chunk013_checked } :
      PackedCheckedChunk (restrictedAutoOracle restrictedTerms restrictedLogFuel)
        (follow restrictedLowerRoot chunk013Path))

def chunk014Path : Path :=
  [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .upper }, { axis := .k, branch := .upper }, { axis := .chi, branch := .lower }]

def chunk014Packed : String :=
  "khkMMMhMM"

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem chunk014_checked :
    packedCheck (restrictedAutoOracle restrictedTerms restrictedLogFuel)
      (follow restrictedLowerRoot chunk014Path) chunk014Packed = true := by
  rfl'

noncomputable def chunk014 :
    CheckedChunk (restrictedAutoOracle restrictedTerms restrictedLogFuel)
      (follow restrictedLowerRoot chunk014Path) :=
  PackedCheckedChunk.toCheckedChunk
    ({ packed := chunk014Packed
       checked := chunk014_checked } :
      PackedCheckedChunk (restrictedAutoOracle restrictedTerms restrictedLogFuel)
        (follow restrictedLowerRoot chunk014Path))

def chunk015Path : Path :=
  [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .upper }, { axis := .k, branch := .upper }, { axis := .chi, branch := .upper }]

def chunk015Packed : String :=
  "khMMhMM"

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem chunk015_checked :
    packedCheck (restrictedAutoOracle restrictedTerms restrictedLogFuel)
      (follow restrictedLowerRoot chunk015Path) chunk015Packed = true := by
  rfl'

noncomputable def chunk015 :
    CheckedChunk (restrictedAutoOracle restrictedTerms restrictedLogFuel)
      (follow restrictedLowerRoot chunk015Path) :=
  PackedCheckedChunk.toCheckedChunk
    ({ packed := chunk015Packed
       checked := chunk015_checked } :
      PackedCheckedChunk (restrictedAutoOracle restrictedTerms restrictedLogFuel)
        (follow restrictedLowerRoot chunk015Path))

end L14LowerG03
end CourtadeKumar.LRIdealFinalRefinedReplayGenerated
