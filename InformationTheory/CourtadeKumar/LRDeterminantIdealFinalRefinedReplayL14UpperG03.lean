import InformationTheory.CourtadeKumar.LRDeterminantIdealFinalRefinedReplayConfig

/-! Generated full-input packed checks for one bounded chunk group. -/

namespace CourtadeKumar.LRIdealFinalRefinedReplayGenerated
namespace L14UpperG03

open LRLowKIdealMeanValue
open LRLowKIdealMeanValuePackedCertificate
open LRIdealCenteredMeanOracle
open LRIdealHistoricalReplayAssembly

def chunk012Path : Path :=
  [{ axis := .chi, branch := .upper }, { axis := .k, branch := .lower }, { axis := .chi, branch := .lower }]

def chunk012Packed : String :=
  "khkMMMhMM"

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem chunk012_checked :
    packedCheck (restrictedAutoOracle restrictedTerms restrictedLogFuel)
      (follow restrictedUpperRoot chunk012Path) chunk012Packed = true := by
  rfl'

noncomputable def chunk012 :
    CheckedChunk (restrictedAutoOracle restrictedTerms restrictedLogFuel)
      (follow restrictedUpperRoot chunk012Path) :=
  PackedCheckedChunk.toCheckedChunk
    ({ packed := chunk012Packed
       checked := chunk012_checked } :
      PackedCheckedChunk (restrictedAutoOracle restrictedTerms restrictedLogFuel)
        (follow restrictedUpperRoot chunk012Path))

def chunk013Path : Path :=
  [{ axis := .chi, branch := .upper }, { axis := .k, branch := .lower }, { axis := .chi, branch := .upper }]

def chunk013Packed : String :=
  "khMMhMM"

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem chunk013_checked :
    packedCheck (restrictedAutoOracle restrictedTerms restrictedLogFuel)
      (follow restrictedUpperRoot chunk013Path) chunk013Packed = true := by
  rfl'

noncomputable def chunk013 :
    CheckedChunk (restrictedAutoOracle restrictedTerms restrictedLogFuel)
      (follow restrictedUpperRoot chunk013Path) :=
  PackedCheckedChunk.toCheckedChunk
    ({ packed := chunk013Packed
       checked := chunk013_checked } :
      PackedCheckedChunk (restrictedAutoOracle restrictedTerms restrictedLogFuel)
        (follow restrictedUpperRoot chunk013Path))

def chunk014Path : Path :=
  [{ axis := .chi, branch := .upper }, { axis := .k, branch := .upper }]

def chunk014Packed : String :=
  "hhkMMkMMhkMMM"

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem chunk014_checked :
    packedCheck (restrictedAutoOracle restrictedTerms restrictedLogFuel)
      (follow restrictedUpperRoot chunk014Path) chunk014Packed = true := by
  rfl'

noncomputable def chunk014 :
    CheckedChunk (restrictedAutoOracle restrictedTerms restrictedLogFuel)
      (follow restrictedUpperRoot chunk014Path) :=
  PackedCheckedChunk.toCheckedChunk
    ({ packed := chunk014Packed
       checked := chunk014_checked } :
      PackedCheckedChunk (restrictedAutoOracle restrictedTerms restrictedLogFuel)
        (follow restrictedUpperRoot chunk014Path))

end L14UpperG03
end CourtadeKumar.LRIdealFinalRefinedReplayGenerated
