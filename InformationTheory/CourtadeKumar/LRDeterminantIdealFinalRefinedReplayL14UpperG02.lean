import InformationTheory.CourtadeKumar.LRDeterminantIdealFinalRefinedReplayConfig

/-! Generated full-input packed checks for one bounded chunk group. -/

namespace CourtadeKumar.LRIdealFinalRefinedReplayGenerated
namespace L14UpperG02

open LRLowKIdealMeanValue
open LRLowKIdealMeanValuePackedCertificate
open LRIdealCenteredMeanOracle
open LRIdealHistoricalReplayAssembly

def chunk008Path : Path :=
  [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .upper }, { axis := .k, branch := .upper }]

def chunk008Packed : String :=
  "hkkMMkMMkkMMM"

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem chunk008_checked :
    packedCheck (restrictedAutoOracle restrictedTerms restrictedLogFuel)
      (follow restrictedUpperRoot chunk008Path) chunk008Packed = true := by
  rfl'

noncomputable def chunk008 :
    CheckedChunk (restrictedAutoOracle restrictedTerms restrictedLogFuel)
      (follow restrictedUpperRoot chunk008Path) :=
  PackedCheckedChunk.toCheckedChunk
    ({ packed := chunk008Packed
       checked := chunk008_checked } :
      PackedCheckedChunk (restrictedAutoOracle restrictedTerms restrictedLogFuel)
        (follow restrictedUpperRoot chunk008Path))

def chunk009Path : Path :=
  [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .upper }, { axis := .k, branch := .lower }, { axis := .chi, branch := .lower }]

def chunk009Packed : String :=
  "khkMMkMMhkMMM"

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem chunk009_checked :
    packedCheck (restrictedAutoOracle restrictedTerms restrictedLogFuel)
      (follow restrictedUpperRoot chunk009Path) chunk009Packed = true := by
  rfl'

noncomputable def chunk009 :
    CheckedChunk (restrictedAutoOracle restrictedTerms restrictedLogFuel)
      (follow restrictedUpperRoot chunk009Path) :=
  PackedCheckedChunk.toCheckedChunk
    ({ packed := chunk009Packed
       checked := chunk009_checked } :
      PackedCheckedChunk (restrictedAutoOracle restrictedTerms restrictedLogFuel)
        (follow restrictedUpperRoot chunk009Path))

def chunk010Path : Path :=
  [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .upper }, { axis := .k, branch := .lower }, { axis := .chi, branch := .upper }]

def chunk010Packed : String :=
  "khkMMMhMM"

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem chunk010_checked :
    packedCheck (restrictedAutoOracle restrictedTerms restrictedLogFuel)
      (follow restrictedUpperRoot chunk010Path) chunk010Packed = true := by
  rfl'

noncomputable def chunk010 :
    CheckedChunk (restrictedAutoOracle restrictedTerms restrictedLogFuel)
      (follow restrictedUpperRoot chunk010Path) :=
  PackedCheckedChunk.toCheckedChunk
    ({ packed := chunk010Packed
       checked := chunk010_checked } :
      PackedCheckedChunk (restrictedAutoOracle restrictedTerms restrictedLogFuel)
        (follow restrictedUpperRoot chunk010Path))

def chunk011Path : Path :=
  [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .upper }, { axis := .k, branch := .upper }]

def chunk011Packed : String :=
  "hkhMMhMMkhMMhMM"

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem chunk011_checked :
    packedCheck (restrictedAutoOracle restrictedTerms restrictedLogFuel)
      (follow restrictedUpperRoot chunk011Path) chunk011Packed = true := by
  rfl'

noncomputable def chunk011 :
    CheckedChunk (restrictedAutoOracle restrictedTerms restrictedLogFuel)
      (follow restrictedUpperRoot chunk011Path) :=
  PackedCheckedChunk.toCheckedChunk
    ({ packed := chunk011Packed
       checked := chunk011_checked } :
      PackedCheckedChunk (restrictedAutoOracle restrictedTerms restrictedLogFuel)
        (follow restrictedUpperRoot chunk011Path))

end L14UpperG02
end CourtadeKumar.LRIdealFinalRefinedReplayGenerated
