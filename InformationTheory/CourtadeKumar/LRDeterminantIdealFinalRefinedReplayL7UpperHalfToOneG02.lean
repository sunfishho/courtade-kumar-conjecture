import InformationTheory.CourtadeKumar.LRDeterminantIdealFinalRefinedReplayConfig

/-! Generated full-input packed checks for one bounded chunk group. -/

namespace CourtadeKumar.LRIdealFinalRefinedReplayGenerated
namespace L7UpperHalfToOneG02

open LRLowKIdealMeanValue
open LRLowKIdealMeanValuePackedCertificate
open LRIdealCenteredMeanOracle
open LRIdealHistoricalReplayAssembly

def chunk008Path : Path :=
  [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .upper }, { axis := .k, branch := .upper }, { axis := .k, branch := .lower }, { axis := .chi, branch := .upper }]

def chunk008Packed : String :=
  "khkMMkMMhkMMkMM"

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem chunk008_checked :
    packedCheck (upperAutoOracle lowTerms lowLogFuel)
      (follow lowKUpperHalfToOneRoot chunk008Path) chunk008Packed = true := by
  rfl'

noncomputable def chunk008 :
    CheckedChunk (upperAutoOracle lowTerms lowLogFuel)
      (follow lowKUpperHalfToOneRoot chunk008Path) :=
  PackedCheckedChunk.toCheckedChunk
    ({ packed := chunk008Packed
       checked := chunk008_checked } :
      PackedCheckedChunk (upperAutoOracle lowTerms lowLogFuel)
        (follow lowKUpperHalfToOneRoot chunk008Path))

def chunk009Path : Path :=
  [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .upper }, { axis := .k, branch := .upper }, { axis := .k, branch := .upper }, { axis := .chi, branch := .lower }]

def chunk009Packed : String :=
  "hkMhMMkkMMhMkMM"

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem chunk009_checked :
    packedCheck (upperAutoOracle lowTerms lowLogFuel)
      (follow lowKUpperHalfToOneRoot chunk009Path) chunk009Packed = true := by
  rfl'

noncomputable def chunk009 :
    CheckedChunk (upperAutoOracle lowTerms lowLogFuel)
      (follow lowKUpperHalfToOneRoot chunk009Path) :=
  PackedCheckedChunk.toCheckedChunk
    ({ packed := chunk009Packed
       checked := chunk009_checked } :
      PackedCheckedChunk (upperAutoOracle lowTerms lowLogFuel)
        (follow lowKUpperHalfToOneRoot chunk009Path))

def chunk010Path : Path :=
  [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .upper }, { axis := .k, branch := .upper }, { axis := .k, branch := .upper }, { axis := .chi, branch := .upper }, { axis := .k, branch := .lower }]

def chunk010Packed : String :=
  "hkMMkMM"

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem chunk010_checked :
    packedCheck (upperAutoOracle lowTerms lowLogFuel)
      (follow lowKUpperHalfToOneRoot chunk010Path) chunk010Packed = true := by
  rfl'

noncomputable def chunk010 :
    CheckedChunk (upperAutoOracle lowTerms lowLogFuel)
      (follow lowKUpperHalfToOneRoot chunk010Path) :=
  PackedCheckedChunk.toCheckedChunk
    ({ packed := chunk010Packed
       checked := chunk010_checked } :
      PackedCheckedChunk (upperAutoOracle lowTerms lowLogFuel)
        (follow lowKUpperHalfToOneRoot chunk010Path))

def chunk011Path : Path :=
  [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .upper }, { axis := .k, branch := .upper }, { axis := .k, branch := .upper }, { axis := .chi, branch := .upper }, { axis := .k, branch := .upper }]

def chunk011Packed : String :=
  "hkhMMhMMkhMMhMM"

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem chunk011_checked :
    packedCheck (upperAutoOracle lowTerms lowLogFuel)
      (follow lowKUpperHalfToOneRoot chunk011Path) chunk011Packed = true := by
  rfl'

noncomputable def chunk011 :
    CheckedChunk (upperAutoOracle lowTerms lowLogFuel)
      (follow lowKUpperHalfToOneRoot chunk011Path) :=
  PackedCheckedChunk.toCheckedChunk
    ({ packed := chunk011Packed
       checked := chunk011_checked } :
      PackedCheckedChunk (upperAutoOracle lowTerms lowLogFuel)
        (follow lowKUpperHalfToOneRoot chunk011Path))

end L7UpperHalfToOneG02
end CourtadeKumar.LRIdealFinalRefinedReplayGenerated
