import InformationTheory.CourtadeKumar.LRDeterminantIdealFinalRefinedReplayL7MiddleG00
import InformationTheory.CourtadeKumar.LRDeterminantIdealFinalRefinedReplayL7MiddleG01
import InformationTheory.CourtadeKumar.LRDeterminantIdealFinalRefinedReplayL7MiddleG02
import InformationTheory.CourtadeKumar.LRDeterminantIdealFinalRefinedReplayL7MiddleG03
import InformationTheory.CourtadeKumar.LRDeterminantIdealFinalRefinedReplayL7MiddleG04
import InformationTheory.CourtadeKumar.LRDeterminantIdealFinalRefinedReplayL7MiddleG05
import InformationTheory.CourtadeKumar.LRDeterminantIdealFinalRefinedReplayL7UpperFiveThirtySecondsToQuarterG00
import InformationTheory.CourtadeKumar.LRDeterminantIdealFinalRefinedReplayL7UpperFiveThirtySecondsToQuarterG01
import InformationTheory.CourtadeKumar.LRDeterminantIdealFinalRefinedReplayL7UpperFiveThirtySecondsToQuarterG02
import InformationTheory.CourtadeKumar.LRDeterminantIdealFinalRefinedReplayL7UpperQuarterToHalfG00
import InformationTheory.CourtadeKumar.LRDeterminantIdealFinalRefinedReplayL7UpperQuarterToHalfG01
import InformationTheory.CourtadeKumar.LRDeterminantIdealFinalRefinedReplayL7UpperQuarterToHalfG02
import InformationTheory.CourtadeKumar.LRDeterminantIdealFinalRefinedReplayL7UpperHalfToOneG00
import InformationTheory.CourtadeKumar.LRDeterminantIdealFinalRefinedReplayL7UpperHalfToOneG01
import InformationTheory.CourtadeKumar.LRDeterminantIdealFinalRefinedReplayL7UpperHalfToOneG02
import InformationTheory.CourtadeKumar.LRDeterminantIdealFinalRefinedReplayL7UpperHalfToOneG03
import InformationTheory.CourtadeKumar.LRDeterminantIdealFinalRefinedReplayL7UpperHalfToOneG04
import InformationTheory.CourtadeKumar.LRDeterminantIdealFinalRefinedReplayL7UpperHalfToOneG05
import InformationTheory.CourtadeKumar.LRDeterminantIdealFinalRefinedReplayL14LowerG00
import InformationTheory.CourtadeKumar.LRDeterminantIdealFinalRefinedReplayL14LowerG01
import InformationTheory.CourtadeKumar.LRDeterminantIdealFinalRefinedReplayL14LowerG02
import InformationTheory.CourtadeKumar.LRDeterminantIdealFinalRefinedReplayL14LowerG03
import InformationTheory.CourtadeKumar.LRDeterminantIdealFinalRefinedReplayL14LowerG04
import InformationTheory.CourtadeKumar.LRDeterminantIdealFinalRefinedReplayL14UpperG00
import InformationTheory.CourtadeKumar.LRDeterminantIdealFinalRefinedReplayL14UpperG01
import InformationTheory.CourtadeKumar.LRDeterminantIdealFinalRefinedReplayL14UpperG02
import InformationTheory.CourtadeKumar.LRDeterminantIdealFinalRefinedReplayL14UpperG03

/-! Generated structural joins and the two closed historical replay theorems. -/

namespace CourtadeKumar
namespace LRIdealFinalRefinedReplayGenerated

open LRLowKIdealMeanValue
open LRLowKIdealMeanValuePackedCertificate
open LRIdealCenteredMeanOracle
open LRIdealHistoricalReplayAssembly

namespace L7MiddleAssembly

noncomputable def node_h0_h0_h0_h0_h0_h0 :
    CheckedChunk (middleAutoOracle lowTerms lowLogFuel)
      (follow middleRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }]) :=
  joinAtPath middleRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }]
    .k
    (by
      simpa [L7MiddleG00.chunk000Path] using L7MiddleG00.chunk000)
    (by
      simpa [L7MiddleG00.chunk001Path] using L7MiddleG00.chunk001)

noncomputable def node_h0_h0_h0_h0_h0 :
    CheckedChunk (middleAutoOracle lowTerms lowLogFuel)
      (follow middleRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }]) :=
  joinAtPath middleRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }]
    .chi
    (by simpa using node_h0_h0_h0_h0_h0_h0)
    (by
      simpa [L7MiddleG00.chunk002Path] using L7MiddleG00.chunk002)

noncomputable def node_h0_h0_h0_h0 :
    CheckedChunk (middleAutoOracle lowTerms lowLogFuel)
      (follow middleRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }]) :=
  joinAtPath middleRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }]
    .chi
    (by simpa using node_h0_h0_h0_h0_h0)
    (by
      simpa [L7MiddleG00.chunk003Path] using L7MiddleG00.chunk003)

noncomputable def node_h0_h0_h0_h1 :
    CheckedChunk (middleAutoOracle lowTerms lowLogFuel)
      (follow middleRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .upper }]) :=
  joinAtPath middleRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .upper }]
    .k
    (by
      simpa [L7MiddleG01.chunk004Path] using L7MiddleG01.chunk004)
    (by
      simpa [L7MiddleG01.chunk005Path] using L7MiddleG01.chunk005)

noncomputable def node_h0_h0_h0 :
    CheckedChunk (middleAutoOracle lowTerms lowLogFuel)
      (follow middleRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }]) :=
  joinAtPath middleRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }]
    .chi
    (by simpa using node_h0_h0_h0_h0)
    (by simpa using node_h0_h0_h0_h1)

noncomputable def node_h0_h0_h1_k0_k0 :
    CheckedChunk (middleAutoOracle lowTerms lowLogFuel)
      (follow middleRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .upper }, { axis := .k, branch := .lower }, { axis := .k, branch := .lower }]) :=
  joinAtPath middleRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .upper }, { axis := .k, branch := .lower }, { axis := .k, branch := .lower }]
    .k
    (by
      simpa [L7MiddleG01.chunk006Path] using L7MiddleG01.chunk006)
    (by
      simpa [L7MiddleG01.chunk007Path] using L7MiddleG01.chunk007)

noncomputable def node_h0_h0_h1_k0 :
    CheckedChunk (middleAutoOracle lowTerms lowLogFuel)
      (follow middleRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .upper }, { axis := .k, branch := .lower }]) :=
  joinAtPath middleRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .upper }, { axis := .k, branch := .lower }]
    .k
    (by simpa using node_h0_h0_h1_k0_k0)
    (by
      simpa [L7MiddleG02.chunk008Path] using L7MiddleG02.chunk008)

noncomputable def node_h0_h0_h1_k1_k1 :
    CheckedChunk (middleAutoOracle lowTerms lowLogFuel)
      (follow middleRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .upper }, { axis := .k, branch := .upper }, { axis := .k, branch := .upper }]) :=
  joinAtPath middleRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .upper }, { axis := .k, branch := .upper }, { axis := .k, branch := .upper }]
    .k
    (by
      simpa [L7MiddleG02.chunk010Path] using L7MiddleG02.chunk010)
    (by
      simpa [L7MiddleG02.chunk011Path] using L7MiddleG02.chunk011)

noncomputable def node_h0_h0_h1_k1 :
    CheckedChunk (middleAutoOracle lowTerms lowLogFuel)
      (follow middleRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .upper }, { axis := .k, branch := .upper }]) :=
  joinAtPath middleRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .upper }, { axis := .k, branch := .upper }]
    .k
    (by
      simpa [L7MiddleG02.chunk009Path] using L7MiddleG02.chunk009)
    (by simpa using node_h0_h0_h1_k1_k1)

noncomputable def node_h0_h0_h1 :
    CheckedChunk (middleAutoOracle lowTerms lowLogFuel)
      (follow middleRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .upper }]) :=
  joinAtPath middleRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .upper }]
    .k
    (by simpa using node_h0_h0_h1_k0)
    (by simpa using node_h0_h0_h1_k1)

noncomputable def node_h0_h0 :
    CheckedChunk (middleAutoOracle lowTerms lowLogFuel)
      (follow middleRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }]) :=
  joinAtPath middleRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }]
    .chi
    (by simpa using node_h0_h0_h0)
    (by simpa using node_h0_h0_h1)

noncomputable def node_h0_h1_k0_k0 :
    CheckedChunk (middleAutoOracle lowTerms lowLogFuel)
      (follow middleRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .upper }, { axis := .k, branch := .lower }, { axis := .k, branch := .lower }]) :=
  joinAtPath middleRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .upper }, { axis := .k, branch := .lower }, { axis := .k, branch := .lower }]
    .k
    (by
      simpa [L7MiddleG03.chunk012Path] using L7MiddleG03.chunk012)
    (by
      simpa [L7MiddleG03.chunk013Path] using L7MiddleG03.chunk013)

noncomputable def node_h0_h1_k0 :
    CheckedChunk (middleAutoOracle lowTerms lowLogFuel)
      (follow middleRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .upper }, { axis := .k, branch := .lower }]) :=
  joinAtPath middleRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .upper }, { axis := .k, branch := .lower }]
    .k
    (by simpa using node_h0_h1_k0_k0)
    (by
      simpa [L7MiddleG03.chunk014Path] using L7MiddleG03.chunk014)

noncomputable def node_h0_h1_k1_k1_h0 :
    CheckedChunk (middleAutoOracle lowTerms lowLogFuel)
      (follow middleRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .upper }, { axis := .k, branch := .upper }, { axis := .k, branch := .upper }, { axis := .chi, branch := .lower }]) :=
  joinAtPath middleRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .upper }, { axis := .k, branch := .upper }, { axis := .k, branch := .upper }, { axis := .chi, branch := .lower }]
    .k
    (by
      simpa [L7MiddleG04.chunk016Path] using L7MiddleG04.chunk016)
    (by
      simpa [L7MiddleG04.chunk017Path] using L7MiddleG04.chunk017)

noncomputable def node_h0_h1_k1_k1 :
    CheckedChunk (middleAutoOracle lowTerms lowLogFuel)
      (follow middleRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .upper }, { axis := .k, branch := .upper }, { axis := .k, branch := .upper }]) :=
  joinAtPath middleRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .upper }, { axis := .k, branch := .upper }, { axis := .k, branch := .upper }]
    .chi
    (by simpa using node_h0_h1_k1_k1_h0)
    (by
      simpa [L7MiddleG04.chunk018Path] using L7MiddleG04.chunk018)

noncomputable def node_h0_h1_k1 :
    CheckedChunk (middleAutoOracle lowTerms lowLogFuel)
      (follow middleRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .upper }, { axis := .k, branch := .upper }]) :=
  joinAtPath middleRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .upper }, { axis := .k, branch := .upper }]
    .k
    (by
      simpa [L7MiddleG03.chunk015Path] using L7MiddleG03.chunk015)
    (by simpa using node_h0_h1_k1_k1)

noncomputable def node_h0_h1 :
    CheckedChunk (middleAutoOracle lowTerms lowLogFuel)
      (follow middleRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .upper }]) :=
  joinAtPath middleRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .upper }]
    .k
    (by simpa using node_h0_h1_k0)
    (by simpa using node_h0_h1_k1)

noncomputable def node_h0 :
    CheckedChunk (middleAutoOracle lowTerms lowLogFuel)
      (follow middleRoot [{ axis := .chi, branch := .lower }]) :=
  joinAtPath middleRoot [{ axis := .chi, branch := .lower }]
    .chi
    (by simpa using node_h0_h0)
    (by simpa using node_h0_h1)

noncomputable def node_h1_k0 :
    CheckedChunk (middleAutoOracle lowTerms lowLogFuel)
      (follow middleRoot [{ axis := .chi, branch := .upper }, { axis := .k, branch := .lower }]) :=
  joinAtPath middleRoot [{ axis := .chi, branch := .upper }, { axis := .k, branch := .lower }]
    .k
    (by
      simpa [L7MiddleG04.chunk019Path] using L7MiddleG04.chunk019)
    (by
      simpa [L7MiddleG05.chunk020Path] using L7MiddleG05.chunk020)

noncomputable def node_h1 :
    CheckedChunk (middleAutoOracle lowTerms lowLogFuel)
      (follow middleRoot [{ axis := .chi, branch := .upper }]) :=
  joinAtPath middleRoot [{ axis := .chi, branch := .upper }]
    .k
    (by simpa using node_h1_k0)
    (by
      simpa [L7MiddleG05.chunk021Path] using L7MiddleG05.chunk021)

noncomputable def node_root :
    CheckedChunk (middleAutoOracle lowTerms lowLogFuel)
      (follow middleRoot []) :=
  joinAtPath middleRoot []
    .chi
    (by simpa using node_h0)
    (by simpa using node_h1)

noncomputable def checkedTree :
    CheckedTree (middleAutoOracle lowTerms lowLogFuel) middleRoot :=
  CheckedChunk.toCheckedTree
    (by
      simpa [follow] using node_root)

end L7MiddleAssembly

namespace L7UpperFiveThirtySecondsToQuarterAssembly

noncomputable def node_h0_h0_h0 :
    CheckedChunk (upperAutoOracle lowTerms lowLogFuel)
      (follow lowKUpperFiveThirtySecondsToQuarterRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }]) :=
  joinAtPath lowKUpperFiveThirtySecondsToQuarterRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }]
    .chi
    (by
      simpa [L7UpperFiveThirtySecondsToQuarterG00.chunk000Path] using L7UpperFiveThirtySecondsToQuarterG00.chunk000)
    (by
      simpa [L7UpperFiveThirtySecondsToQuarterG00.chunk001Path] using L7UpperFiveThirtySecondsToQuarterG00.chunk001)

noncomputable def node_h0_h0_h1_k0 :
    CheckedChunk (upperAutoOracle lowTerms lowLogFuel)
      (follow lowKUpperFiveThirtySecondsToQuarterRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .upper }, { axis := .k, branch := .lower }]) :=
  joinAtPath lowKUpperFiveThirtySecondsToQuarterRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .upper }, { axis := .k, branch := .lower }]
    .k
    (by
      simpa [L7UpperFiveThirtySecondsToQuarterG00.chunk002Path] using L7UpperFiveThirtySecondsToQuarterG00.chunk002)
    (by
      simpa [L7UpperFiveThirtySecondsToQuarterG00.chunk003Path] using L7UpperFiveThirtySecondsToQuarterG00.chunk003)

noncomputable def node_h0_h0_h1 :
    CheckedChunk (upperAutoOracle lowTerms lowLogFuel)
      (follow lowKUpperFiveThirtySecondsToQuarterRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .upper }]) :=
  joinAtPath lowKUpperFiveThirtySecondsToQuarterRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .upper }]
    .k
    (by simpa using node_h0_h0_h1_k0)
    (by
      simpa [L7UpperFiveThirtySecondsToQuarterG01.chunk004Path] using L7UpperFiveThirtySecondsToQuarterG01.chunk004)

noncomputable def node_h0_h0 :
    CheckedChunk (upperAutoOracle lowTerms lowLogFuel)
      (follow lowKUpperFiveThirtySecondsToQuarterRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }]) :=
  joinAtPath lowKUpperFiveThirtySecondsToQuarterRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }]
    .chi
    (by simpa using node_h0_h0_h0)
    (by simpa using node_h0_h0_h1)

noncomputable def node_h0_h1_k0_k0 :
    CheckedChunk (upperAutoOracle lowTerms lowLogFuel)
      (follow lowKUpperFiveThirtySecondsToQuarterRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .upper }, { axis := .k, branch := .lower }, { axis := .k, branch := .lower }]) :=
  joinAtPath lowKUpperFiveThirtySecondsToQuarterRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .upper }, { axis := .k, branch := .lower }, { axis := .k, branch := .lower }]
    .chi
    (by
      simpa [L7UpperFiveThirtySecondsToQuarterG01.chunk005Path] using L7UpperFiveThirtySecondsToQuarterG01.chunk005)
    (by
      simpa [L7UpperFiveThirtySecondsToQuarterG01.chunk006Path] using L7UpperFiveThirtySecondsToQuarterG01.chunk006)

noncomputable def node_h0_h1_k0 :
    CheckedChunk (upperAutoOracle lowTerms lowLogFuel)
      (follow lowKUpperFiveThirtySecondsToQuarterRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .upper }, { axis := .k, branch := .lower }]) :=
  joinAtPath lowKUpperFiveThirtySecondsToQuarterRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .upper }, { axis := .k, branch := .lower }]
    .k
    (by simpa using node_h0_h1_k0_k0)
    (by
      simpa [L7UpperFiveThirtySecondsToQuarterG01.chunk007Path] using L7UpperFiveThirtySecondsToQuarterG01.chunk007)

noncomputable def node_h0_h1 :
    CheckedChunk (upperAutoOracle lowTerms lowLogFuel)
      (follow lowKUpperFiveThirtySecondsToQuarterRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .upper }]) :=
  joinAtPath lowKUpperFiveThirtySecondsToQuarterRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .upper }]
    .k
    (by simpa using node_h0_h1_k0)
    (by
      simpa [L7UpperFiveThirtySecondsToQuarterG02.chunk008Path] using L7UpperFiveThirtySecondsToQuarterG02.chunk008)

noncomputable def node_h0 :
    CheckedChunk (upperAutoOracle lowTerms lowLogFuel)
      (follow lowKUpperFiveThirtySecondsToQuarterRoot [{ axis := .chi, branch := .lower }]) :=
  joinAtPath lowKUpperFiveThirtySecondsToQuarterRoot [{ axis := .chi, branch := .lower }]
    .chi
    (by simpa using node_h0_h0)
    (by simpa using node_h0_h1)

noncomputable def node_root :
    CheckedChunk (upperAutoOracle lowTerms lowLogFuel)
      (follow lowKUpperFiveThirtySecondsToQuarterRoot []) :=
  joinAtPath lowKUpperFiveThirtySecondsToQuarterRoot []
    .chi
    (by simpa using node_h0)
    (by
      simpa [L7UpperFiveThirtySecondsToQuarterG02.chunk009Path] using L7UpperFiveThirtySecondsToQuarterG02.chunk009)

noncomputable def checkedTree :
    CheckedTree (upperAutoOracle lowTerms lowLogFuel) lowKUpperFiveThirtySecondsToQuarterRoot :=
  CheckedChunk.toCheckedTree
    (by
      simpa [follow] using node_root)

end L7UpperFiveThirtySecondsToQuarterAssembly

namespace L7UpperQuarterToHalfAssembly

noncomputable def node_h0_h0_h0_h0_h0 :
    CheckedChunk (upperAutoOracle lowTerms lowLogFuel)
      (follow lowKUpperQuarterToHalfRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }]) :=
  joinAtPath lowKUpperQuarterToHalfRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }]
    .chi
    (by
      simpa [L7UpperQuarterToHalfG00.chunk000Path] using L7UpperQuarterToHalfG00.chunk000)
    (by
      simpa [L7UpperQuarterToHalfG00.chunk001Path] using L7UpperQuarterToHalfG00.chunk001)

noncomputable def node_h0_h0_h0_h0 :
    CheckedChunk (upperAutoOracle lowTerms lowLogFuel)
      (follow lowKUpperQuarterToHalfRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }]) :=
  joinAtPath lowKUpperQuarterToHalfRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }]
    .chi
    (by simpa using node_h0_h0_h0_h0_h0)
    (by
      simpa [L7UpperQuarterToHalfG00.chunk002Path] using L7UpperQuarterToHalfG00.chunk002)

noncomputable def node_h0_h0_h0 :
    CheckedChunk (upperAutoOracle lowTerms lowLogFuel)
      (follow lowKUpperQuarterToHalfRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }]) :=
  joinAtPath lowKUpperQuarterToHalfRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }]
    .chi
    (by simpa using node_h0_h0_h0_h0)
    (by
      simpa [L7UpperQuarterToHalfG00.chunk003Path] using L7UpperQuarterToHalfG00.chunk003)

noncomputable def node_h0_h0_h1 :
    CheckedChunk (upperAutoOracle lowTerms lowLogFuel)
      (follow lowKUpperQuarterToHalfRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .upper }]) :=
  joinAtPath lowKUpperQuarterToHalfRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .upper }]
    .k
    (by
      simpa [L7UpperQuarterToHalfG01.chunk004Path] using L7UpperQuarterToHalfG01.chunk004)
    (by
      simpa [L7UpperQuarterToHalfG01.chunk005Path] using L7UpperQuarterToHalfG01.chunk005)

noncomputable def node_h0_h0 :
    CheckedChunk (upperAutoOracle lowTerms lowLogFuel)
      (follow lowKUpperQuarterToHalfRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }]) :=
  joinAtPath lowKUpperQuarterToHalfRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }]
    .chi
    (by simpa using node_h0_h0_h0)
    (by simpa using node_h0_h0_h1)

noncomputable def node_h0_h1_k0 :
    CheckedChunk (upperAutoOracle lowTerms lowLogFuel)
      (follow lowKUpperQuarterToHalfRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .upper }, { axis := .k, branch := .lower }]) :=
  joinAtPath lowKUpperQuarterToHalfRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .upper }, { axis := .k, branch := .lower }]
    .k
    (by
      simpa [L7UpperQuarterToHalfG01.chunk006Path] using L7UpperQuarterToHalfG01.chunk006)
    (by
      simpa [L7UpperQuarterToHalfG01.chunk007Path] using L7UpperQuarterToHalfG01.chunk007)

noncomputable def node_h0_h1 :
    CheckedChunk (upperAutoOracle lowTerms lowLogFuel)
      (follow lowKUpperQuarterToHalfRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .upper }]) :=
  joinAtPath lowKUpperQuarterToHalfRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .upper }]
    .k
    (by simpa using node_h0_h1_k0)
    (by
      simpa [L7UpperQuarterToHalfG02.chunk008Path] using L7UpperQuarterToHalfG02.chunk008)

noncomputable def node_h0 :
    CheckedChunk (upperAutoOracle lowTerms lowLogFuel)
      (follow lowKUpperQuarterToHalfRoot [{ axis := .chi, branch := .lower }]) :=
  joinAtPath lowKUpperQuarterToHalfRoot [{ axis := .chi, branch := .lower }]
    .chi
    (by simpa using node_h0_h0)
    (by simpa using node_h0_h1)

noncomputable def node_h1 :
    CheckedChunk (upperAutoOracle lowTerms lowLogFuel)
      (follow lowKUpperQuarterToHalfRoot [{ axis := .chi, branch := .upper }]) :=
  joinAtPath lowKUpperQuarterToHalfRoot [{ axis := .chi, branch := .upper }]
    .k
    (by
      simpa [L7UpperQuarterToHalfG02.chunk009Path] using L7UpperQuarterToHalfG02.chunk009)
    (by
      simpa [L7UpperQuarterToHalfG02.chunk010Path] using L7UpperQuarterToHalfG02.chunk010)

noncomputable def node_root :
    CheckedChunk (upperAutoOracle lowTerms lowLogFuel)
      (follow lowKUpperQuarterToHalfRoot []) :=
  joinAtPath lowKUpperQuarterToHalfRoot []
    .chi
    (by simpa using node_h0)
    (by simpa using node_h1)

noncomputable def checkedTree :
    CheckedTree (upperAutoOracle lowTerms lowLogFuel) lowKUpperQuarterToHalfRoot :=
  CheckedChunk.toCheckedTree
    (by
      simpa [follow] using node_root)

end L7UpperQuarterToHalfAssembly

namespace L7UpperHalfToOneAssembly

noncomputable def node_h0_h0_h0_h0_h0 :
    CheckedChunk (upperAutoOracle lowTerms lowLogFuel)
      (follow lowKUpperHalfToOneRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }]) :=
  joinAtPath lowKUpperHalfToOneRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }]
    .chi
    (by
      simpa [L7UpperHalfToOneG00.chunk000Path] using L7UpperHalfToOneG00.chunk000)
    (by
      simpa [L7UpperHalfToOneG00.chunk001Path] using L7UpperHalfToOneG00.chunk001)

noncomputable def node_h0_h0_h0_h0 :
    CheckedChunk (upperAutoOracle lowTerms lowLogFuel)
      (follow lowKUpperHalfToOneRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }]) :=
  joinAtPath lowKUpperHalfToOneRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }]
    .chi
    (by simpa using node_h0_h0_h0_h0_h0)
    (by
      simpa [L7UpperHalfToOneG00.chunk002Path] using L7UpperHalfToOneG00.chunk002)

noncomputable def node_h0_h0_h0_h1 :
    CheckedChunk (upperAutoOracle lowTerms lowLogFuel)
      (follow lowKUpperHalfToOneRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .upper }]) :=
  joinAtPath lowKUpperHalfToOneRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .upper }]
    .k
    (by
      simpa [L7UpperHalfToOneG00.chunk003Path] using L7UpperHalfToOneG00.chunk003)
    (by
      simpa [L7UpperHalfToOneG01.chunk004Path] using L7UpperHalfToOneG01.chunk004)

noncomputable def node_h0_h0_h0 :
    CheckedChunk (upperAutoOracle lowTerms lowLogFuel)
      (follow lowKUpperHalfToOneRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }]) :=
  joinAtPath lowKUpperHalfToOneRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }]
    .chi
    (by simpa using node_h0_h0_h0_h0)
    (by simpa using node_h0_h0_h0_h1)

noncomputable def node_h0_h0_h1_k0 :
    CheckedChunk (upperAutoOracle lowTerms lowLogFuel)
      (follow lowKUpperHalfToOneRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .upper }, { axis := .k, branch := .lower }]) :=
  joinAtPath lowKUpperHalfToOneRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .upper }, { axis := .k, branch := .lower }]
    .k
    (by
      simpa [L7UpperHalfToOneG01.chunk005Path] using L7UpperHalfToOneG01.chunk005)
    (by
      simpa [L7UpperHalfToOneG01.chunk006Path] using L7UpperHalfToOneG01.chunk006)

noncomputable def node_h0_h0_h1_k1_k0 :
    CheckedChunk (upperAutoOracle lowTerms lowLogFuel)
      (follow lowKUpperHalfToOneRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .upper }, { axis := .k, branch := .upper }, { axis := .k, branch := .lower }]) :=
  joinAtPath lowKUpperHalfToOneRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .upper }, { axis := .k, branch := .upper }, { axis := .k, branch := .lower }]
    .chi
    (by
      simpa [L7UpperHalfToOneG01.chunk007Path] using L7UpperHalfToOneG01.chunk007)
    (by
      simpa [L7UpperHalfToOneG02.chunk008Path] using L7UpperHalfToOneG02.chunk008)

noncomputable def node_h0_h0_h1_k1_k1_h1 :
    CheckedChunk (upperAutoOracle lowTerms lowLogFuel)
      (follow lowKUpperHalfToOneRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .upper }, { axis := .k, branch := .upper }, { axis := .k, branch := .upper }, { axis := .chi, branch := .upper }]) :=
  joinAtPath lowKUpperHalfToOneRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .upper }, { axis := .k, branch := .upper }, { axis := .k, branch := .upper }, { axis := .chi, branch := .upper }]
    .k
    (by
      simpa [L7UpperHalfToOneG02.chunk010Path] using L7UpperHalfToOneG02.chunk010)
    (by
      simpa [L7UpperHalfToOneG02.chunk011Path] using L7UpperHalfToOneG02.chunk011)

noncomputable def node_h0_h0_h1_k1_k1 :
    CheckedChunk (upperAutoOracle lowTerms lowLogFuel)
      (follow lowKUpperHalfToOneRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .upper }, { axis := .k, branch := .upper }, { axis := .k, branch := .upper }]) :=
  joinAtPath lowKUpperHalfToOneRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .upper }, { axis := .k, branch := .upper }, { axis := .k, branch := .upper }]
    .chi
    (by
      simpa [L7UpperHalfToOneG02.chunk009Path] using L7UpperHalfToOneG02.chunk009)
    (by simpa using node_h0_h0_h1_k1_k1_h1)

noncomputable def node_h0_h0_h1_k1 :
    CheckedChunk (upperAutoOracle lowTerms lowLogFuel)
      (follow lowKUpperHalfToOneRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .upper }, { axis := .k, branch := .upper }]) :=
  joinAtPath lowKUpperHalfToOneRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .upper }, { axis := .k, branch := .upper }]
    .k
    (by simpa using node_h0_h0_h1_k1_k0)
    (by simpa using node_h0_h0_h1_k1_k1)

noncomputable def node_h0_h0_h1 :
    CheckedChunk (upperAutoOracle lowTerms lowLogFuel)
      (follow lowKUpperHalfToOneRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .upper }]) :=
  joinAtPath lowKUpperHalfToOneRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .upper }]
    .k
    (by simpa using node_h0_h0_h1_k0)
    (by simpa using node_h0_h0_h1_k1)

noncomputable def node_h0_h0 :
    CheckedChunk (upperAutoOracle lowTerms lowLogFuel)
      (follow lowKUpperHalfToOneRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }]) :=
  joinAtPath lowKUpperHalfToOneRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }]
    .chi
    (by simpa using node_h0_h0_h0)
    (by simpa using node_h0_h0_h1)

noncomputable def node_h0_h1_k0_k1 :
    CheckedChunk (upperAutoOracle lowTerms lowLogFuel)
      (follow lowKUpperHalfToOneRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .upper }, { axis := .k, branch := .lower }, { axis := .k, branch := .upper }]) :=
  joinAtPath lowKUpperHalfToOneRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .upper }, { axis := .k, branch := .lower }, { axis := .k, branch := .upper }]
    .chi
    (by
      simpa [L7UpperHalfToOneG03.chunk013Path] using L7UpperHalfToOneG03.chunk013)
    (by
      simpa [L7UpperHalfToOneG03.chunk014Path] using L7UpperHalfToOneG03.chunk014)

noncomputable def node_h0_h1_k0 :
    CheckedChunk (upperAutoOracle lowTerms lowLogFuel)
      (follow lowKUpperHalfToOneRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .upper }, { axis := .k, branch := .lower }]) :=
  joinAtPath lowKUpperHalfToOneRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .upper }, { axis := .k, branch := .lower }]
    .k
    (by
      simpa [L7UpperHalfToOneG03.chunk012Path] using L7UpperHalfToOneG03.chunk012)
    (by simpa using node_h0_h1_k0_k1)

noncomputable def node_h0_h1_k1_h0_k1 :
    CheckedChunk (upperAutoOracle lowTerms lowLogFuel)
      (follow lowKUpperHalfToOneRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .upper }, { axis := .k, branch := .upper }, { axis := .chi, branch := .lower }, { axis := .k, branch := .upper }]) :=
  joinAtPath lowKUpperHalfToOneRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .upper }, { axis := .k, branch := .upper }, { axis := .chi, branch := .lower }, { axis := .k, branch := .upper }]
    .chi
    (by
      simpa [L7UpperHalfToOneG04.chunk016Path] using L7UpperHalfToOneG04.chunk016)
    (by
      simpa [L7UpperHalfToOneG04.chunk017Path] using L7UpperHalfToOneG04.chunk017)

noncomputable def node_h0_h1_k1_h0 :
    CheckedChunk (upperAutoOracle lowTerms lowLogFuel)
      (follow lowKUpperHalfToOneRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .upper }, { axis := .k, branch := .upper }, { axis := .chi, branch := .lower }]) :=
  joinAtPath lowKUpperHalfToOneRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .upper }, { axis := .k, branch := .upper }, { axis := .chi, branch := .lower }]
    .k
    (by
      simpa [L7UpperHalfToOneG03.chunk015Path] using L7UpperHalfToOneG03.chunk015)
    (by simpa using node_h0_h1_k1_h0_k1)

noncomputable def node_h0_h1_k1 :
    CheckedChunk (upperAutoOracle lowTerms lowLogFuel)
      (follow lowKUpperHalfToOneRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .upper }, { axis := .k, branch := .upper }]) :=
  joinAtPath lowKUpperHalfToOneRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .upper }, { axis := .k, branch := .upper }]
    .chi
    (by simpa using node_h0_h1_k1_h0)
    (by
      simpa [L7UpperHalfToOneG04.chunk018Path] using L7UpperHalfToOneG04.chunk018)

noncomputable def node_h0_h1 :
    CheckedChunk (upperAutoOracle lowTerms lowLogFuel)
      (follow lowKUpperHalfToOneRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .upper }]) :=
  joinAtPath lowKUpperHalfToOneRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .upper }]
    .k
    (by simpa using node_h0_h1_k0)
    (by simpa using node_h0_h1_k1)

noncomputable def node_h0 :
    CheckedChunk (upperAutoOracle lowTerms lowLogFuel)
      (follow lowKUpperHalfToOneRoot [{ axis := .chi, branch := .lower }]) :=
  joinAtPath lowKUpperHalfToOneRoot [{ axis := .chi, branch := .lower }]
    .chi
    (by simpa using node_h0_h0)
    (by simpa using node_h0_h1)

noncomputable def node_h1 :
    CheckedChunk (upperAutoOracle lowTerms lowLogFuel)
      (follow lowKUpperHalfToOneRoot [{ axis := .chi, branch := .upper }]) :=
  joinAtPath lowKUpperHalfToOneRoot [{ axis := .chi, branch := .upper }]
    .k
    (by
      simpa [L7UpperHalfToOneG04.chunk019Path] using L7UpperHalfToOneG04.chunk019)
    (by
      simpa [L7UpperHalfToOneG05.chunk020Path] using L7UpperHalfToOneG05.chunk020)

noncomputable def node_root :
    CheckedChunk (upperAutoOracle lowTerms lowLogFuel)
      (follow lowKUpperHalfToOneRoot []) :=
  joinAtPath lowKUpperHalfToOneRoot []
    .chi
    (by simpa using node_h0)
    (by simpa using node_h1)

noncomputable def checkedTree :
    CheckedTree (upperAutoOracle lowTerms lowLogFuel) lowKUpperHalfToOneRoot :=
  CheckedChunk.toCheckedTree
    (by
      simpa [follow] using node_root)

end L7UpperHalfToOneAssembly

namespace L14LowerAssembly

noncomputable def node_h0_h0_h0_h0_h0_h0 :
    CheckedChunk (restrictedAutoOracle restrictedTerms restrictedLogFuel)
      (follow restrictedLowerRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }]) :=
  joinAtPath restrictedLowerRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }]
    .k
    (by
      simpa [L14LowerG00.chunk000Path] using L14LowerG00.chunk000)
    (by
      simpa [L14LowerG00.chunk001Path] using L14LowerG00.chunk001)

noncomputable def node_h0_h0_h0_h0_h0 :
    CheckedChunk (restrictedAutoOracle restrictedTerms restrictedLogFuel)
      (follow restrictedLowerRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }]) :=
  joinAtPath restrictedLowerRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }]
    .chi
    (by simpa using node_h0_h0_h0_h0_h0_h0)
    (by
      simpa [L14LowerG00.chunk002Path] using L14LowerG00.chunk002)

noncomputable def node_h0_h0_h0_h0 :
    CheckedChunk (restrictedAutoOracle restrictedTerms restrictedLogFuel)
      (follow restrictedLowerRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }]) :=
  joinAtPath restrictedLowerRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }]
    .chi
    (by simpa using node_h0_h0_h0_h0_h0)
    (by
      simpa [L14LowerG00.chunk003Path] using L14LowerG00.chunk003)

noncomputable def node_h0_h0_h0_h1 :
    CheckedChunk (restrictedAutoOracle restrictedTerms restrictedLogFuel)
      (follow restrictedLowerRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .upper }]) :=
  joinAtPath restrictedLowerRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .upper }]
    .k
    (by
      simpa [L14LowerG01.chunk004Path] using L14LowerG01.chunk004)
    (by
      simpa [L14LowerG01.chunk005Path] using L14LowerG01.chunk005)

noncomputable def node_h0_h0_h0 :
    CheckedChunk (restrictedAutoOracle restrictedTerms restrictedLogFuel)
      (follow restrictedLowerRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }]) :=
  joinAtPath restrictedLowerRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }]
    .chi
    (by simpa using node_h0_h0_h0_h0)
    (by simpa using node_h0_h0_h0_h1)

noncomputable def node_h0_h0_h1_k0_k0 :
    CheckedChunk (restrictedAutoOracle restrictedTerms restrictedLogFuel)
      (follow restrictedLowerRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .upper }, { axis := .k, branch := .lower }, { axis := .k, branch := .lower }]) :=
  joinAtPath restrictedLowerRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .upper }, { axis := .k, branch := .lower }, { axis := .k, branch := .lower }]
    .chi
    (by
      simpa [L14LowerG01.chunk006Path] using L14LowerG01.chunk006)
    (by
      simpa [L14LowerG01.chunk007Path] using L14LowerG01.chunk007)

noncomputable def node_h0_h0_h1_k0 :
    CheckedChunk (restrictedAutoOracle restrictedTerms restrictedLogFuel)
      (follow restrictedLowerRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .upper }, { axis := .k, branch := .lower }]) :=
  joinAtPath restrictedLowerRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .upper }, { axis := .k, branch := .lower }]
    .k
    (by simpa using node_h0_h0_h1_k0_k0)
    (by
      simpa [L14LowerG02.chunk008Path] using L14LowerG02.chunk008)

noncomputable def node_h0_h0_h1_k1 :
    CheckedChunk (restrictedAutoOracle restrictedTerms restrictedLogFuel)
      (follow restrictedLowerRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .upper }, { axis := .k, branch := .upper }]) :=
  joinAtPath restrictedLowerRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .upper }, { axis := .k, branch := .upper }]
    .k
    (by
      simpa [L14LowerG02.chunk009Path] using L14LowerG02.chunk009)
    (by
      simpa [L14LowerG02.chunk010Path] using L14LowerG02.chunk010)

noncomputable def node_h0_h0_h1 :
    CheckedChunk (restrictedAutoOracle restrictedTerms restrictedLogFuel)
      (follow restrictedLowerRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .upper }]) :=
  joinAtPath restrictedLowerRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .upper }]
    .k
    (by simpa using node_h0_h0_h1_k0)
    (by simpa using node_h0_h0_h1_k1)

noncomputable def node_h0_h0 :
    CheckedChunk (restrictedAutoOracle restrictedTerms restrictedLogFuel)
      (follow restrictedLowerRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }]) :=
  joinAtPath restrictedLowerRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }]
    .chi
    (by simpa using node_h0_h0_h0)
    (by simpa using node_h0_h0_h1)

noncomputable def node_h0_h1_k0_h0 :
    CheckedChunk (restrictedAutoOracle restrictedTerms restrictedLogFuel)
      (follow restrictedLowerRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .upper }, { axis := .k, branch := .lower }, { axis := .chi, branch := .lower }]) :=
  joinAtPath restrictedLowerRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .upper }, { axis := .k, branch := .lower }, { axis := .chi, branch := .lower }]
    .k
    (by
      simpa [L14LowerG02.chunk011Path] using L14LowerG02.chunk011)
    (by
      simpa [L14LowerG03.chunk012Path] using L14LowerG03.chunk012)

noncomputable def node_h0_h1_k0 :
    CheckedChunk (restrictedAutoOracle restrictedTerms restrictedLogFuel)
      (follow restrictedLowerRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .upper }, { axis := .k, branch := .lower }]) :=
  joinAtPath restrictedLowerRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .upper }, { axis := .k, branch := .lower }]
    .chi
    (by simpa using node_h0_h1_k0_h0)
    (by
      simpa [L14LowerG03.chunk013Path] using L14LowerG03.chunk013)

noncomputable def node_h0_h1_k1 :
    CheckedChunk (restrictedAutoOracle restrictedTerms restrictedLogFuel)
      (follow restrictedLowerRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .upper }, { axis := .k, branch := .upper }]) :=
  joinAtPath restrictedLowerRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .upper }, { axis := .k, branch := .upper }]
    .chi
    (by
      simpa [L14LowerG03.chunk014Path] using L14LowerG03.chunk014)
    (by
      simpa [L14LowerG03.chunk015Path] using L14LowerG03.chunk015)

noncomputable def node_h0_h1 :
    CheckedChunk (restrictedAutoOracle restrictedTerms restrictedLogFuel)
      (follow restrictedLowerRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .upper }]) :=
  joinAtPath restrictedLowerRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .upper }]
    .k
    (by simpa using node_h0_h1_k0)
    (by simpa using node_h0_h1_k1)

noncomputable def node_h0 :
    CheckedChunk (restrictedAutoOracle restrictedTerms restrictedLogFuel)
      (follow restrictedLowerRoot [{ axis := .chi, branch := .lower }]) :=
  joinAtPath restrictedLowerRoot [{ axis := .chi, branch := .lower }]
    .chi
    (by simpa using node_h0_h0)
    (by simpa using node_h0_h1)

noncomputable def node_h1 :
    CheckedChunk (restrictedAutoOracle restrictedTerms restrictedLogFuel)
      (follow restrictedLowerRoot [{ axis := .chi, branch := .upper }]) :=
  joinAtPath restrictedLowerRoot [{ axis := .chi, branch := .upper }]
    .k
    (by
      simpa [L14LowerG04.chunk016Path] using L14LowerG04.chunk016)
    (by
      simpa [L14LowerG04.chunk017Path] using L14LowerG04.chunk017)

noncomputable def node_root :
    CheckedChunk (restrictedAutoOracle restrictedTerms restrictedLogFuel)
      (follow restrictedLowerRoot []) :=
  joinAtPath restrictedLowerRoot []
    .chi
    (by simpa using node_h0)
    (by simpa using node_h1)

noncomputable def checkedTree :
    CheckedTree (restrictedAutoOracle restrictedTerms restrictedLogFuel) restrictedLowerRoot :=
  CheckedChunk.toCheckedTree
    (by
      simpa [follow] using node_root)

end L14LowerAssembly

namespace L14UpperAssembly

noncomputable def node_h0_h0_h0_h0_h0_h0 :
    CheckedChunk (restrictedAutoOracle restrictedTerms restrictedLogFuel)
      (follow restrictedUpperRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }]) :=
  joinAtPath restrictedUpperRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }]
    .k
    (by
      simpa [L14UpperG00.chunk000Path] using L14UpperG00.chunk000)
    (by
      simpa [L14UpperG00.chunk001Path] using L14UpperG00.chunk001)

noncomputable def node_h0_h0_h0_h0_h0 :
    CheckedChunk (restrictedAutoOracle restrictedTerms restrictedLogFuel)
      (follow restrictedUpperRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }]) :=
  joinAtPath restrictedUpperRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }]
    .chi
    (by simpa using node_h0_h0_h0_h0_h0_h0)
    (by
      simpa [L14UpperG00.chunk002Path] using L14UpperG00.chunk002)

noncomputable def node_h0_h0_h0_h0 :
    CheckedChunk (restrictedAutoOracle restrictedTerms restrictedLogFuel)
      (follow restrictedUpperRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }]) :=
  joinAtPath restrictedUpperRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }]
    .chi
    (by simpa using node_h0_h0_h0_h0_h0)
    (by
      simpa [L14UpperG00.chunk003Path] using L14UpperG00.chunk003)

noncomputable def node_h0_h0_h0_h1 :
    CheckedChunk (restrictedAutoOracle restrictedTerms restrictedLogFuel)
      (follow restrictedUpperRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .upper }]) :=
  joinAtPath restrictedUpperRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .upper }]
    .k
    (by
      simpa [L14UpperG01.chunk004Path] using L14UpperG01.chunk004)
    (by
      simpa [L14UpperG01.chunk005Path] using L14UpperG01.chunk005)

noncomputable def node_h0_h0_h0 :
    CheckedChunk (restrictedAutoOracle restrictedTerms restrictedLogFuel)
      (follow restrictedUpperRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }]) :=
  joinAtPath restrictedUpperRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }]
    .chi
    (by simpa using node_h0_h0_h0_h0)
    (by simpa using node_h0_h0_h0_h1)

noncomputable def node_h0_h0_h1_k0 :
    CheckedChunk (restrictedAutoOracle restrictedTerms restrictedLogFuel)
      (follow restrictedUpperRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .upper }, { axis := .k, branch := .lower }]) :=
  joinAtPath restrictedUpperRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .upper }, { axis := .k, branch := .lower }]
    .k
    (by
      simpa [L14UpperG01.chunk006Path] using L14UpperG01.chunk006)
    (by
      simpa [L14UpperG01.chunk007Path] using L14UpperG01.chunk007)

noncomputable def node_h0_h0_h1 :
    CheckedChunk (restrictedAutoOracle restrictedTerms restrictedLogFuel)
      (follow restrictedUpperRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .upper }]) :=
  joinAtPath restrictedUpperRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }, { axis := .chi, branch := .upper }]
    .k
    (by simpa using node_h0_h0_h1_k0)
    (by
      simpa [L14UpperG02.chunk008Path] using L14UpperG02.chunk008)

noncomputable def node_h0_h0 :
    CheckedChunk (restrictedAutoOracle restrictedTerms restrictedLogFuel)
      (follow restrictedUpperRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }]) :=
  joinAtPath restrictedUpperRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .lower }]
    .chi
    (by simpa using node_h0_h0_h0)
    (by simpa using node_h0_h0_h1)

noncomputable def node_h0_h1_k0 :
    CheckedChunk (restrictedAutoOracle restrictedTerms restrictedLogFuel)
      (follow restrictedUpperRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .upper }, { axis := .k, branch := .lower }]) :=
  joinAtPath restrictedUpperRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .upper }, { axis := .k, branch := .lower }]
    .chi
    (by
      simpa [L14UpperG02.chunk009Path] using L14UpperG02.chunk009)
    (by
      simpa [L14UpperG02.chunk010Path] using L14UpperG02.chunk010)

noncomputable def node_h0_h1 :
    CheckedChunk (restrictedAutoOracle restrictedTerms restrictedLogFuel)
      (follow restrictedUpperRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .upper }]) :=
  joinAtPath restrictedUpperRoot [{ axis := .chi, branch := .lower }, { axis := .chi, branch := .upper }]
    .k
    (by simpa using node_h0_h1_k0)
    (by
      simpa [L14UpperG02.chunk011Path] using L14UpperG02.chunk011)

noncomputable def node_h0 :
    CheckedChunk (restrictedAutoOracle restrictedTerms restrictedLogFuel)
      (follow restrictedUpperRoot [{ axis := .chi, branch := .lower }]) :=
  joinAtPath restrictedUpperRoot [{ axis := .chi, branch := .lower }]
    .chi
    (by simpa using node_h0_h0)
    (by simpa using node_h0_h1)

noncomputable def node_h1_k0 :
    CheckedChunk (restrictedAutoOracle restrictedTerms restrictedLogFuel)
      (follow restrictedUpperRoot [{ axis := .chi, branch := .upper }, { axis := .k, branch := .lower }]) :=
  joinAtPath restrictedUpperRoot [{ axis := .chi, branch := .upper }, { axis := .k, branch := .lower }]
    .chi
    (by
      simpa [L14UpperG03.chunk012Path] using L14UpperG03.chunk012)
    (by
      simpa [L14UpperG03.chunk013Path] using L14UpperG03.chunk013)

noncomputable def node_h1 :
    CheckedChunk (restrictedAutoOracle restrictedTerms restrictedLogFuel)
      (follow restrictedUpperRoot [{ axis := .chi, branch := .upper }]) :=
  joinAtPath restrictedUpperRoot [{ axis := .chi, branch := .upper }]
    .k
    (by simpa using node_h1_k0)
    (by
      simpa [L14UpperG03.chunk014Path] using L14UpperG03.chunk014)

noncomputable def node_root :
    CheckedChunk (restrictedAutoOracle restrictedTerms restrictedLogFuel)
      (follow restrictedUpperRoot []) :=
  joinAtPath restrictedUpperRoot []
    .chi
    (by simpa using node_h0)
    (by simpa using node_h1)

noncomputable def checkedTree :
    CheckedTree (restrictedAutoOracle restrictedTerms restrictedLogFuel) restrictedUpperRoot :=
  CheckedChunk.toCheckedTree
    (by
      simpa [follow] using node_root)

end L14UpperAssembly

noncomputable def lowKCheckedForest :
    LowKHistoricalCheckedForest
      (middleAutoOracle lowTerms lowLogFuel)
      (upperAutoOracle lowTerms lowLogFuel) where
  middle := L7MiddleAssembly.checkedTree
  upperFiveThirtySecondsToQuarter :=
    L7UpperFiveThirtySecondsToQuarterAssembly.checkedTree
  upperQuarterToHalf := L7UpperQuarterToHalfAssembly.checkedTree
  upperHalfToOne := L7UpperHalfToOneAssembly.checkedTree

noncomputable def restrictedCheckedForest :
    RestrictedHistoricalCheckedForest
      (restrictedAutoOracle restrictedTerms restrictedLogFuel) where
  lower := L14LowerAssembly.checkedTree
  upper := L14UpperAssembly.checkedTree

end LRIdealFinalRefinedReplayGenerated

theorem lrLowKIdealReplayCertificate_finalRefined_proved :
    LRLowKIdealReplayCertificate :=
  LRIdealHistoricalReplayAssembly.lowKIdealReplayCertificate_of_historicalCheckedForest
      (LRIdealCenteredMeanOracle.middleAutoOracle
        LRIdealFinalRefinedReplayGenerated.lowTerms
        LRIdealFinalRefinedReplayGenerated.lowLogFuel)
      (LRIdealCenteredMeanOracle.upperAutoOracle
        LRIdealFinalRefinedReplayGenerated.lowTerms
        LRIdealFinalRefinedReplayGenerated.lowLogFuel)
      LRIdealFinalRefinedReplayGenerated.lowKCheckedForest

theorem lrDeterminantIdealOneToFour_finalRefined_proved :
    LRDeterminantIdealOneToFourTheorem :=
  LRIdealHistoricalReplayAssembly.RestrictedHistoricalCheckedForest.toIdealTheorem
      LRIdealFinalRefinedReplayGenerated.restrictedCheckedForest

end CourtadeKumar
