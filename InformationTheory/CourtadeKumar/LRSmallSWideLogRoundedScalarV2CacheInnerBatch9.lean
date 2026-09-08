import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch3
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch4
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch5
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch6

namespace CourtadeKumar
namespace LRSmallSWideLogRoundedScalarV2

open LRSmallSBridgeCoreCertificate
open LRSmallSWideLog
open LRSmallSWideLogRounded
open LRSmallSWideLogRoundedValue
open LRSmallSWideLogSharedSliceCore
open LRSmallSWideLogFactoredValidity
open LRSmallSWideLogFactoredRounded
open LRUpperKDyadicOuterRounding

noncomputable def innerPair576Data : WideLogData :=
  { lower := endpoint299
    upper := endpoint305 }

noncomputable def innerPair576Input : RationalEnclosure :=
  { lower := (14401507/16777216), upper := (14731563/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair576Input_eq :
    innerPair576Input = outerEnclosure 24 innerPair576Data.output := by
  rfl'

theorem innerPair576RoundedFacts :
    InnerPairRoundedFacts innerPair576Data innerPair576Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair576Input_eq }

noncomputable def innerPair577Data : WideLogData :=
  { lower := endpoint299
    upper := endpoint308 }

noncomputable def innerPair577Input : RationalEnclosure :=
  { lower := (14401507/16777216), upper := (7420077/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair577Input_eq :
    innerPair577Input = outerEnclosure 24 innerPair577Data.output := by
  rfl'

theorem innerPair577RoundedFacts :
    InnerPairRoundedFacts innerPair577Data innerPair577Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair577Input_eq }

noncomputable def innerPair578Data : WideLogData :=
  { lower := endpoint299
    upper := endpoint403 }

noncomputable def innerPair578Input : RationalEnclosure :=
  { lower := (14401507/16777216), upper := (15055249/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair578Input_eq :
    innerPair578Input = outerEnclosure 24 innerPair578Data.output := by
  rfl'

theorem innerPair578RoundedFacts :
    InnerPairRoundedFacts innerPair578Data innerPair578Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair578Input_eq }

noncomputable def innerPair579Data : WideLogData :=
  { lower := endpoint300
    upper := endpoint301 }

noncomputable def innerPair579Input : RationalEnclosure :=
  { lower := (13886763/16777216), upper := (14269047/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair579Input_eq :
    innerPair579Input = outerEnclosure 24 innerPair579Data.output := by
  rfl'

theorem innerPair579RoundedFacts :
    InnerPairRoundedFacts innerPair579Data innerPair579Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair579Input_eq }

noncomputable def innerPair580Data : WideLogData :=
  { lower := endpoint302
    upper := endpoint303 }

noncomputable def innerPair580Input : RationalEnclosure :=
  { lower := (7018233/8388608), upper := (7214631/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair580Input_eq :
    innerPair580Input = outerEnclosure 24 innerPair580Data.output := by
  rfl'

theorem innerPair580RoundedFacts :
    InnerPairRoundedFacts innerPair580Data innerPair580Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair580Input_eq }

noncomputable def innerPair581Data : WideLogData :=
  { lower := endpoint302
    upper := endpoint306 }

noncomputable def innerPair581Input : RationalEnclosure :=
  { lower := (7018233/8388608), upper := (7131023/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair581Input_eq :
    innerPair581Input = outerEnclosure 24 innerPair581Data.output := by
  rfl'

theorem innerPair581RoundedFacts :
    InnerPairRoundedFacts innerPair581Data innerPair581Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair581Input_eq }

noncomputable def innerPair582Data : WideLogData :=
  { lower := endpoint303
    upper := endpoint402 }

noncomputable def innerPair582Input : RationalEnclosure :=
  { lower := (14429261/16777216), upper := (1831207/2097152) }

set_option maxRecDepth 1000000 in
private theorem innerPair582Input_eq :
    innerPair582Input = outerEnclosure 24 innerPair582Data.output := by
  rfl'

theorem innerPair582RoundedFacts :
    InnerPairRoundedFacts innerPair582Data innerPair582Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair582Input_eq }

noncomputable def innerPair583Data : WideLogData :=
  { lower := endpoint303
    upper := endpoint423 }

noncomputable def innerPair583Input : RationalEnclosure :=
  { lower := (14429261/16777216), upper := (1844847/2097152) }

set_option maxRecDepth 1000000 in
private theorem innerPair583Input_eq :
    innerPair583Input = outerEnclosure 24 innerPair583Data.output := by
  rfl'

theorem innerPair583RoundedFacts :
    InnerPairRoundedFacts innerPair583Data innerPair583Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair583Input_eq }

noncomputable def innerPair584Data : WideLogData :=
  { lower := endpoint304
    upper := endpoint94 }

noncomputable def innerPair584Input : RationalEnclosure :=
  { lower := (14622263/16777216), upper := (15161771/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair584Input_eq :
    innerPair584Input = outerEnclosure 24 innerPair584Data.output := by
  rfl'

theorem innerPair584RoundedFacts :
    InnerPairRoundedFacts innerPair584Data innerPair584Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair584Input_eq }

noncomputable def innerPair585Data : WideLogData :=
  { lower := endpoint304
    upper := endpoint308 }

noncomputable def innerPair585Input : RationalEnclosure :=
  { lower := (14622263/16777216), upper := (7420077/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair585Input_eq :
    innerPair585Input = outerEnclosure 24 innerPair585Data.output := by
  rfl'

theorem innerPair585RoundedFacts :
    InnerPairRoundedFacts innerPair585Data innerPair585Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair585Input_eq }

noncomputable def innerPair586Data : WideLogData :=
  { lower := endpoint304
    upper := endpoint403 }

noncomputable def innerPair586Input : RationalEnclosure :=
  { lower := (14622263/16777216), upper := (15055249/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair586Input_eq :
    innerPair586Input = outerEnclosure 24 innerPair586Data.output := by
  rfl'

theorem innerPair586RoundedFacts :
    InnerPairRoundedFacts innerPair586Data innerPair586Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair586Input_eq }

noncomputable def innerPair587Data : WideLogData :=
  { lower := endpoint304
    upper := endpoint419 }

noncomputable def innerPair587Input : RationalEnclosure :=
  { lower := (14622263/16777216), upper := (3869335/4194304) }

set_option maxRecDepth 1000000 in
private theorem innerPair587Input_eq :
    innerPair587Input = outerEnclosure 24 innerPair587Data.output := by
  rfl'

theorem innerPair587RoundedFacts :
    InnerPairRoundedFacts innerPair587Data innerPair587Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair587Input_eq }

noncomputable def innerPair588Data : WideLogData :=
  { lower := endpoint304
    upper := endpoint424 }

noncomputable def innerPair588Input : RationalEnclosure :=
  { lower := (14622263/16777216), upper := (7460569/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair588Input_eq :
    innerPair588Input = outerEnclosure 24 innerPair588Data.output := by
  rfl'

theorem innerPair588RoundedFacts :
    InnerPairRoundedFacts innerPair588Data innerPair588Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair588Input_eq }

noncomputable def innerPair589Data : WideLogData :=
  { lower := endpoint305
    upper := endpoint94 }

noncomputable def innerPair589Input : RationalEnclosure :=
  { lower := (14731561/16777216), upper := (15161771/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair589Input_eq :
    innerPair589Input = outerEnclosure 24 innerPair589Data.output := by
  rfl'

theorem innerPair589RoundedFacts :
    InnerPairRoundedFacts innerPair589Data innerPair589Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair589Input_eq }

noncomputable def innerPair590Data : WideLogData :=
  { lower := endpoint305
    upper := endpoint403 }

noncomputable def innerPair590Input : RationalEnclosure :=
  { lower := (14731561/16777216), upper := (15055249/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair590Input_eq :
    innerPair590Input = outerEnclosure 24 innerPair590Data.output := by
  rfl'

theorem innerPair590RoundedFacts :
    InnerPairRoundedFacts innerPair590Data innerPair590Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair590Input_eq }

noncomputable def innerPair591Data : WideLogData :=
  { lower := endpoint306
    upper := endpoint307 }

noncomputable def innerPair591Input : RationalEnclosure :=
  { lower := (14262045/16777216), upper := (7317983/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair591Input_eq :
    innerPair591Input = outerEnclosure 24 innerPair591Data.output := by
  rfl'

theorem innerPair591RoundedFacts :
    InnerPairRoundedFacts innerPair591Data innerPair591Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair591Input_eq }

noncomputable def innerPair592Data : WideLogData :=
  { lower := endpoint308
    upper := endpoint94 }

noncomputable def innerPair592Input : RationalEnclosure :=
  { lower := (1855019/2097152), upper := (15161771/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair592Input_eq :
    innerPair592Input = outerEnclosure 24 innerPair592Data.output := by
  rfl'

theorem innerPair592RoundedFacts :
    InnerPairRoundedFacts innerPair592Data innerPair592Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair592Input_eq }

noncomputable def innerPair593Data : WideLogData :=
  { lower := endpoint308
    upper := endpoint403 }

noncomputable def innerPair593Input : RationalEnclosure :=
  { lower := (1855019/2097152), upper := (15055249/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair593Input_eq :
    innerPair593Input = outerEnclosure 24 innerPair593Data.output := by
  rfl'

theorem innerPair593RoundedFacts :
    InnerPairRoundedFacts innerPair593Data innerPair593Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair593Input_eq }

noncomputable def innerPair594Data : WideLogData :=
  { lower := endpoint308
    upper := endpoint414 }

noncomputable def innerPair594Input : RationalEnclosure :=
  { lower := (1855019/2097152), upper := (7633811/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair594Input_eq :
    innerPair594Input = outerEnclosure 24 innerPair594Data.output := by
  rfl'

theorem innerPair594RoundedFacts :
    InnerPairRoundedFacts innerPair594Data innerPair594Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair594Input_eq }

noncomputable def innerPair595Data : WideLogData :=
  { lower := endpoint309
    upper := endpoint310 }

noncomputable def innerPair595Input : RationalEnclosure :=
  { lower := (14629115/16777216), upper := (938027/1048576) }

set_option maxRecDepth 1000000 in
private theorem innerPair595Input_eq :
    innerPair595Input = outerEnclosure 24 innerPair595Data.output := by
  rfl'

theorem innerPair595RoundedFacts :
    InnerPairRoundedFacts innerPair595Data innerPair595Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair595Input_eq }

noncomputable def innerPair596Data : WideLogData :=
  { lower := endpoint311
    upper := endpoint312 }

noncomputable def innerPair596Input : RationalEnclosure :=
  { lower := (5527045/8388608), upper := (11348215/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair596Input_eq :
    innerPair596Input = outerEnclosure 24 innerPair596Data.output := by
  rfl'

theorem innerPair596RoundedFacts :
    InnerPairRoundedFacts innerPair596Data innerPair596Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair596Input_eq }

noncomputable def innerPair597Data : WideLogData :=
  { lower := endpoint313
    upper := endpoint253 }

noncomputable def innerPair597Input : RationalEnclosure :=
  { lower := (10184159/16777216), upper := (10388275/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair597Input_eq :
    innerPair597Input = outerEnclosure 24 innerPair597Data.output := by
  rfl'

theorem innerPair597RoundedFacts :
    InnerPairRoundedFacts innerPair597Data innerPair597Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair597Input_eq }

noncomputable def innerPair598Data : WideLogData :=
  { lower := endpoint314
    upper := endpoint259 }

noncomputable def innerPair598Input : RationalEnclosure :=
  { lower := (327931/524288), upper := (5347099/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair598Input_eq :
    innerPair598Input = outerEnclosure 24 innerPair598Data.output := by
  rfl'

theorem innerPair598RoundedFacts :
    InnerPairRoundedFacts innerPair598Data innerPair598Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair598Input_eq }

noncomputable def innerPair599Data : WideLogData :=
  { lower := endpoint315
    upper := endpoint316 }

noncomputable def innerPair599Input : RationalEnclosure :=
  { lower := (10808571/16777216), upper := (5500511/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair599Input_eq :
    innerPair599Input = outerEnclosure 24 innerPair599Data.output := by
  rfl'

theorem innerPair599RoundedFacts :
    InnerPairRoundedFacts innerPair599Data innerPair599Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair599Input_eq }

noncomputable def innerPair600Data : WideLogData :=
  { lower := endpoint317
    upper := endpoint318 }

noncomputable def innerPair600Input : RationalEnclosure :=
  { lower := (5518563/8388608), upper := (5619785/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair600Input_eq :
    innerPair600Input = outerEnclosure 24 innerPair600Data.output := by
  rfl'

theorem innerPair600RoundedFacts :
    InnerPairRoundedFacts innerPair600Data innerPair600Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair600Input_eq }

noncomputable def innerPair601Data : WideLogData :=
  { lower := endpoint319
    upper := endpoint278 }

noncomputable def innerPair601Input : RationalEnclosure :=
  { lower := (11331545/16777216), upper := (1445427/2097152) }

set_option maxRecDepth 1000000 in
private theorem innerPair601Input_eq :
    innerPair601Input = outerEnclosure 24 innerPair601Data.output := by
  rfl'

theorem innerPair601RoundedFacts :
    InnerPairRoundedFacts innerPair601Data innerPair601Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair601Input_eq }

noncomputable def innerPair602Data : WideLogData :=
  { lower := endpoint321
    upper := endpoint288 }

noncomputable def innerPair602Input : RationalEnclosure :=
  { lower := (11727097/16777216), upper := (12049747/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair602Input_eq :
    innerPair602Input = outerEnclosure 24 innerPair602Data.output := by
  rfl'

theorem innerPair602RoundedFacts :
    InnerPairRoundedFacts innerPair602Data innerPair602Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair602Input_eq }

noncomputable def innerPair603Data : WideLogData :=
  { lower := endpoint323
    upper := endpoint84 }

noncomputable def innerPair603Input : RationalEnclosure :=
  { lower := (5928451/8388608), upper := (12081673/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair603Input_eq :
    innerPair603Input = outerEnclosure 24 innerPair603Data.output := by
  rfl'

theorem innerPair603RoundedFacts :
    InnerPairRoundedFacts innerPair603Data innerPair603Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair603Input_eq }

noncomputable def innerPair604Data : WideLogData :=
  { lower := endpoint325
    upper := endpoint326 }

noncomputable def innerPair604Input : RationalEnclosure :=
  { lower := (5992855/8388608), upper := (190267/262144) }

set_option maxRecDepth 1000000 in
private theorem innerPair604Input_eq :
    innerPair604Input = outerEnclosure 24 innerPair604Data.output := by
  rfl'

theorem innerPair604RoundedFacts :
    InnerPairRoundedFacts innerPair604Data innerPair604Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair604Input_eq }

noncomputable def innerPair605Data : WideLogData :=
  { lower := endpoint330
    upper := endpoint331 }

noncomputable def innerPair605Input : RationalEnclosure :=
  { lower := (11921429/16777216), upper := (12216685/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair605Input_eq :
    innerPair605Input = outerEnclosure 24 innerPair605Data.output := by
  rfl'

theorem innerPair605RoundedFacts :
    InnerPairRoundedFacts innerPair605Data innerPair605Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair605Input_eq }

noncomputable def innerPair606Data : WideLogData :=
  { lower := endpoint331
    upper := endpoint359 }

noncomputable def innerPair606Input : RationalEnclosure :=
  { lower := (3054171/4194304), upper := (1550927/2097152) }

set_option maxRecDepth 1000000 in
private theorem innerPair606Input_eq :
    innerPair606Input = outerEnclosure 24 innerPair606Data.output := by
  rfl'

theorem innerPair606RoundedFacts :
    InnerPairRoundedFacts innerPair606Data innerPair606Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair606Input_eq }

noncomputable def innerPair607Data : WideLogData :=
  { lower := endpoint332
    upper := endpoint333 }

noncomputable def innerPair607Input : RationalEnclosure :=
  { lower := (12113537/16777216), upper := (12428909/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair607Input_eq :
    innerPair607Input = outerEnclosure 24 innerPair607Data.output := by
  rfl'

theorem innerPair607RoundedFacts :
    InnerPairRoundedFacts innerPair607Data innerPair607Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair607Input_eq }

noncomputable def innerPair608Data : WideLogData :=
  { lower := endpoint332
    upper := endpoint355 }

noncomputable def innerPair608Input : RationalEnclosure :=
  { lower := (12113537/16777216), upper := (12334919/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair608Input_eq :
    innerPair608Input = outerEnclosure 24 innerPair608Data.output := by
  rfl'

theorem innerPair608RoundedFacts :
    InnerPairRoundedFacts innerPair608Data innerPair608Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair608Input_eq }

noncomputable def innerPair609Data : WideLogData :=
  { lower := endpoint335
    upper := endpoint336 }

noncomputable def innerPair609Input : RationalEnclosure :=
  { lower := (3122819/4194304), upper := (12799691/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair609Input_eq :
    innerPair609Input = outerEnclosure 24 innerPair609Data.output := by
  rfl'

theorem innerPair609RoundedFacts :
    InnerPairRoundedFacts innerPair609Data innerPair609Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair609Input_eq }

noncomputable def innerPair610Data : WideLogData :=
  { lower := endpoint335
    upper := endpoint360 }

noncomputable def innerPair610Input : RationalEnclosure :=
  { lower := (3122819/4194304), upper := (12707761/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair610Input_eq :
    innerPair610Input = outerEnclosure 24 innerPair610Data.output := by
  rfl'

theorem innerPair610RoundedFacts :
    InnerPairRoundedFacts innerPair610Data innerPair610Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair610Input_eq }

noncomputable def innerPair611Data : WideLogData :=
  { lower := endpoint337
    upper := endpoint80 }

noncomputable def innerPair611Input : RationalEnclosure :=
  { lower := (13012255/16777216), upper := (6685251/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair611Input_eq :
    innerPair611Input = outerEnclosure 24 innerPair611Data.output := by
  rfl'

theorem innerPair611RoundedFacts :
    InnerPairRoundedFacts innerPair611Data innerPair611Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair611Input_eq }

noncomputable def innerPair612Data : WideLogData :=
  { lower := endpoint337
    upper := endpoint291 }

noncomputable def innerPair612Input : RationalEnclosure :=
  { lower := (13012255/16777216), upper := (13251935/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair612Input_eq :
    innerPair612Input = outerEnclosure 24 innerPair612Data.output := by
  rfl'

theorem innerPair612RoundedFacts :
    InnerPairRoundedFacts innerPair612Data innerPair612Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair612Input_eq }

noncomputable def innerPair613Data : WideLogData :=
  { lower := endpoint337
    upper := endpoint298 }

noncomputable def innerPair613Input : RationalEnclosure :=
  { lower := (13012255/16777216), upper := (6975543/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair613Input_eq :
    innerPair613Input = outerEnclosure 24 innerPair613Data.output := by
  rfl'

theorem innerPair613RoundedFacts :
    InnerPairRoundedFacts innerPair613Data innerPair613Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair613Input_eq }

noncomputable def innerPair614Data : WideLogData :=
  { lower := endpoint338
    upper := endpoint339 }

noncomputable def innerPair614Input : RationalEnclosure :=
  { lower := (12576657/16777216), upper := (12875917/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair614Input_eq :
    innerPair614Input = outerEnclosure 24 innerPair614Data.output := by
  rfl'

theorem innerPair614RoundedFacts :
    InnerPairRoundedFacts innerPair614Data innerPair614Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair614Input_eq }

noncomputable def innerPair615Data : WideLogData :=
  { lower := endpoint341
    upper := endpoint342 }

noncomputable def innerPair615Input : RationalEnclosure :=
  { lower := (6430349/8388608), upper := (1645307/2097152) }

set_option maxRecDepth 1000000 in
private theorem innerPair615Input_eq :
    innerPair615Input = outerEnclosure 24 innerPair615Data.output := by
  rfl'

theorem innerPair615RoundedFacts :
    InnerPairRoundedFacts innerPair615Data innerPair615Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair615Input_eq }

noncomputable def innerPair616Data : WideLogData :=
  { lower := endpoint341
    upper := endpoint379 }

noncomputable def innerPair616Input : RationalEnclosure :=
  { lower := (6430349/8388608), upper := (13429473/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair616Input_eq :
    innerPair616Input = outerEnclosure 24 innerPair616Data.output := by
  rfl'

theorem innerPair616RoundedFacts :
    InnerPairRoundedFacts innerPair616Data innerPair616Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair616Input_eq }

noncomputable def innerPair617Data : WideLogData :=
  { lower := endpoint343
    upper := endpoint344 }

noncomputable def innerPair617Input : RationalEnclosure :=
  { lower := (12953689/16777216), upper := (1655097/2097152) }

set_option maxRecDepth 1000000 in
private theorem innerPair617Input_eq :
    innerPair617Input = outerEnclosure 24 innerPair617Data.output := by
  rfl'

theorem innerPair617RoundedFacts :
    InnerPairRoundedFacts innerPair617Data innerPair617Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair617Input_eq }

noncomputable def innerPair618Data : WideLogData :=
  { lower := endpoint345
    upper := endpoint342 }

noncomputable def innerPair618Input : RationalEnclosure :=
  { lower := (3237949/4194304), upper := (1645307/2097152) }

set_option maxRecDepth 1000000 in
private theorem innerPair618Input_eq :
    innerPair618Input = outerEnclosure 24 innerPair618Data.output := by
  rfl'

theorem innerPair618RoundedFacts :
    InnerPairRoundedFacts innerPair618Data innerPair618Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair618Input_eq }

noncomputable def innerPair619Data : WideLogData :=
  { lower := endpoint345
    upper := endpoint346 }

noncomputable def innerPair619Input : RationalEnclosure :=
  { lower := (3237949/4194304), upper := (13281655/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair619Input_eq :
    innerPair619Input = outerEnclosure 24 innerPair619Data.output := by
  rfl'

theorem innerPair619RoundedFacts :
    InnerPairRoundedFacts innerPair619Data innerPair619Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair619Input_eq }

noncomputable def innerPair620Data : WideLogData :=
  { lower := endpoint346
    upper := endpoint293 }

noncomputable def innerPair620Input : RationalEnclosure :=
  { lower := (6640827/8388608), upper := (6758771/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair620Input_eq :
    innerPair620Input = outerEnclosure 24 innerPair620Data.output := by
  rfl'

theorem innerPair620RoundedFacts :
    InnerPairRoundedFacts innerPair620Data innerPair620Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair620Input_eq }

noncomputable def innerPair621Data : WideLogData :=
  { lower := endpoint347
    upper := endpoint292 }

noncomputable def innerPair621Input : RationalEnclosure :=
  { lower := (3372059/4194304), upper := (6860629/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair621Input_eq :
    innerPair621Input = outerEnclosure 24 innerPair621Data.output := by
  rfl'

theorem innerPair621RoundedFacts :
    InnerPairRoundedFacts innerPair621Data innerPair621Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair621Input_eq }

noncomputable def innerPair622Data : WideLogData :=
  { lower := endpoint347
    upper := endpoint295 }

noncomputable def innerPair622Input : RationalEnclosure :=
  { lower := (3372059/4194304), upper := (6918283/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair622Input_eq :
    innerPair622Input = outerEnclosure 24 innerPair622Data.output := by
  rfl'

theorem innerPair622RoundedFacts :
    InnerPairRoundedFacts innerPair622Data innerPair622Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair622Input_eq }

noncomputable def innerPair623Data : WideLogData :=
  { lower := endpoint349
    upper := endpoint350 }

noncomputable def innerPair623Input : RationalEnclosure :=
  { lower := (13237053/16777216), upper := (13524861/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair623Input_eq :
    innerPair623Input = outerEnclosure 24 innerPair623Data.output := by
  rfl'

theorem innerPair623RoundedFacts :
    InnerPairRoundedFacts innerPair623Data innerPair623Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair623Input_eq }

noncomputable def innerPair624Data : WideLogData :=
  { lower := endpoint351
    upper := endpoint352 }

noncomputable def innerPair624Input : RationalEnclosure :=
  { lower := (2931265/4194304), upper := (11917405/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair624Input_eq :
    innerPair624Input = outerEnclosure 24 innerPair624Data.output := by
  rfl'

theorem innerPair624RoundedFacts :
    InnerPairRoundedFacts innerPair624Data innerPair624Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair624Input_eq }

noncomputable def innerPair625Data : WideLogData :=
  { lower := endpoint353
    upper := endpoint354 }

noncomputable def innerPair625Input : RationalEnclosure :=
  { lower := (12025761/16777216), upper := (6112297/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair625Input_eq :
    innerPair625Input = outerEnclosure 24 innerPair625Data.output := by
  rfl'

theorem innerPair625RoundedFacts :
    InnerPairRoundedFacts innerPair625Data innerPair625Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair625Input_eq }

noncomputable def innerPair626Data : WideLogData :=
  { lower := endpoint355
    upper := endpoint358 }

noncomputable def innerPair626Input : RationalEnclosure :=
  { lower := (12334917/16777216), upper := (1569177/2097152) }

set_option maxRecDepth 1000000 in
private theorem innerPair626Input_eq :
    innerPair626Input = outerEnclosure 24 innerPair626Data.output := by
  rfl'

theorem innerPair626RoundedFacts :
    InnerPairRoundedFacts innerPair626Data innerPair626Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair626Input_eq }

noncomputable def innerPair627Data : WideLogData :=
  { lower := endpoint356
    upper := endpoint357 }

noncomputable def innerPair627Input : RationalEnclosure :=
  { lower := (6120199/8388608), upper := (6230061/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair627Input_eq :
    innerPair627Input = outerEnclosure 24 innerPair627Data.output := by
  rfl'

theorem innerPair627RoundedFacts :
    InnerPairRoundedFacts innerPair627Data innerPair627Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair627Input_eq }

noncomputable def innerPair628Data : WideLogData :=
  { lower := endpoint357
    upper := endpoint363 }

noncomputable def innerPair628Input : RationalEnclosure :=
  { lower := (12460121/16777216), upper := (12677005/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair628Input_eq :
    innerPair628Input = outerEnclosure 24 innerPair628Data.output := by
  rfl'

theorem innerPair628RoundedFacts :
    InnerPairRoundedFacts innerPair628Data innerPair628Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair628Input_eq }

noncomputable def innerPair629Data : WideLogData :=
  { lower := endpoint358
    upper := endpoint336 }

noncomputable def innerPair629Input : RationalEnclosure :=
  { lower := (6276707/8388608), upper := (12799691/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair629Input_eq :
    innerPair629Input = outerEnclosure 24 innerPair629Data.output := by
  rfl'

theorem innerPair629RoundedFacts :
    InnerPairRoundedFacts innerPair629Data innerPair629Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair629Input_eq }

noncomputable def innerPair630Data : WideLogData :=
  { lower := endpoint362
    upper := endpoint322 }

noncomputable def innerPair630Input : RationalEnclosure :=
  { lower := (11596279/16777216), upper := (5896063/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair630Input_eq :
    innerPair630Input = outerEnclosure 24 innerPair630Data.output := by
  rfl'

theorem innerPair630RoundedFacts :
    InnerPairRoundedFacts innerPair630Data innerPair630Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair630Input_eq }

noncomputable def innerPair631Data : WideLogData :=
  { lower := endpoint364
    upper := endpoint365 }

noncomputable def innerPair631Input : RationalEnclosure :=
  { lower := (12615323/16777216), upper := (12830223/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair631Input_eq :
    innerPair631Input = outerEnclosure 24 innerPair631Data.output := by
  rfl'

theorem innerPair631RoundedFacts :
    InnerPairRoundedFacts innerPair631Data innerPair631Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair631Input_eq }

noncomputable def innerPair632Data : WideLogData :=
  { lower := endpoint365
    upper := endpoint367 }

noncomputable def innerPair632Input : RationalEnclosure :=
  { lower := (6415111/8388608), upper := (3260601/4194304) }

set_option maxRecDepth 1000000 in
private theorem innerPair632Input_eq :
    innerPair632Input = outerEnclosure 24 innerPair632Data.output := by
  rfl'

theorem innerPair632RoundedFacts :
    InnerPairRoundedFacts innerPair632Data innerPair632Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair632Input_eq }

noncomputable def innerPair633Data : WideLogData :=
  { lower := endpoint366
    upper := endpoint345 }

noncomputable def innerPair633Input : RationalEnclosure :=
  { lower := (12738459/16777216), upper := (12951797/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair633Input_eq :
    innerPair633Input = outerEnclosure 24 innerPair633Data.output := by
  rfl'

theorem innerPair633RoundedFacts :
    InnerPairRoundedFacts innerPair633Data innerPair633Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair633Input_eq }

noncomputable def innerPair634Data : WideLogData :=
  { lower := endpoint367
    upper := endpoint346 }

noncomputable def innerPair634Input : RationalEnclosure :=
  { lower := (6521201/8388608), upper := (13281655/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair634Input_eq :
    innerPair634Input = outerEnclosure 24 innerPair634Data.output := by
  rfl'

theorem innerPair634RoundedFacts :
    InnerPairRoundedFacts innerPair634Data innerPair634Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair634Input_eq }

noncomputable def innerPair635Data : WideLogData :=
  { lower := endpoint368
    upper := endpoint369 }

noncomputable def innerPair635Input : RationalEnclosure :=
  { lower := (3175019/4194304), upper := (12898717/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair635Input_eq :
    innerPair635Input = outerEnclosure 24 innerPair635Data.output := by
  rfl'

theorem innerPair635RoundedFacts :
    InnerPairRoundedFacts innerPair635Data innerPair635Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair635Input_eq }

noncomputable def innerPair636Data : WideLogData :=
  { lower := endpoint371
    upper := endpoint372 }

noncomputable def innerPair636Input : RationalEnclosure :=
  { lower := (12982053/16777216), upper := (13222161/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair636Input_eq :
    innerPair636Input = outerEnclosure 24 innerPair636Data.output := by
  rfl'

theorem innerPair636RoundedFacts :
    InnerPairRoundedFacts innerPair636Data innerPair636Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair636Input_eq }

noncomputable def innerPair637Data : WideLogData :=
  { lower := endpoint372
    upper := endpoint379 }

noncomputable def innerPair637Input : RationalEnclosure :=
  { lower := (826385/1048576), upper := (13429473/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair637Input_eq :
    innerPair637Input = outerEnclosure 24 innerPair637Data.output := by
  rfl'

theorem innerPair637RoundedFacts :
    InnerPairRoundedFacts innerPair637Data innerPair637Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair637Input_eq }

noncomputable def innerPair638Data : WideLogData :=
  { lower := endpoint373
    upper := endpoint374 }

noncomputable def innerPair638Input : RationalEnclosure :=
  { lower := (1637817/2097152), upper := (13311323/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair638Input_eq :
    innerPair638Input = outerEnclosure 24 innerPair638Data.output := by
  rfl'

theorem innerPair638RoundedFacts :
    InnerPairRoundedFacts innerPair638Data innerPair638Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair638Input_eq }

noncomputable def innerPair639Data : WideLogData :=
  { lower := endpoint375
    upper := endpoint376 }

noncomputable def innerPair639Input : RationalEnclosure :=
  { lower := (13080011/16777216), upper := (6637115/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair639Input_eq :
    innerPair639Input = outerEnclosure 24 innerPair639Data.output := by
  rfl'

theorem innerPair639RoundedFacts :
    InnerPairRoundedFacts innerPair639Data innerPair639Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair639Input_eq }

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
