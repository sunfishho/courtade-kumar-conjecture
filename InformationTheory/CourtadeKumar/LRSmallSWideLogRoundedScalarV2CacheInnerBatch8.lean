import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch3
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch4
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch5

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

noncomputable def innerPair512Data : WideLogData :=
  { lower := endpoint241
    upper := endpoint245 }

noncomputable def innerPair512Input : RationalEnclosure :=
  { lower := (2610279/4194304), upper := (10650835/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair512Input_eq :
    innerPair512Input = outerEnclosure 24 innerPair512Data.output := by
  rfl'

theorem innerPair512RoundedFacts :
    InnerPairRoundedFacts innerPair512Data innerPair512Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair512Input_eq }

noncomputable def innerPair513Data : WideLogData :=
  { lower := endpoint241
    upper := endpoint247 }

noncomputable def innerPair513Input : RationalEnclosure :=
  { lower := (2610279/4194304), upper := (10789205/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair513Input_eq :
    innerPair513Input = outerEnclosure 24 innerPair513Data.output := by
  rfl'

theorem innerPair513RoundedFacts :
    InnerPairRoundedFacts innerPair513Data innerPair513Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair513Input_eq }

noncomputable def innerPair514Data : WideLogData :=
  { lower := endpoint243
    upper := endpoint244 }

noncomputable def innerPair514Input : RationalEnclosure :=
  { lower := (5255657/8388608), upper := (10720163/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair514Input_eq :
    innerPair514Input = outerEnclosure 24 innerPair514Data.output := by
  rfl'

theorem innerPair514RoundedFacts :
    InnerPairRoundedFacts innerPair514Data innerPair514Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair514Input_eq }

noncomputable def innerPair515Data : WideLogData :=
  { lower := endpoint245
    upper := endpoint246 }

noncomputable def innerPair515Input : RationalEnclosure :=
  { lower := (5325417/8388608), upper := (2714491/4194304) }

set_option maxRecDepth 1000000 in
private theorem innerPair515Input_eq :
    innerPair515Input = outerEnclosure 24 innerPair515Data.output := by
  rfl'

theorem innerPair515RoundedFacts :
    InnerPairRoundedFacts innerPair515Data innerPair515Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair515Input_eq }

noncomputable def innerPair516Data : WideLogData :=
  { lower := endpoint245
    upper := endpoint248 }

noncomputable def innerPair516Input : RationalEnclosure :=
  { lower := (5325417/8388608), upper := (10994643/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair516Input_eq :
    innerPair516Input = outerEnclosure 24 innerPair516Data.output := by
  rfl'

theorem innerPair516RoundedFacts :
    InnerPairRoundedFacts innerPair516Data innerPair516Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair516Input_eq }

noncomputable def innerPair517Data : WideLogData :=
  { lower := endpoint247
    upper := endpoint248 }

noncomputable def innerPair517Input : RationalEnclosure :=
  { lower := (2697301/4194304), upper := (10994643/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair517Input_eq :
    innerPair517Input = outerEnclosure 24 innerPair517Data.output := by
  rfl'

theorem innerPair517RoundedFacts :
    InnerPairRoundedFacts innerPair517Data innerPair517Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair517Input_eq }

noncomputable def innerPair518Data : WideLogData :=
  { lower := endpoint248
    upper := endpoint271 }

noncomputable def innerPair518Input : RationalEnclosure :=
  { lower := (10994641/16777216), upper := (1396545/2097152) }

set_option maxRecDepth 1000000 in
private theorem innerPair518Input_eq :
    innerPair518Input = outerEnclosure 24 innerPair518Data.output := by
  rfl'

theorem innerPair518RoundedFacts :
    InnerPairRoundedFacts innerPair518Data innerPair518Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair518Input_eq }

noncomputable def innerPair519Data : WideLogData :=
  { lower := endpoint249
    upper := endpoint250 }

noncomputable def innerPair519Input : RationalEnclosure :=
  { lower := (10926441/16777216), upper := (11130217/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair519Input_eq :
    innerPair519Input = outerEnclosure 24 innerPair519Data.output := by
  rfl'

theorem innerPair519RoundedFacts :
    InnerPairRoundedFacts innerPair519Data innerPair519Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair519Input_eq }

noncomputable def innerPair520Data : WideLogData :=
  { lower := endpoint250
    upper := endpoint272 }

noncomputable def innerPair520Input : RationalEnclosure :=
  { lower := (1391277/2097152), upper := (11306511/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair520Input_eq :
    innerPair520Input = outerEnclosure 24 innerPair520Data.output := by
  rfl'

theorem innerPair520RoundedFacts :
    InnerPairRoundedFacts innerPair520Data innerPair520Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair520Input_eq }

noncomputable def innerPair521Data : WideLogData :=
  { lower := endpoint253
    upper := endpoint254 }

noncomputable def innerPair521Input : RationalEnclosure :=
  { lower := (5194137/8388608), upper := (10563771/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair521Input_eq :
    innerPair521Input = outerEnclosure 24 innerPair521Data.output := by
  rfl'

theorem innerPair521RoundedFacts :
    InnerPairRoundedFacts innerPair521Data innerPair521Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair521Input_eq }

noncomputable def innerPair522Data : WideLogData :=
  { lower := endpoint255
    upper := endpoint256 }

noncomputable def innerPair522Input : RationalEnclosure :=
  { lower := (10528817/16777216), upper := (5351429/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair522Input_eq :
    innerPair522Input = outerEnclosure 24 innerPair522Data.output := by
  rfl'

theorem innerPair522RoundedFacts :
    InnerPairRoundedFacts innerPair522Data innerPair522Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair522Input_eq }

noncomputable def innerPair523Data : WideLogData :=
  { lower := endpoint257
    upper := endpoint248 }

noncomputable def innerPair523Input : RationalEnclosure :=
  { lower := (5377359/8388608), upper := (10994643/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair523Input_eq :
    innerPair523Input = outerEnclosure 24 innerPair523Data.output := by
  rfl'

theorem innerPair523RoundedFacts :
    InnerPairRoundedFacts innerPair523Data innerPair523Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair523Input_eq }

noncomputable def innerPair524Data : WideLogData :=
  { lower := endpoint257
    upper := endpoint265 }

noncomputable def innerPair524Input : RationalEnclosure :=
  { lower := (5377359/8388608), upper := (11062567/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair524Input_eq :
    innerPair524Input = outerEnclosure 24 innerPair524Data.output := by
  rfl'

theorem innerPair524RoundedFacts :
    InnerPairRoundedFacts innerPair524Data innerPair524Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair524Input_eq }

noncomputable def innerPair525Data : WideLogData :=
  { lower := endpoint259
    upper := endpoint260 }

noncomputable def innerPair525Input : RationalEnclosure :=
  { lower := (10694197/16777216), upper := (10866539/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair525Input_eq :
    innerPair525Input = outerEnclosure 24 innerPair525Data.output := by
  rfl'

theorem innerPair525RoundedFacts :
    InnerPairRoundedFacts innerPair525Data innerPair525Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair525Input_eq }

noncomputable def innerPair526Data : WideLogData :=
  { lower := endpoint261
    upper := endpoint262 }

noncomputable def innerPair526Input : RationalEnclosure :=
  { lower := (10832211/16777216), upper := (2750787/4194304) }

set_option maxRecDepth 1000000 in
private theorem innerPair526Input_eq :
    innerPair526Input = outerEnclosure 24 innerPair526Data.output := by
  rfl'

theorem innerPair526RoundedFacts :
    InnerPairRoundedFacts innerPair526Data innerPair526Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair526Input_eq }

noncomputable def innerPair527Data : WideLogData :=
  { lower := endpoint263
    upper := endpoint264 }

noncomputable def innerPair527Input : RationalEnclosure :=
  { lower := (10864395/16777216), upper := (2758221/4194304) }

set_option maxRecDepth 1000000 in
private theorem innerPair527Input_eq :
    innerPair527Input = outerEnclosure 24 innerPair527Data.output := by
  rfl'

theorem innerPair527RoundedFacts :
    InnerPairRoundedFacts innerPair527Data innerPair527Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair527Input_eq }

noncomputable def innerPair528Data : WideLogData :=
  { lower := endpoint265
    upper := endpoint83 }

noncomputable def innerPair528Input : RationalEnclosure :=
  { lower := (5531283/8388608), upper := (5649079/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair528Input_eq :
    innerPair528Input = outerEnclosure 24 innerPair528Data.output := by
  rfl'

theorem innerPair528RoundedFacts :
    InnerPairRoundedFacts innerPair528Data innerPair528Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair528Input_eq }

noncomputable def innerPair529Data : WideLogData :=
  { lower := endpoint265
    upper := endpoint266 }

noncomputable def innerPair529Input : RationalEnclosure :=
  { lower := (5531283/8388608), upper := (176011/262144) }

set_option maxRecDepth 1000000 in
private theorem innerPair529Input_eq :
    innerPair529Input = outerEnclosure 24 innerPair529Data.output := by
  rfl'

theorem innerPair529RoundedFacts :
    InnerPairRoundedFacts innerPair529Data innerPair529Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair529Input_eq }

noncomputable def innerPair530Data : WideLogData :=
  { lower := endpoint266
    upper := endpoint276 }

noncomputable def innerPair530Input : RationalEnclosure :=
  { lower := (11264703/16777216), upper := (11464435/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair530Input_eq :
    innerPair530Input = outerEnclosure 24 innerPair530Data.output := by
  rfl'

theorem innerPair530RoundedFacts :
    InnerPairRoundedFacts innerPair530Data innerPair530Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair530Input_eq }

noncomputable def innerPair531Data : WideLogData :=
  { lower := endpoint267
    upper := endpoint82 }

noncomputable def innerPair531Input : RationalEnclosure :=
  { lower := (11497493/16777216), upper := (5944599/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair531Input_eq :
    innerPair531Input = outerEnclosure 24 innerPair531Data.output := by
  rfl'

theorem innerPair531RoundedFacts :
    InnerPairRoundedFacts innerPair531Data innerPair531Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair531Input_eq }

noncomputable def innerPair532Data : WideLogData :=
  { lower := endpoint267
    upper := endpoint86 }

noncomputable def innerPair532Input : RationalEnclosure :=
  { lower := (11497493/16777216), upper := (12271965/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair532Input_eq :
    innerPair532Input = outerEnclosure 24 innerPair532Data.output := by
  rfl'

theorem innerPair532RoundedFacts :
    InnerPairRoundedFacts innerPair532Data innerPair532Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair532Input_eq }

noncomputable def innerPair533Data : WideLogData :=
  { lower := endpoint267
    upper := endpoint283 }

noncomputable def innerPair533Input : RationalEnclosure :=
  { lower := (11497493/16777216), upper := (11759643/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair533Input_eq :
    innerPair533Input = outerEnclosure 24 innerPair533Data.output := by
  rfl'

theorem innerPair533RoundedFacts :
    InnerPairRoundedFacts innerPair533Data innerPair533Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair533Input_eq }

noncomputable def innerPair534Data : WideLogData :=
  { lower := endpoint267
    upper := endpoint361 }

noncomputable def innerPair534Input : RationalEnclosure :=
  { lower := (11497493/16777216), upper := (11694489/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair534Input_eq :
    innerPair534Input = outerEnclosure 24 innerPair534Data.output := by
  rfl'

theorem innerPair534RoundedFacts :
    InnerPairRoundedFacts innerPair534Data innerPair534Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair534Input_eq }

noncomputable def innerPair535Data : WideLogData :=
  { lower := endpoint268
    upper := endpoint269 }

noncomputable def innerPair535Input : RationalEnclosure :=
  { lower := (5598797/8388608), upper := (5699061/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair535Input_eq :
    innerPair535Input = outerEnclosure 24 innerPair535Data.output := by
  rfl'

theorem innerPair535RoundedFacts :
    InnerPairRoundedFacts innerPair535Data innerPair535Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair535Input_eq }

noncomputable def innerPair536Data : WideLogData :=
  { lower := endpoint269
    upper := endpoint278 }

noncomputable def innerPair536Input : RationalEnclosure :=
  { lower := (11398121/16777216), upper := (1445427/2097152) }

set_option maxRecDepth 1000000 in
private theorem innerPair536Input_eq :
    innerPair536Input = outerEnclosure 24 innerPair536Data.output := by
  rfl'

theorem innerPair536RoundedFacts :
    InnerPairRoundedFacts innerPair536Data innerPair536Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair536Input_eq }

noncomputable def innerPair537Data : WideLogData :=
  { lower := endpoint272
    upper := endpoint282 }

noncomputable def innerPair537Input : RationalEnclosure :=
  { lower := (5653255/8388608), upper := (2960183/4194304) }

set_option maxRecDepth 1000000 in
private theorem innerPair537Input_eq :
    innerPair537Input = outerEnclosure 24 innerPair537Data.output := by
  rfl'

theorem innerPair537RoundedFacts :
    InnerPairRoundedFacts innerPair537Data innerPair537Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair537Input_eq }

noncomputable def innerPair538Data : WideLogData :=
  { lower := endpoint273
    upper := endpoint269 }

noncomputable def innerPair538Input : RationalEnclosure :=
  { lower := (11163939/16777216), upper := (5699061/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair538Input_eq :
    innerPair538Input = outerEnclosure 24 innerPair538Data.output := by
  rfl'

theorem innerPair538RoundedFacts :
    InnerPairRoundedFacts innerPair538Data innerPair538Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair538Input_eq }

noncomputable def innerPair539Data : WideLogData :=
  { lower := endpoint273
    upper := endpoint274 }

noncomputable def innerPair539Input : RationalEnclosure :=
  { lower := (11163939/16777216), upper := (5669941/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair539Input_eq :
    innerPair539Input = outerEnclosure 24 innerPair539Data.output := by
  rfl'

theorem innerPair539RoundedFacts :
    InnerPairRoundedFacts innerPair539Data innerPair539Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair539Input_eq }

noncomputable def innerPair540Data : WideLogData :=
  { lower := endpoint274
    upper := endpoint328 }

noncomputable def innerPair540Input : RationalEnclosure :=
  { lower := (11339881/16777216), upper := (11637271/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair540Input_eq :
    innerPair540Input = outerEnclosure 24 innerPair540Data.output := by
  rfl'

theorem innerPair540RoundedFacts :
    InnerPairRoundedFacts innerPair540Data innerPair540Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair540Input_eq }

noncomputable def innerPair541Data : WideLogData :=
  { lower := endpoint275
    upper := endpoint320 }

noncomputable def innerPair541Input : RationalEnclosure :=
  { lower := (5715655/8388608), upper := (11661817/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair541Input_eq :
    innerPair541Input = outerEnclosure 24 innerPair541Data.output := by
  rfl'

theorem innerPair541RoundedFacts :
    InnerPairRoundedFacts innerPair541Data innerPair541Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair541Input_eq }

noncomputable def innerPair542Data : WideLogData :=
  { lower := endpoint276
    upper := endpoint320 }

noncomputable def innerPair542Input : RationalEnclosure :=
  { lower := (5732217/8388608), upper := (11661817/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair542Input_eq :
    innerPair542Input = outerEnclosure 24 innerPair542Data.output := by
  rfl'

theorem innerPair542RoundedFacts :
    InnerPairRoundedFacts innerPair542Data innerPair542Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair542Input_eq }

noncomputable def innerPair543Data : WideLogData :=
  { lower := endpoint277
    upper := endpoint321 }

noncomputable def innerPair543Input : RationalEnclosure :=
  { lower := (5765243/8388608), upper := (5863549/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair543Input_eq :
    innerPair543Input = outerEnclosure 24 innerPair543Data.output := by
  rfl'

theorem innerPair543RoundedFacts :
    InnerPairRoundedFacts innerPair543Data innerPair543Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair543Input_eq }

noncomputable def innerPair544Data : WideLogData :=
  { lower := endpoint278
    upper := endpoint288 }

noncomputable def innerPair544Input : RationalEnclosure :=
  { lower := (11563415/16777216), upper := (12049747/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair544Input_eq :
    innerPair544Input = outerEnclosure 24 innerPair544Data.output := by
  rfl'

theorem innerPair544RoundedFacts :
    InnerPairRoundedFacts innerPair544Data innerPair544Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair544Input_eq }

noncomputable def innerPair545Data : WideLogData :=
  { lower := endpoint278
    upper := endpoint322 }

noncomputable def innerPair545Input : RationalEnclosure :=
  { lower := (11563415/16777216), upper := (5896063/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair545Input_eq :
    innerPair545Input = outerEnclosure 24 innerPair545Data.output := by
  rfl'

theorem innerPair545RoundedFacts :
    InnerPairRoundedFacts innerPair545Data innerPair545Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair545Input_eq }

noncomputable def innerPair546Data : WideLogData :=
  { lower := endpoint280
    upper := endpoint281 }

noncomputable def innerPair546Input : RationalEnclosure :=
  { lower := (10780589/16777216), upper := (2828715/4194304) }

set_option maxRecDepth 1000000 in
private theorem innerPair546Input_eq :
    innerPair546Input = outerEnclosure 24 innerPair546Data.output := by
  rfl'

theorem innerPair546RoundedFacts :
    InnerPairRoundedFacts innerPair546Data innerPair546Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair546Input_eq }

noncomputable def innerPair547Data : WideLogData :=
  { lower := endpoint283
    upper := endpoint86 }

noncomputable def innerPair547Input : RationalEnclosure :=
  { lower := (5879821/8388608), upper := (12271965/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair547Input_eq :
    innerPair547Input = outerEnclosure 24 innerPair547Data.output := by
  rfl'

theorem innerPair547RoundedFacts :
    InnerPairRoundedFacts innerPair547Data innerPair547Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair547Input_eq }

noncomputable def innerPair548Data : WideLogData :=
  { lower := endpoint283
    upper := endpoint87 }

noncomputable def innerPair548Input : RationalEnclosure :=
  { lower := (5879821/8388608), upper := (375555/524288) }

set_option maxRecDepth 1000000 in
private theorem innerPair548Input_eq :
    innerPair548Input = outerEnclosure 24 innerPair548Data.output := by
  rfl'

theorem innerPair548RoundedFacts :
    InnerPairRoundedFacts innerPair548Data innerPair548Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair548Input_eq }

noncomputable def innerPair549Data : WideLogData :=
  { lower := endpoint283
    upper := endpoint284 }

noncomputable def innerPair549Input : RationalEnclosure :=
  { lower := (5879821/8388608), upper := (12397637/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair549Input_eq :
    innerPair549Input = outerEnclosure 24 innerPair549Data.output := by
  rfl'

theorem innerPair549RoundedFacts :
    InnerPairRoundedFacts innerPair549Data innerPair549Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair549Input_eq }

noncomputable def innerPair550Data : WideLogData :=
  { lower := endpoint283
    upper := endpoint324 }

noncomputable def innerPair550Input : RationalEnclosure :=
  { lower := (5879821/8388608), upper := (5976801/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair550Input_eq :
    innerPair550Input = outerEnclosure 24 innerPair550Data.output := by
  rfl'

theorem innerPair550RoundedFacts :
    InnerPairRoundedFacts innerPair550Data innerPair550Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair550Input_eq }

noncomputable def innerPair551Data : WideLogData :=
  { lower := endpoint284
    upper := endpoint289 }

noncomputable def innerPair551Input : RationalEnclosure :=
  { lower := (3099409/4194304), upper := (798069/1048576) }

set_option maxRecDepth 1000000 in
private theorem innerPair551Input_eq :
    innerPair551Input = outerEnclosure 24 innerPair551Data.output := by
  rfl'

theorem innerPair551RoundedFacts :
    InnerPairRoundedFacts innerPair551Data innerPair551Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair551Input_eq }

noncomputable def innerPair552Data : WideLogData :=
  { lower := endpoint285
    upper := endpoint286 }

noncomputable def innerPair552Input : RationalEnclosure :=
  { lower := (369517/524288), upper := (12366307/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair552Input_eq :
    innerPair552Input = outerEnclosure 24 innerPair552Data.output := by
  rfl'

theorem innerPair552RoundedFacts :
    InnerPairRoundedFacts innerPair552Data innerPair552Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair552Input_eq }

noncomputable def innerPair553Data : WideLogData :=
  { lower := endpoint285
    upper := endpoint288 }

noncomputable def innerPair553Input : RationalEnclosure :=
  { lower := (369517/524288), upper := (12049747/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair553Input_eq :
    innerPair553Input = outerEnclosure 24 innerPair553Data.output := by
  rfl'

theorem innerPair553RoundedFacts :
    InnerPairRoundedFacts innerPair553Data innerPair553Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair553Input_eq }

noncomputable def innerPair554Data : WideLogData :=
  { lower := endpoint289
    upper := endpoint337 }

noncomputable def innerPair554Input : RationalEnclosure :=
  { lower := (6384551/8388608), upper := (406633/524288) }

set_option maxRecDepth 1000000 in
private theorem innerPair554Input_eq :
    innerPair554Input = outerEnclosure 24 innerPair554Data.output := by
  rfl'

theorem innerPair554RoundedFacts :
    InnerPairRoundedFacts innerPair554Data innerPair554Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair554Input_eq }

noncomputable def innerPair555Data : WideLogData :=
  { lower := endpoint289
    upper := endpoint340 }

noncomputable def innerPair555Input : RationalEnclosure :=
  { lower := (6384551/8388608), upper := (13072497/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair555Input_eq :
    innerPair555Input = outerEnclosure 24 innerPair555Data.output := by
  rfl'

theorem innerPair555RoundedFacts :
    InnerPairRoundedFacts innerPair555Data innerPair555Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair555Input_eq }

noncomputable def innerPair556Data : WideLogData :=
  { lower := endpoint291
    upper := endpoint292 }

noncomputable def innerPair556Input : RationalEnclosure :=
  { lower := (13251933/16777216), upper := (6860629/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair556Input_eq :
    innerPair556Input = outerEnclosure 24 innerPair556Data.output := by
  rfl'

theorem innerPair556RoundedFacts :
    InnerPairRoundedFacts innerPair556Data innerPair556Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair556Input_eq }

noncomputable def innerPair557Data : WideLogData :=
  { lower := endpoint291
    upper := endpoint347 }

noncomputable def innerPair557Input : RationalEnclosure :=
  { lower := (13251933/16777216), upper := (13488237/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair557Input_eq :
    innerPair557Input = outerEnclosure 24 innerPair557Data.output := by
  rfl'

theorem innerPair557RoundedFacts :
    InnerPairRoundedFacts innerPair557Data innerPair557Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair557Input_eq }

noncomputable def innerPair558Data : WideLogData :=
  { lower := endpoint291
    upper := endpoint348 }

noncomputable def innerPair558Input : RationalEnclosure :=
  { lower := (13251933/16777216), upper := (13458881/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair558Input_eq :
    innerPair558Input = outerEnclosure 24 innerPair558Data.output := by
  rfl'

theorem innerPair558RoundedFacts :
    InnerPairRoundedFacts innerPair558Data innerPair558Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair558Input_eq }

noncomputable def innerPair559Data : WideLogData :=
  { lower := endpoint292
    upper := endpoint296 }

noncomputable def innerPair559Input : RationalEnclosure :=
  { lower := (13721257/16777216), upper := (14177809/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair559Input_eq :
    innerPair559Input = outerEnclosure 24 innerPair559Data.output := by
  rfl'

theorem innerPair559RoundedFacts :
    InnerPairRoundedFacts innerPair559Data innerPair559Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair559Input_eq }

noncomputable def innerPair560Data : WideLogData :=
  { lower := endpoint292
    upper := endpoint297 }

noncomputable def innerPair560Input : RationalEnclosure :=
  { lower := (13721257/16777216), upper := (893127/1048576) }

set_option maxRecDepth 1000000 in
private theorem innerPair560Input_eq :
    innerPair560Input = outerEnclosure 24 innerPair560Data.output := by
  rfl'

theorem innerPair560RoundedFacts :
    InnerPairRoundedFacts innerPair560Data innerPair560Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair560Input_eq }

noncomputable def innerPair561Data : WideLogData :=
  { lower := endpoint292
    upper := endpoint298 }

noncomputable def innerPair561Input : RationalEnclosure :=
  { lower := (13721257/16777216), upper := (6975543/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair561Input_eq :
    innerPair561Input = outerEnclosure 24 innerPair561Data.output := by
  rfl'

theorem innerPair561RoundedFacts :
    InnerPairRoundedFacts innerPair561Data innerPair561Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair561Input_eq }

noncomputable def innerPair562Data : WideLogData :=
  { lower := endpoint293
    upper := endpoint294 }

noncomputable def innerPair562Input : RationalEnclosure :=
  { lower := (13517541/16777216), upper := (3473481/4194304) }

set_option maxRecDepth 1000000 in
private theorem innerPair562Input_eq :
    innerPair562Input = outerEnclosure 24 innerPair562Data.output := by
  rfl'

theorem innerPair562RoundedFacts :
    InnerPairRoundedFacts innerPair562Data innerPair562Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair562Input_eq }

noncomputable def innerPair563Data : WideLogData :=
  { lower := endpoint295
    upper := endpoint296 }

noncomputable def innerPair563Input : RationalEnclosure :=
  { lower := (3459141/4194304), upper := (14177809/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair563Input_eq :
    innerPair563Input = outerEnclosure 24 innerPair563Data.output := by
  rfl'

theorem innerPair563RoundedFacts :
    InnerPairRoundedFacts innerPair563Data innerPair563Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair563Input_eq }

noncomputable def innerPair564Data : WideLogData :=
  { lower := endpoint295
    upper := endpoint297 }

noncomputable def innerPair564Input : RationalEnclosure :=
  { lower := (3459141/4194304), upper := (893127/1048576) }

set_option maxRecDepth 1000000 in
private theorem innerPair564Input_eq :
    innerPair564Input = outerEnclosure 24 innerPair564Data.output := by
  rfl'

theorem innerPair564RoundedFacts :
    InnerPairRoundedFacts innerPair564Data innerPair564Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair564Input_eq }

noncomputable def innerPair565Data : WideLogData :=
  { lower := endpoint295
    upper := endpoint305 }

noncomputable def innerPair565Input : RationalEnclosure :=
  { lower := (3459141/4194304), upper := (14731563/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair565Input_eq :
    innerPair565Input = outerEnclosure 24 innerPair565Data.output := by
  rfl'

theorem innerPair565RoundedFacts :
    InnerPairRoundedFacts innerPair565Data innerPair565Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair565Input_eq }

noncomputable def innerPair566Data : WideLogData :=
  { lower := endpoint296
    upper := endpoint299 }

noncomputable def innerPair566Input : RationalEnclosure :=
  { lower := (886113/1048576), upper := (14401509/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair566Input_eq :
    innerPair566Input = outerEnclosure 24 innerPair566Data.output := by
  rfl'

theorem innerPair566RoundedFacts :
    InnerPairRoundedFacts innerPair566Data innerPair566Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair566Input_eq }

noncomputable def innerPair567Data : WideLogData :=
  { lower := endpoint296
    upper := endpoint304 }

noncomputable def innerPair567Input : RationalEnclosure :=
  { lower := (886113/1048576), upper := (14622265/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair567Input_eq :
    innerPair567Input = outerEnclosure 24 innerPair567Data.output := by
  rfl'

theorem innerPair567RoundedFacts :
    InnerPairRoundedFacts innerPair567Data innerPair567Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair567Input_eq }

noncomputable def innerPair568Data : WideLogData :=
  { lower := endpoint296
    upper := endpoint305 }

noncomputable def innerPair568Input : RationalEnclosure :=
  { lower := (886113/1048576), upper := (14731563/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair568Input_eq :
    innerPair568Input = outerEnclosure 24 innerPair568Data.output := by
  rfl'

theorem innerPair568RoundedFacts :
    InnerPairRoundedFacts innerPair568Data innerPair568Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair568Input_eq }

noncomputable def innerPair569Data : WideLogData :=
  { lower := endpoint297
    upper := endpoint304 }

noncomputable def innerPair569Input : RationalEnclosure :=
  { lower := (7145015/8388608), upper := (14622265/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair569Input_eq :
    innerPair569Input = outerEnclosure 24 innerPair569Data.output := by
  rfl'

theorem innerPair569RoundedFacts :
    InnerPairRoundedFacts innerPair569Data innerPair569Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair569Input_eq }

noncomputable def innerPair570Data : WideLogData :=
  { lower := endpoint297
    upper := endpoint305 }

noncomputable def innerPair570Input : RationalEnclosure :=
  { lower := (7145015/8388608), upper := (14731563/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair570Input_eq :
    innerPair570Input = outerEnclosure 24 innerPair570Data.output := by
  rfl'

theorem innerPair570RoundedFacts :
    InnerPairRoundedFacts innerPair570Data innerPair570Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair570Input_eq }

noncomputable def innerPair571Data : WideLogData :=
  { lower := endpoint298
    upper := endpoint296 }

noncomputable def innerPair571Input : RationalEnclosure :=
  { lower := (13951085/16777216), upper := (14177809/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair571Input_eq :
    innerPair571Input = outerEnclosure 24 innerPair571Data.output := by
  rfl'

theorem innerPair571RoundedFacts :
    InnerPairRoundedFacts innerPair571Data innerPair571Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair571Input_eq }

noncomputable def innerPair572Data : WideLogData :=
  { lower := endpoint298
    upper := endpoint297 }

noncomputable def innerPair572Input : RationalEnclosure :=
  { lower := (13951085/16777216), upper := (893127/1048576) }

set_option maxRecDepth 1000000 in
private theorem innerPair572Input_eq :
    innerPair572Input = outerEnclosure 24 innerPair572Data.output := by
  rfl'

theorem innerPair572RoundedFacts :
    InnerPairRoundedFacts innerPair572Data innerPair572Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair572Input_eq }

noncomputable def innerPair573Data : WideLogData :=
  { lower := endpoint298
    upper := endpoint299 }

noncomputable def innerPair573Input : RationalEnclosure :=
  { lower := (13951085/16777216), upper := (14401509/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair573Input_eq :
    innerPair573Input = outerEnclosure 24 innerPair573Data.output := by
  rfl'

theorem innerPair573RoundedFacts :
    InnerPairRoundedFacts innerPair573Data innerPair573Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair573Input_eq }

noncomputable def innerPair574Data : WideLogData :=
  { lower := endpoint298
    upper := endpoint306 }

noncomputable def innerPair574Input : RationalEnclosure :=
  { lower := (13951085/16777216), upper := (7131023/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair574Input_eq :
    innerPair574Input = outerEnclosure 24 innerPair574Data.output := by
  rfl'

theorem innerPair574RoundedFacts :
    InnerPairRoundedFacts innerPair574Data innerPair574Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair574Input_eq }

noncomputable def innerPair575Data : WideLogData :=
  { lower := endpoint299
    upper := endpoint304 }

noncomputable def innerPair575Input : RationalEnclosure :=
  { lower := (14401507/16777216), upper := (14622265/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair575Input_eq :
    innerPair575Input = outerEnclosure 24 innerPair575Data.output := by
  rfl'

theorem innerPair575RoundedFacts :
    InnerPairRoundedFacts innerPair575Data innerPair575Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair575Input_eq }

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
