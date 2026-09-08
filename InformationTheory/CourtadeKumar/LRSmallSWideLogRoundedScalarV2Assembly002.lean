import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component017
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component018
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component019
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component020
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component021
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component022
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component023
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component024
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component025
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component026
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component027
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component028
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component029
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component030
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component031
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component032
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component033
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component034
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component035
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component036
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component037
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component038
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component039
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component040
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component041
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component042
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component043
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component044
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component045
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component046
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component047
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component048
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component049
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component050
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component051
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component052
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component053
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component054
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component055
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component056
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component057
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component058
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component059
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component060
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component061
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component062
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component063
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component064
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component065
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component066
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component067
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component068
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component069
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component070
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component071
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component072
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component073

namespace CourtadeKumar
namespace LRSmallSWideLogRoundedScalarV2

open LRSmallSBridgeCoreCertificate
open LRSmallSWideLogRoundedFlatTopology

private noncomputable def assembly2Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (5/2), chiLo := (0), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem assembly2Node0_sound : Sound assembly2Node0Box :=
  sound_of_literal_split assembly2Node0Box component17Box component18Box
    .k (9/4) (by rfl) (by rfl)
    component17_sound component18_sound

private noncomputable def assembly2Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (5/2), chiLo := (1/8), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem assembly2Node1_sound : Sound assembly2Node1Box :=
  sound_of_literal_split assembly2Node1Box component20Box component21Box
    .chi (3/16) (by rfl) (by rfl)
    component20_sound component21_sound

private noncomputable def assembly2Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (5/2), chiLo := (1/8), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem assembly2Node2_sound : Sound assembly2Node2Box :=
  sound_of_literal_split assembly2Node2Box component19Box assembly2Node1Box
    .k (9/4) (by rfl) (by rfl)
    component19_sound assembly2Node1_sound

private noncomputable def assembly2Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (5/2), chiLo := (0), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem assembly2Node3_sound : Sound assembly2Node3Box :=
  sound_of_literal_split assembly2Node3Box assembly2Node0Box assembly2Node2Box
    .chi (1/8) (by rfl) (by rfl)
    assembly2Node0_sound assembly2Node2_sound

private noncomputable def assembly2Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (3), chiLo := (1/16), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem assembly2Node4_sound : Sound assembly2Node4Box :=
  sound_of_literal_split assembly2Node4Box component23Box component24Box
    .k (11/4) (by rfl) (by rfl)
    component23_sound component24_sound

private noncomputable def assembly2Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (3), chiLo := (0), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem assembly2Node5_sound : Sound assembly2Node5Box :=
  sound_of_literal_split assembly2Node5Box component22Box assembly2Node4Box
    .chi (1/16) (by rfl) (by rfl)
    component22_sound assembly2Node4_sound

private noncomputable def assembly2Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (3), chiLo := (1/8), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem assembly2Node6_sound : Sound assembly2Node6Box :=
  sound_of_literal_split assembly2Node6Box component26Box component27Box
    .chi (5/32) (by rfl) (by rfl)
    component26_sound component27_sound

private noncomputable def assembly2Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (3), chiLo := (1/8), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem assembly2Node7_sound : Sound assembly2Node7Box :=
  sound_of_literal_split assembly2Node7Box component25Box assembly2Node6Box
    .k (11/4) (by rfl) (by rfl)
    component25_sound assembly2Node6_sound

private noncomputable def assembly2Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (3), chiLo := (3/16), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem assembly2Node8_sound : Sound assembly2Node8Box :=
  sound_of_literal_split assembly2Node8Box component29Box component30Box
    .chi (7/32) (by rfl) (by rfl)
    component29_sound component30_sound

private noncomputable def assembly2Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (3), chiLo := (3/16), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem assembly2Node9_sound : Sound assembly2Node9Box :=
  sound_of_literal_split assembly2Node9Box component28Box assembly2Node8Box
    .k (11/4) (by rfl) (by rfl)
    component28_sound assembly2Node8_sound

private noncomputable def assembly2Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (3), chiLo := (1/8), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem assembly2Node10_sound : Sound assembly2Node10Box :=
  sound_of_literal_split assembly2Node10Box assembly2Node7Box assembly2Node9Box
    .chi (3/16) (by rfl) (by rfl)
    assembly2Node7_sound assembly2Node9_sound

private noncomputable def assembly2Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (3), chiLo := (0), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem assembly2Node11_sound : Sound assembly2Node11Box :=
  sound_of_literal_split assembly2Node11Box assembly2Node5Box assembly2Node10Box
    .chi (1/8) (by rfl) (by rfl)
    assembly2Node5_sound assembly2Node10_sound

private noncomputable def assembly2Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (3), chiLo := (0), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem assembly2Node12_sound : Sound assembly2Node12Box :=
  sound_of_literal_split assembly2Node12Box assembly2Node3Box assembly2Node11Box
    .k (5/2) (by rfl) (by rfl)
    assembly2Node3_sound assembly2Node11_sound

private noncomputable def assembly2Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (13/4), chiLo := (1/16), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem assembly2Node13_sound : Sound assembly2Node13Box :=
  sound_of_literal_split assembly2Node13Box component32Box component33Box
    .chi (3/32) (by rfl) (by rfl)
    component32_sound component33_sound

private noncomputable def assembly2Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (7/2), chiLo := (1/16), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem assembly2Node14_sound : Sound assembly2Node14Box :=
  sound_of_literal_split assembly2Node14Box component34Box component35Box
    .chi (3/32) (by rfl) (by rfl)
    component34_sound component35_sound

private noncomputable def assembly2Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (7/2), chiLo := (1/16), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem assembly2Node15_sound : Sound assembly2Node15Box :=
  sound_of_literal_split assembly2Node15Box assembly2Node13Box assembly2Node14Box
    .k (13/4) (by rfl) (by rfl)
    assembly2Node13_sound assembly2Node14_sound

private noncomputable def assembly2Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (7/2), chiLo := (0), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem assembly2Node16_sound : Sound assembly2Node16Box :=
  sound_of_literal_split assembly2Node16Box component31Box assembly2Node15Box
    .chi (1/16) (by rfl) (by rfl)
    component31_sound assembly2Node15_sound

private noncomputable def assembly2Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (4), chiLo := (0), chiHi := (1/16) }

set_option maxRecDepth 1000000 in
private theorem assembly2Node17_sound : Sound assembly2Node17Box :=
  sound_of_literal_split assembly2Node17Box component36Box component37Box
    .chi (1/32) (by rfl) (by rfl)
    component36_sound component37_sound

private noncomputable def assembly2Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (4), chiLo := (1/16), chiHi := (3/32) }

set_option maxRecDepth 1000000 in
private theorem assembly2Node18_sound : Sound assembly2Node18Box :=
  sound_of_literal_split assembly2Node18Box component38Box component39Box
    .k (15/4) (by rfl) (by rfl)
    component38_sound component39_sound

private noncomputable def assembly2Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (4), chiLo := (3/32), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem assembly2Node19_sound : Sound assembly2Node19Box :=
  sound_of_literal_split assembly2Node19Box component41Box component42Box
    .chi (7/64) (by rfl) (by rfl)
    component41_sound component42_sound

private noncomputable def assembly2Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (4), chiLo := (3/32), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem assembly2Node20_sound : Sound assembly2Node20Box :=
  sound_of_literal_split assembly2Node20Box component40Box assembly2Node19Box
    .k (15/4) (by rfl) (by rfl)
    component40_sound assembly2Node19_sound

private noncomputable def assembly2Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (4), chiLo := (1/16), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem assembly2Node21_sound : Sound assembly2Node21Box :=
  sound_of_literal_split assembly2Node21Box assembly2Node18Box assembly2Node20Box
    .chi (3/32) (by rfl) (by rfl)
    assembly2Node18_sound assembly2Node20_sound

private noncomputable def assembly2Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (4), chiLo := (0), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem assembly2Node22_sound : Sound assembly2Node22Box :=
  sound_of_literal_split assembly2Node22Box assembly2Node17Box assembly2Node21Box
    .chi (1/16) (by rfl) (by rfl)
    assembly2Node17_sound assembly2Node21_sound

private noncomputable def assembly2Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (4), chiLo := (0), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem assembly2Node23_sound : Sound assembly2Node23Box :=
  sound_of_literal_split assembly2Node23Box assembly2Node16Box assembly2Node22Box
    .k (7/2) (by rfl) (by rfl)
    assembly2Node16_sound assembly2Node22_sound

private noncomputable def assembly2Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (13/4), chiLo := (1/8), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem assembly2Node24_sound : Sound assembly2Node24Box :=
  sound_of_literal_split assembly2Node24Box component43Box component44Box
    .chi (5/32) (by rfl) (by rfl)
    component43_sound component44_sound

private noncomputable def assembly2Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (7/2), chiLo := (5/32), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem assembly2Node25_sound : Sound assembly2Node25Box :=
  sound_of_literal_split assembly2Node25Box component46Box component47Box
    .k (27/8) (by rfl) (by rfl)
    component46_sound component47_sound

private noncomputable def assembly2Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (7/2), chiLo := (1/8), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem assembly2Node26_sound : Sound assembly2Node26Box :=
  sound_of_literal_split assembly2Node26Box component45Box assembly2Node25Box
    .chi (5/32) (by rfl) (by rfl)
    component45_sound assembly2Node25_sound

private noncomputable def assembly2Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (7/2), chiLo := (1/8), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem assembly2Node27_sound : Sound assembly2Node27Box :=
  sound_of_literal_split assembly2Node27Box assembly2Node24Box assembly2Node26Box
    .k (13/4) (by rfl) (by rfl)
    assembly2Node24_sound assembly2Node26_sound

private noncomputable def assembly2Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (13/4), chiLo := (3/16), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem assembly2Node28_sound : Sound assembly2Node28Box :=
  sound_of_literal_split assembly2Node28Box component48Box component49Box
    .chi (7/32) (by rfl) (by rfl)
    component48_sound component49_sound

private noncomputable def assembly2Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (7/2), chiLo := (3/16), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem assembly2Node29_sound : Sound assembly2Node29Box :=
  sound_of_literal_split assembly2Node29Box component50Box component51Box
    .k (27/8) (by rfl) (by rfl)
    component50_sound component51_sound

private noncomputable def assembly2Node30Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (7/2), chiLo := (7/32), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem assembly2Node30_sound : Sound assembly2Node30Box :=
  sound_of_literal_split assembly2Node30Box component52Box component53Box
    .k (27/8) (by rfl) (by rfl)
    component52_sound component53_sound

private noncomputable def assembly2Node31Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (7/2), chiLo := (3/16), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem assembly2Node31_sound : Sound assembly2Node31Box :=
  sound_of_literal_split assembly2Node31Box assembly2Node29Box assembly2Node30Box
    .chi (7/32) (by rfl) (by rfl)
    assembly2Node29_sound assembly2Node30_sound

private noncomputable def assembly2Node32Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (7/2), chiLo := (3/16), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem assembly2Node32_sound : Sound assembly2Node32Box :=
  sound_of_literal_split assembly2Node32Box assembly2Node28Box assembly2Node31Box
    .k (13/4) (by rfl) (by rfl)
    assembly2Node28_sound assembly2Node31_sound

private noncomputable def assembly2Node33Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (7/2), chiLo := (1/8), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem assembly2Node33_sound : Sound assembly2Node33Box :=
  sound_of_literal_split assembly2Node33Box assembly2Node27Box assembly2Node32Box
    .chi (3/16) (by rfl) (by rfl)
    assembly2Node27_sound assembly2Node32_sound

private noncomputable def assembly2Node34Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (15/4), chiLo := (1/8), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem assembly2Node34_sound : Sound assembly2Node34Box :=
  sound_of_literal_split assembly2Node34Box component54Box component55Box
    .k (29/8) (by rfl) (by rfl)
    component54_sound component55_sound

private noncomputable def assembly2Node35Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (15/4), chiLo := (5/32), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem assembly2Node35_sound : Sound assembly2Node35Box :=
  sound_of_literal_split assembly2Node35Box component56Box component57Box
    .k (29/8) (by rfl) (by rfl)
    component56_sound component57_sound

private noncomputable def assembly2Node36Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (15/4), chiLo := (1/8), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem assembly2Node36_sound : Sound assembly2Node36Box :=
  sound_of_literal_split assembly2Node36Box assembly2Node34Box assembly2Node35Box
    .chi (5/32) (by rfl) (by rfl)
    assembly2Node34_sound assembly2Node35_sound

private noncomputable def assembly2Node37Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (4), chiLo := (1/8), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem assembly2Node37_sound : Sound assembly2Node37Box :=
  sound_of_literal_split assembly2Node37Box component59Box component60Box
    .chi (9/64) (by rfl) (by rfl)
    component59_sound component60_sound

private noncomputable def assembly2Node38Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (4), chiLo := (1/8), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem assembly2Node38_sound : Sound assembly2Node38Box :=
  sound_of_literal_split assembly2Node38Box component58Box assembly2Node37Box
    .k (31/8) (by rfl) (by rfl)
    component58_sound assembly2Node37_sound

private noncomputable def assembly2Node39Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (4), chiLo := (5/32), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem assembly2Node39_sound : Sound assembly2Node39Box :=
  sound_of_literal_split assembly2Node39Box component62Box component63Box
    .chi (11/64) (by rfl) (by rfl)
    component62_sound component63_sound

private noncomputable def assembly2Node40Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (4), chiLo := (5/32), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem assembly2Node40_sound : Sound assembly2Node40Box :=
  sound_of_literal_split assembly2Node40Box component61Box assembly2Node39Box
    .k (31/8) (by rfl) (by rfl)
    component61_sound assembly2Node39_sound

private noncomputable def assembly2Node41Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (4), chiLo := (1/8), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem assembly2Node41_sound : Sound assembly2Node41Box :=
  sound_of_literal_split assembly2Node41Box assembly2Node38Box assembly2Node40Box
    .chi (5/32) (by rfl) (by rfl)
    assembly2Node38_sound assembly2Node40_sound

private noncomputable def assembly2Node42Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (4), chiLo := (1/8), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem assembly2Node42_sound : Sound assembly2Node42Box :=
  sound_of_literal_split assembly2Node42Box assembly2Node36Box assembly2Node41Box
    .k (15/4) (by rfl) (by rfl)
    assembly2Node36_sound assembly2Node41_sound

private noncomputable def assembly2Node43Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (15/4), chiLo := (3/16), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem assembly2Node43_sound : Sound assembly2Node43Box :=
  sound_of_literal_split assembly2Node43Box component64Box component65Box
    .k (29/8) (by rfl) (by rfl)
    component64_sound component65_sound

private noncomputable def assembly2Node44Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (15/4), chiLo := (7/32), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem assembly2Node44_sound : Sound assembly2Node44Box :=
  sound_of_literal_split assembly2Node44Box component66Box component67Box
    .k (29/8) (by rfl) (by rfl)
    component66_sound component67_sound

private noncomputable def assembly2Node45Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (15/4), chiLo := (3/16), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem assembly2Node45_sound : Sound assembly2Node45Box :=
  sound_of_literal_split assembly2Node45Box assembly2Node43Box assembly2Node44Box
    .chi (7/32) (by rfl) (by rfl)
    assembly2Node43_sound assembly2Node44_sound

private noncomputable def assembly2Node46Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (4), chiLo := (3/16), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem assembly2Node46_sound : Sound assembly2Node46Box :=
  sound_of_literal_split assembly2Node46Box component69Box component70Box
    .chi (13/64) (by rfl) (by rfl)
    component69_sound component70_sound

private noncomputable def assembly2Node47Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (4), chiLo := (3/16), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem assembly2Node47_sound : Sound assembly2Node47Box :=
  sound_of_literal_split assembly2Node47Box component68Box assembly2Node46Box
    .k (31/8) (by rfl) (by rfl)
    component68_sound assembly2Node46_sound

private noncomputable def assembly2Node48Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (4), chiLo := (7/32), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem assembly2Node48_sound : Sound assembly2Node48Box :=
  sound_of_literal_split assembly2Node48Box component72Box component73Box
    .chi (15/64) (by rfl) (by rfl)
    component72_sound component73_sound

private noncomputable def assembly2Node49Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (4), chiLo := (7/32), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem assembly2Node49_sound : Sound assembly2Node49Box :=
  sound_of_literal_split assembly2Node49Box component71Box assembly2Node48Box
    .k (31/8) (by rfl) (by rfl)
    component71_sound assembly2Node48_sound

private noncomputable def assembly2Node50Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (4), chiLo := (3/16), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem assembly2Node50_sound : Sound assembly2Node50Box :=
  sound_of_literal_split assembly2Node50Box assembly2Node47Box assembly2Node49Box
    .chi (7/32) (by rfl) (by rfl)
    assembly2Node47_sound assembly2Node49_sound

private noncomputable def assembly2Node51Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (4), chiLo := (3/16), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem assembly2Node51_sound : Sound assembly2Node51Box :=
  sound_of_literal_split assembly2Node51Box assembly2Node45Box assembly2Node50Box
    .k (15/4) (by rfl) (by rfl)
    assembly2Node45_sound assembly2Node50_sound

private noncomputable def assembly2Node52Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (4), chiLo := (1/8), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem assembly2Node52_sound : Sound assembly2Node52Box :=
  sound_of_literal_split assembly2Node52Box assembly2Node42Box assembly2Node51Box
    .chi (3/16) (by rfl) (by rfl)
    assembly2Node42_sound assembly2Node51_sound

private noncomputable def assembly2Node53Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (4), chiLo := (1/8), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem assembly2Node53_sound : Sound assembly2Node53Box :=
  sound_of_literal_split assembly2Node53Box assembly2Node33Box assembly2Node52Box
    .k (7/2) (by rfl) (by rfl)
    assembly2Node33_sound assembly2Node52_sound

private noncomputable def assembly2Node54Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (4), chiLo := (0), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem assembly2Node54_sound : Sound assembly2Node54Box :=
  sound_of_literal_split assembly2Node54Box assembly2Node23Box assembly2Node53Box
    .chi (1/8) (by rfl) (by rfl)
    assembly2Node23_sound assembly2Node53_sound

noncomputable def assembly2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (4), chiLo := (0), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
theorem assembly2_sound : Sound assembly2Box :=
  sound_of_literal_split assembly2Box assembly2Node12Box assembly2Node54Box
    .k (3) (by rfl) (by rfl)
    assembly2Node12_sound assembly2Node54_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
