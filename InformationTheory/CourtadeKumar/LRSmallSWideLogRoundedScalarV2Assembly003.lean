import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component074
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component075
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component076
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component077
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component078
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component079
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component080
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component081
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component082
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component083
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component084
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component085
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component086
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component087
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component088
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component089
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component090
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component091
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component092
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component093
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component094
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component095
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component096
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component097
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component098
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component099
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component100
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component101
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component102
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component103
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component104
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component105
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component106
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component107
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component108
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component109
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component110
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component111
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component112
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component113
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component114
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component115
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component116
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component117
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component118
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component119
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component120
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component121
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component122

namespace CourtadeKumar
namespace LRSmallSWideLogRoundedScalarV2

open LRSmallSBridgeCoreCertificate
open LRSmallSWideLogRoundedFlatTopology

private noncomputable def assembly3Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (5/2), chiLo := (1/4), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem assembly3Node0_sound : Sound assembly3Node0Box :=
  sound_of_literal_split assembly3Node0Box component75Box component76Box
    .chi (5/16) (by rfl) (by rfl)
    component75_sound component76_sound

private noncomputable def assembly3Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (5/2), chiLo := (1/4), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem assembly3Node1_sound : Sound assembly3Node1Box :=
  sound_of_literal_split assembly3Node1Box component74Box assembly3Node0Box
    .k (9/4) (by rfl) (by rfl)
    component74_sound assembly3Node0_sound

private noncomputable def assembly3Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (5/2), chiLo := (3/8), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem assembly3Node2_sound : Sound assembly3Node2Box :=
  sound_of_literal_split assembly3Node2Box component77Box component78Box
    .k (9/4) (by rfl) (by rfl)
    component77_sound component78_sound

private noncomputable def assembly3Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (5/2), chiLo := (1/4), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem assembly3Node3_sound : Sound assembly3Node3Box :=
  sound_of_literal_split assembly3Node3Box assembly3Node1Box assembly3Node2Box
    .chi (3/8) (by rfl) (by rfl)
    assembly3Node1_sound assembly3Node2_sound

private noncomputable def assembly3Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (11/4), chiLo := (1/4), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem assembly3Node4_sound : Sound assembly3Node4Box :=
  sound_of_literal_split assembly3Node4Box component79Box component80Box
    .chi (5/16) (by rfl) (by rfl)
    component79_sound component80_sound

private noncomputable def assembly3Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (3), chiLo := (1/4), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem assembly3Node5_sound : Sound assembly3Node5Box :=
  sound_of_literal_split assembly3Node5Box component81Box component82Box
    .k (23/8) (by rfl) (by rfl)
    component81_sound component82_sound

private noncomputable def assembly3Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (3), chiLo := (1/4), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem assembly3Node6_sound : Sound assembly3Node6Box :=
  sound_of_literal_split assembly3Node6Box assembly3Node5Box component83Box
    .chi (5/16) (by rfl) (by rfl)
    assembly3Node5_sound component83_sound

private noncomputable def assembly3Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (3), chiLo := (1/4), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem assembly3Node7_sound : Sound assembly3Node7Box :=
  sound_of_literal_split assembly3Node7Box assembly3Node4Box assembly3Node6Box
    .k (11/4) (by rfl) (by rfl)
    assembly3Node4_sound assembly3Node6_sound

private noncomputable def assembly3Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (11/4), chiLo := (3/8), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem assembly3Node8_sound : Sound assembly3Node8Box :=
  sound_of_literal_split assembly3Node8Box component84Box component85Box
    .chi (7/16) (by rfl) (by rfl)
    component84_sound component85_sound

private noncomputable def assembly3Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (3), chiLo := (3/8), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem assembly3Node9_sound : Sound assembly3Node9Box :=
  sound_of_literal_split assembly3Node9Box component86Box component87Box
    .chi (7/16) (by rfl) (by rfl)
    component86_sound component87_sound

private noncomputable def assembly3Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (3), chiLo := (3/8), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem assembly3Node10_sound : Sound assembly3Node10Box :=
  sound_of_literal_split assembly3Node10Box assembly3Node8Box assembly3Node9Box
    .k (11/4) (by rfl) (by rfl)
    assembly3Node8_sound assembly3Node9_sound

private noncomputable def assembly3Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (3), chiLo := (1/4), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem assembly3Node11_sound : Sound assembly3Node11Box :=
  sound_of_literal_split assembly3Node11Box assembly3Node7Box assembly3Node10Box
    .chi (3/8) (by rfl) (by rfl)
    assembly3Node7_sound assembly3Node10_sound

private noncomputable def assembly3Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (3), chiLo := (1/4), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem assembly3Node12_sound : Sound assembly3Node12Box :=
  sound_of_literal_split assembly3Node12Box assembly3Node3Box assembly3Node11Box
    .k (5/2) (by rfl) (by rfl)
    assembly3Node3_sound assembly3Node11_sound

private noncomputable def assembly3Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (13/4), chiLo := (1/4), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem assembly3Node13_sound : Sound assembly3Node13Box :=
  sound_of_literal_split assembly3Node13Box component88Box component89Box
    .chi (9/32) (by rfl) (by rfl)
    component88_sound component89_sound

private noncomputable def assembly3Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (7/2), chiLo := (1/4), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem assembly3Node14_sound : Sound assembly3Node14Box :=
  sound_of_literal_split assembly3Node14Box component90Box component91Box
    .k (27/8) (by rfl) (by rfl)
    component90_sound component91_sound

private noncomputable def assembly3Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (7/2), chiLo := (9/32), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem assembly3Node15_sound : Sound assembly3Node15Box :=
  sound_of_literal_split assembly3Node15Box component92Box component93Box
    .k (27/8) (by rfl) (by rfl)
    component92_sound component93_sound

private noncomputable def assembly3Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (7/2), chiLo := (1/4), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem assembly3Node16_sound : Sound assembly3Node16Box :=
  sound_of_literal_split assembly3Node16Box assembly3Node14Box assembly3Node15Box
    .chi (9/32) (by rfl) (by rfl)
    assembly3Node14_sound assembly3Node15_sound

private noncomputable def assembly3Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (7/2), chiLo := (1/4), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem assembly3Node17_sound : Sound assembly3Node17Box :=
  sound_of_literal_split assembly3Node17Box assembly3Node13Box assembly3Node16Box
    .k (13/4) (by rfl) (by rfl)
    assembly3Node13_sound assembly3Node16_sound

private noncomputable def assembly3Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (13/4), chiLo := (5/16), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem assembly3Node18_sound : Sound assembly3Node18Box :=
  sound_of_literal_split assembly3Node18Box component94Box component95Box
    .chi (11/32) (by rfl) (by rfl)
    component94_sound component95_sound

private noncomputable def assembly3Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (7/2), chiLo := (5/16), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem assembly3Node19_sound : Sound assembly3Node19Box :=
  sound_of_literal_split assembly3Node19Box component96Box component97Box
    .chi (11/32) (by rfl) (by rfl)
    component96_sound component97_sound

private noncomputable def assembly3Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (7/2), chiLo := (5/16), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem assembly3Node20_sound : Sound assembly3Node20Box :=
  sound_of_literal_split assembly3Node20Box assembly3Node18Box assembly3Node19Box
    .k (13/4) (by rfl) (by rfl)
    assembly3Node18_sound assembly3Node19_sound

private noncomputable def assembly3Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (7/2), chiLo := (1/4), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem assembly3Node21_sound : Sound assembly3Node21Box :=
  sound_of_literal_split assembly3Node21Box assembly3Node17Box assembly3Node20Box
    .chi (5/16) (by rfl) (by rfl)
    assembly3Node17_sound assembly3Node20_sound

private noncomputable def assembly3Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (15/4), chiLo := (1/4), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem assembly3Node22_sound : Sound assembly3Node22Box :=
  sound_of_literal_split assembly3Node22Box component98Box component99Box
    .k (29/8) (by rfl) (by rfl)
    component98_sound component99_sound

private noncomputable def assembly3Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (15/4), chiLo := (9/32), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem assembly3Node23_sound : Sound assembly3Node23Box :=
  sound_of_literal_split assembly3Node23Box component100Box component101Box
    .k (29/8) (by rfl) (by rfl)
    component100_sound component101_sound

private noncomputable def assembly3Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (15/4), chiLo := (1/4), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem assembly3Node24_sound : Sound assembly3Node24Box :=
  sound_of_literal_split assembly3Node24Box assembly3Node22Box assembly3Node23Box
    .chi (9/32) (by rfl) (by rfl)
    assembly3Node22_sound assembly3Node23_sound

private noncomputable def assembly3Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (4), chiLo := (1/4), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem assembly3Node25_sound : Sound assembly3Node25Box :=
  sound_of_literal_split assembly3Node25Box component102Box component103Box
    .k (31/8) (by rfl) (by rfl)
    component102_sound component103_sound

private noncomputable def assembly3Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (4), chiLo := (9/32), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem assembly3Node26_sound : Sound assembly3Node26Box :=
  sound_of_literal_split assembly3Node26Box component104Box component105Box
    .k (31/8) (by rfl) (by rfl)
    component104_sound component105_sound

private noncomputable def assembly3Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (4), chiLo := (1/4), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem assembly3Node27_sound : Sound assembly3Node27Box :=
  sound_of_literal_split assembly3Node27Box assembly3Node25Box assembly3Node26Box
    .chi (9/32) (by rfl) (by rfl)
    assembly3Node25_sound assembly3Node26_sound

private noncomputable def assembly3Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (4), chiLo := (1/4), chiHi := (5/16) }

set_option maxRecDepth 1000000 in
private theorem assembly3Node28_sound : Sound assembly3Node28Box :=
  sound_of_literal_split assembly3Node28Box assembly3Node24Box assembly3Node27Box
    .k (15/4) (by rfl) (by rfl)
    assembly3Node24_sound assembly3Node27_sound

private noncomputable def assembly3Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (15/4), chiLo := (5/16), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem assembly3Node29_sound : Sound assembly3Node29Box :=
  sound_of_literal_split assembly3Node29Box component106Box component107Box
    .k (29/8) (by rfl) (by rfl)
    component106_sound component107_sound

private noncomputable def assembly3Node30Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (15/4), chiLo := (5/16), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem assembly3Node30_sound : Sound assembly3Node30Box :=
  sound_of_literal_split assembly3Node30Box assembly3Node29Box component108Box
    .chi (11/32) (by rfl) (by rfl)
    assembly3Node29_sound component108_sound

private noncomputable def assembly3Node31Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (4), chiLo := (5/16), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem assembly3Node31_sound : Sound assembly3Node31Box :=
  sound_of_literal_split assembly3Node31Box component109Box component110Box
    .k (31/8) (by rfl) (by rfl)
    component109_sound component110_sound

private noncomputable def assembly3Node32Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (4), chiLo := (11/32), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem assembly3Node32_sound : Sound assembly3Node32Box :=
  sound_of_literal_split assembly3Node32Box component111Box component112Box
    .k (31/8) (by rfl) (by rfl)
    component111_sound component112_sound

private noncomputable def assembly3Node33Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (4), chiLo := (5/16), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem assembly3Node33_sound : Sound assembly3Node33Box :=
  sound_of_literal_split assembly3Node33Box assembly3Node31Box assembly3Node32Box
    .chi (11/32) (by rfl) (by rfl)
    assembly3Node31_sound assembly3Node32_sound

private noncomputable def assembly3Node34Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (4), chiLo := (5/16), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem assembly3Node34_sound : Sound assembly3Node34Box :=
  sound_of_literal_split assembly3Node34Box assembly3Node30Box assembly3Node33Box
    .k (15/4) (by rfl) (by rfl)
    assembly3Node30_sound assembly3Node33_sound

private noncomputable def assembly3Node35Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (4), chiLo := (1/4), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem assembly3Node35_sound : Sound assembly3Node35Box :=
  sound_of_literal_split assembly3Node35Box assembly3Node28Box assembly3Node34Box
    .chi (5/16) (by rfl) (by rfl)
    assembly3Node28_sound assembly3Node34_sound

private noncomputable def assembly3Node36Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (4), chiLo := (1/4), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem assembly3Node36_sound : Sound assembly3Node36Box :=
  sound_of_literal_split assembly3Node36Box assembly3Node21Box assembly3Node35Box
    .k (7/2) (by rfl) (by rfl)
    assembly3Node21_sound assembly3Node35_sound

private noncomputable def assembly3Node37Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (13/4), chiLo := (3/8), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem assembly3Node37_sound : Sound assembly3Node37Box :=
  sound_of_literal_split assembly3Node37Box component113Box component114Box
    .chi (7/16) (by rfl) (by rfl)
    component113_sound component114_sound

private noncomputable def assembly3Node38Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (7/2), chiLo := (3/8), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem assembly3Node38_sound : Sound assembly3Node38Box :=
  sound_of_literal_split assembly3Node38Box component115Box component116Box
    .chi (7/16) (by rfl) (by rfl)
    component115_sound component116_sound

private noncomputable def assembly3Node39Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (7/2), chiLo := (3/8), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem assembly3Node39_sound : Sound assembly3Node39Box :=
  sound_of_literal_split assembly3Node39Box assembly3Node37Box assembly3Node38Box
    .k (13/4) (by rfl) (by rfl)
    assembly3Node37_sound assembly3Node38_sound

private noncomputable def assembly3Node40Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (15/4), chiLo := (3/8), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem assembly3Node40_sound : Sound assembly3Node40Box :=
  sound_of_literal_split assembly3Node40Box component117Box component118Box
    .chi (13/32) (by rfl) (by rfl)
    component117_sound component118_sound

private noncomputable def assembly3Node41Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (4), chiLo := (3/8), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem assembly3Node41_sound : Sound assembly3Node41Box :=
  sound_of_literal_split assembly3Node41Box component119Box component120Box
    .chi (13/32) (by rfl) (by rfl)
    component119_sound component120_sound

private noncomputable def assembly3Node42Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (4), chiLo := (3/8), chiHi := (7/16) }

set_option maxRecDepth 1000000 in
private theorem assembly3Node42_sound : Sound assembly3Node42Box :=
  sound_of_literal_split assembly3Node42Box assembly3Node40Box assembly3Node41Box
    .k (15/4) (by rfl) (by rfl)
    assembly3Node40_sound assembly3Node41_sound

private noncomputable def assembly3Node43Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (4), chiLo := (7/16), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem assembly3Node43_sound : Sound assembly3Node43Box :=
  sound_of_literal_split assembly3Node43Box component121Box component122Box
    .k (15/4) (by rfl) (by rfl)
    component121_sound component122_sound

private noncomputable def assembly3Node44Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (4), chiLo := (3/8), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem assembly3Node44_sound : Sound assembly3Node44Box :=
  sound_of_literal_split assembly3Node44Box assembly3Node42Box assembly3Node43Box
    .chi (7/16) (by rfl) (by rfl)
    assembly3Node42_sound assembly3Node43_sound

private noncomputable def assembly3Node45Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (4), chiLo := (3/8), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem assembly3Node45_sound : Sound assembly3Node45Box :=
  sound_of_literal_split assembly3Node45Box assembly3Node39Box assembly3Node44Box
    .k (7/2) (by rfl) (by rfl)
    assembly3Node39_sound assembly3Node44_sound

private noncomputable def assembly3Node46Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (4), chiLo := (1/4), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem assembly3Node46_sound : Sound assembly3Node46Box :=
  sound_of_literal_split assembly3Node46Box assembly3Node36Box assembly3Node45Box
    .chi (3/8) (by rfl) (by rfl)
    assembly3Node36_sound assembly3Node45_sound

noncomputable def assembly3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (4), chiLo := (1/4), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
theorem assembly3_sound : Sound assembly3Box :=
  sound_of_literal_split assembly3Box assembly3Node12Box assembly3Node46Box
    .k (3) (by rfl) (by rfl)
    assembly3Node12_sound assembly3Node46_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
