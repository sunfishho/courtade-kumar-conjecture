import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component123
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component124
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component125
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component126
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component127
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component128
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component129
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component130
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component131
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component132
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component133
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component134
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component135
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component136
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component137
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component138
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component139
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component140
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component141
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component142
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component143
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component144
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component145
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component146
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component147

namespace CourtadeKumar
namespace LRSmallSWideLogRoundedScalarV2

open LRSmallSBridgeCoreCertificate
open LRSmallSWideLogRoundedFlatTopology

private noncomputable def assembly4Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (5/2), chiLo := (1/2), chiHi := (5/8) }

set_option maxRecDepth 1000000 in
private theorem assembly4Node0_sound : Sound assembly4Node0Box :=
  sound_of_literal_split assembly4Node0Box component123Box component124Box
    .k (9/4) (by rfl) (by rfl)
    component123_sound component124_sound

private noncomputable def assembly4Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (5/2), chiLo := (1/2), chiHi := (3/4) }

set_option maxRecDepth 1000000 in
private theorem assembly4Node1_sound : Sound assembly4Node1Box :=
  sound_of_literal_split assembly4Node1Box assembly4Node0Box component125Box
    .chi (5/8) (by rfl) (by rfl)
    assembly4Node0_sound component125_sound

private noncomputable def assembly4Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (3), chiLo := (1/2), chiHi := (5/8) }

set_option maxRecDepth 1000000 in
private theorem assembly4Node2_sound : Sound assembly4Node2Box :=
  sound_of_literal_split assembly4Node2Box component126Box component127Box
    .k (11/4) (by rfl) (by rfl)
    component126_sound component127_sound

private noncomputable def assembly4Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (3), chiLo := (1/2), chiHi := (3/4) }

set_option maxRecDepth 1000000 in
private theorem assembly4Node3_sound : Sound assembly4Node3Box :=
  sound_of_literal_split assembly4Node3Box assembly4Node2Box component128Box
    .chi (5/8) (by rfl) (by rfl)
    assembly4Node2_sound component128_sound

private noncomputable def assembly4Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (3), chiLo := (1/2), chiHi := (3/4) }

set_option maxRecDepth 1000000 in
private theorem assembly4Node4_sound : Sound assembly4Node4Box :=
  sound_of_literal_split assembly4Node4Box assembly4Node1Box assembly4Node3Box
    .k (5/2) (by rfl) (by rfl)
    assembly4Node1_sound assembly4Node3_sound

private noncomputable def assembly4Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (3), chiLo := (3/4), chiHi := (1) }

set_option maxRecDepth 1000000 in
private theorem assembly4Node5_sound : Sound assembly4Node5Box :=
  sound_of_literal_split assembly4Node5Box component130Box component131Box
    .chi (7/8) (by rfl) (by rfl)
    component130_sound component131_sound

private noncomputable def assembly4Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (3), chiLo := (3/4), chiHi := (1) }

set_option maxRecDepth 1000000 in
private theorem assembly4Node6_sound : Sound assembly4Node6Box :=
  sound_of_literal_split assembly4Node6Box component129Box assembly4Node5Box
    .k (5/2) (by rfl) (by rfl)
    component129_sound assembly4Node5_sound

private noncomputable def assembly4Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (3), chiLo := (1/2), chiHi := (1) }

set_option maxRecDepth 1000000 in
private theorem assembly4Node7_sound : Sound assembly4Node7Box :=
  sound_of_literal_split assembly4Node7Box assembly4Node4Box assembly4Node6Box
    .chi (3/4) (by rfl) (by rfl)
    assembly4Node4_sound assembly4Node6_sound

private noncomputable def assembly4Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (13/4), chiLo := (1/2), chiHi := (5/8) }

set_option maxRecDepth 1000000 in
private theorem assembly4Node8_sound : Sound assembly4Node8Box :=
  sound_of_literal_split assembly4Node8Box component132Box component133Box
    .chi (9/16) (by rfl) (by rfl)
    component132_sound component133_sound

private noncomputable def assembly4Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (7/2), chiLo := (1/2), chiHi := (5/8) }

set_option maxRecDepth 1000000 in
private theorem assembly4Node9_sound : Sound assembly4Node9Box :=
  sound_of_literal_split assembly4Node9Box component134Box component135Box
    .chi (9/16) (by rfl) (by rfl)
    component134_sound component135_sound

private noncomputable def assembly4Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (7/2), chiLo := (1/2), chiHi := (5/8) }

set_option maxRecDepth 1000000 in
private theorem assembly4Node10_sound : Sound assembly4Node10Box :=
  sound_of_literal_split assembly4Node10Box assembly4Node8Box assembly4Node9Box
    .k (13/4) (by rfl) (by rfl)
    assembly4Node8_sound assembly4Node9_sound

private noncomputable def assembly4Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (7/2), chiLo := (5/8), chiHi := (3/4) }

set_option maxRecDepth 1000000 in
private theorem assembly4Node11_sound : Sound assembly4Node11Box :=
  sound_of_literal_split assembly4Node11Box component136Box component137Box
    .k (13/4) (by rfl) (by rfl)
    component136_sound component137_sound

private noncomputable def assembly4Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (7/2), chiLo := (1/2), chiHi := (3/4) }

set_option maxRecDepth 1000000 in
private theorem assembly4Node12_sound : Sound assembly4Node12Box :=
  sound_of_literal_split assembly4Node12Box assembly4Node10Box assembly4Node11Box
    .chi (5/8) (by rfl) (by rfl)
    assembly4Node10_sound assembly4Node11_sound

private noncomputable def assembly4Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (15/4), chiLo := (1/2), chiHi := (5/8) }

set_option maxRecDepth 1000000 in
private theorem assembly4Node13_sound : Sound assembly4Node13Box :=
  sound_of_literal_split assembly4Node13Box component138Box component139Box
    .chi (9/16) (by rfl) (by rfl)
    component138_sound component139_sound

private noncomputable def assembly4Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (4), chiLo := (1/2), chiHi := (5/8) }

set_option maxRecDepth 1000000 in
private theorem assembly4Node14_sound : Sound assembly4Node14Box :=
  sound_of_literal_split assembly4Node14Box component140Box component141Box
    .chi (9/16) (by rfl) (by rfl)
    component140_sound component141_sound

private noncomputable def assembly4Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (4), chiLo := (1/2), chiHi := (5/8) }

set_option maxRecDepth 1000000 in
private theorem assembly4Node15_sound : Sound assembly4Node15Box :=
  sound_of_literal_split assembly4Node15Box assembly4Node13Box assembly4Node14Box
    .k (15/4) (by rfl) (by rfl)
    assembly4Node13_sound assembly4Node14_sound

private noncomputable def assembly4Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (4), chiLo := (5/8), chiHi := (3/4) }

set_option maxRecDepth 1000000 in
private theorem assembly4Node16_sound : Sound assembly4Node16Box :=
  sound_of_literal_split assembly4Node16Box component142Box component143Box
    .k (15/4) (by rfl) (by rfl)
    component142_sound component143_sound

private noncomputable def assembly4Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (4), chiLo := (1/2), chiHi := (3/4) }

set_option maxRecDepth 1000000 in
private theorem assembly4Node17_sound : Sound assembly4Node17Box :=
  sound_of_literal_split assembly4Node17Box assembly4Node15Box assembly4Node16Box
    .chi (5/8) (by rfl) (by rfl)
    assembly4Node15_sound assembly4Node16_sound

private noncomputable def assembly4Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (4), chiLo := (1/2), chiHi := (3/4) }

set_option maxRecDepth 1000000 in
private theorem assembly4Node18_sound : Sound assembly4Node18Box :=
  sound_of_literal_split assembly4Node18Box assembly4Node12Box assembly4Node17Box
    .k (7/2) (by rfl) (by rfl)
    assembly4Node12_sound assembly4Node17_sound

private noncomputable def assembly4Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (7/2), chiLo := (3/4), chiHi := (1) }

set_option maxRecDepth 1000000 in
private theorem assembly4Node19_sound : Sound assembly4Node19Box :=
  sound_of_literal_split assembly4Node19Box component144Box component145Box
    .chi (7/8) (by rfl) (by rfl)
    component144_sound component145_sound

private noncomputable def assembly4Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (4), chiLo := (3/4), chiHi := (1) }

set_option maxRecDepth 1000000 in
private theorem assembly4Node20_sound : Sound assembly4Node20Box :=
  sound_of_literal_split assembly4Node20Box component146Box component147Box
    .chi (7/8) (by rfl) (by rfl)
    component146_sound component147_sound

private noncomputable def assembly4Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (4), chiLo := (3/4), chiHi := (1) }

set_option maxRecDepth 1000000 in
private theorem assembly4Node21_sound : Sound assembly4Node21Box :=
  sound_of_literal_split assembly4Node21Box assembly4Node19Box assembly4Node20Box
    .k (7/2) (by rfl) (by rfl)
    assembly4Node19_sound assembly4Node20_sound

private noncomputable def assembly4Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (4), chiLo := (1/2), chiHi := (1) }

set_option maxRecDepth 1000000 in
private theorem assembly4Node22_sound : Sound assembly4Node22Box :=
  sound_of_literal_split assembly4Node22Box assembly4Node18Box assembly4Node21Box
    .chi (3/4) (by rfl) (by rfl)
    assembly4Node18_sound assembly4Node21_sound

noncomputable def assembly4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (4), chiLo := (1/2), chiHi := (1) }

set_option maxRecDepth 1000000 in
theorem assembly4_sound : Sound assembly4Box :=
  sound_of_literal_split assembly4Box assembly4Node7Box assembly4Node22Box
    .k (3) (by rfl) (by rfl)
    assembly4Node7_sound assembly4Node22_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
