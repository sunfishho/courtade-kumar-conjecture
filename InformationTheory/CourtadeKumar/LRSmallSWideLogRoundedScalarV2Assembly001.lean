import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component003
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component004
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component005
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component006
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component007
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component008
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component009
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component010
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component011
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component012
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component013
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component014
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component015
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component016

namespace CourtadeKumar
namespace LRSmallSWideLogRoundedScalarV2

open LRSmallSBridgeCoreCertificate
open LRSmallSWideLogRoundedFlatTopology

private noncomputable def assembly1Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/2), kHi := (2), chiLo := (1/8), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem assembly1Node0_sound : Sound assembly1Node0Box :=
  sound_of_literal_split assembly1Node0Box component5Box component6Box
    .k (7/4) (by rfl) (by rfl)
    component5_sound component6_sound

private noncomputable def assembly1Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/2), kHi := (2), chiLo := (0), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem assembly1Node1_sound : Sound assembly1Node1Box :=
  sound_of_literal_split assembly1Node1Box component4Box assembly1Node0Box
    .chi (1/8) (by rfl) (by rfl)
    component4_sound assembly1Node0_sound

private noncomputable def assembly1Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (1), kHi := (2), chiLo := (0), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem assembly1Node2_sound : Sound assembly1Node2Box :=
  sound_of_literal_split assembly1Node2Box component3Box assembly1Node1Box
    .k (3/2) (by rfl) (by rfl)
    component3_sound assembly1Node1_sound

private noncomputable def assembly1Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (1), kHi := (3/2), chiLo := (1/4), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem assembly1Node3_sound : Sound assembly1Node3Box :=
  sound_of_literal_split assembly1Node3Box component7Box component8Box
    .k (5/4) (by rfl) (by rfl)
    component7_sound component8_sound

private noncomputable def assembly1Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/2), kHi := (2), chiLo := (1/4), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem assembly1Node4_sound : Sound assembly1Node4Box :=
  sound_of_literal_split assembly1Node4Box component9Box component10Box
    .k (7/4) (by rfl) (by rfl)
    component9_sound component10_sound

private noncomputable def assembly1Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/2), kHi := (2), chiLo := (1/4), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem assembly1Node5_sound : Sound assembly1Node5Box :=
  sound_of_literal_split assembly1Node5Box assembly1Node4Box component11Box
    .chi (3/8) (by rfl) (by rfl)
    assembly1Node4_sound component11_sound

private noncomputable def assembly1Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (1), kHi := (2), chiLo := (1/4), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem assembly1Node6_sound : Sound assembly1Node6Box :=
  sound_of_literal_split assembly1Node6Box assembly1Node3Box assembly1Node5Box
    .k (3/2) (by rfl) (by rfl)
    assembly1Node3_sound assembly1Node5_sound

private noncomputable def assembly1Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (1), kHi := (2), chiLo := (0), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem assembly1Node7_sound : Sound assembly1Node7Box :=
  sound_of_literal_split assembly1Node7Box assembly1Node2Box assembly1Node6Box
    .chi (1/4) (by rfl) (by rfl)
    assembly1Node2_sound assembly1Node6_sound

private noncomputable def assembly1Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (1), kHi := (3/2), chiLo := (1/2), chiHi := (1) }

set_option maxRecDepth 1000000 in
private theorem assembly1Node8_sound : Sound assembly1Node8Box :=
  sound_of_literal_split assembly1Node8Box component12Box component13Box
    .chi (3/4) (by rfl) (by rfl)
    component12_sound component13_sound

private noncomputable def assembly1Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/2), kHi := (2), chiLo := (1/2), chiHi := (3/4) }

set_option maxRecDepth 1000000 in
private theorem assembly1Node9_sound : Sound assembly1Node9Box :=
  sound_of_literal_split assembly1Node9Box component14Box component15Box
    .k (7/4) (by rfl) (by rfl)
    component14_sound component15_sound

private noncomputable def assembly1Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/2), kHi := (2), chiLo := (1/2), chiHi := (1) }

set_option maxRecDepth 1000000 in
private theorem assembly1Node10_sound : Sound assembly1Node10Box :=
  sound_of_literal_split assembly1Node10Box assembly1Node9Box component16Box
    .chi (3/4) (by rfl) (by rfl)
    assembly1Node9_sound component16_sound

private noncomputable def assembly1Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (1), kHi := (2), chiLo := (1/2), chiHi := (1) }

set_option maxRecDepth 1000000 in
private theorem assembly1Node11_sound : Sound assembly1Node11Box :=
  sound_of_literal_split assembly1Node11Box assembly1Node8Box assembly1Node10Box
    .k (3/2) (by rfl) (by rfl)
    assembly1Node8_sound assembly1Node10_sound

noncomputable def assembly1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (1), kHi := (2), chiLo := (0), chiHi := (1) }

set_option maxRecDepth 1000000 in
theorem assembly1_sound : Sound assembly1Box :=
  sound_of_literal_split assembly1Box assembly1Node7Box assembly1Node11Box
    .chi (1/2) (by rfl) (by rfl)
    assembly1Node7_sound assembly1Node11_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
