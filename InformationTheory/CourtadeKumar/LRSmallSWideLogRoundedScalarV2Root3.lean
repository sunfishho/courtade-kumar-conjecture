import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Assembly002
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Assembly003
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Assembly004

namespace CourtadeKumar
namespace LRSmallSWideLogRoundedScalarV2

open LRSmallSBridgeCoreCertificate
open LRSmallSWideLogRoundedFlatTopology

private noncomputable def root3Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (4), chiLo := (0), chiHi := (1/2) }

set_option maxRecDepth 1000000 in
private theorem root3Node0_sound : Sound root3Node0Box :=
  sound_of_literal_split root3Node0Box assembly2Box assembly3Box
    .chi (1/4) (by rfl) (by rfl)
    assembly2_sound assembly3_sound

noncomputable def root3FlatBox : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (4), chiLo := (0), chiHi := (1) }

set_option maxRecDepth 1000000 in
theorem root3Flat_sound : Sound root3FlatBox :=
  sound_of_literal_split root3FlatBox root3Node0Box assembly4Box
    .chi (1/2) (by rfl) (by rfl)
    root3Node0_sound assembly4_sound

theorem root3_sound :
    Sound (rootBox (2) (4)) :=
  sound_of_box_eq (by rfl') root3Flat_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
