import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component000

namespace CourtadeKumar
namespace LRSmallSWideLogRoundedScalarV2

open LRSmallSBridgeCoreCertificate
open LRSmallSWideLogRoundedFlatTopology

noncomputable def root0FlatBox : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (1/4), kHi := (1/2), chiLo := (0), chiHi := (1) }

theorem root0Flat_sound : Sound root0FlatBox :=
  sound_of_box_eq (by rfl') component0_sound

theorem root0_sound :
    Sound (rootBox (1/4) (1/2)) :=
  sound_of_box_eq (by rfl') root0Flat_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
