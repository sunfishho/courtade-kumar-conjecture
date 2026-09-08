import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Assembly000

namespace CourtadeKumar
namespace LRSmallSWideLogRoundedScalarV2

open LRSmallSBridgeCoreCertificate
open LRSmallSWideLogRoundedFlatTopology

noncomputable def root1FlatBox : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (1/2), kHi := (1), chiLo := (0), chiHi := (1) }

theorem root1Flat_sound : Sound root1FlatBox :=
  sound_of_box_eq (by rfl') assembly0_sound

theorem root1_sound :
    Sound (rootBox (1/2) (1)) :=
  sound_of_box_eq (by rfl') root1Flat_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
