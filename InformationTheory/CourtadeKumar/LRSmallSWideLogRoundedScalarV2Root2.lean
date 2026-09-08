import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Assembly001

namespace CourtadeKumar
namespace LRSmallSWideLogRoundedScalarV2

open LRSmallSBridgeCoreCertificate
open LRSmallSWideLogRoundedFlatTopology

noncomputable def root2FlatBox : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (1), kHi := (2), chiLo := (0), chiHi := (1) }

theorem root2Flat_sound : Sound root2FlatBox :=
  sound_of_box_eq (by rfl') assembly1_sound

theorem root2_sound :
    Sound (rootBox (1) (2)) :=
  sound_of_box_eq (by rfl') root2Flat_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
