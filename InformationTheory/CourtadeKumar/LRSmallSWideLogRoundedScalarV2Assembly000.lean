import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component001
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Component002

namespace CourtadeKumar
namespace LRSmallSWideLogRoundedScalarV2

open LRSmallSBridgeCoreCertificate
open LRSmallSWideLogRoundedFlatTopology

noncomputable def assembly0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (1/2), kHi := (1), chiLo := (0), chiHi := (1) }

set_option maxRecDepth 1000000 in
theorem assembly0_sound : Sound assembly0Box :=
  sound_of_literal_split assembly0Box component1Box component2Box
    .chi (1/2) (by rfl) (by rfl)
    component1_sound component2_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
