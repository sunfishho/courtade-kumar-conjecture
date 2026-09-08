import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Root0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Root1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Root2
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2Root3

namespace CourtadeKumar
namespace LRSmallSWideLogRoundedScalarV2

open LRSmallSBridgeCoreCertificate
open LRSmallSWideLogRoundedFlatTopology

theorem four_roots_sound {s k chi : Real}
    (hs : s ∈ Set.Icc (0 : Real) (1 / 16384))
    (hk : k ∈ Set.Icc (1 / 4 : Real) 4)
    (hchi : chi ∈ Set.Icc (0 : Real) 1) :
    (2 / 3 : Real) < lrSmallSBridgeCoreTarget ⟨s, k, chi⟩ := by
  by_cases hkHalf : k ≤ (1 / 2 : Real)
  · exact root0_sound ⟨s, k, chi⟩
      (rootBox_contains hs (by norm_num; exact ⟨hk.1, hkHalf⟩) hchi)
  by_cases hkOne : k ≤ (1 : Real)
  · exact root1_sound ⟨s, k, chi⟩
      (rootBox_contains hs (by norm_num; exact ⟨(not_le.mp hkHalf).le, hkOne⟩) hchi)
  by_cases hkTwo : k ≤ (2 : Real)
  · exact root2_sound ⟨s, k, chi⟩
      (rootBox_contains hs (by norm_num; exact ⟨(not_le.mp hkOne).le, hkTwo⟩) hchi)
  · exact root3_sound ⟨s, k, chi⟩
      (rootBox_contains hs (by norm_num; exact ⟨(not_le.mp hkTwo).le, hk.2⟩) hchi)

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
