import InformationTheory.CourtadeKumar.GeneratedLRCompactVLowR.Chunk000
import InformationTheory.CourtadeKumar.GeneratedLRCompactVLowR.Chunk001
import InformationTheory.CourtadeKumar.GeneratedLRCompactVLowR.Chunk002
import InformationTheory.CourtadeKumar.GeneratedLRCompactVLowR.Chunk003
import InformationTheory.CourtadeKumar.GeneratedLRCompactVLowR.Chunk004
import InformationTheory.CourtadeKumar.GeneratedLRCompactVLowR.Chunk005
import InformationTheory.CourtadeKumar.GeneratedLRCompactVLowR.Chunk006
import InformationTheory.CourtadeKumar.GeneratedLRCompactVLowR.Chunk007
import InformationTheory.CourtadeKumar.GeneratedLRCompactVLowR.Chunk008
import InformationTheory.CourtadeKumar.GeneratedLRCompactVLowR.Chunk009
import InformationTheory.CourtadeKumar.GeneratedLRCompactVLowR.Chunk010
import InformationTheory.CourtadeKumar.GeneratedLRCompactVLowR.Chunk011
import InformationTheory.CourtadeKumar.GeneratedLRCompactVLowR.Chunk012
import InformationTheory.CourtadeKumar.GeneratedLRCompactVLowR.Chunk013
import InformationTheory.CourtadeKumar.GeneratedLRCompactVLowR.Chunk014

/-! Frozen basic compact-V replay.
Plan SHA-256: ce3f7a498b2b9caf346dcf88ce7861f8cc091af8cd93f5624d7684e21322ecd5
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CourtadeKumar.GeneratedLRCompactVLowR

def rootBox : CertificateBox where
  sLo := (0 : ℚ)
  sHi := ((1 : ℚ) / 2)
  kLo := ((1 : ℚ) / 3)
  kHi := ((1 : ℚ) / 2)
  chiLo := ((17 : ℚ) / 20)
  chiHi := (1 : ℚ)


def box_rL : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 2), ((1 : ℚ) / 3), ((1 : ℚ) / 2), ((17 : ℚ) / 20), ((37 : ℚ) / 40)⟩


def box_rLL : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 4), ((1 : ℚ) / 3), ((1 : ℚ) / 2), ((17 : ℚ) / 20), ((37 : ℚ) / 40)⟩


def box_rLLL : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 4), ((1 : ℚ) / 3), ((1 : ℚ) / 2), ((17 : ℚ) / 20), ((71 : ℚ) / 80)⟩


def box_rLR : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((1 : ℚ) / 2), ((1 : ℚ) / 3), ((1 : ℚ) / 2), ((17 : ℚ) / 20), ((37 : ℚ) / 40)⟩


def box_rLRL : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((1 : ℚ) / 2), ((1 : ℚ) / 3), ((1 : ℚ) / 2), ((17 : ℚ) / 20), ((71 : ℚ) / 80)⟩


def box_rLRLR : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((1 : ℚ) / 2), ((1 : ℚ) / 3), ((1 : ℚ) / 2), ((17 : ℚ) / 20), ((71 : ℚ) / 80)⟩


def box_rLRR : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((1 : ℚ) / 2), ((1 : ℚ) / 3), ((1 : ℚ) / 2), ((71 : ℚ) / 80), ((37 : ℚ) / 40)⟩


def box_rLRRR : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((1 : ℚ) / 2), ((1 : ℚ) / 3), ((1 : ℚ) / 2), ((71 : ℚ) / 80), ((37 : ℚ) / 40)⟩


def box_rR : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 2), ((1 : ℚ) / 3), ((1 : ℚ) / 2), ((37 : ℚ) / 40), (1 : ℚ)⟩


def box_rRL : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 4), ((1 : ℚ) / 3), ((1 : ℚ) / 2), ((37 : ℚ) / 40), (1 : ℚ)⟩


def box_rRR : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((1 : ℚ) / 2), ((1 : ℚ) / 3), ((1 : ℚ) / 2), ((37 : ℚ) / 40), (1 : ℚ)⟩


def box_rRRL : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((1 : ℚ) / 2), ((1 : ℚ) / 3), ((1 : ℚ) / 2), ((37 : ℚ) / 40), ((77 : ℚ) / 80)⟩


def box_rRRR : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((1 : ℚ) / 2), ((1 : ℚ) / 3), ((1 : ℚ) / 2), ((77 : ℚ) / 80), (1 : ℚ)⟩


theorem target_nonnegative : LRCompactVBoxSound rootBox :=
  (LRCompactVBoxSound.join (box := rootBox) .chi ((37 : ℚ) / 40)
    (LRCompactVBoxSound.join (box := box_rL) .s ((1 : ℚ) / 4)
      (LRCompactVBoxSound.join (box := box_rLL) .chi ((71 : ℚ) / 80)
        (LRCompactVBoxSound.join (box := box_rLLL) .s ((1 : ℚ) / 8)
          sound0
          sound1)
        sound2)
      (LRCompactVBoxSound.join (box := box_rLR) .chi ((71 : ℚ) / 80)
        (LRCompactVBoxSound.join (box := box_rLRL) .s ((3 : ℚ) / 8)
          sound3
          (LRCompactVBoxSound.join (box := box_rLRLR) .k ((5 : ℚ) / 12)
            sound4
            sound5))
        (LRCompactVBoxSound.join (box := box_rLRR) .s ((3 : ℚ) / 8)
          sound6
          (LRCompactVBoxSound.join (box := box_rLRRR) .k ((5 : ℚ) / 12)
            sound7
            sound8))))
    (LRCompactVBoxSound.join (box := box_rR) .s ((1 : ℚ) / 4)
      (LRCompactVBoxSound.join (box := box_rRL) .chi ((77 : ℚ) / 80)
        sound9
        sound10)
      (LRCompactVBoxSound.join (box := box_rRR) .chi ((77 : ℚ) / 80)
        (LRCompactVBoxSound.join (box := box_rRRL) .s ((3 : ℚ) / 8)
          sound11
          sound12)
        (LRCompactVBoxSound.join (box := box_rRRR) .s ((3 : ℚ) / 8)
          sound13
          sound14))))

end CourtadeKumar.GeneratedLRCompactVLowR
