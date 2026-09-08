import InformationTheory.CourtadeKumar.LRCompactVBasicReplay

/-! Frozen basic compact-V replay.
Plan SHA-256: ce3f7a498b2b9caf346dcf88ce7861f8cc091af8cd93f5624d7684e21322ecd5
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CourtadeKumar.GeneratedLRCompactVLowR

-- 127 accepted leaves below path rRRLR.
def box12 : CertificateBox where
  sLo := ((3 : ℚ) / 8)
  sHi := ((1 : ℚ) / 2)
  kLo := ((1 : ℚ) / 3)
  kHi := ((1 : ℚ) / 2)
  chiLo := ((37 : ℚ) / 40)
  chiHi := ((77 : ℚ) / 80)


def subbox12_0 : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((1 : ℚ) / 3), ((17 : ℚ) / 48), ((37 : ℚ) / 40), ((299 : ℚ) / 320)⟩

theorem checked12_0 :
    LRCompactVLeafParameters.check subbox12_0 .short = true := by decide +kernel

theorem subsound12_0 : LRCompactVBoxSound subbox12_0 :=
  LRCompactVLeafParameters.sound checked12_0


def subbox12_1 : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((17 : ℚ) / 48), ((3 : ℚ) / 8), ((37 : ℚ) / 40), ((299 : ℚ) / 320)⟩

theorem checked12_1 :
    LRCompactVLeafParameters.check subbox12_1 .short = true := by decide +kernel

theorem subsound12_1 : LRCompactVBoxSound subbox12_1 :=
  LRCompactVLeafParameters.sound checked12_1


def subbox12_2 : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((1 : ℚ) / 3), ((17 : ℚ) / 48), ((37 : ℚ) / 40), ((299 : ℚ) / 320)⟩

theorem checked12_2 :
    LRCompactVLeafParameters.check subbox12_2 .short = true := by decide +kernel

theorem subsound12_2 : LRCompactVBoxSound subbox12_2 :=
  LRCompactVLeafParameters.sound checked12_2


def subbox12_3 : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((17 : ℚ) / 48), ((3 : ℚ) / 8), ((37 : ℚ) / 40), ((299 : ℚ) / 320)⟩

theorem checked12_3 :
    LRCompactVLeafParameters.check subbox12_3 .short = true := by decide +kernel

theorem subsound12_3 : LRCompactVBoxSound subbox12_3 :=
  LRCompactVLeafParameters.sound checked12_3


def subbox12_4 : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((1 : ℚ) / 3), ((17 : ℚ) / 48), ((299 : ℚ) / 320), ((151 : ℚ) / 160)⟩

theorem checked12_4 :
    LRCompactVLeafParameters.check subbox12_4 .short = true := by decide +kernel

theorem subsound12_4 : LRCompactVBoxSound subbox12_4 :=
  LRCompactVLeafParameters.sound checked12_4


def subbox12_5 : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((17 : ℚ) / 48), ((3 : ℚ) / 8), ((299 : ℚ) / 320), ((151 : ℚ) / 160)⟩

theorem checked12_5 :
    LRCompactVLeafParameters.check subbox12_5 .short = true := by decide +kernel

theorem subsound12_5 : LRCompactVBoxSound subbox12_5 :=
  LRCompactVLeafParameters.sound checked12_5


def subbox12_6 : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((1 : ℚ) / 3), ((17 : ℚ) / 48), ((299 : ℚ) / 320), ((151 : ℚ) / 160)⟩

theorem checked12_6 :
    LRCompactVLeafParameters.check subbox12_6 .short = true := by decide +kernel

theorem subsound12_6 : LRCompactVBoxSound subbox12_6 :=
  LRCompactVLeafParameters.sound checked12_6


def subbox12_7 : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((17 : ℚ) / 48), ((3 : ℚ) / 8), ((299 : ℚ) / 320), ((151 : ℚ) / 160)⟩

theorem checked12_7 :
    LRCompactVLeafParameters.check subbox12_7 .short = true := by decide +kernel

theorem subsound12_7 : LRCompactVBoxSound subbox12_7 :=
  LRCompactVLeafParameters.sound checked12_7


def subbox12_8 : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((3 : ℚ) / 8), ((19 : ℚ) / 48), ((37 : ℚ) / 40), ((299 : ℚ) / 320)⟩

theorem checked12_8 :
    LRCompactVLeafParameters.check subbox12_8 .short = true := by decide +kernel

theorem subsound12_8 : LRCompactVBoxSound subbox12_8 :=
  LRCompactVLeafParameters.sound checked12_8


def subbox12_9 : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((19 : ℚ) / 48), ((5 : ℚ) / 12), ((37 : ℚ) / 40), ((299 : ℚ) / 320)⟩

theorem checked12_9 :
    LRCompactVLeafParameters.check subbox12_9 .short = true := by decide +kernel

theorem subsound12_9 : LRCompactVBoxSound subbox12_9 :=
  LRCompactVLeafParameters.sound checked12_9


def subbox12_10 : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((3 : ℚ) / 8), ((19 : ℚ) / 48), ((37 : ℚ) / 40), ((299 : ℚ) / 320)⟩

theorem checked12_10 :
    LRCompactVLeafParameters.check subbox12_10 .short = true := by decide +kernel

theorem subsound12_10 : LRCompactVBoxSound subbox12_10 :=
  LRCompactVLeafParameters.sound checked12_10


def subbox12_11 : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((19 : ℚ) / 48), ((5 : ℚ) / 12), ((37 : ℚ) / 40), ((299 : ℚ) / 320)⟩

theorem checked12_11 :
    LRCompactVLeafParameters.check subbox12_11 .short = true := by decide +kernel

theorem subsound12_11 : LRCompactVBoxSound subbox12_11 :=
  LRCompactVLeafParameters.sound checked12_11


def subbox12_12 : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((3 : ℚ) / 8), ((19 : ℚ) / 48), ((299 : ℚ) / 320), ((151 : ℚ) / 160)⟩

theorem checked12_12 :
    LRCompactVLeafParameters.check subbox12_12 .short = true := by decide +kernel

theorem subsound12_12 : LRCompactVBoxSound subbox12_12 :=
  LRCompactVLeafParameters.sound checked12_12


def subbox12_13 : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((19 : ℚ) / 48), ((5 : ℚ) / 12), ((299 : ℚ) / 320), ((151 : ℚ) / 160)⟩

theorem checked12_13 :
    LRCompactVLeafParameters.check subbox12_13 .short = true := by decide +kernel

theorem subsound12_13 : LRCompactVBoxSound subbox12_13 :=
  LRCompactVLeafParameters.sound checked12_13


def subbox12_14 : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((3 : ℚ) / 8), ((19 : ℚ) / 48), ((299 : ℚ) / 320), ((151 : ℚ) / 160)⟩

theorem checked12_14 :
    LRCompactVLeafParameters.check subbox12_14 .short = true := by decide +kernel

theorem subsound12_14 : LRCompactVBoxSound subbox12_14 :=
  LRCompactVLeafParameters.sound checked12_14


def subbox12_15 : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((19 : ℚ) / 48), ((5 : ℚ) / 12), ((299 : ℚ) / 320), ((151 : ℚ) / 160)⟩

theorem checked12_15 :
    LRCompactVLeafParameters.check subbox12_15 .short = true := by decide +kernel

theorem subsound12_15 : LRCompactVBoxSound subbox12_15 :=
  LRCompactVLeafParameters.sound checked12_15


def subbox12_16 : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((1 : ℚ) / 3), ((17 : ℚ) / 48), ((37 : ℚ) / 40), ((299 : ℚ) / 320)⟩

theorem checked12_16 :
    LRCompactVLeafParameters.check subbox12_16 .short = true := by decide +kernel

theorem subsound12_16 : LRCompactVBoxSound subbox12_16 :=
  LRCompactVLeafParameters.sound checked12_16


def subbox12_17 : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((17 : ℚ) / 48), ((3 : ℚ) / 8), ((37 : ℚ) / 40), ((299 : ℚ) / 320)⟩

theorem checked12_17 :
    LRCompactVLeafParameters.check subbox12_17 .short = true := by decide +kernel

theorem subsound12_17 : LRCompactVBoxSound subbox12_17 :=
  LRCompactVLeafParameters.sound checked12_17


def subbox12_18 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((1 : ℚ) / 3), ((17 : ℚ) / 48), ((37 : ℚ) / 40), ((299 : ℚ) / 320)⟩

theorem checked12_18 :
    LRCompactVLeafParameters.check subbox12_18 .short = true := by decide +kernel

theorem subsound12_18 : LRCompactVBoxSound subbox12_18 :=
  LRCompactVLeafParameters.sound checked12_18


def subbox12_19 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((17 : ℚ) / 48), ((3 : ℚ) / 8), ((37 : ℚ) / 40), ((299 : ℚ) / 320)⟩

theorem checked12_19 :
    LRCompactVLeafParameters.check subbox12_19 .accurateLog = true := by decide +kernel

theorem subsound12_19 : LRCompactVBoxSound subbox12_19 :=
  LRCompactVLeafParameters.sound checked12_19


def subbox12_20 : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((1 : ℚ) / 3), ((17 : ℚ) / 48), ((299 : ℚ) / 320), ((151 : ℚ) / 160)⟩

theorem checked12_20 :
    LRCompactVLeafParameters.check subbox12_20 .short = true := by decide +kernel

theorem subsound12_20 : LRCompactVBoxSound subbox12_20 :=
  LRCompactVLeafParameters.sound checked12_20


def subbox12_21 : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((17 : ℚ) / 48), ((3 : ℚ) / 8), ((299 : ℚ) / 320), ((151 : ℚ) / 160)⟩

theorem checked12_21 :
    LRCompactVLeafParameters.check subbox12_21 .short = true := by decide +kernel

theorem subsound12_21 : LRCompactVBoxSound subbox12_21 :=
  LRCompactVLeafParameters.sound checked12_21


def subbox12_22 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((1 : ℚ) / 3), ((17 : ℚ) / 48), ((299 : ℚ) / 320), ((151 : ℚ) / 160)⟩

theorem checked12_22 :
    LRCompactVLeafParameters.check subbox12_22 .short = true := by decide +kernel

theorem subsound12_22 : LRCompactVBoxSound subbox12_22 :=
  LRCompactVLeafParameters.sound checked12_22


def subbox12_23 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((17 : ℚ) / 48), ((3 : ℚ) / 8), ((299 : ℚ) / 320), ((151 : ℚ) / 160)⟩

theorem checked12_23 :
    LRCompactVLeafParameters.check subbox12_23 .short = true := by decide +kernel

theorem subsound12_23 : LRCompactVBoxSound subbox12_23 :=
  LRCompactVLeafParameters.sound checked12_23


def subbox12_24 : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((3 : ℚ) / 8), ((19 : ℚ) / 48), ((37 : ℚ) / 40), ((299 : ℚ) / 320)⟩

theorem checked12_24 :
    LRCompactVLeafParameters.check subbox12_24 .short = true := by decide +kernel

theorem subsound12_24 : LRCompactVBoxSound subbox12_24 :=
  LRCompactVLeafParameters.sound checked12_24


def subbox12_25 : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((19 : ℚ) / 48), ((5 : ℚ) / 12), ((37 : ℚ) / 40), ((299 : ℚ) / 320)⟩

theorem checked12_25 :
    LRCompactVLeafParameters.check subbox12_25 .short = true := by decide +kernel

theorem subsound12_25 : LRCompactVBoxSound subbox12_25 :=
  LRCompactVLeafParameters.sound checked12_25


def subbox12_26 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((3 : ℚ) / 8), ((19 : ℚ) / 48), ((37 : ℚ) / 40), ((299 : ℚ) / 320)⟩

theorem checked12_26 :
    LRCompactVLeafParameters.check subbox12_26 .long = true := by decide +kernel

theorem subsound12_26 : LRCompactVBoxSound subbox12_26 :=
  LRCompactVLeafParameters.sound checked12_26


def subbox12_27 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((19 : ℚ) / 48), ((5 : ℚ) / 12), ((37 : ℚ) / 40), ((299 : ℚ) / 320)⟩

theorem checked12_27 :
    LRCompactVLeafParameters.check subbox12_27 .long = true := by decide +kernel

theorem subsound12_27 : LRCompactVBoxSound subbox12_27 :=
  LRCompactVLeafParameters.sound checked12_27


def subbox12_28 : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((3 : ℚ) / 8), ((19 : ℚ) / 48), ((299 : ℚ) / 320), ((151 : ℚ) / 160)⟩

theorem checked12_28 :
    LRCompactVLeafParameters.check subbox12_28 .short = true := by decide +kernel

theorem subsound12_28 : LRCompactVBoxSound subbox12_28 :=
  LRCompactVLeafParameters.sound checked12_28


def subbox12_29 : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((19 : ℚ) / 48), ((5 : ℚ) / 12), ((299 : ℚ) / 320), ((151 : ℚ) / 160)⟩

theorem checked12_29 :
    LRCompactVLeafParameters.check subbox12_29 .short = true := by decide +kernel

theorem subsound12_29 : LRCompactVBoxSound subbox12_29 :=
  LRCompactVLeafParameters.sound checked12_29


def subbox12_30 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((3 : ℚ) / 8), ((19 : ℚ) / 48), ((299 : ℚ) / 320), ((151 : ℚ) / 160)⟩

theorem checked12_30 :
    LRCompactVLeafParameters.check subbox12_30 .long = true := by decide +kernel

theorem subsound12_30 : LRCompactVBoxSound subbox12_30 :=
  LRCompactVLeafParameters.sound checked12_30


def subbox12_31 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((19 : ℚ) / 48), ((5 : ℚ) / 12), ((299 : ℚ) / 320), ((151 : ℚ) / 160)⟩

theorem checked12_31 :
    LRCompactVLeafParameters.check subbox12_31 .long = true := by decide +kernel

theorem subsound12_31 : LRCompactVBoxSound subbox12_31 :=
  LRCompactVLeafParameters.sound checked12_31


def subbox12_32 : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((151 : ℚ) / 160), ((61 : ℚ) / 64)⟩

theorem checked12_32 :
    LRCompactVLeafParameters.check subbox12_32 .long = true := by decide +kernel

theorem subsound12_32 : LRCompactVBoxSound subbox12_32 :=
  LRCompactVLeafParameters.sound checked12_32


def subbox12_33 : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((1 : ℚ) / 3), ((17 : ℚ) / 48), ((151 : ℚ) / 160), ((61 : ℚ) / 64)⟩

theorem checked12_33 :
    LRCompactVLeafParameters.check subbox12_33 .short = true := by decide +kernel

theorem subsound12_33 : LRCompactVBoxSound subbox12_33 :=
  LRCompactVLeafParameters.sound checked12_33


def subbox12_34 : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((17 : ℚ) / 48), ((3 : ℚ) / 8), ((151 : ℚ) / 160), ((61 : ℚ) / 64)⟩

theorem checked12_34 :
    LRCompactVLeafParameters.check subbox12_34 .short = true := by decide +kernel

theorem subsound12_34 : LRCompactVBoxSound subbox12_34 :=
  LRCompactVLeafParameters.sound checked12_34


def subbox12_35 : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((61 : ℚ) / 64), ((77 : ℚ) / 80)⟩

theorem checked12_35 :
    LRCompactVLeafParameters.check subbox12_35 .long = true := by decide +kernel

theorem subsound12_35 : LRCompactVBoxSound subbox12_35 :=
  LRCompactVLeafParameters.sound checked12_35


def subbox12_36 : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((1 : ℚ) / 3), ((17 : ℚ) / 48), ((61 : ℚ) / 64), ((77 : ℚ) / 80)⟩

theorem checked12_36 :
    LRCompactVLeafParameters.check subbox12_36 .short = true := by decide +kernel

theorem subsound12_36 : LRCompactVBoxSound subbox12_36 :=
  LRCompactVLeafParameters.sound checked12_36


def subbox12_37 : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((17 : ℚ) / 48), ((3 : ℚ) / 8), ((61 : ℚ) / 64), ((77 : ℚ) / 80)⟩

theorem checked12_37 :
    LRCompactVLeafParameters.check subbox12_37 .short = true := by decide +kernel

theorem subsound12_37 : LRCompactVBoxSound subbox12_37 :=
  LRCompactVLeafParameters.sound checked12_37


def subbox12_38 : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((3 : ℚ) / 8), ((19 : ℚ) / 48), ((151 : ℚ) / 160), ((61 : ℚ) / 64)⟩

theorem checked12_38 :
    LRCompactVLeafParameters.check subbox12_38 .short = true := by decide +kernel

theorem subsound12_38 : LRCompactVBoxSound subbox12_38 :=
  LRCompactVLeafParameters.sound checked12_38


def subbox12_39 : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((19 : ℚ) / 48), ((5 : ℚ) / 12), ((151 : ℚ) / 160), ((61 : ℚ) / 64)⟩

theorem checked12_39 :
    LRCompactVLeafParameters.check subbox12_39 .short = true := by decide +kernel

theorem subsound12_39 : LRCompactVBoxSound subbox12_39 :=
  LRCompactVLeafParameters.sound checked12_39


def subbox12_40 : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((3 : ℚ) / 8), ((19 : ℚ) / 48), ((151 : ℚ) / 160), ((61 : ℚ) / 64)⟩

theorem checked12_40 :
    LRCompactVLeafParameters.check subbox12_40 .short = true := by decide +kernel

theorem subsound12_40 : LRCompactVBoxSound subbox12_40 :=
  LRCompactVLeafParameters.sound checked12_40


def subbox12_41 : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((19 : ℚ) / 48), ((5 : ℚ) / 12), ((151 : ℚ) / 160), ((61 : ℚ) / 64)⟩

theorem checked12_41 :
    LRCompactVLeafParameters.check subbox12_41 .short = true := by decide +kernel

theorem subsound12_41 : LRCompactVBoxSound subbox12_41 :=
  LRCompactVLeafParameters.sound checked12_41


def subbox12_42 : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((3 : ℚ) / 8), ((19 : ℚ) / 48), ((61 : ℚ) / 64), ((77 : ℚ) / 80)⟩

theorem checked12_42 :
    LRCompactVLeafParameters.check subbox12_42 .short = true := by decide +kernel

theorem subsound12_42 : LRCompactVBoxSound subbox12_42 :=
  LRCompactVLeafParameters.sound checked12_42


def subbox12_43 : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((19 : ℚ) / 48), ((5 : ℚ) / 12), ((61 : ℚ) / 64), ((77 : ℚ) / 80)⟩

theorem checked12_43 :
    LRCompactVLeafParameters.check subbox12_43 .short = true := by decide +kernel

theorem subsound12_43 : LRCompactVBoxSound subbox12_43 :=
  LRCompactVLeafParameters.sound checked12_43


def subbox12_44 : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((3 : ℚ) / 8), ((19 : ℚ) / 48), ((61 : ℚ) / 64), ((77 : ℚ) / 80)⟩

theorem checked12_44 :
    LRCompactVLeafParameters.check subbox12_44 .short = true := by decide +kernel

theorem subsound12_44 : LRCompactVBoxSound subbox12_44 :=
  LRCompactVLeafParameters.sound checked12_44


def subbox12_45 : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((19 : ℚ) / 48), ((5 : ℚ) / 12), ((61 : ℚ) / 64), ((77 : ℚ) / 80)⟩

theorem checked12_45 :
    LRCompactVLeafParameters.check subbox12_45 .short = true := by decide +kernel

theorem subsound12_45 : LRCompactVBoxSound subbox12_45 :=
  LRCompactVLeafParameters.sound checked12_45


def subbox12_46 : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((1 : ℚ) / 3), ((17 : ℚ) / 48), ((151 : ℚ) / 160), ((61 : ℚ) / 64)⟩

theorem checked12_46 :
    LRCompactVLeafParameters.check subbox12_46 .short = true := by decide +kernel

theorem subsound12_46 : LRCompactVBoxSound subbox12_46 :=
  LRCompactVLeafParameters.sound checked12_46


def subbox12_47 : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((17 : ℚ) / 48), ((3 : ℚ) / 8), ((151 : ℚ) / 160), ((61 : ℚ) / 64)⟩

theorem checked12_47 :
    LRCompactVLeafParameters.check subbox12_47 .short = true := by decide +kernel

theorem subsound12_47 : LRCompactVBoxSound subbox12_47 :=
  LRCompactVLeafParameters.sound checked12_47


def subbox12_48 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((1 : ℚ) / 3), ((17 : ℚ) / 48), ((151 : ℚ) / 160), ((61 : ℚ) / 64)⟩

theorem checked12_48 :
    LRCompactVLeafParameters.check subbox12_48 .short = true := by decide +kernel

theorem subsound12_48 : LRCompactVBoxSound subbox12_48 :=
  LRCompactVLeafParameters.sound checked12_48


def subbox12_49 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((17 : ℚ) / 48), ((3 : ℚ) / 8), ((151 : ℚ) / 160), ((61 : ℚ) / 64)⟩

theorem checked12_49 :
    LRCompactVLeafParameters.check subbox12_49 .short = true := by decide +kernel

theorem subsound12_49 : LRCompactVBoxSound subbox12_49 :=
  LRCompactVLeafParameters.sound checked12_49


def subbox12_50 : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((1 : ℚ) / 3), ((17 : ℚ) / 48), ((61 : ℚ) / 64), ((77 : ℚ) / 80)⟩

theorem checked12_50 :
    LRCompactVLeafParameters.check subbox12_50 .short = true := by decide +kernel

theorem subsound12_50 : LRCompactVBoxSound subbox12_50 :=
  LRCompactVLeafParameters.sound checked12_50


def subbox12_51 : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((17 : ℚ) / 48), ((3 : ℚ) / 8), ((61 : ℚ) / 64), ((77 : ℚ) / 80)⟩

theorem checked12_51 :
    LRCompactVLeafParameters.check subbox12_51 .short = true := by decide +kernel

theorem subsound12_51 : LRCompactVBoxSound subbox12_51 :=
  LRCompactVLeafParameters.sound checked12_51


def subbox12_52 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((1 : ℚ) / 3), ((17 : ℚ) / 48), ((61 : ℚ) / 64), ((77 : ℚ) / 80)⟩

theorem checked12_52 :
    LRCompactVLeafParameters.check subbox12_52 .short = true := by decide +kernel

theorem subsound12_52 : LRCompactVBoxSound subbox12_52 :=
  LRCompactVLeafParameters.sound checked12_52


def subbox12_53 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((17 : ℚ) / 48), ((3 : ℚ) / 8), ((61 : ℚ) / 64), ((77 : ℚ) / 80)⟩

theorem checked12_53 :
    LRCompactVLeafParameters.check subbox12_53 .short = true := by decide +kernel

theorem subsound12_53 : LRCompactVBoxSound subbox12_53 :=
  LRCompactVLeafParameters.sound checked12_53


def subbox12_54 : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((3 : ℚ) / 8), ((19 : ℚ) / 48), ((151 : ℚ) / 160), ((61 : ℚ) / 64)⟩

theorem checked12_54 :
    LRCompactVLeafParameters.check subbox12_54 .short = true := by decide +kernel

theorem subsound12_54 : LRCompactVBoxSound subbox12_54 :=
  LRCompactVLeafParameters.sound checked12_54


def subbox12_55 : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((19 : ℚ) / 48), ((5 : ℚ) / 12), ((151 : ℚ) / 160), ((61 : ℚ) / 64)⟩

theorem checked12_55 :
    LRCompactVLeafParameters.check subbox12_55 .short = true := by decide +kernel

theorem subsound12_55 : LRCompactVBoxSound subbox12_55 :=
  LRCompactVLeafParameters.sound checked12_55


def subbox12_56 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((3 : ℚ) / 8), ((19 : ℚ) / 48), ((151 : ℚ) / 160), ((61 : ℚ) / 64)⟩

theorem checked12_56 :
    LRCompactVLeafParameters.check subbox12_56 .short = true := by decide +kernel

theorem subsound12_56 : LRCompactVBoxSound subbox12_56 :=
  LRCompactVLeafParameters.sound checked12_56


def subbox12_57 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((19 : ℚ) / 48), ((5 : ℚ) / 12), ((151 : ℚ) / 160), ((61 : ℚ) / 64)⟩

theorem checked12_57 :
    LRCompactVLeafParameters.check subbox12_57 .long = true := by decide +kernel

theorem subsound12_57 : LRCompactVBoxSound subbox12_57 :=
  LRCompactVLeafParameters.sound checked12_57


def subbox12_58 : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((3 : ℚ) / 8), ((19 : ℚ) / 48), ((61 : ℚ) / 64), ((77 : ℚ) / 80)⟩

theorem checked12_58 :
    LRCompactVLeafParameters.check subbox12_58 .short = true := by decide +kernel

theorem subsound12_58 : LRCompactVBoxSound subbox12_58 :=
  LRCompactVLeafParameters.sound checked12_58


def subbox12_59 : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((19 : ℚ) / 48), ((5 : ℚ) / 12), ((61 : ℚ) / 64), ((77 : ℚ) / 80)⟩

theorem checked12_59 :
    LRCompactVLeafParameters.check subbox12_59 .short = true := by decide +kernel

theorem subsound12_59 : LRCompactVBoxSound subbox12_59 :=
  LRCompactVLeafParameters.sound checked12_59


def subbox12_60 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((3 : ℚ) / 8), ((19 : ℚ) / 48), ((61 : ℚ) / 64), ((77 : ℚ) / 80)⟩

theorem checked12_60 :
    LRCompactVLeafParameters.check subbox12_60 .short = true := by decide +kernel

theorem subsound12_60 : LRCompactVBoxSound subbox12_60 :=
  LRCompactVLeafParameters.sound checked12_60


def subbox12_61 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((19 : ℚ) / 48), ((5 : ℚ) / 12), ((61 : ℚ) / 64), ((77 : ℚ) / 80)⟩

theorem checked12_61 :
    LRCompactVLeafParameters.check subbox12_61 .long = true := by decide +kernel

theorem subsound12_61 : LRCompactVBoxSound subbox12_61 :=
  LRCompactVLeafParameters.sound checked12_61


def subbox12_62 : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((5 : ℚ) / 12), ((7 : ℚ) / 16), ((37 : ℚ) / 40), ((299 : ℚ) / 320)⟩

theorem checked12_62 :
    LRCompactVLeafParameters.check subbox12_62 .short = true := by decide +kernel

theorem subsound12_62 : LRCompactVBoxSound subbox12_62 :=
  LRCompactVLeafParameters.sound checked12_62


def subbox12_63 : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((37 : ℚ) / 40), ((299 : ℚ) / 320)⟩

theorem checked12_63 :
    LRCompactVLeafParameters.check subbox12_63 .short = true := by decide +kernel

theorem subsound12_63 : LRCompactVBoxSound subbox12_63 :=
  LRCompactVLeafParameters.sound checked12_63


def subbox12_64 : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((5 : ℚ) / 12), ((7 : ℚ) / 16), ((37 : ℚ) / 40), ((299 : ℚ) / 320)⟩

theorem checked12_64 :
    LRCompactVLeafParameters.check subbox12_64 .short = true := by decide +kernel

theorem subsound12_64 : LRCompactVBoxSound subbox12_64 :=
  LRCompactVLeafParameters.sound checked12_64


def subbox12_65 : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((37 : ℚ) / 40), ((299 : ℚ) / 320)⟩

theorem checked12_65 :
    LRCompactVLeafParameters.check subbox12_65 .short = true := by decide +kernel

theorem subsound12_65 : LRCompactVBoxSound subbox12_65 :=
  LRCompactVLeafParameters.sound checked12_65


def subbox12_66 : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((5 : ℚ) / 12), ((7 : ℚ) / 16), ((299 : ℚ) / 320), ((151 : ℚ) / 160)⟩

theorem checked12_66 :
    LRCompactVLeafParameters.check subbox12_66 .short = true := by decide +kernel

theorem subsound12_66 : LRCompactVBoxSound subbox12_66 :=
  LRCompactVLeafParameters.sound checked12_66


def subbox12_67 : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((299 : ℚ) / 320), ((151 : ℚ) / 160)⟩

theorem checked12_67 :
    LRCompactVLeafParameters.check subbox12_67 .short = true := by decide +kernel

theorem subsound12_67 : LRCompactVBoxSound subbox12_67 :=
  LRCompactVLeafParameters.sound checked12_67


def subbox12_68 : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((5 : ℚ) / 12), ((7 : ℚ) / 16), ((299 : ℚ) / 320), ((151 : ℚ) / 160)⟩

theorem checked12_68 :
    LRCompactVLeafParameters.check subbox12_68 .short = true := by decide +kernel

theorem subsound12_68 : LRCompactVBoxSound subbox12_68 :=
  LRCompactVLeafParameters.sound checked12_68


def subbox12_69 : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((299 : ℚ) / 320), ((151 : ℚ) / 160)⟩

theorem checked12_69 :
    LRCompactVLeafParameters.check subbox12_69 .short = true := by decide +kernel

theorem subsound12_69 : LRCompactVBoxSound subbox12_69 :=
  LRCompactVLeafParameters.sound checked12_69


def subbox12_70 : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((37 : ℚ) / 40), ((299 : ℚ) / 320)⟩

theorem checked12_70 :
    LRCompactVLeafParameters.check subbox12_70 .short = true := by decide +kernel

theorem subsound12_70 : LRCompactVBoxSound subbox12_70 :=
  LRCompactVLeafParameters.sound checked12_70


def subbox12_71 : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((37 : ℚ) / 40), ((299 : ℚ) / 320)⟩

theorem checked12_71 :
    LRCompactVLeafParameters.check subbox12_71 .short = true := by decide +kernel

theorem subsound12_71 : LRCompactVBoxSound subbox12_71 :=
  LRCompactVLeafParameters.sound checked12_71


def subbox12_72 : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((37 : ℚ) / 40), ((299 : ℚ) / 320)⟩

theorem checked12_72 :
    LRCompactVLeafParameters.check subbox12_72 .short = true := by decide +kernel

theorem subsound12_72 : LRCompactVBoxSound subbox12_72 :=
  LRCompactVLeafParameters.sound checked12_72


def subbox12_73 : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((37 : ℚ) / 40), ((299 : ℚ) / 320)⟩

theorem checked12_73 :
    LRCompactVLeafParameters.check subbox12_73 .short = true := by decide +kernel

theorem subsound12_73 : LRCompactVBoxSound subbox12_73 :=
  LRCompactVLeafParameters.sound checked12_73


def subbox12_74 : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((299 : ℚ) / 320), ((151 : ℚ) / 160)⟩

theorem checked12_74 :
    LRCompactVLeafParameters.check subbox12_74 .short = true := by decide +kernel

theorem subsound12_74 : LRCompactVBoxSound subbox12_74 :=
  LRCompactVLeafParameters.sound checked12_74


def subbox12_75 : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((299 : ℚ) / 320), ((151 : ℚ) / 160)⟩

theorem checked12_75 :
    LRCompactVLeafParameters.check subbox12_75 .short = true := by decide +kernel

theorem subsound12_75 : LRCompactVBoxSound subbox12_75 :=
  LRCompactVLeafParameters.sound checked12_75


def subbox12_76 : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((299 : ℚ) / 320), ((151 : ℚ) / 160)⟩

theorem checked12_76 :
    LRCompactVLeafParameters.check subbox12_76 .short = true := by decide +kernel

theorem subsound12_76 : LRCompactVBoxSound subbox12_76 :=
  LRCompactVLeafParameters.sound checked12_76


def subbox12_77 : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((299 : ℚ) / 320), ((151 : ℚ) / 160)⟩

theorem checked12_77 :
    LRCompactVLeafParameters.check subbox12_77 .short = true := by decide +kernel

theorem subsound12_77 : LRCompactVBoxSound subbox12_77 :=
  LRCompactVLeafParameters.sound checked12_77


def subbox12_78 : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((5 : ℚ) / 12), ((7 : ℚ) / 16), ((37 : ℚ) / 40), ((299 : ℚ) / 320)⟩

theorem checked12_78 :
    LRCompactVLeafParameters.check subbox12_78 .short = true := by decide +kernel

theorem subsound12_78 : LRCompactVBoxSound subbox12_78 :=
  LRCompactVLeafParameters.sound checked12_78


def subbox12_79 : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((37 : ℚ) / 40), ((299 : ℚ) / 320)⟩

theorem checked12_79 :
    LRCompactVLeafParameters.check subbox12_79 .long = true := by decide +kernel

theorem subsound12_79 : LRCompactVBoxSound subbox12_79 :=
  LRCompactVLeafParameters.sound checked12_79


def subbox12_80 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((5 : ℚ) / 12), ((7 : ℚ) / 16), ((37 : ℚ) / 40), ((299 : ℚ) / 320)⟩

theorem checked12_80 :
    LRCompactVLeafParameters.check subbox12_80 .long = true := by decide +kernel

theorem subsound12_80 : LRCompactVBoxSound subbox12_80 :=
  LRCompactVLeafParameters.sound checked12_80


def subbox12_81 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((37 : ℚ) / 40), ((299 : ℚ) / 320)⟩

theorem checked12_81 :
    LRCompactVLeafParameters.check subbox12_81 .long = true := by decide +kernel

theorem subsound12_81 : LRCompactVBoxSound subbox12_81 :=
  LRCompactVLeafParameters.sound checked12_81


def subbox12_82 : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((5 : ℚ) / 12), ((7 : ℚ) / 16), ((299 : ℚ) / 320), ((151 : ℚ) / 160)⟩

theorem checked12_82 :
    LRCompactVLeafParameters.check subbox12_82 .short = true := by decide +kernel

theorem subsound12_82 : LRCompactVBoxSound subbox12_82 :=
  LRCompactVLeafParameters.sound checked12_82


def subbox12_83 : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((299 : ℚ) / 320), ((151 : ℚ) / 160)⟩

theorem checked12_83 :
    LRCompactVLeafParameters.check subbox12_83 .long = true := by decide +kernel

theorem subsound12_83 : LRCompactVBoxSound subbox12_83 :=
  LRCompactVLeafParameters.sound checked12_83


def subbox12_84 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((5 : ℚ) / 12), ((7 : ℚ) / 16), ((299 : ℚ) / 320), ((151 : ℚ) / 160)⟩

theorem checked12_84 :
    LRCompactVLeafParameters.check subbox12_84 .long = true := by decide +kernel

theorem subsound12_84 : LRCompactVBoxSound subbox12_84 :=
  LRCompactVLeafParameters.sound checked12_84


def subbox12_85 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((299 : ℚ) / 320), ((151 : ℚ) / 160)⟩

theorem checked12_85 :
    LRCompactVLeafParameters.check subbox12_85 .long = true := by decide +kernel

theorem subsound12_85 : LRCompactVBoxSound subbox12_85 :=
  LRCompactVLeafParameters.sound checked12_85


def subbox12_86 : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((37 : ℚ) / 40), ((299 : ℚ) / 320)⟩

theorem checked12_86 :
    LRCompactVLeafParameters.check subbox12_86 .long = true := by decide +kernel

theorem subsound12_86 : LRCompactVBoxSound subbox12_86 :=
  LRCompactVLeafParameters.sound checked12_86


def subbox12_87 : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((37 : ℚ) / 40), ((299 : ℚ) / 320)⟩

theorem checked12_87 :
    LRCompactVLeafParameters.check subbox12_87 .long = true := by decide +kernel

theorem subsound12_87 : LRCompactVBoxSound subbox12_87 :=
  LRCompactVLeafParameters.sound checked12_87


def subbox12_88 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((37 : ℚ) / 40), ((299 : ℚ) / 320)⟩

theorem checked12_88 :
    LRCompactVLeafParameters.check subbox12_88 .long = true := by decide +kernel

theorem subsound12_88 : LRCompactVBoxSound subbox12_88 :=
  LRCompactVLeafParameters.sound checked12_88


def subbox12_89 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((37 : ℚ) / 40), ((119 : ℚ) / 128)⟩

theorem checked12_89 :
    LRCompactVLeafParameters.check subbox12_89 .long = true := by decide +kernel

theorem subsound12_89 : LRCompactVBoxSound subbox12_89 :=
  LRCompactVLeafParameters.sound checked12_89


def subbox12_90 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((119 : ℚ) / 128), ((299 : ℚ) / 320)⟩

theorem checked12_90 :
    LRCompactVLeafParameters.check subbox12_90 .long = true := by decide +kernel

theorem subsound12_90 : LRCompactVBoxSound subbox12_90 :=
  LRCompactVLeafParameters.sound checked12_90


def subbox12_91 : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((299 : ℚ) / 320), ((151 : ℚ) / 160)⟩

theorem checked12_91 :
    LRCompactVLeafParameters.check subbox12_91 .long = true := by decide +kernel

theorem subsound12_91 : LRCompactVBoxSound subbox12_91 :=
  LRCompactVLeafParameters.sound checked12_91


def subbox12_92 : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((299 : ℚ) / 320), ((151 : ℚ) / 160)⟩

theorem checked12_92 :
    LRCompactVLeafParameters.check subbox12_92 .long = true := by decide +kernel

theorem subsound12_92 : LRCompactVBoxSound subbox12_92 :=
  LRCompactVLeafParameters.sound checked12_92


def subbox12_93 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((299 : ℚ) / 320), ((151 : ℚ) / 160)⟩

theorem checked12_93 :
    LRCompactVLeafParameters.check subbox12_93 .long = true := by decide +kernel

theorem subsound12_93 : LRCompactVBoxSound subbox12_93 :=
  LRCompactVLeafParameters.sound checked12_93


def subbox12_94 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((299 : ℚ) / 320), ((151 : ℚ) / 160)⟩

theorem checked12_94 :
    LRCompactVLeafParameters.check subbox12_94 .long = true := by decide +kernel

theorem subsound12_94 : LRCompactVBoxSound subbox12_94 :=
  LRCompactVLeafParameters.sound checked12_94


def subbox12_95 : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((5 : ℚ) / 12), ((7 : ℚ) / 16), ((151 : ℚ) / 160), ((61 : ℚ) / 64)⟩

theorem checked12_95 :
    LRCompactVLeafParameters.check subbox12_95 .short = true := by decide +kernel

theorem subsound12_95 : LRCompactVBoxSound subbox12_95 :=
  LRCompactVLeafParameters.sound checked12_95


def subbox12_96 : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((151 : ℚ) / 160), ((61 : ℚ) / 64)⟩

theorem checked12_96 :
    LRCompactVLeafParameters.check subbox12_96 .short = true := by decide +kernel

theorem subsound12_96 : LRCompactVBoxSound subbox12_96 :=
  LRCompactVLeafParameters.sound checked12_96


def subbox12_97 : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((5 : ℚ) / 12), ((7 : ℚ) / 16), ((151 : ℚ) / 160), ((61 : ℚ) / 64)⟩

theorem checked12_97 :
    LRCompactVLeafParameters.check subbox12_97 .short = true := by decide +kernel

theorem subsound12_97 : LRCompactVBoxSound subbox12_97 :=
  LRCompactVLeafParameters.sound checked12_97


def subbox12_98 : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((151 : ℚ) / 160), ((61 : ℚ) / 64)⟩

theorem checked12_98 :
    LRCompactVLeafParameters.check subbox12_98 .short = true := by decide +kernel

theorem subsound12_98 : LRCompactVBoxSound subbox12_98 :=
  LRCompactVLeafParameters.sound checked12_98


def subbox12_99 : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((5 : ℚ) / 12), ((7 : ℚ) / 16), ((61 : ℚ) / 64), ((77 : ℚ) / 80)⟩

theorem checked12_99 :
    LRCompactVLeafParameters.check subbox12_99 .short = true := by decide +kernel

theorem subsound12_99 : LRCompactVBoxSound subbox12_99 :=
  LRCompactVLeafParameters.sound checked12_99


def subbox12_100 : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((61 : ℚ) / 64), ((77 : ℚ) / 80)⟩

theorem checked12_100 :
    LRCompactVLeafParameters.check subbox12_100 .short = true := by decide +kernel

theorem subsound12_100 : LRCompactVBoxSound subbox12_100 :=
  LRCompactVLeafParameters.sound checked12_100


def subbox12_101 : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((5 : ℚ) / 12), ((7 : ℚ) / 16), ((61 : ℚ) / 64), ((77 : ℚ) / 80)⟩

theorem checked12_101 :
    LRCompactVLeafParameters.check subbox12_101 .short = true := by decide +kernel

theorem subsound12_101 : LRCompactVBoxSound subbox12_101 :=
  LRCompactVLeafParameters.sound checked12_101


def subbox12_102 : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((61 : ℚ) / 64), ((77 : ℚ) / 80)⟩

theorem checked12_102 :
    LRCompactVLeafParameters.check subbox12_102 .short = true := by decide +kernel

theorem subsound12_102 : LRCompactVBoxSound subbox12_102 :=
  LRCompactVLeafParameters.sound checked12_102


def subbox12_103 : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((151 : ℚ) / 160), ((61 : ℚ) / 64)⟩

theorem checked12_103 :
    LRCompactVLeafParameters.check subbox12_103 .short = true := by decide +kernel

theorem subsound12_103 : LRCompactVBoxSound subbox12_103 :=
  LRCompactVLeafParameters.sound checked12_103


def subbox12_104 : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((151 : ℚ) / 160), ((61 : ℚ) / 64)⟩

theorem checked12_104 :
    LRCompactVLeafParameters.check subbox12_104 .short = true := by decide +kernel

theorem subsound12_104 : LRCompactVBoxSound subbox12_104 :=
  LRCompactVLeafParameters.sound checked12_104


def subbox12_105 : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((151 : ℚ) / 160), ((61 : ℚ) / 64)⟩

theorem checked12_105 :
    LRCompactVLeafParameters.check subbox12_105 .short = true := by decide +kernel

theorem subsound12_105 : LRCompactVBoxSound subbox12_105 :=
  LRCompactVLeafParameters.sound checked12_105


def subbox12_106 : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((151 : ℚ) / 160), ((61 : ℚ) / 64)⟩

theorem checked12_106 :
    LRCompactVLeafParameters.check subbox12_106 .short = true := by decide +kernel

theorem subsound12_106 : LRCompactVBoxSound subbox12_106 :=
  LRCompactVLeafParameters.sound checked12_106


def subbox12_107 : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((61 : ℚ) / 64), ((77 : ℚ) / 80)⟩

theorem checked12_107 :
    LRCompactVLeafParameters.check subbox12_107 .short = true := by decide +kernel

theorem subsound12_107 : LRCompactVBoxSound subbox12_107 :=
  LRCompactVLeafParameters.sound checked12_107


def subbox12_108 : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((61 : ℚ) / 64), ((77 : ℚ) / 80)⟩

theorem checked12_108 :
    LRCompactVLeafParameters.check subbox12_108 .short = true := by decide +kernel

theorem subsound12_108 : LRCompactVBoxSound subbox12_108 :=
  LRCompactVLeafParameters.sound checked12_108


def subbox12_109 : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((61 : ℚ) / 64), ((77 : ℚ) / 80)⟩

theorem checked12_109 :
    LRCompactVLeafParameters.check subbox12_109 .short = true := by decide +kernel

theorem subsound12_109 : LRCompactVBoxSound subbox12_109 :=
  LRCompactVLeafParameters.sound checked12_109


def subbox12_110 : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((61 : ℚ) / 64), ((77 : ℚ) / 80)⟩

theorem checked12_110 :
    LRCompactVLeafParameters.check subbox12_110 .short = true := by decide +kernel

theorem subsound12_110 : LRCompactVBoxSound subbox12_110 :=
  LRCompactVLeafParameters.sound checked12_110


def subbox12_111 : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((5 : ℚ) / 12), ((7 : ℚ) / 16), ((151 : ℚ) / 160), ((61 : ℚ) / 64)⟩

theorem checked12_111 :
    LRCompactVLeafParameters.check subbox12_111 .short = true := by decide +kernel

theorem subsound12_111 : LRCompactVBoxSound subbox12_111 :=
  LRCompactVLeafParameters.sound checked12_111


def subbox12_112 : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((151 : ℚ) / 160), ((61 : ℚ) / 64)⟩

theorem checked12_112 :
    LRCompactVLeafParameters.check subbox12_112 .short = true := by decide +kernel

theorem subsound12_112 : LRCompactVBoxSound subbox12_112 :=
  LRCompactVLeafParameters.sound checked12_112


def subbox12_113 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((5 : ℚ) / 12), ((7 : ℚ) / 16), ((151 : ℚ) / 160), ((61 : ℚ) / 64)⟩

theorem checked12_113 :
    LRCompactVLeafParameters.check subbox12_113 .long = true := by decide +kernel

theorem subsound12_113 : LRCompactVBoxSound subbox12_113 :=
  LRCompactVLeafParameters.sound checked12_113


def subbox12_114 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((151 : ℚ) / 160), ((61 : ℚ) / 64)⟩

theorem checked12_114 :
    LRCompactVLeafParameters.check subbox12_114 .long = true := by decide +kernel

theorem subsound12_114 : LRCompactVBoxSound subbox12_114 :=
  LRCompactVLeafParameters.sound checked12_114


def subbox12_115 : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((5 : ℚ) / 12), ((7 : ℚ) / 16), ((61 : ℚ) / 64), ((77 : ℚ) / 80)⟩

theorem checked12_115 :
    LRCompactVLeafParameters.check subbox12_115 .short = true := by decide +kernel

theorem subsound12_115 : LRCompactVBoxSound subbox12_115 :=
  LRCompactVLeafParameters.sound checked12_115


def subbox12_116 : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((61 : ℚ) / 64), ((77 : ℚ) / 80)⟩

theorem checked12_116 :
    LRCompactVLeafParameters.check subbox12_116 .short = true := by decide +kernel

theorem subsound12_116 : LRCompactVBoxSound subbox12_116 :=
  LRCompactVLeafParameters.sound checked12_116


def subbox12_117 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((5 : ℚ) / 12), ((7 : ℚ) / 16), ((61 : ℚ) / 64), ((77 : ℚ) / 80)⟩

theorem checked12_117 :
    LRCompactVLeafParameters.check subbox12_117 .long = true := by decide +kernel

theorem subsound12_117 : LRCompactVBoxSound subbox12_117 :=
  LRCompactVLeafParameters.sound checked12_117


def subbox12_118 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((61 : ℚ) / 64), ((77 : ℚ) / 80)⟩

theorem checked12_118 :
    LRCompactVLeafParameters.check subbox12_118 .long = true := by decide +kernel

theorem subsound12_118 : LRCompactVBoxSound subbox12_118 :=
  LRCompactVLeafParameters.sound checked12_118


def subbox12_119 : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((151 : ℚ) / 160), ((61 : ℚ) / 64)⟩

theorem checked12_119 :
    LRCompactVLeafParameters.check subbox12_119 .long = true := by decide +kernel

theorem subsound12_119 : LRCompactVBoxSound subbox12_119 :=
  LRCompactVLeafParameters.sound checked12_119


def subbox12_120 : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((151 : ℚ) / 160), ((61 : ℚ) / 64)⟩

theorem checked12_120 :
    LRCompactVLeafParameters.check subbox12_120 .long = true := by decide +kernel

theorem subsound12_120 : LRCompactVBoxSound subbox12_120 :=
  LRCompactVLeafParameters.sound checked12_120


def subbox12_121 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((151 : ℚ) / 160), ((61 : ℚ) / 64)⟩

theorem checked12_121 :
    LRCompactVLeafParameters.check subbox12_121 .long = true := by decide +kernel

theorem subsound12_121 : LRCompactVBoxSound subbox12_121 :=
  LRCompactVLeafParameters.sound checked12_121


def subbox12_122 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((151 : ℚ) / 160), ((61 : ℚ) / 64)⟩

theorem checked12_122 :
    LRCompactVLeafParameters.check subbox12_122 .long = true := by decide +kernel

theorem subsound12_122 : LRCompactVBoxSound subbox12_122 :=
  LRCompactVLeafParameters.sound checked12_122


def subbox12_123 : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((61 : ℚ) / 64), ((77 : ℚ) / 80)⟩

theorem checked12_123 :
    LRCompactVLeafParameters.check subbox12_123 .long = true := by decide +kernel

theorem subsound12_123 : LRCompactVBoxSound subbox12_123 :=
  LRCompactVLeafParameters.sound checked12_123


def subbox12_124 : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((61 : ℚ) / 64), ((77 : ℚ) / 80)⟩

theorem checked12_124 :
    LRCompactVLeafParameters.check subbox12_124 .long = true := by decide +kernel

theorem subsound12_124 : LRCompactVBoxSound subbox12_124 :=
  LRCompactVLeafParameters.sound checked12_124


def subbox12_125 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((61 : ℚ) / 64), ((77 : ℚ) / 80)⟩

theorem checked12_125 :
    LRCompactVLeafParameters.check subbox12_125 .long = true := by decide +kernel

theorem subsound12_125 : LRCompactVBoxSound subbox12_125 :=
  LRCompactVLeafParameters.sound checked12_125


def subbox12_126 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((61 : ℚ) / 64), ((77 : ℚ) / 80)⟩

theorem checked12_126 :
    LRCompactVLeafParameters.check subbox12_126 .long = true := by decide +kernel

theorem subsound12_126 : LRCompactVBoxSound subbox12_126 :=
  LRCompactVLeafParameters.sound checked12_126


def joinbox12_rRRLRL : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((1 : ℚ) / 2), ((1 : ℚ) / 3), ((5 : ℚ) / 12), ((37 : ℚ) / 40), ((77 : ℚ) / 80)⟩


def joinbox12_rRRLRLL : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((1 : ℚ) / 2), ((1 : ℚ) / 3), ((5 : ℚ) / 12), ((37 : ℚ) / 40), ((151 : ℚ) / 160)⟩


def joinbox12_rRRLRLLL : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((7 : ℚ) / 16), ((1 : ℚ) / 3), ((5 : ℚ) / 12), ((37 : ℚ) / 40), ((151 : ℚ) / 160)⟩


def joinbox12_rRRLRLLLL : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((7 : ℚ) / 16), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((37 : ℚ) / 40), ((151 : ℚ) / 160)⟩


def joinbox12_rRRLRLLLLL : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((7 : ℚ) / 16), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((37 : ℚ) / 40), ((299 : ℚ) / 320)⟩


def joinbox12_rRRLRLLLLLL : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((37 : ℚ) / 40), ((299 : ℚ) / 320)⟩


def joinbox12_rRRLRLLLLLR : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((37 : ℚ) / 40), ((299 : ℚ) / 320)⟩


def joinbox12_rRRLRLLLLR : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((7 : ℚ) / 16), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((299 : ℚ) / 320), ((151 : ℚ) / 160)⟩


def joinbox12_rRRLRLLLLRL : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((299 : ℚ) / 320), ((151 : ℚ) / 160)⟩


def joinbox12_rRRLRLLLLRR : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((299 : ℚ) / 320), ((151 : ℚ) / 160)⟩


def joinbox12_rRRLRLLLR : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((7 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((37 : ℚ) / 40), ((151 : ℚ) / 160)⟩


def joinbox12_rRRLRLLLRL : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((7 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((37 : ℚ) / 40), ((299 : ℚ) / 320)⟩


def joinbox12_rRRLRLLLRLL : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((37 : ℚ) / 40), ((299 : ℚ) / 320)⟩


def joinbox12_rRRLRLLLRLR : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((37 : ℚ) / 40), ((299 : ℚ) / 320)⟩


def joinbox12_rRRLRLLLRR : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((7 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((299 : ℚ) / 320), ((151 : ℚ) / 160)⟩


def joinbox12_rRRLRLLLRRL : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((299 : ℚ) / 320), ((151 : ℚ) / 160)⟩


def joinbox12_rRRLRLLLRRR : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((299 : ℚ) / 320), ((151 : ℚ) / 160)⟩


def joinbox12_rRRLRLLR : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((1 : ℚ) / 2), ((1 : ℚ) / 3), ((5 : ℚ) / 12), ((37 : ℚ) / 40), ((151 : ℚ) / 160)⟩


def joinbox12_rRRLRLLRL : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((1 : ℚ) / 2), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((37 : ℚ) / 40), ((151 : ℚ) / 160)⟩


def joinbox12_rRRLRLLRLL : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((1 : ℚ) / 2), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((37 : ℚ) / 40), ((299 : ℚ) / 320)⟩


def joinbox12_rRRLRLLRLLL : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((37 : ℚ) / 40), ((299 : ℚ) / 320)⟩


def joinbox12_rRRLRLLRLLR : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((37 : ℚ) / 40), ((299 : ℚ) / 320)⟩


def joinbox12_rRRLRLLRLR : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((1 : ℚ) / 2), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((299 : ℚ) / 320), ((151 : ℚ) / 160)⟩


def joinbox12_rRRLRLLRLRL : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((299 : ℚ) / 320), ((151 : ℚ) / 160)⟩


def joinbox12_rRRLRLLRLRR : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((299 : ℚ) / 320), ((151 : ℚ) / 160)⟩


def joinbox12_rRRLRLLRR : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((1 : ℚ) / 2), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((37 : ℚ) / 40), ((151 : ℚ) / 160)⟩


def joinbox12_rRRLRLLRRL : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((1 : ℚ) / 2), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((37 : ℚ) / 40), ((299 : ℚ) / 320)⟩


def joinbox12_rRRLRLLRRLL : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((37 : ℚ) / 40), ((299 : ℚ) / 320)⟩


def joinbox12_rRRLRLLRRLR : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((37 : ℚ) / 40), ((299 : ℚ) / 320)⟩


def joinbox12_rRRLRLLRRR : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((1 : ℚ) / 2), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((299 : ℚ) / 320), ((151 : ℚ) / 160)⟩


def joinbox12_rRRLRLLRRRL : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((299 : ℚ) / 320), ((151 : ℚ) / 160)⟩


def joinbox12_rRRLRLLRRRR : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((299 : ℚ) / 320), ((151 : ℚ) / 160)⟩


def joinbox12_rRRLRLR : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((1 : ℚ) / 2), ((1 : ℚ) / 3), ((5 : ℚ) / 12), ((151 : ℚ) / 160), ((77 : ℚ) / 80)⟩


def joinbox12_rRRLRLRL : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((7 : ℚ) / 16), ((1 : ℚ) / 3), ((5 : ℚ) / 12), ((151 : ℚ) / 160), ((77 : ℚ) / 80)⟩


def joinbox12_rRRLRLRLL : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((7 : ℚ) / 16), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((151 : ℚ) / 160), ((77 : ℚ) / 80)⟩


def joinbox12_rRRLRLRLLL : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((7 : ℚ) / 16), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((151 : ℚ) / 160), ((61 : ℚ) / 64)⟩


def joinbox12_rRRLRLRLLLR : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((151 : ℚ) / 160), ((61 : ℚ) / 64)⟩


def joinbox12_rRRLRLRLLR : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((7 : ℚ) / 16), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((61 : ℚ) / 64), ((77 : ℚ) / 80)⟩


def joinbox12_rRRLRLRLLRR : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((61 : ℚ) / 64), ((77 : ℚ) / 80)⟩


def joinbox12_rRRLRLRLR : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((7 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((151 : ℚ) / 160), ((77 : ℚ) / 80)⟩


def joinbox12_rRRLRLRLRL : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((7 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((151 : ℚ) / 160), ((61 : ℚ) / 64)⟩


def joinbox12_rRRLRLRLRLL : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((151 : ℚ) / 160), ((61 : ℚ) / 64)⟩


def joinbox12_rRRLRLRLRLR : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((151 : ℚ) / 160), ((61 : ℚ) / 64)⟩


def joinbox12_rRRLRLRLRR : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((7 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((61 : ℚ) / 64), ((77 : ℚ) / 80)⟩


def joinbox12_rRRLRLRLRRL : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((61 : ℚ) / 64), ((77 : ℚ) / 80)⟩


def joinbox12_rRRLRLRLRRR : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((61 : ℚ) / 64), ((77 : ℚ) / 80)⟩


def joinbox12_rRRLRLRR : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((1 : ℚ) / 2), ((1 : ℚ) / 3), ((5 : ℚ) / 12), ((151 : ℚ) / 160), ((77 : ℚ) / 80)⟩


def joinbox12_rRRLRLRRL : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((1 : ℚ) / 2), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((151 : ℚ) / 160), ((77 : ℚ) / 80)⟩


def joinbox12_rRRLRLRRLL : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((1 : ℚ) / 2), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((151 : ℚ) / 160), ((61 : ℚ) / 64)⟩


def joinbox12_rRRLRLRRLLL : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((151 : ℚ) / 160), ((61 : ℚ) / 64)⟩


def joinbox12_rRRLRLRRLLR : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((151 : ℚ) / 160), ((61 : ℚ) / 64)⟩


def joinbox12_rRRLRLRRLR : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((1 : ℚ) / 2), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((61 : ℚ) / 64), ((77 : ℚ) / 80)⟩


def joinbox12_rRRLRLRRLRL : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((61 : ℚ) / 64), ((77 : ℚ) / 80)⟩


def joinbox12_rRRLRLRRLRR : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((61 : ℚ) / 64), ((77 : ℚ) / 80)⟩


def joinbox12_rRRLRLRRR : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((1 : ℚ) / 2), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((151 : ℚ) / 160), ((77 : ℚ) / 80)⟩


def joinbox12_rRRLRLRRRL : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((1 : ℚ) / 2), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((151 : ℚ) / 160), ((61 : ℚ) / 64)⟩


def joinbox12_rRRLRLRRRLL : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((151 : ℚ) / 160), ((61 : ℚ) / 64)⟩


def joinbox12_rRRLRLRRRLR : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((151 : ℚ) / 160), ((61 : ℚ) / 64)⟩


def joinbox12_rRRLRLRRRR : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((1 : ℚ) / 2), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((61 : ℚ) / 64), ((77 : ℚ) / 80)⟩


def joinbox12_rRRLRLRRRRL : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((61 : ℚ) / 64), ((77 : ℚ) / 80)⟩


def joinbox12_rRRLRLRRRRR : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((61 : ℚ) / 64), ((77 : ℚ) / 80)⟩


def joinbox12_rRRLRR : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((1 : ℚ) / 2), ((5 : ℚ) / 12), ((1 : ℚ) / 2), ((37 : ℚ) / 40), ((77 : ℚ) / 80)⟩


def joinbox12_rRRLRRL : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((1 : ℚ) / 2), ((5 : ℚ) / 12), ((1 : ℚ) / 2), ((37 : ℚ) / 40), ((151 : ℚ) / 160)⟩


def joinbox12_rRRLRRLL : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((7 : ℚ) / 16), ((5 : ℚ) / 12), ((1 : ℚ) / 2), ((37 : ℚ) / 40), ((151 : ℚ) / 160)⟩


def joinbox12_rRRLRRLLL : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((7 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((37 : ℚ) / 40), ((151 : ℚ) / 160)⟩


def joinbox12_rRRLRRLLLL : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((7 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((37 : ℚ) / 40), ((299 : ℚ) / 320)⟩


def joinbox12_rRRLRRLLLLL : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((37 : ℚ) / 40), ((299 : ℚ) / 320)⟩


def joinbox12_rRRLRRLLLLR : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((37 : ℚ) / 40), ((299 : ℚ) / 320)⟩


def joinbox12_rRRLRRLLLR : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((7 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((299 : ℚ) / 320), ((151 : ℚ) / 160)⟩


def joinbox12_rRRLRRLLLRL : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((299 : ℚ) / 320), ((151 : ℚ) / 160)⟩


def joinbox12_rRRLRRLLLRR : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((299 : ℚ) / 320), ((151 : ℚ) / 160)⟩


def joinbox12_rRRLRRLLR : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((37 : ℚ) / 40), ((151 : ℚ) / 160)⟩


def joinbox12_rRRLRRLLRL : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((37 : ℚ) / 40), ((299 : ℚ) / 320)⟩


def joinbox12_rRRLRRLLRLL : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((37 : ℚ) / 40), ((299 : ℚ) / 320)⟩


def joinbox12_rRRLRRLLRLR : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((37 : ℚ) / 40), ((299 : ℚ) / 320)⟩


def joinbox12_rRRLRRLLRR : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((299 : ℚ) / 320), ((151 : ℚ) / 160)⟩


def joinbox12_rRRLRRLLRRL : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((299 : ℚ) / 320), ((151 : ℚ) / 160)⟩


def joinbox12_rRRLRRLLRRR : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((299 : ℚ) / 320), ((151 : ℚ) / 160)⟩


def joinbox12_rRRLRRLR : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((1 : ℚ) / 2), ((5 : ℚ) / 12), ((1 : ℚ) / 2), ((37 : ℚ) / 40), ((151 : ℚ) / 160)⟩


def joinbox12_rRRLRRLRL : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((1 : ℚ) / 2), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((37 : ℚ) / 40), ((151 : ℚ) / 160)⟩


def joinbox12_rRRLRRLRLL : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((1 : ℚ) / 2), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((37 : ℚ) / 40), ((299 : ℚ) / 320)⟩


def joinbox12_rRRLRRLRLLL : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((37 : ℚ) / 40), ((299 : ℚ) / 320)⟩


def joinbox12_rRRLRRLRLLR : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((37 : ℚ) / 40), ((299 : ℚ) / 320)⟩


def joinbox12_rRRLRRLRLR : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((1 : ℚ) / 2), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((299 : ℚ) / 320), ((151 : ℚ) / 160)⟩


def joinbox12_rRRLRRLRLRL : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((299 : ℚ) / 320), ((151 : ℚ) / 160)⟩


def joinbox12_rRRLRRLRLRR : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((299 : ℚ) / 320), ((151 : ℚ) / 160)⟩


def joinbox12_rRRLRRLRR : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((1 : ℚ) / 2), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((37 : ℚ) / 40), ((151 : ℚ) / 160)⟩


def joinbox12_rRRLRRLRRL : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((1 : ℚ) / 2), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((37 : ℚ) / 40), ((299 : ℚ) / 320)⟩


def joinbox12_rRRLRRLRRLL : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((37 : ℚ) / 40), ((299 : ℚ) / 320)⟩


def joinbox12_rRRLRRLRRLR : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((37 : ℚ) / 40), ((299 : ℚ) / 320)⟩


def joinbox12_rRRLRRLRRLRR : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((37 : ℚ) / 40), ((299 : ℚ) / 320)⟩


def joinbox12_rRRLRRLRRR : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((1 : ℚ) / 2), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((299 : ℚ) / 320), ((151 : ℚ) / 160)⟩


def joinbox12_rRRLRRLRRRL : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((299 : ℚ) / 320), ((151 : ℚ) / 160)⟩


def joinbox12_rRRLRRLRRRR : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((299 : ℚ) / 320), ((151 : ℚ) / 160)⟩


def joinbox12_rRRLRRR : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((1 : ℚ) / 2), ((5 : ℚ) / 12), ((1 : ℚ) / 2), ((151 : ℚ) / 160), ((77 : ℚ) / 80)⟩


def joinbox12_rRRLRRRL : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((7 : ℚ) / 16), ((5 : ℚ) / 12), ((1 : ℚ) / 2), ((151 : ℚ) / 160), ((77 : ℚ) / 80)⟩


def joinbox12_rRRLRRRLL : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((7 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((151 : ℚ) / 160), ((77 : ℚ) / 80)⟩


def joinbox12_rRRLRRRLLL : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((7 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((151 : ℚ) / 160), ((61 : ℚ) / 64)⟩


def joinbox12_rRRLRRRLLLL : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((151 : ℚ) / 160), ((61 : ℚ) / 64)⟩


def joinbox12_rRRLRRRLLLR : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((151 : ℚ) / 160), ((61 : ℚ) / 64)⟩


def joinbox12_rRRLRRRLLR : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((7 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((61 : ℚ) / 64), ((77 : ℚ) / 80)⟩


def joinbox12_rRRLRRRLLRL : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((61 : ℚ) / 64), ((77 : ℚ) / 80)⟩


def joinbox12_rRRLRRRLLRR : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((61 : ℚ) / 64), ((77 : ℚ) / 80)⟩


def joinbox12_rRRLRRRLR : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((151 : ℚ) / 160), ((77 : ℚ) / 80)⟩


def joinbox12_rRRLRRRLRL : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((151 : ℚ) / 160), ((61 : ℚ) / 64)⟩


def joinbox12_rRRLRRRLRLL : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((151 : ℚ) / 160), ((61 : ℚ) / 64)⟩


def joinbox12_rRRLRRRLRLR : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((151 : ℚ) / 160), ((61 : ℚ) / 64)⟩


def joinbox12_rRRLRRRLRR : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((61 : ℚ) / 64), ((77 : ℚ) / 80)⟩


def joinbox12_rRRLRRRLRRL : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((61 : ℚ) / 64), ((77 : ℚ) / 80)⟩


def joinbox12_rRRLRRRLRRR : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((61 : ℚ) / 64), ((77 : ℚ) / 80)⟩


def joinbox12_rRRLRRRR : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((1 : ℚ) / 2), ((5 : ℚ) / 12), ((1 : ℚ) / 2), ((151 : ℚ) / 160), ((77 : ℚ) / 80)⟩


def joinbox12_rRRLRRRRL : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((1 : ℚ) / 2), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((151 : ℚ) / 160), ((77 : ℚ) / 80)⟩


def joinbox12_rRRLRRRRLL : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((1 : ℚ) / 2), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((151 : ℚ) / 160), ((61 : ℚ) / 64)⟩


def joinbox12_rRRLRRRRLLL : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((151 : ℚ) / 160), ((61 : ℚ) / 64)⟩


def joinbox12_rRRLRRRRLLR : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((151 : ℚ) / 160), ((61 : ℚ) / 64)⟩


def joinbox12_rRRLRRRRLR : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((1 : ℚ) / 2), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((61 : ℚ) / 64), ((77 : ℚ) / 80)⟩


def joinbox12_rRRLRRRRLRL : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((61 : ℚ) / 64), ((77 : ℚ) / 80)⟩


def joinbox12_rRRLRRRRLRR : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((61 : ℚ) / 64), ((77 : ℚ) / 80)⟩


def joinbox12_rRRLRRRRR : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((1 : ℚ) / 2), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((151 : ℚ) / 160), ((77 : ℚ) / 80)⟩


def joinbox12_rRRLRRRRRL : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((1 : ℚ) / 2), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((151 : ℚ) / 160), ((61 : ℚ) / 64)⟩


def joinbox12_rRRLRRRRRLL : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((151 : ℚ) / 160), ((61 : ℚ) / 64)⟩


def joinbox12_rRRLRRRRRLR : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((151 : ℚ) / 160), ((61 : ℚ) / 64)⟩


def joinbox12_rRRLRRRRRR : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((1 : ℚ) / 2), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((61 : ℚ) / 64), ((77 : ℚ) / 80)⟩


def joinbox12_rRRLRRRRRRL : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((61 : ℚ) / 64), ((77 : ℚ) / 80)⟩


def joinbox12_rRRLRRRRRRR : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((61 : ℚ) / 64), ((77 : ℚ) / 80)⟩


theorem sound12 : LRCompactVBoxSound box12 :=
  (LRCompactVBoxSound.join (box := box12) .k ((5 : ℚ) / 12)
    (LRCompactVBoxSound.join (box := joinbox12_rRRLRL) .chi ((151 : ℚ) / 160)
      (LRCompactVBoxSound.join (box := joinbox12_rRRLRLL) .s ((7 : ℚ) / 16)
        (LRCompactVBoxSound.join (box := joinbox12_rRRLRLLL) .k ((3 : ℚ) / 8)
          (LRCompactVBoxSound.join (box := joinbox12_rRRLRLLLL) .chi ((299 : ℚ) / 320)
            (LRCompactVBoxSound.join (box := joinbox12_rRRLRLLLLL) .s ((13 : ℚ) / 32)
              (LRCompactVBoxSound.join (box := joinbox12_rRRLRLLLLLL) .k ((17 : ℚ) / 48)
                subsound12_0
                subsound12_1)
              (LRCompactVBoxSound.join (box := joinbox12_rRRLRLLLLLR) .k ((17 : ℚ) / 48)
                subsound12_2
                subsound12_3))
            (LRCompactVBoxSound.join (box := joinbox12_rRRLRLLLLR) .s ((13 : ℚ) / 32)
              (LRCompactVBoxSound.join (box := joinbox12_rRRLRLLLLRL) .k ((17 : ℚ) / 48)
                subsound12_4
                subsound12_5)
              (LRCompactVBoxSound.join (box := joinbox12_rRRLRLLLLRR) .k ((17 : ℚ) / 48)
                subsound12_6
                subsound12_7)))
          (LRCompactVBoxSound.join (box := joinbox12_rRRLRLLLR) .chi ((299 : ℚ) / 320)
            (LRCompactVBoxSound.join (box := joinbox12_rRRLRLLLRL) .s ((13 : ℚ) / 32)
              (LRCompactVBoxSound.join (box := joinbox12_rRRLRLLLRLL) .k ((19 : ℚ) / 48)
                subsound12_8
                subsound12_9)
              (LRCompactVBoxSound.join (box := joinbox12_rRRLRLLLRLR) .k ((19 : ℚ) / 48)
                subsound12_10
                subsound12_11))
            (LRCompactVBoxSound.join (box := joinbox12_rRRLRLLLRR) .s ((13 : ℚ) / 32)
              (LRCompactVBoxSound.join (box := joinbox12_rRRLRLLLRRL) .k ((19 : ℚ) / 48)
                subsound12_12
                subsound12_13)
              (LRCompactVBoxSound.join (box := joinbox12_rRRLRLLLRRR) .k ((19 : ℚ) / 48)
                subsound12_14
                subsound12_15))))
        (LRCompactVBoxSound.join (box := joinbox12_rRRLRLLR) .k ((3 : ℚ) / 8)
          (LRCompactVBoxSound.join (box := joinbox12_rRRLRLLRL) .chi ((299 : ℚ) / 320)
            (LRCompactVBoxSound.join (box := joinbox12_rRRLRLLRLL) .s ((15 : ℚ) / 32)
              (LRCompactVBoxSound.join (box := joinbox12_rRRLRLLRLLL) .k ((17 : ℚ) / 48)
                subsound12_16
                subsound12_17)
              (LRCompactVBoxSound.join (box := joinbox12_rRRLRLLRLLR) .k ((17 : ℚ) / 48)
                subsound12_18
                subsound12_19))
            (LRCompactVBoxSound.join (box := joinbox12_rRRLRLLRLR) .s ((15 : ℚ) / 32)
              (LRCompactVBoxSound.join (box := joinbox12_rRRLRLLRLRL) .k ((17 : ℚ) / 48)
                subsound12_20
                subsound12_21)
              (LRCompactVBoxSound.join (box := joinbox12_rRRLRLLRLRR) .k ((17 : ℚ) / 48)
                subsound12_22
                subsound12_23)))
          (LRCompactVBoxSound.join (box := joinbox12_rRRLRLLRR) .chi ((299 : ℚ) / 320)
            (LRCompactVBoxSound.join (box := joinbox12_rRRLRLLRRL) .s ((15 : ℚ) / 32)
              (LRCompactVBoxSound.join (box := joinbox12_rRRLRLLRRLL) .k ((19 : ℚ) / 48)
                subsound12_24
                subsound12_25)
              (LRCompactVBoxSound.join (box := joinbox12_rRRLRLLRRLR) .k ((19 : ℚ) / 48)
                subsound12_26
                subsound12_27))
            (LRCompactVBoxSound.join (box := joinbox12_rRRLRLLRRR) .s ((15 : ℚ) / 32)
              (LRCompactVBoxSound.join (box := joinbox12_rRRLRLLRRRL) .k ((19 : ℚ) / 48)
                subsound12_28
                subsound12_29)
              (LRCompactVBoxSound.join (box := joinbox12_rRRLRLLRRRR) .k ((19 : ℚ) / 48)
                subsound12_30
                subsound12_31)))))
      (LRCompactVBoxSound.join (box := joinbox12_rRRLRLR) .s ((7 : ℚ) / 16)
        (LRCompactVBoxSound.join (box := joinbox12_rRRLRLRL) .k ((3 : ℚ) / 8)
          (LRCompactVBoxSound.join (box := joinbox12_rRRLRLRLL) .chi ((61 : ℚ) / 64)
            (LRCompactVBoxSound.join (box := joinbox12_rRRLRLRLLL) .s ((13 : ℚ) / 32)
              subsound12_32
              (LRCompactVBoxSound.join (box := joinbox12_rRRLRLRLLLR) .k ((17 : ℚ) / 48)
                subsound12_33
                subsound12_34))
            (LRCompactVBoxSound.join (box := joinbox12_rRRLRLRLLR) .s ((13 : ℚ) / 32)
              subsound12_35
              (LRCompactVBoxSound.join (box := joinbox12_rRRLRLRLLRR) .k ((17 : ℚ) / 48)
                subsound12_36
                subsound12_37)))
          (LRCompactVBoxSound.join (box := joinbox12_rRRLRLRLR) .chi ((61 : ℚ) / 64)
            (LRCompactVBoxSound.join (box := joinbox12_rRRLRLRLRL) .s ((13 : ℚ) / 32)
              (LRCompactVBoxSound.join (box := joinbox12_rRRLRLRLRLL) .k ((19 : ℚ) / 48)
                subsound12_38
                subsound12_39)
              (LRCompactVBoxSound.join (box := joinbox12_rRRLRLRLRLR) .k ((19 : ℚ) / 48)
                subsound12_40
                subsound12_41))
            (LRCompactVBoxSound.join (box := joinbox12_rRRLRLRLRR) .s ((13 : ℚ) / 32)
              (LRCompactVBoxSound.join (box := joinbox12_rRRLRLRLRRL) .k ((19 : ℚ) / 48)
                subsound12_42
                subsound12_43)
              (LRCompactVBoxSound.join (box := joinbox12_rRRLRLRLRRR) .k ((19 : ℚ) / 48)
                subsound12_44
                subsound12_45))))
        (LRCompactVBoxSound.join (box := joinbox12_rRRLRLRR) .k ((3 : ℚ) / 8)
          (LRCompactVBoxSound.join (box := joinbox12_rRRLRLRRL) .chi ((61 : ℚ) / 64)
            (LRCompactVBoxSound.join (box := joinbox12_rRRLRLRRLL) .s ((15 : ℚ) / 32)
              (LRCompactVBoxSound.join (box := joinbox12_rRRLRLRRLLL) .k ((17 : ℚ) / 48)
                subsound12_46
                subsound12_47)
              (LRCompactVBoxSound.join (box := joinbox12_rRRLRLRRLLR) .k ((17 : ℚ) / 48)
                subsound12_48
                subsound12_49))
            (LRCompactVBoxSound.join (box := joinbox12_rRRLRLRRLR) .s ((15 : ℚ) / 32)
              (LRCompactVBoxSound.join (box := joinbox12_rRRLRLRRLRL) .k ((17 : ℚ) / 48)
                subsound12_50
                subsound12_51)
              (LRCompactVBoxSound.join (box := joinbox12_rRRLRLRRLRR) .k ((17 : ℚ) / 48)
                subsound12_52
                subsound12_53)))
          (LRCompactVBoxSound.join (box := joinbox12_rRRLRLRRR) .chi ((61 : ℚ) / 64)
            (LRCompactVBoxSound.join (box := joinbox12_rRRLRLRRRL) .s ((15 : ℚ) / 32)
              (LRCompactVBoxSound.join (box := joinbox12_rRRLRLRRRLL) .k ((19 : ℚ) / 48)
                subsound12_54
                subsound12_55)
              (LRCompactVBoxSound.join (box := joinbox12_rRRLRLRRRLR) .k ((19 : ℚ) / 48)
                subsound12_56
                subsound12_57))
            (LRCompactVBoxSound.join (box := joinbox12_rRRLRLRRRR) .s ((15 : ℚ) / 32)
              (LRCompactVBoxSound.join (box := joinbox12_rRRLRLRRRRL) .k ((19 : ℚ) / 48)
                subsound12_58
                subsound12_59)
              (LRCompactVBoxSound.join (box := joinbox12_rRRLRLRRRRR) .k ((19 : ℚ) / 48)
                subsound12_60
                subsound12_61))))))
    (LRCompactVBoxSound.join (box := joinbox12_rRRLRR) .chi ((151 : ℚ) / 160)
      (LRCompactVBoxSound.join (box := joinbox12_rRRLRRL) .s ((7 : ℚ) / 16)
        (LRCompactVBoxSound.join (box := joinbox12_rRRLRRLL) .k ((11 : ℚ) / 24)
          (LRCompactVBoxSound.join (box := joinbox12_rRRLRRLLL) .chi ((299 : ℚ) / 320)
            (LRCompactVBoxSound.join (box := joinbox12_rRRLRRLLLL) .s ((13 : ℚ) / 32)
              (LRCompactVBoxSound.join (box := joinbox12_rRRLRRLLLLL) .k ((7 : ℚ) / 16)
                subsound12_62
                subsound12_63)
              (LRCompactVBoxSound.join (box := joinbox12_rRRLRRLLLLR) .k ((7 : ℚ) / 16)
                subsound12_64
                subsound12_65))
            (LRCompactVBoxSound.join (box := joinbox12_rRRLRRLLLR) .s ((13 : ℚ) / 32)
              (LRCompactVBoxSound.join (box := joinbox12_rRRLRRLLLRL) .k ((7 : ℚ) / 16)
                subsound12_66
                subsound12_67)
              (LRCompactVBoxSound.join (box := joinbox12_rRRLRRLLLRR) .k ((7 : ℚ) / 16)
                subsound12_68
                subsound12_69)))
          (LRCompactVBoxSound.join (box := joinbox12_rRRLRRLLR) .chi ((299 : ℚ) / 320)
            (LRCompactVBoxSound.join (box := joinbox12_rRRLRRLLRL) .s ((13 : ℚ) / 32)
              (LRCompactVBoxSound.join (box := joinbox12_rRRLRRLLRLL) .k ((23 : ℚ) / 48)
                subsound12_70
                subsound12_71)
              (LRCompactVBoxSound.join (box := joinbox12_rRRLRRLLRLR) .k ((23 : ℚ) / 48)
                subsound12_72
                subsound12_73))
            (LRCompactVBoxSound.join (box := joinbox12_rRRLRRLLRR) .s ((13 : ℚ) / 32)
              (LRCompactVBoxSound.join (box := joinbox12_rRRLRRLLRRL) .k ((23 : ℚ) / 48)
                subsound12_74
                subsound12_75)
              (LRCompactVBoxSound.join (box := joinbox12_rRRLRRLLRRR) .k ((23 : ℚ) / 48)
                subsound12_76
                subsound12_77))))
        (LRCompactVBoxSound.join (box := joinbox12_rRRLRRLR) .k ((11 : ℚ) / 24)
          (LRCompactVBoxSound.join (box := joinbox12_rRRLRRLRL) .chi ((299 : ℚ) / 320)
            (LRCompactVBoxSound.join (box := joinbox12_rRRLRRLRLL) .s ((15 : ℚ) / 32)
              (LRCompactVBoxSound.join (box := joinbox12_rRRLRRLRLLL) .k ((7 : ℚ) / 16)
                subsound12_78
                subsound12_79)
              (LRCompactVBoxSound.join (box := joinbox12_rRRLRRLRLLR) .k ((7 : ℚ) / 16)
                subsound12_80
                subsound12_81))
            (LRCompactVBoxSound.join (box := joinbox12_rRRLRRLRLR) .s ((15 : ℚ) / 32)
              (LRCompactVBoxSound.join (box := joinbox12_rRRLRRLRLRL) .k ((7 : ℚ) / 16)
                subsound12_82
                subsound12_83)
              (LRCompactVBoxSound.join (box := joinbox12_rRRLRRLRLRR) .k ((7 : ℚ) / 16)
                subsound12_84
                subsound12_85)))
          (LRCompactVBoxSound.join (box := joinbox12_rRRLRRLRR) .chi ((299 : ℚ) / 320)
            (LRCompactVBoxSound.join (box := joinbox12_rRRLRRLRRL) .s ((15 : ℚ) / 32)
              (LRCompactVBoxSound.join (box := joinbox12_rRRLRRLRRLL) .k ((23 : ℚ) / 48)
                subsound12_86
                subsound12_87)
              (LRCompactVBoxSound.join (box := joinbox12_rRRLRRLRRLR) .k ((23 : ℚ) / 48)
                subsound12_88
                (LRCompactVBoxSound.join (box := joinbox12_rRRLRRLRRLRR) .chi ((119 : ℚ) / 128)
                  subsound12_89
                  subsound12_90)))
            (LRCompactVBoxSound.join (box := joinbox12_rRRLRRLRRR) .s ((15 : ℚ) / 32)
              (LRCompactVBoxSound.join (box := joinbox12_rRRLRRLRRRL) .k ((23 : ℚ) / 48)
                subsound12_91
                subsound12_92)
              (LRCompactVBoxSound.join (box := joinbox12_rRRLRRLRRRR) .k ((23 : ℚ) / 48)
                subsound12_93
                subsound12_94)))))
      (LRCompactVBoxSound.join (box := joinbox12_rRRLRRR) .s ((7 : ℚ) / 16)
        (LRCompactVBoxSound.join (box := joinbox12_rRRLRRRL) .k ((11 : ℚ) / 24)
          (LRCompactVBoxSound.join (box := joinbox12_rRRLRRRLL) .chi ((61 : ℚ) / 64)
            (LRCompactVBoxSound.join (box := joinbox12_rRRLRRRLLL) .s ((13 : ℚ) / 32)
              (LRCompactVBoxSound.join (box := joinbox12_rRRLRRRLLLL) .k ((7 : ℚ) / 16)
                subsound12_95
                subsound12_96)
              (LRCompactVBoxSound.join (box := joinbox12_rRRLRRRLLLR) .k ((7 : ℚ) / 16)
                subsound12_97
                subsound12_98))
            (LRCompactVBoxSound.join (box := joinbox12_rRRLRRRLLR) .s ((13 : ℚ) / 32)
              (LRCompactVBoxSound.join (box := joinbox12_rRRLRRRLLRL) .k ((7 : ℚ) / 16)
                subsound12_99
                subsound12_100)
              (LRCompactVBoxSound.join (box := joinbox12_rRRLRRRLLRR) .k ((7 : ℚ) / 16)
                subsound12_101
                subsound12_102)))
          (LRCompactVBoxSound.join (box := joinbox12_rRRLRRRLR) .chi ((61 : ℚ) / 64)
            (LRCompactVBoxSound.join (box := joinbox12_rRRLRRRLRL) .s ((13 : ℚ) / 32)
              (LRCompactVBoxSound.join (box := joinbox12_rRRLRRRLRLL) .k ((23 : ℚ) / 48)
                subsound12_103
                subsound12_104)
              (LRCompactVBoxSound.join (box := joinbox12_rRRLRRRLRLR) .k ((23 : ℚ) / 48)
                subsound12_105
                subsound12_106))
            (LRCompactVBoxSound.join (box := joinbox12_rRRLRRRLRR) .s ((13 : ℚ) / 32)
              (LRCompactVBoxSound.join (box := joinbox12_rRRLRRRLRRL) .k ((23 : ℚ) / 48)
                subsound12_107
                subsound12_108)
              (LRCompactVBoxSound.join (box := joinbox12_rRRLRRRLRRR) .k ((23 : ℚ) / 48)
                subsound12_109
                subsound12_110))))
        (LRCompactVBoxSound.join (box := joinbox12_rRRLRRRR) .k ((11 : ℚ) / 24)
          (LRCompactVBoxSound.join (box := joinbox12_rRRLRRRRL) .chi ((61 : ℚ) / 64)
            (LRCompactVBoxSound.join (box := joinbox12_rRRLRRRRLL) .s ((15 : ℚ) / 32)
              (LRCompactVBoxSound.join (box := joinbox12_rRRLRRRRLLL) .k ((7 : ℚ) / 16)
                subsound12_111
                subsound12_112)
              (LRCompactVBoxSound.join (box := joinbox12_rRRLRRRRLLR) .k ((7 : ℚ) / 16)
                subsound12_113
                subsound12_114))
            (LRCompactVBoxSound.join (box := joinbox12_rRRLRRRRLR) .s ((15 : ℚ) / 32)
              (LRCompactVBoxSound.join (box := joinbox12_rRRLRRRRLRL) .k ((7 : ℚ) / 16)
                subsound12_115
                subsound12_116)
              (LRCompactVBoxSound.join (box := joinbox12_rRRLRRRRLRR) .k ((7 : ℚ) / 16)
                subsound12_117
                subsound12_118)))
          (LRCompactVBoxSound.join (box := joinbox12_rRRLRRRRR) .chi ((61 : ℚ) / 64)
            (LRCompactVBoxSound.join (box := joinbox12_rRRLRRRRRL) .s ((15 : ℚ) / 32)
              (LRCompactVBoxSound.join (box := joinbox12_rRRLRRRRRLL) .k ((23 : ℚ) / 48)
                subsound12_119
                subsound12_120)
              (LRCompactVBoxSound.join (box := joinbox12_rRRLRRRRRLR) .k ((23 : ℚ) / 48)
                subsound12_121
                subsound12_122))
            (LRCompactVBoxSound.join (box := joinbox12_rRRLRRRRRR) .s ((15 : ℚ) / 32)
              (LRCompactVBoxSound.join (box := joinbox12_rRRLRRRRRRL) .k ((23 : ℚ) / 48)
                subsound12_123
                subsound12_124)
              (LRCompactVBoxSound.join (box := joinbox12_rRRLRRRRRRR) .k ((23 : ℚ) / 48)
                subsound12_125
                subsound12_126)))))))

end CourtadeKumar.GeneratedLRCompactVLowR
