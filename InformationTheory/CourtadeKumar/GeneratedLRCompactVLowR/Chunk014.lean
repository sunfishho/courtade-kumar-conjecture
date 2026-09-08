import InformationTheory.CourtadeKumar.LRCompactVBasicReplay

/-! Frozen basic compact-V replay.
Plan SHA-256: ce3f7a498b2b9caf346dcf88ce7861f8cc091af8cd93f5624d7684e21322ecd5
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CourtadeKumar.GeneratedLRCompactVLowR

-- 110 accepted leaves below path rRRRR.
def box14 : CertificateBox where
  sLo := ((3 : ℚ) / 8)
  sHi := ((1 : ℚ) / 2)
  kLo := ((1 : ℚ) / 3)
  kHi := ((1 : ℚ) / 2)
  chiLo := ((77 : ℚ) / 80)
  chiHi := (1 : ℚ)


def subbox14_0 : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((77 : ℚ) / 80), ((311 : ℚ) / 320)⟩

theorem checked14_0 :
    LRCompactVLeafParameters.check subbox14_0 .long = true := by decide +kernel

theorem subsound14_0 : LRCompactVBoxSound subbox14_0 :=
  LRCompactVLeafParameters.sound checked14_0


def subbox14_1 : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((77 : ℚ) / 80), ((311 : ℚ) / 320)⟩

theorem checked14_1 :
    LRCompactVLeafParameters.check subbox14_1 .long = true := by decide +kernel

theorem subsound14_1 : LRCompactVBoxSound subbox14_1 :=
  LRCompactVLeafParameters.sound checked14_1


def subbox14_2 : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((311 : ℚ) / 320), ((157 : ℚ) / 160)⟩

theorem checked14_2 :
    LRCompactVLeafParameters.check subbox14_2 .long = true := by decide +kernel

theorem subsound14_2 : LRCompactVBoxSound subbox14_2 :=
  LRCompactVLeafParameters.sound checked14_2


def subbox14_3 : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((311 : ℚ) / 320), ((157 : ℚ) / 160)⟩

theorem checked14_3 :
    LRCompactVLeafParameters.check subbox14_3 .long = true := by decide +kernel

theorem subsound14_3 : LRCompactVBoxSound subbox14_3 :=
  LRCompactVLeafParameters.sound checked14_3


def subbox14_4 : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((77 : ℚ) / 80), ((311 : ℚ) / 320)⟩

theorem checked14_4 :
    LRCompactVLeafParameters.check subbox14_4 .long = true := by decide +kernel

theorem subsound14_4 : LRCompactVBoxSound subbox14_4 :=
  LRCompactVLeafParameters.sound checked14_4


def subbox14_5 : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((3 : ℚ) / 8), ((19 : ℚ) / 48), ((77 : ℚ) / 80), ((311 : ℚ) / 320)⟩

theorem checked14_5 :
    LRCompactVLeafParameters.check subbox14_5 .short = true := by decide +kernel

theorem subsound14_5 : LRCompactVBoxSound subbox14_5 :=
  LRCompactVLeafParameters.sound checked14_5


def subbox14_6 : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((19 : ℚ) / 48), ((5 : ℚ) / 12), ((77 : ℚ) / 80), ((311 : ℚ) / 320)⟩

theorem checked14_6 :
    LRCompactVLeafParameters.check subbox14_6 .short = true := by decide +kernel

theorem subsound14_6 : LRCompactVBoxSound subbox14_6 :=
  LRCompactVLeafParameters.sound checked14_6


def subbox14_7 : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((311 : ℚ) / 320), ((157 : ℚ) / 160)⟩

theorem checked14_7 :
    LRCompactVLeafParameters.check subbox14_7 .long = true := by decide +kernel

theorem subsound14_7 : LRCompactVBoxSound subbox14_7 :=
  LRCompactVLeafParameters.sound checked14_7


def subbox14_8 : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((3 : ℚ) / 8), ((19 : ℚ) / 48), ((311 : ℚ) / 320), ((157 : ℚ) / 160)⟩

theorem checked14_8 :
    LRCompactVLeafParameters.check subbox14_8 .short = true := by decide +kernel

theorem subsound14_8 : LRCompactVBoxSound subbox14_8 :=
  LRCompactVLeafParameters.sound checked14_8


def subbox14_9 : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((19 : ℚ) / 48), ((5 : ℚ) / 12), ((311 : ℚ) / 320), ((157 : ℚ) / 160)⟩

theorem checked14_9 :
    LRCompactVLeafParameters.check subbox14_9 .short = true := by decide +kernel

theorem subsound14_9 : LRCompactVBoxSound subbox14_9 :=
  LRCompactVLeafParameters.sound checked14_9


def subbox14_10 : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((1 : ℚ) / 3), ((17 : ℚ) / 48), ((77 : ℚ) / 80), ((311 : ℚ) / 320)⟩

theorem checked14_10 :
    LRCompactVLeafParameters.check subbox14_10 .short = true := by decide +kernel

theorem subsound14_10 : LRCompactVBoxSound subbox14_10 :=
  LRCompactVLeafParameters.sound checked14_10


def subbox14_11 : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((17 : ℚ) / 48), ((3 : ℚ) / 8), ((77 : ℚ) / 80), ((311 : ℚ) / 320)⟩

theorem checked14_11 :
    LRCompactVLeafParameters.check subbox14_11 .short = true := by decide +kernel

theorem subsound14_11 : LRCompactVBoxSound subbox14_11 :=
  LRCompactVLeafParameters.sound checked14_11


def subbox14_12 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((1 : ℚ) / 3), ((17 : ℚ) / 48), ((77 : ℚ) / 80), ((311 : ℚ) / 320)⟩

theorem checked14_12 :
    LRCompactVLeafParameters.check subbox14_12 .short = true := by decide +kernel

theorem subsound14_12 : LRCompactVBoxSound subbox14_12 :=
  LRCompactVLeafParameters.sound checked14_12


def subbox14_13 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((17 : ℚ) / 48), ((3 : ℚ) / 8), ((77 : ℚ) / 80), ((311 : ℚ) / 320)⟩

theorem checked14_13 :
    LRCompactVLeafParameters.check subbox14_13 .short = true := by decide +kernel

theorem subsound14_13 : LRCompactVBoxSound subbox14_13 :=
  LRCompactVLeafParameters.sound checked14_13


def subbox14_14 : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((1 : ℚ) / 3), ((17 : ℚ) / 48), ((311 : ℚ) / 320), ((157 : ℚ) / 160)⟩

theorem checked14_14 :
    LRCompactVLeafParameters.check subbox14_14 .short = true := by decide +kernel

theorem subsound14_14 : LRCompactVBoxSound subbox14_14 :=
  LRCompactVLeafParameters.sound checked14_14


def subbox14_15 : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((17 : ℚ) / 48), ((3 : ℚ) / 8), ((311 : ℚ) / 320), ((157 : ℚ) / 160)⟩

theorem checked14_15 :
    LRCompactVLeafParameters.check subbox14_15 .short = true := by decide +kernel

theorem subsound14_15 : LRCompactVBoxSound subbox14_15 :=
  LRCompactVLeafParameters.sound checked14_15


def subbox14_16 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((1 : ℚ) / 3), ((17 : ℚ) / 48), ((311 : ℚ) / 320), ((157 : ℚ) / 160)⟩

theorem checked14_16 :
    LRCompactVLeafParameters.check subbox14_16 .short = true := by decide +kernel

theorem subsound14_16 : LRCompactVBoxSound subbox14_16 :=
  LRCompactVLeafParameters.sound checked14_16


def subbox14_17 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((17 : ℚ) / 48), ((3 : ℚ) / 8), ((311 : ℚ) / 320), ((157 : ℚ) / 160)⟩

theorem checked14_17 :
    LRCompactVLeafParameters.check subbox14_17 .short = true := by decide +kernel

theorem subsound14_17 : LRCompactVBoxSound subbox14_17 :=
  LRCompactVLeafParameters.sound checked14_17


def subbox14_18 : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((3 : ℚ) / 8), ((19 : ℚ) / 48), ((77 : ℚ) / 80), ((311 : ℚ) / 320)⟩

theorem checked14_18 :
    LRCompactVLeafParameters.check subbox14_18 .short = true := by decide +kernel

theorem subsound14_18 : LRCompactVBoxSound subbox14_18 :=
  LRCompactVLeafParameters.sound checked14_18


def subbox14_19 : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((19 : ℚ) / 48), ((5 : ℚ) / 12), ((77 : ℚ) / 80), ((311 : ℚ) / 320)⟩

theorem checked14_19 :
    LRCompactVLeafParameters.check subbox14_19 .short = true := by decide +kernel

theorem subsound14_19 : LRCompactVBoxSound subbox14_19 :=
  LRCompactVLeafParameters.sound checked14_19


def subbox14_20 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((3 : ℚ) / 8), ((19 : ℚ) / 48), ((77 : ℚ) / 80), ((311 : ℚ) / 320)⟩

theorem checked14_20 :
    LRCompactVLeafParameters.check subbox14_20 .short = true := by decide +kernel

theorem subsound14_20 : LRCompactVBoxSound subbox14_20 :=
  LRCompactVLeafParameters.sound checked14_20


def subbox14_21 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((19 : ℚ) / 48), ((5 : ℚ) / 12), ((77 : ℚ) / 80), ((311 : ℚ) / 320)⟩

theorem checked14_21 :
    LRCompactVLeafParameters.check subbox14_21 .accurateLog = true := by decide +kernel

theorem subsound14_21 : LRCompactVBoxSound subbox14_21 :=
  LRCompactVLeafParameters.sound checked14_21


def subbox14_22 : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((3 : ℚ) / 8), ((19 : ℚ) / 48), ((311 : ℚ) / 320), ((157 : ℚ) / 160)⟩

theorem checked14_22 :
    LRCompactVLeafParameters.check subbox14_22 .short = true := by decide +kernel

theorem subsound14_22 : LRCompactVBoxSound subbox14_22 :=
  LRCompactVLeafParameters.sound checked14_22


def subbox14_23 : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((19 : ℚ) / 48), ((5 : ℚ) / 12), ((311 : ℚ) / 320), ((157 : ℚ) / 160)⟩

theorem checked14_23 :
    LRCompactVLeafParameters.check subbox14_23 .short = true := by decide +kernel

theorem subsound14_23 : LRCompactVBoxSound subbox14_23 :=
  LRCompactVLeafParameters.sound checked14_23


def subbox14_24 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((3 : ℚ) / 8), ((19 : ℚ) / 48), ((311 : ℚ) / 320), ((157 : ℚ) / 160)⟩

theorem checked14_24 :
    LRCompactVLeafParameters.check subbox14_24 .short = true := by decide +kernel

theorem subsound14_24 : LRCompactVBoxSound subbox14_24 :=
  LRCompactVLeafParameters.sound checked14_24


def subbox14_25 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((19 : ℚ) / 48), ((5 : ℚ) / 12), ((311 : ℚ) / 320), ((157 : ℚ) / 160)⟩

theorem checked14_25 :
    LRCompactVLeafParameters.check subbox14_25 .short = true := by decide +kernel

theorem subsound14_25 : LRCompactVBoxSound subbox14_25 :=
  LRCompactVLeafParameters.sound checked14_25


def subbox14_26 : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((157 : ℚ) / 160), ((317 : ℚ) / 320)⟩

theorem checked14_26 :
    LRCompactVLeafParameters.check subbox14_26 .accurateLog = true := by decide +kernel

theorem subsound14_26 : LRCompactVBoxSound subbox14_26 :=
  LRCompactVLeafParameters.sound checked14_26


def subbox14_27 : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((157 : ℚ) / 160), ((317 : ℚ) / 320)⟩

theorem checked14_27 :
    LRCompactVLeafParameters.check subbox14_27 .long = true := by decide +kernel

theorem subsound14_27 : LRCompactVBoxSound subbox14_27 :=
  LRCompactVLeafParameters.sound checked14_27


def subbox14_28 : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((317 : ℚ) / 320), (1 : ℚ)⟩

theorem checked14_28 :
    LRCompactVLeafParameters.check subbox14_28 .short = true := by decide +kernel

theorem subsound14_28 : LRCompactVBoxSound subbox14_28 :=
  LRCompactVLeafParameters.sound checked14_28


def subbox14_29 : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((317 : ℚ) / 320), (1 : ℚ)⟩

theorem checked14_29 :
    LRCompactVLeafParameters.check subbox14_29 .long = true := by decide +kernel

theorem subsound14_29 : LRCompactVBoxSound subbox14_29 :=
  LRCompactVLeafParameters.sound checked14_29


def subbox14_30 : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((157 : ℚ) / 160), ((317 : ℚ) / 320)⟩

theorem checked14_30 :
    LRCompactVLeafParameters.check subbox14_30 .long = true := by decide +kernel

theorem subsound14_30 : LRCompactVBoxSound subbox14_30 :=
  LRCompactVLeafParameters.sound checked14_30


def subbox14_31 : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((157 : ℚ) / 160), ((317 : ℚ) / 320)⟩

theorem checked14_31 :
    LRCompactVLeafParameters.check subbox14_31 .long = true := by decide +kernel

theorem subsound14_31 : LRCompactVBoxSound subbox14_31 :=
  LRCompactVLeafParameters.sound checked14_31


def subbox14_32 : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((317 : ℚ) / 320), (1 : ℚ)⟩

theorem checked14_32 :
    LRCompactVLeafParameters.check subbox14_32 .long = true := by decide +kernel

theorem subsound14_32 : LRCompactVBoxSound subbox14_32 :=
  LRCompactVLeafParameters.sound checked14_32


def subbox14_33 : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((317 : ℚ) / 320), (1 : ℚ)⟩

theorem checked14_33 :
    LRCompactVLeafParameters.check subbox14_33 .long = true := by decide +kernel

theorem subsound14_33 : LRCompactVBoxSound subbox14_33 :=
  LRCompactVLeafParameters.sound checked14_33


def subbox14_34 : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((157 : ℚ) / 160), ((317 : ℚ) / 320)⟩

theorem checked14_34 :
    LRCompactVLeafParameters.check subbox14_34 .long = true := by decide +kernel

theorem subsound14_34 : LRCompactVBoxSound subbox14_34 :=
  LRCompactVLeafParameters.sound checked14_34


def subbox14_35 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((1 : ℚ) / 3), ((17 : ℚ) / 48), ((157 : ℚ) / 160), ((317 : ℚ) / 320)⟩

theorem checked14_35 :
    LRCompactVLeafParameters.check subbox14_35 .short = true := by decide +kernel

theorem subsound14_35 : LRCompactVBoxSound subbox14_35 :=
  LRCompactVLeafParameters.sound checked14_35


def subbox14_36 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((17 : ℚ) / 48), ((3 : ℚ) / 8), ((157 : ℚ) / 160), ((317 : ℚ) / 320)⟩

theorem checked14_36 :
    LRCompactVLeafParameters.check subbox14_36 .short = true := by decide +kernel

theorem subsound14_36 : LRCompactVBoxSound subbox14_36 :=
  LRCompactVLeafParameters.sound checked14_36


def subbox14_37 : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((317 : ℚ) / 320), (1 : ℚ)⟩

theorem checked14_37 :
    LRCompactVLeafParameters.check subbox14_37 .long = true := by decide +kernel

theorem subsound14_37 : LRCompactVBoxSound subbox14_37 :=
  LRCompactVLeafParameters.sound checked14_37


def subbox14_38 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((1 : ℚ) / 3), ((17 : ℚ) / 48), ((317 : ℚ) / 320), (1 : ℚ)⟩

theorem checked14_38 :
    LRCompactVLeafParameters.check subbox14_38 .short = true := by decide +kernel

theorem subsound14_38 : LRCompactVBoxSound subbox14_38 :=
  LRCompactVLeafParameters.sound checked14_38


def subbox14_39 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((17 : ℚ) / 48), ((3 : ℚ) / 8), ((317 : ℚ) / 320), (1 : ℚ)⟩

theorem checked14_39 :
    LRCompactVLeafParameters.check subbox14_39 .short = true := by decide +kernel

theorem subsound14_39 : LRCompactVBoxSound subbox14_39 :=
  LRCompactVLeafParameters.sound checked14_39


def subbox14_40 : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((3 : ℚ) / 8), ((19 : ℚ) / 48), ((157 : ℚ) / 160), ((317 : ℚ) / 320)⟩

theorem checked14_40 :
    LRCompactVLeafParameters.check subbox14_40 .short = true := by decide +kernel

theorem subsound14_40 : LRCompactVBoxSound subbox14_40 :=
  LRCompactVLeafParameters.sound checked14_40


def subbox14_41 : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((19 : ℚ) / 48), ((5 : ℚ) / 12), ((157 : ℚ) / 160), ((317 : ℚ) / 320)⟩

theorem checked14_41 :
    LRCompactVLeafParameters.check subbox14_41 .short = true := by decide +kernel

theorem subsound14_41 : LRCompactVBoxSound subbox14_41 :=
  LRCompactVLeafParameters.sound checked14_41


def subbox14_42 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((3 : ℚ) / 8), ((19 : ℚ) / 48), ((157 : ℚ) / 160), ((317 : ℚ) / 320)⟩

theorem checked14_42 :
    LRCompactVLeafParameters.check subbox14_42 .short = true := by decide +kernel

theorem subsound14_42 : LRCompactVBoxSound subbox14_42 :=
  LRCompactVLeafParameters.sound checked14_42


def subbox14_43 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((19 : ℚ) / 48), ((5 : ℚ) / 12), ((157 : ℚ) / 160), ((317 : ℚ) / 320)⟩

theorem checked14_43 :
    LRCompactVLeafParameters.check subbox14_43 .short = true := by decide +kernel

theorem subsound14_43 : LRCompactVBoxSound subbox14_43 :=
  LRCompactVLeafParameters.sound checked14_43


def subbox14_44 : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((3 : ℚ) / 8), ((19 : ℚ) / 48), ((317 : ℚ) / 320), (1 : ℚ)⟩

theorem checked14_44 :
    LRCompactVLeafParameters.check subbox14_44 .short = true := by decide +kernel

theorem subsound14_44 : LRCompactVBoxSound subbox14_44 :=
  LRCompactVLeafParameters.sound checked14_44


def subbox14_45 : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((19 : ℚ) / 48), ((5 : ℚ) / 12), ((317 : ℚ) / 320), (1 : ℚ)⟩

theorem checked14_45 :
    LRCompactVLeafParameters.check subbox14_45 .short = true := by decide +kernel

theorem subsound14_45 : LRCompactVBoxSound subbox14_45 :=
  LRCompactVLeafParameters.sound checked14_45


def subbox14_46 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((3 : ℚ) / 8), ((19 : ℚ) / 48), ((317 : ℚ) / 320), (1 : ℚ)⟩

theorem checked14_46 :
    LRCompactVLeafParameters.check subbox14_46 .short = true := by decide +kernel

theorem subsound14_46 : LRCompactVBoxSound subbox14_46 :=
  LRCompactVLeafParameters.sound checked14_46


def subbox14_47 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((19 : ℚ) / 48), ((5 : ℚ) / 12), ((317 : ℚ) / 320), (1 : ℚ)⟩

theorem checked14_47 :
    LRCompactVLeafParameters.check subbox14_47 .short = true := by decide +kernel

theorem subsound14_47 : LRCompactVBoxSound subbox14_47 :=
  LRCompactVLeafParameters.sound checked14_47


def subbox14_48 : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((5 : ℚ) / 12), ((7 : ℚ) / 16), ((77 : ℚ) / 80), ((311 : ℚ) / 320)⟩

theorem checked14_48 :
    LRCompactVLeafParameters.check subbox14_48 .short = true := by decide +kernel

theorem subsound14_48 : LRCompactVBoxSound subbox14_48 :=
  LRCompactVLeafParameters.sound checked14_48


def subbox14_49 : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((77 : ℚ) / 80), ((311 : ℚ) / 320)⟩

theorem checked14_49 :
    LRCompactVLeafParameters.check subbox14_49 .short = true := by decide +kernel

theorem subsound14_49 : LRCompactVBoxSound subbox14_49 :=
  LRCompactVLeafParameters.sound checked14_49


def subbox14_50 : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((5 : ℚ) / 12), ((7 : ℚ) / 16), ((77 : ℚ) / 80), ((311 : ℚ) / 320)⟩

theorem checked14_50 :
    LRCompactVLeafParameters.check subbox14_50 .short = true := by decide +kernel

theorem subsound14_50 : LRCompactVBoxSound subbox14_50 :=
  LRCompactVLeafParameters.sound checked14_50


def subbox14_51 : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((77 : ℚ) / 80), ((311 : ℚ) / 320)⟩

theorem checked14_51 :
    LRCompactVLeafParameters.check subbox14_51 .short = true := by decide +kernel

theorem subsound14_51 : LRCompactVBoxSound subbox14_51 :=
  LRCompactVLeafParameters.sound checked14_51


def subbox14_52 : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((5 : ℚ) / 12), ((7 : ℚ) / 16), ((311 : ℚ) / 320), ((157 : ℚ) / 160)⟩

theorem checked14_52 :
    LRCompactVLeafParameters.check subbox14_52 .short = true := by decide +kernel

theorem subsound14_52 : LRCompactVBoxSound subbox14_52 :=
  LRCompactVLeafParameters.sound checked14_52


def subbox14_53 : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((311 : ℚ) / 320), ((157 : ℚ) / 160)⟩

theorem checked14_53 :
    LRCompactVLeafParameters.check subbox14_53 .short = true := by decide +kernel

theorem subsound14_53 : LRCompactVBoxSound subbox14_53 :=
  LRCompactVLeafParameters.sound checked14_53


def subbox14_54 : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((5 : ℚ) / 12), ((7 : ℚ) / 16), ((311 : ℚ) / 320), ((157 : ℚ) / 160)⟩

theorem checked14_54 :
    LRCompactVLeafParameters.check subbox14_54 .short = true := by decide +kernel

theorem subsound14_54 : LRCompactVBoxSound subbox14_54 :=
  LRCompactVLeafParameters.sound checked14_54


def subbox14_55 : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((311 : ℚ) / 320), ((157 : ℚ) / 160)⟩

theorem checked14_55 :
    LRCompactVLeafParameters.check subbox14_55 .short = true := by decide +kernel

theorem subsound14_55 : LRCompactVBoxSound subbox14_55 :=
  LRCompactVLeafParameters.sound checked14_55


def subbox14_56 : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((77 : ℚ) / 80), ((311 : ℚ) / 320)⟩

theorem checked14_56 :
    LRCompactVLeafParameters.check subbox14_56 .short = true := by decide +kernel

theorem subsound14_56 : LRCompactVBoxSound subbox14_56 :=
  LRCompactVLeafParameters.sound checked14_56


def subbox14_57 : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((77 : ℚ) / 80), ((311 : ℚ) / 320)⟩

theorem checked14_57 :
    LRCompactVLeafParameters.check subbox14_57 .short = true := by decide +kernel

theorem subsound14_57 : LRCompactVBoxSound subbox14_57 :=
  LRCompactVLeafParameters.sound checked14_57


def subbox14_58 : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((77 : ℚ) / 80), ((311 : ℚ) / 320)⟩

theorem checked14_58 :
    LRCompactVLeafParameters.check subbox14_58 .short = true := by decide +kernel

theorem subsound14_58 : LRCompactVBoxSound subbox14_58 :=
  LRCompactVLeafParameters.sound checked14_58


def subbox14_59 : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((77 : ℚ) / 80), ((311 : ℚ) / 320)⟩

theorem checked14_59 :
    LRCompactVLeafParameters.check subbox14_59 .short = true := by decide +kernel

theorem subsound14_59 : LRCompactVBoxSound subbox14_59 :=
  LRCompactVLeafParameters.sound checked14_59


def subbox14_60 : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((311 : ℚ) / 320), ((157 : ℚ) / 160)⟩

theorem checked14_60 :
    LRCompactVLeafParameters.check subbox14_60 .short = true := by decide +kernel

theorem subsound14_60 : LRCompactVBoxSound subbox14_60 :=
  LRCompactVLeafParameters.sound checked14_60


def subbox14_61 : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((311 : ℚ) / 320), ((157 : ℚ) / 160)⟩

theorem checked14_61 :
    LRCompactVLeafParameters.check subbox14_61 .short = true := by decide +kernel

theorem subsound14_61 : LRCompactVBoxSound subbox14_61 :=
  LRCompactVLeafParameters.sound checked14_61


def subbox14_62 : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((311 : ℚ) / 320), ((157 : ℚ) / 160)⟩

theorem checked14_62 :
    LRCompactVLeafParameters.check subbox14_62 .short = true := by decide +kernel

theorem subsound14_62 : LRCompactVBoxSound subbox14_62 :=
  LRCompactVLeafParameters.sound checked14_62


def subbox14_63 : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((311 : ℚ) / 320), ((157 : ℚ) / 160)⟩

theorem checked14_63 :
    LRCompactVLeafParameters.check subbox14_63 .short = true := by decide +kernel

theorem subsound14_63 : LRCompactVBoxSound subbox14_63 :=
  LRCompactVLeafParameters.sound checked14_63


def subbox14_64 : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((5 : ℚ) / 12), ((7 : ℚ) / 16), ((77 : ℚ) / 80), ((311 : ℚ) / 320)⟩

theorem checked14_64 :
    LRCompactVLeafParameters.check subbox14_64 .short = true := by decide +kernel

theorem subsound14_64 : LRCompactVBoxSound subbox14_64 :=
  LRCompactVLeafParameters.sound checked14_64


def subbox14_65 : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((77 : ℚ) / 80), ((311 : ℚ) / 320)⟩

theorem checked14_65 :
    LRCompactVLeafParameters.check subbox14_65 .short = true := by decide +kernel

theorem subsound14_65 : LRCompactVBoxSound subbox14_65 :=
  LRCompactVLeafParameters.sound checked14_65


def subbox14_66 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((5 : ℚ) / 12), ((7 : ℚ) / 16), ((77 : ℚ) / 80), ((311 : ℚ) / 320)⟩

theorem checked14_66 :
    LRCompactVLeafParameters.check subbox14_66 .long = true := by decide +kernel

theorem subsound14_66 : LRCompactVBoxSound subbox14_66 :=
  LRCompactVLeafParameters.sound checked14_66


def subbox14_67 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((77 : ℚ) / 80), ((311 : ℚ) / 320)⟩

theorem checked14_67 :
    LRCompactVLeafParameters.check subbox14_67 .long = true := by decide +kernel

theorem subsound14_67 : LRCompactVBoxSound subbox14_67 :=
  LRCompactVLeafParameters.sound checked14_67


def subbox14_68 : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((5 : ℚ) / 12), ((7 : ℚ) / 16), ((311 : ℚ) / 320), ((157 : ℚ) / 160)⟩

theorem checked14_68 :
    LRCompactVLeafParameters.check subbox14_68 .short = true := by decide +kernel

theorem subsound14_68 : LRCompactVBoxSound subbox14_68 :=
  LRCompactVLeafParameters.sound checked14_68


def subbox14_69 : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((311 : ℚ) / 320), ((157 : ℚ) / 160)⟩

theorem checked14_69 :
    LRCompactVLeafParameters.check subbox14_69 .short = true := by decide +kernel

theorem subsound14_69 : LRCompactVBoxSound subbox14_69 :=
  LRCompactVLeafParameters.sound checked14_69


def subbox14_70 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((5 : ℚ) / 12), ((7 : ℚ) / 16), ((311 : ℚ) / 320), ((157 : ℚ) / 160)⟩

theorem checked14_70 :
    LRCompactVLeafParameters.check subbox14_70 .long = true := by decide +kernel

theorem subsound14_70 : LRCompactVBoxSound subbox14_70 :=
  LRCompactVLeafParameters.sound checked14_70


def subbox14_71 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((311 : ℚ) / 320), ((157 : ℚ) / 160)⟩

theorem checked14_71 :
    LRCompactVLeafParameters.check subbox14_71 .long = true := by decide +kernel

theorem subsound14_71 : LRCompactVBoxSound subbox14_71 :=
  LRCompactVLeafParameters.sound checked14_71


def subbox14_72 : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((77 : ℚ) / 80), ((311 : ℚ) / 320)⟩

theorem checked14_72 :
    LRCompactVLeafParameters.check subbox14_72 .long = true := by decide +kernel

theorem subsound14_72 : LRCompactVBoxSound subbox14_72 :=
  LRCompactVLeafParameters.sound checked14_72


def subbox14_73 : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((77 : ℚ) / 80), ((311 : ℚ) / 320)⟩

theorem checked14_73 :
    LRCompactVLeafParameters.check subbox14_73 .long = true := by decide +kernel

theorem subsound14_73 : LRCompactVBoxSound subbox14_73 :=
  LRCompactVLeafParameters.sound checked14_73


def subbox14_74 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((77 : ℚ) / 80), ((311 : ℚ) / 320)⟩

theorem checked14_74 :
    LRCompactVLeafParameters.check subbox14_74 .long = true := by decide +kernel

theorem subsound14_74 : LRCompactVBoxSound subbox14_74 :=
  LRCompactVLeafParameters.sound checked14_74


def subbox14_75 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((77 : ℚ) / 80), ((311 : ℚ) / 320)⟩

theorem checked14_75 :
    LRCompactVLeafParameters.check subbox14_75 .long = true := by decide +kernel

theorem subsound14_75 : LRCompactVBoxSound subbox14_75 :=
  LRCompactVLeafParameters.sound checked14_75


def subbox14_76 : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((311 : ℚ) / 320), ((157 : ℚ) / 160)⟩

theorem checked14_76 :
    LRCompactVLeafParameters.check subbox14_76 .short = true := by decide +kernel

theorem subsound14_76 : LRCompactVBoxSound subbox14_76 :=
  LRCompactVLeafParameters.sound checked14_76


def subbox14_77 : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((311 : ℚ) / 320), ((157 : ℚ) / 160)⟩

theorem checked14_77 :
    LRCompactVLeafParameters.check subbox14_77 .long = true := by decide +kernel

theorem subsound14_77 : LRCompactVBoxSound subbox14_77 :=
  LRCompactVLeafParameters.sound checked14_77


def subbox14_78 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((311 : ℚ) / 320), ((157 : ℚ) / 160)⟩

theorem checked14_78 :
    LRCompactVLeafParameters.check subbox14_78 .long = true := by decide +kernel

theorem subsound14_78 : LRCompactVBoxSound subbox14_78 :=
  LRCompactVLeafParameters.sound checked14_78


def subbox14_79 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((311 : ℚ) / 320), ((157 : ℚ) / 160)⟩

theorem checked14_79 :
    LRCompactVLeafParameters.check subbox14_79 .long = true := by decide +kernel

theorem subsound14_79 : LRCompactVBoxSound subbox14_79 :=
  LRCompactVLeafParameters.sound checked14_79


def subbox14_80 : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((157 : ℚ) / 160), ((317 : ℚ) / 320)⟩

theorem checked14_80 :
    LRCompactVLeafParameters.check subbox14_80 .long = true := by decide +kernel

theorem subsound14_80 : LRCompactVBoxSound subbox14_80 :=
  LRCompactVLeafParameters.sound checked14_80


def subbox14_81 : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((5 : ℚ) / 12), ((7 : ℚ) / 16), ((157 : ℚ) / 160), ((317 : ℚ) / 320)⟩

theorem checked14_81 :
    LRCompactVLeafParameters.check subbox14_81 .short = true := by decide +kernel

theorem subsound14_81 : LRCompactVBoxSound subbox14_81 :=
  LRCompactVLeafParameters.sound checked14_81


def subbox14_82 : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((157 : ℚ) / 160), ((317 : ℚ) / 320)⟩

theorem checked14_82 :
    LRCompactVLeafParameters.check subbox14_82 .short = true := by decide +kernel

theorem subsound14_82 : LRCompactVBoxSound subbox14_82 :=
  LRCompactVLeafParameters.sound checked14_82


def subbox14_83 : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((317 : ℚ) / 320), (1 : ℚ)⟩

theorem checked14_83 :
    LRCompactVLeafParameters.check subbox14_83 .long = true := by decide +kernel

theorem subsound14_83 : LRCompactVBoxSound subbox14_83 :=
  LRCompactVLeafParameters.sound checked14_83


def subbox14_84 : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((5 : ℚ) / 12), ((7 : ℚ) / 16), ((317 : ℚ) / 320), (1 : ℚ)⟩

theorem checked14_84 :
    LRCompactVLeafParameters.check subbox14_84 .short = true := by decide +kernel

theorem subsound14_84 : LRCompactVBoxSound subbox14_84 :=
  LRCompactVLeafParameters.sound checked14_84


def subbox14_85 : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((317 : ℚ) / 320), (1 : ℚ)⟩

theorem checked14_85 :
    LRCompactVLeafParameters.check subbox14_85 .short = true := by decide +kernel

theorem subsound14_85 : LRCompactVBoxSound subbox14_85 :=
  LRCompactVLeafParameters.sound checked14_85


def subbox14_86 : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((157 : ℚ) / 160), ((317 : ℚ) / 320)⟩

theorem checked14_86 :
    LRCompactVLeafParameters.check subbox14_86 .short = true := by decide +kernel

theorem subsound14_86 : LRCompactVBoxSound subbox14_86 :=
  LRCompactVLeafParameters.sound checked14_86


def subbox14_87 : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((157 : ℚ) / 160), ((317 : ℚ) / 320)⟩

theorem checked14_87 :
    LRCompactVLeafParameters.check subbox14_87 .short = true := by decide +kernel

theorem subsound14_87 : LRCompactVBoxSound subbox14_87 :=
  LRCompactVLeafParameters.sound checked14_87


def subbox14_88 : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((157 : ℚ) / 160), ((317 : ℚ) / 320)⟩

theorem checked14_88 :
    LRCompactVLeafParameters.check subbox14_88 .short = true := by decide +kernel

theorem subsound14_88 : LRCompactVBoxSound subbox14_88 :=
  LRCompactVLeafParameters.sound checked14_88


def subbox14_89 : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((157 : ℚ) / 160), ((317 : ℚ) / 320)⟩

theorem checked14_89 :
    LRCompactVLeafParameters.check subbox14_89 .short = true := by decide +kernel

theorem subsound14_89 : LRCompactVBoxSound subbox14_89 :=
  LRCompactVLeafParameters.sound checked14_89


def subbox14_90 : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((317 : ℚ) / 320), (1 : ℚ)⟩

theorem checked14_90 :
    LRCompactVLeafParameters.check subbox14_90 .short = true := by decide +kernel

theorem subsound14_90 : LRCompactVBoxSound subbox14_90 :=
  LRCompactVLeafParameters.sound checked14_90


def subbox14_91 : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((317 : ℚ) / 320), (1 : ℚ)⟩

theorem checked14_91 :
    LRCompactVLeafParameters.check subbox14_91 .short = true := by decide +kernel

theorem subsound14_91 : LRCompactVBoxSound subbox14_91 :=
  LRCompactVLeafParameters.sound checked14_91


def subbox14_92 : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((317 : ℚ) / 320), (1 : ℚ)⟩

theorem checked14_92 :
    LRCompactVLeafParameters.check subbox14_92 .short = true := by decide +kernel

theorem subsound14_92 : LRCompactVBoxSound subbox14_92 :=
  LRCompactVLeafParameters.sound checked14_92


def subbox14_93 : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((317 : ℚ) / 320), (1 : ℚ)⟩

theorem checked14_93 :
    LRCompactVLeafParameters.check subbox14_93 .short = true := by decide +kernel

theorem subsound14_93 : LRCompactVBoxSound subbox14_93 :=
  LRCompactVLeafParameters.sound checked14_93


def subbox14_94 : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((5 : ℚ) / 12), ((7 : ℚ) / 16), ((157 : ℚ) / 160), ((317 : ℚ) / 320)⟩

theorem checked14_94 :
    LRCompactVLeafParameters.check subbox14_94 .short = true := by decide +kernel

theorem subsound14_94 : LRCompactVBoxSound subbox14_94 :=
  LRCompactVLeafParameters.sound checked14_94


def subbox14_95 : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((157 : ℚ) / 160), ((317 : ℚ) / 320)⟩

theorem checked14_95 :
    LRCompactVLeafParameters.check subbox14_95 .short = true := by decide +kernel

theorem subsound14_95 : LRCompactVBoxSound subbox14_95 :=
  LRCompactVLeafParameters.sound checked14_95


def subbox14_96 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((5 : ℚ) / 12), ((7 : ℚ) / 16), ((157 : ℚ) / 160), ((317 : ℚ) / 320)⟩

theorem checked14_96 :
    LRCompactVLeafParameters.check subbox14_96 .long = true := by decide +kernel

theorem subsound14_96 : LRCompactVBoxSound subbox14_96 :=
  LRCompactVLeafParameters.sound checked14_96


def subbox14_97 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((157 : ℚ) / 160), ((317 : ℚ) / 320)⟩

theorem checked14_97 :
    LRCompactVLeafParameters.check subbox14_97 .long = true := by decide +kernel

theorem subsound14_97 : LRCompactVBoxSound subbox14_97 :=
  LRCompactVLeafParameters.sound checked14_97


def subbox14_98 : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((5 : ℚ) / 12), ((7 : ℚ) / 16), ((317 : ℚ) / 320), (1 : ℚ)⟩

theorem checked14_98 :
    LRCompactVLeafParameters.check subbox14_98 .short = true := by decide +kernel

theorem subsound14_98 : LRCompactVBoxSound subbox14_98 :=
  LRCompactVLeafParameters.sound checked14_98


def subbox14_99 : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((317 : ℚ) / 320), (1 : ℚ)⟩

theorem checked14_99 :
    LRCompactVLeafParameters.check subbox14_99 .short = true := by decide +kernel

theorem subsound14_99 : LRCompactVBoxSound subbox14_99 :=
  LRCompactVLeafParameters.sound checked14_99


def subbox14_100 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((5 : ℚ) / 12), ((7 : ℚ) / 16), ((317 : ℚ) / 320), (1 : ℚ)⟩

theorem checked14_100 :
    LRCompactVLeafParameters.check subbox14_100 .short = true := by decide +kernel

theorem subsound14_100 : LRCompactVBoxSound subbox14_100 :=
  LRCompactVLeafParameters.sound checked14_100


def subbox14_101 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((317 : ℚ) / 320), (1 : ℚ)⟩

theorem checked14_101 :
    LRCompactVLeafParameters.check subbox14_101 .long = true := by decide +kernel

theorem subsound14_101 : LRCompactVBoxSound subbox14_101 :=
  LRCompactVLeafParameters.sound checked14_101


def subbox14_102 : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((157 : ℚ) / 160), ((317 : ℚ) / 320)⟩

theorem checked14_102 :
    LRCompactVLeafParameters.check subbox14_102 .short = true := by decide +kernel

theorem subsound14_102 : LRCompactVBoxSound subbox14_102 :=
  LRCompactVLeafParameters.sound checked14_102


def subbox14_103 : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((157 : ℚ) / 160), ((317 : ℚ) / 320)⟩

theorem checked14_103 :
    LRCompactVLeafParameters.check subbox14_103 .long = true := by decide +kernel

theorem subsound14_103 : LRCompactVBoxSound subbox14_103 :=
  LRCompactVLeafParameters.sound checked14_103


def subbox14_104 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((157 : ℚ) / 160), ((317 : ℚ) / 320)⟩

theorem checked14_104 :
    LRCompactVLeafParameters.check subbox14_104 .long = true := by decide +kernel

theorem subsound14_104 : LRCompactVBoxSound subbox14_104 :=
  LRCompactVLeafParameters.sound checked14_104


def subbox14_105 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((157 : ℚ) / 160), ((317 : ℚ) / 320)⟩

theorem checked14_105 :
    LRCompactVLeafParameters.check subbox14_105 .long = true := by decide +kernel

theorem subsound14_105 : LRCompactVBoxSound subbox14_105 :=
  LRCompactVLeafParameters.sound checked14_105


def subbox14_106 : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((317 : ℚ) / 320), (1 : ℚ)⟩

theorem checked14_106 :
    LRCompactVLeafParameters.check subbox14_106 .short = true := by decide +kernel

theorem subsound14_106 : LRCompactVBoxSound subbox14_106 :=
  LRCompactVLeafParameters.sound checked14_106


def subbox14_107 : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((317 : ℚ) / 320), (1 : ℚ)⟩

theorem checked14_107 :
    LRCompactVLeafParameters.check subbox14_107 .long = true := by decide +kernel

theorem subsound14_107 : LRCompactVBoxSound subbox14_107 :=
  LRCompactVLeafParameters.sound checked14_107


def subbox14_108 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((317 : ℚ) / 320), (1 : ℚ)⟩

theorem checked14_108 :
    LRCompactVLeafParameters.check subbox14_108 .long = true := by decide +kernel

theorem subsound14_108 : LRCompactVBoxSound subbox14_108 :=
  LRCompactVLeafParameters.sound checked14_108


def subbox14_109 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((317 : ℚ) / 320), (1 : ℚ)⟩

theorem checked14_109 :
    LRCompactVLeafParameters.check subbox14_109 .long = true := by decide +kernel

theorem subsound14_109 : LRCompactVBoxSound subbox14_109 :=
  LRCompactVLeafParameters.sound checked14_109


def joinbox14_rRRRRL : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((1 : ℚ) / 2), ((1 : ℚ) / 3), ((5 : ℚ) / 12), ((77 : ℚ) / 80), (1 : ℚ)⟩


def joinbox14_rRRRRLL : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((1 : ℚ) / 2), ((1 : ℚ) / 3), ((5 : ℚ) / 12), ((77 : ℚ) / 80), ((157 : ℚ) / 160)⟩


def joinbox14_rRRRRLLL : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((7 : ℚ) / 16), ((1 : ℚ) / 3), ((5 : ℚ) / 12), ((77 : ℚ) / 80), ((157 : ℚ) / 160)⟩


def joinbox14_rRRRRLLLL : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((7 : ℚ) / 16), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((77 : ℚ) / 80), ((157 : ℚ) / 160)⟩


def joinbox14_rRRRRLLLLL : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((7 : ℚ) / 16), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((77 : ℚ) / 80), ((311 : ℚ) / 320)⟩


def joinbox14_rRRRRLLLLR : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((7 : ℚ) / 16), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((311 : ℚ) / 320), ((157 : ℚ) / 160)⟩


def joinbox14_rRRRRLLLR : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((7 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((77 : ℚ) / 80), ((157 : ℚ) / 160)⟩


def joinbox14_rRRRRLLLRL : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((7 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((77 : ℚ) / 80), ((311 : ℚ) / 320)⟩


def joinbox14_rRRRRLLLRLR : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((77 : ℚ) / 80), ((311 : ℚ) / 320)⟩


def joinbox14_rRRRRLLLRR : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((7 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((311 : ℚ) / 320), ((157 : ℚ) / 160)⟩


def joinbox14_rRRRRLLLRRR : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((311 : ℚ) / 320), ((157 : ℚ) / 160)⟩


def joinbox14_rRRRRLLR : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((1 : ℚ) / 2), ((1 : ℚ) / 3), ((5 : ℚ) / 12), ((77 : ℚ) / 80), ((157 : ℚ) / 160)⟩


def joinbox14_rRRRRLLRL : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((1 : ℚ) / 2), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((77 : ℚ) / 80), ((157 : ℚ) / 160)⟩


def joinbox14_rRRRRLLRLL : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((1 : ℚ) / 2), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((77 : ℚ) / 80), ((311 : ℚ) / 320)⟩


def joinbox14_rRRRRLLRLLL : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((77 : ℚ) / 80), ((311 : ℚ) / 320)⟩


def joinbox14_rRRRRLLRLLR : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((77 : ℚ) / 80), ((311 : ℚ) / 320)⟩


def joinbox14_rRRRRLLRLR : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((1 : ℚ) / 2), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((311 : ℚ) / 320), ((157 : ℚ) / 160)⟩


def joinbox14_rRRRRLLRLRL : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((311 : ℚ) / 320), ((157 : ℚ) / 160)⟩


def joinbox14_rRRRRLLRLRR : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((311 : ℚ) / 320), ((157 : ℚ) / 160)⟩


def joinbox14_rRRRRLLRR : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((1 : ℚ) / 2), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((77 : ℚ) / 80), ((157 : ℚ) / 160)⟩


def joinbox14_rRRRRLLRRL : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((1 : ℚ) / 2), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((77 : ℚ) / 80), ((311 : ℚ) / 320)⟩


def joinbox14_rRRRRLLRRLL : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((77 : ℚ) / 80), ((311 : ℚ) / 320)⟩


def joinbox14_rRRRRLLRRLR : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((77 : ℚ) / 80), ((311 : ℚ) / 320)⟩


def joinbox14_rRRRRLLRRR : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((1 : ℚ) / 2), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((311 : ℚ) / 320), ((157 : ℚ) / 160)⟩


def joinbox14_rRRRRLLRRRL : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((311 : ℚ) / 320), ((157 : ℚ) / 160)⟩


def joinbox14_rRRRRLLRRRR : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((311 : ℚ) / 320), ((157 : ℚ) / 160)⟩


def joinbox14_rRRRRLR : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((1 : ℚ) / 2), ((1 : ℚ) / 3), ((5 : ℚ) / 12), ((157 : ℚ) / 160), (1 : ℚ)⟩


def joinbox14_rRRRRLRL : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((7 : ℚ) / 16), ((1 : ℚ) / 3), ((5 : ℚ) / 12), ((157 : ℚ) / 160), (1 : ℚ)⟩


def joinbox14_rRRRRLRLL : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((7 : ℚ) / 16), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((157 : ℚ) / 160), (1 : ℚ)⟩


def joinbox14_rRRRRLRLLL : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((7 : ℚ) / 16), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((157 : ℚ) / 160), ((317 : ℚ) / 320)⟩


def joinbox14_rRRRRLRLLR : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((7 : ℚ) / 16), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((317 : ℚ) / 320), (1 : ℚ)⟩


def joinbox14_rRRRRLRLR : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((7 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((157 : ℚ) / 160), (1 : ℚ)⟩


def joinbox14_rRRRRLRLRL : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((7 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((157 : ℚ) / 160), ((317 : ℚ) / 320)⟩


def joinbox14_rRRRRLRLRR : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((7 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((317 : ℚ) / 320), (1 : ℚ)⟩


def joinbox14_rRRRRLRR : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((1 : ℚ) / 2), ((1 : ℚ) / 3), ((5 : ℚ) / 12), ((157 : ℚ) / 160), (1 : ℚ)⟩


def joinbox14_rRRRRLRRL : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((1 : ℚ) / 2), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((157 : ℚ) / 160), (1 : ℚ)⟩


def joinbox14_rRRRRLRRLL : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((1 : ℚ) / 2), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((157 : ℚ) / 160), ((317 : ℚ) / 320)⟩


def joinbox14_rRRRRLRRLLR : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((157 : ℚ) / 160), ((317 : ℚ) / 320)⟩


def joinbox14_rRRRRLRRLR : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((1 : ℚ) / 2), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((317 : ℚ) / 320), (1 : ℚ)⟩


def joinbox14_rRRRRLRRLRR : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((317 : ℚ) / 320), (1 : ℚ)⟩


def joinbox14_rRRRRLRRR : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((1 : ℚ) / 2), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((157 : ℚ) / 160), (1 : ℚ)⟩


def joinbox14_rRRRRLRRRL : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((1 : ℚ) / 2), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((157 : ℚ) / 160), ((317 : ℚ) / 320)⟩


def joinbox14_rRRRRLRRRLL : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((157 : ℚ) / 160), ((317 : ℚ) / 320)⟩


def joinbox14_rRRRRLRRRLR : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((157 : ℚ) / 160), ((317 : ℚ) / 320)⟩


def joinbox14_rRRRRLRRRR : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((1 : ℚ) / 2), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((317 : ℚ) / 320), (1 : ℚ)⟩


def joinbox14_rRRRRLRRRRL : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((317 : ℚ) / 320), (1 : ℚ)⟩


def joinbox14_rRRRRLRRRRR : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((317 : ℚ) / 320), (1 : ℚ)⟩


def joinbox14_rRRRRR : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((1 : ℚ) / 2), ((5 : ℚ) / 12), ((1 : ℚ) / 2), ((77 : ℚ) / 80), (1 : ℚ)⟩


def joinbox14_rRRRRRL : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((1 : ℚ) / 2), ((5 : ℚ) / 12), ((1 : ℚ) / 2), ((77 : ℚ) / 80), ((157 : ℚ) / 160)⟩


def joinbox14_rRRRRRLL : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((7 : ℚ) / 16), ((5 : ℚ) / 12), ((1 : ℚ) / 2), ((77 : ℚ) / 80), ((157 : ℚ) / 160)⟩


def joinbox14_rRRRRRLLL : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((7 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((77 : ℚ) / 80), ((157 : ℚ) / 160)⟩


def joinbox14_rRRRRRLLLL : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((7 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((77 : ℚ) / 80), ((311 : ℚ) / 320)⟩


def joinbox14_rRRRRRLLLLL : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((77 : ℚ) / 80), ((311 : ℚ) / 320)⟩


def joinbox14_rRRRRRLLLLR : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((77 : ℚ) / 80), ((311 : ℚ) / 320)⟩


def joinbox14_rRRRRRLLLR : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((7 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((311 : ℚ) / 320), ((157 : ℚ) / 160)⟩


def joinbox14_rRRRRRLLLRL : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((311 : ℚ) / 320), ((157 : ℚ) / 160)⟩


def joinbox14_rRRRRRLLLRR : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((311 : ℚ) / 320), ((157 : ℚ) / 160)⟩


def joinbox14_rRRRRRLLR : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((77 : ℚ) / 80), ((157 : ℚ) / 160)⟩


def joinbox14_rRRRRRLLRL : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((77 : ℚ) / 80), ((311 : ℚ) / 320)⟩


def joinbox14_rRRRRRLLRLL : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((77 : ℚ) / 80), ((311 : ℚ) / 320)⟩


def joinbox14_rRRRRRLLRLR : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((77 : ℚ) / 80), ((311 : ℚ) / 320)⟩


def joinbox14_rRRRRRLLRR : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((311 : ℚ) / 320), ((157 : ℚ) / 160)⟩


def joinbox14_rRRRRRLLRRL : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((311 : ℚ) / 320), ((157 : ℚ) / 160)⟩


def joinbox14_rRRRRRLLRRR : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((311 : ℚ) / 320), ((157 : ℚ) / 160)⟩


def joinbox14_rRRRRRLR : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((1 : ℚ) / 2), ((5 : ℚ) / 12), ((1 : ℚ) / 2), ((77 : ℚ) / 80), ((157 : ℚ) / 160)⟩


def joinbox14_rRRRRRLRL : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((1 : ℚ) / 2), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((77 : ℚ) / 80), ((157 : ℚ) / 160)⟩


def joinbox14_rRRRRRLRLL : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((1 : ℚ) / 2), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((77 : ℚ) / 80), ((311 : ℚ) / 320)⟩


def joinbox14_rRRRRRLRLLL : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((77 : ℚ) / 80), ((311 : ℚ) / 320)⟩


def joinbox14_rRRRRRLRLLR : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((77 : ℚ) / 80), ((311 : ℚ) / 320)⟩


def joinbox14_rRRRRRLRLR : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((1 : ℚ) / 2), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((311 : ℚ) / 320), ((157 : ℚ) / 160)⟩


def joinbox14_rRRRRRLRLRL : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((311 : ℚ) / 320), ((157 : ℚ) / 160)⟩


def joinbox14_rRRRRRLRLRR : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((311 : ℚ) / 320), ((157 : ℚ) / 160)⟩


def joinbox14_rRRRRRLRR : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((1 : ℚ) / 2), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((77 : ℚ) / 80), ((157 : ℚ) / 160)⟩


def joinbox14_rRRRRRLRRL : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((1 : ℚ) / 2), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((77 : ℚ) / 80), ((311 : ℚ) / 320)⟩


def joinbox14_rRRRRRLRRLL : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((77 : ℚ) / 80), ((311 : ℚ) / 320)⟩


def joinbox14_rRRRRRLRRLR : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((77 : ℚ) / 80), ((311 : ℚ) / 320)⟩


def joinbox14_rRRRRRLRRR : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((1 : ℚ) / 2), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((311 : ℚ) / 320), ((157 : ℚ) / 160)⟩


def joinbox14_rRRRRRLRRRL : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((311 : ℚ) / 320), ((157 : ℚ) / 160)⟩


def joinbox14_rRRRRRLRRRR : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((311 : ℚ) / 320), ((157 : ℚ) / 160)⟩


def joinbox14_rRRRRRR : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((1 : ℚ) / 2), ((5 : ℚ) / 12), ((1 : ℚ) / 2), ((157 : ℚ) / 160), (1 : ℚ)⟩


def joinbox14_rRRRRRRL : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((7 : ℚ) / 16), ((5 : ℚ) / 12), ((1 : ℚ) / 2), ((157 : ℚ) / 160), (1 : ℚ)⟩


def joinbox14_rRRRRRRLL : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((7 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((157 : ℚ) / 160), (1 : ℚ)⟩


def joinbox14_rRRRRRRLLL : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((7 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((157 : ℚ) / 160), ((317 : ℚ) / 320)⟩


def joinbox14_rRRRRRRLLLR : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((157 : ℚ) / 160), ((317 : ℚ) / 320)⟩


def joinbox14_rRRRRRRLLR : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((7 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((317 : ℚ) / 320), (1 : ℚ)⟩


def joinbox14_rRRRRRRLLRR : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((317 : ℚ) / 320), (1 : ℚ)⟩


def joinbox14_rRRRRRRLR : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((157 : ℚ) / 160), (1 : ℚ)⟩


def joinbox14_rRRRRRRLRL : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((157 : ℚ) / 160), ((317 : ℚ) / 320)⟩


def joinbox14_rRRRRRRLRLL : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((157 : ℚ) / 160), ((317 : ℚ) / 320)⟩


def joinbox14_rRRRRRRLRLR : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((157 : ℚ) / 160), ((317 : ℚ) / 320)⟩


def joinbox14_rRRRRRRLRR : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((317 : ℚ) / 320), (1 : ℚ)⟩


def joinbox14_rRRRRRRLRRL : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((317 : ℚ) / 320), (1 : ℚ)⟩


def joinbox14_rRRRRRRLRRR : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((317 : ℚ) / 320), (1 : ℚ)⟩


def joinbox14_rRRRRRRR : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((1 : ℚ) / 2), ((5 : ℚ) / 12), ((1 : ℚ) / 2), ((157 : ℚ) / 160), (1 : ℚ)⟩


def joinbox14_rRRRRRRRL : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((1 : ℚ) / 2), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((157 : ℚ) / 160), (1 : ℚ)⟩


def joinbox14_rRRRRRRRLL : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((1 : ℚ) / 2), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((157 : ℚ) / 160), ((317 : ℚ) / 320)⟩


def joinbox14_rRRRRRRRLLL : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((157 : ℚ) / 160), ((317 : ℚ) / 320)⟩


def joinbox14_rRRRRRRRLLR : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((157 : ℚ) / 160), ((317 : ℚ) / 320)⟩


def joinbox14_rRRRRRRRLR : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((1 : ℚ) / 2), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((317 : ℚ) / 320), (1 : ℚ)⟩


def joinbox14_rRRRRRRRLRL : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((317 : ℚ) / 320), (1 : ℚ)⟩


def joinbox14_rRRRRRRRLRR : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((317 : ℚ) / 320), (1 : ℚ)⟩


def joinbox14_rRRRRRRRR : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((1 : ℚ) / 2), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((157 : ℚ) / 160), (1 : ℚ)⟩


def joinbox14_rRRRRRRRRL : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((1 : ℚ) / 2), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((157 : ℚ) / 160), ((317 : ℚ) / 320)⟩


def joinbox14_rRRRRRRRRLL : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((157 : ℚ) / 160), ((317 : ℚ) / 320)⟩


def joinbox14_rRRRRRRRRLR : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((157 : ℚ) / 160), ((317 : ℚ) / 320)⟩


def joinbox14_rRRRRRRRRR : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((1 : ℚ) / 2), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((317 : ℚ) / 320), (1 : ℚ)⟩


def joinbox14_rRRRRRRRRRL : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((317 : ℚ) / 320), (1 : ℚ)⟩


def joinbox14_rRRRRRRRRRR : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((317 : ℚ) / 320), (1 : ℚ)⟩


theorem sound14 : LRCompactVBoxSound box14 :=
  (LRCompactVBoxSound.join (box := box14) .k ((5 : ℚ) / 12)
    (LRCompactVBoxSound.join (box := joinbox14_rRRRRL) .chi ((157 : ℚ) / 160)
      (LRCompactVBoxSound.join (box := joinbox14_rRRRRLL) .s ((7 : ℚ) / 16)
        (LRCompactVBoxSound.join (box := joinbox14_rRRRRLLL) .k ((3 : ℚ) / 8)
          (LRCompactVBoxSound.join (box := joinbox14_rRRRRLLLL) .chi ((311 : ℚ) / 320)
            (LRCompactVBoxSound.join (box := joinbox14_rRRRRLLLLL) .s ((13 : ℚ) / 32)
              subsound14_0
              subsound14_1)
            (LRCompactVBoxSound.join (box := joinbox14_rRRRRLLLLR) .s ((13 : ℚ) / 32)
              subsound14_2
              subsound14_3))
          (LRCompactVBoxSound.join (box := joinbox14_rRRRRLLLR) .chi ((311 : ℚ) / 320)
            (LRCompactVBoxSound.join (box := joinbox14_rRRRRLLLRL) .s ((13 : ℚ) / 32)
              subsound14_4
              (LRCompactVBoxSound.join (box := joinbox14_rRRRRLLLRLR) .k ((19 : ℚ) / 48)
                subsound14_5
                subsound14_6))
            (LRCompactVBoxSound.join (box := joinbox14_rRRRRLLLRR) .s ((13 : ℚ) / 32)
              subsound14_7
              (LRCompactVBoxSound.join (box := joinbox14_rRRRRLLLRRR) .k ((19 : ℚ) / 48)
                subsound14_8
                subsound14_9))))
        (LRCompactVBoxSound.join (box := joinbox14_rRRRRLLR) .k ((3 : ℚ) / 8)
          (LRCompactVBoxSound.join (box := joinbox14_rRRRRLLRL) .chi ((311 : ℚ) / 320)
            (LRCompactVBoxSound.join (box := joinbox14_rRRRRLLRLL) .s ((15 : ℚ) / 32)
              (LRCompactVBoxSound.join (box := joinbox14_rRRRRLLRLLL) .k ((17 : ℚ) / 48)
                subsound14_10
                subsound14_11)
              (LRCompactVBoxSound.join (box := joinbox14_rRRRRLLRLLR) .k ((17 : ℚ) / 48)
                subsound14_12
                subsound14_13))
            (LRCompactVBoxSound.join (box := joinbox14_rRRRRLLRLR) .s ((15 : ℚ) / 32)
              (LRCompactVBoxSound.join (box := joinbox14_rRRRRLLRLRL) .k ((17 : ℚ) / 48)
                subsound14_14
                subsound14_15)
              (LRCompactVBoxSound.join (box := joinbox14_rRRRRLLRLRR) .k ((17 : ℚ) / 48)
                subsound14_16
                subsound14_17)))
          (LRCompactVBoxSound.join (box := joinbox14_rRRRRLLRR) .chi ((311 : ℚ) / 320)
            (LRCompactVBoxSound.join (box := joinbox14_rRRRRLLRRL) .s ((15 : ℚ) / 32)
              (LRCompactVBoxSound.join (box := joinbox14_rRRRRLLRRLL) .k ((19 : ℚ) / 48)
                subsound14_18
                subsound14_19)
              (LRCompactVBoxSound.join (box := joinbox14_rRRRRLLRRLR) .k ((19 : ℚ) / 48)
                subsound14_20
                subsound14_21))
            (LRCompactVBoxSound.join (box := joinbox14_rRRRRLLRRR) .s ((15 : ℚ) / 32)
              (LRCompactVBoxSound.join (box := joinbox14_rRRRRLLRRRL) .k ((19 : ℚ) / 48)
                subsound14_22
                subsound14_23)
              (LRCompactVBoxSound.join (box := joinbox14_rRRRRLLRRRR) .k ((19 : ℚ) / 48)
                subsound14_24
                subsound14_25)))))
      (LRCompactVBoxSound.join (box := joinbox14_rRRRRLR) .s ((7 : ℚ) / 16)
        (LRCompactVBoxSound.join (box := joinbox14_rRRRRLRL) .k ((3 : ℚ) / 8)
          (LRCompactVBoxSound.join (box := joinbox14_rRRRRLRLL) .chi ((317 : ℚ) / 320)
            (LRCompactVBoxSound.join (box := joinbox14_rRRRRLRLLL) .s ((13 : ℚ) / 32)
              subsound14_26
              subsound14_27)
            (LRCompactVBoxSound.join (box := joinbox14_rRRRRLRLLR) .s ((13 : ℚ) / 32)
              subsound14_28
              subsound14_29))
          (LRCompactVBoxSound.join (box := joinbox14_rRRRRLRLR) .chi ((317 : ℚ) / 320)
            (LRCompactVBoxSound.join (box := joinbox14_rRRRRLRLRL) .s ((13 : ℚ) / 32)
              subsound14_30
              subsound14_31)
            (LRCompactVBoxSound.join (box := joinbox14_rRRRRLRLRR) .s ((13 : ℚ) / 32)
              subsound14_32
              subsound14_33)))
        (LRCompactVBoxSound.join (box := joinbox14_rRRRRLRR) .k ((3 : ℚ) / 8)
          (LRCompactVBoxSound.join (box := joinbox14_rRRRRLRRL) .chi ((317 : ℚ) / 320)
            (LRCompactVBoxSound.join (box := joinbox14_rRRRRLRRLL) .s ((15 : ℚ) / 32)
              subsound14_34
              (LRCompactVBoxSound.join (box := joinbox14_rRRRRLRRLLR) .k ((17 : ℚ) / 48)
                subsound14_35
                subsound14_36))
            (LRCompactVBoxSound.join (box := joinbox14_rRRRRLRRLR) .s ((15 : ℚ) / 32)
              subsound14_37
              (LRCompactVBoxSound.join (box := joinbox14_rRRRRLRRLRR) .k ((17 : ℚ) / 48)
                subsound14_38
                subsound14_39)))
          (LRCompactVBoxSound.join (box := joinbox14_rRRRRLRRR) .chi ((317 : ℚ) / 320)
            (LRCompactVBoxSound.join (box := joinbox14_rRRRRLRRRL) .s ((15 : ℚ) / 32)
              (LRCompactVBoxSound.join (box := joinbox14_rRRRRLRRRLL) .k ((19 : ℚ) / 48)
                subsound14_40
                subsound14_41)
              (LRCompactVBoxSound.join (box := joinbox14_rRRRRLRRRLR) .k ((19 : ℚ) / 48)
                subsound14_42
                subsound14_43))
            (LRCompactVBoxSound.join (box := joinbox14_rRRRRLRRRR) .s ((15 : ℚ) / 32)
              (LRCompactVBoxSound.join (box := joinbox14_rRRRRLRRRRL) .k ((19 : ℚ) / 48)
                subsound14_44
                subsound14_45)
              (LRCompactVBoxSound.join (box := joinbox14_rRRRRLRRRRR) .k ((19 : ℚ) / 48)
                subsound14_46
                subsound14_47))))))
    (LRCompactVBoxSound.join (box := joinbox14_rRRRRR) .chi ((157 : ℚ) / 160)
      (LRCompactVBoxSound.join (box := joinbox14_rRRRRRL) .s ((7 : ℚ) / 16)
        (LRCompactVBoxSound.join (box := joinbox14_rRRRRRLL) .k ((11 : ℚ) / 24)
          (LRCompactVBoxSound.join (box := joinbox14_rRRRRRLLL) .chi ((311 : ℚ) / 320)
            (LRCompactVBoxSound.join (box := joinbox14_rRRRRRLLLL) .s ((13 : ℚ) / 32)
              (LRCompactVBoxSound.join (box := joinbox14_rRRRRRLLLLL) .k ((7 : ℚ) / 16)
                subsound14_48
                subsound14_49)
              (LRCompactVBoxSound.join (box := joinbox14_rRRRRRLLLLR) .k ((7 : ℚ) / 16)
                subsound14_50
                subsound14_51))
            (LRCompactVBoxSound.join (box := joinbox14_rRRRRRLLLR) .s ((13 : ℚ) / 32)
              (LRCompactVBoxSound.join (box := joinbox14_rRRRRRLLLRL) .k ((7 : ℚ) / 16)
                subsound14_52
                subsound14_53)
              (LRCompactVBoxSound.join (box := joinbox14_rRRRRRLLLRR) .k ((7 : ℚ) / 16)
                subsound14_54
                subsound14_55)))
          (LRCompactVBoxSound.join (box := joinbox14_rRRRRRLLR) .chi ((311 : ℚ) / 320)
            (LRCompactVBoxSound.join (box := joinbox14_rRRRRRLLRL) .s ((13 : ℚ) / 32)
              (LRCompactVBoxSound.join (box := joinbox14_rRRRRRLLRLL) .k ((23 : ℚ) / 48)
                subsound14_56
                subsound14_57)
              (LRCompactVBoxSound.join (box := joinbox14_rRRRRRLLRLR) .k ((23 : ℚ) / 48)
                subsound14_58
                subsound14_59))
            (LRCompactVBoxSound.join (box := joinbox14_rRRRRRLLRR) .s ((13 : ℚ) / 32)
              (LRCompactVBoxSound.join (box := joinbox14_rRRRRRLLRRL) .k ((23 : ℚ) / 48)
                subsound14_60
                subsound14_61)
              (LRCompactVBoxSound.join (box := joinbox14_rRRRRRLLRRR) .k ((23 : ℚ) / 48)
                subsound14_62
                subsound14_63))))
        (LRCompactVBoxSound.join (box := joinbox14_rRRRRRLR) .k ((11 : ℚ) / 24)
          (LRCompactVBoxSound.join (box := joinbox14_rRRRRRLRL) .chi ((311 : ℚ) / 320)
            (LRCompactVBoxSound.join (box := joinbox14_rRRRRRLRLL) .s ((15 : ℚ) / 32)
              (LRCompactVBoxSound.join (box := joinbox14_rRRRRRLRLLL) .k ((7 : ℚ) / 16)
                subsound14_64
                subsound14_65)
              (LRCompactVBoxSound.join (box := joinbox14_rRRRRRLRLLR) .k ((7 : ℚ) / 16)
                subsound14_66
                subsound14_67))
            (LRCompactVBoxSound.join (box := joinbox14_rRRRRRLRLR) .s ((15 : ℚ) / 32)
              (LRCompactVBoxSound.join (box := joinbox14_rRRRRRLRLRL) .k ((7 : ℚ) / 16)
                subsound14_68
                subsound14_69)
              (LRCompactVBoxSound.join (box := joinbox14_rRRRRRLRLRR) .k ((7 : ℚ) / 16)
                subsound14_70
                subsound14_71)))
          (LRCompactVBoxSound.join (box := joinbox14_rRRRRRLRR) .chi ((311 : ℚ) / 320)
            (LRCompactVBoxSound.join (box := joinbox14_rRRRRRLRRL) .s ((15 : ℚ) / 32)
              (LRCompactVBoxSound.join (box := joinbox14_rRRRRRLRRLL) .k ((23 : ℚ) / 48)
                subsound14_72
                subsound14_73)
              (LRCompactVBoxSound.join (box := joinbox14_rRRRRRLRRLR) .k ((23 : ℚ) / 48)
                subsound14_74
                subsound14_75))
            (LRCompactVBoxSound.join (box := joinbox14_rRRRRRLRRR) .s ((15 : ℚ) / 32)
              (LRCompactVBoxSound.join (box := joinbox14_rRRRRRLRRRL) .k ((23 : ℚ) / 48)
                subsound14_76
                subsound14_77)
              (LRCompactVBoxSound.join (box := joinbox14_rRRRRRLRRRR) .k ((23 : ℚ) / 48)
                subsound14_78
                subsound14_79)))))
      (LRCompactVBoxSound.join (box := joinbox14_rRRRRRR) .s ((7 : ℚ) / 16)
        (LRCompactVBoxSound.join (box := joinbox14_rRRRRRRL) .k ((11 : ℚ) / 24)
          (LRCompactVBoxSound.join (box := joinbox14_rRRRRRRLL) .chi ((317 : ℚ) / 320)
            (LRCompactVBoxSound.join (box := joinbox14_rRRRRRRLLL) .s ((13 : ℚ) / 32)
              subsound14_80
              (LRCompactVBoxSound.join (box := joinbox14_rRRRRRRLLLR) .k ((7 : ℚ) / 16)
                subsound14_81
                subsound14_82))
            (LRCompactVBoxSound.join (box := joinbox14_rRRRRRRLLR) .s ((13 : ℚ) / 32)
              subsound14_83
              (LRCompactVBoxSound.join (box := joinbox14_rRRRRRRLLRR) .k ((7 : ℚ) / 16)
                subsound14_84
                subsound14_85)))
          (LRCompactVBoxSound.join (box := joinbox14_rRRRRRRLR) .chi ((317 : ℚ) / 320)
            (LRCompactVBoxSound.join (box := joinbox14_rRRRRRRLRL) .s ((13 : ℚ) / 32)
              (LRCompactVBoxSound.join (box := joinbox14_rRRRRRRLRLL) .k ((23 : ℚ) / 48)
                subsound14_86
                subsound14_87)
              (LRCompactVBoxSound.join (box := joinbox14_rRRRRRRLRLR) .k ((23 : ℚ) / 48)
                subsound14_88
                subsound14_89))
            (LRCompactVBoxSound.join (box := joinbox14_rRRRRRRLRR) .s ((13 : ℚ) / 32)
              (LRCompactVBoxSound.join (box := joinbox14_rRRRRRRLRRL) .k ((23 : ℚ) / 48)
                subsound14_90
                subsound14_91)
              (LRCompactVBoxSound.join (box := joinbox14_rRRRRRRLRRR) .k ((23 : ℚ) / 48)
                subsound14_92
                subsound14_93))))
        (LRCompactVBoxSound.join (box := joinbox14_rRRRRRRR) .k ((11 : ℚ) / 24)
          (LRCompactVBoxSound.join (box := joinbox14_rRRRRRRRL) .chi ((317 : ℚ) / 320)
            (LRCompactVBoxSound.join (box := joinbox14_rRRRRRRRLL) .s ((15 : ℚ) / 32)
              (LRCompactVBoxSound.join (box := joinbox14_rRRRRRRRLLL) .k ((7 : ℚ) / 16)
                subsound14_94
                subsound14_95)
              (LRCompactVBoxSound.join (box := joinbox14_rRRRRRRRLLR) .k ((7 : ℚ) / 16)
                subsound14_96
                subsound14_97))
            (LRCompactVBoxSound.join (box := joinbox14_rRRRRRRRLR) .s ((15 : ℚ) / 32)
              (LRCompactVBoxSound.join (box := joinbox14_rRRRRRRRLRL) .k ((7 : ℚ) / 16)
                subsound14_98
                subsound14_99)
              (LRCompactVBoxSound.join (box := joinbox14_rRRRRRRRLRR) .k ((7 : ℚ) / 16)
                subsound14_100
                subsound14_101)))
          (LRCompactVBoxSound.join (box := joinbox14_rRRRRRRRR) .chi ((317 : ℚ) / 320)
            (LRCompactVBoxSound.join (box := joinbox14_rRRRRRRRRL) .s ((15 : ℚ) / 32)
              (LRCompactVBoxSound.join (box := joinbox14_rRRRRRRRRLL) .k ((23 : ℚ) / 48)
                subsound14_102
                subsound14_103)
              (LRCompactVBoxSound.join (box := joinbox14_rRRRRRRRRLR) .k ((23 : ℚ) / 48)
                subsound14_104
                subsound14_105))
            (LRCompactVBoxSound.join (box := joinbox14_rRRRRRRRRR) .s ((15 : ℚ) / 32)
              (LRCompactVBoxSound.join (box := joinbox14_rRRRRRRRRRL) .k ((23 : ℚ) / 48)
                subsound14_106
                subsound14_107)
              (LRCompactVBoxSound.join (box := joinbox14_rRRRRRRRRRR) .k ((23 : ℚ) / 48)
                subsound14_108
                subsound14_109)))))))

end CourtadeKumar.GeneratedLRCompactVLowR
