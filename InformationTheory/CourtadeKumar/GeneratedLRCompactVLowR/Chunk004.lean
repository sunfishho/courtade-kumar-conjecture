import InformationTheory.CourtadeKumar.LRCompactVBasicReplay

/-! Frozen basic compact-V replay.
Plan SHA-256: ce3f7a498b2b9caf346dcf88ce7861f8cc091af8cd93f5624d7684e21322ecd5
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CourtadeKumar.GeneratedLRCompactVLowR

-- 66 accepted leaves below path rLRLRL.
def box4 : CertificateBox where
  sLo := ((3 : ℚ) / 8)
  sHi := ((1 : ℚ) / 2)
  kLo := ((1 : ℚ) / 3)
  kHi := ((5 : ℚ) / 12)
  chiLo := ((17 : ℚ) / 20)
  chiHi := ((71 : ℚ) / 80)


def subbox4_0 : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((1 : ℚ) / 3), ((17 : ℚ) / 48), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩

theorem checked4_0 :
    LRCompactVLeafParameters.check subbox4_0 .short = true := by decide +kernel

theorem subsound4_0 : LRCompactVBoxSound subbox4_0 :=
  LRCompactVLeafParameters.sound checked4_0


def subbox4_1 : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((17 : ℚ) / 48), ((3 : ℚ) / 8), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩

theorem checked4_1 :
    LRCompactVLeafParameters.check subbox4_1 .short = true := by decide +kernel

theorem subsound4_1 : LRCompactVBoxSound subbox4_1 :=
  LRCompactVLeafParameters.sound checked4_1


def subbox4_2 : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((1 : ℚ) / 3), ((17 : ℚ) / 48), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩

theorem checked4_2 :
    LRCompactVLeafParameters.check subbox4_2 .short = true := by decide +kernel

theorem subsound4_2 : LRCompactVBoxSound subbox4_2 :=
  LRCompactVLeafParameters.sound checked4_2


def subbox4_3 : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((17 : ℚ) / 48), ((3 : ℚ) / 8), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩

theorem checked4_3 :
    LRCompactVLeafParameters.check subbox4_3 .short = true := by decide +kernel

theorem subsound4_3 : LRCompactVBoxSound subbox4_3 :=
  LRCompactVLeafParameters.sound checked4_3


def subbox4_4 : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((1 : ℚ) / 3), ((17 : ℚ) / 48), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩

theorem checked4_4 :
    LRCompactVLeafParameters.check subbox4_4 .short = true := by decide +kernel

theorem subsound4_4 : LRCompactVBoxSound subbox4_4 :=
  LRCompactVLeafParameters.sound checked4_4


def subbox4_5 : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((17 : ℚ) / 48), ((3 : ℚ) / 8), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩

theorem checked4_5 :
    LRCompactVLeafParameters.check subbox4_5 .short = true := by decide +kernel

theorem subsound4_5 : LRCompactVBoxSound subbox4_5 :=
  LRCompactVLeafParameters.sound checked4_5


def subbox4_6 : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((1 : ℚ) / 3), ((17 : ℚ) / 48), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩

theorem checked4_6 :
    LRCompactVLeafParameters.check subbox4_6 .short = true := by decide +kernel

theorem subsound4_6 : LRCompactVBoxSound subbox4_6 :=
  LRCompactVLeafParameters.sound checked4_6


def subbox4_7 : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((17 : ℚ) / 48), ((3 : ℚ) / 8), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩

theorem checked4_7 :
    LRCompactVLeafParameters.check subbox4_7 .short = true := by decide +kernel

theorem subsound4_7 : LRCompactVBoxSound subbox4_7 :=
  LRCompactVLeafParameters.sound checked4_7


def subbox4_8 : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((3 : ℚ) / 8), ((19 : ℚ) / 48), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩

theorem checked4_8 :
    LRCompactVLeafParameters.check subbox4_8 .short = true := by decide +kernel

theorem subsound4_8 : LRCompactVBoxSound subbox4_8 :=
  LRCompactVLeafParameters.sound checked4_8


def subbox4_9 : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((19 : ℚ) / 48), ((5 : ℚ) / 12), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩

theorem checked4_9 :
    LRCompactVLeafParameters.check subbox4_9 .short = true := by decide +kernel

theorem subsound4_9 : LRCompactVBoxSound subbox4_9 :=
  LRCompactVLeafParameters.sound checked4_9


def subbox4_10 : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((3 : ℚ) / 8), ((19 : ℚ) / 48), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩

theorem checked4_10 :
    LRCompactVLeafParameters.check subbox4_10 .short = true := by decide +kernel

theorem subsound4_10 : LRCompactVBoxSound subbox4_10 :=
  LRCompactVLeafParameters.sound checked4_10


def subbox4_11 : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((19 : ℚ) / 48), ((5 : ℚ) / 12), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩

theorem checked4_11 :
    LRCompactVLeafParameters.check subbox4_11 .short = true := by decide +kernel

theorem subsound4_11 : LRCompactVBoxSound subbox4_11 :=
  LRCompactVLeafParameters.sound checked4_11


def subbox4_12 : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((3 : ℚ) / 8), ((19 : ℚ) / 48), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩

theorem checked4_12 :
    LRCompactVLeafParameters.check subbox4_12 .short = true := by decide +kernel

theorem subsound4_12 : LRCompactVBoxSound subbox4_12 :=
  LRCompactVLeafParameters.sound checked4_12


def subbox4_13 : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((19 : ℚ) / 48), ((5 : ℚ) / 12), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩

theorem checked4_13 :
    LRCompactVLeafParameters.check subbox4_13 .short = true := by decide +kernel

theorem subsound4_13 : LRCompactVBoxSound subbox4_13 :=
  LRCompactVLeafParameters.sound checked4_13


def subbox4_14 : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((3 : ℚ) / 8), ((19 : ℚ) / 48), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩

theorem checked4_14 :
    LRCompactVLeafParameters.check subbox4_14 .short = true := by decide +kernel

theorem subsound4_14 : LRCompactVBoxSound subbox4_14 :=
  LRCompactVLeafParameters.sound checked4_14


def subbox4_15 : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((19 : ℚ) / 48), ((5 : ℚ) / 12), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩

theorem checked4_15 :
    LRCompactVLeafParameters.check subbox4_15 .short = true := by decide +kernel

theorem subsound4_15 : LRCompactVBoxSound subbox4_15 :=
  LRCompactVLeafParameters.sound checked4_15


def subbox4_16 : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((1 : ℚ) / 3), ((17 : ℚ) / 48), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩

theorem checked4_16 :
    LRCompactVLeafParameters.check subbox4_16 .short = true := by decide +kernel

theorem subsound4_16 : LRCompactVBoxSound subbox4_16 :=
  LRCompactVLeafParameters.sound checked4_16


def subbox4_17 : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((17 : ℚ) / 48), ((3 : ℚ) / 8), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩

theorem checked4_17 :
    LRCompactVLeafParameters.check subbox4_17 .long = true := by decide +kernel

theorem subsound4_17 : LRCompactVBoxSound subbox4_17 :=
  LRCompactVLeafParameters.sound checked4_17


def subbox4_18 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((1 : ℚ) / 3), ((17 : ℚ) / 48), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩

theorem checked4_18 :
    LRCompactVLeafParameters.check subbox4_18 .long = true := by decide +kernel

theorem subsound4_18 : LRCompactVBoxSound subbox4_18 :=
  LRCompactVLeafParameters.sound checked4_18


def subbox4_19 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((17 : ℚ) / 48), ((3 : ℚ) / 8), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩

theorem checked4_19 :
    LRCompactVLeafParameters.check subbox4_19 .long = true := by decide +kernel

theorem subsound4_19 : LRCompactVBoxSound subbox4_19 :=
  LRCompactVLeafParameters.sound checked4_19


def subbox4_20 : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((1 : ℚ) / 3), ((17 : ℚ) / 48), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩

theorem checked4_20 :
    LRCompactVLeafParameters.check subbox4_20 .short = true := by decide +kernel

theorem subsound4_20 : LRCompactVBoxSound subbox4_20 :=
  LRCompactVLeafParameters.sound checked4_20


def subbox4_21 : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((17 : ℚ) / 48), ((3 : ℚ) / 8), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩

theorem checked4_21 :
    LRCompactVLeafParameters.check subbox4_21 .short = true := by decide +kernel

theorem subsound4_21 : LRCompactVBoxSound subbox4_21 :=
  LRCompactVLeafParameters.sound checked4_21


def subbox4_22 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((1 : ℚ) / 3), ((17 : ℚ) / 48), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩

theorem checked4_22 :
    LRCompactVLeafParameters.check subbox4_22 .long = true := by decide +kernel

theorem subsound4_22 : LRCompactVBoxSound subbox4_22 :=
  LRCompactVLeafParameters.sound checked4_22


def subbox4_23 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((17 : ℚ) / 48), ((3 : ℚ) / 8), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩

theorem checked4_23 :
    LRCompactVLeafParameters.check subbox4_23 .long = true := by decide +kernel

theorem subsound4_23 : LRCompactVBoxSound subbox4_23 :=
  LRCompactVLeafParameters.sound checked4_23


def subbox4_24 : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((3 : ℚ) / 8), ((19 : ℚ) / 48), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩

theorem checked4_24 :
    LRCompactVLeafParameters.check subbox4_24 .long = true := by decide +kernel

theorem subsound4_24 : LRCompactVBoxSound subbox4_24 :=
  LRCompactVLeafParameters.sound checked4_24


def subbox4_25 : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((19 : ℚ) / 48), ((5 : ℚ) / 12), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩

theorem checked4_25 :
    LRCompactVLeafParameters.check subbox4_25 .long = true := by decide +kernel

theorem subsound4_25 : LRCompactVBoxSound subbox4_25 :=
  LRCompactVLeafParameters.sound checked4_25


def subbox4_26 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((3 : ℚ) / 8), ((19 : ℚ) / 48), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩

theorem checked4_26 :
    LRCompactVLeafParameters.check subbox4_26 .long = true := by decide +kernel

theorem subsound4_26 : LRCompactVBoxSound subbox4_26 :=
  LRCompactVLeafParameters.sound checked4_26


def subbox4_27 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((19 : ℚ) / 48), ((5 : ℚ) / 12), ((17 : ℚ) / 20), ((547 : ℚ) / 640)⟩

theorem checked4_27 :
    LRCompactVLeafParameters.check subbox4_27 .long = true := by decide +kernel

theorem subsound4_27 : LRCompactVBoxSound subbox4_27 :=
  LRCompactVLeafParameters.sound checked4_27


def subbox4_28 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((19 : ℚ) / 48), ((5 : ℚ) / 12), ((547 : ℚ) / 640), ((55 : ℚ) / 64)⟩

theorem checked4_28 :
    LRCompactVLeafParameters.check subbox4_28 .long = true := by decide +kernel

theorem subsound4_28 : LRCompactVBoxSound subbox4_28 :=
  LRCompactVLeafParameters.sound checked4_28


def subbox4_29 : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((3 : ℚ) / 8), ((19 : ℚ) / 48), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩

theorem checked4_29 :
    LRCompactVLeafParameters.check subbox4_29 .long = true := by decide +kernel

theorem subsound4_29 : LRCompactVBoxSound subbox4_29 :=
  LRCompactVLeafParameters.sound checked4_29


def subbox4_30 : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((19 : ℚ) / 48), ((5 : ℚ) / 12), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩

theorem checked4_30 :
    LRCompactVLeafParameters.check subbox4_30 .long = true := by decide +kernel

theorem subsound4_30 : LRCompactVBoxSound subbox4_30 :=
  LRCompactVLeafParameters.sound checked4_30


def subbox4_31 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((3 : ℚ) / 8), ((19 : ℚ) / 48), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩

theorem checked4_31 :
    LRCompactVLeafParameters.check subbox4_31 .long = true := by decide +kernel

theorem subsound4_31 : LRCompactVBoxSound subbox4_31 :=
  LRCompactVLeafParameters.sound checked4_31


def subbox4_32 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((19 : ℚ) / 48), ((5 : ℚ) / 12), ((55 : ℚ) / 64), ((553 : ℚ) / 640)⟩

theorem checked4_32 :
    LRCompactVLeafParameters.check subbox4_32 .long = true := by decide +kernel

theorem subsound4_32 : LRCompactVBoxSound subbox4_32 :=
  LRCompactVLeafParameters.sound checked4_32


def subbox4_33 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((19 : ℚ) / 48), ((5 : ℚ) / 12), ((553 : ℚ) / 640), ((139 : ℚ) / 160)⟩

theorem checked4_33 :
    LRCompactVLeafParameters.check subbox4_33 .long = true := by decide +kernel

theorem subsound4_33 : LRCompactVBoxSound subbox4_33 :=
  LRCompactVLeafParameters.sound checked4_33


def subbox4_34 : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((1 : ℚ) / 3), ((17 : ℚ) / 48), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩

theorem checked4_34 :
    LRCompactVLeafParameters.check subbox4_34 .short = true := by decide +kernel

theorem subsound4_34 : LRCompactVBoxSound subbox4_34 :=
  LRCompactVLeafParameters.sound checked4_34


def subbox4_35 : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((17 : ℚ) / 48), ((3 : ℚ) / 8), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩

theorem checked4_35 :
    LRCompactVLeafParameters.check subbox4_35 .short = true := by decide +kernel

theorem subsound4_35 : LRCompactVBoxSound subbox4_35 :=
  LRCompactVLeafParameters.sound checked4_35


def subbox4_36 : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((1 : ℚ) / 3), ((17 : ℚ) / 48), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩

theorem checked4_36 :
    LRCompactVLeafParameters.check subbox4_36 .short = true := by decide +kernel

theorem subsound4_36 : LRCompactVBoxSound subbox4_36 :=
  LRCompactVLeafParameters.sound checked4_36


def subbox4_37 : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((17 : ℚ) / 48), ((3 : ℚ) / 8), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩

theorem checked4_37 :
    LRCompactVLeafParameters.check subbox4_37 .short = true := by decide +kernel

theorem subsound4_37 : LRCompactVBoxSound subbox4_37 :=
  LRCompactVLeafParameters.sound checked4_37


def subbox4_38 : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((1 : ℚ) / 3), ((17 : ℚ) / 48), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩

theorem checked4_38 :
    LRCompactVLeafParameters.check subbox4_38 .short = true := by decide +kernel

theorem subsound4_38 : LRCompactVBoxSound subbox4_38 :=
  LRCompactVLeafParameters.sound checked4_38


def subbox4_39 : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((17 : ℚ) / 48), ((3 : ℚ) / 8), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩

theorem checked4_39 :
    LRCompactVLeafParameters.check subbox4_39 .short = true := by decide +kernel

theorem subsound4_39 : LRCompactVBoxSound subbox4_39 :=
  LRCompactVLeafParameters.sound checked4_39


def subbox4_40 : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((1 : ℚ) / 3), ((17 : ℚ) / 48), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩

theorem checked4_40 :
    LRCompactVLeafParameters.check subbox4_40 .short = true := by decide +kernel

theorem subsound4_40 : LRCompactVBoxSound subbox4_40 :=
  LRCompactVLeafParameters.sound checked4_40


def subbox4_41 : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((17 : ℚ) / 48), ((3 : ℚ) / 8), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩

theorem checked4_41 :
    LRCompactVLeafParameters.check subbox4_41 .short = true := by decide +kernel

theorem subsound4_41 : LRCompactVBoxSound subbox4_41 :=
  LRCompactVLeafParameters.sound checked4_41


def subbox4_42 : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((3 : ℚ) / 8), ((19 : ℚ) / 48), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩

theorem checked4_42 :
    LRCompactVLeafParameters.check subbox4_42 .short = true := by decide +kernel

theorem subsound4_42 : LRCompactVBoxSound subbox4_42 :=
  LRCompactVLeafParameters.sound checked4_42


def subbox4_43 : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((19 : ℚ) / 48), ((5 : ℚ) / 12), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩

theorem checked4_43 :
    LRCompactVLeafParameters.check subbox4_43 .short = true := by decide +kernel

theorem subsound4_43 : LRCompactVBoxSound subbox4_43 :=
  LRCompactVLeafParameters.sound checked4_43


def subbox4_44 : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((3 : ℚ) / 8), ((19 : ℚ) / 48), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩

theorem checked4_44 :
    LRCompactVLeafParameters.check subbox4_44 .short = true := by decide +kernel

theorem subsound4_44 : LRCompactVBoxSound subbox4_44 :=
  LRCompactVLeafParameters.sound checked4_44


def subbox4_45 : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((19 : ℚ) / 48), ((5 : ℚ) / 12), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩

theorem checked4_45 :
    LRCompactVLeafParameters.check subbox4_45 .short = true := by decide +kernel

theorem subsound4_45 : LRCompactVBoxSound subbox4_45 :=
  LRCompactVLeafParameters.sound checked4_45


def subbox4_46 : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((3 : ℚ) / 8), ((19 : ℚ) / 48), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩

theorem checked4_46 :
    LRCompactVLeafParameters.check subbox4_46 .short = true := by decide +kernel

theorem subsound4_46 : LRCompactVBoxSound subbox4_46 :=
  LRCompactVLeafParameters.sound checked4_46


def subbox4_47 : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((19 : ℚ) / 48), ((5 : ℚ) / 12), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩

theorem checked4_47 :
    LRCompactVLeafParameters.check subbox4_47 .short = true := by decide +kernel

theorem subsound4_47 : LRCompactVBoxSound subbox4_47 :=
  LRCompactVLeafParameters.sound checked4_47


def subbox4_48 : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((3 : ℚ) / 8), ((19 : ℚ) / 48), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩

theorem checked4_48 :
    LRCompactVLeafParameters.check subbox4_48 .short = true := by decide +kernel

theorem subsound4_48 : LRCompactVBoxSound subbox4_48 :=
  LRCompactVLeafParameters.sound checked4_48


def subbox4_49 : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((19 : ℚ) / 48), ((5 : ℚ) / 12), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩

theorem checked4_49 :
    LRCompactVLeafParameters.check subbox4_49 .short = true := by decide +kernel

theorem subsound4_49 : LRCompactVBoxSound subbox4_49 :=
  LRCompactVLeafParameters.sound checked4_49


def subbox4_50 : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((1 : ℚ) / 3), ((17 : ℚ) / 48), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩

theorem checked4_50 :
    LRCompactVLeafParameters.check subbox4_50 .short = true := by decide +kernel

theorem subsound4_50 : LRCompactVBoxSound subbox4_50 :=
  LRCompactVLeafParameters.sound checked4_50


def subbox4_51 : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((17 : ℚ) / 48), ((3 : ℚ) / 8), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩

theorem checked4_51 :
    LRCompactVLeafParameters.check subbox4_51 .short = true := by decide +kernel

theorem subsound4_51 : LRCompactVBoxSound subbox4_51 :=
  LRCompactVLeafParameters.sound checked4_51


def subbox4_52 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((1 : ℚ) / 3), ((17 : ℚ) / 48), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩

theorem checked4_52 :
    LRCompactVLeafParameters.check subbox4_52 .long = true := by decide +kernel

theorem subsound4_52 : LRCompactVBoxSound subbox4_52 :=
  LRCompactVLeafParameters.sound checked4_52


def subbox4_53 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((17 : ℚ) / 48), ((3 : ℚ) / 8), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩

theorem checked4_53 :
    LRCompactVLeafParameters.check subbox4_53 .long = true := by decide +kernel

theorem subsound4_53 : LRCompactVBoxSound subbox4_53 :=
  LRCompactVLeafParameters.sound checked4_53


def subbox4_54 : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((1 : ℚ) / 3), ((17 : ℚ) / 48), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩

theorem checked4_54 :
    LRCompactVLeafParameters.check subbox4_54 .short = true := by decide +kernel

theorem subsound4_54 : LRCompactVBoxSound subbox4_54 :=
  LRCompactVLeafParameters.sound checked4_54


def subbox4_55 : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((17 : ℚ) / 48), ((3 : ℚ) / 8), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩

theorem checked4_55 :
    LRCompactVLeafParameters.check subbox4_55 .short = true := by decide +kernel

theorem subsound4_55 : LRCompactVBoxSound subbox4_55 :=
  LRCompactVLeafParameters.sound checked4_55


def subbox4_56 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((1 : ℚ) / 3), ((17 : ℚ) / 48), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩

theorem checked4_56 :
    LRCompactVLeafParameters.check subbox4_56 .long = true := by decide +kernel

theorem subsound4_56 : LRCompactVBoxSound subbox4_56 :=
  LRCompactVLeafParameters.sound checked4_56


def subbox4_57 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((17 : ℚ) / 48), ((3 : ℚ) / 8), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩

theorem checked4_57 :
    LRCompactVLeafParameters.check subbox4_57 .long = true := by decide +kernel

theorem subsound4_57 : LRCompactVBoxSound subbox4_57 :=
  LRCompactVLeafParameters.sound checked4_57


def subbox4_58 : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((3 : ℚ) / 8), ((19 : ℚ) / 48), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩

theorem checked4_58 :
    LRCompactVLeafParameters.check subbox4_58 .long = true := by decide +kernel

theorem subsound4_58 : LRCompactVBoxSound subbox4_58 :=
  LRCompactVLeafParameters.sound checked4_58


def subbox4_59 : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((19 : ℚ) / 48), ((5 : ℚ) / 12), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩

theorem checked4_59 :
    LRCompactVLeafParameters.check subbox4_59 .long = true := by decide +kernel

theorem subsound4_59 : LRCompactVBoxSound subbox4_59 :=
  LRCompactVLeafParameters.sound checked4_59


def subbox4_60 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((3 : ℚ) / 8), ((19 : ℚ) / 48), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩

theorem checked4_60 :
    LRCompactVLeafParameters.check subbox4_60 .long = true := by decide +kernel

theorem subsound4_60 : LRCompactVBoxSound subbox4_60 :=
  LRCompactVLeafParameters.sound checked4_60


def subbox4_61 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((19 : ℚ) / 48), ((5 : ℚ) / 12), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩

theorem checked4_61 :
    LRCompactVLeafParameters.check subbox4_61 .long = true := by decide +kernel

theorem subsound4_61 : LRCompactVBoxSound subbox4_61 :=
  LRCompactVLeafParameters.sound checked4_61


def subbox4_62 : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((3 : ℚ) / 8), ((19 : ℚ) / 48), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩

theorem checked4_62 :
    LRCompactVLeafParameters.check subbox4_62 .short = true := by decide +kernel

theorem subsound4_62 : LRCompactVBoxSound subbox4_62 :=
  LRCompactVLeafParameters.sound checked4_62


def subbox4_63 : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((19 : ℚ) / 48), ((5 : ℚ) / 12), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩

theorem checked4_63 :
    LRCompactVLeafParameters.check subbox4_63 .long = true := by decide +kernel

theorem subsound4_63 : LRCompactVBoxSound subbox4_63 :=
  LRCompactVLeafParameters.sound checked4_63


def subbox4_64 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((3 : ℚ) / 8), ((19 : ℚ) / 48), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩

theorem checked4_64 :
    LRCompactVLeafParameters.check subbox4_64 .long = true := by decide +kernel

theorem subsound4_64 : LRCompactVBoxSound subbox4_64 :=
  LRCompactVLeafParameters.sound checked4_64


def subbox4_65 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((19 : ℚ) / 48), ((5 : ℚ) / 12), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩

theorem checked4_65 :
    LRCompactVLeafParameters.check subbox4_65 .long = true := by decide +kernel

theorem subsound4_65 : LRCompactVBoxSound subbox4_65 :=
  LRCompactVLeafParameters.sound checked4_65


def joinbox4_rLRLRLL : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((1 : ℚ) / 2), ((1 : ℚ) / 3), ((5 : ℚ) / 12), ((17 : ℚ) / 20), ((139 : ℚ) / 160)⟩


def joinbox4_rLRLRLLL : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((7 : ℚ) / 16), ((1 : ℚ) / 3), ((5 : ℚ) / 12), ((17 : ℚ) / 20), ((139 : ℚ) / 160)⟩


def joinbox4_rLRLRLLLL : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((7 : ℚ) / 16), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((17 : ℚ) / 20), ((139 : ℚ) / 160)⟩


def joinbox4_rLRLRLLLLL : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((7 : ℚ) / 16), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩


def joinbox4_rLRLRLLLLLL : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩


def joinbox4_rLRLRLLLLLR : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩


def joinbox4_rLRLRLLLLR : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((7 : ℚ) / 16), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩


def joinbox4_rLRLRLLLLRL : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩


def joinbox4_rLRLRLLLLRR : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩


def joinbox4_rLRLRLLLR : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((7 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((17 : ℚ) / 20), ((139 : ℚ) / 160)⟩


def joinbox4_rLRLRLLLRL : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((7 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩


def joinbox4_rLRLRLLLRLL : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩


def joinbox4_rLRLRLLLRLR : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩


def joinbox4_rLRLRLLLRR : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((7 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩


def joinbox4_rLRLRLLLRRL : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩


def joinbox4_rLRLRLLLRRR : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩


def joinbox4_rLRLRLLR : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((1 : ℚ) / 2), ((1 : ℚ) / 3), ((5 : ℚ) / 12), ((17 : ℚ) / 20), ((139 : ℚ) / 160)⟩


def joinbox4_rLRLRLLRL : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((1 : ℚ) / 2), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((17 : ℚ) / 20), ((139 : ℚ) / 160)⟩


def joinbox4_rLRLRLLRLL : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((1 : ℚ) / 2), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩


def joinbox4_rLRLRLLRLLL : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩


def joinbox4_rLRLRLLRLLR : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩


def joinbox4_rLRLRLLRLR : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((1 : ℚ) / 2), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩


def joinbox4_rLRLRLLRLRL : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩


def joinbox4_rLRLRLLRLRR : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩


def joinbox4_rLRLRLLRR : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((1 : ℚ) / 2), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((17 : ℚ) / 20), ((139 : ℚ) / 160)⟩


def joinbox4_rLRLRLLRRL : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((1 : ℚ) / 2), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩


def joinbox4_rLRLRLLRRLL : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩


def joinbox4_rLRLRLLRRLR : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩


def joinbox4_rLRLRLLRRLRR : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((19 : ℚ) / 48), ((5 : ℚ) / 12), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩


def joinbox4_rLRLRLLRRR : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((1 : ℚ) / 2), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩


def joinbox4_rLRLRLLRRRL : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩


def joinbox4_rLRLRLLRRRR : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩


def joinbox4_rLRLRLLRRRRR : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((19 : ℚ) / 48), ((5 : ℚ) / 12), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩


def joinbox4_rLRLRLR : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((1 : ℚ) / 2), ((1 : ℚ) / 3), ((5 : ℚ) / 12), ((139 : ℚ) / 160), ((71 : ℚ) / 80)⟩


def joinbox4_rLRLRLRL : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((7 : ℚ) / 16), ((1 : ℚ) / 3), ((5 : ℚ) / 12), ((139 : ℚ) / 160), ((71 : ℚ) / 80)⟩


def joinbox4_rLRLRLRLL : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((7 : ℚ) / 16), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((139 : ℚ) / 160), ((71 : ℚ) / 80)⟩


def joinbox4_rLRLRLRLLL : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((7 : ℚ) / 16), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩


def joinbox4_rLRLRLRLLLL : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩


def joinbox4_rLRLRLRLLLR : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩


def joinbox4_rLRLRLRLLR : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((7 : ℚ) / 16), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩


def joinbox4_rLRLRLRLLRL : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩


def joinbox4_rLRLRLRLLRR : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩


def joinbox4_rLRLRLRLR : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((7 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((139 : ℚ) / 160), ((71 : ℚ) / 80)⟩


def joinbox4_rLRLRLRLRL : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((7 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩


def joinbox4_rLRLRLRLRLL : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩


def joinbox4_rLRLRLRLRLR : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩


def joinbox4_rLRLRLRLRR : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((7 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩


def joinbox4_rLRLRLRLRRL : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩


def joinbox4_rLRLRLRLRRR : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩


def joinbox4_rLRLRLRR : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((1 : ℚ) / 2), ((1 : ℚ) / 3), ((5 : ℚ) / 12), ((139 : ℚ) / 160), ((71 : ℚ) / 80)⟩


def joinbox4_rLRLRLRRL : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((1 : ℚ) / 2), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((139 : ℚ) / 160), ((71 : ℚ) / 80)⟩


def joinbox4_rLRLRLRRLL : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((1 : ℚ) / 2), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩


def joinbox4_rLRLRLRRLLL : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩


def joinbox4_rLRLRLRRLLR : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩


def joinbox4_rLRLRLRRLR : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((1 : ℚ) / 2), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩


def joinbox4_rLRLRLRRLRL : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩


def joinbox4_rLRLRLRRLRR : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩


def joinbox4_rLRLRLRRR : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((1 : ℚ) / 2), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((139 : ℚ) / 160), ((71 : ℚ) / 80)⟩


def joinbox4_rLRLRLRRRL : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((1 : ℚ) / 2), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩


def joinbox4_rLRLRLRRRLL : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩


def joinbox4_rLRLRLRRRLR : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩


def joinbox4_rLRLRLRRRR : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((1 : ℚ) / 2), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩


def joinbox4_rLRLRLRRRRL : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩


def joinbox4_rLRLRLRRRRR : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩


theorem sound4 : LRCompactVBoxSound box4 :=
  (LRCompactVBoxSound.join (box := box4) .chi ((139 : ℚ) / 160)
    (LRCompactVBoxSound.join (box := joinbox4_rLRLRLL) .s ((7 : ℚ) / 16)
      (LRCompactVBoxSound.join (box := joinbox4_rLRLRLLL) .k ((3 : ℚ) / 8)
        (LRCompactVBoxSound.join (box := joinbox4_rLRLRLLLL) .chi ((55 : ℚ) / 64)
          (LRCompactVBoxSound.join (box := joinbox4_rLRLRLLLLL) .s ((13 : ℚ) / 32)
            (LRCompactVBoxSound.join (box := joinbox4_rLRLRLLLLLL) .k ((17 : ℚ) / 48)
              subsound4_0
              subsound4_1)
            (LRCompactVBoxSound.join (box := joinbox4_rLRLRLLLLLR) .k ((17 : ℚ) / 48)
              subsound4_2
              subsound4_3))
          (LRCompactVBoxSound.join (box := joinbox4_rLRLRLLLLR) .s ((13 : ℚ) / 32)
            (LRCompactVBoxSound.join (box := joinbox4_rLRLRLLLLRL) .k ((17 : ℚ) / 48)
              subsound4_4
              subsound4_5)
            (LRCompactVBoxSound.join (box := joinbox4_rLRLRLLLLRR) .k ((17 : ℚ) / 48)
              subsound4_6
              subsound4_7)))
        (LRCompactVBoxSound.join (box := joinbox4_rLRLRLLLR) .chi ((55 : ℚ) / 64)
          (LRCompactVBoxSound.join (box := joinbox4_rLRLRLLLRL) .s ((13 : ℚ) / 32)
            (LRCompactVBoxSound.join (box := joinbox4_rLRLRLLLRLL) .k ((19 : ℚ) / 48)
              subsound4_8
              subsound4_9)
            (LRCompactVBoxSound.join (box := joinbox4_rLRLRLLLRLR) .k ((19 : ℚ) / 48)
              subsound4_10
              subsound4_11))
          (LRCompactVBoxSound.join (box := joinbox4_rLRLRLLLRR) .s ((13 : ℚ) / 32)
            (LRCompactVBoxSound.join (box := joinbox4_rLRLRLLLRRL) .k ((19 : ℚ) / 48)
              subsound4_12
              subsound4_13)
            (LRCompactVBoxSound.join (box := joinbox4_rLRLRLLLRRR) .k ((19 : ℚ) / 48)
              subsound4_14
              subsound4_15))))
      (LRCompactVBoxSound.join (box := joinbox4_rLRLRLLR) .k ((3 : ℚ) / 8)
        (LRCompactVBoxSound.join (box := joinbox4_rLRLRLLRL) .chi ((55 : ℚ) / 64)
          (LRCompactVBoxSound.join (box := joinbox4_rLRLRLLRLL) .s ((15 : ℚ) / 32)
            (LRCompactVBoxSound.join (box := joinbox4_rLRLRLLRLLL) .k ((17 : ℚ) / 48)
              subsound4_16
              subsound4_17)
            (LRCompactVBoxSound.join (box := joinbox4_rLRLRLLRLLR) .k ((17 : ℚ) / 48)
              subsound4_18
              subsound4_19))
          (LRCompactVBoxSound.join (box := joinbox4_rLRLRLLRLR) .s ((15 : ℚ) / 32)
            (LRCompactVBoxSound.join (box := joinbox4_rLRLRLLRLRL) .k ((17 : ℚ) / 48)
              subsound4_20
              subsound4_21)
            (LRCompactVBoxSound.join (box := joinbox4_rLRLRLLRLRR) .k ((17 : ℚ) / 48)
              subsound4_22
              subsound4_23)))
        (LRCompactVBoxSound.join (box := joinbox4_rLRLRLLRR) .chi ((55 : ℚ) / 64)
          (LRCompactVBoxSound.join (box := joinbox4_rLRLRLLRRL) .s ((15 : ℚ) / 32)
            (LRCompactVBoxSound.join (box := joinbox4_rLRLRLLRRLL) .k ((19 : ℚ) / 48)
              subsound4_24
              subsound4_25)
            (LRCompactVBoxSound.join (box := joinbox4_rLRLRLLRRLR) .k ((19 : ℚ) / 48)
              subsound4_26
              (LRCompactVBoxSound.join (box := joinbox4_rLRLRLLRRLRR) .chi ((547 : ℚ) / 640)
                subsound4_27
                subsound4_28)))
          (LRCompactVBoxSound.join (box := joinbox4_rLRLRLLRRR) .s ((15 : ℚ) / 32)
            (LRCompactVBoxSound.join (box := joinbox4_rLRLRLLRRRL) .k ((19 : ℚ) / 48)
              subsound4_29
              subsound4_30)
            (LRCompactVBoxSound.join (box := joinbox4_rLRLRLLRRRR) .k ((19 : ℚ) / 48)
              subsound4_31
              (LRCompactVBoxSound.join (box := joinbox4_rLRLRLLRRRRR) .chi ((553 : ℚ) / 640)
                subsound4_32
                subsound4_33))))))
    (LRCompactVBoxSound.join (box := joinbox4_rLRLRLR) .s ((7 : ℚ) / 16)
      (LRCompactVBoxSound.join (box := joinbox4_rLRLRLRL) .k ((3 : ℚ) / 8)
        (LRCompactVBoxSound.join (box := joinbox4_rLRLRLRLL) .chi ((281 : ℚ) / 320)
          (LRCompactVBoxSound.join (box := joinbox4_rLRLRLRLLL) .s ((13 : ℚ) / 32)
            (LRCompactVBoxSound.join (box := joinbox4_rLRLRLRLLLL) .k ((17 : ℚ) / 48)
              subsound4_34
              subsound4_35)
            (LRCompactVBoxSound.join (box := joinbox4_rLRLRLRLLLR) .k ((17 : ℚ) / 48)
              subsound4_36
              subsound4_37))
          (LRCompactVBoxSound.join (box := joinbox4_rLRLRLRLLR) .s ((13 : ℚ) / 32)
            (LRCompactVBoxSound.join (box := joinbox4_rLRLRLRLLRL) .k ((17 : ℚ) / 48)
              subsound4_38
              subsound4_39)
            (LRCompactVBoxSound.join (box := joinbox4_rLRLRLRLLRR) .k ((17 : ℚ) / 48)
              subsound4_40
              subsound4_41)))
        (LRCompactVBoxSound.join (box := joinbox4_rLRLRLRLR) .chi ((281 : ℚ) / 320)
          (LRCompactVBoxSound.join (box := joinbox4_rLRLRLRLRL) .s ((13 : ℚ) / 32)
            (LRCompactVBoxSound.join (box := joinbox4_rLRLRLRLRLL) .k ((19 : ℚ) / 48)
              subsound4_42
              subsound4_43)
            (LRCompactVBoxSound.join (box := joinbox4_rLRLRLRLRLR) .k ((19 : ℚ) / 48)
              subsound4_44
              subsound4_45))
          (LRCompactVBoxSound.join (box := joinbox4_rLRLRLRLRR) .s ((13 : ℚ) / 32)
            (LRCompactVBoxSound.join (box := joinbox4_rLRLRLRLRRL) .k ((19 : ℚ) / 48)
              subsound4_46
              subsound4_47)
            (LRCompactVBoxSound.join (box := joinbox4_rLRLRLRLRRR) .k ((19 : ℚ) / 48)
              subsound4_48
              subsound4_49))))
      (LRCompactVBoxSound.join (box := joinbox4_rLRLRLRR) .k ((3 : ℚ) / 8)
        (LRCompactVBoxSound.join (box := joinbox4_rLRLRLRRL) .chi ((281 : ℚ) / 320)
          (LRCompactVBoxSound.join (box := joinbox4_rLRLRLRRLL) .s ((15 : ℚ) / 32)
            (LRCompactVBoxSound.join (box := joinbox4_rLRLRLRRLLL) .k ((17 : ℚ) / 48)
              subsound4_50
              subsound4_51)
            (LRCompactVBoxSound.join (box := joinbox4_rLRLRLRRLLR) .k ((17 : ℚ) / 48)
              subsound4_52
              subsound4_53))
          (LRCompactVBoxSound.join (box := joinbox4_rLRLRLRRLR) .s ((15 : ℚ) / 32)
            (LRCompactVBoxSound.join (box := joinbox4_rLRLRLRRLRL) .k ((17 : ℚ) / 48)
              subsound4_54
              subsound4_55)
            (LRCompactVBoxSound.join (box := joinbox4_rLRLRLRRLRR) .k ((17 : ℚ) / 48)
              subsound4_56
              subsound4_57)))
        (LRCompactVBoxSound.join (box := joinbox4_rLRLRLRRR) .chi ((281 : ℚ) / 320)
          (LRCompactVBoxSound.join (box := joinbox4_rLRLRLRRRL) .s ((15 : ℚ) / 32)
            (LRCompactVBoxSound.join (box := joinbox4_rLRLRLRRRLL) .k ((19 : ℚ) / 48)
              subsound4_58
              subsound4_59)
            (LRCompactVBoxSound.join (box := joinbox4_rLRLRLRRRLR) .k ((19 : ℚ) / 48)
              subsound4_60
              subsound4_61))
          (LRCompactVBoxSound.join (box := joinbox4_rLRLRLRRRR) .s ((15 : ℚ) / 32)
            (LRCompactVBoxSound.join (box := joinbox4_rLRLRLRRRRL) .k ((19 : ℚ) / 48)
              subsound4_62
              subsound4_63)
            (LRCompactVBoxSound.join (box := joinbox4_rLRLRLRRRRR) .k ((19 : ℚ) / 48)
              subsound4_64
              subsound4_65))))))

end CourtadeKumar.GeneratedLRCompactVLowR
