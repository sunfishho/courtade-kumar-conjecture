import InformationTheory.CourtadeKumar.LRCompactVBasicReplay

/-! Frozen basic compact-V replay.
Plan SHA-256: ce3f7a498b2b9caf346dcf88ce7861f8cc091af8cd93f5624d7684e21322ecd5
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CourtadeKumar.GeneratedLRCompactVLowR

-- 86 accepted leaves below path rLRLRR.
def box5 : CertificateBox where
  sLo := ((3 : ℚ) / 8)
  sHi := ((1 : ℚ) / 2)
  kLo := ((5 : ℚ) / 12)
  kHi := ((1 : ℚ) / 2)
  chiLo := ((17 : ℚ) / 20)
  chiHi := ((71 : ℚ) / 80)


def subbox5_0 : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((5 : ℚ) / 12), ((7 : ℚ) / 16), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩

theorem checked5_0 :
    LRCompactVLeafParameters.check subbox5_0 .short = true := by decide +kernel

theorem subsound5_0 : LRCompactVBoxSound subbox5_0 :=
  LRCompactVLeafParameters.sound checked5_0


def subbox5_1 : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩

theorem checked5_1 :
    LRCompactVLeafParameters.check subbox5_1 .short = true := by decide +kernel

theorem subsound5_1 : LRCompactVBoxSound subbox5_1 :=
  LRCompactVLeafParameters.sound checked5_1


def subbox5_2 : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((5 : ℚ) / 12), ((7 : ℚ) / 16), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩

theorem checked5_2 :
    LRCompactVLeafParameters.check subbox5_2 .short = true := by decide +kernel

theorem subsound5_2 : LRCompactVBoxSound subbox5_2 :=
  LRCompactVLeafParameters.sound checked5_2


def subbox5_3 : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩

theorem checked5_3 :
    LRCompactVLeafParameters.check subbox5_3 .long = true := by decide +kernel

theorem subsound5_3 : LRCompactVBoxSound subbox5_3 :=
  LRCompactVLeafParameters.sound checked5_3


def subbox5_4 : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((5 : ℚ) / 12), ((7 : ℚ) / 16), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩

theorem checked5_4 :
    LRCompactVLeafParameters.check subbox5_4 .short = true := by decide +kernel

theorem subsound5_4 : LRCompactVBoxSound subbox5_4 :=
  LRCompactVLeafParameters.sound checked5_4


def subbox5_5 : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩

theorem checked5_5 :
    LRCompactVLeafParameters.check subbox5_5 .short = true := by decide +kernel

theorem subsound5_5 : LRCompactVBoxSound subbox5_5 :=
  LRCompactVLeafParameters.sound checked5_5


def subbox5_6 : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((5 : ℚ) / 12), ((7 : ℚ) / 16), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩

theorem checked5_6 :
    LRCompactVLeafParameters.check subbox5_6 .short = true := by decide +kernel

theorem subsound5_6 : LRCompactVBoxSound subbox5_6 :=
  LRCompactVLeafParameters.sound checked5_6


def subbox5_7 : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩

theorem checked5_7 :
    LRCompactVLeafParameters.check subbox5_7 .accurateLog = true := by decide +kernel

theorem subsound5_7 : LRCompactVBoxSound subbox5_7 :=
  LRCompactVLeafParameters.sound checked5_7


def subbox5_8 : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩

theorem checked5_8 :
    LRCompactVLeafParameters.check subbox5_8 .short = true := by decide +kernel

theorem subsound5_8 : LRCompactVBoxSound subbox5_8 :=
  LRCompactVLeafParameters.sound checked5_8


def subbox5_9 : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩

theorem checked5_9 :
    LRCompactVLeafParameters.check subbox5_9 .short = true := by decide +kernel

theorem subsound5_9 : LRCompactVBoxSound subbox5_9 :=
  LRCompactVLeafParameters.sound checked5_9


def subbox5_10 : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩

theorem checked5_10 :
    LRCompactVLeafParameters.check subbox5_10 .long = true := by decide +kernel

theorem subsound5_10 : LRCompactVBoxSound subbox5_10 :=
  LRCompactVLeafParameters.sound checked5_10


def subbox5_11 : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩

theorem checked5_11 :
    LRCompactVLeafParameters.check subbox5_11 .long = true := by decide +kernel

theorem subsound5_11 : LRCompactVBoxSound subbox5_11 :=
  LRCompactVLeafParameters.sound checked5_11


def subbox5_12 : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩

theorem checked5_12 :
    LRCompactVLeafParameters.check subbox5_12 .short = true := by decide +kernel

theorem subsound5_12 : LRCompactVBoxSound subbox5_12 :=
  LRCompactVLeafParameters.sound checked5_12


def subbox5_13 : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩

theorem checked5_13 :
    LRCompactVLeafParameters.check subbox5_13 .short = true := by decide +kernel

theorem subsound5_13 : LRCompactVBoxSound subbox5_13 :=
  LRCompactVLeafParameters.sound checked5_13


def subbox5_14 : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩

theorem checked5_14 :
    LRCompactVLeafParameters.check subbox5_14 .long = true := by decide +kernel

theorem subsound5_14 : LRCompactVBoxSound subbox5_14 :=
  LRCompactVLeafParameters.sound checked5_14


def subbox5_15 : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩

theorem checked5_15 :
    LRCompactVLeafParameters.check subbox5_15 .long = true := by decide +kernel

theorem subsound5_15 : LRCompactVBoxSound subbox5_15 :=
  LRCompactVLeafParameters.sound checked5_15


def subbox5_16 : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((5 : ℚ) / 12), ((7 : ℚ) / 16), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩

theorem checked5_16 :
    LRCompactVLeafParameters.check subbox5_16 .long = true := by decide +kernel

theorem subsound5_16 : LRCompactVBoxSound subbox5_16 :=
  LRCompactVLeafParameters.sound checked5_16


def subbox5_17 : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩

theorem checked5_17 :
    LRCompactVLeafParameters.check subbox5_17 .long = true := by decide +kernel

theorem subsound5_17 : LRCompactVBoxSound subbox5_17 :=
  LRCompactVLeafParameters.sound checked5_17


def subbox5_18 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((5 : ℚ) / 12), ((7 : ℚ) / 16), ((17 : ℚ) / 20), ((547 : ℚ) / 640)⟩

theorem checked5_18 :
    LRCompactVLeafParameters.check subbox5_18 .long = true := by decide +kernel

theorem subsound5_18 : LRCompactVBoxSound subbox5_18 :=
  LRCompactVLeafParameters.sound checked5_18


def subbox5_19 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((5 : ℚ) / 12), ((7 : ℚ) / 16), ((547 : ℚ) / 640), ((55 : ℚ) / 64)⟩

theorem checked5_19 :
    LRCompactVLeafParameters.check subbox5_19 .long = true := by decide +kernel

theorem subsound5_19 : LRCompactVBoxSound subbox5_19 :=
  LRCompactVLeafParameters.sound checked5_19


def subbox5_20 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((17 : ℚ) / 20), ((547 : ℚ) / 640)⟩

theorem checked5_20 :
    LRCompactVLeafParameters.check subbox5_20 .long = true := by decide +kernel

theorem subsound5_20 : LRCompactVBoxSound subbox5_20 :=
  LRCompactVLeafParameters.sound checked5_20


def subbox5_21 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((547 : ℚ) / 640), ((55 : ℚ) / 64)⟩

theorem checked5_21 :
    LRCompactVLeafParameters.check subbox5_21 .long = true := by decide +kernel

theorem subsound5_21 : LRCompactVBoxSound subbox5_21 :=
  LRCompactVLeafParameters.sound checked5_21


def subbox5_22 : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((5 : ℚ) / 12), ((7 : ℚ) / 16), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩

theorem checked5_22 :
    LRCompactVLeafParameters.check subbox5_22 .long = true := by decide +kernel

theorem subsound5_22 : LRCompactVBoxSound subbox5_22 :=
  LRCompactVLeafParameters.sound checked5_22


def subbox5_23 : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩

theorem checked5_23 :
    LRCompactVLeafParameters.check subbox5_23 .long = true := by decide +kernel

theorem subsound5_23 : LRCompactVBoxSound subbox5_23 :=
  LRCompactVLeafParameters.sound checked5_23


def subbox5_24 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((5 : ℚ) / 12), ((7 : ℚ) / 16), ((55 : ℚ) / 64), ((553 : ℚ) / 640)⟩

theorem checked5_24 :
    LRCompactVLeafParameters.check subbox5_24 .long = true := by decide +kernel

theorem subsound5_24 : LRCompactVBoxSound subbox5_24 :=
  LRCompactVLeafParameters.sound checked5_24


def subbox5_25 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((5 : ℚ) / 12), ((7 : ℚ) / 16), ((553 : ℚ) / 640), ((139 : ℚ) / 160)⟩

theorem checked5_25 :
    LRCompactVLeafParameters.check subbox5_25 .long = true := by decide +kernel

theorem subsound5_25 : LRCompactVBoxSound subbox5_25 :=
  LRCompactVLeafParameters.sound checked5_25


def subbox5_26 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((55 : ℚ) / 64), ((553 : ℚ) / 640)⟩

theorem checked5_26 :
    LRCompactVLeafParameters.check subbox5_26 .long = true := by decide +kernel

theorem subsound5_26 : LRCompactVBoxSound subbox5_26 :=
  LRCompactVLeafParameters.sound checked5_26


def subbox5_27 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((553 : ℚ) / 640), ((139 : ℚ) / 160)⟩

theorem checked5_27 :
    LRCompactVLeafParameters.check subbox5_27 .long = true := by decide +kernel

theorem subsound5_27 : LRCompactVBoxSound subbox5_27 :=
  LRCompactVLeafParameters.sound checked5_27


def subbox5_28 : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((17 : ℚ) / 20), ((547 : ℚ) / 640)⟩

theorem checked5_28 :
    LRCompactVLeafParameters.check subbox5_28 .long = true := by decide +kernel

theorem subsound5_28 : LRCompactVBoxSound subbox5_28 :=
  LRCompactVLeafParameters.sound checked5_28


def subbox5_29 : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((547 : ℚ) / 640), ((55 : ℚ) / 64)⟩

theorem checked5_29 :
    LRCompactVLeafParameters.check subbox5_29 .long = true := by decide +kernel

theorem subsound5_29 : LRCompactVBoxSound subbox5_29 :=
  LRCompactVLeafParameters.sound checked5_29


def subbox5_30 : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((17 : ℚ) / 20), ((547 : ℚ) / 640)⟩

theorem checked5_30 :
    LRCompactVLeafParameters.check subbox5_30 .long = true := by decide +kernel

theorem subsound5_30 : LRCompactVBoxSound subbox5_30 :=
  LRCompactVLeafParameters.sound checked5_30


def subbox5_31 : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((547 : ℚ) / 640), ((55 : ℚ) / 64)⟩

theorem checked5_31 :
    LRCompactVLeafParameters.check subbox5_31 .long = true := by decide +kernel

theorem subsound5_31 : LRCompactVBoxSound subbox5_31 :=
  LRCompactVLeafParameters.sound checked5_31


def subbox5_32 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((17 : ℚ) / 20), ((547 : ℚ) / 640)⟩

theorem checked5_32 :
    LRCompactVLeafParameters.check subbox5_32 .long = true := by decide +kernel

theorem subsound5_32 : LRCompactVBoxSound subbox5_32 :=
  LRCompactVLeafParameters.sound checked5_32


def subbox5_33 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((547 : ℚ) / 640), ((55 : ℚ) / 64)⟩

theorem checked5_33 :
    LRCompactVLeafParameters.check subbox5_33 .long = true := by decide +kernel

theorem subsound5_33 : LRCompactVBoxSound subbox5_33 :=
  LRCompactVLeafParameters.sound checked5_33


def subbox5_34 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((17 : ℚ) / 20), ((547 : ℚ) / 640)⟩

theorem checked5_34 :
    LRCompactVLeafParameters.check subbox5_34 .long = true := by decide +kernel

theorem subsound5_34 : LRCompactVBoxSound subbox5_34 :=
  LRCompactVLeafParameters.sound checked5_34


def subbox5_35 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((547 : ℚ) / 640), ((55 : ℚ) / 64)⟩

theorem checked5_35 :
    LRCompactVLeafParameters.check subbox5_35 .long = true := by decide +kernel

theorem subsound5_35 : LRCompactVBoxSound subbox5_35 :=
  LRCompactVLeafParameters.sound checked5_35


def subbox5_36 : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((55 : ℚ) / 64), ((553 : ℚ) / 640)⟩

theorem checked5_36 :
    LRCompactVLeafParameters.check subbox5_36 .accurateLog = true := by decide +kernel

theorem subsound5_36 : LRCompactVBoxSound subbox5_36 :=
  LRCompactVLeafParameters.sound checked5_36


def subbox5_37 : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((553 : ℚ) / 640), ((139 : ℚ) / 160)⟩

theorem checked5_37 :
    LRCompactVLeafParameters.check subbox5_37 .short = true := by decide +kernel

theorem subsound5_37 : LRCompactVBoxSound subbox5_37 :=
  LRCompactVLeafParameters.sound checked5_37


def subbox5_38 : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((55 : ℚ) / 64), ((553 : ℚ) / 640)⟩

theorem checked5_38 :
    LRCompactVLeafParameters.check subbox5_38 .long = true := by decide +kernel

theorem subsound5_38 : LRCompactVBoxSound subbox5_38 :=
  LRCompactVLeafParameters.sound checked5_38


def subbox5_39 : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((553 : ℚ) / 640), ((139 : ℚ) / 160)⟩

theorem checked5_39 :
    LRCompactVLeafParameters.check subbox5_39 .long = true := by decide +kernel

theorem subsound5_39 : LRCompactVBoxSound subbox5_39 :=
  LRCompactVLeafParameters.sound checked5_39


def subbox5_40 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((55 : ℚ) / 64), ((553 : ℚ) / 640)⟩

theorem checked5_40 :
    LRCompactVLeafParameters.check subbox5_40 .long = true := by decide +kernel

theorem subsound5_40 : LRCompactVBoxSound subbox5_40 :=
  LRCompactVLeafParameters.sound checked5_40


def subbox5_41 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((553 : ℚ) / 640), ((139 : ℚ) / 160)⟩

theorem checked5_41 :
    LRCompactVLeafParameters.check subbox5_41 .long = true := by decide +kernel

theorem subsound5_41 : LRCompactVBoxSound subbox5_41 :=
  LRCompactVLeafParameters.sound checked5_41


def subbox5_42 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((55 : ℚ) / 64), ((553 : ℚ) / 640)⟩

theorem checked5_42 :
    LRCompactVLeafParameters.check subbox5_42 .long = true := by decide +kernel

theorem subsound5_42 : LRCompactVBoxSound subbox5_42 :=
  LRCompactVLeafParameters.sound checked5_42


def subbox5_43 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((553 : ℚ) / 640), ((139 : ℚ) / 160)⟩

theorem checked5_43 :
    LRCompactVLeafParameters.check subbox5_43 .long = true := by decide +kernel

theorem subsound5_43 : LRCompactVBoxSound subbox5_43 :=
  LRCompactVLeafParameters.sound checked5_43


def subbox5_44 : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((5 : ℚ) / 12), ((7 : ℚ) / 16), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩

theorem checked5_44 :
    LRCompactVLeafParameters.check subbox5_44 .short = true := by decide +kernel

theorem subsound5_44 : LRCompactVBoxSound subbox5_44 :=
  LRCompactVLeafParameters.sound checked5_44


def subbox5_45 : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩

theorem checked5_45 :
    LRCompactVLeafParameters.check subbox5_45 .short = true := by decide +kernel

theorem subsound5_45 : LRCompactVBoxSound subbox5_45 :=
  LRCompactVLeafParameters.sound checked5_45


def subbox5_46 : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((5 : ℚ) / 12), ((7 : ℚ) / 16), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩

theorem checked5_46 :
    LRCompactVLeafParameters.check subbox5_46 .short = true := by decide +kernel

theorem subsound5_46 : LRCompactVBoxSound subbox5_46 :=
  LRCompactVLeafParameters.sound checked5_46


def subbox5_47 : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩

theorem checked5_47 :
    LRCompactVLeafParameters.check subbox5_47 .short = true := by decide +kernel

theorem subsound5_47 : LRCompactVBoxSound subbox5_47 :=
  LRCompactVLeafParameters.sound checked5_47


def subbox5_48 : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((5 : ℚ) / 12), ((7 : ℚ) / 16), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩

theorem checked5_48 :
    LRCompactVLeafParameters.check subbox5_48 .short = true := by decide +kernel

theorem subsound5_48 : LRCompactVBoxSound subbox5_48 :=
  LRCompactVLeafParameters.sound checked5_48


def subbox5_49 : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩

theorem checked5_49 :
    LRCompactVLeafParameters.check subbox5_49 .short = true := by decide +kernel

theorem subsound5_49 : LRCompactVBoxSound subbox5_49 :=
  LRCompactVLeafParameters.sound checked5_49


def subbox5_50 : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((5 : ℚ) / 12), ((7 : ℚ) / 16), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩

theorem checked5_50 :
    LRCompactVLeafParameters.check subbox5_50 .short = true := by decide +kernel

theorem subsound5_50 : LRCompactVBoxSound subbox5_50 :=
  LRCompactVLeafParameters.sound checked5_50


def subbox5_51 : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩

theorem checked5_51 :
    LRCompactVLeafParameters.check subbox5_51 .short = true := by decide +kernel

theorem subsound5_51 : LRCompactVBoxSound subbox5_51 :=
  LRCompactVLeafParameters.sound checked5_51


def subbox5_52 : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩

theorem checked5_52 :
    LRCompactVLeafParameters.check subbox5_52 .short = true := by decide +kernel

theorem subsound5_52 : LRCompactVBoxSound subbox5_52 :=
  LRCompactVLeafParameters.sound checked5_52


def subbox5_53 : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩

theorem checked5_53 :
    LRCompactVLeafParameters.check subbox5_53 .short = true := by decide +kernel

theorem subsound5_53 : LRCompactVBoxSound subbox5_53 :=
  LRCompactVLeafParameters.sound checked5_53


def subbox5_54 : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩

theorem checked5_54 :
    LRCompactVLeafParameters.check subbox5_54 .long = true := by decide +kernel

theorem subsound5_54 : LRCompactVBoxSound subbox5_54 :=
  LRCompactVLeafParameters.sound checked5_54


def subbox5_55 : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩

theorem checked5_55 :
    LRCompactVLeafParameters.check subbox5_55 .long = true := by decide +kernel

theorem subsound5_55 : LRCompactVBoxSound subbox5_55 :=
  LRCompactVLeafParameters.sound checked5_55


def subbox5_56 : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩

theorem checked5_56 :
    LRCompactVLeafParameters.check subbox5_56 .short = true := by decide +kernel

theorem subsound5_56 : LRCompactVBoxSound subbox5_56 :=
  LRCompactVLeafParameters.sound checked5_56


def subbox5_57 : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩

theorem checked5_57 :
    LRCompactVLeafParameters.check subbox5_57 .short = true := by decide +kernel

theorem subsound5_57 : LRCompactVBoxSound subbox5_57 :=
  LRCompactVLeafParameters.sound checked5_57


def subbox5_58 : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩

theorem checked5_58 :
    LRCompactVLeafParameters.check subbox5_58 .long = true := by decide +kernel

theorem subsound5_58 : LRCompactVBoxSound subbox5_58 :=
  LRCompactVLeafParameters.sound checked5_58


def subbox5_59 : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩

theorem checked5_59 :
    LRCompactVLeafParameters.check subbox5_59 .long = true := by decide +kernel

theorem subsound5_59 : LRCompactVBoxSound subbox5_59 :=
  LRCompactVLeafParameters.sound checked5_59


def subbox5_60 : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((5 : ℚ) / 12), ((7 : ℚ) / 16), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩

theorem checked5_60 :
    LRCompactVLeafParameters.check subbox5_60 .long = true := by decide +kernel

theorem subsound5_60 : LRCompactVBoxSound subbox5_60 :=
  LRCompactVLeafParameters.sound checked5_60


def subbox5_61 : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩

theorem checked5_61 :
    LRCompactVLeafParameters.check subbox5_61 .long = true := by decide +kernel

theorem subsound5_61 : LRCompactVBoxSound subbox5_61 :=
  LRCompactVLeafParameters.sound checked5_61


def subbox5_62 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((5 : ℚ) / 12), ((7 : ℚ) / 16), ((139 : ℚ) / 160), ((559 : ℚ) / 640)⟩

theorem checked5_62 :
    LRCompactVLeafParameters.check subbox5_62 .long = true := by decide +kernel

theorem subsound5_62 : LRCompactVBoxSound subbox5_62 :=
  LRCompactVLeafParameters.sound checked5_62


def subbox5_63 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((5 : ℚ) / 12), ((7 : ℚ) / 16), ((559 : ℚ) / 640), ((281 : ℚ) / 320)⟩

theorem checked5_63 :
    LRCompactVLeafParameters.check subbox5_63 .long = true := by decide +kernel

theorem subsound5_63 : LRCompactVBoxSound subbox5_63 :=
  LRCompactVLeafParameters.sound checked5_63


def subbox5_64 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((139 : ℚ) / 160), ((559 : ℚ) / 640)⟩

theorem checked5_64 :
    LRCompactVLeafParameters.check subbox5_64 .long = true := by decide +kernel

theorem subsound5_64 : LRCompactVBoxSound subbox5_64 :=
  LRCompactVLeafParameters.sound checked5_64


def subbox5_65 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((559 : ℚ) / 640), ((281 : ℚ) / 320)⟩

theorem checked5_65 :
    LRCompactVLeafParameters.check subbox5_65 .long = true := by decide +kernel

theorem subsound5_65 : LRCompactVBoxSound subbox5_65 :=
  LRCompactVLeafParameters.sound checked5_65


def subbox5_66 : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((5 : ℚ) / 12), ((7 : ℚ) / 16), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩

theorem checked5_66 :
    LRCompactVLeafParameters.check subbox5_66 .long = true := by decide +kernel

theorem subsound5_66 : LRCompactVBoxSound subbox5_66 :=
  LRCompactVLeafParameters.sound checked5_66


def subbox5_67 : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩

theorem checked5_67 :
    LRCompactVLeafParameters.check subbox5_67 .long = true := by decide +kernel

theorem subsound5_67 : LRCompactVBoxSound subbox5_67 :=
  LRCompactVLeafParameters.sound checked5_67


def subbox5_68 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((5 : ℚ) / 12), ((7 : ℚ) / 16), ((281 : ℚ) / 320), ((113 : ℚ) / 128)⟩

theorem checked5_68 :
    LRCompactVLeafParameters.check subbox5_68 .long = true := by decide +kernel

theorem subsound5_68 : LRCompactVBoxSound subbox5_68 :=
  LRCompactVLeafParameters.sound checked5_68


def subbox5_69 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((5 : ℚ) / 12), ((7 : ℚ) / 16), ((113 : ℚ) / 128), ((71 : ℚ) / 80)⟩

theorem checked5_69 :
    LRCompactVLeafParameters.check subbox5_69 .long = true := by decide +kernel

theorem subsound5_69 : LRCompactVBoxSound subbox5_69 :=
  LRCompactVLeafParameters.sound checked5_69


def subbox5_70 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((281 : ℚ) / 320), ((113 : ℚ) / 128)⟩

theorem checked5_70 :
    LRCompactVLeafParameters.check subbox5_70 .long = true := by decide +kernel

theorem subsound5_70 : LRCompactVBoxSound subbox5_70 :=
  LRCompactVLeafParameters.sound checked5_70


def subbox5_71 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((113 : ℚ) / 128), ((71 : ℚ) / 80)⟩

theorem checked5_71 :
    LRCompactVLeafParameters.check subbox5_71 .long = true := by decide +kernel

theorem subsound5_71 : LRCompactVBoxSound subbox5_71 :=
  LRCompactVLeafParameters.sound checked5_71


def subbox5_72 : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩

theorem checked5_72 :
    LRCompactVLeafParameters.check subbox5_72 .long = true := by decide +kernel

theorem subsound5_72 : LRCompactVBoxSound subbox5_72 :=
  LRCompactVLeafParameters.sound checked5_72


def subbox5_73 : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((139 : ℚ) / 160), ((559 : ℚ) / 640)⟩

theorem checked5_73 :
    LRCompactVLeafParameters.check subbox5_73 .long = true := by decide +kernel

theorem subsound5_73 : LRCompactVBoxSound subbox5_73 :=
  LRCompactVLeafParameters.sound checked5_73


def subbox5_74 : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((559 : ℚ) / 640), ((281 : ℚ) / 320)⟩

theorem checked5_74 :
    LRCompactVLeafParameters.check subbox5_74 .long = true := by decide +kernel

theorem subsound5_74 : LRCompactVBoxSound subbox5_74 :=
  LRCompactVLeafParameters.sound checked5_74


def subbox5_75 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((139 : ℚ) / 160), ((559 : ℚ) / 640)⟩

theorem checked5_75 :
    LRCompactVLeafParameters.check subbox5_75 .long = true := by decide +kernel

theorem subsound5_75 : LRCompactVBoxSound subbox5_75 :=
  LRCompactVLeafParameters.sound checked5_75


def subbox5_76 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((559 : ℚ) / 640), ((281 : ℚ) / 320)⟩

theorem checked5_76 :
    LRCompactVLeafParameters.check subbox5_76 .long = true := by decide +kernel

theorem subsound5_76 : LRCompactVBoxSound subbox5_76 :=
  LRCompactVLeafParameters.sound checked5_76


def subbox5_77 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((139 : ℚ) / 160), ((559 : ℚ) / 640)⟩

theorem checked5_77 :
    LRCompactVLeafParameters.check subbox5_77 .long = true := by decide +kernel

theorem subsound5_77 : LRCompactVBoxSound subbox5_77 :=
  LRCompactVLeafParameters.sound checked5_77


def subbox5_78 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((559 : ℚ) / 640), ((281 : ℚ) / 320)⟩

theorem checked5_78 :
    LRCompactVLeafParameters.check subbox5_78 .long = true := by decide +kernel

theorem subsound5_78 : LRCompactVBoxSound subbox5_78 :=
  LRCompactVLeafParameters.sound checked5_78


def subbox5_79 : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩

theorem checked5_79 :
    LRCompactVLeafParameters.check subbox5_79 .long = true := by decide +kernel

theorem subsound5_79 : LRCompactVBoxSound subbox5_79 :=
  LRCompactVLeafParameters.sound checked5_79


def subbox5_80 : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((281 : ℚ) / 320), ((113 : ℚ) / 128)⟩

theorem checked5_80 :
    LRCompactVLeafParameters.check subbox5_80 .long = true := by decide +kernel

theorem subsound5_80 : LRCompactVBoxSound subbox5_80 :=
  LRCompactVLeafParameters.sound checked5_80


def subbox5_81 : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((113 : ℚ) / 128), ((71 : ℚ) / 80)⟩

theorem checked5_81 :
    LRCompactVLeafParameters.check subbox5_81 .long = true := by decide +kernel

theorem subsound5_81 : LRCompactVBoxSound subbox5_81 :=
  LRCompactVLeafParameters.sound checked5_81


def subbox5_82 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((281 : ℚ) / 320), ((113 : ℚ) / 128)⟩

theorem checked5_82 :
    LRCompactVLeafParameters.check subbox5_82 .long = true := by decide +kernel

theorem subsound5_82 : LRCompactVBoxSound subbox5_82 :=
  LRCompactVLeafParameters.sound checked5_82


def subbox5_83 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((113 : ℚ) / 128), ((71 : ℚ) / 80)⟩

theorem checked5_83 :
    LRCompactVLeafParameters.check subbox5_83 .long = true := by decide +kernel

theorem subsound5_83 : LRCompactVBoxSound subbox5_83 :=
  LRCompactVLeafParameters.sound checked5_83


def subbox5_84 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((281 : ℚ) / 320), ((113 : ℚ) / 128)⟩

theorem checked5_84 :
    LRCompactVLeafParameters.check subbox5_84 .long = true := by decide +kernel

theorem subsound5_84 : LRCompactVBoxSound subbox5_84 :=
  LRCompactVLeafParameters.sound checked5_84


def subbox5_85 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((113 : ℚ) / 128), ((71 : ℚ) / 80)⟩

theorem checked5_85 :
    LRCompactVLeafParameters.check subbox5_85 .long = true := by decide +kernel

theorem subsound5_85 : LRCompactVBoxSound subbox5_85 :=
  LRCompactVLeafParameters.sound checked5_85


def joinbox5_rLRLRRL : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((1 : ℚ) / 2), ((5 : ℚ) / 12), ((1 : ℚ) / 2), ((17 : ℚ) / 20), ((139 : ℚ) / 160)⟩


def joinbox5_rLRLRRLL : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((7 : ℚ) / 16), ((5 : ℚ) / 12), ((1 : ℚ) / 2), ((17 : ℚ) / 20), ((139 : ℚ) / 160)⟩


def joinbox5_rLRLRRLLL : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((7 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((17 : ℚ) / 20), ((139 : ℚ) / 160)⟩


def joinbox5_rLRLRRLLLL : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((7 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩


def joinbox5_rLRLRRLLLLL : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩


def joinbox5_rLRLRRLLLLR : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩


def joinbox5_rLRLRRLLLR : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((7 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩


def joinbox5_rLRLRRLLLRL : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩


def joinbox5_rLRLRRLLLRR : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩


def joinbox5_rLRLRRLLR : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((17 : ℚ) / 20), ((139 : ℚ) / 160)⟩


def joinbox5_rLRLRRLLRL : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩


def joinbox5_rLRLRRLLRLL : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩


def joinbox5_rLRLRRLLRLR : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩


def joinbox5_rLRLRRLLRR : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩


def joinbox5_rLRLRRLLRRL : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩


def joinbox5_rLRLRRLLRRR : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩


def joinbox5_rLRLRRLR : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((1 : ℚ) / 2), ((5 : ℚ) / 12), ((1 : ℚ) / 2), ((17 : ℚ) / 20), ((139 : ℚ) / 160)⟩


def joinbox5_rLRLRRLRL : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((1 : ℚ) / 2), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((17 : ℚ) / 20), ((139 : ℚ) / 160)⟩


def joinbox5_rLRLRRLRLL : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((1 : ℚ) / 2), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩


def joinbox5_rLRLRRLRLLL : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩


def joinbox5_rLRLRRLRLLR : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩


def joinbox5_rLRLRRLRLLRL : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((5 : ℚ) / 12), ((7 : ℚ) / 16), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩


def joinbox5_rLRLRRLRLLRR : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩


def joinbox5_rLRLRRLRLR : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((1 : ℚ) / 2), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩


def joinbox5_rLRLRRLRLRL : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩


def joinbox5_rLRLRRLRLRR : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩


def joinbox5_rLRLRRLRLRRL : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((5 : ℚ) / 12), ((7 : ℚ) / 16), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩


def joinbox5_rLRLRRLRLRRR : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩


def joinbox5_rLRLRRLRR : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((1 : ℚ) / 2), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((17 : ℚ) / 20), ((139 : ℚ) / 160)⟩


def joinbox5_rLRLRRLRRL : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((1 : ℚ) / 2), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩


def joinbox5_rLRLRRLRRLL : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩


def joinbox5_rLRLRRLRRLLL : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩


def joinbox5_rLRLRRLRRLLR : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩


def joinbox5_rLRLRRLRRLR : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩


def joinbox5_rLRLRRLRRLRL : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩


def joinbox5_rLRLRRLRRLRR : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩


def joinbox5_rLRLRRLRRR : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((1 : ℚ) / 2), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩


def joinbox5_rLRLRRLRRRL : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩


def joinbox5_rLRLRRLRRRLL : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩


def joinbox5_rLRLRRLRRRLR : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩


def joinbox5_rLRLRRLRRRR : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩


def joinbox5_rLRLRRLRRRRL : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩


def joinbox5_rLRLRRLRRRRR : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩


def joinbox5_rLRLRRR : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((1 : ℚ) / 2), ((5 : ℚ) / 12), ((1 : ℚ) / 2), ((139 : ℚ) / 160), ((71 : ℚ) / 80)⟩


def joinbox5_rLRLRRRL : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((7 : ℚ) / 16), ((5 : ℚ) / 12), ((1 : ℚ) / 2), ((139 : ℚ) / 160), ((71 : ℚ) / 80)⟩


def joinbox5_rLRLRRRLL : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((7 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((139 : ℚ) / 160), ((71 : ℚ) / 80)⟩


def joinbox5_rLRLRRRLLL : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((7 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩


def joinbox5_rLRLRRRLLLL : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩


def joinbox5_rLRLRRRLLLR : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩


def joinbox5_rLRLRRRLLR : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((7 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩


def joinbox5_rLRLRRRLLRL : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩


def joinbox5_rLRLRRRLLRR : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩


def joinbox5_rLRLRRRLR : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((139 : ℚ) / 160), ((71 : ℚ) / 80)⟩


def joinbox5_rLRLRRRLRL : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩


def joinbox5_rLRLRRRLRLL : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩


def joinbox5_rLRLRRRLRLR : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩


def joinbox5_rLRLRRRLRR : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩


def joinbox5_rLRLRRRLRRL : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩


def joinbox5_rLRLRRRLRRR : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩


def joinbox5_rLRLRRRR : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((1 : ℚ) / 2), ((5 : ℚ) / 12), ((1 : ℚ) / 2), ((139 : ℚ) / 160), ((71 : ℚ) / 80)⟩


def joinbox5_rLRLRRRRL : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((1 : ℚ) / 2), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((139 : ℚ) / 160), ((71 : ℚ) / 80)⟩


def joinbox5_rLRLRRRRLL : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((1 : ℚ) / 2), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩


def joinbox5_rLRLRRRRLLL : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩


def joinbox5_rLRLRRRRLLR : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩


def joinbox5_rLRLRRRRLLRL : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((5 : ℚ) / 12), ((7 : ℚ) / 16), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩


def joinbox5_rLRLRRRRLLRR : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩


def joinbox5_rLRLRRRRLR : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((1 : ℚ) / 2), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩


def joinbox5_rLRLRRRRLRL : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩


def joinbox5_rLRLRRRRLRR : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩


def joinbox5_rLRLRRRRLRRL : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((5 : ℚ) / 12), ((7 : ℚ) / 16), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩


def joinbox5_rLRLRRRRLRRR : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩


def joinbox5_rLRLRRRRR : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((1 : ℚ) / 2), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((139 : ℚ) / 160), ((71 : ℚ) / 80)⟩


def joinbox5_rLRLRRRRRL : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((1 : ℚ) / 2), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩


def joinbox5_rLRLRRRRRLL : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩


def joinbox5_rLRLRRRRRLLR : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩


def joinbox5_rLRLRRRRRLR : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩


def joinbox5_rLRLRRRRRLRL : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩


def joinbox5_rLRLRRRRRLRR : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩


def joinbox5_rLRLRRRRRR : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((1 : ℚ) / 2), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩


def joinbox5_rLRLRRRRRRL : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩


def joinbox5_rLRLRRRRRRLR : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩


def joinbox5_rLRLRRRRRRR : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩


def joinbox5_rLRLRRRRRRRL : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩


def joinbox5_rLRLRRRRRRRR : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩


theorem sound5 : LRCompactVBoxSound box5 :=
  (LRCompactVBoxSound.join (box := box5) .chi ((139 : ℚ) / 160)
    (LRCompactVBoxSound.join (box := joinbox5_rLRLRRL) .s ((7 : ℚ) / 16)
      (LRCompactVBoxSound.join (box := joinbox5_rLRLRRLL) .k ((11 : ℚ) / 24)
        (LRCompactVBoxSound.join (box := joinbox5_rLRLRRLLL) .chi ((55 : ℚ) / 64)
          (LRCompactVBoxSound.join (box := joinbox5_rLRLRRLLLL) .s ((13 : ℚ) / 32)
            (LRCompactVBoxSound.join (box := joinbox5_rLRLRRLLLLL) .k ((7 : ℚ) / 16)
              subsound5_0
              subsound5_1)
            (LRCompactVBoxSound.join (box := joinbox5_rLRLRRLLLLR) .k ((7 : ℚ) / 16)
              subsound5_2
              subsound5_3))
          (LRCompactVBoxSound.join (box := joinbox5_rLRLRRLLLR) .s ((13 : ℚ) / 32)
            (LRCompactVBoxSound.join (box := joinbox5_rLRLRRLLLRL) .k ((7 : ℚ) / 16)
              subsound5_4
              subsound5_5)
            (LRCompactVBoxSound.join (box := joinbox5_rLRLRRLLLRR) .k ((7 : ℚ) / 16)
              subsound5_6
              subsound5_7)))
        (LRCompactVBoxSound.join (box := joinbox5_rLRLRRLLR) .chi ((55 : ℚ) / 64)
          (LRCompactVBoxSound.join (box := joinbox5_rLRLRRLLRL) .s ((13 : ℚ) / 32)
            (LRCompactVBoxSound.join (box := joinbox5_rLRLRRLLRLL) .k ((23 : ℚ) / 48)
              subsound5_8
              subsound5_9)
            (LRCompactVBoxSound.join (box := joinbox5_rLRLRRLLRLR) .k ((23 : ℚ) / 48)
              subsound5_10
              subsound5_11))
          (LRCompactVBoxSound.join (box := joinbox5_rLRLRRLLRR) .s ((13 : ℚ) / 32)
            (LRCompactVBoxSound.join (box := joinbox5_rLRLRRLLRRL) .k ((23 : ℚ) / 48)
              subsound5_12
              subsound5_13)
            (LRCompactVBoxSound.join (box := joinbox5_rLRLRRLLRRR) .k ((23 : ℚ) / 48)
              subsound5_14
              subsound5_15))))
      (LRCompactVBoxSound.join (box := joinbox5_rLRLRRLR) .k ((11 : ℚ) / 24)
        (LRCompactVBoxSound.join (box := joinbox5_rLRLRRLRL) .chi ((55 : ℚ) / 64)
          (LRCompactVBoxSound.join (box := joinbox5_rLRLRRLRLL) .s ((15 : ℚ) / 32)
            (LRCompactVBoxSound.join (box := joinbox5_rLRLRRLRLLL) .k ((7 : ℚ) / 16)
              subsound5_16
              subsound5_17)
            (LRCompactVBoxSound.join (box := joinbox5_rLRLRRLRLLR) .k ((7 : ℚ) / 16)
              (LRCompactVBoxSound.join (box := joinbox5_rLRLRRLRLLRL) .chi ((547 : ℚ) / 640)
                subsound5_18
                subsound5_19)
              (LRCompactVBoxSound.join (box := joinbox5_rLRLRRLRLLRR) .chi ((547 : ℚ) / 640)
                subsound5_20
                subsound5_21)))
          (LRCompactVBoxSound.join (box := joinbox5_rLRLRRLRLR) .s ((15 : ℚ) / 32)
            (LRCompactVBoxSound.join (box := joinbox5_rLRLRRLRLRL) .k ((7 : ℚ) / 16)
              subsound5_22
              subsound5_23)
            (LRCompactVBoxSound.join (box := joinbox5_rLRLRRLRLRR) .k ((7 : ℚ) / 16)
              (LRCompactVBoxSound.join (box := joinbox5_rLRLRRLRLRRL) .chi ((553 : ℚ) / 640)
                subsound5_24
                subsound5_25)
              (LRCompactVBoxSound.join (box := joinbox5_rLRLRRLRLRRR) .chi ((553 : ℚ) / 640)
                subsound5_26
                subsound5_27))))
        (LRCompactVBoxSound.join (box := joinbox5_rLRLRRLRR) .chi ((55 : ℚ) / 64)
          (LRCompactVBoxSound.join (box := joinbox5_rLRLRRLRRL) .s ((15 : ℚ) / 32)
            (LRCompactVBoxSound.join (box := joinbox5_rLRLRRLRRLL) .k ((23 : ℚ) / 48)
              (LRCompactVBoxSound.join (box := joinbox5_rLRLRRLRRLLL) .chi ((547 : ℚ) / 640)
                subsound5_28
                subsound5_29)
              (LRCompactVBoxSound.join (box := joinbox5_rLRLRRLRRLLR) .chi ((547 : ℚ) / 640)
                subsound5_30
                subsound5_31))
            (LRCompactVBoxSound.join (box := joinbox5_rLRLRRLRRLR) .k ((23 : ℚ) / 48)
              (LRCompactVBoxSound.join (box := joinbox5_rLRLRRLRRLRL) .chi ((547 : ℚ) / 640)
                subsound5_32
                subsound5_33)
              (LRCompactVBoxSound.join (box := joinbox5_rLRLRRLRRLRR) .chi ((547 : ℚ) / 640)
                subsound5_34
                subsound5_35)))
          (LRCompactVBoxSound.join (box := joinbox5_rLRLRRLRRR) .s ((15 : ℚ) / 32)
            (LRCompactVBoxSound.join (box := joinbox5_rLRLRRLRRRL) .k ((23 : ℚ) / 48)
              (LRCompactVBoxSound.join (box := joinbox5_rLRLRRLRRRLL) .chi ((553 : ℚ) / 640)
                subsound5_36
                subsound5_37)
              (LRCompactVBoxSound.join (box := joinbox5_rLRLRRLRRRLR) .chi ((553 : ℚ) / 640)
                subsound5_38
                subsound5_39))
            (LRCompactVBoxSound.join (box := joinbox5_rLRLRRLRRRR) .k ((23 : ℚ) / 48)
              (LRCompactVBoxSound.join (box := joinbox5_rLRLRRLRRRRL) .chi ((553 : ℚ) / 640)
                subsound5_40
                subsound5_41)
              (LRCompactVBoxSound.join (box := joinbox5_rLRLRRLRRRRR) .chi ((553 : ℚ) / 640)
                subsound5_42
                subsound5_43))))))
    (LRCompactVBoxSound.join (box := joinbox5_rLRLRRR) .s ((7 : ℚ) / 16)
      (LRCompactVBoxSound.join (box := joinbox5_rLRLRRRL) .k ((11 : ℚ) / 24)
        (LRCompactVBoxSound.join (box := joinbox5_rLRLRRRLL) .chi ((281 : ℚ) / 320)
          (LRCompactVBoxSound.join (box := joinbox5_rLRLRRRLLL) .s ((13 : ℚ) / 32)
            (LRCompactVBoxSound.join (box := joinbox5_rLRLRRRLLLL) .k ((7 : ℚ) / 16)
              subsound5_44
              subsound5_45)
            (LRCompactVBoxSound.join (box := joinbox5_rLRLRRRLLLR) .k ((7 : ℚ) / 16)
              subsound5_46
              subsound5_47))
          (LRCompactVBoxSound.join (box := joinbox5_rLRLRRRLLR) .s ((13 : ℚ) / 32)
            (LRCompactVBoxSound.join (box := joinbox5_rLRLRRRLLRL) .k ((7 : ℚ) / 16)
              subsound5_48
              subsound5_49)
            (LRCompactVBoxSound.join (box := joinbox5_rLRLRRRLLRR) .k ((7 : ℚ) / 16)
              subsound5_50
              subsound5_51)))
        (LRCompactVBoxSound.join (box := joinbox5_rLRLRRRLR) .chi ((281 : ℚ) / 320)
          (LRCompactVBoxSound.join (box := joinbox5_rLRLRRRLRL) .s ((13 : ℚ) / 32)
            (LRCompactVBoxSound.join (box := joinbox5_rLRLRRRLRLL) .k ((23 : ℚ) / 48)
              subsound5_52
              subsound5_53)
            (LRCompactVBoxSound.join (box := joinbox5_rLRLRRRLRLR) .k ((23 : ℚ) / 48)
              subsound5_54
              subsound5_55))
          (LRCompactVBoxSound.join (box := joinbox5_rLRLRRRLRR) .s ((13 : ℚ) / 32)
            (LRCompactVBoxSound.join (box := joinbox5_rLRLRRRLRRL) .k ((23 : ℚ) / 48)
              subsound5_56
              subsound5_57)
            (LRCompactVBoxSound.join (box := joinbox5_rLRLRRRLRRR) .k ((23 : ℚ) / 48)
              subsound5_58
              subsound5_59))))
      (LRCompactVBoxSound.join (box := joinbox5_rLRLRRRR) .k ((11 : ℚ) / 24)
        (LRCompactVBoxSound.join (box := joinbox5_rLRLRRRRL) .chi ((281 : ℚ) / 320)
          (LRCompactVBoxSound.join (box := joinbox5_rLRLRRRRLL) .s ((15 : ℚ) / 32)
            (LRCompactVBoxSound.join (box := joinbox5_rLRLRRRRLLL) .k ((7 : ℚ) / 16)
              subsound5_60
              subsound5_61)
            (LRCompactVBoxSound.join (box := joinbox5_rLRLRRRRLLR) .k ((7 : ℚ) / 16)
              (LRCompactVBoxSound.join (box := joinbox5_rLRLRRRRLLRL) .chi ((559 : ℚ) / 640)
                subsound5_62
                subsound5_63)
              (LRCompactVBoxSound.join (box := joinbox5_rLRLRRRRLLRR) .chi ((559 : ℚ) / 640)
                subsound5_64
                subsound5_65)))
          (LRCompactVBoxSound.join (box := joinbox5_rLRLRRRRLR) .s ((15 : ℚ) / 32)
            (LRCompactVBoxSound.join (box := joinbox5_rLRLRRRRLRL) .k ((7 : ℚ) / 16)
              subsound5_66
              subsound5_67)
            (LRCompactVBoxSound.join (box := joinbox5_rLRLRRRRLRR) .k ((7 : ℚ) / 16)
              (LRCompactVBoxSound.join (box := joinbox5_rLRLRRRRLRRL) .chi ((113 : ℚ) / 128)
                subsound5_68
                subsound5_69)
              (LRCompactVBoxSound.join (box := joinbox5_rLRLRRRRLRRR) .chi ((113 : ℚ) / 128)
                subsound5_70
                subsound5_71))))
        (LRCompactVBoxSound.join (box := joinbox5_rLRLRRRRR) .chi ((281 : ℚ) / 320)
          (LRCompactVBoxSound.join (box := joinbox5_rLRLRRRRRL) .s ((15 : ℚ) / 32)
            (LRCompactVBoxSound.join (box := joinbox5_rLRLRRRRRLL) .k ((23 : ℚ) / 48)
              subsound5_72
              (LRCompactVBoxSound.join (box := joinbox5_rLRLRRRRRLLR) .chi ((559 : ℚ) / 640)
                subsound5_73
                subsound5_74))
            (LRCompactVBoxSound.join (box := joinbox5_rLRLRRRRRLR) .k ((23 : ℚ) / 48)
              (LRCompactVBoxSound.join (box := joinbox5_rLRLRRRRRLRL) .chi ((559 : ℚ) / 640)
                subsound5_75
                subsound5_76)
              (LRCompactVBoxSound.join (box := joinbox5_rLRLRRRRRLRR) .chi ((559 : ℚ) / 640)
                subsound5_77
                subsound5_78)))
          (LRCompactVBoxSound.join (box := joinbox5_rLRLRRRRRR) .s ((15 : ℚ) / 32)
            (LRCompactVBoxSound.join (box := joinbox5_rLRLRRRRRRL) .k ((23 : ℚ) / 48)
              subsound5_79
              (LRCompactVBoxSound.join (box := joinbox5_rLRLRRRRRRLR) .chi ((113 : ℚ) / 128)
                subsound5_80
                subsound5_81))
            (LRCompactVBoxSound.join (box := joinbox5_rLRLRRRRRRR) .k ((23 : ℚ) / 48)
              (LRCompactVBoxSound.join (box := joinbox5_rLRLRRRRRRRL) .chi ((113 : ℚ) / 128)
                subsound5_82
                subsound5_83)
              (LRCompactVBoxSound.join (box := joinbox5_rLRLRRRRRRRR) .chi ((113 : ℚ) / 128)
                subsound5_84
                subsound5_85)))))))

end CourtadeKumar.GeneratedLRCompactVLowR
