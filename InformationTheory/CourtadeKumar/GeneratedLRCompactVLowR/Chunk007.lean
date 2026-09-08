import InformationTheory.CourtadeKumar.LRCompactVBasicReplay

/-! Frozen basic compact-V replay.
Plan SHA-256: ce3f7a498b2b9caf346dcf88ce7861f8cc091af8cd93f5624d7684e21322ecd5
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CourtadeKumar.GeneratedLRCompactVLowR

-- 64 accepted leaves below path rLRRRL.
def box7 : CertificateBox where
  sLo := ((3 : ℚ) / 8)
  sHi := ((1 : ℚ) / 2)
  kLo := ((1 : ℚ) / 3)
  kHi := ((5 : ℚ) / 12)
  chiLo := ((71 : ℚ) / 80)
  chiHi := ((37 : ℚ) / 40)


def subbox7_0 : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((1 : ℚ) / 3), ((17 : ℚ) / 48), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩

theorem checked7_0 :
    LRCompactVLeafParameters.check subbox7_0 .short = true := by decide +kernel

theorem subsound7_0 : LRCompactVBoxSound subbox7_0 :=
  LRCompactVLeafParameters.sound checked7_0


def subbox7_1 : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((17 : ℚ) / 48), ((3 : ℚ) / 8), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩

theorem checked7_1 :
    LRCompactVLeafParameters.check subbox7_1 .short = true := by decide +kernel

theorem subsound7_1 : LRCompactVBoxSound subbox7_1 :=
  LRCompactVLeafParameters.sound checked7_1


def subbox7_2 : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((1 : ℚ) / 3), ((17 : ℚ) / 48), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩

theorem checked7_2 :
    LRCompactVLeafParameters.check subbox7_2 .short = true := by decide +kernel

theorem subsound7_2 : LRCompactVBoxSound subbox7_2 :=
  LRCompactVLeafParameters.sound checked7_2


def subbox7_3 : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((17 : ℚ) / 48), ((3 : ℚ) / 8), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩

theorem checked7_3 :
    LRCompactVLeafParameters.check subbox7_3 .short = true := by decide +kernel

theorem subsound7_3 : LRCompactVBoxSound subbox7_3 :=
  LRCompactVLeafParameters.sound checked7_3


def subbox7_4 : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((1 : ℚ) / 3), ((17 : ℚ) / 48), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩

theorem checked7_4 :
    LRCompactVLeafParameters.check subbox7_4 .short = true := by decide +kernel

theorem subsound7_4 : LRCompactVBoxSound subbox7_4 :=
  LRCompactVLeafParameters.sound checked7_4


def subbox7_5 : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((17 : ℚ) / 48), ((3 : ℚ) / 8), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩

theorem checked7_5 :
    LRCompactVLeafParameters.check subbox7_5 .short = true := by decide +kernel

theorem subsound7_5 : LRCompactVBoxSound subbox7_5 :=
  LRCompactVLeafParameters.sound checked7_5


def subbox7_6 : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((1 : ℚ) / 3), ((17 : ℚ) / 48), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩

theorem checked7_6 :
    LRCompactVLeafParameters.check subbox7_6 .short = true := by decide +kernel

theorem subsound7_6 : LRCompactVBoxSound subbox7_6 :=
  LRCompactVLeafParameters.sound checked7_6


def subbox7_7 : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((17 : ℚ) / 48), ((3 : ℚ) / 8), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩

theorem checked7_7 :
    LRCompactVLeafParameters.check subbox7_7 .short = true := by decide +kernel

theorem subsound7_7 : LRCompactVBoxSound subbox7_7 :=
  LRCompactVLeafParameters.sound checked7_7


def subbox7_8 : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((3 : ℚ) / 8), ((19 : ℚ) / 48), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩

theorem checked7_8 :
    LRCompactVLeafParameters.check subbox7_8 .short = true := by decide +kernel

theorem subsound7_8 : LRCompactVBoxSound subbox7_8 :=
  LRCompactVLeafParameters.sound checked7_8


def subbox7_9 : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((19 : ℚ) / 48), ((5 : ℚ) / 12), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩

theorem checked7_9 :
    LRCompactVLeafParameters.check subbox7_9 .short = true := by decide +kernel

theorem subsound7_9 : LRCompactVBoxSound subbox7_9 :=
  LRCompactVLeafParameters.sound checked7_9


def subbox7_10 : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((3 : ℚ) / 8), ((19 : ℚ) / 48), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩

theorem checked7_10 :
    LRCompactVLeafParameters.check subbox7_10 .short = true := by decide +kernel

theorem subsound7_10 : LRCompactVBoxSound subbox7_10 :=
  LRCompactVLeafParameters.sound checked7_10


def subbox7_11 : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((19 : ℚ) / 48), ((5 : ℚ) / 12), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩

theorem checked7_11 :
    LRCompactVLeafParameters.check subbox7_11 .short = true := by decide +kernel

theorem subsound7_11 : LRCompactVBoxSound subbox7_11 :=
  LRCompactVLeafParameters.sound checked7_11


def subbox7_12 : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((3 : ℚ) / 8), ((19 : ℚ) / 48), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩

theorem checked7_12 :
    LRCompactVLeafParameters.check subbox7_12 .short = true := by decide +kernel

theorem subsound7_12 : LRCompactVBoxSound subbox7_12 :=
  LRCompactVLeafParameters.sound checked7_12


def subbox7_13 : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((19 : ℚ) / 48), ((5 : ℚ) / 12), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩

theorem checked7_13 :
    LRCompactVLeafParameters.check subbox7_13 .short = true := by decide +kernel

theorem subsound7_13 : LRCompactVBoxSound subbox7_13 :=
  LRCompactVLeafParameters.sound checked7_13


def subbox7_14 : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((3 : ℚ) / 8), ((19 : ℚ) / 48), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩

theorem checked7_14 :
    LRCompactVLeafParameters.check subbox7_14 .short = true := by decide +kernel

theorem subsound7_14 : LRCompactVBoxSound subbox7_14 :=
  LRCompactVLeafParameters.sound checked7_14


def subbox7_15 : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((19 : ℚ) / 48), ((5 : ℚ) / 12), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩

theorem checked7_15 :
    LRCompactVLeafParameters.check subbox7_15 .short = true := by decide +kernel

theorem subsound7_15 : LRCompactVBoxSound subbox7_15 :=
  LRCompactVLeafParameters.sound checked7_15


def subbox7_16 : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((1 : ℚ) / 3), ((17 : ℚ) / 48), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩

theorem checked7_16 :
    LRCompactVLeafParameters.check subbox7_16 .short = true := by decide +kernel

theorem subsound7_16 : LRCompactVBoxSound subbox7_16 :=
  LRCompactVLeafParameters.sound checked7_16


def subbox7_17 : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((17 : ℚ) / 48), ((3 : ℚ) / 8), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩

theorem checked7_17 :
    LRCompactVLeafParameters.check subbox7_17 .short = true := by decide +kernel

theorem subsound7_17 : LRCompactVBoxSound subbox7_17 :=
  LRCompactVLeafParameters.sound checked7_17


def subbox7_18 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((1 : ℚ) / 3), ((17 : ℚ) / 48), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩

theorem checked7_18 :
    LRCompactVLeafParameters.check subbox7_18 .long = true := by decide +kernel

theorem subsound7_18 : LRCompactVBoxSound subbox7_18 :=
  LRCompactVLeafParameters.sound checked7_18


def subbox7_19 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((17 : ℚ) / 48), ((3 : ℚ) / 8), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩

theorem checked7_19 :
    LRCompactVLeafParameters.check subbox7_19 .long = true := by decide +kernel

theorem subsound7_19 : LRCompactVBoxSound subbox7_19 :=
  LRCompactVLeafParameters.sound checked7_19


def subbox7_20 : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((1 : ℚ) / 3), ((17 : ℚ) / 48), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩

theorem checked7_20 :
    LRCompactVLeafParameters.check subbox7_20 .short = true := by decide +kernel

theorem subsound7_20 : LRCompactVBoxSound subbox7_20 :=
  LRCompactVLeafParameters.sound checked7_20


def subbox7_21 : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((17 : ℚ) / 48), ((3 : ℚ) / 8), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩

theorem checked7_21 :
    LRCompactVLeafParameters.check subbox7_21 .short = true := by decide +kernel

theorem subsound7_21 : LRCompactVBoxSound subbox7_21 :=
  LRCompactVLeafParameters.sound checked7_21


def subbox7_22 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((1 : ℚ) / 3), ((17 : ℚ) / 48), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩

theorem checked7_22 :
    LRCompactVLeafParameters.check subbox7_22 .long = true := by decide +kernel

theorem subsound7_22 : LRCompactVBoxSound subbox7_22 :=
  LRCompactVLeafParameters.sound checked7_22


def subbox7_23 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((17 : ℚ) / 48), ((3 : ℚ) / 8), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩

theorem checked7_23 :
    LRCompactVLeafParameters.check subbox7_23 .long = true := by decide +kernel

theorem subsound7_23 : LRCompactVBoxSound subbox7_23 :=
  LRCompactVLeafParameters.sound checked7_23


def subbox7_24 : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((3 : ℚ) / 8), ((19 : ℚ) / 48), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩

theorem checked7_24 :
    LRCompactVLeafParameters.check subbox7_24 .short = true := by decide +kernel

theorem subsound7_24 : LRCompactVBoxSound subbox7_24 :=
  LRCompactVLeafParameters.sound checked7_24


def subbox7_25 : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((19 : ℚ) / 48), ((5 : ℚ) / 12), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩

theorem checked7_25 :
    LRCompactVLeafParameters.check subbox7_25 .long = true := by decide +kernel

theorem subsound7_25 : LRCompactVBoxSound subbox7_25 :=
  LRCompactVLeafParameters.sound checked7_25


def subbox7_26 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((3 : ℚ) / 8), ((19 : ℚ) / 48), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩

theorem checked7_26 :
    LRCompactVLeafParameters.check subbox7_26 .long = true := by decide +kernel

theorem subsound7_26 : LRCompactVBoxSound subbox7_26 :=
  LRCompactVLeafParameters.sound checked7_26


def subbox7_27 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((19 : ℚ) / 48), ((5 : ℚ) / 12), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩

theorem checked7_27 :
    LRCompactVLeafParameters.check subbox7_27 .long = true := by decide +kernel

theorem subsound7_27 : LRCompactVBoxSound subbox7_27 :=
  LRCompactVLeafParameters.sound checked7_27


def subbox7_28 : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((3 : ℚ) / 8), ((19 : ℚ) / 48), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩

theorem checked7_28 :
    LRCompactVLeafParameters.check subbox7_28 .short = true := by decide +kernel

theorem subsound7_28 : LRCompactVBoxSound subbox7_28 :=
  LRCompactVLeafParameters.sound checked7_28


def subbox7_29 : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((19 : ℚ) / 48), ((5 : ℚ) / 12), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩

theorem checked7_29 :
    LRCompactVLeafParameters.check subbox7_29 .short = true := by decide +kernel

theorem subsound7_29 : LRCompactVBoxSound subbox7_29 :=
  LRCompactVLeafParameters.sound checked7_29


def subbox7_30 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((3 : ℚ) / 8), ((19 : ℚ) / 48), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩

theorem checked7_30 :
    LRCompactVLeafParameters.check subbox7_30 .long = true := by decide +kernel

theorem subsound7_30 : LRCompactVBoxSound subbox7_30 :=
  LRCompactVLeafParameters.sound checked7_30


def subbox7_31 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((19 : ℚ) / 48), ((5 : ℚ) / 12), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩

theorem checked7_31 :
    LRCompactVLeafParameters.check subbox7_31 .long = true := by decide +kernel

theorem subsound7_31 : LRCompactVBoxSound subbox7_31 :=
  LRCompactVLeafParameters.sound checked7_31


def subbox7_32 : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((1 : ℚ) / 3), ((17 : ℚ) / 48), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩

theorem checked7_32 :
    LRCompactVLeafParameters.check subbox7_32 .short = true := by decide +kernel

theorem subsound7_32 : LRCompactVBoxSound subbox7_32 :=
  LRCompactVLeafParameters.sound checked7_32


def subbox7_33 : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((17 : ℚ) / 48), ((3 : ℚ) / 8), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩

theorem checked7_33 :
    LRCompactVLeafParameters.check subbox7_33 .short = true := by decide +kernel

theorem subsound7_33 : LRCompactVBoxSound subbox7_33 :=
  LRCompactVLeafParameters.sound checked7_33


def subbox7_34 : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((1 : ℚ) / 3), ((17 : ℚ) / 48), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩

theorem checked7_34 :
    LRCompactVLeafParameters.check subbox7_34 .short = true := by decide +kernel

theorem subsound7_34 : LRCompactVBoxSound subbox7_34 :=
  LRCompactVLeafParameters.sound checked7_34


def subbox7_35 : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((17 : ℚ) / 48), ((3 : ℚ) / 8), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩

theorem checked7_35 :
    LRCompactVLeafParameters.check subbox7_35 .short = true := by decide +kernel

theorem subsound7_35 : LRCompactVBoxSound subbox7_35 :=
  LRCompactVLeafParameters.sound checked7_35


def subbox7_36 : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((1 : ℚ) / 3), ((17 : ℚ) / 48), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩

theorem checked7_36 :
    LRCompactVLeafParameters.check subbox7_36 .short = true := by decide +kernel

theorem subsound7_36 : LRCompactVBoxSound subbox7_36 :=
  LRCompactVLeafParameters.sound checked7_36


def subbox7_37 : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((17 : ℚ) / 48), ((3 : ℚ) / 8), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩

theorem checked7_37 :
    LRCompactVLeafParameters.check subbox7_37 .short = true := by decide +kernel

theorem subsound7_37 : LRCompactVBoxSound subbox7_37 :=
  LRCompactVLeafParameters.sound checked7_37


def subbox7_38 : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((1 : ℚ) / 3), ((17 : ℚ) / 48), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩

theorem checked7_38 :
    LRCompactVLeafParameters.check subbox7_38 .short = true := by decide +kernel

theorem subsound7_38 : LRCompactVBoxSound subbox7_38 :=
  LRCompactVLeafParameters.sound checked7_38


def subbox7_39 : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((17 : ℚ) / 48), ((3 : ℚ) / 8), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩

theorem checked7_39 :
    LRCompactVLeafParameters.check subbox7_39 .short = true := by decide +kernel

theorem subsound7_39 : LRCompactVBoxSound subbox7_39 :=
  LRCompactVLeafParameters.sound checked7_39


def subbox7_40 : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((3 : ℚ) / 8), ((19 : ℚ) / 48), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩

theorem checked7_40 :
    LRCompactVLeafParameters.check subbox7_40 .short = true := by decide +kernel

theorem subsound7_40 : LRCompactVBoxSound subbox7_40 :=
  LRCompactVLeafParameters.sound checked7_40


def subbox7_41 : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((19 : ℚ) / 48), ((5 : ℚ) / 12), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩

theorem checked7_41 :
    LRCompactVLeafParameters.check subbox7_41 .short = true := by decide +kernel

theorem subsound7_41 : LRCompactVBoxSound subbox7_41 :=
  LRCompactVLeafParameters.sound checked7_41


def subbox7_42 : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((3 : ℚ) / 8), ((19 : ℚ) / 48), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩

theorem checked7_42 :
    LRCompactVLeafParameters.check subbox7_42 .short = true := by decide +kernel

theorem subsound7_42 : LRCompactVBoxSound subbox7_42 :=
  LRCompactVLeafParameters.sound checked7_42


def subbox7_43 : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((19 : ℚ) / 48), ((5 : ℚ) / 12), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩

theorem checked7_43 :
    LRCompactVLeafParameters.check subbox7_43 .short = true := by decide +kernel

theorem subsound7_43 : LRCompactVBoxSound subbox7_43 :=
  LRCompactVLeafParameters.sound checked7_43


def subbox7_44 : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((3 : ℚ) / 8), ((19 : ℚ) / 48), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩

theorem checked7_44 :
    LRCompactVLeafParameters.check subbox7_44 .short = true := by decide +kernel

theorem subsound7_44 : LRCompactVBoxSound subbox7_44 :=
  LRCompactVLeafParameters.sound checked7_44


def subbox7_45 : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((19 : ℚ) / 48), ((5 : ℚ) / 12), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩

theorem checked7_45 :
    LRCompactVLeafParameters.check subbox7_45 .short = true := by decide +kernel

theorem subsound7_45 : LRCompactVBoxSound subbox7_45 :=
  LRCompactVLeafParameters.sound checked7_45


def subbox7_46 : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((3 : ℚ) / 8), ((19 : ℚ) / 48), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩

theorem checked7_46 :
    LRCompactVLeafParameters.check subbox7_46 .short = true := by decide +kernel

theorem subsound7_46 : LRCompactVBoxSound subbox7_46 :=
  LRCompactVLeafParameters.sound checked7_46


def subbox7_47 : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((19 : ℚ) / 48), ((5 : ℚ) / 12), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩

theorem checked7_47 :
    LRCompactVLeafParameters.check subbox7_47 .short = true := by decide +kernel

theorem subsound7_47 : LRCompactVBoxSound subbox7_47 :=
  LRCompactVLeafParameters.sound checked7_47


def subbox7_48 : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((1 : ℚ) / 3), ((17 : ℚ) / 48), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩

theorem checked7_48 :
    LRCompactVLeafParameters.check subbox7_48 .short = true := by decide +kernel

theorem subsound7_48 : LRCompactVBoxSound subbox7_48 :=
  LRCompactVLeafParameters.sound checked7_48


def subbox7_49 : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((17 : ℚ) / 48), ((3 : ℚ) / 8), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩

theorem checked7_49 :
    LRCompactVLeafParameters.check subbox7_49 .short = true := by decide +kernel

theorem subsound7_49 : LRCompactVBoxSound subbox7_49 :=
  LRCompactVLeafParameters.sound checked7_49


def subbox7_50 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((1 : ℚ) / 3), ((17 : ℚ) / 48), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩

theorem checked7_50 :
    LRCompactVLeafParameters.check subbox7_50 .long = true := by decide +kernel

theorem subsound7_50 : LRCompactVBoxSound subbox7_50 :=
  LRCompactVLeafParameters.sound checked7_50


def subbox7_51 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((17 : ℚ) / 48), ((3 : ℚ) / 8), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩

theorem checked7_51 :
    LRCompactVLeafParameters.check subbox7_51 .long = true := by decide +kernel

theorem subsound7_51 : LRCompactVBoxSound subbox7_51 :=
  LRCompactVLeafParameters.sound checked7_51


def subbox7_52 : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((1 : ℚ) / 3), ((17 : ℚ) / 48), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩

theorem checked7_52 :
    LRCompactVLeafParameters.check subbox7_52 .short = true := by decide +kernel

theorem subsound7_52 : LRCompactVBoxSound subbox7_52 :=
  LRCompactVLeafParameters.sound checked7_52


def subbox7_53 : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((17 : ℚ) / 48), ((3 : ℚ) / 8), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩

theorem checked7_53 :
    LRCompactVLeafParameters.check subbox7_53 .short = true := by decide +kernel

theorem subsound7_53 : LRCompactVBoxSound subbox7_53 :=
  LRCompactVLeafParameters.sound checked7_53


def subbox7_54 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((1 : ℚ) / 3), ((17 : ℚ) / 48), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩

theorem checked7_54 :
    LRCompactVLeafParameters.check subbox7_54 .short = true := by decide +kernel

theorem subsound7_54 : LRCompactVBoxSound subbox7_54 :=
  LRCompactVLeafParameters.sound checked7_54


def subbox7_55 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((17 : ℚ) / 48), ((3 : ℚ) / 8), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩

theorem checked7_55 :
    LRCompactVLeafParameters.check subbox7_55 .long = true := by decide +kernel

theorem subsound7_55 : LRCompactVBoxSound subbox7_55 :=
  LRCompactVLeafParameters.sound checked7_55


def subbox7_56 : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((3 : ℚ) / 8), ((19 : ℚ) / 48), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩

theorem checked7_56 :
    LRCompactVLeafParameters.check subbox7_56 .short = true := by decide +kernel

theorem subsound7_56 : LRCompactVBoxSound subbox7_56 :=
  LRCompactVLeafParameters.sound checked7_56


def subbox7_57 : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((19 : ℚ) / 48), ((5 : ℚ) / 12), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩

theorem checked7_57 :
    LRCompactVLeafParameters.check subbox7_57 .short = true := by decide +kernel

theorem subsound7_57 : LRCompactVBoxSound subbox7_57 :=
  LRCompactVLeafParameters.sound checked7_57


def subbox7_58 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((3 : ℚ) / 8), ((19 : ℚ) / 48), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩

theorem checked7_58 :
    LRCompactVLeafParameters.check subbox7_58 .long = true := by decide +kernel

theorem subsound7_58 : LRCompactVBoxSound subbox7_58 :=
  LRCompactVLeafParameters.sound checked7_58


def subbox7_59 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((19 : ℚ) / 48), ((5 : ℚ) / 12), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩

theorem checked7_59 :
    LRCompactVLeafParameters.check subbox7_59 .long = true := by decide +kernel

theorem subsound7_59 : LRCompactVBoxSound subbox7_59 :=
  LRCompactVLeafParameters.sound checked7_59


def subbox7_60 : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((3 : ℚ) / 8), ((19 : ℚ) / 48), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩

theorem checked7_60 :
    LRCompactVLeafParameters.check subbox7_60 .short = true := by decide +kernel

theorem subsound7_60 : LRCompactVBoxSound subbox7_60 :=
  LRCompactVLeafParameters.sound checked7_60


def subbox7_61 : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((19 : ℚ) / 48), ((5 : ℚ) / 12), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩

theorem checked7_61 :
    LRCompactVLeafParameters.check subbox7_61 .short = true := by decide +kernel

theorem subsound7_61 : LRCompactVBoxSound subbox7_61 :=
  LRCompactVLeafParameters.sound checked7_61


def subbox7_62 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((3 : ℚ) / 8), ((19 : ℚ) / 48), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩

theorem checked7_62 :
    LRCompactVLeafParameters.check subbox7_62 .long = true := by decide +kernel

theorem subsound7_62 : LRCompactVBoxSound subbox7_62 :=
  LRCompactVLeafParameters.sound checked7_62


def subbox7_63 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((19 : ℚ) / 48), ((5 : ℚ) / 12), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩

theorem checked7_63 :
    LRCompactVLeafParameters.check subbox7_63 .long = true := by decide +kernel

theorem subsound7_63 : LRCompactVBoxSound subbox7_63 :=
  LRCompactVLeafParameters.sound checked7_63


def joinbox7_rLRRRLL : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((1 : ℚ) / 2), ((1 : ℚ) / 3), ((5 : ℚ) / 12), ((71 : ℚ) / 80), ((29 : ℚ) / 32)⟩


def joinbox7_rLRRRLLL : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((7 : ℚ) / 16), ((1 : ℚ) / 3), ((5 : ℚ) / 12), ((71 : ℚ) / 80), ((29 : ℚ) / 32)⟩


def joinbox7_rLRRRLLLL : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((7 : ℚ) / 16), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((71 : ℚ) / 80), ((29 : ℚ) / 32)⟩


def joinbox7_rLRRRLLLLL : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((7 : ℚ) / 16), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩


def joinbox7_rLRRRLLLLLL : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩


def joinbox7_rLRRRLLLLLR : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩


def joinbox7_rLRRRLLLLR : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((7 : ℚ) / 16), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩


def joinbox7_rLRRRLLLLRL : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩


def joinbox7_rLRRRLLLLRR : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩


def joinbox7_rLRRRLLLR : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((7 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((71 : ℚ) / 80), ((29 : ℚ) / 32)⟩


def joinbox7_rLRRRLLLRL : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((7 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩


def joinbox7_rLRRRLLLRLL : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩


def joinbox7_rLRRRLLLRLR : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩


def joinbox7_rLRRRLLLRR : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((7 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩


def joinbox7_rLRRRLLLRRL : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩


def joinbox7_rLRRRLLLRRR : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩


def joinbox7_rLRRRLLR : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((1 : ℚ) / 2), ((1 : ℚ) / 3), ((5 : ℚ) / 12), ((71 : ℚ) / 80), ((29 : ℚ) / 32)⟩


def joinbox7_rLRRRLLRL : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((1 : ℚ) / 2), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((71 : ℚ) / 80), ((29 : ℚ) / 32)⟩


def joinbox7_rLRRRLLRLL : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((1 : ℚ) / 2), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩


def joinbox7_rLRRRLLRLLL : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩


def joinbox7_rLRRRLLRLLR : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩


def joinbox7_rLRRRLLRLR : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((1 : ℚ) / 2), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩


def joinbox7_rLRRRLLRLRL : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩


def joinbox7_rLRRRLLRLRR : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩


def joinbox7_rLRRRLLRR : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((1 : ℚ) / 2), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((71 : ℚ) / 80), ((29 : ℚ) / 32)⟩


def joinbox7_rLRRRLLRRL : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((1 : ℚ) / 2), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩


def joinbox7_rLRRRLLRRLL : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩


def joinbox7_rLRRRLLRRLR : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩


def joinbox7_rLRRRLLRRR : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((1 : ℚ) / 2), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩


def joinbox7_rLRRRLLRRRL : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩


def joinbox7_rLRRRLLRRRR : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩


def joinbox7_rLRRRLR : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((1 : ℚ) / 2), ((1 : ℚ) / 3), ((5 : ℚ) / 12), ((29 : ℚ) / 32), ((37 : ℚ) / 40)⟩


def joinbox7_rLRRRLRL : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((7 : ℚ) / 16), ((1 : ℚ) / 3), ((5 : ℚ) / 12), ((29 : ℚ) / 32), ((37 : ℚ) / 40)⟩


def joinbox7_rLRRRLRLL : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((7 : ℚ) / 16), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((29 : ℚ) / 32), ((37 : ℚ) / 40)⟩


def joinbox7_rLRRRLRLLL : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((7 : ℚ) / 16), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩


def joinbox7_rLRRRLRLLLL : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩


def joinbox7_rLRRRLRLLLR : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩


def joinbox7_rLRRRLRLLR : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((7 : ℚ) / 16), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩


def joinbox7_rLRRRLRLLRL : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩


def joinbox7_rLRRRLRLLRR : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩


def joinbox7_rLRRRLRLR : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((7 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((29 : ℚ) / 32), ((37 : ℚ) / 40)⟩


def joinbox7_rLRRRLRLRL : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((7 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩


def joinbox7_rLRRRLRLRLL : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩


def joinbox7_rLRRRLRLRLR : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩


def joinbox7_rLRRRLRLRR : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((7 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩


def joinbox7_rLRRRLRLRRL : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩


def joinbox7_rLRRRLRLRRR : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩


def joinbox7_rLRRRLRR : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((1 : ℚ) / 2), ((1 : ℚ) / 3), ((5 : ℚ) / 12), ((29 : ℚ) / 32), ((37 : ℚ) / 40)⟩


def joinbox7_rLRRRLRRL : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((1 : ℚ) / 2), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((29 : ℚ) / 32), ((37 : ℚ) / 40)⟩


def joinbox7_rLRRRLRRLL : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((1 : ℚ) / 2), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩


def joinbox7_rLRRRLRRLLL : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩


def joinbox7_rLRRRLRRLLR : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩


def joinbox7_rLRRRLRRLR : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((1 : ℚ) / 2), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩


def joinbox7_rLRRRLRRLRL : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩


def joinbox7_rLRRRLRRLRR : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩


def joinbox7_rLRRRLRRR : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((1 : ℚ) / 2), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((29 : ℚ) / 32), ((37 : ℚ) / 40)⟩


def joinbox7_rLRRRLRRRL : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((1 : ℚ) / 2), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩


def joinbox7_rLRRRLRRRLL : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩


def joinbox7_rLRRRLRRRLR : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩


def joinbox7_rLRRRLRRRR : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((1 : ℚ) / 2), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩


def joinbox7_rLRRRLRRRRL : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩


def joinbox7_rLRRRLRRRRR : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩


theorem sound7 : LRCompactVBoxSound box7 :=
  (LRCompactVBoxSound.join (box := box7) .chi ((29 : ℚ) / 32)
    (LRCompactVBoxSound.join (box := joinbox7_rLRRRLL) .s ((7 : ℚ) / 16)
      (LRCompactVBoxSound.join (box := joinbox7_rLRRRLLL) .k ((3 : ℚ) / 8)
        (LRCompactVBoxSound.join (box := joinbox7_rLRRRLLLL) .chi ((287 : ℚ) / 320)
          (LRCompactVBoxSound.join (box := joinbox7_rLRRRLLLLL) .s ((13 : ℚ) / 32)
            (LRCompactVBoxSound.join (box := joinbox7_rLRRRLLLLLL) .k ((17 : ℚ) / 48)
              subsound7_0
              subsound7_1)
            (LRCompactVBoxSound.join (box := joinbox7_rLRRRLLLLLR) .k ((17 : ℚ) / 48)
              subsound7_2
              subsound7_3))
          (LRCompactVBoxSound.join (box := joinbox7_rLRRRLLLLR) .s ((13 : ℚ) / 32)
            (LRCompactVBoxSound.join (box := joinbox7_rLRRRLLLLRL) .k ((17 : ℚ) / 48)
              subsound7_4
              subsound7_5)
            (LRCompactVBoxSound.join (box := joinbox7_rLRRRLLLLRR) .k ((17 : ℚ) / 48)
              subsound7_6
              subsound7_7)))
        (LRCompactVBoxSound.join (box := joinbox7_rLRRRLLLR) .chi ((287 : ℚ) / 320)
          (LRCompactVBoxSound.join (box := joinbox7_rLRRRLLLRL) .s ((13 : ℚ) / 32)
            (LRCompactVBoxSound.join (box := joinbox7_rLRRRLLLRLL) .k ((19 : ℚ) / 48)
              subsound7_8
              subsound7_9)
            (LRCompactVBoxSound.join (box := joinbox7_rLRRRLLLRLR) .k ((19 : ℚ) / 48)
              subsound7_10
              subsound7_11))
          (LRCompactVBoxSound.join (box := joinbox7_rLRRRLLLRR) .s ((13 : ℚ) / 32)
            (LRCompactVBoxSound.join (box := joinbox7_rLRRRLLLRRL) .k ((19 : ℚ) / 48)
              subsound7_12
              subsound7_13)
            (LRCompactVBoxSound.join (box := joinbox7_rLRRRLLLRRR) .k ((19 : ℚ) / 48)
              subsound7_14
              subsound7_15))))
      (LRCompactVBoxSound.join (box := joinbox7_rLRRRLLR) .k ((3 : ℚ) / 8)
        (LRCompactVBoxSound.join (box := joinbox7_rLRRRLLRL) .chi ((287 : ℚ) / 320)
          (LRCompactVBoxSound.join (box := joinbox7_rLRRRLLRLL) .s ((15 : ℚ) / 32)
            (LRCompactVBoxSound.join (box := joinbox7_rLRRRLLRLLL) .k ((17 : ℚ) / 48)
              subsound7_16
              subsound7_17)
            (LRCompactVBoxSound.join (box := joinbox7_rLRRRLLRLLR) .k ((17 : ℚ) / 48)
              subsound7_18
              subsound7_19))
          (LRCompactVBoxSound.join (box := joinbox7_rLRRRLLRLR) .s ((15 : ℚ) / 32)
            (LRCompactVBoxSound.join (box := joinbox7_rLRRRLLRLRL) .k ((17 : ℚ) / 48)
              subsound7_20
              subsound7_21)
            (LRCompactVBoxSound.join (box := joinbox7_rLRRRLLRLRR) .k ((17 : ℚ) / 48)
              subsound7_22
              subsound7_23)))
        (LRCompactVBoxSound.join (box := joinbox7_rLRRRLLRR) .chi ((287 : ℚ) / 320)
          (LRCompactVBoxSound.join (box := joinbox7_rLRRRLLRRL) .s ((15 : ℚ) / 32)
            (LRCompactVBoxSound.join (box := joinbox7_rLRRRLLRRLL) .k ((19 : ℚ) / 48)
              subsound7_24
              subsound7_25)
            (LRCompactVBoxSound.join (box := joinbox7_rLRRRLLRRLR) .k ((19 : ℚ) / 48)
              subsound7_26
              subsound7_27))
          (LRCompactVBoxSound.join (box := joinbox7_rLRRRLLRRR) .s ((15 : ℚ) / 32)
            (LRCompactVBoxSound.join (box := joinbox7_rLRRRLLRRRL) .k ((19 : ℚ) / 48)
              subsound7_28
              subsound7_29)
            (LRCompactVBoxSound.join (box := joinbox7_rLRRRLLRRRR) .k ((19 : ℚ) / 48)
              subsound7_30
              subsound7_31)))))
    (LRCompactVBoxSound.join (box := joinbox7_rLRRRLR) .s ((7 : ℚ) / 16)
      (LRCompactVBoxSound.join (box := joinbox7_rLRRRLRL) .k ((3 : ℚ) / 8)
        (LRCompactVBoxSound.join (box := joinbox7_rLRRRLRLL) .chi ((293 : ℚ) / 320)
          (LRCompactVBoxSound.join (box := joinbox7_rLRRRLRLLL) .s ((13 : ℚ) / 32)
            (LRCompactVBoxSound.join (box := joinbox7_rLRRRLRLLLL) .k ((17 : ℚ) / 48)
              subsound7_32
              subsound7_33)
            (LRCompactVBoxSound.join (box := joinbox7_rLRRRLRLLLR) .k ((17 : ℚ) / 48)
              subsound7_34
              subsound7_35))
          (LRCompactVBoxSound.join (box := joinbox7_rLRRRLRLLR) .s ((13 : ℚ) / 32)
            (LRCompactVBoxSound.join (box := joinbox7_rLRRRLRLLRL) .k ((17 : ℚ) / 48)
              subsound7_36
              subsound7_37)
            (LRCompactVBoxSound.join (box := joinbox7_rLRRRLRLLRR) .k ((17 : ℚ) / 48)
              subsound7_38
              subsound7_39)))
        (LRCompactVBoxSound.join (box := joinbox7_rLRRRLRLR) .chi ((293 : ℚ) / 320)
          (LRCompactVBoxSound.join (box := joinbox7_rLRRRLRLRL) .s ((13 : ℚ) / 32)
            (LRCompactVBoxSound.join (box := joinbox7_rLRRRLRLRLL) .k ((19 : ℚ) / 48)
              subsound7_40
              subsound7_41)
            (LRCompactVBoxSound.join (box := joinbox7_rLRRRLRLRLR) .k ((19 : ℚ) / 48)
              subsound7_42
              subsound7_43))
          (LRCompactVBoxSound.join (box := joinbox7_rLRRRLRLRR) .s ((13 : ℚ) / 32)
            (LRCompactVBoxSound.join (box := joinbox7_rLRRRLRLRRL) .k ((19 : ℚ) / 48)
              subsound7_44
              subsound7_45)
            (LRCompactVBoxSound.join (box := joinbox7_rLRRRLRLRRR) .k ((19 : ℚ) / 48)
              subsound7_46
              subsound7_47))))
      (LRCompactVBoxSound.join (box := joinbox7_rLRRRLRR) .k ((3 : ℚ) / 8)
        (LRCompactVBoxSound.join (box := joinbox7_rLRRRLRRL) .chi ((293 : ℚ) / 320)
          (LRCompactVBoxSound.join (box := joinbox7_rLRRRLRRLL) .s ((15 : ℚ) / 32)
            (LRCompactVBoxSound.join (box := joinbox7_rLRRRLRRLLL) .k ((17 : ℚ) / 48)
              subsound7_48
              subsound7_49)
            (LRCompactVBoxSound.join (box := joinbox7_rLRRRLRRLLR) .k ((17 : ℚ) / 48)
              subsound7_50
              subsound7_51))
          (LRCompactVBoxSound.join (box := joinbox7_rLRRRLRRLR) .s ((15 : ℚ) / 32)
            (LRCompactVBoxSound.join (box := joinbox7_rLRRRLRRLRL) .k ((17 : ℚ) / 48)
              subsound7_52
              subsound7_53)
            (LRCompactVBoxSound.join (box := joinbox7_rLRRRLRRLRR) .k ((17 : ℚ) / 48)
              subsound7_54
              subsound7_55)))
        (LRCompactVBoxSound.join (box := joinbox7_rLRRRLRRR) .chi ((293 : ℚ) / 320)
          (LRCompactVBoxSound.join (box := joinbox7_rLRRRLRRRL) .s ((15 : ℚ) / 32)
            (LRCompactVBoxSound.join (box := joinbox7_rLRRRLRRRLL) .k ((19 : ℚ) / 48)
              subsound7_56
              subsound7_57)
            (LRCompactVBoxSound.join (box := joinbox7_rLRRRLRRRLR) .k ((19 : ℚ) / 48)
              subsound7_58
              subsound7_59))
          (LRCompactVBoxSound.join (box := joinbox7_rLRRRLRRRR) .s ((15 : ℚ) / 32)
            (LRCompactVBoxSound.join (box := joinbox7_rLRRRLRRRRL) .k ((19 : ℚ) / 48)
              subsound7_60
              subsound7_61)
            (LRCompactVBoxSound.join (box := joinbox7_rLRRRLRRRRR) .k ((19 : ℚ) / 48)
              subsound7_62
              subsound7_63))))))

end CourtadeKumar.GeneratedLRCompactVLowR
