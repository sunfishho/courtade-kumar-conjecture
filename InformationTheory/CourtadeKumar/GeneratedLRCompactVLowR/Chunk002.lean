import InformationTheory.CourtadeKumar.LRCompactVBasicReplay

/-! Frozen basic compact-V replay.
Plan SHA-256: ce3f7a498b2b9caf346dcf88ce7861f8cc091af8cd93f5624d7684e21322ecd5
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CourtadeKumar.GeneratedLRCompactVLowR

-- 108 accepted leaves below path rLLR.
def box2 : CertificateBox where
  sLo := (0 : ℚ)
  sHi := ((1 : ℚ) / 4)
  kLo := ((1 : ℚ) / 3)
  kHi := ((1 : ℚ) / 2)
  chiLo := ((71 : ℚ) / 80)
  chiHi := ((37 : ℚ) / 40)


def subbox2_0 : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 16), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩

theorem checked2_0 :
    LRCompactVLeafParameters.check subbox2_0 .short = true := by decide +kernel

theorem subsound2_0 : LRCompactVBoxSound subbox2_0 :=
  LRCompactVLeafParameters.sound checked2_0


def subbox2_1 : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 16), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩

theorem checked2_1 :
    LRCompactVLeafParameters.check subbox2_1 .short = true := by decide +kernel

theorem subsound2_1 : LRCompactVBoxSound subbox2_1 :=
  LRCompactVLeafParameters.sound checked2_1


def subbox2_2 : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩

theorem checked2_2 :
    LRCompactVLeafParameters.check subbox2_2 .short = true := by decide +kernel

theorem subsound2_2 : LRCompactVBoxSound subbox2_2 :=
  LRCompactVLeafParameters.sound checked2_2


def subbox2_3 : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩

theorem checked2_3 :
    LRCompactVLeafParameters.check subbox2_3 .short = true := by decide +kernel

theorem subsound2_3 : LRCompactVBoxSound subbox2_3 :=
  LRCompactVLeafParameters.sound checked2_3


def subbox2_4 : CertificateBox :=
  ⟨((1 : ℚ) / 16), ((1 : ℚ) / 8), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩

theorem checked2_4 :
    LRCompactVLeafParameters.check subbox2_4 .short = true := by decide +kernel

theorem subsound2_4 : LRCompactVBoxSound subbox2_4 :=
  LRCompactVLeafParameters.sound checked2_4


def subbox2_5 : CertificateBox :=
  ⟨((1 : ℚ) / 16), ((1 : ℚ) / 8), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩

theorem checked2_5 :
    LRCompactVLeafParameters.check subbox2_5 .short = true := by decide +kernel

theorem subsound2_5 : LRCompactVBoxSound subbox2_5 :=
  LRCompactVLeafParameters.sound checked2_5


def subbox2_6 : CertificateBox :=
  ⟨((1 : ℚ) / 16), ((3 : ℚ) / 32), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩

theorem checked2_6 :
    LRCompactVLeafParameters.check subbox2_6 .short = true := by decide +kernel

theorem subsound2_6 : LRCompactVBoxSound subbox2_6 :=
  LRCompactVLeafParameters.sound checked2_6


def subbox2_7 : CertificateBox :=
  ⟨((3 : ℚ) / 32), ((1 : ℚ) / 8), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩

theorem checked2_7 :
    LRCompactVLeafParameters.check subbox2_7 .short = true := by decide +kernel

theorem subsound2_7 : LRCompactVBoxSound subbox2_7 :=
  LRCompactVLeafParameters.sound checked2_7


def subbox2_8 : CertificateBox :=
  ⟨((1 : ℚ) / 16), ((1 : ℚ) / 8), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩

theorem checked2_8 :
    LRCompactVLeafParameters.check subbox2_8 .long = true := by decide +kernel

theorem subsound2_8 : LRCompactVBoxSound subbox2_8 :=
  LRCompactVLeafParameters.sound checked2_8


def subbox2_9 : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 16), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((29 : ℚ) / 32), ((37 : ℚ) / 40)⟩

theorem checked2_9 :
    LRCompactVLeafParameters.check subbox2_9 .long = true := by decide +kernel

theorem subsound2_9 : LRCompactVBoxSound subbox2_9 :=
  LRCompactVLeafParameters.sound checked2_9


def subbox2_10 : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩

theorem checked2_10 :
    LRCompactVLeafParameters.check subbox2_10 .short = true := by decide +kernel

theorem subsound2_10 : LRCompactVBoxSound subbox2_10 :=
  LRCompactVLeafParameters.sound checked2_10


def subbox2_11 : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩

theorem checked2_11 :
    LRCompactVLeafParameters.check subbox2_11 .short = true := by decide +kernel

theorem subsound2_11 : LRCompactVBoxSound subbox2_11 :=
  LRCompactVLeafParameters.sound checked2_11


def subbox2_12 : CertificateBox :=
  ⟨((1 : ℚ) / 16), ((1 : ℚ) / 8), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩

theorem checked2_12 :
    LRCompactVLeafParameters.check subbox2_12 .short = true := by decide +kernel

theorem subsound2_12 : LRCompactVBoxSound subbox2_12 :=
  LRCompactVLeafParameters.sound checked2_12


def subbox2_13 : CertificateBox :=
  ⟨((1 : ℚ) / 16), ((1 : ℚ) / 8), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩

theorem checked2_13 :
    LRCompactVLeafParameters.check subbox2_13 .short = true := by decide +kernel

theorem subsound2_13 : LRCompactVBoxSound subbox2_13 :=
  LRCompactVLeafParameters.sound checked2_13


def subbox2_14 : CertificateBox :=
  ⟨((1 : ℚ) / 16), ((1 : ℚ) / 8), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩

theorem checked2_14 :
    LRCompactVLeafParameters.check subbox2_14 .long = true := by decide +kernel

theorem subsound2_14 : LRCompactVBoxSound subbox2_14 :=
  LRCompactVLeafParameters.sound checked2_14


def subbox2_15 : CertificateBox :=
  ⟨((1 : ℚ) / 16), ((1 : ℚ) / 8), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩

theorem checked2_15 :
    LRCompactVLeafParameters.check subbox2_15 .short = true := by decide +kernel

theorem subsound2_15 : LRCompactVBoxSound subbox2_15 :=
  LRCompactVLeafParameters.sound checked2_15


def subbox2_16 : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩

theorem checked2_16 :
    LRCompactVLeafParameters.check subbox2_16 .long = true := by decide +kernel

theorem subsound2_16 : LRCompactVBoxSound subbox2_16 :=
  LRCompactVLeafParameters.sound checked2_16


def subbox2_17 : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩

theorem checked2_17 :
    LRCompactVLeafParameters.check subbox2_17 .long = true := by decide +kernel

theorem subsound2_17 : LRCompactVBoxSound subbox2_17 :=
  LRCompactVLeafParameters.sound checked2_17


def subbox2_18 : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 32), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩

theorem checked2_18 :
    LRCompactVLeafParameters.check subbox2_18 .short = true := by decide +kernel

theorem subsound2_18 : LRCompactVBoxSound subbox2_18 :=
  LRCompactVLeafParameters.sound checked2_18


def subbox2_19 : CertificateBox :=
  ⟨((1 : ℚ) / 32), ((1 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩

theorem checked2_19 :
    LRCompactVLeafParameters.check subbox2_19 .short = true := by decide +kernel

theorem subsound2_19 : LRCompactVBoxSound subbox2_19 :=
  LRCompactVLeafParameters.sound checked2_19


def subbox2_20 : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 32), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩

theorem checked2_20 :
    LRCompactVLeafParameters.check subbox2_20 .short = true := by decide +kernel

theorem subsound2_20 : LRCompactVBoxSound subbox2_20 :=
  LRCompactVLeafParameters.sound checked2_20


def subbox2_21 : CertificateBox :=
  ⟨((1 : ℚ) / 32), ((1 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩

theorem checked2_21 :
    LRCompactVLeafParameters.check subbox2_21 .short = true := by decide +kernel

theorem subsound2_21 : LRCompactVBoxSound subbox2_21 :=
  LRCompactVLeafParameters.sound checked2_21


def subbox2_22 : CertificateBox :=
  ⟨((1 : ℚ) / 16), ((3 : ℚ) / 32), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩

theorem checked2_22 :
    LRCompactVLeafParameters.check subbox2_22 .short = true := by decide +kernel

theorem subsound2_22 : LRCompactVBoxSound subbox2_22 :=
  LRCompactVLeafParameters.sound checked2_22


def subbox2_23 : CertificateBox :=
  ⟨((3 : ℚ) / 32), ((1 : ℚ) / 8), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩

theorem checked2_23 :
    LRCompactVLeafParameters.check subbox2_23 .short = true := by decide +kernel

theorem subsound2_23 : LRCompactVBoxSound subbox2_23 :=
  LRCompactVLeafParameters.sound checked2_23


def subbox2_24 : CertificateBox :=
  ⟨((1 : ℚ) / 16), ((3 : ℚ) / 32), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩

theorem checked2_24 :
    LRCompactVLeafParameters.check subbox2_24 .short = true := by decide +kernel

theorem subsound2_24 : LRCompactVBoxSound subbox2_24 :=
  LRCompactVLeafParameters.sound checked2_24


def subbox2_25 : CertificateBox :=
  ⟨((3 : ℚ) / 32), ((1 : ℚ) / 8), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩

theorem checked2_25 :
    LRCompactVLeafParameters.check subbox2_25 .short = true := by decide +kernel

theorem subsound2_25 : LRCompactVBoxSound subbox2_25 :=
  LRCompactVLeafParameters.sound checked2_25


def subbox2_26 : CertificateBox :=
  ⟨((1 : ℚ) / 16), ((3 : ℚ) / 32), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩

theorem checked2_26 :
    LRCompactVLeafParameters.check subbox2_26 .short = true := by decide +kernel

theorem subsound2_26 : LRCompactVBoxSound subbox2_26 :=
  LRCompactVLeafParameters.sound checked2_26


def subbox2_27 : CertificateBox :=
  ⟨((3 : ℚ) / 32), ((1 : ℚ) / 8), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩

theorem checked2_27 :
    LRCompactVLeafParameters.check subbox2_27 .short = true := by decide +kernel

theorem subsound2_27 : LRCompactVBoxSound subbox2_27 :=
  LRCompactVLeafParameters.sound checked2_27


def subbox2_28 : CertificateBox :=
  ⟨((1 : ℚ) / 16), ((3 : ℚ) / 32), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩

theorem checked2_28 :
    LRCompactVLeafParameters.check subbox2_28 .short = true := by decide +kernel

theorem subsound2_28 : LRCompactVBoxSound subbox2_28 :=
  LRCompactVLeafParameters.sound checked2_28


def subbox2_29 : CertificateBox :=
  ⟨((3 : ℚ) / 32), ((1 : ℚ) / 8), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩

theorem checked2_29 :
    LRCompactVLeafParameters.check subbox2_29 .short = true := by decide +kernel

theorem subsound2_29 : LRCompactVBoxSound subbox2_29 :=
  LRCompactVLeafParameters.sound checked2_29


def subbox2_30 : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩

theorem checked2_30 :
    LRCompactVLeafParameters.check subbox2_30 .long = true := by decide +kernel

theorem subsound2_30 : LRCompactVBoxSound subbox2_30 :=
  LRCompactVLeafParameters.sound checked2_30


def subbox2_31 : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩

theorem checked2_31 :
    LRCompactVLeafParameters.check subbox2_31 .short = true := by decide +kernel

theorem subsound2_31 : LRCompactVBoxSound subbox2_31 :=
  LRCompactVLeafParameters.sound checked2_31


def subbox2_32 : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 32), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩

theorem checked2_32 :
    LRCompactVLeafParameters.check subbox2_32 .short = true := by decide +kernel

theorem subsound2_32 : LRCompactVBoxSound subbox2_32 :=
  LRCompactVLeafParameters.sound checked2_32


def subbox2_33 : CertificateBox :=
  ⟨((1 : ℚ) / 32), ((1 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩

theorem checked2_33 :
    LRCompactVLeafParameters.check subbox2_33 .short = true := by decide +kernel

theorem subsound2_33 : LRCompactVBoxSound subbox2_33 :=
  LRCompactVLeafParameters.sound checked2_33


def subbox2_34 : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 32), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩

theorem checked2_34 :
    LRCompactVLeafParameters.check subbox2_34 .short = true := by decide +kernel

theorem subsound2_34 : LRCompactVBoxSound subbox2_34 :=
  LRCompactVLeafParameters.sound checked2_34


def subbox2_35 : CertificateBox :=
  ⟨((1 : ℚ) / 32), ((1 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩

theorem checked2_35 :
    LRCompactVLeafParameters.check subbox2_35 .short = true := by decide +kernel

theorem subsound2_35 : LRCompactVBoxSound subbox2_35 :=
  LRCompactVLeafParameters.sound checked2_35


def subbox2_36 : CertificateBox :=
  ⟨((1 : ℚ) / 16), ((3 : ℚ) / 32), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩

theorem checked2_36 :
    LRCompactVLeafParameters.check subbox2_36 .short = true := by decide +kernel

theorem subsound2_36 : LRCompactVBoxSound subbox2_36 :=
  LRCompactVLeafParameters.sound checked2_36


def subbox2_37 : CertificateBox :=
  ⟨((3 : ℚ) / 32), ((1 : ℚ) / 8), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩

theorem checked2_37 :
    LRCompactVLeafParameters.check subbox2_37 .short = true := by decide +kernel

theorem subsound2_37 : LRCompactVBoxSound subbox2_37 :=
  LRCompactVLeafParameters.sound checked2_37


def subbox2_38 : CertificateBox :=
  ⟨((1 : ℚ) / 16), ((3 : ℚ) / 32), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩

theorem checked2_38 :
    LRCompactVLeafParameters.check subbox2_38 .short = true := by decide +kernel

theorem subsound2_38 : LRCompactVBoxSound subbox2_38 :=
  LRCompactVLeafParameters.sound checked2_38


def subbox2_39 : CertificateBox :=
  ⟨((3 : ℚ) / 32), ((1 : ℚ) / 8), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩

theorem checked2_39 :
    LRCompactVLeafParameters.check subbox2_39 .short = true := by decide +kernel

theorem subsound2_39 : LRCompactVBoxSound subbox2_39 :=
  LRCompactVLeafParameters.sound checked2_39


def subbox2_40 : CertificateBox :=
  ⟨((1 : ℚ) / 16), ((3 : ℚ) / 32), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩

theorem checked2_40 :
    LRCompactVLeafParameters.check subbox2_40 .short = true := by decide +kernel

theorem subsound2_40 : LRCompactVBoxSound subbox2_40 :=
  LRCompactVLeafParameters.sound checked2_40


def subbox2_41 : CertificateBox :=
  ⟨((3 : ℚ) / 32), ((1 : ℚ) / 8), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩

theorem checked2_41 :
    LRCompactVLeafParameters.check subbox2_41 .short = true := by decide +kernel

theorem subsound2_41 : LRCompactVBoxSound subbox2_41 :=
  LRCompactVLeafParameters.sound checked2_41


def subbox2_42 : CertificateBox :=
  ⟨((1 : ℚ) / 16), ((3 : ℚ) / 32), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩

theorem checked2_42 :
    LRCompactVLeafParameters.check subbox2_42 .short = true := by decide +kernel

theorem subsound2_42 : LRCompactVBoxSound subbox2_42 :=
  LRCompactVLeafParameters.sound checked2_42


def subbox2_43 : CertificateBox :=
  ⟨((3 : ℚ) / 32), ((1 : ℚ) / 8), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩

theorem checked2_43 :
    LRCompactVLeafParameters.check subbox2_43 .short = true := by decide +kernel

theorem subsound2_43 : LRCompactVBoxSound subbox2_43 :=
  LRCompactVLeafParameters.sound checked2_43


def subbox2_44 : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((5 : ℚ) / 32), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩

theorem checked2_44 :
    LRCompactVLeafParameters.check subbox2_44 .short = true := by decide +kernel

theorem subsound2_44 : LRCompactVBoxSound subbox2_44 :=
  LRCompactVLeafParameters.sound checked2_44


def subbox2_45 : CertificateBox :=
  ⟨((5 : ℚ) / 32), ((3 : ℚ) / 16), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩

theorem checked2_45 :
    LRCompactVLeafParameters.check subbox2_45 .short = true := by decide +kernel

theorem subsound2_45 : LRCompactVBoxSound subbox2_45 :=
  LRCompactVLeafParameters.sound checked2_45


def subbox2_46 : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((5 : ℚ) / 32), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩

theorem checked2_46 :
    LRCompactVLeafParameters.check subbox2_46 .short = true := by decide +kernel

theorem subsound2_46 : LRCompactVBoxSound subbox2_46 :=
  LRCompactVLeafParameters.sound checked2_46


def subbox2_47 : CertificateBox :=
  ⟨((5 : ℚ) / 32), ((3 : ℚ) / 16), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩

theorem checked2_47 :
    LRCompactVLeafParameters.check subbox2_47 .short = true := by decide +kernel

theorem subsound2_47 : LRCompactVBoxSound subbox2_47 :=
  LRCompactVLeafParameters.sound checked2_47


def subbox2_48 : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((5 : ℚ) / 32), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩

theorem checked2_48 :
    LRCompactVLeafParameters.check subbox2_48 .short = true := by decide +kernel

theorem subsound2_48 : LRCompactVBoxSound subbox2_48 :=
  LRCompactVLeafParameters.sound checked2_48


def subbox2_49 : CertificateBox :=
  ⟨((5 : ℚ) / 32), ((3 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩

theorem checked2_49 :
    LRCompactVLeafParameters.check subbox2_49 .short = true := by decide +kernel

theorem subsound2_49 : LRCompactVBoxSound subbox2_49 :=
  LRCompactVLeafParameters.sound checked2_49


def subbox2_50 : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((5 : ℚ) / 32), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩

theorem checked2_50 :
    LRCompactVLeafParameters.check subbox2_50 .short = true := by decide +kernel

theorem subsound2_50 : LRCompactVBoxSound subbox2_50 :=
  LRCompactVLeafParameters.sound checked2_50


def subbox2_51 : CertificateBox :=
  ⟨((5 : ℚ) / 32), ((3 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩

theorem checked2_51 :
    LRCompactVLeafParameters.check subbox2_51 .short = true := by decide +kernel

theorem subsound2_51 : LRCompactVBoxSound subbox2_51 :=
  LRCompactVLeafParameters.sound checked2_51


def subbox2_52 : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((7 : ℚ) / 32), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩

theorem checked2_52 :
    LRCompactVLeafParameters.check subbox2_52 .short = true := by decide +kernel

theorem subsound2_52 : LRCompactVBoxSound subbox2_52 :=
  LRCompactVLeafParameters.sound checked2_52


def subbox2_53 : CertificateBox :=
  ⟨((7 : ℚ) / 32), ((1 : ℚ) / 4), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩

theorem checked2_53 :
    LRCompactVLeafParameters.check subbox2_53 .short = true := by decide +kernel

theorem subsound2_53 : LRCompactVBoxSound subbox2_53 :=
  LRCompactVLeafParameters.sound checked2_53


def subbox2_54 : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((7 : ℚ) / 32), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩

theorem checked2_54 :
    LRCompactVLeafParameters.check subbox2_54 .short = true := by decide +kernel

theorem subsound2_54 : LRCompactVBoxSound subbox2_54 :=
  LRCompactVLeafParameters.sound checked2_54


def subbox2_55 : CertificateBox :=
  ⟨((7 : ℚ) / 32), ((1 : ℚ) / 4), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩

theorem checked2_55 :
    LRCompactVLeafParameters.check subbox2_55 .short = true := by decide +kernel

theorem subsound2_55 : LRCompactVBoxSound subbox2_55 :=
  LRCompactVLeafParameters.sound checked2_55


def subbox2_56 : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((7 : ℚ) / 32), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩

theorem checked2_56 :
    LRCompactVLeafParameters.check subbox2_56 .short = true := by decide +kernel

theorem subsound2_56 : LRCompactVBoxSound subbox2_56 :=
  LRCompactVLeafParameters.sound checked2_56


def subbox2_57 : CertificateBox :=
  ⟨((7 : ℚ) / 32), ((1 : ℚ) / 4), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩

theorem checked2_57 :
    LRCompactVLeafParameters.check subbox2_57 .short = true := by decide +kernel

theorem subsound2_57 : LRCompactVBoxSound subbox2_57 :=
  LRCompactVLeafParameters.sound checked2_57


def subbox2_58 : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((7 : ℚ) / 32), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩

theorem checked2_58 :
    LRCompactVLeafParameters.check subbox2_58 .short = true := by decide +kernel

theorem subsound2_58 : LRCompactVBoxSound subbox2_58 :=
  LRCompactVLeafParameters.sound checked2_58


def subbox2_59 : CertificateBox :=
  ⟨((7 : ℚ) / 32), ((1 : ℚ) / 4), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩

theorem checked2_59 :
    LRCompactVLeafParameters.check subbox2_59 .short = true := by decide +kernel

theorem subsound2_59 : LRCompactVBoxSound subbox2_59 :=
  LRCompactVLeafParameters.sound checked2_59


def subbox2_60 : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((3 : ℚ) / 16), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩

theorem checked2_60 :
    LRCompactVLeafParameters.check subbox2_60 .long = true := by decide +kernel

theorem subsound2_60 : LRCompactVBoxSound subbox2_60 :=
  LRCompactVLeafParameters.sound checked2_60


def subbox2_61 : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((3 : ℚ) / 16), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩

theorem checked2_61 :
    LRCompactVLeafParameters.check subbox2_61 .long = true := by decide +kernel

theorem subsound2_61 : LRCompactVBoxSound subbox2_61 :=
  LRCompactVLeafParameters.sound checked2_61


def subbox2_62 : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((5 : ℚ) / 32), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩

theorem checked2_62 :
    LRCompactVLeafParameters.check subbox2_62 .short = true := by decide +kernel

theorem subsound2_62 : LRCompactVBoxSound subbox2_62 :=
  LRCompactVLeafParameters.sound checked2_62


def subbox2_63 : CertificateBox :=
  ⟨((5 : ℚ) / 32), ((3 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩

theorem checked2_63 :
    LRCompactVLeafParameters.check subbox2_63 .short = true := by decide +kernel

theorem subsound2_63 : LRCompactVBoxSound subbox2_63 :=
  LRCompactVLeafParameters.sound checked2_63


def subbox2_64 : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((5 : ℚ) / 32), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩

theorem checked2_64 :
    LRCompactVLeafParameters.check subbox2_64 .short = true := by decide +kernel

theorem subsound2_64 : LRCompactVBoxSound subbox2_64 :=
  LRCompactVLeafParameters.sound checked2_64


def subbox2_65 : CertificateBox :=
  ⟨((5 : ℚ) / 32), ((3 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩

theorem checked2_65 :
    LRCompactVLeafParameters.check subbox2_65 .short = true := by decide +kernel

theorem subsound2_65 : LRCompactVBoxSound subbox2_65 :=
  LRCompactVLeafParameters.sound checked2_65


def subbox2_66 : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((7 : ℚ) / 32), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩

theorem checked2_66 :
    LRCompactVLeafParameters.check subbox2_66 .short = true := by decide +kernel

theorem subsound2_66 : LRCompactVBoxSound subbox2_66 :=
  LRCompactVLeafParameters.sound checked2_66


def subbox2_67 : CertificateBox :=
  ⟨((7 : ℚ) / 32), ((1 : ℚ) / 4), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩

theorem checked2_67 :
    LRCompactVLeafParameters.check subbox2_67 .short = true := by decide +kernel

theorem subsound2_67 : LRCompactVBoxSound subbox2_67 :=
  LRCompactVLeafParameters.sound checked2_67


def subbox2_68 : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((7 : ℚ) / 32), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩

theorem checked2_68 :
    LRCompactVLeafParameters.check subbox2_68 .short = true := by decide +kernel

theorem subsound2_68 : LRCompactVBoxSound subbox2_68 :=
  LRCompactVLeafParameters.sound checked2_68


def subbox2_69 : CertificateBox :=
  ⟨((7 : ℚ) / 32), ((1 : ℚ) / 4), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩

theorem checked2_69 :
    LRCompactVLeafParameters.check subbox2_69 .short = true := by decide +kernel

theorem subsound2_69 : LRCompactVBoxSound subbox2_69 :=
  LRCompactVLeafParameters.sound checked2_69


def subbox2_70 : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((7 : ℚ) / 32), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩

theorem checked2_70 :
    LRCompactVLeafParameters.check subbox2_70 .short = true := by decide +kernel

theorem subsound2_70 : LRCompactVBoxSound subbox2_70 :=
  LRCompactVLeafParameters.sound checked2_70


def subbox2_71 : CertificateBox :=
  ⟨((7 : ℚ) / 32), ((1 : ℚ) / 4), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩

theorem checked2_71 :
    LRCompactVLeafParameters.check subbox2_71 .short = true := by decide +kernel

theorem subsound2_71 : LRCompactVBoxSound subbox2_71 :=
  LRCompactVLeafParameters.sound checked2_71


def subbox2_72 : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((7 : ℚ) / 32), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩

theorem checked2_72 :
    LRCompactVLeafParameters.check subbox2_72 .short = true := by decide +kernel

theorem subsound2_72 : LRCompactVBoxSound subbox2_72 :=
  LRCompactVLeafParameters.sound checked2_72


def subbox2_73 : CertificateBox :=
  ⟨((7 : ℚ) / 32), ((1 : ℚ) / 4), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩

theorem checked2_73 :
    LRCompactVLeafParameters.check subbox2_73 .short = true := by decide +kernel

theorem subsound2_73 : LRCompactVBoxSound subbox2_73 :=
  LRCompactVLeafParameters.sound checked2_73


def subbox2_74 : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((5 : ℚ) / 32), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩

theorem checked2_74 :
    LRCompactVLeafParameters.check subbox2_74 .short = true := by decide +kernel

theorem subsound2_74 : LRCompactVBoxSound subbox2_74 :=
  LRCompactVLeafParameters.sound checked2_74


def subbox2_75 : CertificateBox :=
  ⟨((5 : ℚ) / 32), ((3 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩

theorem checked2_75 :
    LRCompactVLeafParameters.check subbox2_75 .short = true := by decide +kernel

theorem subsound2_75 : LRCompactVBoxSound subbox2_75 :=
  LRCompactVLeafParameters.sound checked2_75


def subbox2_76 : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((5 : ℚ) / 32), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩

theorem checked2_76 :
    LRCompactVLeafParameters.check subbox2_76 .short = true := by decide +kernel

theorem subsound2_76 : LRCompactVBoxSound subbox2_76 :=
  LRCompactVLeafParameters.sound checked2_76


def subbox2_77 : CertificateBox :=
  ⟨((5 : ℚ) / 32), ((3 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩

theorem checked2_77 :
    LRCompactVLeafParameters.check subbox2_77 .short = true := by decide +kernel

theorem subsound2_77 : LRCompactVBoxSound subbox2_77 :=
  LRCompactVLeafParameters.sound checked2_77


def subbox2_78 : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((5 : ℚ) / 32), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩

theorem checked2_78 :
    LRCompactVLeafParameters.check subbox2_78 .short = true := by decide +kernel

theorem subsound2_78 : LRCompactVBoxSound subbox2_78 :=
  LRCompactVLeafParameters.sound checked2_78


def subbox2_79 : CertificateBox :=
  ⟨((5 : ℚ) / 32), ((3 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩

theorem checked2_79 :
    LRCompactVLeafParameters.check subbox2_79 .short = true := by decide +kernel

theorem subsound2_79 : LRCompactVBoxSound subbox2_79 :=
  LRCompactVLeafParameters.sound checked2_79


def subbox2_80 : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((5 : ℚ) / 32), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩

theorem checked2_80 :
    LRCompactVLeafParameters.check subbox2_80 .short = true := by decide +kernel

theorem subsound2_80 : LRCompactVBoxSound subbox2_80 :=
  LRCompactVLeafParameters.sound checked2_80


def subbox2_81 : CertificateBox :=
  ⟨((5 : ℚ) / 32), ((3 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩

theorem checked2_81 :
    LRCompactVLeafParameters.check subbox2_81 .short = true := by decide +kernel

theorem subsound2_81 : LRCompactVBoxSound subbox2_81 :=
  LRCompactVLeafParameters.sound checked2_81


def subbox2_82 : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((7 : ℚ) / 32), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩

theorem checked2_82 :
    LRCompactVLeafParameters.check subbox2_82 .short = true := by decide +kernel

theorem subsound2_82 : LRCompactVBoxSound subbox2_82 :=
  LRCompactVLeafParameters.sound checked2_82


def subbox2_83 : CertificateBox :=
  ⟨((7 : ℚ) / 32), ((1 : ℚ) / 4), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩

theorem checked2_83 :
    LRCompactVLeafParameters.check subbox2_83 .long = true := by decide +kernel

theorem subsound2_83 : LRCompactVBoxSound subbox2_83 :=
  LRCompactVLeafParameters.sound checked2_83


def subbox2_84 : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((7 : ℚ) / 32), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩

theorem checked2_84 :
    LRCompactVLeafParameters.check subbox2_84 .short = true := by decide +kernel

theorem subsound2_84 : LRCompactVBoxSound subbox2_84 :=
  LRCompactVLeafParameters.sound checked2_84


def subbox2_85 : CertificateBox :=
  ⟨((7 : ℚ) / 32), ((1 : ℚ) / 4), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩

theorem checked2_85 :
    LRCompactVLeafParameters.check subbox2_85 .long = true := by decide +kernel

theorem subsound2_85 : LRCompactVBoxSound subbox2_85 :=
  LRCompactVLeafParameters.sound checked2_85


def subbox2_86 : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((7 : ℚ) / 32), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩

theorem checked2_86 :
    LRCompactVLeafParameters.check subbox2_86 .long = true := by decide +kernel

theorem subsound2_86 : LRCompactVBoxSound subbox2_86 :=
  LRCompactVLeafParameters.sound checked2_86


def subbox2_87 : CertificateBox :=
  ⟨((7 : ℚ) / 32), ((1 : ℚ) / 4), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩

theorem checked2_87 :
    LRCompactVLeafParameters.check subbox2_87 .short = true := by decide +kernel

theorem subsound2_87 : LRCompactVBoxSound subbox2_87 :=
  LRCompactVLeafParameters.sound checked2_87


def subbox2_88 : CertificateBox :=
  ⟨((7 : ℚ) / 32), ((1 : ℚ) / 4), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩

theorem checked2_88 :
    LRCompactVLeafParameters.check subbox2_88 .short = true := by decide +kernel

theorem subsound2_88 : LRCompactVBoxSound subbox2_88 :=
  LRCompactVLeafParameters.sound checked2_88


def subbox2_89 : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((7 : ℚ) / 32), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩

theorem checked2_89 :
    LRCompactVLeafParameters.check subbox2_89 .long = true := by decide +kernel

theorem subsound2_89 : LRCompactVBoxSound subbox2_89 :=
  LRCompactVLeafParameters.sound checked2_89


def subbox2_90 : CertificateBox :=
  ⟨((7 : ℚ) / 32), ((1 : ℚ) / 4), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩

theorem checked2_90 :
    LRCompactVLeafParameters.check subbox2_90 .short = true := by decide +kernel

theorem subsound2_90 : LRCompactVBoxSound subbox2_90 :=
  LRCompactVLeafParameters.sound checked2_90


def subbox2_91 : CertificateBox :=
  ⟨((7 : ℚ) / 32), ((1 : ℚ) / 4), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩

theorem checked2_91 :
    LRCompactVLeafParameters.check subbox2_91 .short = true := by decide +kernel

theorem subsound2_91 : LRCompactVBoxSound subbox2_91 :=
  LRCompactVLeafParameters.sound checked2_91


def subbox2_92 : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((5 : ℚ) / 32), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩

theorem checked2_92 :
    LRCompactVLeafParameters.check subbox2_92 .short = true := by decide +kernel

theorem subsound2_92 : LRCompactVBoxSound subbox2_92 :=
  LRCompactVLeafParameters.sound checked2_92


def subbox2_93 : CertificateBox :=
  ⟨((5 : ℚ) / 32), ((3 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩

theorem checked2_93 :
    LRCompactVLeafParameters.check subbox2_93 .short = true := by decide +kernel

theorem subsound2_93 : LRCompactVBoxSound subbox2_93 :=
  LRCompactVLeafParameters.sound checked2_93


def subbox2_94 : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((5 : ℚ) / 32), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩

theorem checked2_94 :
    LRCompactVLeafParameters.check subbox2_94 .short = true := by decide +kernel

theorem subsound2_94 : LRCompactVBoxSound subbox2_94 :=
  LRCompactVLeafParameters.sound checked2_94


def subbox2_95 : CertificateBox :=
  ⟨((5 : ℚ) / 32), ((3 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩

theorem checked2_95 :
    LRCompactVLeafParameters.check subbox2_95 .short = true := by decide +kernel

theorem subsound2_95 : LRCompactVBoxSound subbox2_95 :=
  LRCompactVLeafParameters.sound checked2_95


def subbox2_96 : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((5 : ℚ) / 32), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩

theorem checked2_96 :
    LRCompactVLeafParameters.check subbox2_96 .short = true := by decide +kernel

theorem subsound2_96 : LRCompactVBoxSound subbox2_96 :=
  LRCompactVLeafParameters.sound checked2_96


def subbox2_97 : CertificateBox :=
  ⟨((5 : ℚ) / 32), ((3 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩

theorem checked2_97 :
    LRCompactVLeafParameters.check subbox2_97 .short = true := by decide +kernel

theorem subsound2_97 : LRCompactVBoxSound subbox2_97 :=
  LRCompactVLeafParameters.sound checked2_97


def subbox2_98 : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((5 : ℚ) / 32), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩

theorem checked2_98 :
    LRCompactVLeafParameters.check subbox2_98 .short = true := by decide +kernel

theorem subsound2_98 : LRCompactVBoxSound subbox2_98 :=
  LRCompactVLeafParameters.sound checked2_98


def subbox2_99 : CertificateBox :=
  ⟨((5 : ℚ) / 32), ((3 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩

theorem checked2_99 :
    LRCompactVLeafParameters.check subbox2_99 .short = true := by decide +kernel

theorem subsound2_99 : LRCompactVBoxSound subbox2_99 :=
  LRCompactVLeafParameters.sound checked2_99


def subbox2_100 : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((7 : ℚ) / 32), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩

theorem checked2_100 :
    LRCompactVLeafParameters.check subbox2_100 .short = true := by decide +kernel

theorem subsound2_100 : LRCompactVBoxSound subbox2_100 :=
  LRCompactVLeafParameters.sound checked2_100


def subbox2_101 : CertificateBox :=
  ⟨((7 : ℚ) / 32), ((1 : ℚ) / 4), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩

theorem checked2_101 :
    LRCompactVLeafParameters.check subbox2_101 .short = true := by decide +kernel

theorem subsound2_101 : LRCompactVBoxSound subbox2_101 :=
  LRCompactVLeafParameters.sound checked2_101


def subbox2_102 : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((7 : ℚ) / 32), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩

theorem checked2_102 :
    LRCompactVLeafParameters.check subbox2_102 .short = true := by decide +kernel

theorem subsound2_102 : LRCompactVBoxSound subbox2_102 :=
  LRCompactVLeafParameters.sound checked2_102


def subbox2_103 : CertificateBox :=
  ⟨((7 : ℚ) / 32), ((1 : ℚ) / 4), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩

theorem checked2_103 :
    LRCompactVLeafParameters.check subbox2_103 .short = true := by decide +kernel

theorem subsound2_103 : LRCompactVBoxSound subbox2_103 :=
  LRCompactVLeafParameters.sound checked2_103


def subbox2_104 : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((7 : ℚ) / 32), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩

theorem checked2_104 :
    LRCompactVLeafParameters.check subbox2_104 .long = true := by decide +kernel

theorem subsound2_104 : LRCompactVBoxSound subbox2_104 :=
  LRCompactVLeafParameters.sound checked2_104


def subbox2_105 : CertificateBox :=
  ⟨((7 : ℚ) / 32), ((1 : ℚ) / 4), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩

theorem checked2_105 :
    LRCompactVLeafParameters.check subbox2_105 .long = true := by decide +kernel

theorem subsound2_105 : LRCompactVBoxSound subbox2_105 :=
  LRCompactVLeafParameters.sound checked2_105


def subbox2_106 : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((7 : ℚ) / 32), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩

theorem checked2_106 :
    LRCompactVLeafParameters.check subbox2_106 .accurateLog = true := by decide +kernel

theorem subsound2_106 : LRCompactVBoxSound subbox2_106 :=
  LRCompactVLeafParameters.sound checked2_106


def subbox2_107 : CertificateBox :=
  ⟨((7 : ℚ) / 32), ((1 : ℚ) / 4), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩

theorem checked2_107 :
    LRCompactVLeafParameters.check subbox2_107 .long = true := by decide +kernel

theorem subsound2_107 : LRCompactVBoxSound subbox2_107 :=
  LRCompactVLeafParameters.sound checked2_107


def joinbox2_rLLRL : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 8), ((1 : ℚ) / 3), ((1 : ℚ) / 2), ((71 : ℚ) / 80), ((37 : ℚ) / 40)⟩


def joinbox2_rLLRLL : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 8), ((1 : ℚ) / 3), ((5 : ℚ) / 12), ((71 : ℚ) / 80), ((37 : ℚ) / 40)⟩


def joinbox2_rLLRLLL : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 8), ((1 : ℚ) / 3), ((5 : ℚ) / 12), ((71 : ℚ) / 80), ((29 : ℚ) / 32)⟩


def joinbox2_rLLRLLLL : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 16), ((1 : ℚ) / 3), ((5 : ℚ) / 12), ((71 : ℚ) / 80), ((29 : ℚ) / 32)⟩


def joinbox2_rLLRLLLLL : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 16), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((71 : ℚ) / 80), ((29 : ℚ) / 32)⟩


def joinbox2_rLLRLLLLR : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((71 : ℚ) / 80), ((29 : ℚ) / 32)⟩


def joinbox2_rLLRLLLR : CertificateBox :=
  ⟨((1 : ℚ) / 16), ((1 : ℚ) / 8), ((1 : ℚ) / 3), ((5 : ℚ) / 12), ((71 : ℚ) / 80), ((29 : ℚ) / 32)⟩


def joinbox2_rLLRLLLRL : CertificateBox :=
  ⟨((1 : ℚ) / 16), ((1 : ℚ) / 8), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((71 : ℚ) / 80), ((29 : ℚ) / 32)⟩


def joinbox2_rLLRLLLRR : CertificateBox :=
  ⟨((1 : ℚ) / 16), ((1 : ℚ) / 8), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((71 : ℚ) / 80), ((29 : ℚ) / 32)⟩


def joinbox2_rLLRLLLRRL : CertificateBox :=
  ⟨((1 : ℚ) / 16), ((1 : ℚ) / 8), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩


def joinbox2_rLLRLLR : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 8), ((1 : ℚ) / 3), ((5 : ℚ) / 12), ((29 : ℚ) / 32), ((37 : ℚ) / 40)⟩


def joinbox2_rLLRLLRL : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 16), ((1 : ℚ) / 3), ((5 : ℚ) / 12), ((29 : ℚ) / 32), ((37 : ℚ) / 40)⟩


def joinbox2_rLLRLLRLR : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((29 : ℚ) / 32), ((37 : ℚ) / 40)⟩


def joinbox2_rLLRLLRR : CertificateBox :=
  ⟨((1 : ℚ) / 16), ((1 : ℚ) / 8), ((1 : ℚ) / 3), ((5 : ℚ) / 12), ((29 : ℚ) / 32), ((37 : ℚ) / 40)⟩


def joinbox2_rLLRLLRRL : CertificateBox :=
  ⟨((1 : ℚ) / 16), ((1 : ℚ) / 8), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((29 : ℚ) / 32), ((37 : ℚ) / 40)⟩


def joinbox2_rLLRLLRRR : CertificateBox :=
  ⟨((1 : ℚ) / 16), ((1 : ℚ) / 8), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((29 : ℚ) / 32), ((37 : ℚ) / 40)⟩


def joinbox2_rLLRLR : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 8), ((5 : ℚ) / 12), ((1 : ℚ) / 2), ((71 : ℚ) / 80), ((37 : ℚ) / 40)⟩


def joinbox2_rLLRLRL : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 8), ((5 : ℚ) / 12), ((1 : ℚ) / 2), ((71 : ℚ) / 80), ((29 : ℚ) / 32)⟩


def joinbox2_rLLRLRLL : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 16), ((5 : ℚ) / 12), ((1 : ℚ) / 2), ((71 : ℚ) / 80), ((29 : ℚ) / 32)⟩


def joinbox2_rLLRLRLLL : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((71 : ℚ) / 80), ((29 : ℚ) / 32)⟩


def joinbox2_rLLRLRLLR : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((71 : ℚ) / 80), ((29 : ℚ) / 32)⟩


def joinbox2_rLLRLRLLRL : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩


def joinbox2_rLLRLRLLRR : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩


def joinbox2_rLLRLRLR : CertificateBox :=
  ⟨((1 : ℚ) / 16), ((1 : ℚ) / 8), ((5 : ℚ) / 12), ((1 : ℚ) / 2), ((71 : ℚ) / 80), ((29 : ℚ) / 32)⟩


def joinbox2_rLLRLRLRL : CertificateBox :=
  ⟨((1 : ℚ) / 16), ((1 : ℚ) / 8), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((71 : ℚ) / 80), ((29 : ℚ) / 32)⟩


def joinbox2_rLLRLRLRLL : CertificateBox :=
  ⟨((1 : ℚ) / 16), ((1 : ℚ) / 8), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩


def joinbox2_rLLRLRLRLR : CertificateBox :=
  ⟨((1 : ℚ) / 16), ((1 : ℚ) / 8), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩


def joinbox2_rLLRLRLRR : CertificateBox :=
  ⟨((1 : ℚ) / 16), ((1 : ℚ) / 8), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((71 : ℚ) / 80), ((29 : ℚ) / 32)⟩


def joinbox2_rLLRLRLRRL : CertificateBox :=
  ⟨((1 : ℚ) / 16), ((1 : ℚ) / 8), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩


def joinbox2_rLLRLRLRRR : CertificateBox :=
  ⟨((1 : ℚ) / 16), ((1 : ℚ) / 8), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩


def joinbox2_rLLRLRR : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 8), ((5 : ℚ) / 12), ((1 : ℚ) / 2), ((29 : ℚ) / 32), ((37 : ℚ) / 40)⟩


def joinbox2_rLLRLRRL : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 16), ((5 : ℚ) / 12), ((1 : ℚ) / 2), ((29 : ℚ) / 32), ((37 : ℚ) / 40)⟩


def joinbox2_rLLRLRRLL : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((29 : ℚ) / 32), ((37 : ℚ) / 40)⟩


def joinbox2_rLLRLRRLR : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((29 : ℚ) / 32), ((37 : ℚ) / 40)⟩


def joinbox2_rLLRLRRLRL : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩


def joinbox2_rLLRLRRLRR : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩


def joinbox2_rLLRLRRR : CertificateBox :=
  ⟨((1 : ℚ) / 16), ((1 : ℚ) / 8), ((5 : ℚ) / 12), ((1 : ℚ) / 2), ((29 : ℚ) / 32), ((37 : ℚ) / 40)⟩


def joinbox2_rLLRLRRRL : CertificateBox :=
  ⟨((1 : ℚ) / 16), ((1 : ℚ) / 8), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((29 : ℚ) / 32), ((37 : ℚ) / 40)⟩


def joinbox2_rLLRLRRRLL : CertificateBox :=
  ⟨((1 : ℚ) / 16), ((1 : ℚ) / 8), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩


def joinbox2_rLLRLRRRLR : CertificateBox :=
  ⟨((1 : ℚ) / 16), ((1 : ℚ) / 8), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩


def joinbox2_rLLRLRRRR : CertificateBox :=
  ⟨((1 : ℚ) / 16), ((1 : ℚ) / 8), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((29 : ℚ) / 32), ((37 : ℚ) / 40)⟩


def joinbox2_rLLRLRRRRL : CertificateBox :=
  ⟨((1 : ℚ) / 16), ((1 : ℚ) / 8), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩


def joinbox2_rLLRLRRRRR : CertificateBox :=
  ⟨((1 : ℚ) / 16), ((1 : ℚ) / 8), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩


def joinbox2_rLLRR : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((1 : ℚ) / 4), ((1 : ℚ) / 3), ((1 : ℚ) / 2), ((71 : ℚ) / 80), ((37 : ℚ) / 40)⟩


def joinbox2_rLLRRL : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((1 : ℚ) / 4), ((1 : ℚ) / 3), ((5 : ℚ) / 12), ((71 : ℚ) / 80), ((37 : ℚ) / 40)⟩


def joinbox2_rLLRRLL : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((1 : ℚ) / 4), ((1 : ℚ) / 3), ((5 : ℚ) / 12), ((71 : ℚ) / 80), ((29 : ℚ) / 32)⟩


def joinbox2_rLLRRLLL : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((3 : ℚ) / 16), ((1 : ℚ) / 3), ((5 : ℚ) / 12), ((71 : ℚ) / 80), ((29 : ℚ) / 32)⟩


def joinbox2_rLLRRLLLL : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((3 : ℚ) / 16), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((71 : ℚ) / 80), ((29 : ℚ) / 32)⟩


def joinbox2_rLLRRLLLLL : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((3 : ℚ) / 16), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩


def joinbox2_rLLRRLLLLR : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((3 : ℚ) / 16), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩


def joinbox2_rLLRRLLLR : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((3 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((71 : ℚ) / 80), ((29 : ℚ) / 32)⟩


def joinbox2_rLLRRLLLRL : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((3 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩


def joinbox2_rLLRRLLLRR : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((3 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩


def joinbox2_rLLRRLLR : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((1 : ℚ) / 4), ((1 : ℚ) / 3), ((5 : ℚ) / 12), ((71 : ℚ) / 80), ((29 : ℚ) / 32)⟩


def joinbox2_rLLRRLLRL : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((1 : ℚ) / 4), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((71 : ℚ) / 80), ((29 : ℚ) / 32)⟩


def joinbox2_rLLRRLLRLL : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((1 : ℚ) / 4), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩


def joinbox2_rLLRRLLRLR : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((1 : ℚ) / 4), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩


def joinbox2_rLLRRLLRR : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((1 : ℚ) / 4), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((71 : ℚ) / 80), ((29 : ℚ) / 32)⟩


def joinbox2_rLLRRLLRRL : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((1 : ℚ) / 4), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩


def joinbox2_rLLRRLLRRR : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((1 : ℚ) / 4), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩


def joinbox2_rLLRRLR : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((1 : ℚ) / 4), ((1 : ℚ) / 3), ((5 : ℚ) / 12), ((29 : ℚ) / 32), ((37 : ℚ) / 40)⟩


def joinbox2_rLLRRLRL : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((3 : ℚ) / 16), ((1 : ℚ) / 3), ((5 : ℚ) / 12), ((29 : ℚ) / 32), ((37 : ℚ) / 40)⟩


def joinbox2_rLLRRLRLL : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((3 : ℚ) / 16), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((29 : ℚ) / 32), ((37 : ℚ) / 40)⟩


def joinbox2_rLLRRLRLR : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((3 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((29 : ℚ) / 32), ((37 : ℚ) / 40)⟩


def joinbox2_rLLRRLRLRL : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((3 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩


def joinbox2_rLLRRLRLRR : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((3 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩


def joinbox2_rLLRRLRR : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((1 : ℚ) / 4), ((1 : ℚ) / 3), ((5 : ℚ) / 12), ((29 : ℚ) / 32), ((37 : ℚ) / 40)⟩


def joinbox2_rLLRRLRRL : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((1 : ℚ) / 4), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((29 : ℚ) / 32), ((37 : ℚ) / 40)⟩


def joinbox2_rLLRRLRRLL : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((1 : ℚ) / 4), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩


def joinbox2_rLLRRLRRLR : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((1 : ℚ) / 4), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩


def joinbox2_rLLRRLRRR : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((1 : ℚ) / 4), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((29 : ℚ) / 32), ((37 : ℚ) / 40)⟩


def joinbox2_rLLRRLRRRL : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((1 : ℚ) / 4), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩


def joinbox2_rLLRRLRRRR : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((1 : ℚ) / 4), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩


def joinbox2_rLLRRR : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((1 : ℚ) / 4), ((5 : ℚ) / 12), ((1 : ℚ) / 2), ((71 : ℚ) / 80), ((37 : ℚ) / 40)⟩


def joinbox2_rLLRRRL : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((1 : ℚ) / 4), ((5 : ℚ) / 12), ((1 : ℚ) / 2), ((71 : ℚ) / 80), ((29 : ℚ) / 32)⟩


def joinbox2_rLLRRRLL : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((3 : ℚ) / 16), ((5 : ℚ) / 12), ((1 : ℚ) / 2), ((71 : ℚ) / 80), ((29 : ℚ) / 32)⟩


def joinbox2_rLLRRRLLL : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((3 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((71 : ℚ) / 80), ((29 : ℚ) / 32)⟩


def joinbox2_rLLRRRLLLL : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((3 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩


def joinbox2_rLLRRRLLLR : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((3 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩


def joinbox2_rLLRRRLLR : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((3 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((71 : ℚ) / 80), ((29 : ℚ) / 32)⟩


def joinbox2_rLLRRRLLRL : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((3 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩


def joinbox2_rLLRRRLLRR : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((3 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩


def joinbox2_rLLRRRLR : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((1 : ℚ) / 4), ((5 : ℚ) / 12), ((1 : ℚ) / 2), ((71 : ℚ) / 80), ((29 : ℚ) / 32)⟩


def joinbox2_rLLRRRLRL : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((1 : ℚ) / 4), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((71 : ℚ) / 80), ((29 : ℚ) / 32)⟩


def joinbox2_rLLRRRLRLL : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((1 : ℚ) / 4), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩


def joinbox2_rLLRRRLRLR : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((1 : ℚ) / 4), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩


def joinbox2_rLLRRRLRR : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((1 : ℚ) / 4), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((71 : ℚ) / 80), ((29 : ℚ) / 32)⟩


def joinbox2_rLLRRRLRRL : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((1 : ℚ) / 4), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩


def joinbox2_rLLRRRLRRLR : CertificateBox :=
  ⟨((7 : ℚ) / 32), ((1 : ℚ) / 4), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩


def joinbox2_rLLRRRLRRR : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((1 : ℚ) / 4), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩


def joinbox2_rLLRRRLRRRR : CertificateBox :=
  ⟨((7 : ℚ) / 32), ((1 : ℚ) / 4), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩


def joinbox2_rLLRRRR : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((1 : ℚ) / 4), ((5 : ℚ) / 12), ((1 : ℚ) / 2), ((29 : ℚ) / 32), ((37 : ℚ) / 40)⟩


def joinbox2_rLLRRRRL : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((3 : ℚ) / 16), ((5 : ℚ) / 12), ((1 : ℚ) / 2), ((29 : ℚ) / 32), ((37 : ℚ) / 40)⟩


def joinbox2_rLLRRRRLL : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((3 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((29 : ℚ) / 32), ((37 : ℚ) / 40)⟩


def joinbox2_rLLRRRRLLL : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((3 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩


def joinbox2_rLLRRRRLLR : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((3 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩


def joinbox2_rLLRRRRLR : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((3 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((29 : ℚ) / 32), ((37 : ℚ) / 40)⟩


def joinbox2_rLLRRRRLRL : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((3 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩


def joinbox2_rLLRRRRLRR : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((3 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩


def joinbox2_rLLRRRRR : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((1 : ℚ) / 4), ((5 : ℚ) / 12), ((1 : ℚ) / 2), ((29 : ℚ) / 32), ((37 : ℚ) / 40)⟩


def joinbox2_rLLRRRRRL : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((1 : ℚ) / 4), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((29 : ℚ) / 32), ((37 : ℚ) / 40)⟩


def joinbox2_rLLRRRRRLL : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((1 : ℚ) / 4), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩


def joinbox2_rLLRRRRRLR : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((1 : ℚ) / 4), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩


def joinbox2_rLLRRRRRR : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((1 : ℚ) / 4), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((29 : ℚ) / 32), ((37 : ℚ) / 40)⟩


def joinbox2_rLLRRRRRRL : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((1 : ℚ) / 4), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩


def joinbox2_rLLRRRRRRR : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((1 : ℚ) / 4), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩


theorem sound2 : LRCompactVBoxSound box2 :=
  (LRCompactVBoxSound.join (box := box2) .s ((1 : ℚ) / 8)
    (LRCompactVBoxSound.join (box := joinbox2_rLLRL) .k ((5 : ℚ) / 12)
      (LRCompactVBoxSound.join (box := joinbox2_rLLRLL) .chi ((29 : ℚ) / 32)
        (LRCompactVBoxSound.join (box := joinbox2_rLLRLLL) .s ((1 : ℚ) / 16)
          (LRCompactVBoxSound.join (box := joinbox2_rLLRLLLL) .k ((3 : ℚ) / 8)
            (LRCompactVBoxSound.join (box := joinbox2_rLLRLLLLL) .chi ((287 : ℚ) / 320)
              subsound2_0
              subsound2_1)
            (LRCompactVBoxSound.join (box := joinbox2_rLLRLLLLR) .chi ((287 : ℚ) / 320)
              subsound2_2
              subsound2_3))
          (LRCompactVBoxSound.join (box := joinbox2_rLLRLLLR) .k ((3 : ℚ) / 8)
            (LRCompactVBoxSound.join (box := joinbox2_rLLRLLLRL) .chi ((287 : ℚ) / 320)
              subsound2_4
              subsound2_5)
            (LRCompactVBoxSound.join (box := joinbox2_rLLRLLLRR) .chi ((287 : ℚ) / 320)
              (LRCompactVBoxSound.join (box := joinbox2_rLLRLLLRRL) .s ((3 : ℚ) / 32)
                subsound2_6
                subsound2_7)
              subsound2_8)))
        (LRCompactVBoxSound.join (box := joinbox2_rLLRLLR) .s ((1 : ℚ) / 16)
          (LRCompactVBoxSound.join (box := joinbox2_rLLRLLRL) .k ((3 : ℚ) / 8)
            subsound2_9
            (LRCompactVBoxSound.join (box := joinbox2_rLLRLLRLR) .chi ((293 : ℚ) / 320)
              subsound2_10
              subsound2_11))
          (LRCompactVBoxSound.join (box := joinbox2_rLLRLLRR) .k ((3 : ℚ) / 8)
            (LRCompactVBoxSound.join (box := joinbox2_rLLRLLRRL) .chi ((293 : ℚ) / 320)
              subsound2_12
              subsound2_13)
            (LRCompactVBoxSound.join (box := joinbox2_rLLRLLRRR) .chi ((293 : ℚ) / 320)
              subsound2_14
              subsound2_15))))
      (LRCompactVBoxSound.join (box := joinbox2_rLLRLR) .chi ((29 : ℚ) / 32)
        (LRCompactVBoxSound.join (box := joinbox2_rLLRLRL) .s ((1 : ℚ) / 16)
          (LRCompactVBoxSound.join (box := joinbox2_rLLRLRLL) .k ((11 : ℚ) / 24)
            (LRCompactVBoxSound.join (box := joinbox2_rLLRLRLLL) .chi ((287 : ℚ) / 320)
              subsound2_16
              subsound2_17)
            (LRCompactVBoxSound.join (box := joinbox2_rLLRLRLLR) .chi ((287 : ℚ) / 320)
              (LRCompactVBoxSound.join (box := joinbox2_rLLRLRLLRL) .s ((1 : ℚ) / 32)
                subsound2_18
                subsound2_19)
              (LRCompactVBoxSound.join (box := joinbox2_rLLRLRLLRR) .s ((1 : ℚ) / 32)
                subsound2_20
                subsound2_21)))
          (LRCompactVBoxSound.join (box := joinbox2_rLLRLRLR) .k ((11 : ℚ) / 24)
            (LRCompactVBoxSound.join (box := joinbox2_rLLRLRLRL) .chi ((287 : ℚ) / 320)
              (LRCompactVBoxSound.join (box := joinbox2_rLLRLRLRLL) .s ((3 : ℚ) / 32)
                subsound2_22
                subsound2_23)
              (LRCompactVBoxSound.join (box := joinbox2_rLLRLRLRLR) .s ((3 : ℚ) / 32)
                subsound2_24
                subsound2_25))
            (LRCompactVBoxSound.join (box := joinbox2_rLLRLRLRR) .chi ((287 : ℚ) / 320)
              (LRCompactVBoxSound.join (box := joinbox2_rLLRLRLRRL) .s ((3 : ℚ) / 32)
                subsound2_26
                subsound2_27)
              (LRCompactVBoxSound.join (box := joinbox2_rLLRLRLRRR) .s ((3 : ℚ) / 32)
                subsound2_28
                subsound2_29))))
        (LRCompactVBoxSound.join (box := joinbox2_rLLRLRR) .s ((1 : ℚ) / 16)
          (LRCompactVBoxSound.join (box := joinbox2_rLLRLRRL) .k ((11 : ℚ) / 24)
            (LRCompactVBoxSound.join (box := joinbox2_rLLRLRRLL) .chi ((293 : ℚ) / 320)
              subsound2_30
              subsound2_31)
            (LRCompactVBoxSound.join (box := joinbox2_rLLRLRRLR) .chi ((293 : ℚ) / 320)
              (LRCompactVBoxSound.join (box := joinbox2_rLLRLRRLRL) .s ((1 : ℚ) / 32)
                subsound2_32
                subsound2_33)
              (LRCompactVBoxSound.join (box := joinbox2_rLLRLRRLRR) .s ((1 : ℚ) / 32)
                subsound2_34
                subsound2_35)))
          (LRCompactVBoxSound.join (box := joinbox2_rLLRLRRR) .k ((11 : ℚ) / 24)
            (LRCompactVBoxSound.join (box := joinbox2_rLLRLRRRL) .chi ((293 : ℚ) / 320)
              (LRCompactVBoxSound.join (box := joinbox2_rLLRLRRRLL) .s ((3 : ℚ) / 32)
                subsound2_36
                subsound2_37)
              (LRCompactVBoxSound.join (box := joinbox2_rLLRLRRRLR) .s ((3 : ℚ) / 32)
                subsound2_38
                subsound2_39))
            (LRCompactVBoxSound.join (box := joinbox2_rLLRLRRRR) .chi ((293 : ℚ) / 320)
              (LRCompactVBoxSound.join (box := joinbox2_rLLRLRRRRL) .s ((3 : ℚ) / 32)
                subsound2_40
                subsound2_41)
              (LRCompactVBoxSound.join (box := joinbox2_rLLRLRRRRR) .s ((3 : ℚ) / 32)
                subsound2_42
                subsound2_43))))))
    (LRCompactVBoxSound.join (box := joinbox2_rLLRR) .k ((5 : ℚ) / 12)
      (LRCompactVBoxSound.join (box := joinbox2_rLLRRL) .chi ((29 : ℚ) / 32)
        (LRCompactVBoxSound.join (box := joinbox2_rLLRRLL) .s ((3 : ℚ) / 16)
          (LRCompactVBoxSound.join (box := joinbox2_rLLRRLLL) .k ((3 : ℚ) / 8)
            (LRCompactVBoxSound.join (box := joinbox2_rLLRRLLLL) .chi ((287 : ℚ) / 320)
              (LRCompactVBoxSound.join (box := joinbox2_rLLRRLLLLL) .s ((5 : ℚ) / 32)
                subsound2_44
                subsound2_45)
              (LRCompactVBoxSound.join (box := joinbox2_rLLRRLLLLR) .s ((5 : ℚ) / 32)
                subsound2_46
                subsound2_47))
            (LRCompactVBoxSound.join (box := joinbox2_rLLRRLLLR) .chi ((287 : ℚ) / 320)
              (LRCompactVBoxSound.join (box := joinbox2_rLLRRLLLRL) .s ((5 : ℚ) / 32)
                subsound2_48
                subsound2_49)
              (LRCompactVBoxSound.join (box := joinbox2_rLLRRLLLRR) .s ((5 : ℚ) / 32)
                subsound2_50
                subsound2_51)))
          (LRCompactVBoxSound.join (box := joinbox2_rLLRRLLR) .k ((3 : ℚ) / 8)
            (LRCompactVBoxSound.join (box := joinbox2_rLLRRLLRL) .chi ((287 : ℚ) / 320)
              (LRCompactVBoxSound.join (box := joinbox2_rLLRRLLRLL) .s ((7 : ℚ) / 32)
                subsound2_52
                subsound2_53)
              (LRCompactVBoxSound.join (box := joinbox2_rLLRRLLRLR) .s ((7 : ℚ) / 32)
                subsound2_54
                subsound2_55))
            (LRCompactVBoxSound.join (box := joinbox2_rLLRRLLRR) .chi ((287 : ℚ) / 320)
              (LRCompactVBoxSound.join (box := joinbox2_rLLRRLLRRL) .s ((7 : ℚ) / 32)
                subsound2_56
                subsound2_57)
              (LRCompactVBoxSound.join (box := joinbox2_rLLRRLLRRR) .s ((7 : ℚ) / 32)
                subsound2_58
                subsound2_59))))
        (LRCompactVBoxSound.join (box := joinbox2_rLLRRLR) .s ((3 : ℚ) / 16)
          (LRCompactVBoxSound.join (box := joinbox2_rLLRRLRL) .k ((3 : ℚ) / 8)
            (LRCompactVBoxSound.join (box := joinbox2_rLLRRLRLL) .chi ((293 : ℚ) / 320)
              subsound2_60
              subsound2_61)
            (LRCompactVBoxSound.join (box := joinbox2_rLLRRLRLR) .chi ((293 : ℚ) / 320)
              (LRCompactVBoxSound.join (box := joinbox2_rLLRRLRLRL) .s ((5 : ℚ) / 32)
                subsound2_62
                subsound2_63)
              (LRCompactVBoxSound.join (box := joinbox2_rLLRRLRLRR) .s ((5 : ℚ) / 32)
                subsound2_64
                subsound2_65)))
          (LRCompactVBoxSound.join (box := joinbox2_rLLRRLRR) .k ((3 : ℚ) / 8)
            (LRCompactVBoxSound.join (box := joinbox2_rLLRRLRRL) .chi ((293 : ℚ) / 320)
              (LRCompactVBoxSound.join (box := joinbox2_rLLRRLRRLL) .s ((7 : ℚ) / 32)
                subsound2_66
                subsound2_67)
              (LRCompactVBoxSound.join (box := joinbox2_rLLRRLRRLR) .s ((7 : ℚ) / 32)
                subsound2_68
                subsound2_69))
            (LRCompactVBoxSound.join (box := joinbox2_rLLRRLRRR) .chi ((293 : ℚ) / 320)
              (LRCompactVBoxSound.join (box := joinbox2_rLLRRLRRRL) .s ((7 : ℚ) / 32)
                subsound2_70
                subsound2_71)
              (LRCompactVBoxSound.join (box := joinbox2_rLLRRLRRRR) .s ((7 : ℚ) / 32)
                subsound2_72
                subsound2_73)))))
      (LRCompactVBoxSound.join (box := joinbox2_rLLRRR) .chi ((29 : ℚ) / 32)
        (LRCompactVBoxSound.join (box := joinbox2_rLLRRRL) .s ((3 : ℚ) / 16)
          (LRCompactVBoxSound.join (box := joinbox2_rLLRRRLL) .k ((11 : ℚ) / 24)
            (LRCompactVBoxSound.join (box := joinbox2_rLLRRRLLL) .chi ((287 : ℚ) / 320)
              (LRCompactVBoxSound.join (box := joinbox2_rLLRRRLLLL) .s ((5 : ℚ) / 32)
                subsound2_74
                subsound2_75)
              (LRCompactVBoxSound.join (box := joinbox2_rLLRRRLLLR) .s ((5 : ℚ) / 32)
                subsound2_76
                subsound2_77))
            (LRCompactVBoxSound.join (box := joinbox2_rLLRRRLLR) .chi ((287 : ℚ) / 320)
              (LRCompactVBoxSound.join (box := joinbox2_rLLRRRLLRL) .s ((5 : ℚ) / 32)
                subsound2_78
                subsound2_79)
              (LRCompactVBoxSound.join (box := joinbox2_rLLRRRLLRR) .s ((5 : ℚ) / 32)
                subsound2_80
                subsound2_81)))
          (LRCompactVBoxSound.join (box := joinbox2_rLLRRRLR) .k ((11 : ℚ) / 24)
            (LRCompactVBoxSound.join (box := joinbox2_rLLRRRLRL) .chi ((287 : ℚ) / 320)
              (LRCompactVBoxSound.join (box := joinbox2_rLLRRRLRLL) .s ((7 : ℚ) / 32)
                subsound2_82
                subsound2_83)
              (LRCompactVBoxSound.join (box := joinbox2_rLLRRRLRLR) .s ((7 : ℚ) / 32)
                subsound2_84
                subsound2_85))
            (LRCompactVBoxSound.join (box := joinbox2_rLLRRRLRR) .chi ((287 : ℚ) / 320)
              (LRCompactVBoxSound.join (box := joinbox2_rLLRRRLRRL) .s ((7 : ℚ) / 32)
                subsound2_86
                (LRCompactVBoxSound.join (box := joinbox2_rLLRRRLRRLR) .k ((23 : ℚ) / 48)
                  subsound2_87
                  subsound2_88))
              (LRCompactVBoxSound.join (box := joinbox2_rLLRRRLRRR) .s ((7 : ℚ) / 32)
                subsound2_89
                (LRCompactVBoxSound.join (box := joinbox2_rLLRRRLRRRR) .k ((23 : ℚ) / 48)
                  subsound2_90
                  subsound2_91)))))
        (LRCompactVBoxSound.join (box := joinbox2_rLLRRRR) .s ((3 : ℚ) / 16)
          (LRCompactVBoxSound.join (box := joinbox2_rLLRRRRL) .k ((11 : ℚ) / 24)
            (LRCompactVBoxSound.join (box := joinbox2_rLLRRRRLL) .chi ((293 : ℚ) / 320)
              (LRCompactVBoxSound.join (box := joinbox2_rLLRRRRLLL) .s ((5 : ℚ) / 32)
                subsound2_92
                subsound2_93)
              (LRCompactVBoxSound.join (box := joinbox2_rLLRRRRLLR) .s ((5 : ℚ) / 32)
                subsound2_94
                subsound2_95))
            (LRCompactVBoxSound.join (box := joinbox2_rLLRRRRLR) .chi ((293 : ℚ) / 320)
              (LRCompactVBoxSound.join (box := joinbox2_rLLRRRRLRL) .s ((5 : ℚ) / 32)
                subsound2_96
                subsound2_97)
              (LRCompactVBoxSound.join (box := joinbox2_rLLRRRRLRR) .s ((5 : ℚ) / 32)
                subsound2_98
                subsound2_99)))
          (LRCompactVBoxSound.join (box := joinbox2_rLLRRRRR) .k ((11 : ℚ) / 24)
            (LRCompactVBoxSound.join (box := joinbox2_rLLRRRRRL) .chi ((293 : ℚ) / 320)
              (LRCompactVBoxSound.join (box := joinbox2_rLLRRRRRLL) .s ((7 : ℚ) / 32)
                subsound2_100
                subsound2_101)
              (LRCompactVBoxSound.join (box := joinbox2_rLLRRRRRLR) .s ((7 : ℚ) / 32)
                subsound2_102
                subsound2_103))
            (LRCompactVBoxSound.join (box := joinbox2_rLLRRRRRR) .chi ((293 : ℚ) / 320)
              (LRCompactVBoxSound.join (box := joinbox2_rLLRRRRRRL) .s ((7 : ℚ) / 32)
                subsound2_104
                subsound2_105)
              (LRCompactVBoxSound.join (box := joinbox2_rLLRRRRRRR) .s ((7 : ℚ) / 32)
                subsound2_106
                subsound2_107)))))))

end CourtadeKumar.GeneratedLRCompactVLowR
