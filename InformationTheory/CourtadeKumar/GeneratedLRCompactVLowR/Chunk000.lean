import InformationTheory.CourtadeKumar.LRCompactVBasicReplay

/-! Frozen basic compact-V replay.
Plan SHA-256: ce3f7a498b2b9caf346dcf88ce7861f8cc091af8cd93f5624d7684e21322ecd5
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CourtadeKumar.GeneratedLRCompactVLowR

-- 55 accepted leaves below path rLLLL.
def box0 : CertificateBox where
  sLo := (0 : ℚ)
  sHi := ((1 : ℚ) / 8)
  kLo := ((1 : ℚ) / 3)
  kHi := ((1 : ℚ) / 2)
  chiLo := ((17 : ℚ) / 20)
  chiHi := ((71 : ℚ) / 80)


def subbox0_0 : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 16), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩

theorem checked0_0 :
    LRCompactVLeafParameters.check subbox0_0 .short = true := by decide +kernel

theorem subsound0_0 : LRCompactVBoxSound subbox0_0 :=
  LRCompactVLeafParameters.sound checked0_0


def subbox0_1 : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 16), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩

theorem checked0_1 :
    LRCompactVLeafParameters.check subbox0_1 .short = true := by decide +kernel

theorem subsound0_1 : LRCompactVBoxSound subbox0_1 :=
  LRCompactVLeafParameters.sound checked0_1


def subbox0_2 : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 32), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩

theorem checked0_2 :
    LRCompactVLeafParameters.check subbox0_2 .short = true := by decide +kernel

theorem subsound0_2 : LRCompactVBoxSound subbox0_2 :=
  LRCompactVLeafParameters.sound checked0_2


def subbox0_3 : CertificateBox :=
  ⟨((1 : ℚ) / 32), ((1 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩

theorem checked0_3 :
    LRCompactVLeafParameters.check subbox0_3 .short = true := by decide +kernel

theorem subsound0_3 : LRCompactVBoxSound subbox0_3 :=
  LRCompactVLeafParameters.sound checked0_3


def subbox0_4 : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩

theorem checked0_4 :
    LRCompactVLeafParameters.check subbox0_4 .long = true := by decide +kernel

theorem subsound0_4 : LRCompactVBoxSound subbox0_4 :=
  LRCompactVLeafParameters.sound checked0_4


def subbox0_5 : CertificateBox :=
  ⟨((1 : ℚ) / 16), ((3 : ℚ) / 32), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩

theorem checked0_5 :
    LRCompactVLeafParameters.check subbox0_5 .short = true := by decide +kernel

theorem subsound0_5 : LRCompactVBoxSound subbox0_5 :=
  LRCompactVLeafParameters.sound checked0_5


def subbox0_6 : CertificateBox :=
  ⟨((3 : ℚ) / 32), ((1 : ℚ) / 8), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩

theorem checked0_6 :
    LRCompactVLeafParameters.check subbox0_6 .short = true := by decide +kernel

theorem subsound0_6 : LRCompactVBoxSound subbox0_6 :=
  LRCompactVLeafParameters.sound checked0_6


def subbox0_7 : CertificateBox :=
  ⟨((1 : ℚ) / 16), ((3 : ℚ) / 32), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩

theorem checked0_7 :
    LRCompactVLeafParameters.check subbox0_7 .short = true := by decide +kernel

theorem subsound0_7 : LRCompactVBoxSound subbox0_7 :=
  LRCompactVLeafParameters.sound checked0_7


def subbox0_8 : CertificateBox :=
  ⟨((3 : ℚ) / 32), ((1 : ℚ) / 8), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩

theorem checked0_8 :
    LRCompactVLeafParameters.check subbox0_8 .short = true := by decide +kernel

theorem subsound0_8 : LRCompactVBoxSound subbox0_8 :=
  LRCompactVLeafParameters.sound checked0_8


def subbox0_9 : CertificateBox :=
  ⟨((1 : ℚ) / 16), ((3 : ℚ) / 32), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩

theorem checked0_9 :
    LRCompactVLeafParameters.check subbox0_9 .short = true := by decide +kernel

theorem subsound0_9 : LRCompactVBoxSound subbox0_9 :=
  LRCompactVLeafParameters.sound checked0_9


def subbox0_10 : CertificateBox :=
  ⟨((3 : ℚ) / 32), ((1 : ℚ) / 8), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩

theorem checked0_10 :
    LRCompactVLeafParameters.check subbox0_10 .short = true := by decide +kernel

theorem subsound0_10 : LRCompactVBoxSound subbox0_10 :=
  LRCompactVLeafParameters.sound checked0_10


def subbox0_11 : CertificateBox :=
  ⟨((1 : ℚ) / 16), ((3 : ℚ) / 32), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩

theorem checked0_11 :
    LRCompactVLeafParameters.check subbox0_11 .short = true := by decide +kernel

theorem subsound0_11 : LRCompactVBoxSound subbox0_11 :=
  LRCompactVLeafParameters.sound checked0_11


def subbox0_12 : CertificateBox :=
  ⟨((3 : ℚ) / 32), ((1 : ℚ) / 8), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩

theorem checked0_12 :
    LRCompactVLeafParameters.check subbox0_12 .short = true := by decide +kernel

theorem subsound0_12 : LRCompactVBoxSound subbox0_12 :=
  LRCompactVLeafParameters.sound checked0_12


def subbox0_13 : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 16), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩

theorem checked0_13 :
    LRCompactVLeafParameters.check subbox0_13 .short = true := by decide +kernel

theorem subsound0_13 : LRCompactVBoxSound subbox0_13 :=
  LRCompactVLeafParameters.sound checked0_13


def subbox0_14 : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 16), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩

theorem checked0_14 :
    LRCompactVLeafParameters.check subbox0_14 .short = true := by decide +kernel

theorem subsound0_14 : LRCompactVBoxSound subbox0_14 :=
  LRCompactVLeafParameters.sound checked0_14


def subbox0_15 : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩

theorem checked0_15 :
    LRCompactVLeafParameters.check subbox0_15 .long = true := by decide +kernel

theorem subsound0_15 : LRCompactVBoxSound subbox0_15 :=
  LRCompactVLeafParameters.sound checked0_15


def subbox0_16 : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩

theorem checked0_16 :
    LRCompactVLeafParameters.check subbox0_16 .short = true := by decide +kernel

theorem subsound0_16 : LRCompactVBoxSound subbox0_16 :=
  LRCompactVLeafParameters.sound checked0_16


def subbox0_17 : CertificateBox :=
  ⟨((1 : ℚ) / 16), ((1 : ℚ) / 8), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩

theorem checked0_17 :
    LRCompactVLeafParameters.check subbox0_17 .long = true := by decide +kernel

theorem subsound0_17 : LRCompactVBoxSound subbox0_17 :=
  LRCompactVLeafParameters.sound checked0_17


def subbox0_18 : CertificateBox :=
  ⟨((1 : ℚ) / 16), ((1 : ℚ) / 8), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩

theorem checked0_18 :
    LRCompactVLeafParameters.check subbox0_18 .long = true := by decide +kernel

theorem subsound0_18 : LRCompactVBoxSound subbox0_18 :=
  LRCompactVLeafParameters.sound checked0_18


def subbox0_19 : CertificateBox :=
  ⟨((1 : ℚ) / 16), ((3 : ℚ) / 32), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩

theorem checked0_19 :
    LRCompactVLeafParameters.check subbox0_19 .short = true := by decide +kernel

theorem subsound0_19 : LRCompactVBoxSound subbox0_19 :=
  LRCompactVLeafParameters.sound checked0_19


def subbox0_20 : CertificateBox :=
  ⟨((3 : ℚ) / 32), ((1 : ℚ) / 8), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩

theorem checked0_20 :
    LRCompactVLeafParameters.check subbox0_20 .short = true := by decide +kernel

theorem subsound0_20 : LRCompactVBoxSound subbox0_20 :=
  LRCompactVLeafParameters.sound checked0_20


def subbox0_21 : CertificateBox :=
  ⟨((1 : ℚ) / 16), ((3 : ℚ) / 32), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩

theorem checked0_21 :
    LRCompactVLeafParameters.check subbox0_21 .short = true := by decide +kernel

theorem subsound0_21 : LRCompactVBoxSound subbox0_21 :=
  LRCompactVLeafParameters.sound checked0_21


def subbox0_22 : CertificateBox :=
  ⟨((3 : ℚ) / 32), ((1 : ℚ) / 8), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩

theorem checked0_22 :
    LRCompactVLeafParameters.check subbox0_22 .short = true := by decide +kernel

theorem subsound0_22 : LRCompactVBoxSound subbox0_22 :=
  LRCompactVLeafParameters.sound checked0_22


def subbox0_23 : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 32), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩

theorem checked0_23 :
    LRCompactVLeafParameters.check subbox0_23 .short = true := by decide +kernel

theorem subsound0_23 : LRCompactVBoxSound subbox0_23 :=
  LRCompactVLeafParameters.sound checked0_23


def subbox0_24 : CertificateBox :=
  ⟨((1 : ℚ) / 32), ((1 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩

theorem checked0_24 :
    LRCompactVLeafParameters.check subbox0_24 .short = true := by decide +kernel

theorem subsound0_24 : LRCompactVBoxSound subbox0_24 :=
  LRCompactVLeafParameters.sound checked0_24


def subbox0_25 : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 32), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩

theorem checked0_25 :
    LRCompactVLeafParameters.check subbox0_25 .short = true := by decide +kernel

theorem subsound0_25 : LRCompactVBoxSound subbox0_25 :=
  LRCompactVLeafParameters.sound checked0_25


def subbox0_26 : CertificateBox :=
  ⟨((1 : ℚ) / 32), ((1 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩

theorem checked0_26 :
    LRCompactVLeafParameters.check subbox0_26 .short = true := by decide +kernel

theorem subsound0_26 : LRCompactVBoxSound subbox0_26 :=
  LRCompactVLeafParameters.sound checked0_26


def subbox0_27 : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 32), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩

theorem checked0_27 :
    LRCompactVLeafParameters.check subbox0_27 .short = true := by decide +kernel

theorem subsound0_27 : LRCompactVBoxSound subbox0_27 :=
  LRCompactVLeafParameters.sound checked0_27


def subbox0_28 : CertificateBox :=
  ⟨((1 : ℚ) / 32), ((1 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩

theorem checked0_28 :
    LRCompactVLeafParameters.check subbox0_28 .short = true := by decide +kernel

theorem subsound0_28 : LRCompactVBoxSound subbox0_28 :=
  LRCompactVLeafParameters.sound checked0_28


def subbox0_29 : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 32), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩

theorem checked0_29 :
    LRCompactVLeafParameters.check subbox0_29 .short = true := by decide +kernel

theorem subsound0_29 : LRCompactVBoxSound subbox0_29 :=
  LRCompactVLeafParameters.sound checked0_29


def subbox0_30 : CertificateBox :=
  ⟨((1 : ℚ) / 32), ((1 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩

theorem checked0_30 :
    LRCompactVLeafParameters.check subbox0_30 .short = true := by decide +kernel

theorem subsound0_30 : LRCompactVBoxSound subbox0_30 :=
  LRCompactVLeafParameters.sound checked0_30


def subbox0_31 : CertificateBox :=
  ⟨((1 : ℚ) / 16), ((3 : ℚ) / 32), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩

theorem checked0_31 :
    LRCompactVLeafParameters.check subbox0_31 .short = true := by decide +kernel

theorem subsound0_31 : LRCompactVBoxSound subbox0_31 :=
  LRCompactVLeafParameters.sound checked0_31


def subbox0_32 : CertificateBox :=
  ⟨((3 : ℚ) / 32), ((1 : ℚ) / 8), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩

theorem checked0_32 :
    LRCompactVLeafParameters.check subbox0_32 .short = true := by decide +kernel

theorem subsound0_32 : LRCompactVBoxSound subbox0_32 :=
  LRCompactVLeafParameters.sound checked0_32


def subbox0_33 : CertificateBox :=
  ⟨((1 : ℚ) / 16), ((3 : ℚ) / 32), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩

theorem checked0_33 :
    LRCompactVLeafParameters.check subbox0_33 .short = true := by decide +kernel

theorem subsound0_33 : LRCompactVBoxSound subbox0_33 :=
  LRCompactVLeafParameters.sound checked0_33


def subbox0_34 : CertificateBox :=
  ⟨((3 : ℚ) / 32), ((1 : ℚ) / 8), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩

theorem checked0_34 :
    LRCompactVLeafParameters.check subbox0_34 .short = true := by decide +kernel

theorem subsound0_34 : LRCompactVBoxSound subbox0_34 :=
  LRCompactVLeafParameters.sound checked0_34


def subbox0_35 : CertificateBox :=
  ⟨((1 : ℚ) / 16), ((3 : ℚ) / 32), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩

theorem checked0_35 :
    LRCompactVLeafParameters.check subbox0_35 .short = true := by decide +kernel

theorem subsound0_35 : LRCompactVBoxSound subbox0_35 :=
  LRCompactVLeafParameters.sound checked0_35


def subbox0_36 : CertificateBox :=
  ⟨((3 : ℚ) / 32), ((1 : ℚ) / 8), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩

theorem checked0_36 :
    LRCompactVLeafParameters.check subbox0_36 .short = true := by decide +kernel

theorem subsound0_36 : LRCompactVBoxSound subbox0_36 :=
  LRCompactVLeafParameters.sound checked0_36


def subbox0_37 : CertificateBox :=
  ⟨((1 : ℚ) / 16), ((3 : ℚ) / 32), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩

theorem checked0_37 :
    LRCompactVLeafParameters.check subbox0_37 .short = true := by decide +kernel

theorem subsound0_37 : LRCompactVBoxSound subbox0_37 :=
  LRCompactVLeafParameters.sound checked0_37


def subbox0_38 : CertificateBox :=
  ⟨((3 : ℚ) / 32), ((1 : ℚ) / 8), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩

theorem checked0_38 :
    LRCompactVLeafParameters.check subbox0_38 .short = true := by decide +kernel

theorem subsound0_38 : LRCompactVBoxSound subbox0_38 :=
  LRCompactVLeafParameters.sound checked0_38


def subbox0_39 : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 32), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩

theorem checked0_39 :
    LRCompactVLeafParameters.check subbox0_39 .short = true := by decide +kernel

theorem subsound0_39 : LRCompactVBoxSound subbox0_39 :=
  LRCompactVLeafParameters.sound checked0_39


def subbox0_40 : CertificateBox :=
  ⟨((1 : ℚ) / 32), ((1 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩

theorem checked0_40 :
    LRCompactVLeafParameters.check subbox0_40 .short = true := by decide +kernel

theorem subsound0_40 : LRCompactVBoxSound subbox0_40 :=
  LRCompactVLeafParameters.sound checked0_40


def subbox0_41 : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 32), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩

theorem checked0_41 :
    LRCompactVLeafParameters.check subbox0_41 .short = true := by decide +kernel

theorem subsound0_41 : LRCompactVBoxSound subbox0_41 :=
  LRCompactVLeafParameters.sound checked0_41


def subbox0_42 : CertificateBox :=
  ⟨((1 : ℚ) / 32), ((1 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩

theorem checked0_42 :
    LRCompactVLeafParameters.check subbox0_42 .short = true := by decide +kernel

theorem subsound0_42 : LRCompactVBoxSound subbox0_42 :=
  LRCompactVLeafParameters.sound checked0_42


def subbox0_43 : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 32), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩

theorem checked0_43 :
    LRCompactVLeafParameters.check subbox0_43 .short = true := by decide +kernel

theorem subsound0_43 : LRCompactVBoxSound subbox0_43 :=
  LRCompactVLeafParameters.sound checked0_43


def subbox0_44 : CertificateBox :=
  ⟨((1 : ℚ) / 32), ((1 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩

theorem checked0_44 :
    LRCompactVLeafParameters.check subbox0_44 .short = true := by decide +kernel

theorem subsound0_44 : LRCompactVBoxSound subbox0_44 :=
  LRCompactVLeafParameters.sound checked0_44


def subbox0_45 : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 32), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩

theorem checked0_45 :
    LRCompactVLeafParameters.check subbox0_45 .short = true := by decide +kernel

theorem subsound0_45 : LRCompactVBoxSound subbox0_45 :=
  LRCompactVLeafParameters.sound checked0_45


def subbox0_46 : CertificateBox :=
  ⟨((1 : ℚ) / 32), ((1 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩

theorem checked0_46 :
    LRCompactVLeafParameters.check subbox0_46 .short = true := by decide +kernel

theorem subsound0_46 : LRCompactVBoxSound subbox0_46 :=
  LRCompactVLeafParameters.sound checked0_46


def subbox0_47 : CertificateBox :=
  ⟨((1 : ℚ) / 16), ((3 : ℚ) / 32), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩

theorem checked0_47 :
    LRCompactVLeafParameters.check subbox0_47 .short = true := by decide +kernel

theorem subsound0_47 : LRCompactVBoxSound subbox0_47 :=
  LRCompactVLeafParameters.sound checked0_47


def subbox0_48 : CertificateBox :=
  ⟨((3 : ℚ) / 32), ((1 : ℚ) / 8), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩

theorem checked0_48 :
    LRCompactVLeafParameters.check subbox0_48 .short = true := by decide +kernel

theorem subsound0_48 : LRCompactVBoxSound subbox0_48 :=
  LRCompactVLeafParameters.sound checked0_48


def subbox0_49 : CertificateBox :=
  ⟨((1 : ℚ) / 16), ((3 : ℚ) / 32), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩

theorem checked0_49 :
    LRCompactVLeafParameters.check subbox0_49 .short = true := by decide +kernel

theorem subsound0_49 : LRCompactVBoxSound subbox0_49 :=
  LRCompactVLeafParameters.sound checked0_49


def subbox0_50 : CertificateBox :=
  ⟨((3 : ℚ) / 32), ((1 : ℚ) / 8), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩

theorem checked0_50 :
    LRCompactVLeafParameters.check subbox0_50 .short = true := by decide +kernel

theorem subsound0_50 : LRCompactVBoxSound subbox0_50 :=
  LRCompactVLeafParameters.sound checked0_50


def subbox0_51 : CertificateBox :=
  ⟨((1 : ℚ) / 16), ((3 : ℚ) / 32), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩

theorem checked0_51 :
    LRCompactVLeafParameters.check subbox0_51 .short = true := by decide +kernel

theorem subsound0_51 : LRCompactVBoxSound subbox0_51 :=
  LRCompactVLeafParameters.sound checked0_51


def subbox0_52 : CertificateBox :=
  ⟨((3 : ℚ) / 32), ((1 : ℚ) / 8), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩

theorem checked0_52 :
    LRCompactVLeafParameters.check subbox0_52 .short = true := by decide +kernel

theorem subsound0_52 : LRCompactVBoxSound subbox0_52 :=
  LRCompactVLeafParameters.sound checked0_52


def subbox0_53 : CertificateBox :=
  ⟨((1 : ℚ) / 16), ((3 : ℚ) / 32), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩

theorem checked0_53 :
    LRCompactVLeafParameters.check subbox0_53 .short = true := by decide +kernel

theorem subsound0_53 : LRCompactVBoxSound subbox0_53 :=
  LRCompactVLeafParameters.sound checked0_53


def subbox0_54 : CertificateBox :=
  ⟨((3 : ℚ) / 32), ((1 : ℚ) / 8), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩

theorem checked0_54 :
    LRCompactVLeafParameters.check subbox0_54 .short = true := by decide +kernel

theorem subsound0_54 : LRCompactVBoxSound subbox0_54 :=
  LRCompactVLeafParameters.sound checked0_54


def joinbox0_rLLLLL : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 8), ((1 : ℚ) / 3), ((5 : ℚ) / 12), ((17 : ℚ) / 20), ((71 : ℚ) / 80)⟩


def joinbox0_rLLLLLL : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 8), ((1 : ℚ) / 3), ((5 : ℚ) / 12), ((17 : ℚ) / 20), ((139 : ℚ) / 160)⟩


def joinbox0_rLLLLLLL : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 16), ((1 : ℚ) / 3), ((5 : ℚ) / 12), ((17 : ℚ) / 20), ((139 : ℚ) / 160)⟩


def joinbox0_rLLLLLLLL : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 16), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((17 : ℚ) / 20), ((139 : ℚ) / 160)⟩


def joinbox0_rLLLLLLLR : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((17 : ℚ) / 20), ((139 : ℚ) / 160)⟩


def joinbox0_rLLLLLLLRL : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩


def joinbox0_rLLLLLLR : CertificateBox :=
  ⟨((1 : ℚ) / 16), ((1 : ℚ) / 8), ((1 : ℚ) / 3), ((5 : ℚ) / 12), ((17 : ℚ) / 20), ((139 : ℚ) / 160)⟩


def joinbox0_rLLLLLLRL : CertificateBox :=
  ⟨((1 : ℚ) / 16), ((1 : ℚ) / 8), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((17 : ℚ) / 20), ((139 : ℚ) / 160)⟩


def joinbox0_rLLLLLLRLL : CertificateBox :=
  ⟨((1 : ℚ) / 16), ((1 : ℚ) / 8), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩


def joinbox0_rLLLLLLRLR : CertificateBox :=
  ⟨((1 : ℚ) / 16), ((1 : ℚ) / 8), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩


def joinbox0_rLLLLLLRR : CertificateBox :=
  ⟨((1 : ℚ) / 16), ((1 : ℚ) / 8), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((17 : ℚ) / 20), ((139 : ℚ) / 160)⟩


def joinbox0_rLLLLLLRRL : CertificateBox :=
  ⟨((1 : ℚ) / 16), ((1 : ℚ) / 8), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩


def joinbox0_rLLLLLLRRR : CertificateBox :=
  ⟨((1 : ℚ) / 16), ((1 : ℚ) / 8), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩


def joinbox0_rLLLLLR : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 8), ((1 : ℚ) / 3), ((5 : ℚ) / 12), ((139 : ℚ) / 160), ((71 : ℚ) / 80)⟩


def joinbox0_rLLLLLRL : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 16), ((1 : ℚ) / 3), ((5 : ℚ) / 12), ((139 : ℚ) / 160), ((71 : ℚ) / 80)⟩


def joinbox0_rLLLLLRLL : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 16), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((139 : ℚ) / 160), ((71 : ℚ) / 80)⟩


def joinbox0_rLLLLLRLR : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((139 : ℚ) / 160), ((71 : ℚ) / 80)⟩


def joinbox0_rLLLLLRR : CertificateBox :=
  ⟨((1 : ℚ) / 16), ((1 : ℚ) / 8), ((1 : ℚ) / 3), ((5 : ℚ) / 12), ((139 : ℚ) / 160), ((71 : ℚ) / 80)⟩


def joinbox0_rLLLLLRRL : CertificateBox :=
  ⟨((1 : ℚ) / 16), ((1 : ℚ) / 8), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((139 : ℚ) / 160), ((71 : ℚ) / 80)⟩


def joinbox0_rLLLLLRRR : CertificateBox :=
  ⟨((1 : ℚ) / 16), ((1 : ℚ) / 8), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((139 : ℚ) / 160), ((71 : ℚ) / 80)⟩


def joinbox0_rLLLLLRRRL : CertificateBox :=
  ⟨((1 : ℚ) / 16), ((1 : ℚ) / 8), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩


def joinbox0_rLLLLLRRRR : CertificateBox :=
  ⟨((1 : ℚ) / 16), ((1 : ℚ) / 8), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩


def joinbox0_rLLLLR : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 8), ((5 : ℚ) / 12), ((1 : ℚ) / 2), ((17 : ℚ) / 20), ((71 : ℚ) / 80)⟩


def joinbox0_rLLLLRL : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 8), ((5 : ℚ) / 12), ((1 : ℚ) / 2), ((17 : ℚ) / 20), ((139 : ℚ) / 160)⟩


def joinbox0_rLLLLRLL : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 16), ((5 : ℚ) / 12), ((1 : ℚ) / 2), ((17 : ℚ) / 20), ((139 : ℚ) / 160)⟩


def joinbox0_rLLLLRLLL : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((17 : ℚ) / 20), ((139 : ℚ) / 160)⟩


def joinbox0_rLLLLRLLLL : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩


def joinbox0_rLLLLRLLLR : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩


def joinbox0_rLLLLRLLR : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((17 : ℚ) / 20), ((139 : ℚ) / 160)⟩


def joinbox0_rLLLLRLLRL : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩


def joinbox0_rLLLLRLLRR : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩


def joinbox0_rLLLLRLR : CertificateBox :=
  ⟨((1 : ℚ) / 16), ((1 : ℚ) / 8), ((5 : ℚ) / 12), ((1 : ℚ) / 2), ((17 : ℚ) / 20), ((139 : ℚ) / 160)⟩


def joinbox0_rLLLLRLRL : CertificateBox :=
  ⟨((1 : ℚ) / 16), ((1 : ℚ) / 8), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((17 : ℚ) / 20), ((139 : ℚ) / 160)⟩


def joinbox0_rLLLLRLRLL : CertificateBox :=
  ⟨((1 : ℚ) / 16), ((1 : ℚ) / 8), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩


def joinbox0_rLLLLRLRLR : CertificateBox :=
  ⟨((1 : ℚ) / 16), ((1 : ℚ) / 8), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩


def joinbox0_rLLLLRLRR : CertificateBox :=
  ⟨((1 : ℚ) / 16), ((1 : ℚ) / 8), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((17 : ℚ) / 20), ((139 : ℚ) / 160)⟩


def joinbox0_rLLLLRLRRL : CertificateBox :=
  ⟨((1 : ℚ) / 16), ((1 : ℚ) / 8), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩


def joinbox0_rLLLLRLRRR : CertificateBox :=
  ⟨((1 : ℚ) / 16), ((1 : ℚ) / 8), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩


def joinbox0_rLLLLRR : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 8), ((5 : ℚ) / 12), ((1 : ℚ) / 2), ((139 : ℚ) / 160), ((71 : ℚ) / 80)⟩


def joinbox0_rLLLLRRL : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 16), ((5 : ℚ) / 12), ((1 : ℚ) / 2), ((139 : ℚ) / 160), ((71 : ℚ) / 80)⟩


def joinbox0_rLLLLRRLL : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((139 : ℚ) / 160), ((71 : ℚ) / 80)⟩


def joinbox0_rLLLLRRLLL : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩


def joinbox0_rLLLLRRLLR : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩


def joinbox0_rLLLLRRLR : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((139 : ℚ) / 160), ((71 : ℚ) / 80)⟩


def joinbox0_rLLLLRRLRL : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩


def joinbox0_rLLLLRRLRR : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩


def joinbox0_rLLLLRRR : CertificateBox :=
  ⟨((1 : ℚ) / 16), ((1 : ℚ) / 8), ((5 : ℚ) / 12), ((1 : ℚ) / 2), ((139 : ℚ) / 160), ((71 : ℚ) / 80)⟩


def joinbox0_rLLLLRRRL : CertificateBox :=
  ⟨((1 : ℚ) / 16), ((1 : ℚ) / 8), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((139 : ℚ) / 160), ((71 : ℚ) / 80)⟩


def joinbox0_rLLLLRRRLL : CertificateBox :=
  ⟨((1 : ℚ) / 16), ((1 : ℚ) / 8), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩


def joinbox0_rLLLLRRRLR : CertificateBox :=
  ⟨((1 : ℚ) / 16), ((1 : ℚ) / 8), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩


def joinbox0_rLLLLRRRR : CertificateBox :=
  ⟨((1 : ℚ) / 16), ((1 : ℚ) / 8), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((139 : ℚ) / 160), ((71 : ℚ) / 80)⟩


def joinbox0_rLLLLRRRRL : CertificateBox :=
  ⟨((1 : ℚ) / 16), ((1 : ℚ) / 8), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩


def joinbox0_rLLLLRRRRR : CertificateBox :=
  ⟨((1 : ℚ) / 16), ((1 : ℚ) / 8), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩


theorem sound0 : LRCompactVBoxSound box0 :=
  (LRCompactVBoxSound.join (box := box0) .k ((5 : ℚ) / 12)
    (LRCompactVBoxSound.join (box := joinbox0_rLLLLL) .chi ((139 : ℚ) / 160)
      (LRCompactVBoxSound.join (box := joinbox0_rLLLLLL) .s ((1 : ℚ) / 16)
        (LRCompactVBoxSound.join (box := joinbox0_rLLLLLLL) .k ((3 : ℚ) / 8)
          (LRCompactVBoxSound.join (box := joinbox0_rLLLLLLLL) .chi ((55 : ℚ) / 64)
            subsound0_0
            subsound0_1)
          (LRCompactVBoxSound.join (box := joinbox0_rLLLLLLLR) .chi ((55 : ℚ) / 64)
            (LRCompactVBoxSound.join (box := joinbox0_rLLLLLLLRL) .s ((1 : ℚ) / 32)
              subsound0_2
              subsound0_3)
            subsound0_4))
        (LRCompactVBoxSound.join (box := joinbox0_rLLLLLLR) .k ((3 : ℚ) / 8)
          (LRCompactVBoxSound.join (box := joinbox0_rLLLLLLRL) .chi ((55 : ℚ) / 64)
            (LRCompactVBoxSound.join (box := joinbox0_rLLLLLLRLL) .s ((3 : ℚ) / 32)
              subsound0_5
              subsound0_6)
            (LRCompactVBoxSound.join (box := joinbox0_rLLLLLLRLR) .s ((3 : ℚ) / 32)
              subsound0_7
              subsound0_8))
          (LRCompactVBoxSound.join (box := joinbox0_rLLLLLLRR) .chi ((55 : ℚ) / 64)
            (LRCompactVBoxSound.join (box := joinbox0_rLLLLLLRRL) .s ((3 : ℚ) / 32)
              subsound0_9
              subsound0_10)
            (LRCompactVBoxSound.join (box := joinbox0_rLLLLLLRRR) .s ((3 : ℚ) / 32)
              subsound0_11
              subsound0_12))))
      (LRCompactVBoxSound.join (box := joinbox0_rLLLLLR) .s ((1 : ℚ) / 16)
        (LRCompactVBoxSound.join (box := joinbox0_rLLLLLRL) .k ((3 : ℚ) / 8)
          (LRCompactVBoxSound.join (box := joinbox0_rLLLLLRLL) .chi ((281 : ℚ) / 320)
            subsound0_13
            subsound0_14)
          (LRCompactVBoxSound.join (box := joinbox0_rLLLLLRLR) .chi ((281 : ℚ) / 320)
            subsound0_15
            subsound0_16))
        (LRCompactVBoxSound.join (box := joinbox0_rLLLLLRR) .k ((3 : ℚ) / 8)
          (LRCompactVBoxSound.join (box := joinbox0_rLLLLLRRL) .chi ((281 : ℚ) / 320)
            subsound0_17
            subsound0_18)
          (LRCompactVBoxSound.join (box := joinbox0_rLLLLLRRR) .chi ((281 : ℚ) / 320)
            (LRCompactVBoxSound.join (box := joinbox0_rLLLLLRRRL) .s ((3 : ℚ) / 32)
              subsound0_19
              subsound0_20)
            (LRCompactVBoxSound.join (box := joinbox0_rLLLLLRRRR) .s ((3 : ℚ) / 32)
              subsound0_21
              subsound0_22)))))
    (LRCompactVBoxSound.join (box := joinbox0_rLLLLR) .chi ((139 : ℚ) / 160)
      (LRCompactVBoxSound.join (box := joinbox0_rLLLLRL) .s ((1 : ℚ) / 16)
        (LRCompactVBoxSound.join (box := joinbox0_rLLLLRLL) .k ((11 : ℚ) / 24)
          (LRCompactVBoxSound.join (box := joinbox0_rLLLLRLLL) .chi ((55 : ℚ) / 64)
            (LRCompactVBoxSound.join (box := joinbox0_rLLLLRLLLL) .s ((1 : ℚ) / 32)
              subsound0_23
              subsound0_24)
            (LRCompactVBoxSound.join (box := joinbox0_rLLLLRLLLR) .s ((1 : ℚ) / 32)
              subsound0_25
              subsound0_26))
          (LRCompactVBoxSound.join (box := joinbox0_rLLLLRLLR) .chi ((55 : ℚ) / 64)
            (LRCompactVBoxSound.join (box := joinbox0_rLLLLRLLRL) .s ((1 : ℚ) / 32)
              subsound0_27
              subsound0_28)
            (LRCompactVBoxSound.join (box := joinbox0_rLLLLRLLRR) .s ((1 : ℚ) / 32)
              subsound0_29
              subsound0_30)))
        (LRCompactVBoxSound.join (box := joinbox0_rLLLLRLR) .k ((11 : ℚ) / 24)
          (LRCompactVBoxSound.join (box := joinbox0_rLLLLRLRL) .chi ((55 : ℚ) / 64)
            (LRCompactVBoxSound.join (box := joinbox0_rLLLLRLRLL) .s ((3 : ℚ) / 32)
              subsound0_31
              subsound0_32)
            (LRCompactVBoxSound.join (box := joinbox0_rLLLLRLRLR) .s ((3 : ℚ) / 32)
              subsound0_33
              subsound0_34))
          (LRCompactVBoxSound.join (box := joinbox0_rLLLLRLRR) .chi ((55 : ℚ) / 64)
            (LRCompactVBoxSound.join (box := joinbox0_rLLLLRLRRL) .s ((3 : ℚ) / 32)
              subsound0_35
              subsound0_36)
            (LRCompactVBoxSound.join (box := joinbox0_rLLLLRLRRR) .s ((3 : ℚ) / 32)
              subsound0_37
              subsound0_38))))
      (LRCompactVBoxSound.join (box := joinbox0_rLLLLRR) .s ((1 : ℚ) / 16)
        (LRCompactVBoxSound.join (box := joinbox0_rLLLLRRL) .k ((11 : ℚ) / 24)
          (LRCompactVBoxSound.join (box := joinbox0_rLLLLRRLL) .chi ((281 : ℚ) / 320)
            (LRCompactVBoxSound.join (box := joinbox0_rLLLLRRLLL) .s ((1 : ℚ) / 32)
              subsound0_39
              subsound0_40)
            (LRCompactVBoxSound.join (box := joinbox0_rLLLLRRLLR) .s ((1 : ℚ) / 32)
              subsound0_41
              subsound0_42))
          (LRCompactVBoxSound.join (box := joinbox0_rLLLLRRLR) .chi ((281 : ℚ) / 320)
            (LRCompactVBoxSound.join (box := joinbox0_rLLLLRRLRL) .s ((1 : ℚ) / 32)
              subsound0_43
              subsound0_44)
            (LRCompactVBoxSound.join (box := joinbox0_rLLLLRRLRR) .s ((1 : ℚ) / 32)
              subsound0_45
              subsound0_46)))
        (LRCompactVBoxSound.join (box := joinbox0_rLLLLRRR) .k ((11 : ℚ) / 24)
          (LRCompactVBoxSound.join (box := joinbox0_rLLLLRRRL) .chi ((281 : ℚ) / 320)
            (LRCompactVBoxSound.join (box := joinbox0_rLLLLRRRLL) .s ((3 : ℚ) / 32)
              subsound0_47
              subsound0_48)
            (LRCompactVBoxSound.join (box := joinbox0_rLLLLRRRLR) .s ((3 : ℚ) / 32)
              subsound0_49
              subsound0_50))
          (LRCompactVBoxSound.join (box := joinbox0_rLLLLRRRR) .chi ((281 : ℚ) / 320)
            (LRCompactVBoxSound.join (box := joinbox0_rLLLLRRRRL) .s ((3 : ℚ) / 32)
              subsound0_51
              subsound0_52)
            (LRCompactVBoxSound.join (box := joinbox0_rLLLLRRRRR) .s ((3 : ℚ) / 32)
              subsound0_53
              subsound0_54))))))

end CourtadeKumar.GeneratedLRCompactVLowR
