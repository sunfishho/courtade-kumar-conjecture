import InformationTheory.CourtadeKumar.LRCompactVBasicReplay

/-! Frozen basic compact-V replay.
Plan SHA-256: ce3f7a498b2b9caf346dcf88ce7861f8cc091af8cd93f5624d7684e21322ecd5
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CourtadeKumar.GeneratedLRCompactVLowR

-- 78 accepted leaves below path rLLLR.
def box1 : CertificateBox where
  sLo := ((1 : ℚ) / 8)
  sHi := ((1 : ℚ) / 4)
  kLo := ((1 : ℚ) / 3)
  kHi := ((1 : ℚ) / 2)
  chiLo := ((17 : ℚ) / 20)
  chiHi := ((71 : ℚ) / 80)


def subbox1_0 : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((5 : ℚ) / 32), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩

theorem checked1_0 :
    LRCompactVLeafParameters.check subbox1_0 .short = true := by decide +kernel

theorem subsound1_0 : LRCompactVBoxSound subbox1_0 :=
  LRCompactVLeafParameters.sound checked1_0


def subbox1_1 : CertificateBox :=
  ⟨((5 : ℚ) / 32), ((3 : ℚ) / 16), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩

theorem checked1_1 :
    LRCompactVLeafParameters.check subbox1_1 .short = true := by decide +kernel

theorem subsound1_1 : LRCompactVBoxSound subbox1_1 :=
  LRCompactVLeafParameters.sound checked1_1


def subbox1_2 : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((5 : ℚ) / 32), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩

theorem checked1_2 :
    LRCompactVLeafParameters.check subbox1_2 .short = true := by decide +kernel

theorem subsound1_2 : LRCompactVBoxSound subbox1_2 :=
  LRCompactVLeafParameters.sound checked1_2


def subbox1_3 : CertificateBox :=
  ⟨((5 : ℚ) / 32), ((3 : ℚ) / 16), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩

theorem checked1_3 :
    LRCompactVLeafParameters.check subbox1_3 .short = true := by decide +kernel

theorem subsound1_3 : LRCompactVBoxSound subbox1_3 :=
  LRCompactVLeafParameters.sound checked1_3


def subbox1_4 : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((5 : ℚ) / 32), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩

theorem checked1_4 :
    LRCompactVLeafParameters.check subbox1_4 .short = true := by decide +kernel

theorem subsound1_4 : LRCompactVBoxSound subbox1_4 :=
  LRCompactVLeafParameters.sound checked1_4


def subbox1_5 : CertificateBox :=
  ⟨((5 : ℚ) / 32), ((3 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩

theorem checked1_5 :
    LRCompactVLeafParameters.check subbox1_5 .short = true := by decide +kernel

theorem subsound1_5 : LRCompactVBoxSound subbox1_5 :=
  LRCompactVLeafParameters.sound checked1_5


def subbox1_6 : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((5 : ℚ) / 32), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩

theorem checked1_6 :
    LRCompactVLeafParameters.check subbox1_6 .short = true := by decide +kernel

theorem subsound1_6 : LRCompactVBoxSound subbox1_6 :=
  LRCompactVLeafParameters.sound checked1_6


def subbox1_7 : CertificateBox :=
  ⟨((5 : ℚ) / 32), ((3 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩

theorem checked1_7 :
    LRCompactVLeafParameters.check subbox1_7 .short = true := by decide +kernel

theorem subsound1_7 : LRCompactVBoxSound subbox1_7 :=
  LRCompactVLeafParameters.sound checked1_7


def subbox1_8 : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((7 : ℚ) / 32), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩

theorem checked1_8 :
    LRCompactVLeafParameters.check subbox1_8 .short = true := by decide +kernel

theorem subsound1_8 : LRCompactVBoxSound subbox1_8 :=
  LRCompactVLeafParameters.sound checked1_8


def subbox1_9 : CertificateBox :=
  ⟨((7 : ℚ) / 32), ((1 : ℚ) / 4), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩

theorem checked1_9 :
    LRCompactVLeafParameters.check subbox1_9 .accurateLog = true := by decide +kernel

theorem subsound1_9 : LRCompactVBoxSound subbox1_9 :=
  LRCompactVLeafParameters.sound checked1_9


def subbox1_10 : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((7 : ℚ) / 32), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩

theorem checked1_10 :
    LRCompactVLeafParameters.check subbox1_10 .short = true := by decide +kernel

theorem subsound1_10 : LRCompactVBoxSound subbox1_10 :=
  LRCompactVLeafParameters.sound checked1_10


def subbox1_11 : CertificateBox :=
  ⟨((7 : ℚ) / 32), ((1 : ℚ) / 4), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩

theorem checked1_11 :
    LRCompactVLeafParameters.check subbox1_11 .short = true := by decide +kernel

theorem subsound1_11 : LRCompactVBoxSound subbox1_11 :=
  LRCompactVLeafParameters.sound checked1_11


def subbox1_12 : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((7 : ℚ) / 32), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩

theorem checked1_12 :
    LRCompactVLeafParameters.check subbox1_12 .short = true := by decide +kernel

theorem subsound1_12 : LRCompactVBoxSound subbox1_12 :=
  LRCompactVLeafParameters.sound checked1_12


def subbox1_13 : CertificateBox :=
  ⟨((7 : ℚ) / 32), ((1 : ℚ) / 4), ((3 : ℚ) / 8), ((19 : ℚ) / 48), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩

theorem checked1_13 :
    LRCompactVLeafParameters.check subbox1_13 .short = true := by decide +kernel

theorem subsound1_13 : LRCompactVBoxSound subbox1_13 :=
  LRCompactVLeafParameters.sound checked1_13


def subbox1_14 : CertificateBox :=
  ⟨((7 : ℚ) / 32), ((1 : ℚ) / 4), ((19 : ℚ) / 48), ((5 : ℚ) / 12), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩

theorem checked1_14 :
    LRCompactVLeafParameters.check subbox1_14 .short = true := by decide +kernel

theorem subsound1_14 : LRCompactVBoxSound subbox1_14 :=
  LRCompactVLeafParameters.sound checked1_14


def subbox1_15 : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((7 : ℚ) / 32), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩

theorem checked1_15 :
    LRCompactVLeafParameters.check subbox1_15 .short = true := by decide +kernel

theorem subsound1_15 : LRCompactVBoxSound subbox1_15 :=
  LRCompactVLeafParameters.sound checked1_15


def subbox1_16 : CertificateBox :=
  ⟨((7 : ℚ) / 32), ((1 : ℚ) / 4), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩

theorem checked1_16 :
    LRCompactVLeafParameters.check subbox1_16 .long = true := by decide +kernel

theorem subsound1_16 : LRCompactVBoxSound subbox1_16 :=
  LRCompactVLeafParameters.sound checked1_16


def subbox1_17 : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((5 : ℚ) / 32), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩

theorem checked1_17 :
    LRCompactVLeafParameters.check subbox1_17 .short = true := by decide +kernel

theorem subsound1_17 : LRCompactVBoxSound subbox1_17 :=
  LRCompactVLeafParameters.sound checked1_17


def subbox1_18 : CertificateBox :=
  ⟨((5 : ℚ) / 32), ((3 : ℚ) / 16), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩

theorem checked1_18 :
    LRCompactVLeafParameters.check subbox1_18 .short = true := by decide +kernel

theorem subsound1_18 : LRCompactVBoxSound subbox1_18 :=
  LRCompactVLeafParameters.sound checked1_18


def subbox1_19 : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((5 : ℚ) / 32), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩

theorem checked1_19 :
    LRCompactVLeafParameters.check subbox1_19 .short = true := by decide +kernel

theorem subsound1_19 : LRCompactVBoxSound subbox1_19 :=
  LRCompactVLeafParameters.sound checked1_19


def subbox1_20 : CertificateBox :=
  ⟨((5 : ℚ) / 32), ((3 : ℚ) / 16), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩

theorem checked1_20 :
    LRCompactVLeafParameters.check subbox1_20 .short = true := by decide +kernel

theorem subsound1_20 : LRCompactVBoxSound subbox1_20 :=
  LRCompactVLeafParameters.sound checked1_20


def subbox1_21 : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((5 : ℚ) / 32), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩

theorem checked1_21 :
    LRCompactVLeafParameters.check subbox1_21 .short = true := by decide +kernel

theorem subsound1_21 : LRCompactVBoxSound subbox1_21 :=
  LRCompactVLeafParameters.sound checked1_21


def subbox1_22 : CertificateBox :=
  ⟨((5 : ℚ) / 32), ((3 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩

theorem checked1_22 :
    LRCompactVLeafParameters.check subbox1_22 .short = true := by decide +kernel

theorem subsound1_22 : LRCompactVBoxSound subbox1_22 :=
  LRCompactVLeafParameters.sound checked1_22


def subbox1_23 : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((5 : ℚ) / 32), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩

theorem checked1_23 :
    LRCompactVLeafParameters.check subbox1_23 .short = true := by decide +kernel

theorem subsound1_23 : LRCompactVBoxSound subbox1_23 :=
  LRCompactVLeafParameters.sound checked1_23


def subbox1_24 : CertificateBox :=
  ⟨((5 : ℚ) / 32), ((3 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩

theorem checked1_24 :
    LRCompactVLeafParameters.check subbox1_24 .short = true := by decide +kernel

theorem subsound1_24 : LRCompactVBoxSound subbox1_24 :=
  LRCompactVLeafParameters.sound checked1_24


def subbox1_25 : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((7 : ℚ) / 32), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩

theorem checked1_25 :
    LRCompactVLeafParameters.check subbox1_25 .short = true := by decide +kernel

theorem subsound1_25 : LRCompactVBoxSound subbox1_25 :=
  LRCompactVLeafParameters.sound checked1_25


def subbox1_26 : CertificateBox :=
  ⟨((7 : ℚ) / 32), ((1 : ℚ) / 4), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩

theorem checked1_26 :
    LRCompactVLeafParameters.check subbox1_26 .short = true := by decide +kernel

theorem subsound1_26 : LRCompactVBoxSound subbox1_26 :=
  LRCompactVLeafParameters.sound checked1_26


def subbox1_27 : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((7 : ℚ) / 32), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩

theorem checked1_27 :
    LRCompactVLeafParameters.check subbox1_27 .short = true := by decide +kernel

theorem subsound1_27 : LRCompactVBoxSound subbox1_27 :=
  LRCompactVLeafParameters.sound checked1_27


def subbox1_28 : CertificateBox :=
  ⟨((7 : ℚ) / 32), ((1 : ℚ) / 4), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩

theorem checked1_28 :
    LRCompactVLeafParameters.check subbox1_28 .short = true := by decide +kernel

theorem subsound1_28 : LRCompactVBoxSound subbox1_28 :=
  LRCompactVLeafParameters.sound checked1_28


def subbox1_29 : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((7 : ℚ) / 32), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩

theorem checked1_29 :
    LRCompactVLeafParameters.check subbox1_29 .short = true := by decide +kernel

theorem subsound1_29 : LRCompactVBoxSound subbox1_29 :=
  LRCompactVLeafParameters.sound checked1_29


def subbox1_30 : CertificateBox :=
  ⟨((7 : ℚ) / 32), ((1 : ℚ) / 4), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩

theorem checked1_30 :
    LRCompactVLeafParameters.check subbox1_30 .long = true := by decide +kernel

theorem subsound1_30 : LRCompactVBoxSound subbox1_30 :=
  LRCompactVLeafParameters.sound checked1_30


def subbox1_31 : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((7 : ℚ) / 32), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩

theorem checked1_31 :
    LRCompactVLeafParameters.check subbox1_31 .short = true := by decide +kernel

theorem subsound1_31 : LRCompactVBoxSound subbox1_31 :=
  LRCompactVLeafParameters.sound checked1_31


def subbox1_32 : CertificateBox :=
  ⟨((7 : ℚ) / 32), ((1 : ℚ) / 4), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩

theorem checked1_32 :
    LRCompactVLeafParameters.check subbox1_32 .short = true := by decide +kernel

theorem subsound1_32 : LRCompactVBoxSound subbox1_32 :=
  LRCompactVLeafParameters.sound checked1_32


def subbox1_33 : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((5 : ℚ) / 32), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩

theorem checked1_33 :
    LRCompactVLeafParameters.check subbox1_33 .short = true := by decide +kernel

theorem subsound1_33 : LRCompactVBoxSound subbox1_33 :=
  LRCompactVLeafParameters.sound checked1_33


def subbox1_34 : CertificateBox :=
  ⟨((5 : ℚ) / 32), ((3 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩

theorem checked1_34 :
    LRCompactVLeafParameters.check subbox1_34 .short = true := by decide +kernel

theorem subsound1_34 : LRCompactVBoxSound subbox1_34 :=
  LRCompactVLeafParameters.sound checked1_34


def subbox1_35 : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((5 : ℚ) / 32), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩

theorem checked1_35 :
    LRCompactVLeafParameters.check subbox1_35 .short = true := by decide +kernel

theorem subsound1_35 : LRCompactVBoxSound subbox1_35 :=
  LRCompactVLeafParameters.sound checked1_35


def subbox1_36 : CertificateBox :=
  ⟨((5 : ℚ) / 32), ((3 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩

theorem checked1_36 :
    LRCompactVLeafParameters.check subbox1_36 .short = true := by decide +kernel

theorem subsound1_36 : LRCompactVBoxSound subbox1_36 :=
  LRCompactVLeafParameters.sound checked1_36


def subbox1_37 : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((5 : ℚ) / 32), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩

theorem checked1_37 :
    LRCompactVLeafParameters.check subbox1_37 .short = true := by decide +kernel

theorem subsound1_37 : LRCompactVBoxSound subbox1_37 :=
  LRCompactVLeafParameters.sound checked1_37


def subbox1_38 : CertificateBox :=
  ⟨((5 : ℚ) / 32), ((3 : ℚ) / 16), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩

theorem checked1_38 :
    LRCompactVLeafParameters.check subbox1_38 .short = true := by decide +kernel

theorem subsound1_38 : LRCompactVBoxSound subbox1_38 :=
  LRCompactVLeafParameters.sound checked1_38


def subbox1_39 : CertificateBox :=
  ⟨((5 : ℚ) / 32), ((3 : ℚ) / 16), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩

theorem checked1_39 :
    LRCompactVLeafParameters.check subbox1_39 .short = true := by decide +kernel

theorem subsound1_39 : LRCompactVBoxSound subbox1_39 :=
  LRCompactVLeafParameters.sound checked1_39


def subbox1_40 : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((5 : ℚ) / 32), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩

theorem checked1_40 :
    LRCompactVLeafParameters.check subbox1_40 .short = true := by decide +kernel

theorem subsound1_40 : LRCompactVBoxSound subbox1_40 :=
  LRCompactVLeafParameters.sound checked1_40


def subbox1_41 : CertificateBox :=
  ⟨((5 : ℚ) / 32), ((3 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩

theorem checked1_41 :
    LRCompactVLeafParameters.check subbox1_41 .long = true := by decide +kernel

theorem subsound1_41 : LRCompactVBoxSound subbox1_41 :=
  LRCompactVLeafParameters.sound checked1_41


def subbox1_42 : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((7 : ℚ) / 32), ((5 : ℚ) / 12), ((7 : ℚ) / 16), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩

theorem checked1_42 :
    LRCompactVLeafParameters.check subbox1_42 .short = true := by decide +kernel

theorem subsound1_42 : LRCompactVBoxSound subbox1_42 :=
  LRCompactVLeafParameters.sound checked1_42


def subbox1_43 : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((7 : ℚ) / 32), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩

theorem checked1_43 :
    LRCompactVLeafParameters.check subbox1_43 .short = true := by decide +kernel

theorem subsound1_43 : LRCompactVBoxSound subbox1_43 :=
  LRCompactVLeafParameters.sound checked1_43


def subbox1_44 : CertificateBox :=
  ⟨((7 : ℚ) / 32), ((1 : ℚ) / 4), ((5 : ℚ) / 12), ((7 : ℚ) / 16), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩

theorem checked1_44 :
    LRCompactVLeafParameters.check subbox1_44 .short = true := by decide +kernel

theorem subsound1_44 : LRCompactVBoxSound subbox1_44 :=
  LRCompactVLeafParameters.sound checked1_44


def subbox1_45 : CertificateBox :=
  ⟨((7 : ℚ) / 32), ((1 : ℚ) / 4), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩

theorem checked1_45 :
    LRCompactVLeafParameters.check subbox1_45 .short = true := by decide +kernel

theorem subsound1_45 : LRCompactVBoxSound subbox1_45 :=
  LRCompactVLeafParameters.sound checked1_45


def subbox1_46 : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((7 : ℚ) / 32), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩

theorem checked1_46 :
    LRCompactVLeafParameters.check subbox1_46 .long = true := by decide +kernel

theorem subsound1_46 : LRCompactVBoxSound subbox1_46 :=
  LRCompactVLeafParameters.sound checked1_46


def subbox1_47 : CertificateBox :=
  ⟨((7 : ℚ) / 32), ((1 : ℚ) / 4), ((5 : ℚ) / 12), ((7 : ℚ) / 16), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩

theorem checked1_47 :
    LRCompactVLeafParameters.check subbox1_47 .short = true := by decide +kernel

theorem subsound1_47 : LRCompactVBoxSound subbox1_47 :=
  LRCompactVLeafParameters.sound checked1_47


def subbox1_48 : CertificateBox :=
  ⟨((7 : ℚ) / 32), ((1 : ℚ) / 4), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩

theorem checked1_48 :
    LRCompactVLeafParameters.check subbox1_48 .short = true := by decide +kernel

theorem subsound1_48 : LRCompactVBoxSound subbox1_48 :=
  LRCompactVLeafParameters.sound checked1_48


def subbox1_49 : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((7 : ℚ) / 32), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩

theorem checked1_49 :
    LRCompactVLeafParameters.check subbox1_49 .short = true := by decide +kernel

theorem subsound1_49 : LRCompactVBoxSound subbox1_49 :=
  LRCompactVLeafParameters.sound checked1_49


def subbox1_50 : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((7 : ℚ) / 32), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩

theorem checked1_50 :
    LRCompactVLeafParameters.check subbox1_50 .short = true := by decide +kernel

theorem subsound1_50 : LRCompactVBoxSound subbox1_50 :=
  LRCompactVLeafParameters.sound checked1_50


def subbox1_51 : CertificateBox :=
  ⟨((7 : ℚ) / 32), ((1 : ℚ) / 4), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩

theorem checked1_51 :
    LRCompactVLeafParameters.check subbox1_51 .short = true := by decide +kernel

theorem subsound1_51 : LRCompactVBoxSound subbox1_51 :=
  LRCompactVLeafParameters.sound checked1_51


def subbox1_52 : CertificateBox :=
  ⟨((7 : ℚ) / 32), ((1 : ℚ) / 4), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩

theorem checked1_52 :
    LRCompactVLeafParameters.check subbox1_52 .short = true := by decide +kernel

theorem subsound1_52 : LRCompactVBoxSound subbox1_52 :=
  LRCompactVLeafParameters.sound checked1_52


def subbox1_53 : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((7 : ℚ) / 32), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩

theorem checked1_53 :
    LRCompactVLeafParameters.check subbox1_53 .short = true := by decide +kernel

theorem subsound1_53 : LRCompactVBoxSound subbox1_53 :=
  LRCompactVLeafParameters.sound checked1_53


def subbox1_54 : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((7 : ℚ) / 32), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩

theorem checked1_54 :
    LRCompactVLeafParameters.check subbox1_54 .short = true := by decide +kernel

theorem subsound1_54 : LRCompactVBoxSound subbox1_54 :=
  LRCompactVLeafParameters.sound checked1_54


def subbox1_55 : CertificateBox :=
  ⟨((7 : ℚ) / 32), ((1 : ℚ) / 4), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩

theorem checked1_55 :
    LRCompactVLeafParameters.check subbox1_55 .short = true := by decide +kernel

theorem subsound1_55 : LRCompactVBoxSound subbox1_55 :=
  LRCompactVLeafParameters.sound checked1_55


def subbox1_56 : CertificateBox :=
  ⟨((7 : ℚ) / 32), ((1 : ℚ) / 4), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩

theorem checked1_56 :
    LRCompactVLeafParameters.check subbox1_56 .short = true := by decide +kernel

theorem subsound1_56 : LRCompactVBoxSound subbox1_56 :=
  LRCompactVLeafParameters.sound checked1_56


def subbox1_57 : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((5 : ℚ) / 32), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩

theorem checked1_57 :
    LRCompactVLeafParameters.check subbox1_57 .short = true := by decide +kernel

theorem subsound1_57 : LRCompactVBoxSound subbox1_57 :=
  LRCompactVLeafParameters.sound checked1_57


def subbox1_58 : CertificateBox :=
  ⟨((5 : ℚ) / 32), ((3 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩

theorem checked1_58 :
    LRCompactVLeafParameters.check subbox1_58 .short = true := by decide +kernel

theorem subsound1_58 : LRCompactVBoxSound subbox1_58 :=
  LRCompactVLeafParameters.sound checked1_58


def subbox1_59 : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((5 : ℚ) / 32), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩

theorem checked1_59 :
    LRCompactVLeafParameters.check subbox1_59 .short = true := by decide +kernel

theorem subsound1_59 : LRCompactVBoxSound subbox1_59 :=
  LRCompactVLeafParameters.sound checked1_59


def subbox1_60 : CertificateBox :=
  ⟨((5 : ℚ) / 32), ((3 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩

theorem checked1_60 :
    LRCompactVLeafParameters.check subbox1_60 .short = true := by decide +kernel

theorem subsound1_60 : LRCompactVBoxSound subbox1_60 :=
  LRCompactVLeafParameters.sound checked1_60


def subbox1_61 : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((5 : ℚ) / 32), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩

theorem checked1_61 :
    LRCompactVLeafParameters.check subbox1_61 .short = true := by decide +kernel

theorem subsound1_61 : LRCompactVBoxSound subbox1_61 :=
  LRCompactVLeafParameters.sound checked1_61


def subbox1_62 : CertificateBox :=
  ⟨((5 : ℚ) / 32), ((3 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩

theorem checked1_62 :
    LRCompactVLeafParameters.check subbox1_62 .long = true := by decide +kernel

theorem subsound1_62 : LRCompactVBoxSound subbox1_62 :=
  LRCompactVLeafParameters.sound checked1_62


def subbox1_63 : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((5 : ℚ) / 32), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩

theorem checked1_63 :
    LRCompactVLeafParameters.check subbox1_63 .short = true := by decide +kernel

theorem subsound1_63 : LRCompactVBoxSound subbox1_63 :=
  LRCompactVLeafParameters.sound checked1_63


def subbox1_64 : CertificateBox :=
  ⟨((5 : ℚ) / 32), ((3 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩

theorem checked1_64 :
    LRCompactVLeafParameters.check subbox1_64 .long = true := by decide +kernel

theorem subsound1_64 : LRCompactVBoxSound subbox1_64 :=
  LRCompactVLeafParameters.sound checked1_64


def subbox1_65 : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((7 : ℚ) / 32), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩

theorem checked1_65 :
    LRCompactVLeafParameters.check subbox1_65 .long = true := by decide +kernel

theorem subsound1_65 : LRCompactVBoxSound subbox1_65 :=
  LRCompactVLeafParameters.sound checked1_65


def subbox1_66 : CertificateBox :=
  ⟨((7 : ℚ) / 32), ((1 : ℚ) / 4), ((5 : ℚ) / 12), ((7 : ℚ) / 16), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩

theorem checked1_66 :
    LRCompactVLeafParameters.check subbox1_66 .short = true := by decide +kernel

theorem subsound1_66 : LRCompactVBoxSound subbox1_66 :=
  LRCompactVLeafParameters.sound checked1_66


def subbox1_67 : CertificateBox :=
  ⟨((7 : ℚ) / 32), ((1 : ℚ) / 4), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩

theorem checked1_67 :
    LRCompactVLeafParameters.check subbox1_67 .short = true := by decide +kernel

theorem subsound1_67 : LRCompactVBoxSound subbox1_67 :=
  LRCompactVLeafParameters.sound checked1_67


def subbox1_68 : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((7 : ℚ) / 32), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩

theorem checked1_68 :
    LRCompactVLeafParameters.check subbox1_68 .short = true := by decide +kernel

theorem subsound1_68 : LRCompactVBoxSound subbox1_68 :=
  LRCompactVLeafParameters.sound checked1_68


def subbox1_69 : CertificateBox :=
  ⟨((7 : ℚ) / 32), ((1 : ℚ) / 4), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩

theorem checked1_69 :
    LRCompactVLeafParameters.check subbox1_69 .long = true := by decide +kernel

theorem subsound1_69 : LRCompactVBoxSound subbox1_69 :=
  LRCompactVLeafParameters.sound checked1_69


def subbox1_70 : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((7 : ℚ) / 32), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩

theorem checked1_70 :
    LRCompactVLeafParameters.check subbox1_70 .short = true := by decide +kernel

theorem subsound1_70 : LRCompactVBoxSound subbox1_70 :=
  LRCompactVLeafParameters.sound checked1_70


def subbox1_71 : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((7 : ℚ) / 32), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩

theorem checked1_71 :
    LRCompactVLeafParameters.check subbox1_71 .short = true := by decide +kernel

theorem subsound1_71 : LRCompactVBoxSound subbox1_71 :=
  LRCompactVLeafParameters.sound checked1_71


def subbox1_72 : CertificateBox :=
  ⟨((7 : ℚ) / 32), ((1 : ℚ) / 4), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩

theorem checked1_72 :
    LRCompactVLeafParameters.check subbox1_72 .short = true := by decide +kernel

theorem subsound1_72 : LRCompactVBoxSound subbox1_72 :=
  LRCompactVLeafParameters.sound checked1_72


def subbox1_73 : CertificateBox :=
  ⟨((7 : ℚ) / 32), ((1 : ℚ) / 4), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩

theorem checked1_73 :
    LRCompactVLeafParameters.check subbox1_73 .short = true := by decide +kernel

theorem subsound1_73 : LRCompactVBoxSound subbox1_73 :=
  LRCompactVLeafParameters.sound checked1_73


def subbox1_74 : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((7 : ℚ) / 32), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩

theorem checked1_74 :
    LRCompactVLeafParameters.check subbox1_74 .short = true := by decide +kernel

theorem subsound1_74 : LRCompactVBoxSound subbox1_74 :=
  LRCompactVLeafParameters.sound checked1_74


def subbox1_75 : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((7 : ℚ) / 32), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩

theorem checked1_75 :
    LRCompactVLeafParameters.check subbox1_75 .short = true := by decide +kernel

theorem subsound1_75 : LRCompactVBoxSound subbox1_75 :=
  LRCompactVLeafParameters.sound checked1_75


def subbox1_76 : CertificateBox :=
  ⟨((7 : ℚ) / 32), ((1 : ℚ) / 4), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩

theorem checked1_76 :
    LRCompactVLeafParameters.check subbox1_76 .short = true := by decide +kernel

theorem subsound1_76 : LRCompactVBoxSound subbox1_76 :=
  LRCompactVLeafParameters.sound checked1_76


def subbox1_77 : CertificateBox :=
  ⟨((7 : ℚ) / 32), ((1 : ℚ) / 4), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩

theorem checked1_77 :
    LRCompactVLeafParameters.check subbox1_77 .short = true := by decide +kernel

theorem subsound1_77 : LRCompactVBoxSound subbox1_77 :=
  LRCompactVLeafParameters.sound checked1_77


def joinbox1_rLLLRL : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((1 : ℚ) / 4), ((1 : ℚ) / 3), ((5 : ℚ) / 12), ((17 : ℚ) / 20), ((71 : ℚ) / 80)⟩


def joinbox1_rLLLRLL : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((1 : ℚ) / 4), ((1 : ℚ) / 3), ((5 : ℚ) / 12), ((17 : ℚ) / 20), ((139 : ℚ) / 160)⟩


def joinbox1_rLLLRLLL : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((3 : ℚ) / 16), ((1 : ℚ) / 3), ((5 : ℚ) / 12), ((17 : ℚ) / 20), ((139 : ℚ) / 160)⟩


def joinbox1_rLLLRLLLL : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((3 : ℚ) / 16), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((17 : ℚ) / 20), ((139 : ℚ) / 160)⟩


def joinbox1_rLLLRLLLLL : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((3 : ℚ) / 16), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩


def joinbox1_rLLLRLLLLR : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((3 : ℚ) / 16), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩


def joinbox1_rLLLRLLLR : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((3 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((17 : ℚ) / 20), ((139 : ℚ) / 160)⟩


def joinbox1_rLLLRLLLRL : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((3 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩


def joinbox1_rLLLRLLLRR : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((3 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩


def joinbox1_rLLLRLLR : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((1 : ℚ) / 4), ((1 : ℚ) / 3), ((5 : ℚ) / 12), ((17 : ℚ) / 20), ((139 : ℚ) / 160)⟩


def joinbox1_rLLLRLLRL : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((1 : ℚ) / 4), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((17 : ℚ) / 20), ((139 : ℚ) / 160)⟩


def joinbox1_rLLLRLLRLL : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((1 : ℚ) / 4), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩


def joinbox1_rLLLRLLRLR : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((1 : ℚ) / 4), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩


def joinbox1_rLLLRLLRR : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((1 : ℚ) / 4), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((17 : ℚ) / 20), ((139 : ℚ) / 160)⟩


def joinbox1_rLLLRLLRRL : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((1 : ℚ) / 4), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩


def joinbox1_rLLLRLLRRLR : CertificateBox :=
  ⟨((7 : ℚ) / 32), ((1 : ℚ) / 4), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩


def joinbox1_rLLLRLLRRR : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((1 : ℚ) / 4), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩


def joinbox1_rLLLRLR : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((1 : ℚ) / 4), ((1 : ℚ) / 3), ((5 : ℚ) / 12), ((139 : ℚ) / 160), ((71 : ℚ) / 80)⟩


def joinbox1_rLLLRLRL : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((3 : ℚ) / 16), ((1 : ℚ) / 3), ((5 : ℚ) / 12), ((139 : ℚ) / 160), ((71 : ℚ) / 80)⟩


def joinbox1_rLLLRLRLL : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((3 : ℚ) / 16), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((139 : ℚ) / 160), ((71 : ℚ) / 80)⟩


def joinbox1_rLLLRLRLLL : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((3 : ℚ) / 16), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩


def joinbox1_rLLLRLRLLR : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((3 : ℚ) / 16), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩


def joinbox1_rLLLRLRLR : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((3 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((139 : ℚ) / 160), ((71 : ℚ) / 80)⟩


def joinbox1_rLLLRLRLRL : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((3 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩


def joinbox1_rLLLRLRLRR : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((3 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩


def joinbox1_rLLLRLRR : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((1 : ℚ) / 4), ((1 : ℚ) / 3), ((5 : ℚ) / 12), ((139 : ℚ) / 160), ((71 : ℚ) / 80)⟩


def joinbox1_rLLLRLRRL : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((1 : ℚ) / 4), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((139 : ℚ) / 160), ((71 : ℚ) / 80)⟩


def joinbox1_rLLLRLRRLL : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((1 : ℚ) / 4), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩


def joinbox1_rLLLRLRRLR : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((1 : ℚ) / 4), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩


def joinbox1_rLLLRLRRR : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((1 : ℚ) / 4), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((139 : ℚ) / 160), ((71 : ℚ) / 80)⟩


def joinbox1_rLLLRLRRRL : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((1 : ℚ) / 4), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩


def joinbox1_rLLLRLRRRR : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((1 : ℚ) / 4), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩


def joinbox1_rLLLRR : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((1 : ℚ) / 4), ((5 : ℚ) / 12), ((1 : ℚ) / 2), ((17 : ℚ) / 20), ((71 : ℚ) / 80)⟩


def joinbox1_rLLLRRL : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((1 : ℚ) / 4), ((5 : ℚ) / 12), ((1 : ℚ) / 2), ((17 : ℚ) / 20), ((139 : ℚ) / 160)⟩


def joinbox1_rLLLRRLL : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((3 : ℚ) / 16), ((5 : ℚ) / 12), ((1 : ℚ) / 2), ((17 : ℚ) / 20), ((139 : ℚ) / 160)⟩


def joinbox1_rLLLRRLLL : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((3 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((17 : ℚ) / 20), ((139 : ℚ) / 160)⟩


def joinbox1_rLLLRRLLLL : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((3 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩


def joinbox1_rLLLRRLLLR : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((3 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩


def joinbox1_rLLLRRLLR : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((3 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((17 : ℚ) / 20), ((139 : ℚ) / 160)⟩


def joinbox1_rLLLRRLLRL : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((3 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩


def joinbox1_rLLLRRLLRLR : CertificateBox :=
  ⟨((5 : ℚ) / 32), ((3 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩


def joinbox1_rLLLRRLLRR : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((3 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩


def joinbox1_rLLLRRLR : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((1 : ℚ) / 4), ((5 : ℚ) / 12), ((1 : ℚ) / 2), ((17 : ℚ) / 20), ((139 : ℚ) / 160)⟩


def joinbox1_rLLLRRLRL : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((1 : ℚ) / 4), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((17 : ℚ) / 20), ((139 : ℚ) / 160)⟩


def joinbox1_rLLLRRLRLL : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((1 : ℚ) / 4), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩


def joinbox1_rLLLRRLRLLL : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((7 : ℚ) / 32), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩


def joinbox1_rLLLRRLRLLR : CertificateBox :=
  ⟨((7 : ℚ) / 32), ((1 : ℚ) / 4), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩


def joinbox1_rLLLRRLRLR : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((1 : ℚ) / 4), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩


def joinbox1_rLLLRRLRLRR : CertificateBox :=
  ⟨((7 : ℚ) / 32), ((1 : ℚ) / 4), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩


def joinbox1_rLLLRRLRR : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((1 : ℚ) / 4), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((17 : ℚ) / 20), ((139 : ℚ) / 160)⟩


def joinbox1_rLLLRRLRRL : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((1 : ℚ) / 4), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩


def joinbox1_rLLLRRLRRLL : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((7 : ℚ) / 32), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩


def joinbox1_rLLLRRLRRLR : CertificateBox :=
  ⟨((7 : ℚ) / 32), ((1 : ℚ) / 4), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩


def joinbox1_rLLLRRLRRR : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((1 : ℚ) / 4), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩


def joinbox1_rLLLRRLRRRL : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((7 : ℚ) / 32), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩


def joinbox1_rLLLRRLRRRR : CertificateBox :=
  ⟨((7 : ℚ) / 32), ((1 : ℚ) / 4), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩


def joinbox1_rLLLRRR : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((1 : ℚ) / 4), ((5 : ℚ) / 12), ((1 : ℚ) / 2), ((139 : ℚ) / 160), ((71 : ℚ) / 80)⟩


def joinbox1_rLLLRRRL : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((3 : ℚ) / 16), ((5 : ℚ) / 12), ((1 : ℚ) / 2), ((139 : ℚ) / 160), ((71 : ℚ) / 80)⟩


def joinbox1_rLLLRRRLL : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((3 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((139 : ℚ) / 160), ((71 : ℚ) / 80)⟩


def joinbox1_rLLLRRRLLL : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((3 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩


def joinbox1_rLLLRRRLLR : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((3 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩


def joinbox1_rLLLRRRLR : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((3 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((139 : ℚ) / 160), ((71 : ℚ) / 80)⟩


def joinbox1_rLLLRRRLRL : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((3 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩


def joinbox1_rLLLRRRLRR : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((3 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩


def joinbox1_rLLLRRRR : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((1 : ℚ) / 4), ((5 : ℚ) / 12), ((1 : ℚ) / 2), ((139 : ℚ) / 160), ((71 : ℚ) / 80)⟩


def joinbox1_rLLLRRRRL : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((1 : ℚ) / 4), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((139 : ℚ) / 160), ((71 : ℚ) / 80)⟩


def joinbox1_rLLLRRRRLL : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((1 : ℚ) / 4), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩


def joinbox1_rLLLRRRRLLR : CertificateBox :=
  ⟨((7 : ℚ) / 32), ((1 : ℚ) / 4), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩


def joinbox1_rLLLRRRRLR : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((1 : ℚ) / 4), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩


def joinbox1_rLLLRRRRR : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((1 : ℚ) / 4), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((139 : ℚ) / 160), ((71 : ℚ) / 80)⟩


def joinbox1_rLLLRRRRRL : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((1 : ℚ) / 4), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩


def joinbox1_rLLLRRRRRLL : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((7 : ℚ) / 32), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩


def joinbox1_rLLLRRRRRLR : CertificateBox :=
  ⟨((7 : ℚ) / 32), ((1 : ℚ) / 4), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩


def joinbox1_rLLLRRRRRR : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((1 : ℚ) / 4), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩


def joinbox1_rLLLRRRRRRL : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((7 : ℚ) / 32), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩


def joinbox1_rLLLRRRRRRR : CertificateBox :=
  ⟨((7 : ℚ) / 32), ((1 : ℚ) / 4), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩


theorem sound1 : LRCompactVBoxSound box1 :=
  (LRCompactVBoxSound.join (box := box1) .k ((5 : ℚ) / 12)
    (LRCompactVBoxSound.join (box := joinbox1_rLLLRL) .chi ((139 : ℚ) / 160)
      (LRCompactVBoxSound.join (box := joinbox1_rLLLRLL) .s ((3 : ℚ) / 16)
        (LRCompactVBoxSound.join (box := joinbox1_rLLLRLLL) .k ((3 : ℚ) / 8)
          (LRCompactVBoxSound.join (box := joinbox1_rLLLRLLLL) .chi ((55 : ℚ) / 64)
            (LRCompactVBoxSound.join (box := joinbox1_rLLLRLLLLL) .s ((5 : ℚ) / 32)
              subsound1_0
              subsound1_1)
            (LRCompactVBoxSound.join (box := joinbox1_rLLLRLLLLR) .s ((5 : ℚ) / 32)
              subsound1_2
              subsound1_3))
          (LRCompactVBoxSound.join (box := joinbox1_rLLLRLLLR) .chi ((55 : ℚ) / 64)
            (LRCompactVBoxSound.join (box := joinbox1_rLLLRLLLRL) .s ((5 : ℚ) / 32)
              subsound1_4
              subsound1_5)
            (LRCompactVBoxSound.join (box := joinbox1_rLLLRLLLRR) .s ((5 : ℚ) / 32)
              subsound1_6
              subsound1_7)))
        (LRCompactVBoxSound.join (box := joinbox1_rLLLRLLR) .k ((3 : ℚ) / 8)
          (LRCompactVBoxSound.join (box := joinbox1_rLLLRLLRL) .chi ((55 : ℚ) / 64)
            (LRCompactVBoxSound.join (box := joinbox1_rLLLRLLRLL) .s ((7 : ℚ) / 32)
              subsound1_8
              subsound1_9)
            (LRCompactVBoxSound.join (box := joinbox1_rLLLRLLRLR) .s ((7 : ℚ) / 32)
              subsound1_10
              subsound1_11))
          (LRCompactVBoxSound.join (box := joinbox1_rLLLRLLRR) .chi ((55 : ℚ) / 64)
            (LRCompactVBoxSound.join (box := joinbox1_rLLLRLLRRL) .s ((7 : ℚ) / 32)
              subsound1_12
              (LRCompactVBoxSound.join (box := joinbox1_rLLLRLLRRLR) .k ((19 : ℚ) / 48)
                subsound1_13
                subsound1_14))
            (LRCompactVBoxSound.join (box := joinbox1_rLLLRLLRRR) .s ((7 : ℚ) / 32)
              subsound1_15
              subsound1_16))))
      (LRCompactVBoxSound.join (box := joinbox1_rLLLRLR) .s ((3 : ℚ) / 16)
        (LRCompactVBoxSound.join (box := joinbox1_rLLLRLRL) .k ((3 : ℚ) / 8)
          (LRCompactVBoxSound.join (box := joinbox1_rLLLRLRLL) .chi ((281 : ℚ) / 320)
            (LRCompactVBoxSound.join (box := joinbox1_rLLLRLRLLL) .s ((5 : ℚ) / 32)
              subsound1_17
              subsound1_18)
            (LRCompactVBoxSound.join (box := joinbox1_rLLLRLRLLR) .s ((5 : ℚ) / 32)
              subsound1_19
              subsound1_20))
          (LRCompactVBoxSound.join (box := joinbox1_rLLLRLRLR) .chi ((281 : ℚ) / 320)
            (LRCompactVBoxSound.join (box := joinbox1_rLLLRLRLRL) .s ((5 : ℚ) / 32)
              subsound1_21
              subsound1_22)
            (LRCompactVBoxSound.join (box := joinbox1_rLLLRLRLRR) .s ((5 : ℚ) / 32)
              subsound1_23
              subsound1_24)))
        (LRCompactVBoxSound.join (box := joinbox1_rLLLRLRR) .k ((3 : ℚ) / 8)
          (LRCompactVBoxSound.join (box := joinbox1_rLLLRLRRL) .chi ((281 : ℚ) / 320)
            (LRCompactVBoxSound.join (box := joinbox1_rLLLRLRRLL) .s ((7 : ℚ) / 32)
              subsound1_25
              subsound1_26)
            (LRCompactVBoxSound.join (box := joinbox1_rLLLRLRRLR) .s ((7 : ℚ) / 32)
              subsound1_27
              subsound1_28))
          (LRCompactVBoxSound.join (box := joinbox1_rLLLRLRRR) .chi ((281 : ℚ) / 320)
            (LRCompactVBoxSound.join (box := joinbox1_rLLLRLRRRL) .s ((7 : ℚ) / 32)
              subsound1_29
              subsound1_30)
            (LRCompactVBoxSound.join (box := joinbox1_rLLLRLRRRR) .s ((7 : ℚ) / 32)
              subsound1_31
              subsound1_32)))))
    (LRCompactVBoxSound.join (box := joinbox1_rLLLRR) .chi ((139 : ℚ) / 160)
      (LRCompactVBoxSound.join (box := joinbox1_rLLLRRL) .s ((3 : ℚ) / 16)
        (LRCompactVBoxSound.join (box := joinbox1_rLLLRRLL) .k ((11 : ℚ) / 24)
          (LRCompactVBoxSound.join (box := joinbox1_rLLLRRLLL) .chi ((55 : ℚ) / 64)
            (LRCompactVBoxSound.join (box := joinbox1_rLLLRRLLLL) .s ((5 : ℚ) / 32)
              subsound1_33
              subsound1_34)
            (LRCompactVBoxSound.join (box := joinbox1_rLLLRRLLLR) .s ((5 : ℚ) / 32)
              subsound1_35
              subsound1_36))
          (LRCompactVBoxSound.join (box := joinbox1_rLLLRRLLR) .chi ((55 : ℚ) / 64)
            (LRCompactVBoxSound.join (box := joinbox1_rLLLRRLLRL) .s ((5 : ℚ) / 32)
              subsound1_37
              (LRCompactVBoxSound.join (box := joinbox1_rLLLRRLLRLR) .k ((23 : ℚ) / 48)
                subsound1_38
                subsound1_39))
            (LRCompactVBoxSound.join (box := joinbox1_rLLLRRLLRR) .s ((5 : ℚ) / 32)
              subsound1_40
              subsound1_41)))
        (LRCompactVBoxSound.join (box := joinbox1_rLLLRRLR) .k ((11 : ℚ) / 24)
          (LRCompactVBoxSound.join (box := joinbox1_rLLLRRLRL) .chi ((55 : ℚ) / 64)
            (LRCompactVBoxSound.join (box := joinbox1_rLLLRRLRLL) .s ((7 : ℚ) / 32)
              (LRCompactVBoxSound.join (box := joinbox1_rLLLRRLRLLL) .k ((7 : ℚ) / 16)
                subsound1_42
                subsound1_43)
              (LRCompactVBoxSound.join (box := joinbox1_rLLLRRLRLLR) .k ((7 : ℚ) / 16)
                subsound1_44
                subsound1_45))
            (LRCompactVBoxSound.join (box := joinbox1_rLLLRRLRLR) .s ((7 : ℚ) / 32)
              subsound1_46
              (LRCompactVBoxSound.join (box := joinbox1_rLLLRRLRLRR) .k ((7 : ℚ) / 16)
                subsound1_47
                subsound1_48)))
          (LRCompactVBoxSound.join (box := joinbox1_rLLLRRLRR) .chi ((55 : ℚ) / 64)
            (LRCompactVBoxSound.join (box := joinbox1_rLLLRRLRRL) .s ((7 : ℚ) / 32)
              (LRCompactVBoxSound.join (box := joinbox1_rLLLRRLRRLL) .k ((23 : ℚ) / 48)
                subsound1_49
                subsound1_50)
              (LRCompactVBoxSound.join (box := joinbox1_rLLLRRLRRLR) .k ((23 : ℚ) / 48)
                subsound1_51
                subsound1_52))
            (LRCompactVBoxSound.join (box := joinbox1_rLLLRRLRRR) .s ((7 : ℚ) / 32)
              (LRCompactVBoxSound.join (box := joinbox1_rLLLRRLRRRL) .k ((23 : ℚ) / 48)
                subsound1_53
                subsound1_54)
              (LRCompactVBoxSound.join (box := joinbox1_rLLLRRLRRRR) .k ((23 : ℚ) / 48)
                subsound1_55
                subsound1_56)))))
      (LRCompactVBoxSound.join (box := joinbox1_rLLLRRR) .s ((3 : ℚ) / 16)
        (LRCompactVBoxSound.join (box := joinbox1_rLLLRRRL) .k ((11 : ℚ) / 24)
          (LRCompactVBoxSound.join (box := joinbox1_rLLLRRRLL) .chi ((281 : ℚ) / 320)
            (LRCompactVBoxSound.join (box := joinbox1_rLLLRRRLLL) .s ((5 : ℚ) / 32)
              subsound1_57
              subsound1_58)
            (LRCompactVBoxSound.join (box := joinbox1_rLLLRRRLLR) .s ((5 : ℚ) / 32)
              subsound1_59
              subsound1_60))
          (LRCompactVBoxSound.join (box := joinbox1_rLLLRRRLR) .chi ((281 : ℚ) / 320)
            (LRCompactVBoxSound.join (box := joinbox1_rLLLRRRLRL) .s ((5 : ℚ) / 32)
              subsound1_61
              subsound1_62)
            (LRCompactVBoxSound.join (box := joinbox1_rLLLRRRLRR) .s ((5 : ℚ) / 32)
              subsound1_63
              subsound1_64)))
        (LRCompactVBoxSound.join (box := joinbox1_rLLLRRRR) .k ((11 : ℚ) / 24)
          (LRCompactVBoxSound.join (box := joinbox1_rLLLRRRRL) .chi ((281 : ℚ) / 320)
            (LRCompactVBoxSound.join (box := joinbox1_rLLLRRRRLL) .s ((7 : ℚ) / 32)
              subsound1_65
              (LRCompactVBoxSound.join (box := joinbox1_rLLLRRRRLLR) .k ((7 : ℚ) / 16)
                subsound1_66
                subsound1_67))
            (LRCompactVBoxSound.join (box := joinbox1_rLLLRRRRLR) .s ((7 : ℚ) / 32)
              subsound1_68
              subsound1_69))
          (LRCompactVBoxSound.join (box := joinbox1_rLLLRRRRR) .chi ((281 : ℚ) / 320)
            (LRCompactVBoxSound.join (box := joinbox1_rLLLRRRRRL) .s ((7 : ℚ) / 32)
              (LRCompactVBoxSound.join (box := joinbox1_rLLLRRRRRLL) .k ((23 : ℚ) / 48)
                subsound1_70
                subsound1_71)
              (LRCompactVBoxSound.join (box := joinbox1_rLLLRRRRRLR) .k ((23 : ℚ) / 48)
                subsound1_72
                subsound1_73))
            (LRCompactVBoxSound.join (box := joinbox1_rLLLRRRRRR) .s ((7 : ℚ) / 32)
              (LRCompactVBoxSound.join (box := joinbox1_rLLLRRRRRRL) .k ((23 : ℚ) / 48)
                subsound1_74
                subsound1_75)
              (LRCompactVBoxSound.join (box := joinbox1_rLLLRRRRRRR) .k ((23 : ℚ) / 48)
                subsound1_76
                subsound1_77)))))))

end CourtadeKumar.GeneratedLRCompactVLowR
