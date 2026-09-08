import InformationTheory.CourtadeKumar.LRCompactVBasicReplay

/-! Frozen basic compact-V replay.
Plan SHA-256: ce3f7a498b2b9caf346dcf88ce7861f8cc091af8cd93f5624d7684e21322ecd5
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CourtadeKumar.GeneratedLRCompactVLowR

-- 81 accepted leaves below path rRLL.
def box9 : CertificateBox where
  sLo := (0 : ℚ)
  sHi := ((1 : ℚ) / 4)
  kLo := ((1 : ℚ) / 3)
  kHi := ((1 : ℚ) / 2)
  chiLo := ((37 : ℚ) / 40)
  chiHi := ((77 : ℚ) / 80)


def subbox9_0 : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 16), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((37 : ℚ) / 40), ((151 : ℚ) / 160)⟩

theorem checked9_0 :
    LRCompactVLeafParameters.check subbox9_0 .short = true := by decide +kernel

theorem subsound9_0 : LRCompactVBoxSound subbox9_0 :=
  LRCompactVLeafParameters.sound checked9_0


def subbox9_1 : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((37 : ℚ) / 40), ((151 : ℚ) / 160)⟩

theorem checked9_1 :
    LRCompactVLeafParameters.check subbox9_1 .long = true := by decide +kernel

theorem subsound9_1 : LRCompactVBoxSound subbox9_1 :=
  LRCompactVLeafParameters.sound checked9_1


def subbox9_2 : CertificateBox :=
  ⟨((1 : ℚ) / 16), ((1 : ℚ) / 8), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((37 : ℚ) / 40), ((151 : ℚ) / 160)⟩

theorem checked9_2 :
    LRCompactVLeafParameters.check subbox9_2 .long = true := by decide +kernel

theorem subsound9_2 : LRCompactVBoxSound subbox9_2 :=
  LRCompactVLeafParameters.sound checked9_2


def subbox9_3 : CertificateBox :=
  ⟨((1 : ℚ) / 16), ((1 : ℚ) / 8), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((37 : ℚ) / 40), ((299 : ℚ) / 320)⟩

theorem checked9_3 :
    LRCompactVLeafParameters.check subbox9_3 .short = true := by decide +kernel

theorem subsound9_3 : LRCompactVBoxSound subbox9_3 :=
  LRCompactVLeafParameters.sound checked9_3


def subbox9_4 : CertificateBox :=
  ⟨((1 : ℚ) / 16), ((1 : ℚ) / 8), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((299 : ℚ) / 320), ((151 : ℚ) / 160)⟩

theorem checked9_4 :
    LRCompactVLeafParameters.check subbox9_4 .short = true := by decide +kernel

theorem subsound9_4 : LRCompactVBoxSound subbox9_4 :=
  LRCompactVLeafParameters.sound checked9_4


def subbox9_5 : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 16), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((151 : ℚ) / 160), ((77 : ℚ) / 80)⟩

theorem checked9_5 :
    LRCompactVLeafParameters.check subbox9_5 .short = true := by decide +kernel

theorem subsound9_5 : LRCompactVBoxSound subbox9_5 :=
  LRCompactVLeafParameters.sound checked9_5


def subbox9_6 : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((151 : ℚ) / 160), ((77 : ℚ) / 80)⟩

theorem checked9_6 :
    LRCompactVLeafParameters.check subbox9_6 .accurateLog = true := by decide +kernel

theorem subsound9_6 : LRCompactVBoxSound subbox9_6 :=
  LRCompactVLeafParameters.sound checked9_6


def subbox9_7 : CertificateBox :=
  ⟨((1 : ℚ) / 16), ((1 : ℚ) / 8), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((151 : ℚ) / 160), ((77 : ℚ) / 80)⟩

theorem checked9_7 :
    LRCompactVLeafParameters.check subbox9_7 .accurateLog = true := by decide +kernel

theorem subsound9_7 : LRCompactVBoxSound subbox9_7 :=
  LRCompactVLeafParameters.sound checked9_7


def subbox9_8 : CertificateBox :=
  ⟨((1 : ℚ) / 16), ((1 : ℚ) / 8), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((151 : ℚ) / 160), ((61 : ℚ) / 64)⟩

theorem checked9_8 :
    LRCompactVLeafParameters.check subbox9_8 .short = true := by decide +kernel

theorem subsound9_8 : LRCompactVBoxSound subbox9_8 :=
  LRCompactVLeafParameters.sound checked9_8


def subbox9_9 : CertificateBox :=
  ⟨((1 : ℚ) / 16), ((1 : ℚ) / 8), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((61 : ℚ) / 64), ((77 : ℚ) / 80)⟩

theorem checked9_9 :
    LRCompactVLeafParameters.check subbox9_9 .short = true := by decide +kernel

theorem subsound9_9 : LRCompactVBoxSound subbox9_9 :=
  LRCompactVLeafParameters.sound checked9_9


def subbox9_10 : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((37 : ℚ) / 40), ((299 : ℚ) / 320)⟩

theorem checked9_10 :
    LRCompactVLeafParameters.check subbox9_10 .short = true := by decide +kernel

theorem subsound9_10 : LRCompactVBoxSound subbox9_10 :=
  LRCompactVLeafParameters.sound checked9_10


def subbox9_11 : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((299 : ℚ) / 320), ((151 : ℚ) / 160)⟩

theorem checked9_11 :
    LRCompactVLeafParameters.check subbox9_11 .short = true := by decide +kernel

theorem subsound9_11 : LRCompactVBoxSound subbox9_11 :=
  LRCompactVLeafParameters.sound checked9_11


def subbox9_12 : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((37 : ℚ) / 40), ((299 : ℚ) / 320)⟩

theorem checked9_12 :
    LRCompactVLeafParameters.check subbox9_12 .long = true := by decide +kernel

theorem subsound9_12 : LRCompactVBoxSound subbox9_12 :=
  LRCompactVLeafParameters.sound checked9_12


def subbox9_13 : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((299 : ℚ) / 320), ((151 : ℚ) / 160)⟩

theorem checked9_13 :
    LRCompactVLeafParameters.check subbox9_13 .long = true := by decide +kernel

theorem subsound9_13 : LRCompactVBoxSound subbox9_13 :=
  LRCompactVLeafParameters.sound checked9_13


def subbox9_14 : CertificateBox :=
  ⟨((1 : ℚ) / 16), ((1 : ℚ) / 8), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((37 : ℚ) / 40), ((299 : ℚ) / 320)⟩

theorem checked9_14 :
    LRCompactVLeafParameters.check subbox9_14 .long = true := by decide +kernel

theorem subsound9_14 : LRCompactVBoxSound subbox9_14 :=
  LRCompactVLeafParameters.sound checked9_14


def subbox9_15 : CertificateBox :=
  ⟨((1 : ℚ) / 16), ((1 : ℚ) / 8), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((299 : ℚ) / 320), ((151 : ℚ) / 160)⟩

theorem checked9_15 :
    LRCompactVLeafParameters.check subbox9_15 .long = true := by decide +kernel

theorem subsound9_15 : LRCompactVBoxSound subbox9_15 :=
  LRCompactVLeafParameters.sound checked9_15


def subbox9_16 : CertificateBox :=
  ⟨((1 : ℚ) / 16), ((3 : ℚ) / 32), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((37 : ℚ) / 40), ((299 : ℚ) / 320)⟩

theorem checked9_16 :
    LRCompactVLeafParameters.check subbox9_16 .short = true := by decide +kernel

theorem subsound9_16 : LRCompactVBoxSound subbox9_16 :=
  LRCompactVLeafParameters.sound checked9_16


def subbox9_17 : CertificateBox :=
  ⟨((3 : ℚ) / 32), ((1 : ℚ) / 8), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((37 : ℚ) / 40), ((299 : ℚ) / 320)⟩

theorem checked9_17 :
    LRCompactVLeafParameters.check subbox9_17 .short = true := by decide +kernel

theorem subsound9_17 : LRCompactVBoxSound subbox9_17 :=
  LRCompactVLeafParameters.sound checked9_17


def subbox9_18 : CertificateBox :=
  ⟨((1 : ℚ) / 16), ((3 : ℚ) / 32), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((299 : ℚ) / 320), ((151 : ℚ) / 160)⟩

theorem checked9_18 :
    LRCompactVLeafParameters.check subbox9_18 .short = true := by decide +kernel

theorem subsound9_18 : LRCompactVBoxSound subbox9_18 :=
  LRCompactVLeafParameters.sound checked9_18


def subbox9_19 : CertificateBox :=
  ⟨((3 : ℚ) / 32), ((1 : ℚ) / 8), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((299 : ℚ) / 320), ((151 : ℚ) / 160)⟩

theorem checked9_19 :
    LRCompactVLeafParameters.check subbox9_19 .short = true := by decide +kernel

theorem subsound9_19 : LRCompactVBoxSound subbox9_19 :=
  LRCompactVLeafParameters.sound checked9_19


def subbox9_20 : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((151 : ℚ) / 160), ((61 : ℚ) / 64)⟩

theorem checked9_20 :
    LRCompactVLeafParameters.check subbox9_20 .short = true := by decide +kernel

theorem subsound9_20 : LRCompactVBoxSound subbox9_20 :=
  LRCompactVLeafParameters.sound checked9_20


def subbox9_21 : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((61 : ℚ) / 64), ((77 : ℚ) / 80)⟩

theorem checked9_21 :
    LRCompactVLeafParameters.check subbox9_21 .short = true := by decide +kernel

theorem subsound9_21 : LRCompactVBoxSound subbox9_21 :=
  LRCompactVLeafParameters.sound checked9_21


def subbox9_22 : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((151 : ℚ) / 160), ((61 : ℚ) / 64)⟩

theorem checked9_22 :
    LRCompactVLeafParameters.check subbox9_22 .long = true := by decide +kernel

theorem subsound9_22 : LRCompactVBoxSound subbox9_22 :=
  LRCompactVLeafParameters.sound checked9_22


def subbox9_23 : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((61 : ℚ) / 64), ((77 : ℚ) / 80)⟩

theorem checked9_23 :
    LRCompactVLeafParameters.check subbox9_23 .long = true := by decide +kernel

theorem subsound9_23 : LRCompactVBoxSound subbox9_23 :=
  LRCompactVLeafParameters.sound checked9_23


def subbox9_24 : CertificateBox :=
  ⟨((1 : ℚ) / 16), ((1 : ℚ) / 8), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((151 : ℚ) / 160), ((61 : ℚ) / 64)⟩

theorem checked9_24 :
    LRCompactVLeafParameters.check subbox9_24 .long = true := by decide +kernel

theorem subsound9_24 : LRCompactVBoxSound subbox9_24 :=
  LRCompactVLeafParameters.sound checked9_24


def subbox9_25 : CertificateBox :=
  ⟨((1 : ℚ) / 16), ((1 : ℚ) / 8), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((61 : ℚ) / 64), ((77 : ℚ) / 80)⟩

theorem checked9_25 :
    LRCompactVLeafParameters.check subbox9_25 .short = true := by decide +kernel

theorem subsound9_25 : LRCompactVBoxSound subbox9_25 :=
  LRCompactVLeafParameters.sound checked9_25


def subbox9_26 : CertificateBox :=
  ⟨((1 : ℚ) / 16), ((3 : ℚ) / 32), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((151 : ℚ) / 160), ((61 : ℚ) / 64)⟩

theorem checked9_26 :
    LRCompactVLeafParameters.check subbox9_26 .short = true := by decide +kernel

theorem subsound9_26 : LRCompactVBoxSound subbox9_26 :=
  LRCompactVLeafParameters.sound checked9_26


def subbox9_27 : CertificateBox :=
  ⟨((3 : ℚ) / 32), ((1 : ℚ) / 8), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((151 : ℚ) / 160), ((61 : ℚ) / 64)⟩

theorem checked9_27 :
    LRCompactVLeafParameters.check subbox9_27 .short = true := by decide +kernel

theorem subsound9_27 : LRCompactVBoxSound subbox9_27 :=
  LRCompactVLeafParameters.sound checked9_27


def subbox9_28 : CertificateBox :=
  ⟨((1 : ℚ) / 16), ((1 : ℚ) / 8), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((61 : ℚ) / 64), ((77 : ℚ) / 80)⟩

theorem checked9_28 :
    LRCompactVLeafParameters.check subbox9_28 .long = true := by decide +kernel

theorem subsound9_28 : LRCompactVBoxSound subbox9_28 :=
  LRCompactVLeafParameters.sound checked9_28


def subbox9_29 : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((3 : ℚ) / 16), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((37 : ℚ) / 40), ((299 : ℚ) / 320)⟩

theorem checked9_29 :
    LRCompactVLeafParameters.check subbox9_29 .short = true := by decide +kernel

theorem subsound9_29 : LRCompactVBoxSound subbox9_29 :=
  LRCompactVLeafParameters.sound checked9_29


def subbox9_30 : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((3 : ℚ) / 16), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((299 : ℚ) / 320), ((151 : ℚ) / 160)⟩

theorem checked9_30 :
    LRCompactVLeafParameters.check subbox9_30 .short = true := by decide +kernel

theorem subsound9_30 : LRCompactVBoxSound subbox9_30 :=
  LRCompactVLeafParameters.sound checked9_30


def subbox9_31 : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((3 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((37 : ℚ) / 40), ((299 : ℚ) / 320)⟩

theorem checked9_31 :
    LRCompactVLeafParameters.check subbox9_31 .long = true := by decide +kernel

theorem subsound9_31 : LRCompactVBoxSound subbox9_31 :=
  LRCompactVLeafParameters.sound checked9_31


def subbox9_32 : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((3 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((299 : ℚ) / 320), ((151 : ℚ) / 160)⟩

theorem checked9_32 :
    LRCompactVLeafParameters.check subbox9_32 .long = true := by decide +kernel

theorem subsound9_32 : LRCompactVBoxSound subbox9_32 :=
  LRCompactVLeafParameters.sound checked9_32


def subbox9_33 : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((7 : ℚ) / 32), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((37 : ℚ) / 40), ((299 : ℚ) / 320)⟩

theorem checked9_33 :
    LRCompactVLeafParameters.check subbox9_33 .short = true := by decide +kernel

theorem subsound9_33 : LRCompactVBoxSound subbox9_33 :=
  LRCompactVLeafParameters.sound checked9_33


def subbox9_34 : CertificateBox :=
  ⟨((7 : ℚ) / 32), ((1 : ℚ) / 4), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((37 : ℚ) / 40), ((299 : ℚ) / 320)⟩

theorem checked9_34 :
    LRCompactVLeafParameters.check subbox9_34 .short = true := by decide +kernel

theorem subsound9_34 : LRCompactVBoxSound subbox9_34 :=
  LRCompactVLeafParameters.sound checked9_34


def subbox9_35 : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((1 : ℚ) / 4), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((299 : ℚ) / 320), ((151 : ℚ) / 160)⟩

theorem checked9_35 :
    LRCompactVLeafParameters.check subbox9_35 .long = true := by decide +kernel

theorem subsound9_35 : LRCompactVBoxSound subbox9_35 :=
  LRCompactVLeafParameters.sound checked9_35


def subbox9_36 : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((7 : ℚ) / 32), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((37 : ℚ) / 40), ((299 : ℚ) / 320)⟩

theorem checked9_36 :
    LRCompactVLeafParameters.check subbox9_36 .short = true := by decide +kernel

theorem subsound9_36 : LRCompactVBoxSound subbox9_36 :=
  LRCompactVLeafParameters.sound checked9_36


def subbox9_37 : CertificateBox :=
  ⟨((7 : ℚ) / 32), ((1 : ℚ) / 4), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((37 : ℚ) / 40), ((299 : ℚ) / 320)⟩

theorem checked9_37 :
    LRCompactVLeafParameters.check subbox9_37 .short = true := by decide +kernel

theorem subsound9_37 : LRCompactVBoxSound subbox9_37 :=
  LRCompactVLeafParameters.sound checked9_37


def subbox9_38 : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((7 : ℚ) / 32), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((299 : ℚ) / 320), ((151 : ℚ) / 160)⟩

theorem checked9_38 :
    LRCompactVLeafParameters.check subbox9_38 .short = true := by decide +kernel

theorem subsound9_38 : LRCompactVBoxSound subbox9_38 :=
  LRCompactVLeafParameters.sound checked9_38


def subbox9_39 : CertificateBox :=
  ⟨((7 : ℚ) / 32), ((1 : ℚ) / 4), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((299 : ℚ) / 320), ((151 : ℚ) / 160)⟩

theorem checked9_39 :
    LRCompactVLeafParameters.check subbox9_39 .short = true := by decide +kernel

theorem subsound9_39 : LRCompactVBoxSound subbox9_39 :=
  LRCompactVLeafParameters.sound checked9_39


def subbox9_40 : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((3 : ℚ) / 16), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((151 : ℚ) / 160), ((61 : ℚ) / 64)⟩

theorem checked9_40 :
    LRCompactVLeafParameters.check subbox9_40 .short = true := by decide +kernel

theorem subsound9_40 : LRCompactVBoxSound subbox9_40 :=
  LRCompactVLeafParameters.sound checked9_40


def subbox9_41 : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((3 : ℚ) / 16), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((61 : ℚ) / 64), ((77 : ℚ) / 80)⟩

theorem checked9_41 :
    LRCompactVLeafParameters.check subbox9_41 .short = true := by decide +kernel

theorem subsound9_41 : LRCompactVBoxSound subbox9_41 :=
  LRCompactVLeafParameters.sound checked9_41


def subbox9_42 : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((3 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((151 : ℚ) / 160), ((61 : ℚ) / 64)⟩

theorem checked9_42 :
    LRCompactVLeafParameters.check subbox9_42 .long = true := by decide +kernel

theorem subsound9_42 : LRCompactVBoxSound subbox9_42 :=
  LRCompactVLeafParameters.sound checked9_42


def subbox9_43 : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((3 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((61 : ℚ) / 64), ((77 : ℚ) / 80)⟩

theorem checked9_43 :
    LRCompactVLeafParameters.check subbox9_43 .long = true := by decide +kernel

theorem subsound9_43 : LRCompactVBoxSound subbox9_43 :=
  LRCompactVLeafParameters.sound checked9_43


def subbox9_44 : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((1 : ℚ) / 4), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((151 : ℚ) / 160), ((61 : ℚ) / 64)⟩

theorem checked9_44 :
    LRCompactVLeafParameters.check subbox9_44 .long = true := by decide +kernel

theorem subsound9_44 : LRCompactVBoxSound subbox9_44 :=
  LRCompactVLeafParameters.sound checked9_44


def subbox9_45 : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((1 : ℚ) / 4), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((61 : ℚ) / 64), ((77 : ℚ) / 80)⟩

theorem checked9_45 :
    LRCompactVLeafParameters.check subbox9_45 .long = true := by decide +kernel

theorem subsound9_45 : LRCompactVBoxSound subbox9_45 :=
  LRCompactVLeafParameters.sound checked9_45


def subbox9_46 : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((7 : ℚ) / 32), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((151 : ℚ) / 160), ((61 : ℚ) / 64)⟩

theorem checked9_46 :
    LRCompactVLeafParameters.check subbox9_46 .short = true := by decide +kernel

theorem subsound9_46 : LRCompactVBoxSound subbox9_46 :=
  LRCompactVLeafParameters.sound checked9_46


def subbox9_47 : CertificateBox :=
  ⟨((7 : ℚ) / 32), ((1 : ℚ) / 4), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((151 : ℚ) / 160), ((61 : ℚ) / 64)⟩

theorem checked9_47 :
    LRCompactVLeafParameters.check subbox9_47 .short = true := by decide +kernel

theorem subsound9_47 : LRCompactVBoxSound subbox9_47 :=
  LRCompactVLeafParameters.sound checked9_47


def subbox9_48 : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((7 : ℚ) / 32), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((61 : ℚ) / 64), ((77 : ℚ) / 80)⟩

theorem checked9_48 :
    LRCompactVLeafParameters.check subbox9_48 .short = true := by decide +kernel

theorem subsound9_48 : LRCompactVBoxSound subbox9_48 :=
  LRCompactVLeafParameters.sound checked9_48


def subbox9_49 : CertificateBox :=
  ⟨((7 : ℚ) / 32), ((1 : ℚ) / 4), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((61 : ℚ) / 64), ((77 : ℚ) / 80)⟩

theorem checked9_49 :
    LRCompactVLeafParameters.check subbox9_49 .short = true := by decide +kernel

theorem subsound9_49 : LRCompactVBoxSound subbox9_49 :=
  LRCompactVLeafParameters.sound checked9_49


def subbox9_50 : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((5 : ℚ) / 32), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((37 : ℚ) / 40), ((299 : ℚ) / 320)⟩

theorem checked9_50 :
    LRCompactVLeafParameters.check subbox9_50 .short = true := by decide +kernel

theorem subsound9_50 : LRCompactVBoxSound subbox9_50 :=
  LRCompactVLeafParameters.sound checked9_50


def subbox9_51 : CertificateBox :=
  ⟨((5 : ℚ) / 32), ((3 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((37 : ℚ) / 40), ((299 : ℚ) / 320)⟩

theorem checked9_51 :
    LRCompactVLeafParameters.check subbox9_51 .short = true := by decide +kernel

theorem subsound9_51 : LRCompactVBoxSound subbox9_51 :=
  LRCompactVLeafParameters.sound checked9_51


def subbox9_52 : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((5 : ℚ) / 32), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((299 : ℚ) / 320), ((151 : ℚ) / 160)⟩

theorem checked9_52 :
    LRCompactVLeafParameters.check subbox9_52 .short = true := by decide +kernel

theorem subsound9_52 : LRCompactVBoxSound subbox9_52 :=
  LRCompactVLeafParameters.sound checked9_52


def subbox9_53 : CertificateBox :=
  ⟨((5 : ℚ) / 32), ((3 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((299 : ℚ) / 320), ((151 : ℚ) / 160)⟩

theorem checked9_53 :
    LRCompactVLeafParameters.check subbox9_53 .short = true := by decide +kernel

theorem subsound9_53 : LRCompactVBoxSound subbox9_53 :=
  LRCompactVLeafParameters.sound checked9_53


def subbox9_54 : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((5 : ℚ) / 32), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((37 : ℚ) / 40), ((299 : ℚ) / 320)⟩

theorem checked9_54 :
    LRCompactVLeafParameters.check subbox9_54 .short = true := by decide +kernel

theorem subsound9_54 : LRCompactVBoxSound subbox9_54 :=
  LRCompactVLeafParameters.sound checked9_54


def subbox9_55 : CertificateBox :=
  ⟨((5 : ℚ) / 32), ((3 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((37 : ℚ) / 40), ((299 : ℚ) / 320)⟩

theorem checked9_55 :
    LRCompactVLeafParameters.check subbox9_55 .short = true := by decide +kernel

theorem subsound9_55 : LRCompactVBoxSound subbox9_55 :=
  LRCompactVLeafParameters.sound checked9_55


def subbox9_56 : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((5 : ℚ) / 32), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((299 : ℚ) / 320), ((151 : ℚ) / 160)⟩

theorem checked9_56 :
    LRCompactVLeafParameters.check subbox9_56 .short = true := by decide +kernel

theorem subsound9_56 : LRCompactVBoxSound subbox9_56 :=
  LRCompactVLeafParameters.sound checked9_56


def subbox9_57 : CertificateBox :=
  ⟨((5 : ℚ) / 32), ((3 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((299 : ℚ) / 320), ((151 : ℚ) / 160)⟩

theorem checked9_57 :
    LRCompactVLeafParameters.check subbox9_57 .short = true := by decide +kernel

theorem subsound9_57 : LRCompactVBoxSound subbox9_57 :=
  LRCompactVLeafParameters.sound checked9_57


def subbox9_58 : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((7 : ℚ) / 32), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((37 : ℚ) / 40), ((299 : ℚ) / 320)⟩

theorem checked9_58 :
    LRCompactVLeafParameters.check subbox9_58 .short = true := by decide +kernel

theorem subsound9_58 : LRCompactVBoxSound subbox9_58 :=
  LRCompactVLeafParameters.sound checked9_58


def subbox9_59 : CertificateBox :=
  ⟨((7 : ℚ) / 32), ((1 : ℚ) / 4), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((37 : ℚ) / 40), ((299 : ℚ) / 320)⟩

theorem checked9_59 :
    LRCompactVLeafParameters.check subbox9_59 .short = true := by decide +kernel

theorem subsound9_59 : LRCompactVBoxSound subbox9_59 :=
  LRCompactVLeafParameters.sound checked9_59


def subbox9_60 : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((7 : ℚ) / 32), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((299 : ℚ) / 320), ((151 : ℚ) / 160)⟩

theorem checked9_60 :
    LRCompactVLeafParameters.check subbox9_60 .short = true := by decide +kernel

theorem subsound9_60 : LRCompactVBoxSound subbox9_60 :=
  LRCompactVLeafParameters.sound checked9_60


def subbox9_61 : CertificateBox :=
  ⟨((7 : ℚ) / 32), ((1 : ℚ) / 4), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((299 : ℚ) / 320), ((151 : ℚ) / 160)⟩

theorem checked9_61 :
    LRCompactVLeafParameters.check subbox9_61 .short = true := by decide +kernel

theorem subsound9_61 : LRCompactVBoxSound subbox9_61 :=
  LRCompactVLeafParameters.sound checked9_61


def subbox9_62 : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((7 : ℚ) / 32), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((37 : ℚ) / 40), ((299 : ℚ) / 320)⟩

theorem checked9_62 :
    LRCompactVLeafParameters.check subbox9_62 .short = true := by decide +kernel

theorem subsound9_62 : LRCompactVBoxSound subbox9_62 :=
  LRCompactVLeafParameters.sound checked9_62


def subbox9_63 : CertificateBox :=
  ⟨((7 : ℚ) / 32), ((1 : ℚ) / 4), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((37 : ℚ) / 40), ((299 : ℚ) / 320)⟩

theorem checked9_63 :
    LRCompactVLeafParameters.check subbox9_63 .long = true := by decide +kernel

theorem subsound9_63 : LRCompactVBoxSound subbox9_63 :=
  LRCompactVLeafParameters.sound checked9_63


def subbox9_64 : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((7 : ℚ) / 32), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((299 : ℚ) / 320), ((151 : ℚ) / 160)⟩

theorem checked9_64 :
    LRCompactVLeafParameters.check subbox9_64 .short = true := by decide +kernel

theorem subsound9_64 : LRCompactVBoxSound subbox9_64 :=
  LRCompactVLeafParameters.sound checked9_64


def subbox9_65 : CertificateBox :=
  ⟨((7 : ℚ) / 32), ((1 : ℚ) / 4), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((299 : ℚ) / 320), ((151 : ℚ) / 160)⟩

theorem checked9_65 :
    LRCompactVLeafParameters.check subbox9_65 .long = true := by decide +kernel

theorem subsound9_65 : LRCompactVBoxSound subbox9_65 :=
  LRCompactVLeafParameters.sound checked9_65


def subbox9_66 : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((5 : ℚ) / 32), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((151 : ℚ) / 160), ((61 : ℚ) / 64)⟩

theorem checked9_66 :
    LRCompactVLeafParameters.check subbox9_66 .short = true := by decide +kernel

theorem subsound9_66 : LRCompactVBoxSound subbox9_66 :=
  LRCompactVLeafParameters.sound checked9_66


def subbox9_67 : CertificateBox :=
  ⟨((5 : ℚ) / 32), ((3 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((151 : ℚ) / 160), ((61 : ℚ) / 64)⟩

theorem checked9_67 :
    LRCompactVLeafParameters.check subbox9_67 .short = true := by decide +kernel

theorem subsound9_67 : LRCompactVBoxSound subbox9_67 :=
  LRCompactVLeafParameters.sound checked9_67


def subbox9_68 : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((3 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((61 : ℚ) / 64), ((77 : ℚ) / 80)⟩

theorem checked9_68 :
    LRCompactVLeafParameters.check subbox9_68 .long = true := by decide +kernel

theorem subsound9_68 : LRCompactVBoxSound subbox9_68 :=
  LRCompactVLeafParameters.sound checked9_68


def subbox9_69 : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((5 : ℚ) / 32), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((151 : ℚ) / 160), ((61 : ℚ) / 64)⟩

theorem checked9_69 :
    LRCompactVLeafParameters.check subbox9_69 .short = true := by decide +kernel

theorem subsound9_69 : LRCompactVBoxSound subbox9_69 :=
  LRCompactVLeafParameters.sound checked9_69


def subbox9_70 : CertificateBox :=
  ⟨((5 : ℚ) / 32), ((3 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((151 : ℚ) / 160), ((61 : ℚ) / 64)⟩

theorem checked9_70 :
    LRCompactVLeafParameters.check subbox9_70 .short = true := by decide +kernel

theorem subsound9_70 : LRCompactVBoxSound subbox9_70 :=
  LRCompactVLeafParameters.sound checked9_70


def subbox9_71 : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((5 : ℚ) / 32), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((61 : ℚ) / 64), ((77 : ℚ) / 80)⟩

theorem checked9_71 :
    LRCompactVLeafParameters.check subbox9_71 .short = true := by decide +kernel

theorem subsound9_71 : LRCompactVBoxSound subbox9_71 :=
  LRCompactVLeafParameters.sound checked9_71


def subbox9_72 : CertificateBox :=
  ⟨((5 : ℚ) / 32), ((3 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((61 : ℚ) / 64), ((77 : ℚ) / 80)⟩

theorem checked9_72 :
    LRCompactVLeafParameters.check subbox9_72 .short = true := by decide +kernel

theorem subsound9_72 : LRCompactVBoxSound subbox9_72 :=
  LRCompactVLeafParameters.sound checked9_72


def subbox9_73 : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((7 : ℚ) / 32), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((151 : ℚ) / 160), ((61 : ℚ) / 64)⟩

theorem checked9_73 :
    LRCompactVLeafParameters.check subbox9_73 .short = true := by decide +kernel

theorem subsound9_73 : LRCompactVBoxSound subbox9_73 :=
  LRCompactVLeafParameters.sound checked9_73


def subbox9_74 : CertificateBox :=
  ⟨((7 : ℚ) / 32), ((1 : ℚ) / 4), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((151 : ℚ) / 160), ((61 : ℚ) / 64)⟩

theorem checked9_74 :
    LRCompactVLeafParameters.check subbox9_74 .short = true := by decide +kernel

theorem subsound9_74 : LRCompactVBoxSound subbox9_74 :=
  LRCompactVLeafParameters.sound checked9_74


def subbox9_75 : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((7 : ℚ) / 32), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((61 : ℚ) / 64), ((77 : ℚ) / 80)⟩

theorem checked9_75 :
    LRCompactVLeafParameters.check subbox9_75 .short = true := by decide +kernel

theorem subsound9_75 : LRCompactVBoxSound subbox9_75 :=
  LRCompactVLeafParameters.sound checked9_75


def subbox9_76 : CertificateBox :=
  ⟨((7 : ℚ) / 32), ((1 : ℚ) / 4), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((61 : ℚ) / 64), ((77 : ℚ) / 80)⟩

theorem checked9_76 :
    LRCompactVLeafParameters.check subbox9_76 .short = true := by decide +kernel

theorem subsound9_76 : LRCompactVBoxSound subbox9_76 :=
  LRCompactVLeafParameters.sound checked9_76


def subbox9_77 : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((7 : ℚ) / 32), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((151 : ℚ) / 160), ((61 : ℚ) / 64)⟩

theorem checked9_77 :
    LRCompactVLeafParameters.check subbox9_77 .short = true := by decide +kernel

theorem subsound9_77 : LRCompactVBoxSound subbox9_77 :=
  LRCompactVLeafParameters.sound checked9_77


def subbox9_78 : CertificateBox :=
  ⟨((7 : ℚ) / 32), ((1 : ℚ) / 4), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((151 : ℚ) / 160), ((61 : ℚ) / 64)⟩

theorem checked9_78 :
    LRCompactVLeafParameters.check subbox9_78 .long = true := by decide +kernel

theorem subsound9_78 : LRCompactVBoxSound subbox9_78 :=
  LRCompactVLeafParameters.sound checked9_78


def subbox9_79 : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((7 : ℚ) / 32), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((61 : ℚ) / 64), ((77 : ℚ) / 80)⟩

theorem checked9_79 :
    LRCompactVLeafParameters.check subbox9_79 .short = true := by decide +kernel

theorem subsound9_79 : LRCompactVBoxSound subbox9_79 :=
  LRCompactVLeafParameters.sound checked9_79


def subbox9_80 : CertificateBox :=
  ⟨((7 : ℚ) / 32), ((1 : ℚ) / 4), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((61 : ℚ) / 64), ((77 : ℚ) / 80)⟩

theorem checked9_80 :
    LRCompactVLeafParameters.check subbox9_80 .short = true := by decide +kernel

theorem subsound9_80 : LRCompactVBoxSound subbox9_80 :=
  LRCompactVLeafParameters.sound checked9_80


def joinbox9_rRLLL : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 8), ((1 : ℚ) / 3), ((1 : ℚ) / 2), ((37 : ℚ) / 40), ((77 : ℚ) / 80)⟩


def joinbox9_rRLLLL : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 8), ((1 : ℚ) / 3), ((5 : ℚ) / 12), ((37 : ℚ) / 40), ((77 : ℚ) / 80)⟩


def joinbox9_rRLLLLL : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 8), ((1 : ℚ) / 3), ((5 : ℚ) / 12), ((37 : ℚ) / 40), ((151 : ℚ) / 160)⟩


def joinbox9_rRLLLLLL : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 16), ((1 : ℚ) / 3), ((5 : ℚ) / 12), ((37 : ℚ) / 40), ((151 : ℚ) / 160)⟩


def joinbox9_rRLLLLLR : CertificateBox :=
  ⟨((1 : ℚ) / 16), ((1 : ℚ) / 8), ((1 : ℚ) / 3), ((5 : ℚ) / 12), ((37 : ℚ) / 40), ((151 : ℚ) / 160)⟩


def joinbox9_rRLLLLLRR : CertificateBox :=
  ⟨((1 : ℚ) / 16), ((1 : ℚ) / 8), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((37 : ℚ) / 40), ((151 : ℚ) / 160)⟩


def joinbox9_rRLLLLR : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 8), ((1 : ℚ) / 3), ((5 : ℚ) / 12), ((151 : ℚ) / 160), ((77 : ℚ) / 80)⟩


def joinbox9_rRLLLLRL : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 16), ((1 : ℚ) / 3), ((5 : ℚ) / 12), ((151 : ℚ) / 160), ((77 : ℚ) / 80)⟩


def joinbox9_rRLLLLRR : CertificateBox :=
  ⟨((1 : ℚ) / 16), ((1 : ℚ) / 8), ((1 : ℚ) / 3), ((5 : ℚ) / 12), ((151 : ℚ) / 160), ((77 : ℚ) / 80)⟩


def joinbox9_rRLLLLRRR : CertificateBox :=
  ⟨((1 : ℚ) / 16), ((1 : ℚ) / 8), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((151 : ℚ) / 160), ((77 : ℚ) / 80)⟩


def joinbox9_rRLLLR : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 8), ((5 : ℚ) / 12), ((1 : ℚ) / 2), ((37 : ℚ) / 40), ((77 : ℚ) / 80)⟩


def joinbox9_rRLLLRL : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 8), ((5 : ℚ) / 12), ((1 : ℚ) / 2), ((37 : ℚ) / 40), ((151 : ℚ) / 160)⟩


def joinbox9_rRLLLRLL : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 16), ((5 : ℚ) / 12), ((1 : ℚ) / 2), ((37 : ℚ) / 40), ((151 : ℚ) / 160)⟩


def joinbox9_rRLLLRLLL : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((37 : ℚ) / 40), ((151 : ℚ) / 160)⟩


def joinbox9_rRLLLRLLR : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((37 : ℚ) / 40), ((151 : ℚ) / 160)⟩


def joinbox9_rRLLLRLR : CertificateBox :=
  ⟨((1 : ℚ) / 16), ((1 : ℚ) / 8), ((5 : ℚ) / 12), ((1 : ℚ) / 2), ((37 : ℚ) / 40), ((151 : ℚ) / 160)⟩


def joinbox9_rRLLLRLRL : CertificateBox :=
  ⟨((1 : ℚ) / 16), ((1 : ℚ) / 8), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((37 : ℚ) / 40), ((151 : ℚ) / 160)⟩


def joinbox9_rRLLLRLRR : CertificateBox :=
  ⟨((1 : ℚ) / 16), ((1 : ℚ) / 8), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((37 : ℚ) / 40), ((151 : ℚ) / 160)⟩


def joinbox9_rRLLLRLRRL : CertificateBox :=
  ⟨((1 : ℚ) / 16), ((1 : ℚ) / 8), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((37 : ℚ) / 40), ((299 : ℚ) / 320)⟩


def joinbox9_rRLLLRLRRR : CertificateBox :=
  ⟨((1 : ℚ) / 16), ((1 : ℚ) / 8), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((299 : ℚ) / 320), ((151 : ℚ) / 160)⟩


def joinbox9_rRLLLRR : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 8), ((5 : ℚ) / 12), ((1 : ℚ) / 2), ((151 : ℚ) / 160), ((77 : ℚ) / 80)⟩


def joinbox9_rRLLLRRL : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 16), ((5 : ℚ) / 12), ((1 : ℚ) / 2), ((151 : ℚ) / 160), ((77 : ℚ) / 80)⟩


def joinbox9_rRLLLRRLL : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((151 : ℚ) / 160), ((77 : ℚ) / 80)⟩


def joinbox9_rRLLLRRLR : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((151 : ℚ) / 160), ((77 : ℚ) / 80)⟩


def joinbox9_rRLLLRRR : CertificateBox :=
  ⟨((1 : ℚ) / 16), ((1 : ℚ) / 8), ((5 : ℚ) / 12), ((1 : ℚ) / 2), ((151 : ℚ) / 160), ((77 : ℚ) / 80)⟩


def joinbox9_rRLLLRRRL : CertificateBox :=
  ⟨((1 : ℚ) / 16), ((1 : ℚ) / 8), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((151 : ℚ) / 160), ((77 : ℚ) / 80)⟩


def joinbox9_rRLLLRRRR : CertificateBox :=
  ⟨((1 : ℚ) / 16), ((1 : ℚ) / 8), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((151 : ℚ) / 160), ((77 : ℚ) / 80)⟩


def joinbox9_rRLLLRRRRL : CertificateBox :=
  ⟨((1 : ℚ) / 16), ((1 : ℚ) / 8), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((151 : ℚ) / 160), ((61 : ℚ) / 64)⟩


def joinbox9_rRLLR : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((1 : ℚ) / 4), ((1 : ℚ) / 3), ((1 : ℚ) / 2), ((37 : ℚ) / 40), ((77 : ℚ) / 80)⟩


def joinbox9_rRLLRL : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((1 : ℚ) / 4), ((1 : ℚ) / 3), ((5 : ℚ) / 12), ((37 : ℚ) / 40), ((77 : ℚ) / 80)⟩


def joinbox9_rRLLRLL : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((1 : ℚ) / 4), ((1 : ℚ) / 3), ((5 : ℚ) / 12), ((37 : ℚ) / 40), ((151 : ℚ) / 160)⟩


def joinbox9_rRLLRLLL : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((3 : ℚ) / 16), ((1 : ℚ) / 3), ((5 : ℚ) / 12), ((37 : ℚ) / 40), ((151 : ℚ) / 160)⟩


def joinbox9_rRLLRLLLL : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((3 : ℚ) / 16), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((37 : ℚ) / 40), ((151 : ℚ) / 160)⟩


def joinbox9_rRLLRLLLR : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((3 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((37 : ℚ) / 40), ((151 : ℚ) / 160)⟩


def joinbox9_rRLLRLLR : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((1 : ℚ) / 4), ((1 : ℚ) / 3), ((5 : ℚ) / 12), ((37 : ℚ) / 40), ((151 : ℚ) / 160)⟩


def joinbox9_rRLLRLLRL : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((1 : ℚ) / 4), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((37 : ℚ) / 40), ((151 : ℚ) / 160)⟩


def joinbox9_rRLLRLLRLL : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((1 : ℚ) / 4), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((37 : ℚ) / 40), ((299 : ℚ) / 320)⟩


def joinbox9_rRLLRLLRR : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((1 : ℚ) / 4), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((37 : ℚ) / 40), ((151 : ℚ) / 160)⟩


def joinbox9_rRLLRLLRRL : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((1 : ℚ) / 4), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((37 : ℚ) / 40), ((299 : ℚ) / 320)⟩


def joinbox9_rRLLRLLRRR : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((1 : ℚ) / 4), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((299 : ℚ) / 320), ((151 : ℚ) / 160)⟩


def joinbox9_rRLLRLR : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((1 : ℚ) / 4), ((1 : ℚ) / 3), ((5 : ℚ) / 12), ((151 : ℚ) / 160), ((77 : ℚ) / 80)⟩


def joinbox9_rRLLRLRL : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((3 : ℚ) / 16), ((1 : ℚ) / 3), ((5 : ℚ) / 12), ((151 : ℚ) / 160), ((77 : ℚ) / 80)⟩


def joinbox9_rRLLRLRLL : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((3 : ℚ) / 16), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((151 : ℚ) / 160), ((77 : ℚ) / 80)⟩


def joinbox9_rRLLRLRLR : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((3 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((151 : ℚ) / 160), ((77 : ℚ) / 80)⟩


def joinbox9_rRLLRLRR : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((1 : ℚ) / 4), ((1 : ℚ) / 3), ((5 : ℚ) / 12), ((151 : ℚ) / 160), ((77 : ℚ) / 80)⟩


def joinbox9_rRLLRLRRL : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((1 : ℚ) / 4), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((151 : ℚ) / 160), ((77 : ℚ) / 80)⟩


def joinbox9_rRLLRLRRR : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((1 : ℚ) / 4), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((151 : ℚ) / 160), ((77 : ℚ) / 80)⟩


def joinbox9_rRLLRLRRRL : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((1 : ℚ) / 4), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((151 : ℚ) / 160), ((61 : ℚ) / 64)⟩


def joinbox9_rRLLRLRRRR : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((1 : ℚ) / 4), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((61 : ℚ) / 64), ((77 : ℚ) / 80)⟩


def joinbox9_rRLLRR : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((1 : ℚ) / 4), ((5 : ℚ) / 12), ((1 : ℚ) / 2), ((37 : ℚ) / 40), ((77 : ℚ) / 80)⟩


def joinbox9_rRLLRRL : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((1 : ℚ) / 4), ((5 : ℚ) / 12), ((1 : ℚ) / 2), ((37 : ℚ) / 40), ((151 : ℚ) / 160)⟩


def joinbox9_rRLLRRLL : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((3 : ℚ) / 16), ((5 : ℚ) / 12), ((1 : ℚ) / 2), ((37 : ℚ) / 40), ((151 : ℚ) / 160)⟩


def joinbox9_rRLLRRLLL : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((3 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((37 : ℚ) / 40), ((151 : ℚ) / 160)⟩


def joinbox9_rRLLRRLLLL : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((3 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((37 : ℚ) / 40), ((299 : ℚ) / 320)⟩


def joinbox9_rRLLRRLLLR : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((3 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((299 : ℚ) / 320), ((151 : ℚ) / 160)⟩


def joinbox9_rRLLRRLLR : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((3 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((37 : ℚ) / 40), ((151 : ℚ) / 160)⟩


def joinbox9_rRLLRRLLRL : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((3 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((37 : ℚ) / 40), ((299 : ℚ) / 320)⟩


def joinbox9_rRLLRRLLRR : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((3 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((299 : ℚ) / 320), ((151 : ℚ) / 160)⟩


def joinbox9_rRLLRRLR : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((1 : ℚ) / 4), ((5 : ℚ) / 12), ((1 : ℚ) / 2), ((37 : ℚ) / 40), ((151 : ℚ) / 160)⟩


def joinbox9_rRLLRRLRL : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((1 : ℚ) / 4), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((37 : ℚ) / 40), ((151 : ℚ) / 160)⟩


def joinbox9_rRLLRRLRLL : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((1 : ℚ) / 4), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((37 : ℚ) / 40), ((299 : ℚ) / 320)⟩


def joinbox9_rRLLRRLRLR : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((1 : ℚ) / 4), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((299 : ℚ) / 320), ((151 : ℚ) / 160)⟩


def joinbox9_rRLLRRLRR : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((1 : ℚ) / 4), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((37 : ℚ) / 40), ((151 : ℚ) / 160)⟩


def joinbox9_rRLLRRLRRL : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((1 : ℚ) / 4), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((37 : ℚ) / 40), ((299 : ℚ) / 320)⟩


def joinbox9_rRLLRRLRRR : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((1 : ℚ) / 4), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((299 : ℚ) / 320), ((151 : ℚ) / 160)⟩


def joinbox9_rRLLRRR : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((1 : ℚ) / 4), ((5 : ℚ) / 12), ((1 : ℚ) / 2), ((151 : ℚ) / 160), ((77 : ℚ) / 80)⟩


def joinbox9_rRLLRRRL : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((3 : ℚ) / 16), ((5 : ℚ) / 12), ((1 : ℚ) / 2), ((151 : ℚ) / 160), ((77 : ℚ) / 80)⟩


def joinbox9_rRLLRRRLL : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((3 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((151 : ℚ) / 160), ((77 : ℚ) / 80)⟩


def joinbox9_rRLLRRRLLL : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((3 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((151 : ℚ) / 160), ((61 : ℚ) / 64)⟩


def joinbox9_rRLLRRRLR : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((3 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((151 : ℚ) / 160), ((77 : ℚ) / 80)⟩


def joinbox9_rRLLRRRLRL : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((3 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((151 : ℚ) / 160), ((61 : ℚ) / 64)⟩


def joinbox9_rRLLRRRLRR : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((3 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((61 : ℚ) / 64), ((77 : ℚ) / 80)⟩


def joinbox9_rRLLRRRR : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((1 : ℚ) / 4), ((5 : ℚ) / 12), ((1 : ℚ) / 2), ((151 : ℚ) / 160), ((77 : ℚ) / 80)⟩


def joinbox9_rRLLRRRRL : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((1 : ℚ) / 4), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((151 : ℚ) / 160), ((77 : ℚ) / 80)⟩


def joinbox9_rRLLRRRRLL : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((1 : ℚ) / 4), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((151 : ℚ) / 160), ((61 : ℚ) / 64)⟩


def joinbox9_rRLLRRRRLR : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((1 : ℚ) / 4), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((61 : ℚ) / 64), ((77 : ℚ) / 80)⟩


def joinbox9_rRLLRRRRR : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((1 : ℚ) / 4), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((151 : ℚ) / 160), ((77 : ℚ) / 80)⟩


def joinbox9_rRLLRRRRRL : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((1 : ℚ) / 4), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((151 : ℚ) / 160), ((61 : ℚ) / 64)⟩


def joinbox9_rRLLRRRRRR : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((1 : ℚ) / 4), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((61 : ℚ) / 64), ((77 : ℚ) / 80)⟩


theorem sound9 : LRCompactVBoxSound box9 :=
  (LRCompactVBoxSound.join (box := box9) .s ((1 : ℚ) / 8)
    (LRCompactVBoxSound.join (box := joinbox9_rRLLL) .k ((5 : ℚ) / 12)
      (LRCompactVBoxSound.join (box := joinbox9_rRLLLL) .chi ((151 : ℚ) / 160)
        (LRCompactVBoxSound.join (box := joinbox9_rRLLLLL) .s ((1 : ℚ) / 16)
          (LRCompactVBoxSound.join (box := joinbox9_rRLLLLLL) .k ((3 : ℚ) / 8)
            subsound9_0
            subsound9_1)
          (LRCompactVBoxSound.join (box := joinbox9_rRLLLLLR) .k ((3 : ℚ) / 8)
            subsound9_2
            (LRCompactVBoxSound.join (box := joinbox9_rRLLLLLRR) .chi ((299 : ℚ) / 320)
              subsound9_3
              subsound9_4)))
        (LRCompactVBoxSound.join (box := joinbox9_rRLLLLR) .s ((1 : ℚ) / 16)
          (LRCompactVBoxSound.join (box := joinbox9_rRLLLLRL) .k ((3 : ℚ) / 8)
            subsound9_5
            subsound9_6)
          (LRCompactVBoxSound.join (box := joinbox9_rRLLLLRR) .k ((3 : ℚ) / 8)
            subsound9_7
            (LRCompactVBoxSound.join (box := joinbox9_rRLLLLRRR) .chi ((61 : ℚ) / 64)
              subsound9_8
              subsound9_9))))
      (LRCompactVBoxSound.join (box := joinbox9_rRLLLR) .chi ((151 : ℚ) / 160)
        (LRCompactVBoxSound.join (box := joinbox9_rRLLLRL) .s ((1 : ℚ) / 16)
          (LRCompactVBoxSound.join (box := joinbox9_rRLLLRLL) .k ((11 : ℚ) / 24)
            (LRCompactVBoxSound.join (box := joinbox9_rRLLLRLLL) .chi ((299 : ℚ) / 320)
              subsound9_10
              subsound9_11)
            (LRCompactVBoxSound.join (box := joinbox9_rRLLLRLLR) .chi ((299 : ℚ) / 320)
              subsound9_12
              subsound9_13))
          (LRCompactVBoxSound.join (box := joinbox9_rRLLLRLR) .k ((11 : ℚ) / 24)
            (LRCompactVBoxSound.join (box := joinbox9_rRLLLRLRL) .chi ((299 : ℚ) / 320)
              subsound9_14
              subsound9_15)
            (LRCompactVBoxSound.join (box := joinbox9_rRLLLRLRR) .chi ((299 : ℚ) / 320)
              (LRCompactVBoxSound.join (box := joinbox9_rRLLLRLRRL) .s ((3 : ℚ) / 32)
                subsound9_16
                subsound9_17)
              (LRCompactVBoxSound.join (box := joinbox9_rRLLLRLRRR) .s ((3 : ℚ) / 32)
                subsound9_18
                subsound9_19))))
        (LRCompactVBoxSound.join (box := joinbox9_rRLLLRR) .s ((1 : ℚ) / 16)
          (LRCompactVBoxSound.join (box := joinbox9_rRLLLRRL) .k ((11 : ℚ) / 24)
            (LRCompactVBoxSound.join (box := joinbox9_rRLLLRRLL) .chi ((61 : ℚ) / 64)
              subsound9_20
              subsound9_21)
            (LRCompactVBoxSound.join (box := joinbox9_rRLLLRRLR) .chi ((61 : ℚ) / 64)
              subsound9_22
              subsound9_23))
          (LRCompactVBoxSound.join (box := joinbox9_rRLLLRRR) .k ((11 : ℚ) / 24)
            (LRCompactVBoxSound.join (box := joinbox9_rRLLLRRRL) .chi ((61 : ℚ) / 64)
              subsound9_24
              subsound9_25)
            (LRCompactVBoxSound.join (box := joinbox9_rRLLLRRRR) .chi ((61 : ℚ) / 64)
              (LRCompactVBoxSound.join (box := joinbox9_rRLLLRRRRL) .s ((3 : ℚ) / 32)
                subsound9_26
                subsound9_27)
              subsound9_28)))))
    (LRCompactVBoxSound.join (box := joinbox9_rRLLR) .k ((5 : ℚ) / 12)
      (LRCompactVBoxSound.join (box := joinbox9_rRLLRL) .chi ((151 : ℚ) / 160)
        (LRCompactVBoxSound.join (box := joinbox9_rRLLRLL) .s ((3 : ℚ) / 16)
          (LRCompactVBoxSound.join (box := joinbox9_rRLLRLLL) .k ((3 : ℚ) / 8)
            (LRCompactVBoxSound.join (box := joinbox9_rRLLRLLLL) .chi ((299 : ℚ) / 320)
              subsound9_29
              subsound9_30)
            (LRCompactVBoxSound.join (box := joinbox9_rRLLRLLLR) .chi ((299 : ℚ) / 320)
              subsound9_31
              subsound9_32))
          (LRCompactVBoxSound.join (box := joinbox9_rRLLRLLR) .k ((3 : ℚ) / 8)
            (LRCompactVBoxSound.join (box := joinbox9_rRLLRLLRL) .chi ((299 : ℚ) / 320)
              (LRCompactVBoxSound.join (box := joinbox9_rRLLRLLRLL) .s ((7 : ℚ) / 32)
                subsound9_33
                subsound9_34)
              subsound9_35)
            (LRCompactVBoxSound.join (box := joinbox9_rRLLRLLRR) .chi ((299 : ℚ) / 320)
              (LRCompactVBoxSound.join (box := joinbox9_rRLLRLLRRL) .s ((7 : ℚ) / 32)
                subsound9_36
                subsound9_37)
              (LRCompactVBoxSound.join (box := joinbox9_rRLLRLLRRR) .s ((7 : ℚ) / 32)
                subsound9_38
                subsound9_39))))
        (LRCompactVBoxSound.join (box := joinbox9_rRLLRLR) .s ((3 : ℚ) / 16)
          (LRCompactVBoxSound.join (box := joinbox9_rRLLRLRL) .k ((3 : ℚ) / 8)
            (LRCompactVBoxSound.join (box := joinbox9_rRLLRLRLL) .chi ((61 : ℚ) / 64)
              subsound9_40
              subsound9_41)
            (LRCompactVBoxSound.join (box := joinbox9_rRLLRLRLR) .chi ((61 : ℚ) / 64)
              subsound9_42
              subsound9_43))
          (LRCompactVBoxSound.join (box := joinbox9_rRLLRLRR) .k ((3 : ℚ) / 8)
            (LRCompactVBoxSound.join (box := joinbox9_rRLLRLRRL) .chi ((61 : ℚ) / 64)
              subsound9_44
              subsound9_45)
            (LRCompactVBoxSound.join (box := joinbox9_rRLLRLRRR) .chi ((61 : ℚ) / 64)
              (LRCompactVBoxSound.join (box := joinbox9_rRLLRLRRRL) .s ((7 : ℚ) / 32)
                subsound9_46
                subsound9_47)
              (LRCompactVBoxSound.join (box := joinbox9_rRLLRLRRRR) .s ((7 : ℚ) / 32)
                subsound9_48
                subsound9_49)))))
      (LRCompactVBoxSound.join (box := joinbox9_rRLLRR) .chi ((151 : ℚ) / 160)
        (LRCompactVBoxSound.join (box := joinbox9_rRLLRRL) .s ((3 : ℚ) / 16)
          (LRCompactVBoxSound.join (box := joinbox9_rRLLRRLL) .k ((11 : ℚ) / 24)
            (LRCompactVBoxSound.join (box := joinbox9_rRLLRRLLL) .chi ((299 : ℚ) / 320)
              (LRCompactVBoxSound.join (box := joinbox9_rRLLRRLLLL) .s ((5 : ℚ) / 32)
                subsound9_50
                subsound9_51)
              (LRCompactVBoxSound.join (box := joinbox9_rRLLRRLLLR) .s ((5 : ℚ) / 32)
                subsound9_52
                subsound9_53))
            (LRCompactVBoxSound.join (box := joinbox9_rRLLRRLLR) .chi ((299 : ℚ) / 320)
              (LRCompactVBoxSound.join (box := joinbox9_rRLLRRLLRL) .s ((5 : ℚ) / 32)
                subsound9_54
                subsound9_55)
              (LRCompactVBoxSound.join (box := joinbox9_rRLLRRLLRR) .s ((5 : ℚ) / 32)
                subsound9_56
                subsound9_57)))
          (LRCompactVBoxSound.join (box := joinbox9_rRLLRRLR) .k ((11 : ℚ) / 24)
            (LRCompactVBoxSound.join (box := joinbox9_rRLLRRLRL) .chi ((299 : ℚ) / 320)
              (LRCompactVBoxSound.join (box := joinbox9_rRLLRRLRLL) .s ((7 : ℚ) / 32)
                subsound9_58
                subsound9_59)
              (LRCompactVBoxSound.join (box := joinbox9_rRLLRRLRLR) .s ((7 : ℚ) / 32)
                subsound9_60
                subsound9_61))
            (LRCompactVBoxSound.join (box := joinbox9_rRLLRRLRR) .chi ((299 : ℚ) / 320)
              (LRCompactVBoxSound.join (box := joinbox9_rRLLRRLRRL) .s ((7 : ℚ) / 32)
                subsound9_62
                subsound9_63)
              (LRCompactVBoxSound.join (box := joinbox9_rRLLRRLRRR) .s ((7 : ℚ) / 32)
                subsound9_64
                subsound9_65))))
        (LRCompactVBoxSound.join (box := joinbox9_rRLLRRR) .s ((3 : ℚ) / 16)
          (LRCompactVBoxSound.join (box := joinbox9_rRLLRRRL) .k ((11 : ℚ) / 24)
            (LRCompactVBoxSound.join (box := joinbox9_rRLLRRRLL) .chi ((61 : ℚ) / 64)
              (LRCompactVBoxSound.join (box := joinbox9_rRLLRRRLLL) .s ((5 : ℚ) / 32)
                subsound9_66
                subsound9_67)
              subsound9_68)
            (LRCompactVBoxSound.join (box := joinbox9_rRLLRRRLR) .chi ((61 : ℚ) / 64)
              (LRCompactVBoxSound.join (box := joinbox9_rRLLRRRLRL) .s ((5 : ℚ) / 32)
                subsound9_69
                subsound9_70)
              (LRCompactVBoxSound.join (box := joinbox9_rRLLRRRLRR) .s ((5 : ℚ) / 32)
                subsound9_71
                subsound9_72)))
          (LRCompactVBoxSound.join (box := joinbox9_rRLLRRRR) .k ((11 : ℚ) / 24)
            (LRCompactVBoxSound.join (box := joinbox9_rRLLRRRRL) .chi ((61 : ℚ) / 64)
              (LRCompactVBoxSound.join (box := joinbox9_rRLLRRRRLL) .s ((7 : ℚ) / 32)
                subsound9_73
                subsound9_74)
              (LRCompactVBoxSound.join (box := joinbox9_rRLLRRRRLR) .s ((7 : ℚ) / 32)
                subsound9_75
                subsound9_76))
            (LRCompactVBoxSound.join (box := joinbox9_rRLLRRRRR) .chi ((61 : ℚ) / 64)
              (LRCompactVBoxSound.join (box := joinbox9_rRLLRRRRRL) .s ((7 : ℚ) / 32)
                subsound9_77
                subsound9_78)
              (LRCompactVBoxSound.join (box := joinbox9_rRLLRRRRRR) .s ((7 : ℚ) / 32)
                subsound9_79
                subsound9_80)))))))

end CourtadeKumar.GeneratedLRCompactVLowR
