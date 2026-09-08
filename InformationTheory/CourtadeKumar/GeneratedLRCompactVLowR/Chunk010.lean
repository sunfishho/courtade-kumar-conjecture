import InformationTheory.CourtadeKumar.LRCompactVBasicReplay

/-! Frozen basic compact-V replay.
Plan SHA-256: ce3f7a498b2b9caf346dcf88ce7861f8cc091af8cd93f5624d7684e21322ecd5
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CourtadeKumar.GeneratedLRCompactVLowR

-- 58 accepted leaves below path rRLR.
def box10 : CertificateBox where
  sLo := (0 : ℚ)
  sHi := ((1 : ℚ) / 4)
  kLo := ((1 : ℚ) / 3)
  kHi := ((1 : ℚ) / 2)
  chiLo := ((77 : ℚ) / 80)
  chiHi := (1 : ℚ)


def subbox10_0 : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 16), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((77 : ℚ) / 80), ((157 : ℚ) / 160)⟩

theorem checked10_0 :
    LRCompactVLeafParameters.check subbox10_0 .short = true := by decide +kernel

theorem subsound10_0 : LRCompactVBoxSound subbox10_0 :=
  LRCompactVLeafParameters.sound checked10_0


def subbox10_1 : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((77 : ℚ) / 80), ((157 : ℚ) / 160)⟩

theorem checked10_1 :
    LRCompactVLeafParameters.check subbox10_1 .short = true := by decide +kernel

theorem subsound10_1 : LRCompactVBoxSound subbox10_1 :=
  LRCompactVLeafParameters.sound checked10_1


def subbox10_2 : CertificateBox :=
  ⟨((1 : ℚ) / 16), ((1 : ℚ) / 8), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((77 : ℚ) / 80), ((157 : ℚ) / 160)⟩

theorem checked10_2 :
    LRCompactVLeafParameters.check subbox10_2 .short = true := by decide +kernel

theorem subsound10_2 : LRCompactVBoxSound subbox10_2 :=
  LRCompactVLeafParameters.sound checked10_2


def subbox10_3 : CertificateBox :=
  ⟨((1 : ℚ) / 16), ((1 : ℚ) / 8), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((77 : ℚ) / 80), ((157 : ℚ) / 160)⟩

theorem checked10_3 :
    LRCompactVLeafParameters.check subbox10_3 .long = true := by decide +kernel

theorem subsound10_3 : LRCompactVBoxSound subbox10_3 :=
  LRCompactVLeafParameters.sound checked10_3


def subbox10_4 : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 16), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((157 : ℚ) / 160), (1 : ℚ)⟩

theorem checked10_4 :
    LRCompactVLeafParameters.check subbox10_4 .short = true := by decide +kernel

theorem subsound10_4 : LRCompactVBoxSound subbox10_4 :=
  LRCompactVLeafParameters.sound checked10_4


def subbox10_5 : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((157 : ℚ) / 160), (1 : ℚ)⟩

theorem checked10_5 :
    LRCompactVLeafParameters.check subbox10_5 .short = true := by decide +kernel

theorem subsound10_5 : LRCompactVBoxSound subbox10_5 :=
  LRCompactVLeafParameters.sound checked10_5


def subbox10_6 : CertificateBox :=
  ⟨((1 : ℚ) / 16), ((1 : ℚ) / 8), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((157 : ℚ) / 160), (1 : ℚ)⟩

theorem checked10_6 :
    LRCompactVLeafParameters.check subbox10_6 .short = true := by decide +kernel

theorem subsound10_6 : LRCompactVBoxSound subbox10_6 :=
  LRCompactVLeafParameters.sound checked10_6


def subbox10_7 : CertificateBox :=
  ⟨((1 : ℚ) / 16), ((1 : ℚ) / 8), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((157 : ℚ) / 160), (1 : ℚ)⟩

theorem checked10_7 :
    LRCompactVLeafParameters.check subbox10_7 .short = true := by decide +kernel

theorem subsound10_7 : LRCompactVBoxSound subbox10_7 :=
  LRCompactVLeafParameters.sound checked10_7


def subbox10_8 : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((77 : ℚ) / 80), ((157 : ℚ) / 160)⟩

theorem checked10_8 :
    LRCompactVLeafParameters.check subbox10_8 .long = true := by decide +kernel

theorem subsound10_8 : LRCompactVBoxSound subbox10_8 :=
  LRCompactVLeafParameters.sound checked10_8


def subbox10_9 : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((77 : ℚ) / 80), ((311 : ℚ) / 320)⟩

theorem checked10_9 :
    LRCompactVLeafParameters.check subbox10_9 .short = true := by decide +kernel

theorem subsound10_9 : LRCompactVBoxSound subbox10_9 :=
  LRCompactVLeafParameters.sound checked10_9


def subbox10_10 : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((311 : ℚ) / 320), ((157 : ℚ) / 160)⟩

theorem checked10_10 :
    LRCompactVLeafParameters.check subbox10_10 .short = true := by decide +kernel

theorem subsound10_10 : LRCompactVBoxSound subbox10_10 :=
  LRCompactVLeafParameters.sound checked10_10


def subbox10_11 : CertificateBox :=
  ⟨((1 : ℚ) / 16), ((1 : ℚ) / 8), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((77 : ℚ) / 80), ((311 : ℚ) / 320)⟩

theorem checked10_11 :
    LRCompactVLeafParameters.check subbox10_11 .short = true := by decide +kernel

theorem subsound10_11 : LRCompactVBoxSound subbox10_11 :=
  LRCompactVLeafParameters.sound checked10_11


def subbox10_12 : CertificateBox :=
  ⟨((1 : ℚ) / 16), ((1 : ℚ) / 8), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((311 : ℚ) / 320), ((157 : ℚ) / 160)⟩

theorem checked10_12 :
    LRCompactVLeafParameters.check subbox10_12 .short = true := by decide +kernel

theorem subsound10_12 : LRCompactVBoxSound subbox10_12 :=
  LRCompactVLeafParameters.sound checked10_12


def subbox10_13 : CertificateBox :=
  ⟨((1 : ℚ) / 16), ((1 : ℚ) / 8), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((77 : ℚ) / 80), ((311 : ℚ) / 320)⟩

theorem checked10_13 :
    LRCompactVLeafParameters.check subbox10_13 .long = true := by decide +kernel

theorem subsound10_13 : LRCompactVBoxSound subbox10_13 :=
  LRCompactVLeafParameters.sound checked10_13


def subbox10_14 : CertificateBox :=
  ⟨((1 : ℚ) / 16), ((1 : ℚ) / 8), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((311 : ℚ) / 320), ((157 : ℚ) / 160)⟩

theorem checked10_14 :
    LRCompactVLeafParameters.check subbox10_14 .long = true := by decide +kernel

theorem subsound10_14 : LRCompactVBoxSound subbox10_14 :=
  LRCompactVLeafParameters.sound checked10_14


def subbox10_15 : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((157 : ℚ) / 160), (1 : ℚ)⟩

theorem checked10_15 :
    LRCompactVLeafParameters.check subbox10_15 .accurateLog = true := by decide +kernel

theorem subsound10_15 : LRCompactVBoxSound subbox10_15 :=
  LRCompactVLeafParameters.sound checked10_15


def subbox10_16 : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((157 : ℚ) / 160), (1 : ℚ)⟩

theorem checked10_16 :
    LRCompactVLeafParameters.check subbox10_16 .long = true := by decide +kernel

theorem subsound10_16 : LRCompactVBoxSound subbox10_16 :=
  LRCompactVLeafParameters.sound checked10_16


def subbox10_17 : CertificateBox :=
  ⟨((1 : ℚ) / 16), ((1 : ℚ) / 8), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((157 : ℚ) / 160), (1 : ℚ)⟩

theorem checked10_17 :
    LRCompactVLeafParameters.check subbox10_17 .long = true := by decide +kernel

theorem subsound10_17 : LRCompactVBoxSound subbox10_17 :=
  LRCompactVLeafParameters.sound checked10_17


def subbox10_18 : CertificateBox :=
  ⟨((1 : ℚ) / 16), ((1 : ℚ) / 8), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((157 : ℚ) / 160), ((317 : ℚ) / 320)⟩

theorem checked10_18 :
    LRCompactVLeafParameters.check subbox10_18 .long = true := by decide +kernel

theorem subsound10_18 : LRCompactVBoxSound subbox10_18 :=
  LRCompactVLeafParameters.sound checked10_18


def subbox10_19 : CertificateBox :=
  ⟨((1 : ℚ) / 16), ((1 : ℚ) / 8), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((317 : ℚ) / 320), (1 : ℚ)⟩

theorem checked10_19 :
    LRCompactVLeafParameters.check subbox10_19 .long = true := by decide +kernel

theorem subsound10_19 : LRCompactVBoxSound subbox10_19 :=
  LRCompactVLeafParameters.sound checked10_19


def subbox10_20 : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((3 : ℚ) / 16), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((77 : ℚ) / 80), ((157 : ℚ) / 160)⟩

theorem checked10_20 :
    LRCompactVLeafParameters.check subbox10_20 .long = true := by decide +kernel

theorem subsound10_20 : LRCompactVBoxSound subbox10_20 :=
  LRCompactVLeafParameters.sound checked10_20


def subbox10_21 : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((3 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((77 : ℚ) / 80), ((311 : ℚ) / 320)⟩

theorem checked10_21 :
    LRCompactVLeafParameters.check subbox10_21 .short = true := by decide +kernel

theorem subsound10_21 : LRCompactVBoxSound subbox10_21 :=
  LRCompactVLeafParameters.sound checked10_21


def subbox10_22 : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((3 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((311 : ℚ) / 320), ((157 : ℚ) / 160)⟩

theorem checked10_22 :
    LRCompactVLeafParameters.check subbox10_22 .short = true := by decide +kernel

theorem subsound10_22 : LRCompactVBoxSound subbox10_22 :=
  LRCompactVLeafParameters.sound checked10_22


def subbox10_23 : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((1 : ℚ) / 4), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((77 : ℚ) / 80), ((311 : ℚ) / 320)⟩

theorem checked10_23 :
    LRCompactVLeafParameters.check subbox10_23 .short = true := by decide +kernel

theorem subsound10_23 : LRCompactVBoxSound subbox10_23 :=
  LRCompactVLeafParameters.sound checked10_23


def subbox10_24 : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((1 : ℚ) / 4), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((311 : ℚ) / 320), ((157 : ℚ) / 160)⟩

theorem checked10_24 :
    LRCompactVLeafParameters.check subbox10_24 .short = true := by decide +kernel

theorem subsound10_24 : LRCompactVBoxSound subbox10_24 :=
  LRCompactVLeafParameters.sound checked10_24


def subbox10_25 : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((1 : ℚ) / 4), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((77 : ℚ) / 80), ((311 : ℚ) / 320)⟩

theorem checked10_25 :
    LRCompactVLeafParameters.check subbox10_25 .long = true := by decide +kernel

theorem subsound10_25 : LRCompactVBoxSound subbox10_25 :=
  LRCompactVLeafParameters.sound checked10_25


def subbox10_26 : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((1 : ℚ) / 4), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((311 : ℚ) / 320), ((157 : ℚ) / 160)⟩

theorem checked10_26 :
    LRCompactVLeafParameters.check subbox10_26 .long = true := by decide +kernel

theorem subsound10_26 : LRCompactVBoxSound subbox10_26 :=
  LRCompactVLeafParameters.sound checked10_26


def subbox10_27 : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((3 : ℚ) / 16), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((157 : ℚ) / 160), (1 : ℚ)⟩

theorem checked10_27 :
    LRCompactVLeafParameters.check subbox10_27 .short = true := by decide +kernel

theorem subsound10_27 : LRCompactVBoxSound subbox10_27 :=
  LRCompactVLeafParameters.sound checked10_27


def subbox10_28 : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((3 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((157 : ℚ) / 160), (1 : ℚ)⟩

theorem checked10_28 :
    LRCompactVLeafParameters.check subbox10_28 .long = true := by decide +kernel

theorem subsound10_28 : LRCompactVBoxSound subbox10_28 :=
  LRCompactVLeafParameters.sound checked10_28


def subbox10_29 : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((1 : ℚ) / 4), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((157 : ℚ) / 160), (1 : ℚ)⟩

theorem checked10_29 :
    LRCompactVLeafParameters.check subbox10_29 .long = true := by decide +kernel

theorem subsound10_29 : LRCompactVBoxSound subbox10_29 :=
  LRCompactVLeafParameters.sound checked10_29


def subbox10_30 : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((1 : ℚ) / 4), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((157 : ℚ) / 160), ((317 : ℚ) / 320)⟩

theorem checked10_30 :
    LRCompactVLeafParameters.check subbox10_30 .long = true := by decide +kernel

theorem subsound10_30 : LRCompactVBoxSound subbox10_30 :=
  LRCompactVLeafParameters.sound checked10_30


def subbox10_31 : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((1 : ℚ) / 4), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((317 : ℚ) / 320), (1 : ℚ)⟩

theorem checked10_31 :
    LRCompactVLeafParameters.check subbox10_31 .long = true := by decide +kernel

theorem subsound10_31 : LRCompactVBoxSound subbox10_31 :=
  LRCompactVLeafParameters.sound checked10_31


def subbox10_32 : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((3 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((77 : ℚ) / 80), ((311 : ℚ) / 320)⟩

theorem checked10_32 :
    LRCompactVLeafParameters.check subbox10_32 .long = true := by decide +kernel

theorem subsound10_32 : LRCompactVBoxSound subbox10_32 :=
  LRCompactVLeafParameters.sound checked10_32


def subbox10_33 : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((3 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((311 : ℚ) / 320), ((157 : ℚ) / 160)⟩

theorem checked10_33 :
    LRCompactVLeafParameters.check subbox10_33 .long = true := by decide +kernel

theorem subsound10_33 : LRCompactVBoxSound subbox10_33 :=
  LRCompactVLeafParameters.sound checked10_33


def subbox10_34 : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((5 : ℚ) / 32), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((77 : ℚ) / 80), ((311 : ℚ) / 320)⟩

theorem checked10_34 :
    LRCompactVLeafParameters.check subbox10_34 .short = true := by decide +kernel

theorem subsound10_34 : LRCompactVBoxSound subbox10_34 :=
  LRCompactVLeafParameters.sound checked10_34


def subbox10_35 : CertificateBox :=
  ⟨((5 : ℚ) / 32), ((3 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((77 : ℚ) / 80), ((311 : ℚ) / 320)⟩

theorem checked10_35 :
    LRCompactVLeafParameters.check subbox10_35 .short = true := by decide +kernel

theorem subsound10_35 : LRCompactVBoxSound subbox10_35 :=
  LRCompactVLeafParameters.sound checked10_35


def subbox10_36 : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((5 : ℚ) / 32), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((311 : ℚ) / 320), ((157 : ℚ) / 160)⟩

theorem checked10_36 :
    LRCompactVLeafParameters.check subbox10_36 .short = true := by decide +kernel

theorem subsound10_36 : LRCompactVBoxSound subbox10_36 :=
  LRCompactVLeafParameters.sound checked10_36


def subbox10_37 : CertificateBox :=
  ⟨((5 : ℚ) / 32), ((3 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((311 : ℚ) / 320), ((157 : ℚ) / 160)⟩

theorem checked10_37 :
    LRCompactVLeafParameters.check subbox10_37 .short = true := by decide +kernel

theorem subsound10_37 : LRCompactVBoxSound subbox10_37 :=
  LRCompactVLeafParameters.sound checked10_37


def subbox10_38 : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((7 : ℚ) / 32), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((77 : ℚ) / 80), ((311 : ℚ) / 320)⟩

theorem checked10_38 :
    LRCompactVLeafParameters.check subbox10_38 .short = true := by decide +kernel

theorem subsound10_38 : LRCompactVBoxSound subbox10_38 :=
  LRCompactVLeafParameters.sound checked10_38


def subbox10_39 : CertificateBox :=
  ⟨((7 : ℚ) / 32), ((1 : ℚ) / 4), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((77 : ℚ) / 80), ((311 : ℚ) / 320)⟩

theorem checked10_39 :
    LRCompactVLeafParameters.check subbox10_39 .short = true := by decide +kernel

theorem subsound10_39 : LRCompactVBoxSound subbox10_39 :=
  LRCompactVLeafParameters.sound checked10_39


def subbox10_40 : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((7 : ℚ) / 32), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((311 : ℚ) / 320), ((157 : ℚ) / 160)⟩

theorem checked10_40 :
    LRCompactVLeafParameters.check subbox10_40 .short = true := by decide +kernel

theorem subsound10_40 : LRCompactVBoxSound subbox10_40 :=
  LRCompactVLeafParameters.sound checked10_40


def subbox10_41 : CertificateBox :=
  ⟨((7 : ℚ) / 32), ((1 : ℚ) / 4), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((311 : ℚ) / 320), ((157 : ℚ) / 160)⟩

theorem checked10_41 :
    LRCompactVLeafParameters.check subbox10_41 .short = true := by decide +kernel

theorem subsound10_41 : LRCompactVBoxSound subbox10_41 :=
  LRCompactVLeafParameters.sound checked10_41


def subbox10_42 : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((7 : ℚ) / 32), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((77 : ℚ) / 80), ((311 : ℚ) / 320)⟩

theorem checked10_42 :
    LRCompactVLeafParameters.check subbox10_42 .short = true := by decide +kernel

theorem subsound10_42 : LRCompactVBoxSound subbox10_42 :=
  LRCompactVLeafParameters.sound checked10_42


def subbox10_43 : CertificateBox :=
  ⟨((7 : ℚ) / 32), ((1 : ℚ) / 4), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((77 : ℚ) / 80), ((311 : ℚ) / 320)⟩

theorem checked10_43 :
    LRCompactVLeafParameters.check subbox10_43 .short = true := by decide +kernel

theorem subsound10_43 : LRCompactVBoxSound subbox10_43 :=
  LRCompactVLeafParameters.sound checked10_43


def subbox10_44 : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((7 : ℚ) / 32), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((311 : ℚ) / 320), ((157 : ℚ) / 160)⟩

theorem checked10_44 :
    LRCompactVLeafParameters.check subbox10_44 .short = true := by decide +kernel

theorem subsound10_44 : LRCompactVBoxSound subbox10_44 :=
  LRCompactVLeafParameters.sound checked10_44


def subbox10_45 : CertificateBox :=
  ⟨((7 : ℚ) / 32), ((1 : ℚ) / 4), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((311 : ℚ) / 320), ((157 : ℚ) / 160)⟩

theorem checked10_45 :
    LRCompactVLeafParameters.check subbox10_45 .short = true := by decide +kernel

theorem subsound10_45 : LRCompactVBoxSound subbox10_45 :=
  LRCompactVLeafParameters.sound checked10_45


def subbox10_46 : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((3 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((157 : ℚ) / 160), ((317 : ℚ) / 320)⟩

theorem checked10_46 :
    LRCompactVLeafParameters.check subbox10_46 .long = true := by decide +kernel

theorem subsound10_46 : LRCompactVBoxSound subbox10_46 :=
  LRCompactVLeafParameters.sound checked10_46


def subbox10_47 : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((3 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((317 : ℚ) / 320), (1 : ℚ)⟩

theorem checked10_47 :
    LRCompactVLeafParameters.check subbox10_47 .long = true := by decide +kernel

theorem subsound10_47 : LRCompactVBoxSound subbox10_47 :=
  LRCompactVLeafParameters.sound checked10_47


def subbox10_48 : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((5 : ℚ) / 32), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((157 : ℚ) / 160), ((317 : ℚ) / 320)⟩

theorem checked10_48 :
    LRCompactVLeafParameters.check subbox10_48 .short = true := by decide +kernel

theorem subsound10_48 : LRCompactVBoxSound subbox10_48 :=
  LRCompactVLeafParameters.sound checked10_48


def subbox10_49 : CertificateBox :=
  ⟨((5 : ℚ) / 32), ((3 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((157 : ℚ) / 160), ((317 : ℚ) / 320)⟩

theorem checked10_49 :
    LRCompactVLeafParameters.check subbox10_49 .short = true := by decide +kernel

theorem subsound10_49 : LRCompactVBoxSound subbox10_49 :=
  LRCompactVLeafParameters.sound checked10_49


def subbox10_50 : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((3 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((317 : ℚ) / 320), (1 : ℚ)⟩

theorem checked10_50 :
    LRCompactVLeafParameters.check subbox10_50 .long = true := by decide +kernel

theorem subsound10_50 : LRCompactVBoxSound subbox10_50 :=
  LRCompactVLeafParameters.sound checked10_50


def subbox10_51 : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((7 : ℚ) / 32), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((157 : ℚ) / 160), ((317 : ℚ) / 320)⟩

theorem checked10_51 :
    LRCompactVLeafParameters.check subbox10_51 .short = true := by decide +kernel

theorem subsound10_51 : LRCompactVBoxSound subbox10_51 :=
  LRCompactVLeafParameters.sound checked10_51


def subbox10_52 : CertificateBox :=
  ⟨((7 : ℚ) / 32), ((1 : ℚ) / 4), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((157 : ℚ) / 160), ((317 : ℚ) / 320)⟩

theorem checked10_52 :
    LRCompactVLeafParameters.check subbox10_52 .short = true := by decide +kernel

theorem subsound10_52 : LRCompactVBoxSound subbox10_52 :=
  LRCompactVLeafParameters.sound checked10_52


def subbox10_53 : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((1 : ℚ) / 4), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((317 : ℚ) / 320), (1 : ℚ)⟩

theorem checked10_53 :
    LRCompactVLeafParameters.check subbox10_53 .long = true := by decide +kernel

theorem subsound10_53 : LRCompactVBoxSound subbox10_53 :=
  LRCompactVLeafParameters.sound checked10_53


def subbox10_54 : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((7 : ℚ) / 32), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((157 : ℚ) / 160), ((317 : ℚ) / 320)⟩

theorem checked10_54 :
    LRCompactVLeafParameters.check subbox10_54 .short = true := by decide +kernel

theorem subsound10_54 : LRCompactVBoxSound subbox10_54 :=
  LRCompactVLeafParameters.sound checked10_54


def subbox10_55 : CertificateBox :=
  ⟨((7 : ℚ) / 32), ((1 : ℚ) / 4), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((157 : ℚ) / 160), ((317 : ℚ) / 320)⟩

theorem checked10_55 :
    LRCompactVLeafParameters.check subbox10_55 .short = true := by decide +kernel

theorem subsound10_55 : LRCompactVBoxSound subbox10_55 :=
  LRCompactVLeafParameters.sound checked10_55


def subbox10_56 : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((7 : ℚ) / 32), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((317 : ℚ) / 320), (1 : ℚ)⟩

theorem checked10_56 :
    LRCompactVLeafParameters.check subbox10_56 .short = true := by decide +kernel

theorem subsound10_56 : LRCompactVBoxSound subbox10_56 :=
  LRCompactVLeafParameters.sound checked10_56


def subbox10_57 : CertificateBox :=
  ⟨((7 : ℚ) / 32), ((1 : ℚ) / 4), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((317 : ℚ) / 320), (1 : ℚ)⟩

theorem checked10_57 :
    LRCompactVLeafParameters.check subbox10_57 .short = true := by decide +kernel

theorem subsound10_57 : LRCompactVBoxSound subbox10_57 :=
  LRCompactVLeafParameters.sound checked10_57


def joinbox10_rRLRL : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 8), ((1 : ℚ) / 3), ((1 : ℚ) / 2), ((77 : ℚ) / 80), (1 : ℚ)⟩


def joinbox10_rRLRLL : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 8), ((1 : ℚ) / 3), ((5 : ℚ) / 12), ((77 : ℚ) / 80), (1 : ℚ)⟩


def joinbox10_rRLRLLL : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 8), ((1 : ℚ) / 3), ((5 : ℚ) / 12), ((77 : ℚ) / 80), ((157 : ℚ) / 160)⟩


def joinbox10_rRLRLLLL : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 16), ((1 : ℚ) / 3), ((5 : ℚ) / 12), ((77 : ℚ) / 80), ((157 : ℚ) / 160)⟩


def joinbox10_rRLRLLLR : CertificateBox :=
  ⟨((1 : ℚ) / 16), ((1 : ℚ) / 8), ((1 : ℚ) / 3), ((5 : ℚ) / 12), ((77 : ℚ) / 80), ((157 : ℚ) / 160)⟩


def joinbox10_rRLRLLR : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 8), ((1 : ℚ) / 3), ((5 : ℚ) / 12), ((157 : ℚ) / 160), (1 : ℚ)⟩


def joinbox10_rRLRLLRL : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 16), ((1 : ℚ) / 3), ((5 : ℚ) / 12), ((157 : ℚ) / 160), (1 : ℚ)⟩


def joinbox10_rRLRLLRR : CertificateBox :=
  ⟨((1 : ℚ) / 16), ((1 : ℚ) / 8), ((1 : ℚ) / 3), ((5 : ℚ) / 12), ((157 : ℚ) / 160), (1 : ℚ)⟩


def joinbox10_rRLRLR : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 8), ((5 : ℚ) / 12), ((1 : ℚ) / 2), ((77 : ℚ) / 80), (1 : ℚ)⟩


def joinbox10_rRLRLRL : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 8), ((5 : ℚ) / 12), ((1 : ℚ) / 2), ((77 : ℚ) / 80), ((157 : ℚ) / 160)⟩


def joinbox10_rRLRLRLL : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 16), ((5 : ℚ) / 12), ((1 : ℚ) / 2), ((77 : ℚ) / 80), ((157 : ℚ) / 160)⟩


def joinbox10_rRLRLRLLR : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((77 : ℚ) / 80), ((157 : ℚ) / 160)⟩


def joinbox10_rRLRLRLR : CertificateBox :=
  ⟨((1 : ℚ) / 16), ((1 : ℚ) / 8), ((5 : ℚ) / 12), ((1 : ℚ) / 2), ((77 : ℚ) / 80), ((157 : ℚ) / 160)⟩


def joinbox10_rRLRLRLRL : CertificateBox :=
  ⟨((1 : ℚ) / 16), ((1 : ℚ) / 8), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((77 : ℚ) / 80), ((157 : ℚ) / 160)⟩


def joinbox10_rRLRLRLRR : CertificateBox :=
  ⟨((1 : ℚ) / 16), ((1 : ℚ) / 8), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((77 : ℚ) / 80), ((157 : ℚ) / 160)⟩


def joinbox10_rRLRLRR : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 8), ((5 : ℚ) / 12), ((1 : ℚ) / 2), ((157 : ℚ) / 160), (1 : ℚ)⟩


def joinbox10_rRLRLRRL : CertificateBox :=
  ⟨(0 : ℚ), ((1 : ℚ) / 16), ((5 : ℚ) / 12), ((1 : ℚ) / 2), ((157 : ℚ) / 160), (1 : ℚ)⟩


def joinbox10_rRLRLRRR : CertificateBox :=
  ⟨((1 : ℚ) / 16), ((1 : ℚ) / 8), ((5 : ℚ) / 12), ((1 : ℚ) / 2), ((157 : ℚ) / 160), (1 : ℚ)⟩


def joinbox10_rRLRLRRRR : CertificateBox :=
  ⟨((1 : ℚ) / 16), ((1 : ℚ) / 8), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((157 : ℚ) / 160), (1 : ℚ)⟩


def joinbox10_rRLRR : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((1 : ℚ) / 4), ((1 : ℚ) / 3), ((1 : ℚ) / 2), ((77 : ℚ) / 80), (1 : ℚ)⟩


def joinbox10_rRLRRL : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((1 : ℚ) / 4), ((1 : ℚ) / 3), ((5 : ℚ) / 12), ((77 : ℚ) / 80), (1 : ℚ)⟩


def joinbox10_rRLRRLL : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((1 : ℚ) / 4), ((1 : ℚ) / 3), ((5 : ℚ) / 12), ((77 : ℚ) / 80), ((157 : ℚ) / 160)⟩


def joinbox10_rRLRRLLL : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((3 : ℚ) / 16), ((1 : ℚ) / 3), ((5 : ℚ) / 12), ((77 : ℚ) / 80), ((157 : ℚ) / 160)⟩


def joinbox10_rRLRRLLLR : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((3 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((77 : ℚ) / 80), ((157 : ℚ) / 160)⟩


def joinbox10_rRLRRLLR : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((1 : ℚ) / 4), ((1 : ℚ) / 3), ((5 : ℚ) / 12), ((77 : ℚ) / 80), ((157 : ℚ) / 160)⟩


def joinbox10_rRLRRLLRL : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((1 : ℚ) / 4), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((77 : ℚ) / 80), ((157 : ℚ) / 160)⟩


def joinbox10_rRLRRLLRR : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((1 : ℚ) / 4), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((77 : ℚ) / 80), ((157 : ℚ) / 160)⟩


def joinbox10_rRLRRLR : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((1 : ℚ) / 4), ((1 : ℚ) / 3), ((5 : ℚ) / 12), ((157 : ℚ) / 160), (1 : ℚ)⟩


def joinbox10_rRLRRLRL : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((3 : ℚ) / 16), ((1 : ℚ) / 3), ((5 : ℚ) / 12), ((157 : ℚ) / 160), (1 : ℚ)⟩


def joinbox10_rRLRRLRR : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((1 : ℚ) / 4), ((1 : ℚ) / 3), ((5 : ℚ) / 12), ((157 : ℚ) / 160), (1 : ℚ)⟩


def joinbox10_rRLRRLRRR : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((1 : ℚ) / 4), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((157 : ℚ) / 160), (1 : ℚ)⟩


def joinbox10_rRLRRR : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((1 : ℚ) / 4), ((5 : ℚ) / 12), ((1 : ℚ) / 2), ((77 : ℚ) / 80), (1 : ℚ)⟩


def joinbox10_rRLRRRL : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((1 : ℚ) / 4), ((5 : ℚ) / 12), ((1 : ℚ) / 2), ((77 : ℚ) / 80), ((157 : ℚ) / 160)⟩


def joinbox10_rRLRRRLL : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((3 : ℚ) / 16), ((5 : ℚ) / 12), ((1 : ℚ) / 2), ((77 : ℚ) / 80), ((157 : ℚ) / 160)⟩


def joinbox10_rRLRRRLLL : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((3 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((77 : ℚ) / 80), ((157 : ℚ) / 160)⟩


def joinbox10_rRLRRRLLR : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((3 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((77 : ℚ) / 80), ((157 : ℚ) / 160)⟩


def joinbox10_rRLRRRLLRL : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((3 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((77 : ℚ) / 80), ((311 : ℚ) / 320)⟩


def joinbox10_rRLRRRLLRR : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((3 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((311 : ℚ) / 320), ((157 : ℚ) / 160)⟩


def joinbox10_rRLRRRLR : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((1 : ℚ) / 4), ((5 : ℚ) / 12), ((1 : ℚ) / 2), ((77 : ℚ) / 80), ((157 : ℚ) / 160)⟩


def joinbox10_rRLRRRLRL : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((1 : ℚ) / 4), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((77 : ℚ) / 80), ((157 : ℚ) / 160)⟩


def joinbox10_rRLRRRLRLL : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((1 : ℚ) / 4), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((77 : ℚ) / 80), ((311 : ℚ) / 320)⟩


def joinbox10_rRLRRRLRLR : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((1 : ℚ) / 4), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((311 : ℚ) / 320), ((157 : ℚ) / 160)⟩


def joinbox10_rRLRRRLRR : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((1 : ℚ) / 4), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((77 : ℚ) / 80), ((157 : ℚ) / 160)⟩


def joinbox10_rRLRRRLRRL : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((1 : ℚ) / 4), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((77 : ℚ) / 80), ((311 : ℚ) / 320)⟩


def joinbox10_rRLRRRLRRR : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((1 : ℚ) / 4), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((311 : ℚ) / 320), ((157 : ℚ) / 160)⟩


def joinbox10_rRLRRRR : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((1 : ℚ) / 4), ((5 : ℚ) / 12), ((1 : ℚ) / 2), ((157 : ℚ) / 160), (1 : ℚ)⟩


def joinbox10_rRLRRRRL : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((3 : ℚ) / 16), ((5 : ℚ) / 12), ((1 : ℚ) / 2), ((157 : ℚ) / 160), (1 : ℚ)⟩


def joinbox10_rRLRRRRLL : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((3 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((157 : ℚ) / 160), (1 : ℚ)⟩


def joinbox10_rRLRRRRLR : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((3 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((157 : ℚ) / 160), (1 : ℚ)⟩


def joinbox10_rRLRRRRLRL : CertificateBox :=
  ⟨((1 : ℚ) / 8), ((3 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((157 : ℚ) / 160), ((317 : ℚ) / 320)⟩


def joinbox10_rRLRRRRR : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((1 : ℚ) / 4), ((5 : ℚ) / 12), ((1 : ℚ) / 2), ((157 : ℚ) / 160), (1 : ℚ)⟩


def joinbox10_rRLRRRRRL : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((1 : ℚ) / 4), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((157 : ℚ) / 160), (1 : ℚ)⟩


def joinbox10_rRLRRRRRLL : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((1 : ℚ) / 4), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((157 : ℚ) / 160), ((317 : ℚ) / 320)⟩


def joinbox10_rRLRRRRRR : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((1 : ℚ) / 4), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((157 : ℚ) / 160), (1 : ℚ)⟩


def joinbox10_rRLRRRRRRL : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((1 : ℚ) / 4), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((157 : ℚ) / 160), ((317 : ℚ) / 320)⟩


def joinbox10_rRLRRRRRRR : CertificateBox :=
  ⟨((3 : ℚ) / 16), ((1 : ℚ) / 4), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((317 : ℚ) / 320), (1 : ℚ)⟩


theorem sound10 : LRCompactVBoxSound box10 :=
  (LRCompactVBoxSound.join (box := box10) .s ((1 : ℚ) / 8)
    (LRCompactVBoxSound.join (box := joinbox10_rRLRL) .k ((5 : ℚ) / 12)
      (LRCompactVBoxSound.join (box := joinbox10_rRLRLL) .chi ((157 : ℚ) / 160)
        (LRCompactVBoxSound.join (box := joinbox10_rRLRLLL) .s ((1 : ℚ) / 16)
          (LRCompactVBoxSound.join (box := joinbox10_rRLRLLLL) .k ((3 : ℚ) / 8)
            subsound10_0
            subsound10_1)
          (LRCompactVBoxSound.join (box := joinbox10_rRLRLLLR) .k ((3 : ℚ) / 8)
            subsound10_2
            subsound10_3))
        (LRCompactVBoxSound.join (box := joinbox10_rRLRLLR) .s ((1 : ℚ) / 16)
          (LRCompactVBoxSound.join (box := joinbox10_rRLRLLRL) .k ((3 : ℚ) / 8)
            subsound10_4
            subsound10_5)
          (LRCompactVBoxSound.join (box := joinbox10_rRLRLLRR) .k ((3 : ℚ) / 8)
            subsound10_6
            subsound10_7)))
      (LRCompactVBoxSound.join (box := joinbox10_rRLRLR) .chi ((157 : ℚ) / 160)
        (LRCompactVBoxSound.join (box := joinbox10_rRLRLRL) .s ((1 : ℚ) / 16)
          (LRCompactVBoxSound.join (box := joinbox10_rRLRLRLL) .k ((11 : ℚ) / 24)
            subsound10_8
            (LRCompactVBoxSound.join (box := joinbox10_rRLRLRLLR) .chi ((311 : ℚ) / 320)
              subsound10_9
              subsound10_10))
          (LRCompactVBoxSound.join (box := joinbox10_rRLRLRLR) .k ((11 : ℚ) / 24)
            (LRCompactVBoxSound.join (box := joinbox10_rRLRLRLRL) .chi ((311 : ℚ) / 320)
              subsound10_11
              subsound10_12)
            (LRCompactVBoxSound.join (box := joinbox10_rRLRLRLRR) .chi ((311 : ℚ) / 320)
              subsound10_13
              subsound10_14)))
        (LRCompactVBoxSound.join (box := joinbox10_rRLRLRR) .s ((1 : ℚ) / 16)
          (LRCompactVBoxSound.join (box := joinbox10_rRLRLRRL) .k ((11 : ℚ) / 24)
            subsound10_15
            subsound10_16)
          (LRCompactVBoxSound.join (box := joinbox10_rRLRLRRR) .k ((11 : ℚ) / 24)
            subsound10_17
            (LRCompactVBoxSound.join (box := joinbox10_rRLRLRRRR) .chi ((317 : ℚ) / 320)
              subsound10_18
              subsound10_19)))))
    (LRCompactVBoxSound.join (box := joinbox10_rRLRR) .k ((5 : ℚ) / 12)
      (LRCompactVBoxSound.join (box := joinbox10_rRLRRL) .chi ((157 : ℚ) / 160)
        (LRCompactVBoxSound.join (box := joinbox10_rRLRRLL) .s ((3 : ℚ) / 16)
          (LRCompactVBoxSound.join (box := joinbox10_rRLRRLLL) .k ((3 : ℚ) / 8)
            subsound10_20
            (LRCompactVBoxSound.join (box := joinbox10_rRLRRLLLR) .chi ((311 : ℚ) / 320)
              subsound10_21
              subsound10_22))
          (LRCompactVBoxSound.join (box := joinbox10_rRLRRLLR) .k ((3 : ℚ) / 8)
            (LRCompactVBoxSound.join (box := joinbox10_rRLRRLLRL) .chi ((311 : ℚ) / 320)
              subsound10_23
              subsound10_24)
            (LRCompactVBoxSound.join (box := joinbox10_rRLRRLLRR) .chi ((311 : ℚ) / 320)
              subsound10_25
              subsound10_26)))
        (LRCompactVBoxSound.join (box := joinbox10_rRLRRLR) .s ((3 : ℚ) / 16)
          (LRCompactVBoxSound.join (box := joinbox10_rRLRRLRL) .k ((3 : ℚ) / 8)
            subsound10_27
            subsound10_28)
          (LRCompactVBoxSound.join (box := joinbox10_rRLRRLRR) .k ((3 : ℚ) / 8)
            subsound10_29
            (LRCompactVBoxSound.join (box := joinbox10_rRLRRLRRR) .chi ((317 : ℚ) / 320)
              subsound10_30
              subsound10_31))))
      (LRCompactVBoxSound.join (box := joinbox10_rRLRRR) .chi ((157 : ℚ) / 160)
        (LRCompactVBoxSound.join (box := joinbox10_rRLRRRL) .s ((3 : ℚ) / 16)
          (LRCompactVBoxSound.join (box := joinbox10_rRLRRRLL) .k ((11 : ℚ) / 24)
            (LRCompactVBoxSound.join (box := joinbox10_rRLRRRLLL) .chi ((311 : ℚ) / 320)
              subsound10_32
              subsound10_33)
            (LRCompactVBoxSound.join (box := joinbox10_rRLRRRLLR) .chi ((311 : ℚ) / 320)
              (LRCompactVBoxSound.join (box := joinbox10_rRLRRRLLRL) .s ((5 : ℚ) / 32)
                subsound10_34
                subsound10_35)
              (LRCompactVBoxSound.join (box := joinbox10_rRLRRRLLRR) .s ((5 : ℚ) / 32)
                subsound10_36
                subsound10_37)))
          (LRCompactVBoxSound.join (box := joinbox10_rRLRRRLR) .k ((11 : ℚ) / 24)
            (LRCompactVBoxSound.join (box := joinbox10_rRLRRRLRL) .chi ((311 : ℚ) / 320)
              (LRCompactVBoxSound.join (box := joinbox10_rRLRRRLRLL) .s ((7 : ℚ) / 32)
                subsound10_38
                subsound10_39)
              (LRCompactVBoxSound.join (box := joinbox10_rRLRRRLRLR) .s ((7 : ℚ) / 32)
                subsound10_40
                subsound10_41))
            (LRCompactVBoxSound.join (box := joinbox10_rRLRRRLRR) .chi ((311 : ℚ) / 320)
              (LRCompactVBoxSound.join (box := joinbox10_rRLRRRLRRL) .s ((7 : ℚ) / 32)
                subsound10_42
                subsound10_43)
              (LRCompactVBoxSound.join (box := joinbox10_rRLRRRLRRR) .s ((7 : ℚ) / 32)
                subsound10_44
                subsound10_45))))
        (LRCompactVBoxSound.join (box := joinbox10_rRLRRRR) .s ((3 : ℚ) / 16)
          (LRCompactVBoxSound.join (box := joinbox10_rRLRRRRL) .k ((11 : ℚ) / 24)
            (LRCompactVBoxSound.join (box := joinbox10_rRLRRRRLL) .chi ((317 : ℚ) / 320)
              subsound10_46
              subsound10_47)
            (LRCompactVBoxSound.join (box := joinbox10_rRLRRRRLR) .chi ((317 : ℚ) / 320)
              (LRCompactVBoxSound.join (box := joinbox10_rRLRRRRLRL) .s ((5 : ℚ) / 32)
                subsound10_48
                subsound10_49)
              subsound10_50))
          (LRCompactVBoxSound.join (box := joinbox10_rRLRRRRR) .k ((11 : ℚ) / 24)
            (LRCompactVBoxSound.join (box := joinbox10_rRLRRRRRL) .chi ((317 : ℚ) / 320)
              (LRCompactVBoxSound.join (box := joinbox10_rRLRRRRRLL) .s ((7 : ℚ) / 32)
                subsound10_51
                subsound10_52)
              subsound10_53)
            (LRCompactVBoxSound.join (box := joinbox10_rRLRRRRRR) .chi ((317 : ℚ) / 320)
              (LRCompactVBoxSound.join (box := joinbox10_rRLRRRRRRL) .s ((7 : ℚ) / 32)
                subsound10_54
                subsound10_55)
              (LRCompactVBoxSound.join (box := joinbox10_rRLRRRRRRR) .s ((7 : ℚ) / 32)
                subsound10_56
                subsound10_57)))))))

end CourtadeKumar.GeneratedLRCompactVLowR
