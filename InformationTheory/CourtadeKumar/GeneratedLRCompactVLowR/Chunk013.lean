import InformationTheory.CourtadeKumar.LRCompactVBasicReplay

/-! Frozen basic compact-V replay.
Plan SHA-256: ce3f7a498b2b9caf346dcf88ce7861f8cc091af8cd93f5624d7684e21322ecd5
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CourtadeKumar.GeneratedLRCompactVLowR

-- 63 accepted leaves below path rRRRL.
def box13 : CertificateBox where
  sLo := ((1 : ℚ) / 4)
  sHi := ((3 : ℚ) / 8)
  kLo := ((1 : ℚ) / 3)
  kHi := ((1 : ℚ) / 2)
  chiLo := ((77 : ℚ) / 80)
  chiHi := (1 : ℚ)


def subbox13_0 : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((5 : ℚ) / 16), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((77 : ℚ) / 80), ((311 : ℚ) / 320)⟩

theorem checked13_0 :
    LRCompactVLeafParameters.check subbox13_0 .long = true := by decide +kernel

theorem subsound13_0 : LRCompactVBoxSound subbox13_0 :=
  LRCompactVLeafParameters.sound checked13_0


def subbox13_1 : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((5 : ℚ) / 16), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((311 : ℚ) / 320), ((157 : ℚ) / 160)⟩

theorem checked13_1 :
    LRCompactVLeafParameters.check subbox13_1 .long = true := by decide +kernel

theorem subsound13_1 : LRCompactVBoxSound subbox13_1 :=
  LRCompactVLeafParameters.sound checked13_1


def subbox13_2 : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((9 : ℚ) / 32), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((77 : ℚ) / 80), ((311 : ℚ) / 320)⟩

theorem checked13_2 :
    LRCompactVLeafParameters.check subbox13_2 .short = true := by decide +kernel

theorem subsound13_2 : LRCompactVBoxSound subbox13_2 :=
  LRCompactVLeafParameters.sound checked13_2


def subbox13_3 : CertificateBox :=
  ⟨((9 : ℚ) / 32), ((5 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((77 : ℚ) / 80), ((311 : ℚ) / 320)⟩

theorem checked13_3 :
    LRCompactVLeafParameters.check subbox13_3 .short = true := by decide +kernel

theorem subsound13_3 : LRCompactVBoxSound subbox13_3 :=
  LRCompactVLeafParameters.sound checked13_3


def subbox13_4 : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((9 : ℚ) / 32), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((311 : ℚ) / 320), ((157 : ℚ) / 160)⟩

theorem checked13_4 :
    LRCompactVLeafParameters.check subbox13_4 .short = true := by decide +kernel

theorem subsound13_4 : LRCompactVBoxSound subbox13_4 :=
  LRCompactVLeafParameters.sound checked13_4


def subbox13_5 : CertificateBox :=
  ⟨((9 : ℚ) / 32), ((5 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((311 : ℚ) / 320), ((157 : ℚ) / 160)⟩

theorem checked13_5 :
    LRCompactVLeafParameters.check subbox13_5 .short = true := by decide +kernel

theorem subsound13_5 : LRCompactVBoxSound subbox13_5 :=
  LRCompactVLeafParameters.sound checked13_5


def subbox13_6 : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((77 : ℚ) / 80), ((311 : ℚ) / 320)⟩

theorem checked13_6 :
    LRCompactVLeafParameters.check subbox13_6 .short = true := by decide +kernel

theorem subsound13_6 : LRCompactVBoxSound subbox13_6 :=
  LRCompactVLeafParameters.sound checked13_6


def subbox13_7 : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((77 : ℚ) / 80), ((311 : ℚ) / 320)⟩

theorem checked13_7 :
    LRCompactVLeafParameters.check subbox13_7 .short = true := by decide +kernel

theorem subsound13_7 : LRCompactVBoxSound subbox13_7 :=
  LRCompactVLeafParameters.sound checked13_7


def subbox13_8 : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((311 : ℚ) / 320), ((157 : ℚ) / 160)⟩

theorem checked13_8 :
    LRCompactVLeafParameters.check subbox13_8 .short = true := by decide +kernel

theorem subsound13_8 : LRCompactVBoxSound subbox13_8 :=
  LRCompactVLeafParameters.sound checked13_8


def subbox13_9 : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((311 : ℚ) / 320), ((157 : ℚ) / 160)⟩

theorem checked13_9 :
    LRCompactVLeafParameters.check subbox13_9 .short = true := by decide +kernel

theorem subsound13_9 : LRCompactVBoxSound subbox13_9 :=
  LRCompactVLeafParameters.sound checked13_9


def subbox13_10 : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((77 : ℚ) / 80), ((311 : ℚ) / 320)⟩

theorem checked13_10 :
    LRCompactVLeafParameters.check subbox13_10 .short = true := by decide +kernel

theorem subsound13_10 : LRCompactVBoxSound subbox13_10 :=
  LRCompactVLeafParameters.sound checked13_10


def subbox13_11 : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((77 : ℚ) / 80), ((311 : ℚ) / 320)⟩

theorem checked13_11 :
    LRCompactVLeafParameters.check subbox13_11 .long = true := by decide +kernel

theorem subsound13_11 : LRCompactVBoxSound subbox13_11 :=
  LRCompactVLeafParameters.sound checked13_11


def subbox13_12 : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((311 : ℚ) / 320), ((157 : ℚ) / 160)⟩

theorem checked13_12 :
    LRCompactVLeafParameters.check subbox13_12 .short = true := by decide +kernel

theorem subsound13_12 : LRCompactVBoxSound subbox13_12 :=
  LRCompactVLeafParameters.sound checked13_12


def subbox13_13 : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((311 : ℚ) / 320), ((157 : ℚ) / 160)⟩

theorem checked13_13 :
    LRCompactVLeafParameters.check subbox13_13 .long = true := by decide +kernel

theorem subsound13_13 : LRCompactVBoxSound subbox13_13 :=
  LRCompactVLeafParameters.sound checked13_13


def subbox13_14 : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((5 : ℚ) / 16), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((157 : ℚ) / 160), ((317 : ℚ) / 320)⟩

theorem checked13_14 :
    LRCompactVLeafParameters.check subbox13_14 .long = true := by decide +kernel

theorem subsound13_14 : LRCompactVBoxSound subbox13_14 :=
  LRCompactVLeafParameters.sound checked13_14


def subbox13_15 : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((5 : ℚ) / 16), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((317 : ℚ) / 320), (1 : ℚ)⟩

theorem checked13_15 :
    LRCompactVLeafParameters.check subbox13_15 .long = true := by decide +kernel

theorem subsound13_15 : LRCompactVBoxSound subbox13_15 :=
  LRCompactVLeafParameters.sound checked13_15


def subbox13_16 : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((9 : ℚ) / 32), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((157 : ℚ) / 160), ((317 : ℚ) / 320)⟩

theorem checked13_16 :
    LRCompactVLeafParameters.check subbox13_16 .short = true := by decide +kernel

theorem subsound13_16 : LRCompactVBoxSound subbox13_16 :=
  LRCompactVLeafParameters.sound checked13_16


def subbox13_17 : CertificateBox :=
  ⟨((9 : ℚ) / 32), ((5 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((157 : ℚ) / 160), ((317 : ℚ) / 320)⟩

theorem checked13_17 :
    LRCompactVLeafParameters.check subbox13_17 .short = true := by decide +kernel

theorem subsound13_17 : LRCompactVBoxSound subbox13_17 :=
  LRCompactVLeafParameters.sound checked13_17


def subbox13_18 : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((5 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((317 : ℚ) / 320), (1 : ℚ)⟩

theorem checked13_18 :
    LRCompactVLeafParameters.check subbox13_18 .long = true := by decide +kernel

theorem subsound13_18 : LRCompactVBoxSound subbox13_18 :=
  LRCompactVLeafParameters.sound checked13_18


def subbox13_19 : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((157 : ℚ) / 160), ((317 : ℚ) / 320)⟩

theorem checked13_19 :
    LRCompactVLeafParameters.check subbox13_19 .short = true := by decide +kernel

theorem subsound13_19 : LRCompactVBoxSound subbox13_19 :=
  LRCompactVLeafParameters.sound checked13_19


def subbox13_20 : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((157 : ℚ) / 160), ((317 : ℚ) / 320)⟩

theorem checked13_20 :
    LRCompactVLeafParameters.check subbox13_20 .short = true := by decide +kernel

theorem subsound13_20 : LRCompactVBoxSound subbox13_20 :=
  LRCompactVLeafParameters.sound checked13_20


def subbox13_21 : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((317 : ℚ) / 320), (1 : ℚ)⟩

theorem checked13_21 :
    LRCompactVLeafParameters.check subbox13_21 .short = true := by decide +kernel

theorem subsound13_21 : LRCompactVBoxSound subbox13_21 :=
  LRCompactVLeafParameters.sound checked13_21


def subbox13_22 : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((317 : ℚ) / 320), (1 : ℚ)⟩

theorem checked13_22 :
    LRCompactVLeafParameters.check subbox13_22 .short = true := by decide +kernel

theorem subsound13_22 : LRCompactVBoxSound subbox13_22 :=
  LRCompactVLeafParameters.sound checked13_22


def subbox13_23 : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((157 : ℚ) / 160), ((317 : ℚ) / 320)⟩

theorem checked13_23 :
    LRCompactVLeafParameters.check subbox13_23 .short = true := by decide +kernel

theorem subsound13_23 : LRCompactVBoxSound subbox13_23 :=
  LRCompactVLeafParameters.sound checked13_23


def subbox13_24 : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((157 : ℚ) / 160), ((317 : ℚ) / 320)⟩

theorem checked13_24 :
    LRCompactVLeafParameters.check subbox13_24 .accurateLog = true := by decide +kernel

theorem subsound13_24 : LRCompactVBoxSound subbox13_24 :=
  LRCompactVLeafParameters.sound checked13_24


def subbox13_25 : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((317 : ℚ) / 320), (1 : ℚ)⟩

theorem checked13_25 :
    LRCompactVLeafParameters.check subbox13_25 .short = true := by decide +kernel

theorem subsound13_25 : LRCompactVBoxSound subbox13_25 :=
  LRCompactVLeafParameters.sound checked13_25


def subbox13_26 : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((317 : ℚ) / 320), (1 : ℚ)⟩

theorem checked13_26 :
    LRCompactVLeafParameters.check subbox13_26 .short = true := by decide +kernel

theorem subsound13_26 : LRCompactVBoxSound subbox13_26 :=
  LRCompactVLeafParameters.sound checked13_26


def subbox13_27 : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((9 : ℚ) / 32), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((77 : ℚ) / 80), ((311 : ℚ) / 320)⟩

theorem checked13_27 :
    LRCompactVLeafParameters.check subbox13_27 .short = true := by decide +kernel

theorem subsound13_27 : LRCompactVBoxSound subbox13_27 :=
  LRCompactVLeafParameters.sound checked13_27


def subbox13_28 : CertificateBox :=
  ⟨((9 : ℚ) / 32), ((5 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((77 : ℚ) / 80), ((311 : ℚ) / 320)⟩

theorem checked13_28 :
    LRCompactVLeafParameters.check subbox13_28 .short = true := by decide +kernel

theorem subsound13_28 : LRCompactVBoxSound subbox13_28 :=
  LRCompactVLeafParameters.sound checked13_28


def subbox13_29 : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((9 : ℚ) / 32), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((311 : ℚ) / 320), ((157 : ℚ) / 160)⟩

theorem checked13_29 :
    LRCompactVLeafParameters.check subbox13_29 .short = true := by decide +kernel

theorem subsound13_29 : LRCompactVBoxSound subbox13_29 :=
  LRCompactVLeafParameters.sound checked13_29


def subbox13_30 : CertificateBox :=
  ⟨((9 : ℚ) / 32), ((5 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((311 : ℚ) / 320), ((157 : ℚ) / 160)⟩

theorem checked13_30 :
    LRCompactVLeafParameters.check subbox13_30 .short = true := by decide +kernel

theorem subsound13_30 : LRCompactVBoxSound subbox13_30 :=
  LRCompactVLeafParameters.sound checked13_30


def subbox13_31 : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((9 : ℚ) / 32), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((77 : ℚ) / 80), ((311 : ℚ) / 320)⟩

theorem checked13_31 :
    LRCompactVLeafParameters.check subbox13_31 .long = true := by decide +kernel

theorem subsound13_31 : LRCompactVBoxSound subbox13_31 :=
  LRCompactVLeafParameters.sound checked13_31


def subbox13_32 : CertificateBox :=
  ⟨((9 : ℚ) / 32), ((5 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((77 : ℚ) / 80), ((311 : ℚ) / 320)⟩

theorem checked13_32 :
    LRCompactVLeafParameters.check subbox13_32 .long = true := by decide +kernel

theorem subsound13_32 : LRCompactVBoxSound subbox13_32 :=
  LRCompactVLeafParameters.sound checked13_32


def subbox13_33 : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((9 : ℚ) / 32), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((311 : ℚ) / 320), ((157 : ℚ) / 160)⟩

theorem checked13_33 :
    LRCompactVLeafParameters.check subbox13_33 .long = true := by decide +kernel

theorem subsound13_33 : LRCompactVBoxSound subbox13_33 :=
  LRCompactVLeafParameters.sound checked13_33


def subbox13_34 : CertificateBox :=
  ⟨((9 : ℚ) / 32), ((5 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((311 : ℚ) / 320), ((157 : ℚ) / 160)⟩

theorem checked13_34 :
    LRCompactVLeafParameters.check subbox13_34 .long = true := by decide +kernel

theorem subsound13_34 : LRCompactVBoxSound subbox13_34 :=
  LRCompactVLeafParameters.sound checked13_34


def subbox13_35 : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((77 : ℚ) / 80), ((311 : ℚ) / 320)⟩

theorem checked13_35 :
    LRCompactVLeafParameters.check subbox13_35 .long = true := by decide +kernel

theorem subsound13_35 : LRCompactVBoxSound subbox13_35 :=
  LRCompactVLeafParameters.sound checked13_35


def subbox13_36 : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((77 : ℚ) / 80), ((311 : ℚ) / 320)⟩

theorem checked13_36 :
    LRCompactVLeafParameters.check subbox13_36 .long = true := by decide +kernel

theorem subsound13_36 : LRCompactVBoxSound subbox13_36 :=
  LRCompactVLeafParameters.sound checked13_36


def subbox13_37 : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((311 : ℚ) / 320), ((157 : ℚ) / 160)⟩

theorem checked13_37 :
    LRCompactVLeafParameters.check subbox13_37 .long = true := by decide +kernel

theorem subsound13_37 : LRCompactVBoxSound subbox13_37 :=
  LRCompactVLeafParameters.sound checked13_37


def subbox13_38 : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((311 : ℚ) / 320), ((157 : ℚ) / 160)⟩

theorem checked13_38 :
    LRCompactVLeafParameters.check subbox13_38 .long = true := by decide +kernel

theorem subsound13_38 : LRCompactVBoxSound subbox13_38 :=
  LRCompactVLeafParameters.sound checked13_38


def subbox13_39 : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((77 : ℚ) / 80), ((311 : ℚ) / 320)⟩

theorem checked13_39 :
    LRCompactVLeafParameters.check subbox13_39 .short = true := by decide +kernel

theorem subsound13_39 : LRCompactVBoxSound subbox13_39 :=
  LRCompactVLeafParameters.sound checked13_39


def subbox13_40 : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((77 : ℚ) / 80), ((311 : ℚ) / 320)⟩

theorem checked13_40 :
    LRCompactVLeafParameters.check subbox13_40 .short = true := by decide +kernel

theorem subsound13_40 : LRCompactVBoxSound subbox13_40 :=
  LRCompactVLeafParameters.sound checked13_40


def subbox13_41 : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((77 : ℚ) / 80), ((311 : ℚ) / 320)⟩

theorem checked13_41 :
    LRCompactVLeafParameters.check subbox13_41 .short = true := by decide +kernel

theorem subsound13_41 : LRCompactVBoxSound subbox13_41 :=
  LRCompactVLeafParameters.sound checked13_41


def subbox13_42 : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((77 : ℚ) / 80), ((311 : ℚ) / 320)⟩

theorem checked13_42 :
    LRCompactVLeafParameters.check subbox13_42 .short = true := by decide +kernel

theorem subsound13_42 : LRCompactVBoxSound subbox13_42 :=
  LRCompactVLeafParameters.sound checked13_42


def subbox13_43 : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((311 : ℚ) / 320), ((157 : ℚ) / 160)⟩

theorem checked13_43 :
    LRCompactVLeafParameters.check subbox13_43 .long = true := by decide +kernel

theorem subsound13_43 : LRCompactVBoxSound subbox13_43 :=
  LRCompactVLeafParameters.sound checked13_43


def subbox13_44 : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((311 : ℚ) / 320), ((157 : ℚ) / 160)⟩

theorem checked13_44 :
    LRCompactVLeafParameters.check subbox13_44 .short = true := by decide +kernel

theorem subsound13_44 : LRCompactVBoxSound subbox13_44 :=
  LRCompactVLeafParameters.sound checked13_44


def subbox13_45 : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((311 : ℚ) / 320), ((157 : ℚ) / 160)⟩

theorem checked13_45 :
    LRCompactVLeafParameters.check subbox13_45 .short = true := by decide +kernel

theorem subsound13_45 : LRCompactVBoxSound subbox13_45 :=
  LRCompactVLeafParameters.sound checked13_45


def subbox13_46 : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((9 : ℚ) / 32), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((157 : ℚ) / 160), ((317 : ℚ) / 320)⟩

theorem checked13_46 :
    LRCompactVLeafParameters.check subbox13_46 .short = true := by decide +kernel

theorem subsound13_46 : LRCompactVBoxSound subbox13_46 :=
  LRCompactVLeafParameters.sound checked13_46


def subbox13_47 : CertificateBox :=
  ⟨((9 : ℚ) / 32), ((5 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((157 : ℚ) / 160), ((317 : ℚ) / 320)⟩

theorem checked13_47 :
    LRCompactVLeafParameters.check subbox13_47 .short = true := by decide +kernel

theorem subsound13_47 : LRCompactVBoxSound subbox13_47 :=
  LRCompactVLeafParameters.sound checked13_47


def subbox13_48 : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((9 : ℚ) / 32), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((317 : ℚ) / 320), (1 : ℚ)⟩

theorem checked13_48 :
    LRCompactVLeafParameters.check subbox13_48 .short = true := by decide +kernel

theorem subsound13_48 : LRCompactVBoxSound subbox13_48 :=
  LRCompactVLeafParameters.sound checked13_48


def subbox13_49 : CertificateBox :=
  ⟨((9 : ℚ) / 32), ((5 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((317 : ℚ) / 320), (1 : ℚ)⟩

theorem checked13_49 :
    LRCompactVLeafParameters.check subbox13_49 .short = true := by decide +kernel

theorem subsound13_49 : LRCompactVBoxSound subbox13_49 :=
  LRCompactVLeafParameters.sound checked13_49


def subbox13_50 : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((9 : ℚ) / 32), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((157 : ℚ) / 160), ((317 : ℚ) / 320)⟩

theorem checked13_50 :
    LRCompactVLeafParameters.check subbox13_50 .short = true := by decide +kernel

theorem subsound13_50 : LRCompactVBoxSound subbox13_50 :=
  LRCompactVLeafParameters.sound checked13_50


def subbox13_51 : CertificateBox :=
  ⟨((9 : ℚ) / 32), ((5 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((157 : ℚ) / 160), ((317 : ℚ) / 320)⟩

theorem checked13_51 :
    LRCompactVLeafParameters.check subbox13_51 .long = true := by decide +kernel

theorem subsound13_51 : LRCompactVBoxSound subbox13_51 :=
  LRCompactVLeafParameters.sound checked13_51


def subbox13_52 : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((9 : ℚ) / 32), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((317 : ℚ) / 320), (1 : ℚ)⟩

theorem checked13_52 :
    LRCompactVLeafParameters.check subbox13_52 .short = true := by decide +kernel

theorem subsound13_52 : LRCompactVBoxSound subbox13_52 :=
  LRCompactVLeafParameters.sound checked13_52


def subbox13_53 : CertificateBox :=
  ⟨((9 : ℚ) / 32), ((5 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((317 : ℚ) / 320), (1 : ℚ)⟩

theorem checked13_53 :
    LRCompactVLeafParameters.check subbox13_53 .long = true := by decide +kernel

theorem subsound13_53 : LRCompactVBoxSound subbox13_53 :=
  LRCompactVLeafParameters.sound checked13_53


def subbox13_54 : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((157 : ℚ) / 160), ((317 : ℚ) / 320)⟩

theorem checked13_54 :
    LRCompactVLeafParameters.check subbox13_54 .long = true := by decide +kernel

theorem subsound13_54 : LRCompactVBoxSound subbox13_54 :=
  LRCompactVLeafParameters.sound checked13_54


def subbox13_55 : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((157 : ℚ) / 160), ((317 : ℚ) / 320)⟩

theorem checked13_55 :
    LRCompactVLeafParameters.check subbox13_55 .long = true := by decide +kernel

theorem subsound13_55 : LRCompactVBoxSound subbox13_55 :=
  LRCompactVLeafParameters.sound checked13_55


def subbox13_56 : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((317 : ℚ) / 320), (1 : ℚ)⟩

theorem checked13_56 :
    LRCompactVLeafParameters.check subbox13_56 .short = true := by decide +kernel

theorem subsound13_56 : LRCompactVBoxSound subbox13_56 :=
  LRCompactVLeafParameters.sound checked13_56


def subbox13_57 : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((317 : ℚ) / 320), (1 : ℚ)⟩

theorem checked13_57 :
    LRCompactVLeafParameters.check subbox13_57 .long = true := by decide +kernel

theorem subsound13_57 : LRCompactVBoxSound subbox13_57 :=
  LRCompactVLeafParameters.sound checked13_57


def subbox13_58 : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((157 : ℚ) / 160), ((317 : ℚ) / 320)⟩

theorem checked13_58 :
    LRCompactVLeafParameters.check subbox13_58 .long = true := by decide +kernel

theorem subsound13_58 : LRCompactVBoxSound subbox13_58 :=
  LRCompactVLeafParameters.sound checked13_58


def subbox13_59 : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((157 : ℚ) / 160), ((317 : ℚ) / 320)⟩

theorem checked13_59 :
    LRCompactVLeafParameters.check subbox13_59 .short = true := by decide +kernel

theorem subsound13_59 : LRCompactVBoxSound subbox13_59 :=
  LRCompactVLeafParameters.sound checked13_59


def subbox13_60 : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((157 : ℚ) / 160), ((317 : ℚ) / 320)⟩

theorem checked13_60 :
    LRCompactVLeafParameters.check subbox13_60 .short = true := by decide +kernel

theorem subsound13_60 : LRCompactVBoxSound subbox13_60 :=
  LRCompactVLeafParameters.sound checked13_60


def subbox13_61 : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((317 : ℚ) / 320), (1 : ℚ)⟩

theorem checked13_61 :
    LRCompactVLeafParameters.check subbox13_61 .long = true := by decide +kernel

theorem subsound13_61 : LRCompactVBoxSound subbox13_61 :=
  LRCompactVLeafParameters.sound checked13_61


def subbox13_62 : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((317 : ℚ) / 320), (1 : ℚ)⟩

theorem checked13_62 :
    LRCompactVLeafParameters.check subbox13_62 .long = true := by decide +kernel

theorem subsound13_62 : LRCompactVBoxSound subbox13_62 :=
  LRCompactVLeafParameters.sound checked13_62


def joinbox13_rRRRLL : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((3 : ℚ) / 8), ((1 : ℚ) / 3), ((5 : ℚ) / 12), ((77 : ℚ) / 80), (1 : ℚ)⟩


def joinbox13_rRRRLLL : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((3 : ℚ) / 8), ((1 : ℚ) / 3), ((5 : ℚ) / 12), ((77 : ℚ) / 80), ((157 : ℚ) / 160)⟩


def joinbox13_rRRRLLLL : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((5 : ℚ) / 16), ((1 : ℚ) / 3), ((5 : ℚ) / 12), ((77 : ℚ) / 80), ((157 : ℚ) / 160)⟩


def joinbox13_rRRRLLLLL : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((5 : ℚ) / 16), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((77 : ℚ) / 80), ((157 : ℚ) / 160)⟩


def joinbox13_rRRRLLLLR : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((5 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((77 : ℚ) / 80), ((157 : ℚ) / 160)⟩


def joinbox13_rRRRLLLLRL : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((5 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((77 : ℚ) / 80), ((311 : ℚ) / 320)⟩


def joinbox13_rRRRLLLLRR : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((5 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((311 : ℚ) / 320), ((157 : ℚ) / 160)⟩


def joinbox13_rRRRLLLR : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((3 : ℚ) / 8), ((1 : ℚ) / 3), ((5 : ℚ) / 12), ((77 : ℚ) / 80), ((157 : ℚ) / 160)⟩


def joinbox13_rRRRLLLRL : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((3 : ℚ) / 8), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((77 : ℚ) / 80), ((157 : ℚ) / 160)⟩


def joinbox13_rRRRLLLRLL : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((3 : ℚ) / 8), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((77 : ℚ) / 80), ((311 : ℚ) / 320)⟩


def joinbox13_rRRRLLLRLR : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((3 : ℚ) / 8), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((311 : ℚ) / 320), ((157 : ℚ) / 160)⟩


def joinbox13_rRRRLLLRR : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((3 : ℚ) / 8), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((77 : ℚ) / 80), ((157 : ℚ) / 160)⟩


def joinbox13_rRRRLLLRRL : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((3 : ℚ) / 8), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((77 : ℚ) / 80), ((311 : ℚ) / 320)⟩


def joinbox13_rRRRLLLRRR : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((3 : ℚ) / 8), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((311 : ℚ) / 320), ((157 : ℚ) / 160)⟩


def joinbox13_rRRRLLR : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((3 : ℚ) / 8), ((1 : ℚ) / 3), ((5 : ℚ) / 12), ((157 : ℚ) / 160), (1 : ℚ)⟩


def joinbox13_rRRRLLRL : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((5 : ℚ) / 16), ((1 : ℚ) / 3), ((5 : ℚ) / 12), ((157 : ℚ) / 160), (1 : ℚ)⟩


def joinbox13_rRRRLLRLL : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((5 : ℚ) / 16), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((157 : ℚ) / 160), (1 : ℚ)⟩


def joinbox13_rRRRLLRLR : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((5 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((157 : ℚ) / 160), (1 : ℚ)⟩


def joinbox13_rRRRLLRLRL : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((5 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((157 : ℚ) / 160), ((317 : ℚ) / 320)⟩


def joinbox13_rRRRLLRR : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((3 : ℚ) / 8), ((1 : ℚ) / 3), ((5 : ℚ) / 12), ((157 : ℚ) / 160), (1 : ℚ)⟩


def joinbox13_rRRRLLRRL : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((3 : ℚ) / 8), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((157 : ℚ) / 160), (1 : ℚ)⟩


def joinbox13_rRRRLLRRLL : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((3 : ℚ) / 8), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((157 : ℚ) / 160), ((317 : ℚ) / 320)⟩


def joinbox13_rRRRLLRRLR : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((3 : ℚ) / 8), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((317 : ℚ) / 320), (1 : ℚ)⟩


def joinbox13_rRRRLLRRR : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((3 : ℚ) / 8), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((157 : ℚ) / 160), (1 : ℚ)⟩


def joinbox13_rRRRLLRRRL : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((3 : ℚ) / 8), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((157 : ℚ) / 160), ((317 : ℚ) / 320)⟩


def joinbox13_rRRRLLRRRR : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((3 : ℚ) / 8), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((317 : ℚ) / 320), (1 : ℚ)⟩


def joinbox13_rRRRLR : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((1 : ℚ) / 2), ((77 : ℚ) / 80), (1 : ℚ)⟩


def joinbox13_rRRRLRL : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((1 : ℚ) / 2), ((77 : ℚ) / 80), ((157 : ℚ) / 160)⟩


def joinbox13_rRRRLRLL : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((5 : ℚ) / 16), ((5 : ℚ) / 12), ((1 : ℚ) / 2), ((77 : ℚ) / 80), ((157 : ℚ) / 160)⟩


def joinbox13_rRRRLRLLL : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((5 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((77 : ℚ) / 80), ((157 : ℚ) / 160)⟩


def joinbox13_rRRRLRLLLL : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((5 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((77 : ℚ) / 80), ((311 : ℚ) / 320)⟩


def joinbox13_rRRRLRLLLR : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((5 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((311 : ℚ) / 320), ((157 : ℚ) / 160)⟩


def joinbox13_rRRRLRLLR : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((5 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((77 : ℚ) / 80), ((157 : ℚ) / 160)⟩


def joinbox13_rRRRLRLLRL : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((5 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((77 : ℚ) / 80), ((311 : ℚ) / 320)⟩


def joinbox13_rRRRLRLLRR : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((5 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((311 : ℚ) / 320), ((157 : ℚ) / 160)⟩


def joinbox13_rRRRLRLR : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((1 : ℚ) / 2), ((77 : ℚ) / 80), ((157 : ℚ) / 160)⟩


def joinbox13_rRRRLRLRL : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((77 : ℚ) / 80), ((157 : ℚ) / 160)⟩


def joinbox13_rRRRLRLRLL : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((77 : ℚ) / 80), ((311 : ℚ) / 320)⟩


def joinbox13_rRRRLRLRLR : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((311 : ℚ) / 320), ((157 : ℚ) / 160)⟩


def joinbox13_rRRRLRLRR : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((3 : ℚ) / 8), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((77 : ℚ) / 80), ((157 : ℚ) / 160)⟩


def joinbox13_rRRRLRLRRL : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((3 : ℚ) / 8), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((77 : ℚ) / 80), ((311 : ℚ) / 320)⟩


def joinbox13_rRRRLRLRRLL : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((77 : ℚ) / 80), ((311 : ℚ) / 320)⟩


def joinbox13_rRRRLRLRRLR : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((77 : ℚ) / 80), ((311 : ℚ) / 320)⟩


def joinbox13_rRRRLRLRRR : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((3 : ℚ) / 8), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((311 : ℚ) / 320), ((157 : ℚ) / 160)⟩


def joinbox13_rRRRLRLRRRR : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((311 : ℚ) / 320), ((157 : ℚ) / 160)⟩


def joinbox13_rRRRLRR : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((1 : ℚ) / 2), ((157 : ℚ) / 160), (1 : ℚ)⟩


def joinbox13_rRRRLRRL : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((5 : ℚ) / 16), ((5 : ℚ) / 12), ((1 : ℚ) / 2), ((157 : ℚ) / 160), (1 : ℚ)⟩


def joinbox13_rRRRLRRLL : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((5 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((157 : ℚ) / 160), (1 : ℚ)⟩


def joinbox13_rRRRLRRLLL : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((5 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((157 : ℚ) / 160), ((317 : ℚ) / 320)⟩


def joinbox13_rRRRLRRLLR : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((5 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((317 : ℚ) / 320), (1 : ℚ)⟩


def joinbox13_rRRRLRRLR : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((5 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((157 : ℚ) / 160), (1 : ℚ)⟩


def joinbox13_rRRRLRRLRL : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((5 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((157 : ℚ) / 160), ((317 : ℚ) / 320)⟩


def joinbox13_rRRRLRRLRR : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((5 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((317 : ℚ) / 320), (1 : ℚ)⟩


def joinbox13_rRRRLRRR : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((1 : ℚ) / 2), ((157 : ℚ) / 160), (1 : ℚ)⟩


def joinbox13_rRRRLRRRL : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((157 : ℚ) / 160), (1 : ℚ)⟩


def joinbox13_rRRRLRRRLL : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((157 : ℚ) / 160), ((317 : ℚ) / 320)⟩


def joinbox13_rRRRLRRRLR : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((317 : ℚ) / 320), (1 : ℚ)⟩


def joinbox13_rRRRLRRRR : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((3 : ℚ) / 8), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((157 : ℚ) / 160), (1 : ℚ)⟩


def joinbox13_rRRRLRRRRL : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((3 : ℚ) / 8), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((157 : ℚ) / 160), ((317 : ℚ) / 320)⟩


def joinbox13_rRRRLRRRRLR : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((157 : ℚ) / 160), ((317 : ℚ) / 320)⟩


def joinbox13_rRRRLRRRRR : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((3 : ℚ) / 8), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((317 : ℚ) / 320), (1 : ℚ)⟩


theorem sound13 : LRCompactVBoxSound box13 :=
  (LRCompactVBoxSound.join (box := box13) .k ((5 : ℚ) / 12)
    (LRCompactVBoxSound.join (box := joinbox13_rRRRLL) .chi ((157 : ℚ) / 160)
      (LRCompactVBoxSound.join (box := joinbox13_rRRRLLL) .s ((5 : ℚ) / 16)
        (LRCompactVBoxSound.join (box := joinbox13_rRRRLLLL) .k ((3 : ℚ) / 8)
          (LRCompactVBoxSound.join (box := joinbox13_rRRRLLLLL) .chi ((311 : ℚ) / 320)
            subsound13_0
            subsound13_1)
          (LRCompactVBoxSound.join (box := joinbox13_rRRRLLLLR) .chi ((311 : ℚ) / 320)
            (LRCompactVBoxSound.join (box := joinbox13_rRRRLLLLRL) .s ((9 : ℚ) / 32)
              subsound13_2
              subsound13_3)
            (LRCompactVBoxSound.join (box := joinbox13_rRRRLLLLRR) .s ((9 : ℚ) / 32)
              subsound13_4
              subsound13_5)))
        (LRCompactVBoxSound.join (box := joinbox13_rRRRLLLR) .k ((3 : ℚ) / 8)
          (LRCompactVBoxSound.join (box := joinbox13_rRRRLLLRL) .chi ((311 : ℚ) / 320)
            (LRCompactVBoxSound.join (box := joinbox13_rRRRLLLRLL) .s ((11 : ℚ) / 32)
              subsound13_6
              subsound13_7)
            (LRCompactVBoxSound.join (box := joinbox13_rRRRLLLRLR) .s ((11 : ℚ) / 32)
              subsound13_8
              subsound13_9))
          (LRCompactVBoxSound.join (box := joinbox13_rRRRLLLRR) .chi ((311 : ℚ) / 320)
            (LRCompactVBoxSound.join (box := joinbox13_rRRRLLLRRL) .s ((11 : ℚ) / 32)
              subsound13_10
              subsound13_11)
            (LRCompactVBoxSound.join (box := joinbox13_rRRRLLLRRR) .s ((11 : ℚ) / 32)
              subsound13_12
              subsound13_13))))
      (LRCompactVBoxSound.join (box := joinbox13_rRRRLLR) .s ((5 : ℚ) / 16)
        (LRCompactVBoxSound.join (box := joinbox13_rRRRLLRL) .k ((3 : ℚ) / 8)
          (LRCompactVBoxSound.join (box := joinbox13_rRRRLLRLL) .chi ((317 : ℚ) / 320)
            subsound13_14
            subsound13_15)
          (LRCompactVBoxSound.join (box := joinbox13_rRRRLLRLR) .chi ((317 : ℚ) / 320)
            (LRCompactVBoxSound.join (box := joinbox13_rRRRLLRLRL) .s ((9 : ℚ) / 32)
              subsound13_16
              subsound13_17)
            subsound13_18))
        (LRCompactVBoxSound.join (box := joinbox13_rRRRLLRR) .k ((3 : ℚ) / 8)
          (LRCompactVBoxSound.join (box := joinbox13_rRRRLLRRL) .chi ((317 : ℚ) / 320)
            (LRCompactVBoxSound.join (box := joinbox13_rRRRLLRRLL) .s ((11 : ℚ) / 32)
              subsound13_19
              subsound13_20)
            (LRCompactVBoxSound.join (box := joinbox13_rRRRLLRRLR) .s ((11 : ℚ) / 32)
              subsound13_21
              subsound13_22))
          (LRCompactVBoxSound.join (box := joinbox13_rRRRLLRRR) .chi ((317 : ℚ) / 320)
            (LRCompactVBoxSound.join (box := joinbox13_rRRRLLRRRL) .s ((11 : ℚ) / 32)
              subsound13_23
              subsound13_24)
            (LRCompactVBoxSound.join (box := joinbox13_rRRRLLRRRR) .s ((11 : ℚ) / 32)
              subsound13_25
              subsound13_26)))))
    (LRCompactVBoxSound.join (box := joinbox13_rRRRLR) .chi ((157 : ℚ) / 160)
      (LRCompactVBoxSound.join (box := joinbox13_rRRRLRL) .s ((5 : ℚ) / 16)
        (LRCompactVBoxSound.join (box := joinbox13_rRRRLRLL) .k ((11 : ℚ) / 24)
          (LRCompactVBoxSound.join (box := joinbox13_rRRRLRLLL) .chi ((311 : ℚ) / 320)
            (LRCompactVBoxSound.join (box := joinbox13_rRRRLRLLLL) .s ((9 : ℚ) / 32)
              subsound13_27
              subsound13_28)
            (LRCompactVBoxSound.join (box := joinbox13_rRRRLRLLLR) .s ((9 : ℚ) / 32)
              subsound13_29
              subsound13_30))
          (LRCompactVBoxSound.join (box := joinbox13_rRRRLRLLR) .chi ((311 : ℚ) / 320)
            (LRCompactVBoxSound.join (box := joinbox13_rRRRLRLLRL) .s ((9 : ℚ) / 32)
              subsound13_31
              subsound13_32)
            (LRCompactVBoxSound.join (box := joinbox13_rRRRLRLLRR) .s ((9 : ℚ) / 32)
              subsound13_33
              subsound13_34)))
        (LRCompactVBoxSound.join (box := joinbox13_rRRRLRLR) .k ((11 : ℚ) / 24)
          (LRCompactVBoxSound.join (box := joinbox13_rRRRLRLRL) .chi ((311 : ℚ) / 320)
            (LRCompactVBoxSound.join (box := joinbox13_rRRRLRLRLL) .s ((11 : ℚ) / 32)
              subsound13_35
              subsound13_36)
            (LRCompactVBoxSound.join (box := joinbox13_rRRRLRLRLR) .s ((11 : ℚ) / 32)
              subsound13_37
              subsound13_38))
          (LRCompactVBoxSound.join (box := joinbox13_rRRRLRLRR) .chi ((311 : ℚ) / 320)
            (LRCompactVBoxSound.join (box := joinbox13_rRRRLRLRRL) .s ((11 : ℚ) / 32)
              (LRCompactVBoxSound.join (box := joinbox13_rRRRLRLRRLL) .k ((23 : ℚ) / 48)
                subsound13_39
                subsound13_40)
              (LRCompactVBoxSound.join (box := joinbox13_rRRRLRLRRLR) .k ((23 : ℚ) / 48)
                subsound13_41
                subsound13_42))
            (LRCompactVBoxSound.join (box := joinbox13_rRRRLRLRRR) .s ((11 : ℚ) / 32)
              subsound13_43
              (LRCompactVBoxSound.join (box := joinbox13_rRRRLRLRRRR) .k ((23 : ℚ) / 48)
                subsound13_44
                subsound13_45)))))
      (LRCompactVBoxSound.join (box := joinbox13_rRRRLRR) .s ((5 : ℚ) / 16)
        (LRCompactVBoxSound.join (box := joinbox13_rRRRLRRL) .k ((11 : ℚ) / 24)
          (LRCompactVBoxSound.join (box := joinbox13_rRRRLRRLL) .chi ((317 : ℚ) / 320)
            (LRCompactVBoxSound.join (box := joinbox13_rRRRLRRLLL) .s ((9 : ℚ) / 32)
              subsound13_46
              subsound13_47)
            (LRCompactVBoxSound.join (box := joinbox13_rRRRLRRLLR) .s ((9 : ℚ) / 32)
              subsound13_48
              subsound13_49))
          (LRCompactVBoxSound.join (box := joinbox13_rRRRLRRLR) .chi ((317 : ℚ) / 320)
            (LRCompactVBoxSound.join (box := joinbox13_rRRRLRRLRL) .s ((9 : ℚ) / 32)
              subsound13_50
              subsound13_51)
            (LRCompactVBoxSound.join (box := joinbox13_rRRRLRRLRR) .s ((9 : ℚ) / 32)
              subsound13_52
              subsound13_53)))
        (LRCompactVBoxSound.join (box := joinbox13_rRRRLRRR) .k ((11 : ℚ) / 24)
          (LRCompactVBoxSound.join (box := joinbox13_rRRRLRRRL) .chi ((317 : ℚ) / 320)
            (LRCompactVBoxSound.join (box := joinbox13_rRRRLRRRLL) .s ((11 : ℚ) / 32)
              subsound13_54
              subsound13_55)
            (LRCompactVBoxSound.join (box := joinbox13_rRRRLRRRLR) .s ((11 : ℚ) / 32)
              subsound13_56
              subsound13_57))
          (LRCompactVBoxSound.join (box := joinbox13_rRRRLRRRR) .chi ((317 : ℚ) / 320)
            (LRCompactVBoxSound.join (box := joinbox13_rRRRLRRRRL) .s ((11 : ℚ) / 32)
              subsound13_58
              (LRCompactVBoxSound.join (box := joinbox13_rRRRLRRRRLR) .k ((23 : ℚ) / 48)
                subsound13_59
                subsound13_60))
            (LRCompactVBoxSound.join (box := joinbox13_rRRRLRRRRR) .s ((11 : ℚ) / 32)
              subsound13_61
              subsound13_62))))))

end CourtadeKumar.GeneratedLRCompactVLowR
