import InformationTheory.CourtadeKumar.LRCompactVBasicReplay

/-! Frozen basic compact-V replay.
Plan SHA-256: ce3f7a498b2b9caf346dcf88ce7861f8cc091af8cd93f5624d7684e21322ecd5
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CourtadeKumar.GeneratedLRCompactVLowR

-- 123 accepted leaves below path rLRLL.
def box3 : CertificateBox where
  sLo := ((1 : ℚ) / 4)
  sHi := ((3 : ℚ) / 8)
  kLo := ((1 : ℚ) / 3)
  kHi := ((1 : ℚ) / 2)
  chiLo := ((17 : ℚ) / 20)
  chiHi := ((71 : ℚ) / 80)


def subbox3_0 : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((9 : ℚ) / 32), ((1 : ℚ) / 3), ((17 : ℚ) / 48), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩

theorem checked3_0 :
    LRCompactVLeafParameters.check subbox3_0 .short = true := by decide +kernel

theorem subsound3_0 : LRCompactVBoxSound subbox3_0 :=
  LRCompactVLeafParameters.sound checked3_0


def subbox3_1 : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((9 : ℚ) / 32), ((17 : ℚ) / 48), ((3 : ℚ) / 8), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩

theorem checked3_1 :
    LRCompactVLeafParameters.check subbox3_1 .short = true := by decide +kernel

theorem subsound3_1 : LRCompactVBoxSound subbox3_1 :=
  LRCompactVLeafParameters.sound checked3_1


def subbox3_2 : CertificateBox :=
  ⟨((9 : ℚ) / 32), ((5 : ℚ) / 16), ((1 : ℚ) / 3), ((17 : ℚ) / 48), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩

theorem checked3_2 :
    LRCompactVLeafParameters.check subbox3_2 .short = true := by decide +kernel

theorem subsound3_2 : LRCompactVBoxSound subbox3_2 :=
  LRCompactVLeafParameters.sound checked3_2


def subbox3_3 : CertificateBox :=
  ⟨((9 : ℚ) / 32), ((5 : ℚ) / 16), ((17 : ℚ) / 48), ((3 : ℚ) / 8), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩

theorem checked3_3 :
    LRCompactVLeafParameters.check subbox3_3 .short = true := by decide +kernel

theorem subsound3_3 : LRCompactVBoxSound subbox3_3 :=
  LRCompactVLeafParameters.sound checked3_3


def subbox3_4 : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((9 : ℚ) / 32), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩

theorem checked3_4 :
    LRCompactVLeafParameters.check subbox3_4 .long = true := by decide +kernel

theorem subsound3_4 : LRCompactVBoxSound subbox3_4 :=
  LRCompactVLeafParameters.sound checked3_4


def subbox3_5 : CertificateBox :=
  ⟨((9 : ℚ) / 32), ((5 : ℚ) / 16), ((1 : ℚ) / 3), ((17 : ℚ) / 48), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩

theorem checked3_5 :
    LRCompactVLeafParameters.check subbox3_5 .short = true := by decide +kernel

theorem subsound3_5 : LRCompactVBoxSound subbox3_5 :=
  LRCompactVLeafParameters.sound checked3_5


def subbox3_6 : CertificateBox :=
  ⟨((9 : ℚ) / 32), ((5 : ℚ) / 16), ((17 : ℚ) / 48), ((3 : ℚ) / 8), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩

theorem checked3_6 :
    LRCompactVLeafParameters.check subbox3_6 .short = true := by decide +kernel

theorem subsound3_6 : LRCompactVBoxSound subbox3_6 :=
  LRCompactVLeafParameters.sound checked3_6


def subbox3_7 : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((9 : ℚ) / 32), ((3 : ℚ) / 8), ((19 : ℚ) / 48), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩

theorem checked3_7 :
    LRCompactVLeafParameters.check subbox3_7 .short = true := by decide +kernel

theorem subsound3_7 : LRCompactVBoxSound subbox3_7 :=
  LRCompactVLeafParameters.sound checked3_7


def subbox3_8 : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((9 : ℚ) / 32), ((19 : ℚ) / 48), ((5 : ℚ) / 12), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩

theorem checked3_8 :
    LRCompactVLeafParameters.check subbox3_8 .short = true := by decide +kernel

theorem subsound3_8 : LRCompactVBoxSound subbox3_8 :=
  LRCompactVLeafParameters.sound checked3_8


def subbox3_9 : CertificateBox :=
  ⟨((9 : ℚ) / 32), ((5 : ℚ) / 16), ((3 : ℚ) / 8), ((19 : ℚ) / 48), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩

theorem checked3_9 :
    LRCompactVLeafParameters.check subbox3_9 .short = true := by decide +kernel

theorem subsound3_9 : LRCompactVBoxSound subbox3_9 :=
  LRCompactVLeafParameters.sound checked3_9


def subbox3_10 : CertificateBox :=
  ⟨((9 : ℚ) / 32), ((5 : ℚ) / 16), ((19 : ℚ) / 48), ((5 : ℚ) / 12), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩

theorem checked3_10 :
    LRCompactVLeafParameters.check subbox3_10 .short = true := by decide +kernel

theorem subsound3_10 : LRCompactVBoxSound subbox3_10 :=
  LRCompactVLeafParameters.sound checked3_10


def subbox3_11 : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((9 : ℚ) / 32), ((3 : ℚ) / 8), ((19 : ℚ) / 48), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩

theorem checked3_11 :
    LRCompactVLeafParameters.check subbox3_11 .short = true := by decide +kernel

theorem subsound3_11 : LRCompactVBoxSound subbox3_11 :=
  LRCompactVLeafParameters.sound checked3_11


def subbox3_12 : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((9 : ℚ) / 32), ((19 : ℚ) / 48), ((5 : ℚ) / 12), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩

theorem checked3_12 :
    LRCompactVLeafParameters.check subbox3_12 .short = true := by decide +kernel

theorem subsound3_12 : LRCompactVBoxSound subbox3_12 :=
  LRCompactVLeafParameters.sound checked3_12


def subbox3_13 : CertificateBox :=
  ⟨((9 : ℚ) / 32), ((5 : ℚ) / 16), ((3 : ℚ) / 8), ((19 : ℚ) / 48), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩

theorem checked3_13 :
    LRCompactVLeafParameters.check subbox3_13 .short = true := by decide +kernel

theorem subsound3_13 : LRCompactVBoxSound subbox3_13 :=
  LRCompactVLeafParameters.sound checked3_13


def subbox3_14 : CertificateBox :=
  ⟨((9 : ℚ) / 32), ((5 : ℚ) / 16), ((19 : ℚ) / 48), ((5 : ℚ) / 12), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩

theorem checked3_14 :
    LRCompactVLeafParameters.check subbox3_14 .short = true := by decide +kernel

theorem subsound3_14 : LRCompactVBoxSound subbox3_14 :=
  LRCompactVLeafParameters.sound checked3_14


def subbox3_15 : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((1 : ℚ) / 3), ((17 : ℚ) / 48), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩

theorem checked3_15 :
    LRCompactVLeafParameters.check subbox3_15 .short = true := by decide +kernel

theorem subsound3_15 : LRCompactVBoxSound subbox3_15 :=
  LRCompactVLeafParameters.sound checked3_15


def subbox3_16 : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((17 : ℚ) / 48), ((3 : ℚ) / 8), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩

theorem checked3_16 :
    LRCompactVLeafParameters.check subbox3_16 .short = true := by decide +kernel

theorem subsound3_16 : LRCompactVBoxSound subbox3_16 :=
  LRCompactVLeafParameters.sound checked3_16


def subbox3_17 : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((1 : ℚ) / 3), ((17 : ℚ) / 48), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩

theorem checked3_17 :
    LRCompactVLeafParameters.check subbox3_17 .short = true := by decide +kernel

theorem subsound3_17 : LRCompactVBoxSound subbox3_17 :=
  LRCompactVLeafParameters.sound checked3_17


def subbox3_18 : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((17 : ℚ) / 48), ((3 : ℚ) / 8), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩

theorem checked3_18 :
    LRCompactVLeafParameters.check subbox3_18 .short = true := by decide +kernel

theorem subsound3_18 : LRCompactVBoxSound subbox3_18 :=
  LRCompactVLeafParameters.sound checked3_18


def subbox3_19 : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((1 : ℚ) / 3), ((17 : ℚ) / 48), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩

theorem checked3_19 :
    LRCompactVLeafParameters.check subbox3_19 .short = true := by decide +kernel

theorem subsound3_19 : LRCompactVBoxSound subbox3_19 :=
  LRCompactVLeafParameters.sound checked3_19


def subbox3_20 : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((17 : ℚ) / 48), ((3 : ℚ) / 8), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩

theorem checked3_20 :
    LRCompactVLeafParameters.check subbox3_20 .short = true := by decide +kernel

theorem subsound3_20 : LRCompactVBoxSound subbox3_20 :=
  LRCompactVLeafParameters.sound checked3_20


def subbox3_21 : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((1 : ℚ) / 3), ((17 : ℚ) / 48), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩

theorem checked3_21 :
    LRCompactVLeafParameters.check subbox3_21 .short = true := by decide +kernel

theorem subsound3_21 : LRCompactVBoxSound subbox3_21 :=
  LRCompactVLeafParameters.sound checked3_21


def subbox3_22 : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((17 : ℚ) / 48), ((3 : ℚ) / 8), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩

theorem checked3_22 :
    LRCompactVLeafParameters.check subbox3_22 .short = true := by decide +kernel

theorem subsound3_22 : LRCompactVBoxSound subbox3_22 :=
  LRCompactVLeafParameters.sound checked3_22


def subbox3_23 : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((3 : ℚ) / 8), ((19 : ℚ) / 48), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩

theorem checked3_23 :
    LRCompactVLeafParameters.check subbox3_23 .short = true := by decide +kernel

theorem subsound3_23 : LRCompactVBoxSound subbox3_23 :=
  LRCompactVLeafParameters.sound checked3_23


def subbox3_24 : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((19 : ℚ) / 48), ((5 : ℚ) / 12), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩

theorem checked3_24 :
    LRCompactVLeafParameters.check subbox3_24 .short = true := by decide +kernel

theorem subsound3_24 : LRCompactVBoxSound subbox3_24 :=
  LRCompactVLeafParameters.sound checked3_24


def subbox3_25 : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((3 : ℚ) / 8), ((19 : ℚ) / 48), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩

theorem checked3_25 :
    LRCompactVLeafParameters.check subbox3_25 .short = true := by decide +kernel

theorem subsound3_25 : LRCompactVBoxSound subbox3_25 :=
  LRCompactVLeafParameters.sound checked3_25


def subbox3_26 : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((19 : ℚ) / 48), ((5 : ℚ) / 12), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩

theorem checked3_26 :
    LRCompactVLeafParameters.check subbox3_26 .short = true := by decide +kernel

theorem subsound3_26 : LRCompactVBoxSound subbox3_26 :=
  LRCompactVLeafParameters.sound checked3_26


def subbox3_27 : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((3 : ℚ) / 8), ((19 : ℚ) / 48), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩

theorem checked3_27 :
    LRCompactVLeafParameters.check subbox3_27 .short = true := by decide +kernel

theorem subsound3_27 : LRCompactVBoxSound subbox3_27 :=
  LRCompactVLeafParameters.sound checked3_27


def subbox3_28 : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((19 : ℚ) / 48), ((5 : ℚ) / 12), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩

theorem checked3_28 :
    LRCompactVLeafParameters.check subbox3_28 .short = true := by decide +kernel

theorem subsound3_28 : LRCompactVBoxSound subbox3_28 :=
  LRCompactVLeafParameters.sound checked3_28


def subbox3_29 : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((3 : ℚ) / 8), ((19 : ℚ) / 48), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩

theorem checked3_29 :
    LRCompactVLeafParameters.check subbox3_29 .short = true := by decide +kernel

theorem subsound3_29 : LRCompactVBoxSound subbox3_29 :=
  LRCompactVLeafParameters.sound checked3_29


def subbox3_30 : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((19 : ℚ) / 48), ((5 : ℚ) / 12), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩

theorem checked3_30 :
    LRCompactVLeafParameters.check subbox3_30 .short = true := by decide +kernel

theorem subsound3_30 : LRCompactVBoxSound subbox3_30 :=
  LRCompactVLeafParameters.sound checked3_30


def subbox3_31 : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((9 : ℚ) / 32), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩

theorem checked3_31 :
    LRCompactVLeafParameters.check subbox3_31 .long = true := by decide +kernel

theorem subsound3_31 : LRCompactVBoxSound subbox3_31 :=
  LRCompactVLeafParameters.sound checked3_31


def subbox3_32 : CertificateBox :=
  ⟨((9 : ℚ) / 32), ((5 : ℚ) / 16), ((1 : ℚ) / 3), ((17 : ℚ) / 48), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩

theorem checked3_32 :
    LRCompactVLeafParameters.check subbox3_32 .short = true := by decide +kernel

theorem subsound3_32 : LRCompactVBoxSound subbox3_32 :=
  LRCompactVLeafParameters.sound checked3_32


def subbox3_33 : CertificateBox :=
  ⟨((9 : ℚ) / 32), ((5 : ℚ) / 16), ((17 : ℚ) / 48), ((3 : ℚ) / 8), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩

theorem checked3_33 :
    LRCompactVLeafParameters.check subbox3_33 .short = true := by decide +kernel

theorem subsound3_33 : LRCompactVBoxSound subbox3_33 :=
  LRCompactVLeafParameters.sound checked3_33


def subbox3_34 : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((9 : ℚ) / 32), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩

theorem checked3_34 :
    LRCompactVLeafParameters.check subbox3_34 .short = true := by decide +kernel

theorem subsound3_34 : LRCompactVBoxSound subbox3_34 :=
  LRCompactVLeafParameters.sound checked3_34


def subbox3_35 : CertificateBox :=
  ⟨((9 : ℚ) / 32), ((5 : ℚ) / 16), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩

theorem checked3_35 :
    LRCompactVLeafParameters.check subbox3_35 .long = true := by decide +kernel

theorem subsound3_35 : LRCompactVBoxSound subbox3_35 :=
  LRCompactVLeafParameters.sound checked3_35


def subbox3_36 : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((9 : ℚ) / 32), ((3 : ℚ) / 8), ((19 : ℚ) / 48), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩

theorem checked3_36 :
    LRCompactVLeafParameters.check subbox3_36 .short = true := by decide +kernel

theorem subsound3_36 : LRCompactVBoxSound subbox3_36 :=
  LRCompactVLeafParameters.sound checked3_36


def subbox3_37 : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((9 : ℚ) / 32), ((19 : ℚ) / 48), ((5 : ℚ) / 12), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩

theorem checked3_37 :
    LRCompactVLeafParameters.check subbox3_37 .short = true := by decide +kernel

theorem subsound3_37 : LRCompactVBoxSound subbox3_37 :=
  LRCompactVLeafParameters.sound checked3_37


def subbox3_38 : CertificateBox :=
  ⟨((9 : ℚ) / 32), ((5 : ℚ) / 16), ((3 : ℚ) / 8), ((19 : ℚ) / 48), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩

theorem checked3_38 :
    LRCompactVLeafParameters.check subbox3_38 .short = true := by decide +kernel

theorem subsound3_38 : LRCompactVBoxSound subbox3_38 :=
  LRCompactVLeafParameters.sound checked3_38


def subbox3_39 : CertificateBox :=
  ⟨((9 : ℚ) / 32), ((5 : ℚ) / 16), ((19 : ℚ) / 48), ((5 : ℚ) / 12), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩

theorem checked3_39 :
    LRCompactVLeafParameters.check subbox3_39 .short = true := by decide +kernel

theorem subsound3_39 : LRCompactVBoxSound subbox3_39 :=
  LRCompactVLeafParameters.sound checked3_39


def subbox3_40 : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((9 : ℚ) / 32), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩

theorem checked3_40 :
    LRCompactVLeafParameters.check subbox3_40 .long = true := by decide +kernel

theorem subsound3_40 : LRCompactVBoxSound subbox3_40 :=
  LRCompactVLeafParameters.sound checked3_40


def subbox3_41 : CertificateBox :=
  ⟨((9 : ℚ) / 32), ((5 : ℚ) / 16), ((3 : ℚ) / 8), ((19 : ℚ) / 48), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩

theorem checked3_41 :
    LRCompactVLeafParameters.check subbox3_41 .short = true := by decide +kernel

theorem subsound3_41 : LRCompactVBoxSound subbox3_41 :=
  LRCompactVLeafParameters.sound checked3_41


def subbox3_42 : CertificateBox :=
  ⟨((9 : ℚ) / 32), ((5 : ℚ) / 16), ((19 : ℚ) / 48), ((5 : ℚ) / 12), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩

theorem checked3_42 :
    LRCompactVLeafParameters.check subbox3_42 .short = true := by decide +kernel

theorem subsound3_42 : LRCompactVBoxSound subbox3_42 :=
  LRCompactVLeafParameters.sound checked3_42


def subbox3_43 : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((1 : ℚ) / 3), ((17 : ℚ) / 48), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩

theorem checked3_43 :
    LRCompactVLeafParameters.check subbox3_43 .short = true := by decide +kernel

theorem subsound3_43 : LRCompactVBoxSound subbox3_43 :=
  LRCompactVLeafParameters.sound checked3_43


def subbox3_44 : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((17 : ℚ) / 48), ((3 : ℚ) / 8), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩

theorem checked3_44 :
    LRCompactVLeafParameters.check subbox3_44 .short = true := by decide +kernel

theorem subsound3_44 : LRCompactVBoxSound subbox3_44 :=
  LRCompactVLeafParameters.sound checked3_44


def subbox3_45 : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((1 : ℚ) / 3), ((17 : ℚ) / 48), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩

theorem checked3_45 :
    LRCompactVLeafParameters.check subbox3_45 .short = true := by decide +kernel

theorem subsound3_45 : LRCompactVBoxSound subbox3_45 :=
  LRCompactVLeafParameters.sound checked3_45


def subbox3_46 : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((17 : ℚ) / 48), ((3 : ℚ) / 8), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩

theorem checked3_46 :
    LRCompactVLeafParameters.check subbox3_46 .short = true := by decide +kernel

theorem subsound3_46 : LRCompactVBoxSound subbox3_46 :=
  LRCompactVLeafParameters.sound checked3_46


def subbox3_47 : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((1 : ℚ) / 3), ((17 : ℚ) / 48), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩

theorem checked3_47 :
    LRCompactVLeafParameters.check subbox3_47 .short = true := by decide +kernel

theorem subsound3_47 : LRCompactVBoxSound subbox3_47 :=
  LRCompactVLeafParameters.sound checked3_47


def subbox3_48 : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((17 : ℚ) / 48), ((3 : ℚ) / 8), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩

theorem checked3_48 :
    LRCompactVLeafParameters.check subbox3_48 .short = true := by decide +kernel

theorem subsound3_48 : LRCompactVBoxSound subbox3_48 :=
  LRCompactVLeafParameters.sound checked3_48


def subbox3_49 : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((1 : ℚ) / 3), ((17 : ℚ) / 48), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩

theorem checked3_49 :
    LRCompactVLeafParameters.check subbox3_49 .short = true := by decide +kernel

theorem subsound3_49 : LRCompactVBoxSound subbox3_49 :=
  LRCompactVLeafParameters.sound checked3_49


def subbox3_50 : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((17 : ℚ) / 48), ((3 : ℚ) / 8), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩

theorem checked3_50 :
    LRCompactVLeafParameters.check subbox3_50 .short = true := by decide +kernel

theorem subsound3_50 : LRCompactVBoxSound subbox3_50 :=
  LRCompactVLeafParameters.sound checked3_50


def subbox3_51 : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((3 : ℚ) / 8), ((19 : ℚ) / 48), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩

theorem checked3_51 :
    LRCompactVLeafParameters.check subbox3_51 .short = true := by decide +kernel

theorem subsound3_51 : LRCompactVBoxSound subbox3_51 :=
  LRCompactVLeafParameters.sound checked3_51


def subbox3_52 : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((19 : ℚ) / 48), ((5 : ℚ) / 12), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩

theorem checked3_52 :
    LRCompactVLeafParameters.check subbox3_52 .short = true := by decide +kernel

theorem subsound3_52 : LRCompactVBoxSound subbox3_52 :=
  LRCompactVLeafParameters.sound checked3_52


def subbox3_53 : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((3 : ℚ) / 8), ((19 : ℚ) / 48), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩

theorem checked3_53 :
    LRCompactVLeafParameters.check subbox3_53 .short = true := by decide +kernel

theorem subsound3_53 : LRCompactVBoxSound subbox3_53 :=
  LRCompactVLeafParameters.sound checked3_53


def subbox3_54 : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((19 : ℚ) / 48), ((5 : ℚ) / 12), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩

theorem checked3_54 :
    LRCompactVLeafParameters.check subbox3_54 .short = true := by decide +kernel

theorem subsound3_54 : LRCompactVBoxSound subbox3_54 :=
  LRCompactVLeafParameters.sound checked3_54


def subbox3_55 : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((3 : ℚ) / 8), ((19 : ℚ) / 48), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩

theorem checked3_55 :
    LRCompactVLeafParameters.check subbox3_55 .short = true := by decide +kernel

theorem subsound3_55 : LRCompactVBoxSound subbox3_55 :=
  LRCompactVLeafParameters.sound checked3_55


def subbox3_56 : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((19 : ℚ) / 48), ((5 : ℚ) / 12), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩

theorem checked3_56 :
    LRCompactVLeafParameters.check subbox3_56 .short = true := by decide +kernel

theorem subsound3_56 : LRCompactVBoxSound subbox3_56 :=
  LRCompactVLeafParameters.sound checked3_56


def subbox3_57 : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((3 : ℚ) / 8), ((19 : ℚ) / 48), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩

theorem checked3_57 :
    LRCompactVLeafParameters.check subbox3_57 .short = true := by decide +kernel

theorem subsound3_57 : LRCompactVBoxSound subbox3_57 :=
  LRCompactVLeafParameters.sound checked3_57


def subbox3_58 : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((19 : ℚ) / 48), ((5 : ℚ) / 12), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩

theorem checked3_58 :
    LRCompactVLeafParameters.check subbox3_58 .short = true := by decide +kernel

theorem subsound3_58 : LRCompactVBoxSound subbox3_58 :=
  LRCompactVLeafParameters.sound checked3_58


def subbox3_59 : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((9 : ℚ) / 32), ((5 : ℚ) / 12), ((7 : ℚ) / 16), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩

theorem checked3_59 :
    LRCompactVLeafParameters.check subbox3_59 .short = true := by decide +kernel

theorem subsound3_59 : LRCompactVBoxSound subbox3_59 :=
  LRCompactVLeafParameters.sound checked3_59


def subbox3_60 : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((9 : ℚ) / 32), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩

theorem checked3_60 :
    LRCompactVLeafParameters.check subbox3_60 .short = true := by decide +kernel

theorem subsound3_60 : LRCompactVBoxSound subbox3_60 :=
  LRCompactVLeafParameters.sound checked3_60


def subbox3_61 : CertificateBox :=
  ⟨((9 : ℚ) / 32), ((5 : ℚ) / 16), ((5 : ℚ) / 12), ((7 : ℚ) / 16), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩

theorem checked3_61 :
    LRCompactVLeafParameters.check subbox3_61 .short = true := by decide +kernel

theorem subsound3_61 : LRCompactVBoxSound subbox3_61 :=
  LRCompactVLeafParameters.sound checked3_61


def subbox3_62 : CertificateBox :=
  ⟨((9 : ℚ) / 32), ((5 : ℚ) / 16), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩

theorem checked3_62 :
    LRCompactVLeafParameters.check subbox3_62 .short = true := by decide +kernel

theorem subsound3_62 : LRCompactVBoxSound subbox3_62 :=
  LRCompactVLeafParameters.sound checked3_62


def subbox3_63 : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((9 : ℚ) / 32), ((5 : ℚ) / 12), ((7 : ℚ) / 16), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩

theorem checked3_63 :
    LRCompactVLeafParameters.check subbox3_63 .short = true := by decide +kernel

theorem subsound3_63 : LRCompactVBoxSound subbox3_63 :=
  LRCompactVLeafParameters.sound checked3_63


def subbox3_64 : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((9 : ℚ) / 32), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩

theorem checked3_64 :
    LRCompactVLeafParameters.check subbox3_64 .short = true := by decide +kernel

theorem subsound3_64 : LRCompactVBoxSound subbox3_64 :=
  LRCompactVLeafParameters.sound checked3_64


def subbox3_65 : CertificateBox :=
  ⟨((9 : ℚ) / 32), ((5 : ℚ) / 16), ((5 : ℚ) / 12), ((7 : ℚ) / 16), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩

theorem checked3_65 :
    LRCompactVLeafParameters.check subbox3_65 .short = true := by decide +kernel

theorem subsound3_65 : LRCompactVBoxSound subbox3_65 :=
  LRCompactVLeafParameters.sound checked3_65


def subbox3_66 : CertificateBox :=
  ⟨((9 : ℚ) / 32), ((5 : ℚ) / 16), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩

theorem checked3_66 :
    LRCompactVLeafParameters.check subbox3_66 .short = true := by decide +kernel

theorem subsound3_66 : LRCompactVBoxSound subbox3_66 :=
  LRCompactVLeafParameters.sound checked3_66


def subbox3_67 : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((9 : ℚ) / 32), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩

theorem checked3_67 :
    LRCompactVLeafParameters.check subbox3_67 .short = true := by decide +kernel

theorem subsound3_67 : LRCompactVBoxSound subbox3_67 :=
  LRCompactVLeafParameters.sound checked3_67


def subbox3_68 : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((9 : ℚ) / 32), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩

theorem checked3_68 :
    LRCompactVLeafParameters.check subbox3_68 .short = true := by decide +kernel

theorem subsound3_68 : LRCompactVBoxSound subbox3_68 :=
  LRCompactVLeafParameters.sound checked3_68


def subbox3_69 : CertificateBox :=
  ⟨((9 : ℚ) / 32), ((5 : ℚ) / 16), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩

theorem checked3_69 :
    LRCompactVLeafParameters.check subbox3_69 .short = true := by decide +kernel

theorem subsound3_69 : LRCompactVBoxSound subbox3_69 :=
  LRCompactVLeafParameters.sound checked3_69


def subbox3_70 : CertificateBox :=
  ⟨((9 : ℚ) / 32), ((5 : ℚ) / 16), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩

theorem checked3_70 :
    LRCompactVLeafParameters.check subbox3_70 .short = true := by decide +kernel

theorem subsound3_70 : LRCompactVBoxSound subbox3_70 :=
  LRCompactVLeafParameters.sound checked3_70


def subbox3_71 : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((9 : ℚ) / 32), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩

theorem checked3_71 :
    LRCompactVLeafParameters.check subbox3_71 .short = true := by decide +kernel

theorem subsound3_71 : LRCompactVBoxSound subbox3_71 :=
  LRCompactVLeafParameters.sound checked3_71


def subbox3_72 : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((9 : ℚ) / 32), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩

theorem checked3_72 :
    LRCompactVLeafParameters.check subbox3_72 .short = true := by decide +kernel

theorem subsound3_72 : LRCompactVBoxSound subbox3_72 :=
  LRCompactVLeafParameters.sound checked3_72


def subbox3_73 : CertificateBox :=
  ⟨((9 : ℚ) / 32), ((5 : ℚ) / 16), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩

theorem checked3_73 :
    LRCompactVLeafParameters.check subbox3_73 .short = true := by decide +kernel

theorem subsound3_73 : LRCompactVBoxSound subbox3_73 :=
  LRCompactVLeafParameters.sound checked3_73


def subbox3_74 : CertificateBox :=
  ⟨((9 : ℚ) / 32), ((5 : ℚ) / 16), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩

theorem checked3_74 :
    LRCompactVLeafParameters.check subbox3_74 .short = true := by decide +kernel

theorem subsound3_74 : LRCompactVBoxSound subbox3_74 :=
  LRCompactVLeafParameters.sound checked3_74


def subbox3_75 : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((5 : ℚ) / 12), ((7 : ℚ) / 16), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩

theorem checked3_75 :
    LRCompactVLeafParameters.check subbox3_75 .short = true := by decide +kernel

theorem subsound3_75 : LRCompactVBoxSound subbox3_75 :=
  LRCompactVLeafParameters.sound checked3_75


def subbox3_76 : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩

theorem checked3_76 :
    LRCompactVLeafParameters.check subbox3_76 .short = true := by decide +kernel

theorem subsound3_76 : LRCompactVBoxSound subbox3_76 :=
  LRCompactVLeafParameters.sound checked3_76


def subbox3_77 : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((7 : ℚ) / 16), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩

theorem checked3_77 :
    LRCompactVLeafParameters.check subbox3_77 .short = true := by decide +kernel

theorem subsound3_77 : LRCompactVBoxSound subbox3_77 :=
  LRCompactVLeafParameters.sound checked3_77


def subbox3_78 : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩

theorem checked3_78 :
    LRCompactVLeafParameters.check subbox3_78 .short = true := by decide +kernel

theorem subsound3_78 : LRCompactVBoxSound subbox3_78 :=
  LRCompactVLeafParameters.sound checked3_78


def subbox3_79 : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((5 : ℚ) / 12), ((7 : ℚ) / 16), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩

theorem checked3_79 :
    LRCompactVLeafParameters.check subbox3_79 .short = true := by decide +kernel

theorem subsound3_79 : LRCompactVBoxSound subbox3_79 :=
  LRCompactVLeafParameters.sound checked3_79


def subbox3_80 : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩

theorem checked3_80 :
    LRCompactVLeafParameters.check subbox3_80 .short = true := by decide +kernel

theorem subsound3_80 : LRCompactVBoxSound subbox3_80 :=
  LRCompactVLeafParameters.sound checked3_80


def subbox3_81 : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((7 : ℚ) / 16), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩

theorem checked3_81 :
    LRCompactVLeafParameters.check subbox3_81 .short = true := by decide +kernel

theorem subsound3_81 : LRCompactVBoxSound subbox3_81 :=
  LRCompactVLeafParameters.sound checked3_81


def subbox3_82 : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩

theorem checked3_82 :
    LRCompactVLeafParameters.check subbox3_82 .short = true := by decide +kernel

theorem subsound3_82 : LRCompactVBoxSound subbox3_82 :=
  LRCompactVLeafParameters.sound checked3_82


def subbox3_83 : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩

theorem checked3_83 :
    LRCompactVLeafParameters.check subbox3_83 .short = true := by decide +kernel

theorem subsound3_83 : LRCompactVBoxSound subbox3_83 :=
  LRCompactVLeafParameters.sound checked3_83


def subbox3_84 : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩

theorem checked3_84 :
    LRCompactVLeafParameters.check subbox3_84 .short = true := by decide +kernel

theorem subsound3_84 : LRCompactVBoxSound subbox3_84 :=
  LRCompactVLeafParameters.sound checked3_84


def subbox3_85 : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩

theorem checked3_85 :
    LRCompactVLeafParameters.check subbox3_85 .short = true := by decide +kernel

theorem subsound3_85 : LRCompactVBoxSound subbox3_85 :=
  LRCompactVLeafParameters.sound checked3_85


def subbox3_86 : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩

theorem checked3_86 :
    LRCompactVLeafParameters.check subbox3_86 .short = true := by decide +kernel

theorem subsound3_86 : LRCompactVBoxSound subbox3_86 :=
  LRCompactVLeafParameters.sound checked3_86


def subbox3_87 : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩

theorem checked3_87 :
    LRCompactVLeafParameters.check subbox3_87 .short = true := by decide +kernel

theorem subsound3_87 : LRCompactVBoxSound subbox3_87 :=
  LRCompactVLeafParameters.sound checked3_87


def subbox3_88 : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩

theorem checked3_88 :
    LRCompactVLeafParameters.check subbox3_88 .short = true := by decide +kernel

theorem subsound3_88 : LRCompactVBoxSound subbox3_88 :=
  LRCompactVLeafParameters.sound checked3_88


def subbox3_89 : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩

theorem checked3_89 :
    LRCompactVLeafParameters.check subbox3_89 .short = true := by decide +kernel

theorem subsound3_89 : LRCompactVBoxSound subbox3_89 :=
  LRCompactVLeafParameters.sound checked3_89


def subbox3_90 : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩

theorem checked3_90 :
    LRCompactVLeafParameters.check subbox3_90 .short = true := by decide +kernel

theorem subsound3_90 : LRCompactVBoxSound subbox3_90 :=
  LRCompactVLeafParameters.sound checked3_90


def subbox3_91 : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((9 : ℚ) / 32), ((5 : ℚ) / 12), ((7 : ℚ) / 16), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩

theorem checked3_91 :
    LRCompactVLeafParameters.check subbox3_91 .short = true := by decide +kernel

theorem subsound3_91 : LRCompactVBoxSound subbox3_91 :=
  LRCompactVLeafParameters.sound checked3_91


def subbox3_92 : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((9 : ℚ) / 32), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩

theorem checked3_92 :
    LRCompactVLeafParameters.check subbox3_92 .short = true := by decide +kernel

theorem subsound3_92 : LRCompactVBoxSound subbox3_92 :=
  LRCompactVLeafParameters.sound checked3_92


def subbox3_93 : CertificateBox :=
  ⟨((9 : ℚ) / 32), ((5 : ℚ) / 16), ((5 : ℚ) / 12), ((7 : ℚ) / 16), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩

theorem checked3_93 :
    LRCompactVLeafParameters.check subbox3_93 .short = true := by decide +kernel

theorem subsound3_93 : LRCompactVBoxSound subbox3_93 :=
  LRCompactVLeafParameters.sound checked3_93


def subbox3_94 : CertificateBox :=
  ⟨((9 : ℚ) / 32), ((5 : ℚ) / 16), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩

theorem checked3_94 :
    LRCompactVLeafParameters.check subbox3_94 .short = true := by decide +kernel

theorem subsound3_94 : LRCompactVBoxSound subbox3_94 :=
  LRCompactVLeafParameters.sound checked3_94


def subbox3_95 : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((9 : ℚ) / 32), ((5 : ℚ) / 12), ((7 : ℚ) / 16), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩

theorem checked3_95 :
    LRCompactVLeafParameters.check subbox3_95 .short = true := by decide +kernel

theorem subsound3_95 : LRCompactVBoxSound subbox3_95 :=
  LRCompactVLeafParameters.sound checked3_95


def subbox3_96 : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((9 : ℚ) / 32), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩

theorem checked3_96 :
    LRCompactVLeafParameters.check subbox3_96 .short = true := by decide +kernel

theorem subsound3_96 : LRCompactVBoxSound subbox3_96 :=
  LRCompactVLeafParameters.sound checked3_96


def subbox3_97 : CertificateBox :=
  ⟨((9 : ℚ) / 32), ((5 : ℚ) / 16), ((5 : ℚ) / 12), ((7 : ℚ) / 16), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩

theorem checked3_97 :
    LRCompactVLeafParameters.check subbox3_97 .short = true := by decide +kernel

theorem subsound3_97 : LRCompactVBoxSound subbox3_97 :=
  LRCompactVLeafParameters.sound checked3_97


def subbox3_98 : CertificateBox :=
  ⟨((9 : ℚ) / 32), ((5 : ℚ) / 16), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩

theorem checked3_98 :
    LRCompactVLeafParameters.check subbox3_98 .short = true := by decide +kernel

theorem subsound3_98 : LRCompactVBoxSound subbox3_98 :=
  LRCompactVLeafParameters.sound checked3_98


def subbox3_99 : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((9 : ℚ) / 32), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩

theorem checked3_99 :
    LRCompactVLeafParameters.check subbox3_99 .short = true := by decide +kernel

theorem subsound3_99 : LRCompactVBoxSound subbox3_99 :=
  LRCompactVLeafParameters.sound checked3_99


def subbox3_100 : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((9 : ℚ) / 32), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩

theorem checked3_100 :
    LRCompactVLeafParameters.check subbox3_100 .short = true := by decide +kernel

theorem subsound3_100 : LRCompactVBoxSound subbox3_100 :=
  LRCompactVLeafParameters.sound checked3_100


def subbox3_101 : CertificateBox :=
  ⟨((9 : ℚ) / 32), ((5 : ℚ) / 16), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩

theorem checked3_101 :
    LRCompactVLeafParameters.check subbox3_101 .short = true := by decide +kernel

theorem subsound3_101 : LRCompactVBoxSound subbox3_101 :=
  LRCompactVLeafParameters.sound checked3_101


def subbox3_102 : CertificateBox :=
  ⟨((9 : ℚ) / 32), ((5 : ℚ) / 16), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩

theorem checked3_102 :
    LRCompactVLeafParameters.check subbox3_102 .short = true := by decide +kernel

theorem subsound3_102 : LRCompactVBoxSound subbox3_102 :=
  LRCompactVLeafParameters.sound checked3_102


def subbox3_103 : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((9 : ℚ) / 32), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩

theorem checked3_103 :
    LRCompactVLeafParameters.check subbox3_103 .short = true := by decide +kernel

theorem subsound3_103 : LRCompactVBoxSound subbox3_103 :=
  LRCompactVLeafParameters.sound checked3_103


def subbox3_104 : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((9 : ℚ) / 32), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩

theorem checked3_104 :
    LRCompactVLeafParameters.check subbox3_104 .short = true := by decide +kernel

theorem subsound3_104 : LRCompactVBoxSound subbox3_104 :=
  LRCompactVLeafParameters.sound checked3_104


def subbox3_105 : CertificateBox :=
  ⟨((9 : ℚ) / 32), ((5 : ℚ) / 16), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩

theorem checked3_105 :
    LRCompactVLeafParameters.check subbox3_105 .short = true := by decide +kernel

theorem subsound3_105 : LRCompactVBoxSound subbox3_105 :=
  LRCompactVLeafParameters.sound checked3_105


def subbox3_106 : CertificateBox :=
  ⟨((9 : ℚ) / 32), ((5 : ℚ) / 16), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩

theorem checked3_106 :
    LRCompactVLeafParameters.check subbox3_106 .short = true := by decide +kernel

theorem subsound3_106 : LRCompactVBoxSound subbox3_106 :=
  LRCompactVLeafParameters.sound checked3_106


def subbox3_107 : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((5 : ℚ) / 12), ((7 : ℚ) / 16), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩

theorem checked3_107 :
    LRCompactVLeafParameters.check subbox3_107 .short = true := by decide +kernel

theorem subsound3_107 : LRCompactVBoxSound subbox3_107 :=
  LRCompactVLeafParameters.sound checked3_107


def subbox3_108 : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩

theorem checked3_108 :
    LRCompactVLeafParameters.check subbox3_108 .short = true := by decide +kernel

theorem subsound3_108 : LRCompactVBoxSound subbox3_108 :=
  LRCompactVLeafParameters.sound checked3_108


def subbox3_109 : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((7 : ℚ) / 16), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩

theorem checked3_109 :
    LRCompactVLeafParameters.check subbox3_109 .short = true := by decide +kernel

theorem subsound3_109 : LRCompactVBoxSound subbox3_109 :=
  LRCompactVLeafParameters.sound checked3_109


def subbox3_110 : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩

theorem checked3_110 :
    LRCompactVLeafParameters.check subbox3_110 .short = true := by decide +kernel

theorem subsound3_110 : LRCompactVBoxSound subbox3_110 :=
  LRCompactVLeafParameters.sound checked3_110


def subbox3_111 : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((5 : ℚ) / 12), ((7 : ℚ) / 16), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩

theorem checked3_111 :
    LRCompactVLeafParameters.check subbox3_111 .short = true := by decide +kernel

theorem subsound3_111 : LRCompactVBoxSound subbox3_111 :=
  LRCompactVLeafParameters.sound checked3_111


def subbox3_112 : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩

theorem checked3_112 :
    LRCompactVLeafParameters.check subbox3_112 .short = true := by decide +kernel

theorem subsound3_112 : LRCompactVBoxSound subbox3_112 :=
  LRCompactVLeafParameters.sound checked3_112


def subbox3_113 : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((7 : ℚ) / 16), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩

theorem checked3_113 :
    LRCompactVLeafParameters.check subbox3_113 .short = true := by decide +kernel

theorem subsound3_113 : LRCompactVBoxSound subbox3_113 :=
  LRCompactVLeafParameters.sound checked3_113


def subbox3_114 : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩

theorem checked3_114 :
    LRCompactVLeafParameters.check subbox3_114 .short = true := by decide +kernel

theorem subsound3_114 : LRCompactVBoxSound subbox3_114 :=
  LRCompactVLeafParameters.sound checked3_114


def subbox3_115 : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩

theorem checked3_115 :
    LRCompactVLeafParameters.check subbox3_115 .short = true := by decide +kernel

theorem subsound3_115 : LRCompactVBoxSound subbox3_115 :=
  LRCompactVLeafParameters.sound checked3_115


def subbox3_116 : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩

theorem checked3_116 :
    LRCompactVLeafParameters.check subbox3_116 .short = true := by decide +kernel

theorem subsound3_116 : LRCompactVBoxSound subbox3_116 :=
  LRCompactVLeafParameters.sound checked3_116


def subbox3_117 : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩

theorem checked3_117 :
    LRCompactVLeafParameters.check subbox3_117 .short = true := by decide +kernel

theorem subsound3_117 : LRCompactVBoxSound subbox3_117 :=
  LRCompactVLeafParameters.sound checked3_117


def subbox3_118 : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩

theorem checked3_118 :
    LRCompactVLeafParameters.check subbox3_118 .short = true := by decide +kernel

theorem subsound3_118 : LRCompactVBoxSound subbox3_118 :=
  LRCompactVLeafParameters.sound checked3_118


def subbox3_119 : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩

theorem checked3_119 :
    LRCompactVLeafParameters.check subbox3_119 .short = true := by decide +kernel

theorem subsound3_119 : LRCompactVBoxSound subbox3_119 :=
  LRCompactVLeafParameters.sound checked3_119


def subbox3_120 : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩

theorem checked3_120 :
    LRCompactVLeafParameters.check subbox3_120 .short = true := by decide +kernel

theorem subsound3_120 : LRCompactVBoxSound subbox3_120 :=
  LRCompactVLeafParameters.sound checked3_120


def subbox3_121 : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩

theorem checked3_121 :
    LRCompactVLeafParameters.check subbox3_121 .short = true := by decide +kernel

theorem subsound3_121 : LRCompactVBoxSound subbox3_121 :=
  LRCompactVLeafParameters.sound checked3_121


def subbox3_122 : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩

theorem checked3_122 :
    LRCompactVLeafParameters.check subbox3_122 .short = true := by decide +kernel

theorem subsound3_122 : LRCompactVBoxSound subbox3_122 :=
  LRCompactVLeafParameters.sound checked3_122


def joinbox3_rLRLLL : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((3 : ℚ) / 8), ((1 : ℚ) / 3), ((5 : ℚ) / 12), ((17 : ℚ) / 20), ((71 : ℚ) / 80)⟩


def joinbox3_rLRLLLL : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((3 : ℚ) / 8), ((1 : ℚ) / 3), ((5 : ℚ) / 12), ((17 : ℚ) / 20), ((139 : ℚ) / 160)⟩


def joinbox3_rLRLLLLL : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((5 : ℚ) / 16), ((1 : ℚ) / 3), ((5 : ℚ) / 12), ((17 : ℚ) / 20), ((139 : ℚ) / 160)⟩


def joinbox3_rLRLLLLLL : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((5 : ℚ) / 16), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((17 : ℚ) / 20), ((139 : ℚ) / 160)⟩


def joinbox3_rLRLLLLLLL : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((5 : ℚ) / 16), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩


def joinbox3_rLRLLLLLLLL : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((9 : ℚ) / 32), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩


def joinbox3_rLRLLLLLLLR : CertificateBox :=
  ⟨((9 : ℚ) / 32), ((5 : ℚ) / 16), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩


def joinbox3_rLRLLLLLLR : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((5 : ℚ) / 16), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩


def joinbox3_rLRLLLLLLRR : CertificateBox :=
  ⟨((9 : ℚ) / 32), ((5 : ℚ) / 16), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩


def joinbox3_rLRLLLLLR : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((5 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((17 : ℚ) / 20), ((139 : ℚ) / 160)⟩


def joinbox3_rLRLLLLLRL : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((5 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩


def joinbox3_rLRLLLLLRLL : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((9 : ℚ) / 32), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩


def joinbox3_rLRLLLLLRLR : CertificateBox :=
  ⟨((9 : ℚ) / 32), ((5 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩


def joinbox3_rLRLLLLLRR : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((5 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩


def joinbox3_rLRLLLLLRRL : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((9 : ℚ) / 32), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩


def joinbox3_rLRLLLLLRRR : CertificateBox :=
  ⟨((9 : ℚ) / 32), ((5 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩


def joinbox3_rLRLLLLR : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((3 : ℚ) / 8), ((1 : ℚ) / 3), ((5 : ℚ) / 12), ((17 : ℚ) / 20), ((139 : ℚ) / 160)⟩


def joinbox3_rLRLLLLRL : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((3 : ℚ) / 8), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((17 : ℚ) / 20), ((139 : ℚ) / 160)⟩


def joinbox3_rLRLLLLRLL : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((3 : ℚ) / 8), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩


def joinbox3_rLRLLLLRLLL : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩


def joinbox3_rLRLLLLRLLR : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩


def joinbox3_rLRLLLLRLR : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((3 : ℚ) / 8), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩


def joinbox3_rLRLLLLRLRL : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩


def joinbox3_rLRLLLLRLRR : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩


def joinbox3_rLRLLLLRR : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((3 : ℚ) / 8), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((17 : ℚ) / 20), ((139 : ℚ) / 160)⟩


def joinbox3_rLRLLLLRRL : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((3 : ℚ) / 8), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩


def joinbox3_rLRLLLLRRLL : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩


def joinbox3_rLRLLLLRRLR : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩


def joinbox3_rLRLLLLRRR : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((3 : ℚ) / 8), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩


def joinbox3_rLRLLLLRRRL : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩


def joinbox3_rLRLLLLRRRR : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩


def joinbox3_rLRLLLR : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((3 : ℚ) / 8), ((1 : ℚ) / 3), ((5 : ℚ) / 12), ((139 : ℚ) / 160), ((71 : ℚ) / 80)⟩


def joinbox3_rLRLLLRL : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((5 : ℚ) / 16), ((1 : ℚ) / 3), ((5 : ℚ) / 12), ((139 : ℚ) / 160), ((71 : ℚ) / 80)⟩


def joinbox3_rLRLLLRLL : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((5 : ℚ) / 16), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((139 : ℚ) / 160), ((71 : ℚ) / 80)⟩


def joinbox3_rLRLLLRLLL : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((5 : ℚ) / 16), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩


def joinbox3_rLRLLLRLLLR : CertificateBox :=
  ⟨((9 : ℚ) / 32), ((5 : ℚ) / 16), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩


def joinbox3_rLRLLLRLLR : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((5 : ℚ) / 16), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩


def joinbox3_rLRLLLRLR : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((5 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((139 : ℚ) / 160), ((71 : ℚ) / 80)⟩


def joinbox3_rLRLLLRLRL : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((5 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩


def joinbox3_rLRLLLRLRLL : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((9 : ℚ) / 32), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩


def joinbox3_rLRLLLRLRLR : CertificateBox :=
  ⟨((9 : ℚ) / 32), ((5 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩


def joinbox3_rLRLLLRLRR : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((5 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩


def joinbox3_rLRLLLRLRRR : CertificateBox :=
  ⟨((9 : ℚ) / 32), ((5 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩


def joinbox3_rLRLLLRR : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((3 : ℚ) / 8), ((1 : ℚ) / 3), ((5 : ℚ) / 12), ((139 : ℚ) / 160), ((71 : ℚ) / 80)⟩


def joinbox3_rLRLLLRRL : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((3 : ℚ) / 8), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((139 : ℚ) / 160), ((71 : ℚ) / 80)⟩


def joinbox3_rLRLLLRRLL : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((3 : ℚ) / 8), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩


def joinbox3_rLRLLLRRLLL : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩


def joinbox3_rLRLLLRRLLR : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩


def joinbox3_rLRLLLRRLR : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((3 : ℚ) / 8), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩


def joinbox3_rLRLLLRRLRL : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩


def joinbox3_rLRLLLRRLRR : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩


def joinbox3_rLRLLLRRR : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((3 : ℚ) / 8), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((139 : ℚ) / 160), ((71 : ℚ) / 80)⟩


def joinbox3_rLRLLLRRRL : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((3 : ℚ) / 8), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩


def joinbox3_rLRLLLRRRLL : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩


def joinbox3_rLRLLLRRRLR : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩


def joinbox3_rLRLLLRRRR : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((3 : ℚ) / 8), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩


def joinbox3_rLRLLLRRRRL : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩


def joinbox3_rLRLLLRRRRR : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩


def joinbox3_rLRLLR : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((1 : ℚ) / 2), ((17 : ℚ) / 20), ((71 : ℚ) / 80)⟩


def joinbox3_rLRLLRL : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((1 : ℚ) / 2), ((17 : ℚ) / 20), ((139 : ℚ) / 160)⟩


def joinbox3_rLRLLRLL : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((5 : ℚ) / 16), ((5 : ℚ) / 12), ((1 : ℚ) / 2), ((17 : ℚ) / 20), ((139 : ℚ) / 160)⟩


def joinbox3_rLRLLRLLL : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((5 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((17 : ℚ) / 20), ((139 : ℚ) / 160)⟩


def joinbox3_rLRLLRLLLL : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((5 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩


def joinbox3_rLRLLRLLLLL : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((9 : ℚ) / 32), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩


def joinbox3_rLRLLRLLLLR : CertificateBox :=
  ⟨((9 : ℚ) / 32), ((5 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩


def joinbox3_rLRLLRLLLR : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((5 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩


def joinbox3_rLRLLRLLLRL : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((9 : ℚ) / 32), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩


def joinbox3_rLRLLRLLLRR : CertificateBox :=
  ⟨((9 : ℚ) / 32), ((5 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩


def joinbox3_rLRLLRLLR : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((5 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((17 : ℚ) / 20), ((139 : ℚ) / 160)⟩


def joinbox3_rLRLLRLLRL : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((5 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩


def joinbox3_rLRLLRLLRLL : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((9 : ℚ) / 32), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩


def joinbox3_rLRLLRLLRLR : CertificateBox :=
  ⟨((9 : ℚ) / 32), ((5 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩


def joinbox3_rLRLLRLLRR : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((5 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩


def joinbox3_rLRLLRLLRRL : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((9 : ℚ) / 32), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩


def joinbox3_rLRLLRLLRRR : CertificateBox :=
  ⟨((9 : ℚ) / 32), ((5 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩


def joinbox3_rLRLLRLR : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((1 : ℚ) / 2), ((17 : ℚ) / 20), ((139 : ℚ) / 160)⟩


def joinbox3_rLRLLRLRL : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((17 : ℚ) / 20), ((139 : ℚ) / 160)⟩


def joinbox3_rLRLLRLRLL : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩


def joinbox3_rLRLLRLRLLL : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩


def joinbox3_rLRLLRLRLLR : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩


def joinbox3_rLRLLRLRLR : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩


def joinbox3_rLRLLRLRLRL : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩


def joinbox3_rLRLLRLRLRR : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩


def joinbox3_rLRLLRLRR : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((3 : ℚ) / 8), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((17 : ℚ) / 20), ((139 : ℚ) / 160)⟩


def joinbox3_rLRLLRLRRL : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((3 : ℚ) / 8), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩


def joinbox3_rLRLLRLRRLL : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩


def joinbox3_rLRLLRLRRLR : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((17 : ℚ) / 20), ((55 : ℚ) / 64)⟩


def joinbox3_rLRLLRLRRR : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((3 : ℚ) / 8), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩


def joinbox3_rLRLLRLRRRL : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩


def joinbox3_rLRLLRLRRRR : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((55 : ℚ) / 64), ((139 : ℚ) / 160)⟩


def joinbox3_rLRLLRR : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((1 : ℚ) / 2), ((139 : ℚ) / 160), ((71 : ℚ) / 80)⟩


def joinbox3_rLRLLRRL : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((5 : ℚ) / 16), ((5 : ℚ) / 12), ((1 : ℚ) / 2), ((139 : ℚ) / 160), ((71 : ℚ) / 80)⟩


def joinbox3_rLRLLRRLL : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((5 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((139 : ℚ) / 160), ((71 : ℚ) / 80)⟩


def joinbox3_rLRLLRRLLL : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((5 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩


def joinbox3_rLRLLRRLLLL : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((9 : ℚ) / 32), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩


def joinbox3_rLRLLRRLLLR : CertificateBox :=
  ⟨((9 : ℚ) / 32), ((5 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩


def joinbox3_rLRLLRRLLR : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((5 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩


def joinbox3_rLRLLRRLLRL : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((9 : ℚ) / 32), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩


def joinbox3_rLRLLRRLLRR : CertificateBox :=
  ⟨((9 : ℚ) / 32), ((5 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩


def joinbox3_rLRLLRRLR : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((5 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((139 : ℚ) / 160), ((71 : ℚ) / 80)⟩


def joinbox3_rLRLLRRLRL : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((5 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩


def joinbox3_rLRLLRRLRLL : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((9 : ℚ) / 32), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩


def joinbox3_rLRLLRRLRLR : CertificateBox :=
  ⟨((9 : ℚ) / 32), ((5 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩


def joinbox3_rLRLLRRLRR : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((5 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩


def joinbox3_rLRLLRRLRRL : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((9 : ℚ) / 32), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩


def joinbox3_rLRLLRRLRRR : CertificateBox :=
  ⟨((9 : ℚ) / 32), ((5 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩


def joinbox3_rLRLLRRR : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((1 : ℚ) / 2), ((139 : ℚ) / 160), ((71 : ℚ) / 80)⟩


def joinbox3_rLRLLRRRL : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((139 : ℚ) / 160), ((71 : ℚ) / 80)⟩


def joinbox3_rLRLLRRRLL : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩


def joinbox3_rLRLLRRRLLL : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩


def joinbox3_rLRLLRRRLLR : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩


def joinbox3_rLRLLRRRLR : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩


def joinbox3_rLRLLRRRLRL : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩


def joinbox3_rLRLLRRRLRR : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩


def joinbox3_rLRLLRRRR : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((3 : ℚ) / 8), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((139 : ℚ) / 160), ((71 : ℚ) / 80)⟩


def joinbox3_rLRLLRRRRL : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((3 : ℚ) / 8), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩


def joinbox3_rLRLLRRRRLL : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩


def joinbox3_rLRLLRRRRLR : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((139 : ℚ) / 160), ((281 : ℚ) / 320)⟩


def joinbox3_rLRLLRRRRR : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((3 : ℚ) / 8), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩


def joinbox3_rLRLLRRRRRL : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩


def joinbox3_rLRLLRRRRRR : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((281 : ℚ) / 320), ((71 : ℚ) / 80)⟩


theorem sound3 : LRCompactVBoxSound box3 :=
  (LRCompactVBoxSound.join (box := box3) .k ((5 : ℚ) / 12)
    (LRCompactVBoxSound.join (box := joinbox3_rLRLLL) .chi ((139 : ℚ) / 160)
      (LRCompactVBoxSound.join (box := joinbox3_rLRLLLL) .s ((5 : ℚ) / 16)
        (LRCompactVBoxSound.join (box := joinbox3_rLRLLLLL) .k ((3 : ℚ) / 8)
          (LRCompactVBoxSound.join (box := joinbox3_rLRLLLLLL) .chi ((55 : ℚ) / 64)
            (LRCompactVBoxSound.join (box := joinbox3_rLRLLLLLLL) .s ((9 : ℚ) / 32)
              (LRCompactVBoxSound.join (box := joinbox3_rLRLLLLLLLL) .k ((17 : ℚ) / 48)
                subsound3_0
                subsound3_1)
              (LRCompactVBoxSound.join (box := joinbox3_rLRLLLLLLLR) .k ((17 : ℚ) / 48)
                subsound3_2
                subsound3_3))
            (LRCompactVBoxSound.join (box := joinbox3_rLRLLLLLLR) .s ((9 : ℚ) / 32)
              subsound3_4
              (LRCompactVBoxSound.join (box := joinbox3_rLRLLLLLLRR) .k ((17 : ℚ) / 48)
                subsound3_5
                subsound3_6)))
          (LRCompactVBoxSound.join (box := joinbox3_rLRLLLLLR) .chi ((55 : ℚ) / 64)
            (LRCompactVBoxSound.join (box := joinbox3_rLRLLLLLRL) .s ((9 : ℚ) / 32)
              (LRCompactVBoxSound.join (box := joinbox3_rLRLLLLLRLL) .k ((19 : ℚ) / 48)
                subsound3_7
                subsound3_8)
              (LRCompactVBoxSound.join (box := joinbox3_rLRLLLLLRLR) .k ((19 : ℚ) / 48)
                subsound3_9
                subsound3_10))
            (LRCompactVBoxSound.join (box := joinbox3_rLRLLLLLRR) .s ((9 : ℚ) / 32)
              (LRCompactVBoxSound.join (box := joinbox3_rLRLLLLLRRL) .k ((19 : ℚ) / 48)
                subsound3_11
                subsound3_12)
              (LRCompactVBoxSound.join (box := joinbox3_rLRLLLLLRRR) .k ((19 : ℚ) / 48)
                subsound3_13
                subsound3_14))))
        (LRCompactVBoxSound.join (box := joinbox3_rLRLLLLR) .k ((3 : ℚ) / 8)
          (LRCompactVBoxSound.join (box := joinbox3_rLRLLLLRL) .chi ((55 : ℚ) / 64)
            (LRCompactVBoxSound.join (box := joinbox3_rLRLLLLRLL) .s ((11 : ℚ) / 32)
              (LRCompactVBoxSound.join (box := joinbox3_rLRLLLLRLLL) .k ((17 : ℚ) / 48)
                subsound3_15
                subsound3_16)
              (LRCompactVBoxSound.join (box := joinbox3_rLRLLLLRLLR) .k ((17 : ℚ) / 48)
                subsound3_17
                subsound3_18))
            (LRCompactVBoxSound.join (box := joinbox3_rLRLLLLRLR) .s ((11 : ℚ) / 32)
              (LRCompactVBoxSound.join (box := joinbox3_rLRLLLLRLRL) .k ((17 : ℚ) / 48)
                subsound3_19
                subsound3_20)
              (LRCompactVBoxSound.join (box := joinbox3_rLRLLLLRLRR) .k ((17 : ℚ) / 48)
                subsound3_21
                subsound3_22)))
          (LRCompactVBoxSound.join (box := joinbox3_rLRLLLLRR) .chi ((55 : ℚ) / 64)
            (LRCompactVBoxSound.join (box := joinbox3_rLRLLLLRRL) .s ((11 : ℚ) / 32)
              (LRCompactVBoxSound.join (box := joinbox3_rLRLLLLRRLL) .k ((19 : ℚ) / 48)
                subsound3_23
                subsound3_24)
              (LRCompactVBoxSound.join (box := joinbox3_rLRLLLLRRLR) .k ((19 : ℚ) / 48)
                subsound3_25
                subsound3_26))
            (LRCompactVBoxSound.join (box := joinbox3_rLRLLLLRRR) .s ((11 : ℚ) / 32)
              (LRCompactVBoxSound.join (box := joinbox3_rLRLLLLRRRL) .k ((19 : ℚ) / 48)
                subsound3_27
                subsound3_28)
              (LRCompactVBoxSound.join (box := joinbox3_rLRLLLLRRRR) .k ((19 : ℚ) / 48)
                subsound3_29
                subsound3_30)))))
      (LRCompactVBoxSound.join (box := joinbox3_rLRLLLR) .s ((5 : ℚ) / 16)
        (LRCompactVBoxSound.join (box := joinbox3_rLRLLLRL) .k ((3 : ℚ) / 8)
          (LRCompactVBoxSound.join (box := joinbox3_rLRLLLRLL) .chi ((281 : ℚ) / 320)
            (LRCompactVBoxSound.join (box := joinbox3_rLRLLLRLLL) .s ((9 : ℚ) / 32)
              subsound3_31
              (LRCompactVBoxSound.join (box := joinbox3_rLRLLLRLLLR) .k ((17 : ℚ) / 48)
                subsound3_32
                subsound3_33))
            (LRCompactVBoxSound.join (box := joinbox3_rLRLLLRLLR) .s ((9 : ℚ) / 32)
              subsound3_34
              subsound3_35))
          (LRCompactVBoxSound.join (box := joinbox3_rLRLLLRLR) .chi ((281 : ℚ) / 320)
            (LRCompactVBoxSound.join (box := joinbox3_rLRLLLRLRL) .s ((9 : ℚ) / 32)
              (LRCompactVBoxSound.join (box := joinbox3_rLRLLLRLRLL) .k ((19 : ℚ) / 48)
                subsound3_36
                subsound3_37)
              (LRCompactVBoxSound.join (box := joinbox3_rLRLLLRLRLR) .k ((19 : ℚ) / 48)
                subsound3_38
                subsound3_39))
            (LRCompactVBoxSound.join (box := joinbox3_rLRLLLRLRR) .s ((9 : ℚ) / 32)
              subsound3_40
              (LRCompactVBoxSound.join (box := joinbox3_rLRLLLRLRRR) .k ((19 : ℚ) / 48)
                subsound3_41
                subsound3_42))))
        (LRCompactVBoxSound.join (box := joinbox3_rLRLLLRR) .k ((3 : ℚ) / 8)
          (LRCompactVBoxSound.join (box := joinbox3_rLRLLLRRL) .chi ((281 : ℚ) / 320)
            (LRCompactVBoxSound.join (box := joinbox3_rLRLLLRRLL) .s ((11 : ℚ) / 32)
              (LRCompactVBoxSound.join (box := joinbox3_rLRLLLRRLLL) .k ((17 : ℚ) / 48)
                subsound3_43
                subsound3_44)
              (LRCompactVBoxSound.join (box := joinbox3_rLRLLLRRLLR) .k ((17 : ℚ) / 48)
                subsound3_45
                subsound3_46))
            (LRCompactVBoxSound.join (box := joinbox3_rLRLLLRRLR) .s ((11 : ℚ) / 32)
              (LRCompactVBoxSound.join (box := joinbox3_rLRLLLRRLRL) .k ((17 : ℚ) / 48)
                subsound3_47
                subsound3_48)
              (LRCompactVBoxSound.join (box := joinbox3_rLRLLLRRLRR) .k ((17 : ℚ) / 48)
                subsound3_49
                subsound3_50)))
          (LRCompactVBoxSound.join (box := joinbox3_rLRLLLRRR) .chi ((281 : ℚ) / 320)
            (LRCompactVBoxSound.join (box := joinbox3_rLRLLLRRRL) .s ((11 : ℚ) / 32)
              (LRCompactVBoxSound.join (box := joinbox3_rLRLLLRRRLL) .k ((19 : ℚ) / 48)
                subsound3_51
                subsound3_52)
              (LRCompactVBoxSound.join (box := joinbox3_rLRLLLRRRLR) .k ((19 : ℚ) / 48)
                subsound3_53
                subsound3_54))
            (LRCompactVBoxSound.join (box := joinbox3_rLRLLLRRRR) .s ((11 : ℚ) / 32)
              (LRCompactVBoxSound.join (box := joinbox3_rLRLLLRRRRL) .k ((19 : ℚ) / 48)
                subsound3_55
                subsound3_56)
              (LRCompactVBoxSound.join (box := joinbox3_rLRLLLRRRRR) .k ((19 : ℚ) / 48)
                subsound3_57
                subsound3_58))))))
    (LRCompactVBoxSound.join (box := joinbox3_rLRLLR) .chi ((139 : ℚ) / 160)
      (LRCompactVBoxSound.join (box := joinbox3_rLRLLRL) .s ((5 : ℚ) / 16)
        (LRCompactVBoxSound.join (box := joinbox3_rLRLLRLL) .k ((11 : ℚ) / 24)
          (LRCompactVBoxSound.join (box := joinbox3_rLRLLRLLL) .chi ((55 : ℚ) / 64)
            (LRCompactVBoxSound.join (box := joinbox3_rLRLLRLLLL) .s ((9 : ℚ) / 32)
              (LRCompactVBoxSound.join (box := joinbox3_rLRLLRLLLLL) .k ((7 : ℚ) / 16)
                subsound3_59
                subsound3_60)
              (LRCompactVBoxSound.join (box := joinbox3_rLRLLRLLLLR) .k ((7 : ℚ) / 16)
                subsound3_61
                subsound3_62))
            (LRCompactVBoxSound.join (box := joinbox3_rLRLLRLLLR) .s ((9 : ℚ) / 32)
              (LRCompactVBoxSound.join (box := joinbox3_rLRLLRLLLRL) .k ((7 : ℚ) / 16)
                subsound3_63
                subsound3_64)
              (LRCompactVBoxSound.join (box := joinbox3_rLRLLRLLLRR) .k ((7 : ℚ) / 16)
                subsound3_65
                subsound3_66)))
          (LRCompactVBoxSound.join (box := joinbox3_rLRLLRLLR) .chi ((55 : ℚ) / 64)
            (LRCompactVBoxSound.join (box := joinbox3_rLRLLRLLRL) .s ((9 : ℚ) / 32)
              (LRCompactVBoxSound.join (box := joinbox3_rLRLLRLLRLL) .k ((23 : ℚ) / 48)
                subsound3_67
                subsound3_68)
              (LRCompactVBoxSound.join (box := joinbox3_rLRLLRLLRLR) .k ((23 : ℚ) / 48)
                subsound3_69
                subsound3_70))
            (LRCompactVBoxSound.join (box := joinbox3_rLRLLRLLRR) .s ((9 : ℚ) / 32)
              (LRCompactVBoxSound.join (box := joinbox3_rLRLLRLLRRL) .k ((23 : ℚ) / 48)
                subsound3_71
                subsound3_72)
              (LRCompactVBoxSound.join (box := joinbox3_rLRLLRLLRRR) .k ((23 : ℚ) / 48)
                subsound3_73
                subsound3_74))))
        (LRCompactVBoxSound.join (box := joinbox3_rLRLLRLR) .k ((11 : ℚ) / 24)
          (LRCompactVBoxSound.join (box := joinbox3_rLRLLRLRL) .chi ((55 : ℚ) / 64)
            (LRCompactVBoxSound.join (box := joinbox3_rLRLLRLRLL) .s ((11 : ℚ) / 32)
              (LRCompactVBoxSound.join (box := joinbox3_rLRLLRLRLLL) .k ((7 : ℚ) / 16)
                subsound3_75
                subsound3_76)
              (LRCompactVBoxSound.join (box := joinbox3_rLRLLRLRLLR) .k ((7 : ℚ) / 16)
                subsound3_77
                subsound3_78))
            (LRCompactVBoxSound.join (box := joinbox3_rLRLLRLRLR) .s ((11 : ℚ) / 32)
              (LRCompactVBoxSound.join (box := joinbox3_rLRLLRLRLRL) .k ((7 : ℚ) / 16)
                subsound3_79
                subsound3_80)
              (LRCompactVBoxSound.join (box := joinbox3_rLRLLRLRLRR) .k ((7 : ℚ) / 16)
                subsound3_81
                subsound3_82)))
          (LRCompactVBoxSound.join (box := joinbox3_rLRLLRLRR) .chi ((55 : ℚ) / 64)
            (LRCompactVBoxSound.join (box := joinbox3_rLRLLRLRRL) .s ((11 : ℚ) / 32)
              (LRCompactVBoxSound.join (box := joinbox3_rLRLLRLRRLL) .k ((23 : ℚ) / 48)
                subsound3_83
                subsound3_84)
              (LRCompactVBoxSound.join (box := joinbox3_rLRLLRLRRLR) .k ((23 : ℚ) / 48)
                subsound3_85
                subsound3_86))
            (LRCompactVBoxSound.join (box := joinbox3_rLRLLRLRRR) .s ((11 : ℚ) / 32)
              (LRCompactVBoxSound.join (box := joinbox3_rLRLLRLRRRL) .k ((23 : ℚ) / 48)
                subsound3_87
                subsound3_88)
              (LRCompactVBoxSound.join (box := joinbox3_rLRLLRLRRRR) .k ((23 : ℚ) / 48)
                subsound3_89
                subsound3_90)))))
      (LRCompactVBoxSound.join (box := joinbox3_rLRLLRR) .s ((5 : ℚ) / 16)
        (LRCompactVBoxSound.join (box := joinbox3_rLRLLRRL) .k ((11 : ℚ) / 24)
          (LRCompactVBoxSound.join (box := joinbox3_rLRLLRRLL) .chi ((281 : ℚ) / 320)
            (LRCompactVBoxSound.join (box := joinbox3_rLRLLRRLLL) .s ((9 : ℚ) / 32)
              (LRCompactVBoxSound.join (box := joinbox3_rLRLLRRLLLL) .k ((7 : ℚ) / 16)
                subsound3_91
                subsound3_92)
              (LRCompactVBoxSound.join (box := joinbox3_rLRLLRRLLLR) .k ((7 : ℚ) / 16)
                subsound3_93
                subsound3_94))
            (LRCompactVBoxSound.join (box := joinbox3_rLRLLRRLLR) .s ((9 : ℚ) / 32)
              (LRCompactVBoxSound.join (box := joinbox3_rLRLLRRLLRL) .k ((7 : ℚ) / 16)
                subsound3_95
                subsound3_96)
              (LRCompactVBoxSound.join (box := joinbox3_rLRLLRRLLRR) .k ((7 : ℚ) / 16)
                subsound3_97
                subsound3_98)))
          (LRCompactVBoxSound.join (box := joinbox3_rLRLLRRLR) .chi ((281 : ℚ) / 320)
            (LRCompactVBoxSound.join (box := joinbox3_rLRLLRRLRL) .s ((9 : ℚ) / 32)
              (LRCompactVBoxSound.join (box := joinbox3_rLRLLRRLRLL) .k ((23 : ℚ) / 48)
                subsound3_99
                subsound3_100)
              (LRCompactVBoxSound.join (box := joinbox3_rLRLLRRLRLR) .k ((23 : ℚ) / 48)
                subsound3_101
                subsound3_102))
            (LRCompactVBoxSound.join (box := joinbox3_rLRLLRRLRR) .s ((9 : ℚ) / 32)
              (LRCompactVBoxSound.join (box := joinbox3_rLRLLRRLRRL) .k ((23 : ℚ) / 48)
                subsound3_103
                subsound3_104)
              (LRCompactVBoxSound.join (box := joinbox3_rLRLLRRLRRR) .k ((23 : ℚ) / 48)
                subsound3_105
                subsound3_106))))
        (LRCompactVBoxSound.join (box := joinbox3_rLRLLRRR) .k ((11 : ℚ) / 24)
          (LRCompactVBoxSound.join (box := joinbox3_rLRLLRRRL) .chi ((281 : ℚ) / 320)
            (LRCompactVBoxSound.join (box := joinbox3_rLRLLRRRLL) .s ((11 : ℚ) / 32)
              (LRCompactVBoxSound.join (box := joinbox3_rLRLLRRRLLL) .k ((7 : ℚ) / 16)
                subsound3_107
                subsound3_108)
              (LRCompactVBoxSound.join (box := joinbox3_rLRLLRRRLLR) .k ((7 : ℚ) / 16)
                subsound3_109
                subsound3_110))
            (LRCompactVBoxSound.join (box := joinbox3_rLRLLRRRLR) .s ((11 : ℚ) / 32)
              (LRCompactVBoxSound.join (box := joinbox3_rLRLLRRRLRL) .k ((7 : ℚ) / 16)
                subsound3_111
                subsound3_112)
              (LRCompactVBoxSound.join (box := joinbox3_rLRLLRRRLRR) .k ((7 : ℚ) / 16)
                subsound3_113
                subsound3_114)))
          (LRCompactVBoxSound.join (box := joinbox3_rLRLLRRRR) .chi ((281 : ℚ) / 320)
            (LRCompactVBoxSound.join (box := joinbox3_rLRLLRRRRL) .s ((11 : ℚ) / 32)
              (LRCompactVBoxSound.join (box := joinbox3_rLRLLRRRRLL) .k ((23 : ℚ) / 48)
                subsound3_115
                subsound3_116)
              (LRCompactVBoxSound.join (box := joinbox3_rLRLLRRRRLR) .k ((23 : ℚ) / 48)
                subsound3_117
                subsound3_118))
            (LRCompactVBoxSound.join (box := joinbox3_rLRLLRRRRR) .s ((11 : ℚ) / 32)
              (LRCompactVBoxSound.join (box := joinbox3_rLRLLRRRRRL) .k ((23 : ℚ) / 48)
                subsound3_119
                subsound3_120)
              (LRCompactVBoxSound.join (box := joinbox3_rLRLLRRRRRR) .k ((23 : ℚ) / 48)
                subsound3_121
                subsound3_122)))))))

end CourtadeKumar.GeneratedLRCompactVLowR
