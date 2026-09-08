import InformationTheory.CourtadeKumar.LRCompactVBasicReplay

/-! Frozen basic compact-V replay.
Plan SHA-256: ce3f7a498b2b9caf346dcf88ce7861f8cc091af8cd93f5624d7684e21322ecd5
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CourtadeKumar.GeneratedLRCompactVLowR

-- 107 accepted leaves below path rLRRL.
def box6 : CertificateBox where
  sLo := ((1 : ℚ) / 4)
  sHi := ((3 : ℚ) / 8)
  kLo := ((1 : ℚ) / 3)
  kHi := ((1 : ℚ) / 2)
  chiLo := ((71 : ℚ) / 80)
  chiHi := ((37 : ℚ) / 40)


def subbox6_0 : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((9 : ℚ) / 32), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩

theorem checked6_0 :
    LRCompactVLeafParameters.check subbox6_0 .short = true := by decide +kernel

theorem subsound6_0 : LRCompactVBoxSound subbox6_0 :=
  LRCompactVLeafParameters.sound checked6_0


def subbox6_1 : CertificateBox :=
  ⟨((9 : ℚ) / 32), ((5 : ℚ) / 16), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩

theorem checked6_1 :
    LRCompactVLeafParameters.check subbox6_1 .long = true := by decide +kernel

theorem subsound6_1 : LRCompactVBoxSound subbox6_1 :=
  LRCompactVLeafParameters.sound checked6_1


def subbox6_2 : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((9 : ℚ) / 32), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩

theorem checked6_2 :
    LRCompactVLeafParameters.check subbox6_2 .short = true := by decide +kernel

theorem subsound6_2 : LRCompactVBoxSound subbox6_2 :=
  LRCompactVLeafParameters.sound checked6_2


def subbox6_3 : CertificateBox :=
  ⟨((9 : ℚ) / 32), ((5 : ℚ) / 16), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩

theorem checked6_3 :
    LRCompactVLeafParameters.check subbox6_3 .long = true := by decide +kernel

theorem subsound6_3 : LRCompactVBoxSound subbox6_3 :=
  LRCompactVLeafParameters.sound checked6_3


def subbox6_4 : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((9 : ℚ) / 32), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩

theorem checked6_4 :
    LRCompactVLeafParameters.check subbox6_4 .long = true := by decide +kernel

theorem subsound6_4 : LRCompactVBoxSound subbox6_4 :=
  LRCompactVLeafParameters.sound checked6_4


def subbox6_5 : CertificateBox :=
  ⟨((9 : ℚ) / 32), ((5 : ℚ) / 16), ((3 : ℚ) / 8), ((19 : ℚ) / 48), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩

theorem checked6_5 :
    LRCompactVLeafParameters.check subbox6_5 .short = true := by decide +kernel

theorem subsound6_5 : LRCompactVBoxSound subbox6_5 :=
  LRCompactVLeafParameters.sound checked6_5


def subbox6_6 : CertificateBox :=
  ⟨((9 : ℚ) / 32), ((5 : ℚ) / 16), ((19 : ℚ) / 48), ((5 : ℚ) / 12), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩

theorem checked6_6 :
    LRCompactVLeafParameters.check subbox6_6 .short = true := by decide +kernel

theorem subsound6_6 : LRCompactVBoxSound subbox6_6 :=
  LRCompactVLeafParameters.sound checked6_6


def subbox6_7 : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((9 : ℚ) / 32), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩

theorem checked6_7 :
    LRCompactVLeafParameters.check subbox6_7 .long = true := by decide +kernel

theorem subsound6_7 : LRCompactVBoxSound subbox6_7 :=
  LRCompactVLeafParameters.sound checked6_7


def subbox6_8 : CertificateBox :=
  ⟨((9 : ℚ) / 32), ((5 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩

theorem checked6_8 :
    LRCompactVLeafParameters.check subbox6_8 .long = true := by decide +kernel

theorem subsound6_8 : LRCompactVBoxSound subbox6_8 :=
  LRCompactVLeafParameters.sound checked6_8


def subbox6_9 : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((1 : ℚ) / 3), ((17 : ℚ) / 48), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩

theorem checked6_9 :
    LRCompactVLeafParameters.check subbox6_9 .short = true := by decide +kernel

theorem subsound6_9 : LRCompactVBoxSound subbox6_9 :=
  LRCompactVLeafParameters.sound checked6_9


def subbox6_10 : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((17 : ℚ) / 48), ((3 : ℚ) / 8), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩

theorem checked6_10 :
    LRCompactVLeafParameters.check subbox6_10 .short = true := by decide +kernel

theorem subsound6_10 : LRCompactVBoxSound subbox6_10 :=
  LRCompactVLeafParameters.sound checked6_10


def subbox6_11 : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((1 : ℚ) / 3), ((17 : ℚ) / 48), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩

theorem checked6_11 :
    LRCompactVLeafParameters.check subbox6_11 .short = true := by decide +kernel

theorem subsound6_11 : LRCompactVBoxSound subbox6_11 :=
  LRCompactVLeafParameters.sound checked6_11


def subbox6_12 : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((17 : ℚ) / 48), ((3 : ℚ) / 8), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩

theorem checked6_12 :
    LRCompactVLeafParameters.check subbox6_12 .short = true := by decide +kernel

theorem subsound6_12 : LRCompactVBoxSound subbox6_12 :=
  LRCompactVLeafParameters.sound checked6_12


def subbox6_13 : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩

theorem checked6_13 :
    LRCompactVLeafParameters.check subbox6_13 .long = true := by decide +kernel

theorem subsound6_13 : LRCompactVBoxSound subbox6_13 :=
  LRCompactVLeafParameters.sound checked6_13


def subbox6_14 : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((1 : ℚ) / 3), ((17 : ℚ) / 48), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩

theorem checked6_14 :
    LRCompactVLeafParameters.check subbox6_14 .short = true := by decide +kernel

theorem subsound6_14 : LRCompactVBoxSound subbox6_14 :=
  LRCompactVLeafParameters.sound checked6_14


def subbox6_15 : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((17 : ℚ) / 48), ((3 : ℚ) / 8), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩

theorem checked6_15 :
    LRCompactVLeafParameters.check subbox6_15 .short = true := by decide +kernel

theorem subsound6_15 : LRCompactVBoxSound subbox6_15 :=
  LRCompactVLeafParameters.sound checked6_15


def subbox6_16 : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((3 : ℚ) / 8), ((19 : ℚ) / 48), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩

theorem checked6_16 :
    LRCompactVLeafParameters.check subbox6_16 .short = true := by decide +kernel

theorem subsound6_16 : LRCompactVBoxSound subbox6_16 :=
  LRCompactVLeafParameters.sound checked6_16


def subbox6_17 : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((19 : ℚ) / 48), ((5 : ℚ) / 12), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩

theorem checked6_17 :
    LRCompactVLeafParameters.check subbox6_17 .short = true := by decide +kernel

theorem subsound6_17 : LRCompactVBoxSound subbox6_17 :=
  LRCompactVLeafParameters.sound checked6_17


def subbox6_18 : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((3 : ℚ) / 8), ((19 : ℚ) / 48), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩

theorem checked6_18 :
    LRCompactVLeafParameters.check subbox6_18 .short = true := by decide +kernel

theorem subsound6_18 : LRCompactVBoxSound subbox6_18 :=
  LRCompactVLeafParameters.sound checked6_18


def subbox6_19 : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((19 : ℚ) / 48), ((5 : ℚ) / 12), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩

theorem checked6_19 :
    LRCompactVLeafParameters.check subbox6_19 .short = true := by decide +kernel

theorem subsound6_19 : LRCompactVBoxSound subbox6_19 :=
  LRCompactVLeafParameters.sound checked6_19


def subbox6_20 : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((3 : ℚ) / 8), ((19 : ℚ) / 48), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩

theorem checked6_20 :
    LRCompactVLeafParameters.check subbox6_20 .short = true := by decide +kernel

theorem subsound6_20 : LRCompactVBoxSound subbox6_20 :=
  LRCompactVLeafParameters.sound checked6_20


def subbox6_21 : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((19 : ℚ) / 48), ((5 : ℚ) / 12), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩

theorem checked6_21 :
    LRCompactVLeafParameters.check subbox6_21 .short = true := by decide +kernel

theorem subsound6_21 : LRCompactVBoxSound subbox6_21 :=
  LRCompactVLeafParameters.sound checked6_21


def subbox6_22 : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((3 : ℚ) / 8), ((19 : ℚ) / 48), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩

theorem checked6_22 :
    LRCompactVLeafParameters.check subbox6_22 .short = true := by decide +kernel

theorem subsound6_22 : LRCompactVBoxSound subbox6_22 :=
  LRCompactVLeafParameters.sound checked6_22


def subbox6_23 : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((19 : ℚ) / 48), ((5 : ℚ) / 12), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩

theorem checked6_23 :
    LRCompactVLeafParameters.check subbox6_23 .short = true := by decide +kernel

theorem subsound6_23 : LRCompactVBoxSound subbox6_23 :=
  LRCompactVLeafParameters.sound checked6_23


def subbox6_24 : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((9 : ℚ) / 32), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩

theorem checked6_24 :
    LRCompactVLeafParameters.check subbox6_24 .short = true := by decide +kernel

theorem subsound6_24 : LRCompactVBoxSound subbox6_24 :=
  LRCompactVLeafParameters.sound checked6_24


def subbox6_25 : CertificateBox :=
  ⟨((9 : ℚ) / 32), ((5 : ℚ) / 16), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩

theorem checked6_25 :
    LRCompactVLeafParameters.check subbox6_25 .short = true := by decide +kernel

theorem subsound6_25 : LRCompactVBoxSound subbox6_25 :=
  LRCompactVLeafParameters.sound checked6_25


def subbox6_26 : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((9 : ℚ) / 32), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩

theorem checked6_26 :
    LRCompactVLeafParameters.check subbox6_26 .short = true := by decide +kernel

theorem subsound6_26 : LRCompactVBoxSound subbox6_26 :=
  LRCompactVLeafParameters.sound checked6_26


def subbox6_27 : CertificateBox :=
  ⟨((9 : ℚ) / 32), ((5 : ℚ) / 16), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩

theorem checked6_27 :
    LRCompactVLeafParameters.check subbox6_27 .short = true := by decide +kernel

theorem subsound6_27 : LRCompactVBoxSound subbox6_27 :=
  LRCompactVLeafParameters.sound checked6_27


def subbox6_28 : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((9 : ℚ) / 32), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩

theorem checked6_28 :
    LRCompactVLeafParameters.check subbox6_28 .short = true := by decide +kernel

theorem subsound6_28 : LRCompactVBoxSound subbox6_28 :=
  LRCompactVLeafParameters.sound checked6_28


def subbox6_29 : CertificateBox :=
  ⟨((9 : ℚ) / 32), ((5 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩

theorem checked6_29 :
    LRCompactVLeafParameters.check subbox6_29 .long = true := by decide +kernel

theorem subsound6_29 : LRCompactVBoxSound subbox6_29 :=
  LRCompactVLeafParameters.sound checked6_29


def subbox6_30 : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((9 : ℚ) / 32), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩

theorem checked6_30 :
    LRCompactVLeafParameters.check subbox6_30 .short = true := by decide +kernel

theorem subsound6_30 : LRCompactVBoxSound subbox6_30 :=
  LRCompactVLeafParameters.sound checked6_30


def subbox6_31 : CertificateBox :=
  ⟨((9 : ℚ) / 32), ((5 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩

theorem checked6_31 :
    LRCompactVLeafParameters.check subbox6_31 .long = true := by decide +kernel

theorem subsound6_31 : LRCompactVBoxSound subbox6_31 :=
  LRCompactVLeafParameters.sound checked6_31


def subbox6_32 : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩

theorem checked6_32 :
    LRCompactVLeafParameters.check subbox6_32 .long = true := by decide +kernel

theorem subsound6_32 : LRCompactVBoxSound subbox6_32 :=
  LRCompactVLeafParameters.sound checked6_32


def subbox6_33 : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((1 : ℚ) / 3), ((17 : ℚ) / 48), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩

theorem checked6_33 :
    LRCompactVLeafParameters.check subbox6_33 .short = true := by decide +kernel

theorem subsound6_33 : LRCompactVBoxSound subbox6_33 :=
  LRCompactVLeafParameters.sound checked6_33


def subbox6_34 : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((17 : ℚ) / 48), ((3 : ℚ) / 8), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩

theorem checked6_34 :
    LRCompactVLeafParameters.check subbox6_34 .short = true := by decide +kernel

theorem subsound6_34 : LRCompactVBoxSound subbox6_34 :=
  LRCompactVLeafParameters.sound checked6_34


def subbox6_35 : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩

theorem checked6_35 :
    LRCompactVLeafParameters.check subbox6_35 .long = true := by decide +kernel

theorem subsound6_35 : LRCompactVBoxSound subbox6_35 :=
  LRCompactVLeafParameters.sound checked6_35


def subbox6_36 : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩

theorem checked6_36 :
    LRCompactVLeafParameters.check subbox6_36 .long = true := by decide +kernel

theorem subsound6_36 : LRCompactVBoxSound subbox6_36 :=
  LRCompactVLeafParameters.sound checked6_36


def subbox6_37 : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((3 : ℚ) / 8), ((19 : ℚ) / 48), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩

theorem checked6_37 :
    LRCompactVLeafParameters.check subbox6_37 .short = true := by decide +kernel

theorem subsound6_37 : LRCompactVBoxSound subbox6_37 :=
  LRCompactVLeafParameters.sound checked6_37


def subbox6_38 : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((19 : ℚ) / 48), ((5 : ℚ) / 12), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩

theorem checked6_38 :
    LRCompactVLeafParameters.check subbox6_38 .short = true := by decide +kernel

theorem subsound6_38 : LRCompactVBoxSound subbox6_38 :=
  LRCompactVLeafParameters.sound checked6_38


def subbox6_39 : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((3 : ℚ) / 8), ((19 : ℚ) / 48), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩

theorem checked6_39 :
    LRCompactVLeafParameters.check subbox6_39 .short = true := by decide +kernel

theorem subsound6_39 : LRCompactVBoxSound subbox6_39 :=
  LRCompactVLeafParameters.sound checked6_39


def subbox6_40 : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((19 : ℚ) / 48), ((5 : ℚ) / 12), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩

theorem checked6_40 :
    LRCompactVLeafParameters.check subbox6_40 .short = true := by decide +kernel

theorem subsound6_40 : LRCompactVBoxSound subbox6_40 :=
  LRCompactVLeafParameters.sound checked6_40


def subbox6_41 : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((3 : ℚ) / 8), ((19 : ℚ) / 48), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩

theorem checked6_41 :
    LRCompactVLeafParameters.check subbox6_41 .short = true := by decide +kernel

theorem subsound6_41 : LRCompactVBoxSound subbox6_41 :=
  LRCompactVLeafParameters.sound checked6_41


def subbox6_42 : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((19 : ℚ) / 48), ((5 : ℚ) / 12), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩

theorem checked6_42 :
    LRCompactVLeafParameters.check subbox6_42 .short = true := by decide +kernel

theorem subsound6_42 : LRCompactVBoxSound subbox6_42 :=
  LRCompactVLeafParameters.sound checked6_42


def subbox6_43 : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((3 : ℚ) / 8), ((19 : ℚ) / 48), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩

theorem checked6_43 :
    LRCompactVLeafParameters.check subbox6_43 .short = true := by decide +kernel

theorem subsound6_43 : LRCompactVBoxSound subbox6_43 :=
  LRCompactVLeafParameters.sound checked6_43


def subbox6_44 : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((19 : ℚ) / 48), ((5 : ℚ) / 12), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩

theorem checked6_44 :
    LRCompactVLeafParameters.check subbox6_44 .short = true := by decide +kernel

theorem subsound6_44 : LRCompactVBoxSound subbox6_44 :=
  LRCompactVLeafParameters.sound checked6_44


def subbox6_45 : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((9 : ℚ) / 32), ((5 : ℚ) / 12), ((7 : ℚ) / 16), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩

theorem checked6_45 :
    LRCompactVLeafParameters.check subbox6_45 .short = true := by decide +kernel

theorem subsound6_45 : LRCompactVBoxSound subbox6_45 :=
  LRCompactVLeafParameters.sound checked6_45


def subbox6_46 : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((9 : ℚ) / 32), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩

theorem checked6_46 :
    LRCompactVLeafParameters.check subbox6_46 .short = true := by decide +kernel

theorem subsound6_46 : LRCompactVBoxSound subbox6_46 :=
  LRCompactVLeafParameters.sound checked6_46


def subbox6_47 : CertificateBox :=
  ⟨((9 : ℚ) / 32), ((5 : ℚ) / 16), ((5 : ℚ) / 12), ((7 : ℚ) / 16), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩

theorem checked6_47 :
    LRCompactVLeafParameters.check subbox6_47 .short = true := by decide +kernel

theorem subsound6_47 : LRCompactVBoxSound subbox6_47 :=
  LRCompactVLeafParameters.sound checked6_47


def subbox6_48 : CertificateBox :=
  ⟨((9 : ℚ) / 32), ((5 : ℚ) / 16), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩

theorem checked6_48 :
    LRCompactVLeafParameters.check subbox6_48 .short = true := by decide +kernel

theorem subsound6_48 : LRCompactVBoxSound subbox6_48 :=
  LRCompactVLeafParameters.sound checked6_48


def subbox6_49 : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((9 : ℚ) / 32), ((5 : ℚ) / 12), ((7 : ℚ) / 16), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩

theorem checked6_49 :
    LRCompactVLeafParameters.check subbox6_49 .short = true := by decide +kernel

theorem subsound6_49 : LRCompactVBoxSound subbox6_49 :=
  LRCompactVLeafParameters.sound checked6_49


def subbox6_50 : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((9 : ℚ) / 32), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩

theorem checked6_50 :
    LRCompactVLeafParameters.check subbox6_50 .short = true := by decide +kernel

theorem subsound6_50 : LRCompactVBoxSound subbox6_50 :=
  LRCompactVLeafParameters.sound checked6_50


def subbox6_51 : CertificateBox :=
  ⟨((9 : ℚ) / 32), ((5 : ℚ) / 16), ((5 : ℚ) / 12), ((7 : ℚ) / 16), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩

theorem checked6_51 :
    LRCompactVLeafParameters.check subbox6_51 .short = true := by decide +kernel

theorem subsound6_51 : LRCompactVBoxSound subbox6_51 :=
  LRCompactVLeafParameters.sound checked6_51


def subbox6_52 : CertificateBox :=
  ⟨((9 : ℚ) / 32), ((5 : ℚ) / 16), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩

theorem checked6_52 :
    LRCompactVLeafParameters.check subbox6_52 .short = true := by decide +kernel

theorem subsound6_52 : LRCompactVBoxSound subbox6_52 :=
  LRCompactVLeafParameters.sound checked6_52


def subbox6_53 : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((9 : ℚ) / 32), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩

theorem checked6_53 :
    LRCompactVLeafParameters.check subbox6_53 .short = true := by decide +kernel

theorem subsound6_53 : LRCompactVBoxSound subbox6_53 :=
  LRCompactVLeafParameters.sound checked6_53


def subbox6_54 : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((9 : ℚ) / 32), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩

theorem checked6_54 :
    LRCompactVLeafParameters.check subbox6_54 .short = true := by decide +kernel

theorem subsound6_54 : LRCompactVBoxSound subbox6_54 :=
  LRCompactVLeafParameters.sound checked6_54


def subbox6_55 : CertificateBox :=
  ⟨((9 : ℚ) / 32), ((5 : ℚ) / 16), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩

theorem checked6_55 :
    LRCompactVLeafParameters.check subbox6_55 .short = true := by decide +kernel

theorem subsound6_55 : LRCompactVBoxSound subbox6_55 :=
  LRCompactVLeafParameters.sound checked6_55


def subbox6_56 : CertificateBox :=
  ⟨((9 : ℚ) / 32), ((5 : ℚ) / 16), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩

theorem checked6_56 :
    LRCompactVLeafParameters.check subbox6_56 .short = true := by decide +kernel

theorem subsound6_56 : LRCompactVBoxSound subbox6_56 :=
  LRCompactVLeafParameters.sound checked6_56


def subbox6_57 : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((9 : ℚ) / 32), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩

theorem checked6_57 :
    LRCompactVLeafParameters.check subbox6_57 .short = true := by decide +kernel

theorem subsound6_57 : LRCompactVBoxSound subbox6_57 :=
  LRCompactVLeafParameters.sound checked6_57


def subbox6_58 : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((9 : ℚ) / 32), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩

theorem checked6_58 :
    LRCompactVLeafParameters.check subbox6_58 .short = true := by decide +kernel

theorem subsound6_58 : LRCompactVBoxSound subbox6_58 :=
  LRCompactVLeafParameters.sound checked6_58


def subbox6_59 : CertificateBox :=
  ⟨((9 : ℚ) / 32), ((5 : ℚ) / 16), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩

theorem checked6_59 :
    LRCompactVLeafParameters.check subbox6_59 .short = true := by decide +kernel

theorem subsound6_59 : LRCompactVBoxSound subbox6_59 :=
  LRCompactVLeafParameters.sound checked6_59


def subbox6_60 : CertificateBox :=
  ⟨((9 : ℚ) / 32), ((5 : ℚ) / 16), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩

theorem checked6_60 :
    LRCompactVLeafParameters.check subbox6_60 .short = true := by decide +kernel

theorem subsound6_60 : LRCompactVBoxSound subbox6_60 :=
  LRCompactVLeafParameters.sound checked6_60


def subbox6_61 : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((5 : ℚ) / 12), ((7 : ℚ) / 16), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩

theorem checked6_61 :
    LRCompactVLeafParameters.check subbox6_61 .short = true := by decide +kernel

theorem subsound6_61 : LRCompactVBoxSound subbox6_61 :=
  LRCompactVLeafParameters.sound checked6_61


def subbox6_62 : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩

theorem checked6_62 :
    LRCompactVLeafParameters.check subbox6_62 .short = true := by decide +kernel

theorem subsound6_62 : LRCompactVBoxSound subbox6_62 :=
  LRCompactVLeafParameters.sound checked6_62


def subbox6_63 : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((7 : ℚ) / 16), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩

theorem checked6_63 :
    LRCompactVLeafParameters.check subbox6_63 .short = true := by decide +kernel

theorem subsound6_63 : LRCompactVBoxSound subbox6_63 :=
  LRCompactVLeafParameters.sound checked6_63


def subbox6_64 : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩

theorem checked6_64 :
    LRCompactVLeafParameters.check subbox6_64 .short = true := by decide +kernel

theorem subsound6_64 : LRCompactVBoxSound subbox6_64 :=
  LRCompactVLeafParameters.sound checked6_64


def subbox6_65 : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((5 : ℚ) / 12), ((7 : ℚ) / 16), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩

theorem checked6_65 :
    LRCompactVLeafParameters.check subbox6_65 .short = true := by decide +kernel

theorem subsound6_65 : LRCompactVBoxSound subbox6_65 :=
  LRCompactVLeafParameters.sound checked6_65


def subbox6_66 : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩

theorem checked6_66 :
    LRCompactVLeafParameters.check subbox6_66 .short = true := by decide +kernel

theorem subsound6_66 : LRCompactVBoxSound subbox6_66 :=
  LRCompactVLeafParameters.sound checked6_66


def subbox6_67 : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((7 : ℚ) / 16), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩

theorem checked6_67 :
    LRCompactVLeafParameters.check subbox6_67 .short = true := by decide +kernel

theorem subsound6_67 : LRCompactVBoxSound subbox6_67 :=
  LRCompactVLeafParameters.sound checked6_67


def subbox6_68 : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩

theorem checked6_68 :
    LRCompactVLeafParameters.check subbox6_68 .short = true := by decide +kernel

theorem subsound6_68 : LRCompactVBoxSound subbox6_68 :=
  LRCompactVLeafParameters.sound checked6_68


def subbox6_69 : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩

theorem checked6_69 :
    LRCompactVLeafParameters.check subbox6_69 .short = true := by decide +kernel

theorem subsound6_69 : LRCompactVBoxSound subbox6_69 :=
  LRCompactVLeafParameters.sound checked6_69


def subbox6_70 : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩

theorem checked6_70 :
    LRCompactVLeafParameters.check subbox6_70 .short = true := by decide +kernel

theorem subsound6_70 : LRCompactVBoxSound subbox6_70 :=
  LRCompactVLeafParameters.sound checked6_70


def subbox6_71 : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩

theorem checked6_71 :
    LRCompactVLeafParameters.check subbox6_71 .short = true := by decide +kernel

theorem subsound6_71 : LRCompactVBoxSound subbox6_71 :=
  LRCompactVLeafParameters.sound checked6_71


def subbox6_72 : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩

theorem checked6_72 :
    LRCompactVLeafParameters.check subbox6_72 .short = true := by decide +kernel

theorem subsound6_72 : LRCompactVBoxSound subbox6_72 :=
  LRCompactVLeafParameters.sound checked6_72


def subbox6_73 : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩

theorem checked6_73 :
    LRCompactVLeafParameters.check subbox6_73 .short = true := by decide +kernel

theorem subsound6_73 : LRCompactVBoxSound subbox6_73 :=
  LRCompactVLeafParameters.sound checked6_73


def subbox6_74 : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩

theorem checked6_74 :
    LRCompactVLeafParameters.check subbox6_74 .short = true := by decide +kernel

theorem subsound6_74 : LRCompactVBoxSound subbox6_74 :=
  LRCompactVLeafParameters.sound checked6_74


def subbox6_75 : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩

theorem checked6_75 :
    LRCompactVLeafParameters.check subbox6_75 .short = true := by decide +kernel

theorem subsound6_75 : LRCompactVBoxSound subbox6_75 :=
  LRCompactVLeafParameters.sound checked6_75


def subbox6_76 : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩

theorem checked6_76 :
    LRCompactVLeafParameters.check subbox6_76 .short = true := by decide +kernel

theorem subsound6_76 : LRCompactVBoxSound subbox6_76 :=
  LRCompactVLeafParameters.sound checked6_76


def subbox6_77 : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((9 : ℚ) / 32), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩

theorem checked6_77 :
    LRCompactVLeafParameters.check subbox6_77 .long = true := by decide +kernel

theorem subsound6_77 : LRCompactVBoxSound subbox6_77 :=
  LRCompactVLeafParameters.sound checked6_77


def subbox6_78 : CertificateBox :=
  ⟨((9 : ℚ) / 32), ((5 : ℚ) / 16), ((5 : ℚ) / 12), ((7 : ℚ) / 16), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩

theorem checked6_78 :
    LRCompactVLeafParameters.check subbox6_78 .short = true := by decide +kernel

theorem subsound6_78 : LRCompactVBoxSound subbox6_78 :=
  LRCompactVLeafParameters.sound checked6_78


def subbox6_79 : CertificateBox :=
  ⟨((9 : ℚ) / 32), ((5 : ℚ) / 16), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩

theorem checked6_79 :
    LRCompactVLeafParameters.check subbox6_79 .short = true := by decide +kernel

theorem subsound6_79 : LRCompactVBoxSound subbox6_79 :=
  LRCompactVLeafParameters.sound checked6_79


def subbox6_80 : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((9 : ℚ) / 32), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩

theorem checked6_80 :
    LRCompactVLeafParameters.check subbox6_80 .long = true := by decide +kernel

theorem subsound6_80 : LRCompactVBoxSound subbox6_80 :=
  LRCompactVLeafParameters.sound checked6_80


def subbox6_81 : CertificateBox :=
  ⟨((9 : ℚ) / 32), ((5 : ℚ) / 16), ((5 : ℚ) / 12), ((7 : ℚ) / 16), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩

theorem checked6_81 :
    LRCompactVLeafParameters.check subbox6_81 .short = true := by decide +kernel

theorem subsound6_81 : LRCompactVBoxSound subbox6_81 :=
  LRCompactVLeafParameters.sound checked6_81


def subbox6_82 : CertificateBox :=
  ⟨((9 : ℚ) / 32), ((5 : ℚ) / 16), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩

theorem checked6_82 :
    LRCompactVLeafParameters.check subbox6_82 .short = true := by decide +kernel

theorem subsound6_82 : LRCompactVBoxSound subbox6_82 :=
  LRCompactVLeafParameters.sound checked6_82


def subbox6_83 : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((9 : ℚ) / 32), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩

theorem checked6_83 :
    LRCompactVLeafParameters.check subbox6_83 .short = true := by decide +kernel

theorem subsound6_83 : LRCompactVBoxSound subbox6_83 :=
  LRCompactVLeafParameters.sound checked6_83


def subbox6_84 : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((9 : ℚ) / 32), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩

theorem checked6_84 :
    LRCompactVLeafParameters.check subbox6_84 .short = true := by decide +kernel

theorem subsound6_84 : LRCompactVBoxSound subbox6_84 :=
  LRCompactVLeafParameters.sound checked6_84


def subbox6_85 : CertificateBox :=
  ⟨((9 : ℚ) / 32), ((5 : ℚ) / 16), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩

theorem checked6_85 :
    LRCompactVLeafParameters.check subbox6_85 .short = true := by decide +kernel

theorem subsound6_85 : LRCompactVBoxSound subbox6_85 :=
  LRCompactVLeafParameters.sound checked6_85


def subbox6_86 : CertificateBox :=
  ⟨((9 : ℚ) / 32), ((5 : ℚ) / 16), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩

theorem checked6_86 :
    LRCompactVLeafParameters.check subbox6_86 .short = true := by decide +kernel

theorem subsound6_86 : LRCompactVBoxSound subbox6_86 :=
  LRCompactVLeafParameters.sound checked6_86


def subbox6_87 : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((9 : ℚ) / 32), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩

theorem checked6_87 :
    LRCompactVLeafParameters.check subbox6_87 .short = true := by decide +kernel

theorem subsound6_87 : LRCompactVBoxSound subbox6_87 :=
  LRCompactVLeafParameters.sound checked6_87


def subbox6_88 : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((9 : ℚ) / 32), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩

theorem checked6_88 :
    LRCompactVLeafParameters.check subbox6_88 .short = true := by decide +kernel

theorem subsound6_88 : LRCompactVBoxSound subbox6_88 :=
  LRCompactVLeafParameters.sound checked6_88


def subbox6_89 : CertificateBox :=
  ⟨((9 : ℚ) / 32), ((5 : ℚ) / 16), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩

theorem checked6_89 :
    LRCompactVLeafParameters.check subbox6_89 .short = true := by decide +kernel

theorem subsound6_89 : LRCompactVBoxSound subbox6_89 :=
  LRCompactVLeafParameters.sound checked6_89


def subbox6_90 : CertificateBox :=
  ⟨((9 : ℚ) / 32), ((5 : ℚ) / 16), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩

theorem checked6_90 :
    LRCompactVLeafParameters.check subbox6_90 .short = true := by decide +kernel

theorem subsound6_90 : LRCompactVBoxSound subbox6_90 :=
  LRCompactVLeafParameters.sound checked6_90


def subbox6_91 : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((5 : ℚ) / 12), ((7 : ℚ) / 16), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩

theorem checked6_91 :
    LRCompactVLeafParameters.check subbox6_91 .short = true := by decide +kernel

theorem subsound6_91 : LRCompactVBoxSound subbox6_91 :=
  LRCompactVLeafParameters.sound checked6_91


def subbox6_92 : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩

theorem checked6_92 :
    LRCompactVLeafParameters.check subbox6_92 .short = true := by decide +kernel

theorem subsound6_92 : LRCompactVBoxSound subbox6_92 :=
  LRCompactVLeafParameters.sound checked6_92


def subbox6_93 : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((7 : ℚ) / 16), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩

theorem checked6_93 :
    LRCompactVLeafParameters.check subbox6_93 .short = true := by decide +kernel

theorem subsound6_93 : LRCompactVBoxSound subbox6_93 :=
  LRCompactVLeafParameters.sound checked6_93


def subbox6_94 : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩

theorem checked6_94 :
    LRCompactVLeafParameters.check subbox6_94 .short = true := by decide +kernel

theorem subsound6_94 : LRCompactVBoxSound subbox6_94 :=
  LRCompactVLeafParameters.sound checked6_94


def subbox6_95 : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((5 : ℚ) / 12), ((7 : ℚ) / 16), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩

theorem checked6_95 :
    LRCompactVLeafParameters.check subbox6_95 .short = true := by decide +kernel

theorem subsound6_95 : LRCompactVBoxSound subbox6_95 :=
  LRCompactVLeafParameters.sound checked6_95


def subbox6_96 : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩

theorem checked6_96 :
    LRCompactVLeafParameters.check subbox6_96 .short = true := by decide +kernel

theorem subsound6_96 : LRCompactVBoxSound subbox6_96 :=
  LRCompactVLeafParameters.sound checked6_96


def subbox6_97 : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((7 : ℚ) / 16), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩

theorem checked6_97 :
    LRCompactVLeafParameters.check subbox6_97 .short = true := by decide +kernel

theorem subsound6_97 : LRCompactVBoxSound subbox6_97 :=
  LRCompactVLeafParameters.sound checked6_97


def subbox6_98 : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩

theorem checked6_98 :
    LRCompactVLeafParameters.check subbox6_98 .short = true := by decide +kernel

theorem subsound6_98 : LRCompactVBoxSound subbox6_98 :=
  LRCompactVLeafParameters.sound checked6_98


def subbox6_99 : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩

theorem checked6_99 :
    LRCompactVLeafParameters.check subbox6_99 .short = true := by decide +kernel

theorem subsound6_99 : LRCompactVBoxSound subbox6_99 :=
  LRCompactVLeafParameters.sound checked6_99


def subbox6_100 : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩

theorem checked6_100 :
    LRCompactVLeafParameters.check subbox6_100 .short = true := by decide +kernel

theorem subsound6_100 : LRCompactVBoxSound subbox6_100 :=
  LRCompactVLeafParameters.sound checked6_100


def subbox6_101 : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩

theorem checked6_101 :
    LRCompactVLeafParameters.check subbox6_101 .short = true := by decide +kernel

theorem subsound6_101 : LRCompactVBoxSound subbox6_101 :=
  LRCompactVLeafParameters.sound checked6_101


def subbox6_102 : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩

theorem checked6_102 :
    LRCompactVLeafParameters.check subbox6_102 .short = true := by decide +kernel

theorem subsound6_102 : LRCompactVBoxSound subbox6_102 :=
  LRCompactVLeafParameters.sound checked6_102


def subbox6_103 : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩

theorem checked6_103 :
    LRCompactVLeafParameters.check subbox6_103 .short = true := by decide +kernel

theorem subsound6_103 : LRCompactVBoxSound subbox6_103 :=
  LRCompactVLeafParameters.sound checked6_103


def subbox6_104 : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩

theorem checked6_104 :
    LRCompactVLeafParameters.check subbox6_104 .short = true := by decide +kernel

theorem subsound6_104 : LRCompactVBoxSound subbox6_104 :=
  LRCompactVLeafParameters.sound checked6_104


def subbox6_105 : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩

theorem checked6_105 :
    LRCompactVLeafParameters.check subbox6_105 .short = true := by decide +kernel

theorem subsound6_105 : LRCompactVBoxSound subbox6_105 :=
  LRCompactVLeafParameters.sound checked6_105


def subbox6_106 : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩

theorem checked6_106 :
    LRCompactVLeafParameters.check subbox6_106 .short = true := by decide +kernel

theorem subsound6_106 : LRCompactVBoxSound subbox6_106 :=
  LRCompactVLeafParameters.sound checked6_106


def joinbox6_rLRRLL : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((3 : ℚ) / 8), ((1 : ℚ) / 3), ((5 : ℚ) / 12), ((71 : ℚ) / 80), ((37 : ℚ) / 40)⟩


def joinbox6_rLRRLLL : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((3 : ℚ) / 8), ((1 : ℚ) / 3), ((5 : ℚ) / 12), ((71 : ℚ) / 80), ((29 : ℚ) / 32)⟩


def joinbox6_rLRRLLLL : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((5 : ℚ) / 16), ((1 : ℚ) / 3), ((5 : ℚ) / 12), ((71 : ℚ) / 80), ((29 : ℚ) / 32)⟩


def joinbox6_rLRRLLLLL : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((5 : ℚ) / 16), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((71 : ℚ) / 80), ((29 : ℚ) / 32)⟩


def joinbox6_rLRRLLLLLL : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((5 : ℚ) / 16), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩


def joinbox6_rLRRLLLLLR : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((5 : ℚ) / 16), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩


def joinbox6_rLRRLLLLR : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((5 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((71 : ℚ) / 80), ((29 : ℚ) / 32)⟩


def joinbox6_rLRRLLLLRL : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((5 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩


def joinbox6_rLRRLLLLRLR : CertificateBox :=
  ⟨((9 : ℚ) / 32), ((5 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩


def joinbox6_rLRRLLLLRR : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((5 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩


def joinbox6_rLRRLLLR : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((3 : ℚ) / 8), ((1 : ℚ) / 3), ((5 : ℚ) / 12), ((71 : ℚ) / 80), ((29 : ℚ) / 32)⟩


def joinbox6_rLRRLLLRL : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((3 : ℚ) / 8), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((71 : ℚ) / 80), ((29 : ℚ) / 32)⟩


def joinbox6_rLRRLLLRLL : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((3 : ℚ) / 8), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩


def joinbox6_rLRRLLLRLLL : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩


def joinbox6_rLRRLLLRLLR : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩


def joinbox6_rLRRLLLRLR : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((3 : ℚ) / 8), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩


def joinbox6_rLRRLLLRLRR : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩


def joinbox6_rLRRLLLRR : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((3 : ℚ) / 8), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((71 : ℚ) / 80), ((29 : ℚ) / 32)⟩


def joinbox6_rLRRLLLRRL : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((3 : ℚ) / 8), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩


def joinbox6_rLRRLLLRRLL : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩


def joinbox6_rLRRLLLRRLR : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩


def joinbox6_rLRRLLLRRR : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((3 : ℚ) / 8), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩


def joinbox6_rLRRLLLRRRL : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩


def joinbox6_rLRRLLLRRRR : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩


def joinbox6_rLRRLLR : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((3 : ℚ) / 8), ((1 : ℚ) / 3), ((5 : ℚ) / 12), ((29 : ℚ) / 32), ((37 : ℚ) / 40)⟩


def joinbox6_rLRRLLRL : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((5 : ℚ) / 16), ((1 : ℚ) / 3), ((5 : ℚ) / 12), ((29 : ℚ) / 32), ((37 : ℚ) / 40)⟩


def joinbox6_rLRRLLRLL : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((5 : ℚ) / 16), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((29 : ℚ) / 32), ((37 : ℚ) / 40)⟩


def joinbox6_rLRRLLRLLL : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((5 : ℚ) / 16), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩


def joinbox6_rLRRLLRLLR : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((5 : ℚ) / 16), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩


def joinbox6_rLRRLLRLR : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((5 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((29 : ℚ) / 32), ((37 : ℚ) / 40)⟩


def joinbox6_rLRRLLRLRL : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((5 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩


def joinbox6_rLRRLLRLRR : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((5 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩


def joinbox6_rLRRLLRR : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((3 : ℚ) / 8), ((1 : ℚ) / 3), ((5 : ℚ) / 12), ((29 : ℚ) / 32), ((37 : ℚ) / 40)⟩


def joinbox6_rLRRLLRRL : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((3 : ℚ) / 8), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((29 : ℚ) / 32), ((37 : ℚ) / 40)⟩


def joinbox6_rLRRLLRRLL : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((3 : ℚ) / 8), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩


def joinbox6_rLRRLLRRLLR : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩


def joinbox6_rLRRLLRRLR : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((3 : ℚ) / 8), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩


def joinbox6_rLRRLLRRR : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((3 : ℚ) / 8), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((29 : ℚ) / 32), ((37 : ℚ) / 40)⟩


def joinbox6_rLRRLLRRRL : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((3 : ℚ) / 8), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩


def joinbox6_rLRRLLRRRLL : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩


def joinbox6_rLRRLLRRRLR : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩


def joinbox6_rLRRLLRRRR : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((3 : ℚ) / 8), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩


def joinbox6_rLRRLLRRRRL : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩


def joinbox6_rLRRLLRRRRR : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩


def joinbox6_rLRRLR : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((1 : ℚ) / 2), ((71 : ℚ) / 80), ((37 : ℚ) / 40)⟩


def joinbox6_rLRRLRL : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((1 : ℚ) / 2), ((71 : ℚ) / 80), ((29 : ℚ) / 32)⟩


def joinbox6_rLRRLRLL : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((5 : ℚ) / 16), ((5 : ℚ) / 12), ((1 : ℚ) / 2), ((71 : ℚ) / 80), ((29 : ℚ) / 32)⟩


def joinbox6_rLRRLRLLL : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((5 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((71 : ℚ) / 80), ((29 : ℚ) / 32)⟩


def joinbox6_rLRRLRLLLL : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((5 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩


def joinbox6_rLRRLRLLLLL : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((9 : ℚ) / 32), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩


def joinbox6_rLRRLRLLLLR : CertificateBox :=
  ⟨((9 : ℚ) / 32), ((5 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩


def joinbox6_rLRRLRLLLR : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((5 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩


def joinbox6_rLRRLRLLLRL : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((9 : ℚ) / 32), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩


def joinbox6_rLRRLRLLLRR : CertificateBox :=
  ⟨((9 : ℚ) / 32), ((5 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩


def joinbox6_rLRRLRLLR : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((5 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((71 : ℚ) / 80), ((29 : ℚ) / 32)⟩


def joinbox6_rLRRLRLLRL : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((5 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩


def joinbox6_rLRRLRLLRLL : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((9 : ℚ) / 32), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩


def joinbox6_rLRRLRLLRLR : CertificateBox :=
  ⟨((9 : ℚ) / 32), ((5 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩


def joinbox6_rLRRLRLLRR : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((5 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩


def joinbox6_rLRRLRLLRRL : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((9 : ℚ) / 32), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩


def joinbox6_rLRRLRLLRRR : CertificateBox :=
  ⟨((9 : ℚ) / 32), ((5 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩


def joinbox6_rLRRLRLR : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((1 : ℚ) / 2), ((71 : ℚ) / 80), ((29 : ℚ) / 32)⟩


def joinbox6_rLRRLRLRL : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((71 : ℚ) / 80), ((29 : ℚ) / 32)⟩


def joinbox6_rLRRLRLRLL : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩


def joinbox6_rLRRLRLRLLL : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩


def joinbox6_rLRRLRLRLLR : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩


def joinbox6_rLRRLRLRLR : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩


def joinbox6_rLRRLRLRLRL : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩


def joinbox6_rLRRLRLRLRR : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩


def joinbox6_rLRRLRLRR : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((3 : ℚ) / 8), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((71 : ℚ) / 80), ((29 : ℚ) / 32)⟩


def joinbox6_rLRRLRLRRL : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((3 : ℚ) / 8), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩


def joinbox6_rLRRLRLRRLL : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩


def joinbox6_rLRRLRLRRLR : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩


def joinbox6_rLRRLRLRRR : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((3 : ℚ) / 8), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩


def joinbox6_rLRRLRLRRRL : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩


def joinbox6_rLRRLRLRRRR : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩


def joinbox6_rLRRLRR : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((1 : ℚ) / 2), ((29 : ℚ) / 32), ((37 : ℚ) / 40)⟩


def joinbox6_rLRRLRRL : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((5 : ℚ) / 16), ((5 : ℚ) / 12), ((1 : ℚ) / 2), ((29 : ℚ) / 32), ((37 : ℚ) / 40)⟩


def joinbox6_rLRRLRRLL : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((5 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((29 : ℚ) / 32), ((37 : ℚ) / 40)⟩


def joinbox6_rLRRLRRLLL : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((5 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩


def joinbox6_rLRRLRRLLLR : CertificateBox :=
  ⟨((9 : ℚ) / 32), ((5 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩


def joinbox6_rLRRLRRLLR : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((5 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩


def joinbox6_rLRRLRRLLRR : CertificateBox :=
  ⟨((9 : ℚ) / 32), ((5 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩


def joinbox6_rLRRLRRLR : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((5 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((29 : ℚ) / 32), ((37 : ℚ) / 40)⟩


def joinbox6_rLRRLRRLRL : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((5 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩


def joinbox6_rLRRLRRLRLL : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((9 : ℚ) / 32), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩


def joinbox6_rLRRLRRLRLR : CertificateBox :=
  ⟨((9 : ℚ) / 32), ((5 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩


def joinbox6_rLRRLRRLRR : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((5 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩


def joinbox6_rLRRLRRLRRL : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((9 : ℚ) / 32), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩


def joinbox6_rLRRLRRLRRR : CertificateBox :=
  ⟨((9 : ℚ) / 32), ((5 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩


def joinbox6_rLRRLRRR : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((1 : ℚ) / 2), ((29 : ℚ) / 32), ((37 : ℚ) / 40)⟩


def joinbox6_rLRRLRRRL : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((29 : ℚ) / 32), ((37 : ℚ) / 40)⟩


def joinbox6_rLRRLRRRLL : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩


def joinbox6_rLRRLRRRLLL : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩


def joinbox6_rLRRLRRRLLR : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩


def joinbox6_rLRRLRRRLR : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩


def joinbox6_rLRRLRRRLRL : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩


def joinbox6_rLRRLRRRLRR : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩


def joinbox6_rLRRLRRRR : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((3 : ℚ) / 8), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((29 : ℚ) / 32), ((37 : ℚ) / 40)⟩


def joinbox6_rLRRLRRRRL : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((3 : ℚ) / 8), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩


def joinbox6_rLRRLRRRRLL : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩


def joinbox6_rLRRLRRRRLR : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩


def joinbox6_rLRRLRRRRR : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((3 : ℚ) / 8), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩


def joinbox6_rLRRLRRRRRL : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩


def joinbox6_rLRRLRRRRRR : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩


theorem sound6 : LRCompactVBoxSound box6 :=
  (LRCompactVBoxSound.join (box := box6) .k ((5 : ℚ) / 12)
    (LRCompactVBoxSound.join (box := joinbox6_rLRRLL) .chi ((29 : ℚ) / 32)
      (LRCompactVBoxSound.join (box := joinbox6_rLRRLLL) .s ((5 : ℚ) / 16)
        (LRCompactVBoxSound.join (box := joinbox6_rLRRLLLL) .k ((3 : ℚ) / 8)
          (LRCompactVBoxSound.join (box := joinbox6_rLRRLLLLL) .chi ((287 : ℚ) / 320)
            (LRCompactVBoxSound.join (box := joinbox6_rLRRLLLLLL) .s ((9 : ℚ) / 32)
              subsound6_0
              subsound6_1)
            (LRCompactVBoxSound.join (box := joinbox6_rLRRLLLLLR) .s ((9 : ℚ) / 32)
              subsound6_2
              subsound6_3))
          (LRCompactVBoxSound.join (box := joinbox6_rLRRLLLLR) .chi ((287 : ℚ) / 320)
            (LRCompactVBoxSound.join (box := joinbox6_rLRRLLLLRL) .s ((9 : ℚ) / 32)
              subsound6_4
              (LRCompactVBoxSound.join (box := joinbox6_rLRRLLLLRLR) .k ((19 : ℚ) / 48)
                subsound6_5
                subsound6_6))
            (LRCompactVBoxSound.join (box := joinbox6_rLRRLLLLRR) .s ((9 : ℚ) / 32)
              subsound6_7
              subsound6_8)))
        (LRCompactVBoxSound.join (box := joinbox6_rLRRLLLR) .k ((3 : ℚ) / 8)
          (LRCompactVBoxSound.join (box := joinbox6_rLRRLLLRL) .chi ((287 : ℚ) / 320)
            (LRCompactVBoxSound.join (box := joinbox6_rLRRLLLRLL) .s ((11 : ℚ) / 32)
              (LRCompactVBoxSound.join (box := joinbox6_rLRRLLLRLLL) .k ((17 : ℚ) / 48)
                subsound6_9
                subsound6_10)
              (LRCompactVBoxSound.join (box := joinbox6_rLRRLLLRLLR) .k ((17 : ℚ) / 48)
                subsound6_11
                subsound6_12))
            (LRCompactVBoxSound.join (box := joinbox6_rLRRLLLRLR) .s ((11 : ℚ) / 32)
              subsound6_13
              (LRCompactVBoxSound.join (box := joinbox6_rLRRLLLRLRR) .k ((17 : ℚ) / 48)
                subsound6_14
                subsound6_15)))
          (LRCompactVBoxSound.join (box := joinbox6_rLRRLLLRR) .chi ((287 : ℚ) / 320)
            (LRCompactVBoxSound.join (box := joinbox6_rLRRLLLRRL) .s ((11 : ℚ) / 32)
              (LRCompactVBoxSound.join (box := joinbox6_rLRRLLLRRLL) .k ((19 : ℚ) / 48)
                subsound6_16
                subsound6_17)
              (LRCompactVBoxSound.join (box := joinbox6_rLRRLLLRRLR) .k ((19 : ℚ) / 48)
                subsound6_18
                subsound6_19))
            (LRCompactVBoxSound.join (box := joinbox6_rLRRLLLRRR) .s ((11 : ℚ) / 32)
              (LRCompactVBoxSound.join (box := joinbox6_rLRRLLLRRRL) .k ((19 : ℚ) / 48)
                subsound6_20
                subsound6_21)
              (LRCompactVBoxSound.join (box := joinbox6_rLRRLLLRRRR) .k ((19 : ℚ) / 48)
                subsound6_22
                subsound6_23)))))
      (LRCompactVBoxSound.join (box := joinbox6_rLRRLLR) .s ((5 : ℚ) / 16)
        (LRCompactVBoxSound.join (box := joinbox6_rLRRLLRL) .k ((3 : ℚ) / 8)
          (LRCompactVBoxSound.join (box := joinbox6_rLRRLLRLL) .chi ((293 : ℚ) / 320)
            (LRCompactVBoxSound.join (box := joinbox6_rLRRLLRLLL) .s ((9 : ℚ) / 32)
              subsound6_24
              subsound6_25)
            (LRCompactVBoxSound.join (box := joinbox6_rLRRLLRLLR) .s ((9 : ℚ) / 32)
              subsound6_26
              subsound6_27))
          (LRCompactVBoxSound.join (box := joinbox6_rLRRLLRLR) .chi ((293 : ℚ) / 320)
            (LRCompactVBoxSound.join (box := joinbox6_rLRRLLRLRL) .s ((9 : ℚ) / 32)
              subsound6_28
              subsound6_29)
            (LRCompactVBoxSound.join (box := joinbox6_rLRRLLRLRR) .s ((9 : ℚ) / 32)
              subsound6_30
              subsound6_31)))
        (LRCompactVBoxSound.join (box := joinbox6_rLRRLLRR) .k ((3 : ℚ) / 8)
          (LRCompactVBoxSound.join (box := joinbox6_rLRRLLRRL) .chi ((293 : ℚ) / 320)
            (LRCompactVBoxSound.join (box := joinbox6_rLRRLLRRLL) .s ((11 : ℚ) / 32)
              subsound6_32
              (LRCompactVBoxSound.join (box := joinbox6_rLRRLLRRLLR) .k ((17 : ℚ) / 48)
                subsound6_33
                subsound6_34))
            (LRCompactVBoxSound.join (box := joinbox6_rLRRLLRRLR) .s ((11 : ℚ) / 32)
              subsound6_35
              subsound6_36))
          (LRCompactVBoxSound.join (box := joinbox6_rLRRLLRRR) .chi ((293 : ℚ) / 320)
            (LRCompactVBoxSound.join (box := joinbox6_rLRRLLRRRL) .s ((11 : ℚ) / 32)
              (LRCompactVBoxSound.join (box := joinbox6_rLRRLLRRRLL) .k ((19 : ℚ) / 48)
                subsound6_37
                subsound6_38)
              (LRCompactVBoxSound.join (box := joinbox6_rLRRLLRRRLR) .k ((19 : ℚ) / 48)
                subsound6_39
                subsound6_40))
            (LRCompactVBoxSound.join (box := joinbox6_rLRRLLRRRR) .s ((11 : ℚ) / 32)
              (LRCompactVBoxSound.join (box := joinbox6_rLRRLLRRRRL) .k ((19 : ℚ) / 48)
                subsound6_41
                subsound6_42)
              (LRCompactVBoxSound.join (box := joinbox6_rLRRLLRRRRR) .k ((19 : ℚ) / 48)
                subsound6_43
                subsound6_44))))))
    (LRCompactVBoxSound.join (box := joinbox6_rLRRLR) .chi ((29 : ℚ) / 32)
      (LRCompactVBoxSound.join (box := joinbox6_rLRRLRL) .s ((5 : ℚ) / 16)
        (LRCompactVBoxSound.join (box := joinbox6_rLRRLRLL) .k ((11 : ℚ) / 24)
          (LRCompactVBoxSound.join (box := joinbox6_rLRRLRLLL) .chi ((287 : ℚ) / 320)
            (LRCompactVBoxSound.join (box := joinbox6_rLRRLRLLLL) .s ((9 : ℚ) / 32)
              (LRCompactVBoxSound.join (box := joinbox6_rLRRLRLLLLL) .k ((7 : ℚ) / 16)
                subsound6_45
                subsound6_46)
              (LRCompactVBoxSound.join (box := joinbox6_rLRRLRLLLLR) .k ((7 : ℚ) / 16)
                subsound6_47
                subsound6_48))
            (LRCompactVBoxSound.join (box := joinbox6_rLRRLRLLLR) .s ((9 : ℚ) / 32)
              (LRCompactVBoxSound.join (box := joinbox6_rLRRLRLLLRL) .k ((7 : ℚ) / 16)
                subsound6_49
                subsound6_50)
              (LRCompactVBoxSound.join (box := joinbox6_rLRRLRLLLRR) .k ((7 : ℚ) / 16)
                subsound6_51
                subsound6_52)))
          (LRCompactVBoxSound.join (box := joinbox6_rLRRLRLLR) .chi ((287 : ℚ) / 320)
            (LRCompactVBoxSound.join (box := joinbox6_rLRRLRLLRL) .s ((9 : ℚ) / 32)
              (LRCompactVBoxSound.join (box := joinbox6_rLRRLRLLRLL) .k ((23 : ℚ) / 48)
                subsound6_53
                subsound6_54)
              (LRCompactVBoxSound.join (box := joinbox6_rLRRLRLLRLR) .k ((23 : ℚ) / 48)
                subsound6_55
                subsound6_56))
            (LRCompactVBoxSound.join (box := joinbox6_rLRRLRLLRR) .s ((9 : ℚ) / 32)
              (LRCompactVBoxSound.join (box := joinbox6_rLRRLRLLRRL) .k ((23 : ℚ) / 48)
                subsound6_57
                subsound6_58)
              (LRCompactVBoxSound.join (box := joinbox6_rLRRLRLLRRR) .k ((23 : ℚ) / 48)
                subsound6_59
                subsound6_60))))
        (LRCompactVBoxSound.join (box := joinbox6_rLRRLRLR) .k ((11 : ℚ) / 24)
          (LRCompactVBoxSound.join (box := joinbox6_rLRRLRLRL) .chi ((287 : ℚ) / 320)
            (LRCompactVBoxSound.join (box := joinbox6_rLRRLRLRLL) .s ((11 : ℚ) / 32)
              (LRCompactVBoxSound.join (box := joinbox6_rLRRLRLRLLL) .k ((7 : ℚ) / 16)
                subsound6_61
                subsound6_62)
              (LRCompactVBoxSound.join (box := joinbox6_rLRRLRLRLLR) .k ((7 : ℚ) / 16)
                subsound6_63
                subsound6_64))
            (LRCompactVBoxSound.join (box := joinbox6_rLRRLRLRLR) .s ((11 : ℚ) / 32)
              (LRCompactVBoxSound.join (box := joinbox6_rLRRLRLRLRL) .k ((7 : ℚ) / 16)
                subsound6_65
                subsound6_66)
              (LRCompactVBoxSound.join (box := joinbox6_rLRRLRLRLRR) .k ((7 : ℚ) / 16)
                subsound6_67
                subsound6_68)))
          (LRCompactVBoxSound.join (box := joinbox6_rLRRLRLRR) .chi ((287 : ℚ) / 320)
            (LRCompactVBoxSound.join (box := joinbox6_rLRRLRLRRL) .s ((11 : ℚ) / 32)
              (LRCompactVBoxSound.join (box := joinbox6_rLRRLRLRRLL) .k ((23 : ℚ) / 48)
                subsound6_69
                subsound6_70)
              (LRCompactVBoxSound.join (box := joinbox6_rLRRLRLRRLR) .k ((23 : ℚ) / 48)
                subsound6_71
                subsound6_72))
            (LRCompactVBoxSound.join (box := joinbox6_rLRRLRLRRR) .s ((11 : ℚ) / 32)
              (LRCompactVBoxSound.join (box := joinbox6_rLRRLRLRRRL) .k ((23 : ℚ) / 48)
                subsound6_73
                subsound6_74)
              (LRCompactVBoxSound.join (box := joinbox6_rLRRLRLRRRR) .k ((23 : ℚ) / 48)
                subsound6_75
                subsound6_76)))))
      (LRCompactVBoxSound.join (box := joinbox6_rLRRLRR) .s ((5 : ℚ) / 16)
        (LRCompactVBoxSound.join (box := joinbox6_rLRRLRRL) .k ((11 : ℚ) / 24)
          (LRCompactVBoxSound.join (box := joinbox6_rLRRLRRLL) .chi ((293 : ℚ) / 320)
            (LRCompactVBoxSound.join (box := joinbox6_rLRRLRRLLL) .s ((9 : ℚ) / 32)
              subsound6_77
              (LRCompactVBoxSound.join (box := joinbox6_rLRRLRRLLLR) .k ((7 : ℚ) / 16)
                subsound6_78
                subsound6_79))
            (LRCompactVBoxSound.join (box := joinbox6_rLRRLRRLLR) .s ((9 : ℚ) / 32)
              subsound6_80
              (LRCompactVBoxSound.join (box := joinbox6_rLRRLRRLLRR) .k ((7 : ℚ) / 16)
                subsound6_81
                subsound6_82)))
          (LRCompactVBoxSound.join (box := joinbox6_rLRRLRRLR) .chi ((293 : ℚ) / 320)
            (LRCompactVBoxSound.join (box := joinbox6_rLRRLRRLRL) .s ((9 : ℚ) / 32)
              (LRCompactVBoxSound.join (box := joinbox6_rLRRLRRLRLL) .k ((23 : ℚ) / 48)
                subsound6_83
                subsound6_84)
              (LRCompactVBoxSound.join (box := joinbox6_rLRRLRRLRLR) .k ((23 : ℚ) / 48)
                subsound6_85
                subsound6_86))
            (LRCompactVBoxSound.join (box := joinbox6_rLRRLRRLRR) .s ((9 : ℚ) / 32)
              (LRCompactVBoxSound.join (box := joinbox6_rLRRLRRLRRL) .k ((23 : ℚ) / 48)
                subsound6_87
                subsound6_88)
              (LRCompactVBoxSound.join (box := joinbox6_rLRRLRRLRRR) .k ((23 : ℚ) / 48)
                subsound6_89
                subsound6_90))))
        (LRCompactVBoxSound.join (box := joinbox6_rLRRLRRR) .k ((11 : ℚ) / 24)
          (LRCompactVBoxSound.join (box := joinbox6_rLRRLRRRL) .chi ((293 : ℚ) / 320)
            (LRCompactVBoxSound.join (box := joinbox6_rLRRLRRRLL) .s ((11 : ℚ) / 32)
              (LRCompactVBoxSound.join (box := joinbox6_rLRRLRRRLLL) .k ((7 : ℚ) / 16)
                subsound6_91
                subsound6_92)
              (LRCompactVBoxSound.join (box := joinbox6_rLRRLRRRLLR) .k ((7 : ℚ) / 16)
                subsound6_93
                subsound6_94))
            (LRCompactVBoxSound.join (box := joinbox6_rLRRLRRRLR) .s ((11 : ℚ) / 32)
              (LRCompactVBoxSound.join (box := joinbox6_rLRRLRRRLRL) .k ((7 : ℚ) / 16)
                subsound6_95
                subsound6_96)
              (LRCompactVBoxSound.join (box := joinbox6_rLRRLRRRLRR) .k ((7 : ℚ) / 16)
                subsound6_97
                subsound6_98)))
          (LRCompactVBoxSound.join (box := joinbox6_rLRRLRRRR) .chi ((293 : ℚ) / 320)
            (LRCompactVBoxSound.join (box := joinbox6_rLRRLRRRRL) .s ((11 : ℚ) / 32)
              (LRCompactVBoxSound.join (box := joinbox6_rLRRLRRRRLL) .k ((23 : ℚ) / 48)
                subsound6_99
                subsound6_100)
              (LRCompactVBoxSound.join (box := joinbox6_rLRRLRRRRLR) .k ((23 : ℚ) / 48)
                subsound6_101
                subsound6_102))
            (LRCompactVBoxSound.join (box := joinbox6_rLRRLRRRRR) .s ((11 : ℚ) / 32)
              (LRCompactVBoxSound.join (box := joinbox6_rLRRLRRRRRL) .k ((23 : ℚ) / 48)
                subsound6_103
                subsound6_104)
              (LRCompactVBoxSound.join (box := joinbox6_rLRRLRRRRRR) .k ((23 : ℚ) / 48)
                subsound6_105
                subsound6_106)))))))

end CourtadeKumar.GeneratedLRCompactVLowR
