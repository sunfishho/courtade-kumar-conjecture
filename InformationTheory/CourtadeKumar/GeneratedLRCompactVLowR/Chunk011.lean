import InformationTheory.CourtadeKumar.LRCompactVBasicReplay

/-! Frozen basic compact-V replay.
Plan SHA-256: ce3f7a498b2b9caf346dcf88ce7861f8cc091af8cd93f5624d7684e21322ecd5
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CourtadeKumar.GeneratedLRCompactVLowR

-- 84 accepted leaves below path rRRLL.
def box11 : CertificateBox where
  sLo := ((1 : ℚ) / 4)
  sHi := ((3 : ℚ) / 8)
  kLo := ((1 : ℚ) / 3)
  kHi := ((1 : ℚ) / 2)
  chiLo := ((37 : ℚ) / 40)
  chiHi := ((77 : ℚ) / 80)


def subbox11_0 : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((9 : ℚ) / 32), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((37 : ℚ) / 40), ((299 : ℚ) / 320)⟩

theorem checked11_0 :
    LRCompactVLeafParameters.check subbox11_0 .short = true := by decide +kernel

theorem subsound11_0 : LRCompactVBoxSound subbox11_0 :=
  LRCompactVLeafParameters.sound checked11_0


def subbox11_1 : CertificateBox :=
  ⟨((9 : ℚ) / 32), ((5 : ℚ) / 16), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((37 : ℚ) / 40), ((299 : ℚ) / 320)⟩

theorem checked11_1 :
    LRCompactVLeafParameters.check subbox11_1 .short = true := by decide +kernel

theorem subsound11_1 : LRCompactVBoxSound subbox11_1 :=
  LRCompactVLeafParameters.sound checked11_1


def subbox11_2 : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((9 : ℚ) / 32), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((299 : ℚ) / 320), ((151 : ℚ) / 160)⟩

theorem checked11_2 :
    LRCompactVLeafParameters.check subbox11_2 .short = true := by decide +kernel

theorem subsound11_2 : LRCompactVBoxSound subbox11_2 :=
  LRCompactVLeafParameters.sound checked11_2


def subbox11_3 : CertificateBox :=
  ⟨((9 : ℚ) / 32), ((5 : ℚ) / 16), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((299 : ℚ) / 320), ((151 : ℚ) / 160)⟩

theorem checked11_3 :
    LRCompactVLeafParameters.check subbox11_3 .short = true := by decide +kernel

theorem subsound11_3 : LRCompactVBoxSound subbox11_3 :=
  LRCompactVLeafParameters.sound checked11_3


def subbox11_4 : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((9 : ℚ) / 32), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((37 : ℚ) / 40), ((299 : ℚ) / 320)⟩

theorem checked11_4 :
    LRCompactVLeafParameters.check subbox11_4 .short = true := by decide +kernel

theorem subsound11_4 : LRCompactVBoxSound subbox11_4 :=
  LRCompactVLeafParameters.sound checked11_4


def subbox11_5 : CertificateBox :=
  ⟨((9 : ℚ) / 32), ((5 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((37 : ℚ) / 40), ((299 : ℚ) / 320)⟩

theorem checked11_5 :
    LRCompactVLeafParameters.check subbox11_5 .long = true := by decide +kernel

theorem subsound11_5 : LRCompactVBoxSound subbox11_5 :=
  LRCompactVLeafParameters.sound checked11_5


def subbox11_6 : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((9 : ℚ) / 32), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((299 : ℚ) / 320), ((151 : ℚ) / 160)⟩

theorem checked11_6 :
    LRCompactVLeafParameters.check subbox11_6 .short = true := by decide +kernel

theorem subsound11_6 : LRCompactVBoxSound subbox11_6 :=
  LRCompactVLeafParameters.sound checked11_6


def subbox11_7 : CertificateBox :=
  ⟨((9 : ℚ) / 32), ((5 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((299 : ℚ) / 320), ((151 : ℚ) / 160)⟩

theorem checked11_7 :
    LRCompactVLeafParameters.check subbox11_7 .short = true := by decide +kernel

theorem subsound11_7 : LRCompactVBoxSound subbox11_7 :=
  LRCompactVLeafParameters.sound checked11_7


def subbox11_8 : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((37 : ℚ) / 40), ((299 : ℚ) / 320)⟩

theorem checked11_8 :
    LRCompactVLeafParameters.check subbox11_8 .long = true := by decide +kernel

theorem subsound11_8 : LRCompactVBoxSound subbox11_8 :=
  LRCompactVLeafParameters.sound checked11_8


def subbox11_9 : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((37 : ℚ) / 40), ((299 : ℚ) / 320)⟩

theorem checked11_9 :
    LRCompactVLeafParameters.check subbox11_9 .long = true := by decide +kernel

theorem subsound11_9 : LRCompactVBoxSound subbox11_9 :=
  LRCompactVLeafParameters.sound checked11_9


def subbox11_10 : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((299 : ℚ) / 320), ((151 : ℚ) / 160)⟩

theorem checked11_10 :
    LRCompactVLeafParameters.check subbox11_10 .short = true := by decide +kernel

theorem subsound11_10 : LRCompactVBoxSound subbox11_10 :=
  LRCompactVLeafParameters.sound checked11_10


def subbox11_11 : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((299 : ℚ) / 320), ((151 : ℚ) / 160)⟩

theorem checked11_11 :
    LRCompactVLeafParameters.check subbox11_11 .long = true := by decide +kernel

theorem subsound11_11 : LRCompactVBoxSound subbox11_11 :=
  LRCompactVLeafParameters.sound checked11_11


def subbox11_12 : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((37 : ℚ) / 40), ((299 : ℚ) / 320)⟩

theorem checked11_12 :
    LRCompactVLeafParameters.check subbox11_12 .long = true := by decide +kernel

theorem subsound11_12 : LRCompactVBoxSound subbox11_12 :=
  LRCompactVLeafParameters.sound checked11_12


def subbox11_13 : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((3 : ℚ) / 8), ((19 : ℚ) / 48), ((37 : ℚ) / 40), ((299 : ℚ) / 320)⟩

theorem checked11_13 :
    LRCompactVLeafParameters.check subbox11_13 .short = true := by decide +kernel

theorem subsound11_13 : LRCompactVBoxSound subbox11_13 :=
  LRCompactVLeafParameters.sound checked11_13


def subbox11_14 : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((19 : ℚ) / 48), ((5 : ℚ) / 12), ((37 : ℚ) / 40), ((299 : ℚ) / 320)⟩

theorem checked11_14 :
    LRCompactVLeafParameters.check subbox11_14 .short = true := by decide +kernel

theorem subsound11_14 : LRCompactVBoxSound subbox11_14 :=
  LRCompactVLeafParameters.sound checked11_14


def subbox11_15 : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((299 : ℚ) / 320), ((151 : ℚ) / 160)⟩

theorem checked11_15 :
    LRCompactVLeafParameters.check subbox11_15 .long = true := by decide +kernel

theorem subsound11_15 : LRCompactVBoxSound subbox11_15 :=
  LRCompactVLeafParameters.sound checked11_15


def subbox11_16 : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((3 : ℚ) / 8), ((19 : ℚ) / 48), ((299 : ℚ) / 320), ((151 : ℚ) / 160)⟩

theorem checked11_16 :
    LRCompactVLeafParameters.check subbox11_16 .short = true := by decide +kernel

theorem subsound11_16 : LRCompactVBoxSound subbox11_16 :=
  LRCompactVLeafParameters.sound checked11_16


def subbox11_17 : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((19 : ℚ) / 48), ((5 : ℚ) / 12), ((299 : ℚ) / 320), ((151 : ℚ) / 160)⟩

theorem checked11_17 :
    LRCompactVLeafParameters.check subbox11_17 .short = true := by decide +kernel

theorem subsound11_17 : LRCompactVBoxSound subbox11_17 :=
  LRCompactVLeafParameters.sound checked11_17


def subbox11_18 : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((9 : ℚ) / 32), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((151 : ℚ) / 160), ((61 : ℚ) / 64)⟩

theorem checked11_18 :
    LRCompactVLeafParameters.check subbox11_18 .short = true := by decide +kernel

theorem subsound11_18 : LRCompactVBoxSound subbox11_18 :=
  LRCompactVLeafParameters.sound checked11_18


def subbox11_19 : CertificateBox :=
  ⟨((9 : ℚ) / 32), ((5 : ℚ) / 16), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((151 : ℚ) / 160), ((61 : ℚ) / 64)⟩

theorem checked11_19 :
    LRCompactVLeafParameters.check subbox11_19 .short = true := by decide +kernel

theorem subsound11_19 : LRCompactVBoxSound subbox11_19 :=
  LRCompactVLeafParameters.sound checked11_19


def subbox11_20 : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((9 : ℚ) / 32), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((61 : ℚ) / 64), ((77 : ℚ) / 80)⟩

theorem checked11_20 :
    LRCompactVLeafParameters.check subbox11_20 .short = true := by decide +kernel

theorem subsound11_20 : LRCompactVBoxSound subbox11_20 :=
  LRCompactVLeafParameters.sound checked11_20


def subbox11_21 : CertificateBox :=
  ⟨((9 : ℚ) / 32), ((5 : ℚ) / 16), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((61 : ℚ) / 64), ((77 : ℚ) / 80)⟩

theorem checked11_21 :
    LRCompactVLeafParameters.check subbox11_21 .short = true := by decide +kernel

theorem subsound11_21 : LRCompactVBoxSound subbox11_21 :=
  LRCompactVLeafParameters.sound checked11_21


def subbox11_22 : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((9 : ℚ) / 32), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((151 : ℚ) / 160), ((61 : ℚ) / 64)⟩

theorem checked11_22 :
    LRCompactVLeafParameters.check subbox11_22 .short = true := by decide +kernel

theorem subsound11_22 : LRCompactVBoxSound subbox11_22 :=
  LRCompactVLeafParameters.sound checked11_22


def subbox11_23 : CertificateBox :=
  ⟨((9 : ℚ) / 32), ((5 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((151 : ℚ) / 160), ((61 : ℚ) / 64)⟩

theorem checked11_23 :
    LRCompactVLeafParameters.check subbox11_23 .short = true := by decide +kernel

theorem subsound11_23 : LRCompactVBoxSound subbox11_23 :=
  LRCompactVLeafParameters.sound checked11_23


def subbox11_24 : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((9 : ℚ) / 32), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((61 : ℚ) / 64), ((77 : ℚ) / 80)⟩

theorem checked11_24 :
    LRCompactVLeafParameters.check subbox11_24 .short = true := by decide +kernel

theorem subsound11_24 : LRCompactVBoxSound subbox11_24 :=
  LRCompactVLeafParameters.sound checked11_24


def subbox11_25 : CertificateBox :=
  ⟨((9 : ℚ) / 32), ((5 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((61 : ℚ) / 64), ((77 : ℚ) / 80)⟩

theorem checked11_25 :
    LRCompactVLeafParameters.check subbox11_25 .short = true := by decide +kernel

theorem subsound11_25 : LRCompactVBoxSound subbox11_25 :=
  LRCompactVLeafParameters.sound checked11_25


def subbox11_26 : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((151 : ℚ) / 160), ((61 : ℚ) / 64)⟩

theorem checked11_26 :
    LRCompactVLeafParameters.check subbox11_26 .short = true := by decide +kernel

theorem subsound11_26 : LRCompactVBoxSound subbox11_26 :=
  LRCompactVLeafParameters.sound checked11_26


def subbox11_27 : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((151 : ℚ) / 160), ((61 : ℚ) / 64)⟩

theorem checked11_27 :
    LRCompactVLeafParameters.check subbox11_27 .long = true := by decide +kernel

theorem subsound11_27 : LRCompactVBoxSound subbox11_27 :=
  LRCompactVLeafParameters.sound checked11_27


def subbox11_28 : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((61 : ℚ) / 64), ((77 : ℚ) / 80)⟩

theorem checked11_28 :
    LRCompactVLeafParameters.check subbox11_28 .short = true := by decide +kernel

theorem subsound11_28 : LRCompactVBoxSound subbox11_28 :=
  LRCompactVLeafParameters.sound checked11_28


def subbox11_29 : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((61 : ℚ) / 64), ((77 : ℚ) / 80)⟩

theorem checked11_29 :
    LRCompactVLeafParameters.check subbox11_29 .accurateLog = true := by decide +kernel

theorem subsound11_29 : LRCompactVBoxSound subbox11_29 :=
  LRCompactVLeafParameters.sound checked11_29


def subbox11_30 : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((151 : ℚ) / 160), ((61 : ℚ) / 64)⟩

theorem checked11_30 :
    LRCompactVLeafParameters.check subbox11_30 .long = true := by decide +kernel

theorem subsound11_30 : LRCompactVBoxSound subbox11_30 :=
  LRCompactVLeafParameters.sound checked11_30


def subbox11_31 : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((151 : ℚ) / 160), ((61 : ℚ) / 64)⟩

theorem checked11_31 :
    LRCompactVLeafParameters.check subbox11_31 .long = true := by decide +kernel

theorem subsound11_31 : LRCompactVBoxSound subbox11_31 :=
  LRCompactVLeafParameters.sound checked11_31


def subbox11_32 : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((61 : ℚ) / 64), ((77 : ℚ) / 80)⟩

theorem checked11_32 :
    LRCompactVLeafParameters.check subbox11_32 .long = true := by decide +kernel

theorem subsound11_32 : LRCompactVBoxSound subbox11_32 :=
  LRCompactVLeafParameters.sound checked11_32


def subbox11_33 : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((61 : ℚ) / 64), ((77 : ℚ) / 80)⟩

theorem checked11_33 :
    LRCompactVLeafParameters.check subbox11_33 .long = true := by decide +kernel

theorem subsound11_33 : LRCompactVBoxSound subbox11_33 :=
  LRCompactVLeafParameters.sound checked11_33


def subbox11_34 : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((9 : ℚ) / 32), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((37 : ℚ) / 40), ((299 : ℚ) / 320)⟩

theorem checked11_34 :
    LRCompactVLeafParameters.check subbox11_34 .long = true := by decide +kernel

theorem subsound11_34 : LRCompactVBoxSound subbox11_34 :=
  LRCompactVLeafParameters.sound checked11_34


def subbox11_35 : CertificateBox :=
  ⟨((9 : ℚ) / 32), ((5 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((37 : ℚ) / 40), ((299 : ℚ) / 320)⟩

theorem checked11_35 :
    LRCompactVLeafParameters.check subbox11_35 .long = true := by decide +kernel

theorem subsound11_35 : LRCompactVBoxSound subbox11_35 :=
  LRCompactVLeafParameters.sound checked11_35


def subbox11_36 : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((9 : ℚ) / 32), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((299 : ℚ) / 320), ((151 : ℚ) / 160)⟩

theorem checked11_36 :
    LRCompactVLeafParameters.check subbox11_36 .short = true := by decide +kernel

theorem subsound11_36 : LRCompactVBoxSound subbox11_36 :=
  LRCompactVLeafParameters.sound checked11_36


def subbox11_37 : CertificateBox :=
  ⟨((9 : ℚ) / 32), ((5 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((299 : ℚ) / 320), ((151 : ℚ) / 160)⟩

theorem checked11_37 :
    LRCompactVLeafParameters.check subbox11_37 .long = true := by decide +kernel

theorem subsound11_37 : LRCompactVBoxSound subbox11_37 :=
  LRCompactVLeafParameters.sound checked11_37


def subbox11_38 : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((9 : ℚ) / 32), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((37 : ℚ) / 40), ((299 : ℚ) / 320)⟩

theorem checked11_38 :
    LRCompactVLeafParameters.check subbox11_38 .short = true := by decide +kernel

theorem subsound11_38 : LRCompactVBoxSound subbox11_38 :=
  LRCompactVLeafParameters.sound checked11_38


def subbox11_39 : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((9 : ℚ) / 32), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((37 : ℚ) / 40), ((299 : ℚ) / 320)⟩

theorem checked11_39 :
    LRCompactVLeafParameters.check subbox11_39 .short = true := by decide +kernel

theorem subsound11_39 : LRCompactVBoxSound subbox11_39 :=
  LRCompactVLeafParameters.sound checked11_39


def subbox11_40 : CertificateBox :=
  ⟨((9 : ℚ) / 32), ((5 : ℚ) / 16), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((37 : ℚ) / 40), ((299 : ℚ) / 320)⟩

theorem checked11_40 :
    LRCompactVLeafParameters.check subbox11_40 .short = true := by decide +kernel

theorem subsound11_40 : LRCompactVBoxSound subbox11_40 :=
  LRCompactVLeafParameters.sound checked11_40


def subbox11_41 : CertificateBox :=
  ⟨((9 : ℚ) / 32), ((5 : ℚ) / 16), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((37 : ℚ) / 40), ((299 : ℚ) / 320)⟩

theorem checked11_41 :
    LRCompactVLeafParameters.check subbox11_41 .short = true := by decide +kernel

theorem subsound11_41 : LRCompactVBoxSound subbox11_41 :=
  LRCompactVLeafParameters.sound checked11_41


def subbox11_42 : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((9 : ℚ) / 32), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((299 : ℚ) / 320), ((151 : ℚ) / 160)⟩

theorem checked11_42 :
    LRCompactVLeafParameters.check subbox11_42 .long = true := by decide +kernel

theorem subsound11_42 : LRCompactVBoxSound subbox11_42 :=
  LRCompactVLeafParameters.sound checked11_42


def subbox11_43 : CertificateBox :=
  ⟨((9 : ℚ) / 32), ((5 : ℚ) / 16), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((299 : ℚ) / 320), ((151 : ℚ) / 160)⟩

theorem checked11_43 :
    LRCompactVLeafParameters.check subbox11_43 .short = true := by decide +kernel

theorem subsound11_43 : LRCompactVBoxSound subbox11_43 :=
  LRCompactVLeafParameters.sound checked11_43


def subbox11_44 : CertificateBox :=
  ⟨((9 : ℚ) / 32), ((5 : ℚ) / 16), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((299 : ℚ) / 320), ((151 : ℚ) / 160)⟩

theorem checked11_44 :
    LRCompactVLeafParameters.check subbox11_44 .short = true := by decide +kernel

theorem subsound11_44 : LRCompactVBoxSound subbox11_44 :=
  LRCompactVLeafParameters.sound checked11_44


def subbox11_45 : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((5 : ℚ) / 12), ((7 : ℚ) / 16), ((37 : ℚ) / 40), ((299 : ℚ) / 320)⟩

theorem checked11_45 :
    LRCompactVLeafParameters.check subbox11_45 .short = true := by decide +kernel

theorem subsound11_45 : LRCompactVBoxSound subbox11_45 :=
  LRCompactVLeafParameters.sound checked11_45


def subbox11_46 : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((37 : ℚ) / 40), ((299 : ℚ) / 320)⟩

theorem checked11_46 :
    LRCompactVLeafParameters.check subbox11_46 .short = true := by decide +kernel

theorem subsound11_46 : LRCompactVBoxSound subbox11_46 :=
  LRCompactVLeafParameters.sound checked11_46


def subbox11_47 : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((7 : ℚ) / 16), ((37 : ℚ) / 40), ((299 : ℚ) / 320)⟩

theorem checked11_47 :
    LRCompactVLeafParameters.check subbox11_47 .short = true := by decide +kernel

theorem subsound11_47 : LRCompactVBoxSound subbox11_47 :=
  LRCompactVLeafParameters.sound checked11_47


def subbox11_48 : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((37 : ℚ) / 40), ((299 : ℚ) / 320)⟩

theorem checked11_48 :
    LRCompactVLeafParameters.check subbox11_48 .short = true := by decide +kernel

theorem subsound11_48 : LRCompactVBoxSound subbox11_48 :=
  LRCompactVLeafParameters.sound checked11_48


def subbox11_49 : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((5 : ℚ) / 12), ((7 : ℚ) / 16), ((299 : ℚ) / 320), ((151 : ℚ) / 160)⟩

theorem checked11_49 :
    LRCompactVLeafParameters.check subbox11_49 .short = true := by decide +kernel

theorem subsound11_49 : LRCompactVBoxSound subbox11_49 :=
  LRCompactVLeafParameters.sound checked11_49


def subbox11_50 : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((299 : ℚ) / 320), ((151 : ℚ) / 160)⟩

theorem checked11_50 :
    LRCompactVLeafParameters.check subbox11_50 .short = true := by decide +kernel

theorem subsound11_50 : LRCompactVBoxSound subbox11_50 :=
  LRCompactVLeafParameters.sound checked11_50


def subbox11_51 : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((7 : ℚ) / 16), ((299 : ℚ) / 320), ((151 : ℚ) / 160)⟩

theorem checked11_51 :
    LRCompactVLeafParameters.check subbox11_51 .short = true := by decide +kernel

theorem subsound11_51 : LRCompactVBoxSound subbox11_51 :=
  LRCompactVLeafParameters.sound checked11_51


def subbox11_52 : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((299 : ℚ) / 320), ((151 : ℚ) / 160)⟩

theorem checked11_52 :
    LRCompactVLeafParameters.check subbox11_52 .short = true := by decide +kernel

theorem subsound11_52 : LRCompactVBoxSound subbox11_52 :=
  LRCompactVLeafParameters.sound checked11_52


def subbox11_53 : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((37 : ℚ) / 40), ((299 : ℚ) / 320)⟩

theorem checked11_53 :
    LRCompactVLeafParameters.check subbox11_53 .short = true := by decide +kernel

theorem subsound11_53 : LRCompactVBoxSound subbox11_53 :=
  LRCompactVLeafParameters.sound checked11_53


def subbox11_54 : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((37 : ℚ) / 40), ((299 : ℚ) / 320)⟩

theorem checked11_54 :
    LRCompactVLeafParameters.check subbox11_54 .short = true := by decide +kernel

theorem subsound11_54 : LRCompactVBoxSound subbox11_54 :=
  LRCompactVLeafParameters.sound checked11_54


def subbox11_55 : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((37 : ℚ) / 40), ((299 : ℚ) / 320)⟩

theorem checked11_55 :
    LRCompactVLeafParameters.check subbox11_55 .short = true := by decide +kernel

theorem subsound11_55 : LRCompactVBoxSound subbox11_55 :=
  LRCompactVLeafParameters.sound checked11_55


def subbox11_56 : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((37 : ℚ) / 40), ((299 : ℚ) / 320)⟩

theorem checked11_56 :
    LRCompactVLeafParameters.check subbox11_56 .short = true := by decide +kernel

theorem subsound11_56 : LRCompactVBoxSound subbox11_56 :=
  LRCompactVLeafParameters.sound checked11_56


def subbox11_57 : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((299 : ℚ) / 320), ((151 : ℚ) / 160)⟩

theorem checked11_57 :
    LRCompactVLeafParameters.check subbox11_57 .short = true := by decide +kernel

theorem subsound11_57 : LRCompactVBoxSound subbox11_57 :=
  LRCompactVLeafParameters.sound checked11_57


def subbox11_58 : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((299 : ℚ) / 320), ((151 : ℚ) / 160)⟩

theorem checked11_58 :
    LRCompactVLeafParameters.check subbox11_58 .short = true := by decide +kernel

theorem subsound11_58 : LRCompactVBoxSound subbox11_58 :=
  LRCompactVLeafParameters.sound checked11_58


def subbox11_59 : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((299 : ℚ) / 320), ((151 : ℚ) / 160)⟩

theorem checked11_59 :
    LRCompactVLeafParameters.check subbox11_59 .short = true := by decide +kernel

theorem subsound11_59 : LRCompactVBoxSound subbox11_59 :=
  LRCompactVLeafParameters.sound checked11_59


def subbox11_60 : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((299 : ℚ) / 320), ((151 : ℚ) / 160)⟩

theorem checked11_60 :
    LRCompactVLeafParameters.check subbox11_60 .short = true := by decide +kernel

theorem subsound11_60 : LRCompactVBoxSound subbox11_60 :=
  LRCompactVLeafParameters.sound checked11_60


def subbox11_61 : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((9 : ℚ) / 32), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((151 : ℚ) / 160), ((61 : ℚ) / 64)⟩

theorem checked11_61 :
    LRCompactVLeafParameters.check subbox11_61 .short = true := by decide +kernel

theorem subsound11_61 : LRCompactVBoxSound subbox11_61 :=
  LRCompactVLeafParameters.sound checked11_61


def subbox11_62 : CertificateBox :=
  ⟨((9 : ℚ) / 32), ((5 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((151 : ℚ) / 160), ((61 : ℚ) / 64)⟩

theorem checked11_62 :
    LRCompactVLeafParameters.check subbox11_62 .long = true := by decide +kernel

theorem subsound11_62 : LRCompactVBoxSound subbox11_62 :=
  LRCompactVLeafParameters.sound checked11_62


def subbox11_63 : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((9 : ℚ) / 32), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((61 : ℚ) / 64), ((77 : ℚ) / 80)⟩

theorem checked11_63 :
    LRCompactVLeafParameters.check subbox11_63 .short = true := by decide +kernel

theorem subsound11_63 : LRCompactVBoxSound subbox11_63 :=
  LRCompactVLeafParameters.sound checked11_63


def subbox11_64 : CertificateBox :=
  ⟨((9 : ℚ) / 32), ((5 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((61 : ℚ) / 64), ((77 : ℚ) / 80)⟩

theorem checked11_64 :
    LRCompactVLeafParameters.check subbox11_64 .long = true := by decide +kernel

theorem subsound11_64 : LRCompactVBoxSound subbox11_64 :=
  LRCompactVLeafParameters.sound checked11_64


def subbox11_65 : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((9 : ℚ) / 32), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((151 : ℚ) / 160), ((61 : ℚ) / 64)⟩

theorem checked11_65 :
    LRCompactVLeafParameters.check subbox11_65 .long = true := by decide +kernel

theorem subsound11_65 : LRCompactVBoxSound subbox11_65 :=
  LRCompactVLeafParameters.sound checked11_65


def subbox11_66 : CertificateBox :=
  ⟨((9 : ℚ) / 32), ((5 : ℚ) / 16), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((151 : ℚ) / 160), ((61 : ℚ) / 64)⟩

theorem checked11_66 :
    LRCompactVLeafParameters.check subbox11_66 .short = true := by decide +kernel

theorem subsound11_66 : LRCompactVBoxSound subbox11_66 :=
  LRCompactVLeafParameters.sound checked11_66


def subbox11_67 : CertificateBox :=
  ⟨((9 : ℚ) / 32), ((5 : ℚ) / 16), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((151 : ℚ) / 160), ((61 : ℚ) / 64)⟩

theorem checked11_67 :
    LRCompactVLeafParameters.check subbox11_67 .short = true := by decide +kernel

theorem subsound11_67 : LRCompactVBoxSound subbox11_67 :=
  LRCompactVLeafParameters.sound checked11_67


def subbox11_68 : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((9 : ℚ) / 32), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((61 : ℚ) / 64), ((77 : ℚ) / 80)⟩

theorem checked11_68 :
    LRCompactVLeafParameters.check subbox11_68 .long = true := by decide +kernel

theorem subsound11_68 : LRCompactVBoxSound subbox11_68 :=
  LRCompactVLeafParameters.sound checked11_68


def subbox11_69 : CertificateBox :=
  ⟨((9 : ℚ) / 32), ((5 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((61 : ℚ) / 64), ((77 : ℚ) / 80)⟩

theorem checked11_69 :
    LRCompactVLeafParameters.check subbox11_69 .long = true := by decide +kernel

theorem subsound11_69 : LRCompactVBoxSound subbox11_69 :=
  LRCompactVLeafParameters.sound checked11_69


def subbox11_70 : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((151 : ℚ) / 160), ((61 : ℚ) / 64)⟩

theorem checked11_70 :
    LRCompactVLeafParameters.check subbox11_70 .long = true := by decide +kernel

theorem subsound11_70 : LRCompactVBoxSound subbox11_70 :=
  LRCompactVLeafParameters.sound checked11_70


def subbox11_71 : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((7 : ℚ) / 16), ((151 : ℚ) / 160), ((61 : ℚ) / 64)⟩

theorem checked11_71 :
    LRCompactVLeafParameters.check subbox11_71 .short = true := by decide +kernel

theorem subsound11_71 : LRCompactVBoxSound subbox11_71 :=
  LRCompactVLeafParameters.sound checked11_71


def subbox11_72 : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((151 : ℚ) / 160), ((61 : ℚ) / 64)⟩

theorem checked11_72 :
    LRCompactVLeafParameters.check subbox11_72 .short = true := by decide +kernel

theorem subsound11_72 : LRCompactVBoxSound subbox11_72 :=
  LRCompactVLeafParameters.sound checked11_72


def subbox11_73 : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((61 : ℚ) / 64), ((77 : ℚ) / 80)⟩

theorem checked11_73 :
    LRCompactVLeafParameters.check subbox11_73 .long = true := by decide +kernel

theorem subsound11_73 : LRCompactVBoxSound subbox11_73 :=
  LRCompactVLeafParameters.sound checked11_73


def subbox11_74 : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((7 : ℚ) / 16), ((61 : ℚ) / 64), ((77 : ℚ) / 80)⟩

theorem checked11_74 :
    LRCompactVLeafParameters.check subbox11_74 .short = true := by decide +kernel

theorem subsound11_74 : LRCompactVBoxSound subbox11_74 :=
  LRCompactVLeafParameters.sound checked11_74


def subbox11_75 : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((61 : ℚ) / 64), ((77 : ℚ) / 80)⟩

theorem checked11_75 :
    LRCompactVLeafParameters.check subbox11_75 .short = true := by decide +kernel

theorem subsound11_75 : LRCompactVBoxSound subbox11_75 :=
  LRCompactVLeafParameters.sound checked11_75


def subbox11_76 : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((151 : ℚ) / 160), ((61 : ℚ) / 64)⟩

theorem checked11_76 :
    LRCompactVLeafParameters.check subbox11_76 .short = true := by decide +kernel

theorem subsound11_76 : LRCompactVBoxSound subbox11_76 :=
  LRCompactVLeafParameters.sound checked11_76


def subbox11_77 : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((151 : ℚ) / 160), ((61 : ℚ) / 64)⟩

theorem checked11_77 :
    LRCompactVLeafParameters.check subbox11_77 .short = true := by decide +kernel

theorem subsound11_77 : LRCompactVBoxSound subbox11_77 :=
  LRCompactVLeafParameters.sound checked11_77


def subbox11_78 : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((151 : ℚ) / 160), ((61 : ℚ) / 64)⟩

theorem checked11_78 :
    LRCompactVLeafParameters.check subbox11_78 .short = true := by decide +kernel

theorem subsound11_78 : LRCompactVBoxSound subbox11_78 :=
  LRCompactVLeafParameters.sound checked11_78


def subbox11_79 : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((151 : ℚ) / 160), ((61 : ℚ) / 64)⟩

theorem checked11_79 :
    LRCompactVLeafParameters.check subbox11_79 .short = true := by decide +kernel

theorem subsound11_79 : LRCompactVBoxSound subbox11_79 :=
  LRCompactVLeafParameters.sound checked11_79


def subbox11_80 : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((61 : ℚ) / 64), ((77 : ℚ) / 80)⟩

theorem checked11_80 :
    LRCompactVLeafParameters.check subbox11_80 .short = true := by decide +kernel

theorem subsound11_80 : LRCompactVBoxSound subbox11_80 :=
  LRCompactVLeafParameters.sound checked11_80


def subbox11_81 : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((61 : ℚ) / 64), ((77 : ℚ) / 80)⟩

theorem checked11_81 :
    LRCompactVLeafParameters.check subbox11_81 .short = true := by decide +kernel

theorem subsound11_81 : LRCompactVBoxSound subbox11_81 :=
  LRCompactVLeafParameters.sound checked11_81


def subbox11_82 : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((61 : ℚ) / 64), ((77 : ℚ) / 80)⟩

theorem checked11_82 :
    LRCompactVLeafParameters.check subbox11_82 .short = true := by decide +kernel

theorem subsound11_82 : LRCompactVBoxSound subbox11_82 :=
  LRCompactVLeafParameters.sound checked11_82


def subbox11_83 : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((61 : ℚ) / 64), ((77 : ℚ) / 80)⟩

theorem checked11_83 :
    LRCompactVLeafParameters.check subbox11_83 .short = true := by decide +kernel

theorem subsound11_83 : LRCompactVBoxSound subbox11_83 :=
  LRCompactVLeafParameters.sound checked11_83


def joinbox11_rRRLLL : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((3 : ℚ) / 8), ((1 : ℚ) / 3), ((5 : ℚ) / 12), ((37 : ℚ) / 40), ((77 : ℚ) / 80)⟩


def joinbox11_rRRLLLL : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((3 : ℚ) / 8), ((1 : ℚ) / 3), ((5 : ℚ) / 12), ((37 : ℚ) / 40), ((151 : ℚ) / 160)⟩


def joinbox11_rRRLLLLL : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((5 : ℚ) / 16), ((1 : ℚ) / 3), ((5 : ℚ) / 12), ((37 : ℚ) / 40), ((151 : ℚ) / 160)⟩


def joinbox11_rRRLLLLLL : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((5 : ℚ) / 16), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((37 : ℚ) / 40), ((151 : ℚ) / 160)⟩


def joinbox11_rRRLLLLLLL : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((5 : ℚ) / 16), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((37 : ℚ) / 40), ((299 : ℚ) / 320)⟩


def joinbox11_rRRLLLLLLR : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((5 : ℚ) / 16), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((299 : ℚ) / 320), ((151 : ℚ) / 160)⟩


def joinbox11_rRRLLLLLR : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((5 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((37 : ℚ) / 40), ((151 : ℚ) / 160)⟩


def joinbox11_rRRLLLLLRL : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((5 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((37 : ℚ) / 40), ((299 : ℚ) / 320)⟩


def joinbox11_rRRLLLLLRR : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((5 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((299 : ℚ) / 320), ((151 : ℚ) / 160)⟩


def joinbox11_rRRLLLLR : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((3 : ℚ) / 8), ((1 : ℚ) / 3), ((5 : ℚ) / 12), ((37 : ℚ) / 40), ((151 : ℚ) / 160)⟩


def joinbox11_rRRLLLLRL : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((3 : ℚ) / 8), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((37 : ℚ) / 40), ((151 : ℚ) / 160)⟩


def joinbox11_rRRLLLLRLL : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((3 : ℚ) / 8), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((37 : ℚ) / 40), ((299 : ℚ) / 320)⟩


def joinbox11_rRRLLLLRLR : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((3 : ℚ) / 8), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((299 : ℚ) / 320), ((151 : ℚ) / 160)⟩


def joinbox11_rRRLLLLRR : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((3 : ℚ) / 8), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((37 : ℚ) / 40), ((151 : ℚ) / 160)⟩


def joinbox11_rRRLLLLRRL : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((3 : ℚ) / 8), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((37 : ℚ) / 40), ((299 : ℚ) / 320)⟩


def joinbox11_rRRLLLLRRLR : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((37 : ℚ) / 40), ((299 : ℚ) / 320)⟩


def joinbox11_rRRLLLLRRR : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((3 : ℚ) / 8), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((299 : ℚ) / 320), ((151 : ℚ) / 160)⟩


def joinbox11_rRRLLLLRRRR : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((299 : ℚ) / 320), ((151 : ℚ) / 160)⟩


def joinbox11_rRRLLLR : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((3 : ℚ) / 8), ((1 : ℚ) / 3), ((5 : ℚ) / 12), ((151 : ℚ) / 160), ((77 : ℚ) / 80)⟩


def joinbox11_rRRLLLRL : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((5 : ℚ) / 16), ((1 : ℚ) / 3), ((5 : ℚ) / 12), ((151 : ℚ) / 160), ((77 : ℚ) / 80)⟩


def joinbox11_rRRLLLRLL : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((5 : ℚ) / 16), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((151 : ℚ) / 160), ((77 : ℚ) / 80)⟩


def joinbox11_rRRLLLRLLL : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((5 : ℚ) / 16), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((151 : ℚ) / 160), ((61 : ℚ) / 64)⟩


def joinbox11_rRRLLLRLLR : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((5 : ℚ) / 16), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((61 : ℚ) / 64), ((77 : ℚ) / 80)⟩


def joinbox11_rRRLLLRLR : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((5 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((151 : ℚ) / 160), ((77 : ℚ) / 80)⟩


def joinbox11_rRRLLLRLRL : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((5 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((151 : ℚ) / 160), ((61 : ℚ) / 64)⟩


def joinbox11_rRRLLLRLRR : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((5 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((61 : ℚ) / 64), ((77 : ℚ) / 80)⟩


def joinbox11_rRRLLLRR : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((3 : ℚ) / 8), ((1 : ℚ) / 3), ((5 : ℚ) / 12), ((151 : ℚ) / 160), ((77 : ℚ) / 80)⟩


def joinbox11_rRRLLLRRL : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((3 : ℚ) / 8), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((151 : ℚ) / 160), ((77 : ℚ) / 80)⟩


def joinbox11_rRRLLLRRLL : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((3 : ℚ) / 8), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((151 : ℚ) / 160), ((61 : ℚ) / 64)⟩


def joinbox11_rRRLLLRRLR : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((3 : ℚ) / 8), ((1 : ℚ) / 3), ((3 : ℚ) / 8), ((61 : ℚ) / 64), ((77 : ℚ) / 80)⟩


def joinbox11_rRRLLLRRR : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((3 : ℚ) / 8), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((151 : ℚ) / 160), ((77 : ℚ) / 80)⟩


def joinbox11_rRRLLLRRRL : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((3 : ℚ) / 8), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((151 : ℚ) / 160), ((61 : ℚ) / 64)⟩


def joinbox11_rRRLLLRRRR : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((3 : ℚ) / 8), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((61 : ℚ) / 64), ((77 : ℚ) / 80)⟩


def joinbox11_rRRLLR : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((1 : ℚ) / 2), ((37 : ℚ) / 40), ((77 : ℚ) / 80)⟩


def joinbox11_rRRLLRL : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((1 : ℚ) / 2), ((37 : ℚ) / 40), ((151 : ℚ) / 160)⟩


def joinbox11_rRRLLRLL : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((5 : ℚ) / 16), ((5 : ℚ) / 12), ((1 : ℚ) / 2), ((37 : ℚ) / 40), ((151 : ℚ) / 160)⟩


def joinbox11_rRRLLRLLL : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((5 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((37 : ℚ) / 40), ((151 : ℚ) / 160)⟩


def joinbox11_rRRLLRLLLL : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((5 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((37 : ℚ) / 40), ((299 : ℚ) / 320)⟩


def joinbox11_rRRLLRLLLR : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((5 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((299 : ℚ) / 320), ((151 : ℚ) / 160)⟩


def joinbox11_rRRLLRLLR : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((5 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((37 : ℚ) / 40), ((151 : ℚ) / 160)⟩


def joinbox11_rRRLLRLLRL : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((5 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((37 : ℚ) / 40), ((299 : ℚ) / 320)⟩


def joinbox11_rRRLLRLLRLL : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((9 : ℚ) / 32), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((37 : ℚ) / 40), ((299 : ℚ) / 320)⟩


def joinbox11_rRRLLRLLRLR : CertificateBox :=
  ⟨((9 : ℚ) / 32), ((5 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((37 : ℚ) / 40), ((299 : ℚ) / 320)⟩


def joinbox11_rRRLLRLLRR : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((5 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((299 : ℚ) / 320), ((151 : ℚ) / 160)⟩


def joinbox11_rRRLLRLLRRR : CertificateBox :=
  ⟨((9 : ℚ) / 32), ((5 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((299 : ℚ) / 320), ((151 : ℚ) / 160)⟩


def joinbox11_rRRLLRLR : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((1 : ℚ) / 2), ((37 : ℚ) / 40), ((151 : ℚ) / 160)⟩


def joinbox11_rRRLLRLRL : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((37 : ℚ) / 40), ((151 : ℚ) / 160)⟩


def joinbox11_rRRLLRLRLL : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((37 : ℚ) / 40), ((299 : ℚ) / 320)⟩


def joinbox11_rRRLLRLRLLL : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((37 : ℚ) / 40), ((299 : ℚ) / 320)⟩


def joinbox11_rRRLLRLRLLR : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((37 : ℚ) / 40), ((299 : ℚ) / 320)⟩


def joinbox11_rRRLLRLRLR : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((299 : ℚ) / 320), ((151 : ℚ) / 160)⟩


def joinbox11_rRRLLRLRLRL : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((299 : ℚ) / 320), ((151 : ℚ) / 160)⟩


def joinbox11_rRRLLRLRLRR : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((299 : ℚ) / 320), ((151 : ℚ) / 160)⟩


def joinbox11_rRRLLRLRR : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((3 : ℚ) / 8), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((37 : ℚ) / 40), ((151 : ℚ) / 160)⟩


def joinbox11_rRRLLRLRRL : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((3 : ℚ) / 8), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((37 : ℚ) / 40), ((299 : ℚ) / 320)⟩


def joinbox11_rRRLLRLRRLL : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((37 : ℚ) / 40), ((299 : ℚ) / 320)⟩


def joinbox11_rRRLLRLRRLR : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((37 : ℚ) / 40), ((299 : ℚ) / 320)⟩


def joinbox11_rRRLLRLRRR : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((3 : ℚ) / 8), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((299 : ℚ) / 320), ((151 : ℚ) / 160)⟩


def joinbox11_rRRLLRLRRRL : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((299 : ℚ) / 320), ((151 : ℚ) / 160)⟩


def joinbox11_rRRLLRLRRRR : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((299 : ℚ) / 320), ((151 : ℚ) / 160)⟩


def joinbox11_rRRLLRR : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((1 : ℚ) / 2), ((151 : ℚ) / 160), ((77 : ℚ) / 80)⟩


def joinbox11_rRRLLRRL : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((5 : ℚ) / 16), ((5 : ℚ) / 12), ((1 : ℚ) / 2), ((151 : ℚ) / 160), ((77 : ℚ) / 80)⟩


def joinbox11_rRRLLRRLL : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((5 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((151 : ℚ) / 160), ((77 : ℚ) / 80)⟩


def joinbox11_rRRLLRRLLL : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((5 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((151 : ℚ) / 160), ((61 : ℚ) / 64)⟩


def joinbox11_rRRLLRRLLR : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((5 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((61 : ℚ) / 64), ((77 : ℚ) / 80)⟩


def joinbox11_rRRLLRRLR : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((5 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((151 : ℚ) / 160), ((77 : ℚ) / 80)⟩


def joinbox11_rRRLLRRLRL : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((5 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((151 : ℚ) / 160), ((61 : ℚ) / 64)⟩


def joinbox11_rRRLLRRLRLR : CertificateBox :=
  ⟨((9 : ℚ) / 32), ((5 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((151 : ℚ) / 160), ((61 : ℚ) / 64)⟩


def joinbox11_rRRLLRRLRR : CertificateBox :=
  ⟨((1 : ℚ) / 4), ((5 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((61 : ℚ) / 64), ((77 : ℚ) / 80)⟩


def joinbox11_rRRLLRRR : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((1 : ℚ) / 2), ((151 : ℚ) / 160), ((77 : ℚ) / 80)⟩


def joinbox11_rRRLLRRRL : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((151 : ℚ) / 160), ((77 : ℚ) / 80)⟩


def joinbox11_rRRLLRRRLL : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((151 : ℚ) / 160), ((61 : ℚ) / 64)⟩


def joinbox11_rRRLLRRRLLR : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((151 : ℚ) / 160), ((61 : ℚ) / 64)⟩


def joinbox11_rRRLLRRRLR : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((61 : ℚ) / 64), ((77 : ℚ) / 80)⟩


def joinbox11_rRRLLRRRLRR : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((61 : ℚ) / 64), ((77 : ℚ) / 80)⟩


def joinbox11_rRRLLRRRR : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((3 : ℚ) / 8), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((151 : ℚ) / 160), ((77 : ℚ) / 80)⟩


def joinbox11_rRRLLRRRRL : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((3 : ℚ) / 8), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((151 : ℚ) / 160), ((61 : ℚ) / 64)⟩


def joinbox11_rRRLLRRRRLL : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((151 : ℚ) / 160), ((61 : ℚ) / 64)⟩


def joinbox11_rRRLLRRRRLR : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((151 : ℚ) / 160), ((61 : ℚ) / 64)⟩


def joinbox11_rRRLLRRRRR : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((3 : ℚ) / 8), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((61 : ℚ) / 64), ((77 : ℚ) / 80)⟩


def joinbox11_rRRLLRRRRRL : CertificateBox :=
  ⟨((5 : ℚ) / 16), ((11 : ℚ) / 32), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((61 : ℚ) / 64), ((77 : ℚ) / 80)⟩


def joinbox11_rRRLLRRRRRR : CertificateBox :=
  ⟨((11 : ℚ) / 32), ((3 : ℚ) / 8), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((61 : ℚ) / 64), ((77 : ℚ) / 80)⟩


theorem sound11 : LRCompactVBoxSound box11 :=
  (LRCompactVBoxSound.join (box := box11) .k ((5 : ℚ) / 12)
    (LRCompactVBoxSound.join (box := joinbox11_rRRLLL) .chi ((151 : ℚ) / 160)
      (LRCompactVBoxSound.join (box := joinbox11_rRRLLLL) .s ((5 : ℚ) / 16)
        (LRCompactVBoxSound.join (box := joinbox11_rRRLLLLL) .k ((3 : ℚ) / 8)
          (LRCompactVBoxSound.join (box := joinbox11_rRRLLLLLL) .chi ((299 : ℚ) / 320)
            (LRCompactVBoxSound.join (box := joinbox11_rRRLLLLLLL) .s ((9 : ℚ) / 32)
              subsound11_0
              subsound11_1)
            (LRCompactVBoxSound.join (box := joinbox11_rRRLLLLLLR) .s ((9 : ℚ) / 32)
              subsound11_2
              subsound11_3))
          (LRCompactVBoxSound.join (box := joinbox11_rRRLLLLLR) .chi ((299 : ℚ) / 320)
            (LRCompactVBoxSound.join (box := joinbox11_rRRLLLLLRL) .s ((9 : ℚ) / 32)
              subsound11_4
              subsound11_5)
            (LRCompactVBoxSound.join (box := joinbox11_rRRLLLLLRR) .s ((9 : ℚ) / 32)
              subsound11_6
              subsound11_7)))
        (LRCompactVBoxSound.join (box := joinbox11_rRRLLLLR) .k ((3 : ℚ) / 8)
          (LRCompactVBoxSound.join (box := joinbox11_rRRLLLLRL) .chi ((299 : ℚ) / 320)
            (LRCompactVBoxSound.join (box := joinbox11_rRRLLLLRLL) .s ((11 : ℚ) / 32)
              subsound11_8
              subsound11_9)
            (LRCompactVBoxSound.join (box := joinbox11_rRRLLLLRLR) .s ((11 : ℚ) / 32)
              subsound11_10
              subsound11_11))
          (LRCompactVBoxSound.join (box := joinbox11_rRRLLLLRR) .chi ((299 : ℚ) / 320)
            (LRCompactVBoxSound.join (box := joinbox11_rRRLLLLRRL) .s ((11 : ℚ) / 32)
              subsound11_12
              (LRCompactVBoxSound.join (box := joinbox11_rRRLLLLRRLR) .k ((19 : ℚ) / 48)
                subsound11_13
                subsound11_14))
            (LRCompactVBoxSound.join (box := joinbox11_rRRLLLLRRR) .s ((11 : ℚ) / 32)
              subsound11_15
              (LRCompactVBoxSound.join (box := joinbox11_rRRLLLLRRRR) .k ((19 : ℚ) / 48)
                subsound11_16
                subsound11_17)))))
      (LRCompactVBoxSound.join (box := joinbox11_rRRLLLR) .s ((5 : ℚ) / 16)
        (LRCompactVBoxSound.join (box := joinbox11_rRRLLLRL) .k ((3 : ℚ) / 8)
          (LRCompactVBoxSound.join (box := joinbox11_rRRLLLRLL) .chi ((61 : ℚ) / 64)
            (LRCompactVBoxSound.join (box := joinbox11_rRRLLLRLLL) .s ((9 : ℚ) / 32)
              subsound11_18
              subsound11_19)
            (LRCompactVBoxSound.join (box := joinbox11_rRRLLLRLLR) .s ((9 : ℚ) / 32)
              subsound11_20
              subsound11_21))
          (LRCompactVBoxSound.join (box := joinbox11_rRRLLLRLR) .chi ((61 : ℚ) / 64)
            (LRCompactVBoxSound.join (box := joinbox11_rRRLLLRLRL) .s ((9 : ℚ) / 32)
              subsound11_22
              subsound11_23)
            (LRCompactVBoxSound.join (box := joinbox11_rRRLLLRLRR) .s ((9 : ℚ) / 32)
              subsound11_24
              subsound11_25)))
        (LRCompactVBoxSound.join (box := joinbox11_rRRLLLRR) .k ((3 : ℚ) / 8)
          (LRCompactVBoxSound.join (box := joinbox11_rRRLLLRRL) .chi ((61 : ℚ) / 64)
            (LRCompactVBoxSound.join (box := joinbox11_rRRLLLRRLL) .s ((11 : ℚ) / 32)
              subsound11_26
              subsound11_27)
            (LRCompactVBoxSound.join (box := joinbox11_rRRLLLRRLR) .s ((11 : ℚ) / 32)
              subsound11_28
              subsound11_29))
          (LRCompactVBoxSound.join (box := joinbox11_rRRLLLRRR) .chi ((61 : ℚ) / 64)
            (LRCompactVBoxSound.join (box := joinbox11_rRRLLLRRRL) .s ((11 : ℚ) / 32)
              subsound11_30
              subsound11_31)
            (LRCompactVBoxSound.join (box := joinbox11_rRRLLLRRRR) .s ((11 : ℚ) / 32)
              subsound11_32
              subsound11_33)))))
    (LRCompactVBoxSound.join (box := joinbox11_rRRLLR) .chi ((151 : ℚ) / 160)
      (LRCompactVBoxSound.join (box := joinbox11_rRRLLRL) .s ((5 : ℚ) / 16)
        (LRCompactVBoxSound.join (box := joinbox11_rRRLLRLL) .k ((11 : ℚ) / 24)
          (LRCompactVBoxSound.join (box := joinbox11_rRRLLRLLL) .chi ((299 : ℚ) / 320)
            (LRCompactVBoxSound.join (box := joinbox11_rRRLLRLLLL) .s ((9 : ℚ) / 32)
              subsound11_34
              subsound11_35)
            (LRCompactVBoxSound.join (box := joinbox11_rRRLLRLLLR) .s ((9 : ℚ) / 32)
              subsound11_36
              subsound11_37))
          (LRCompactVBoxSound.join (box := joinbox11_rRRLLRLLR) .chi ((299 : ℚ) / 320)
            (LRCompactVBoxSound.join (box := joinbox11_rRRLLRLLRL) .s ((9 : ℚ) / 32)
              (LRCompactVBoxSound.join (box := joinbox11_rRRLLRLLRLL) .k ((23 : ℚ) / 48)
                subsound11_38
                subsound11_39)
              (LRCompactVBoxSound.join (box := joinbox11_rRRLLRLLRLR) .k ((23 : ℚ) / 48)
                subsound11_40
                subsound11_41))
            (LRCompactVBoxSound.join (box := joinbox11_rRRLLRLLRR) .s ((9 : ℚ) / 32)
              subsound11_42
              (LRCompactVBoxSound.join (box := joinbox11_rRRLLRLLRRR) .k ((23 : ℚ) / 48)
                subsound11_43
                subsound11_44))))
        (LRCompactVBoxSound.join (box := joinbox11_rRRLLRLR) .k ((11 : ℚ) / 24)
          (LRCompactVBoxSound.join (box := joinbox11_rRRLLRLRL) .chi ((299 : ℚ) / 320)
            (LRCompactVBoxSound.join (box := joinbox11_rRRLLRLRLL) .s ((11 : ℚ) / 32)
              (LRCompactVBoxSound.join (box := joinbox11_rRRLLRLRLLL) .k ((7 : ℚ) / 16)
                subsound11_45
                subsound11_46)
              (LRCompactVBoxSound.join (box := joinbox11_rRRLLRLRLLR) .k ((7 : ℚ) / 16)
                subsound11_47
                subsound11_48))
            (LRCompactVBoxSound.join (box := joinbox11_rRRLLRLRLR) .s ((11 : ℚ) / 32)
              (LRCompactVBoxSound.join (box := joinbox11_rRRLLRLRLRL) .k ((7 : ℚ) / 16)
                subsound11_49
                subsound11_50)
              (LRCompactVBoxSound.join (box := joinbox11_rRRLLRLRLRR) .k ((7 : ℚ) / 16)
                subsound11_51
                subsound11_52)))
          (LRCompactVBoxSound.join (box := joinbox11_rRRLLRLRR) .chi ((299 : ℚ) / 320)
            (LRCompactVBoxSound.join (box := joinbox11_rRRLLRLRRL) .s ((11 : ℚ) / 32)
              (LRCompactVBoxSound.join (box := joinbox11_rRRLLRLRRLL) .k ((23 : ℚ) / 48)
                subsound11_53
                subsound11_54)
              (LRCompactVBoxSound.join (box := joinbox11_rRRLLRLRRLR) .k ((23 : ℚ) / 48)
                subsound11_55
                subsound11_56))
            (LRCompactVBoxSound.join (box := joinbox11_rRRLLRLRRR) .s ((11 : ℚ) / 32)
              (LRCompactVBoxSound.join (box := joinbox11_rRRLLRLRRRL) .k ((23 : ℚ) / 48)
                subsound11_57
                subsound11_58)
              (LRCompactVBoxSound.join (box := joinbox11_rRRLLRLRRRR) .k ((23 : ℚ) / 48)
                subsound11_59
                subsound11_60)))))
      (LRCompactVBoxSound.join (box := joinbox11_rRRLLRR) .s ((5 : ℚ) / 16)
        (LRCompactVBoxSound.join (box := joinbox11_rRRLLRRL) .k ((11 : ℚ) / 24)
          (LRCompactVBoxSound.join (box := joinbox11_rRRLLRRLL) .chi ((61 : ℚ) / 64)
            (LRCompactVBoxSound.join (box := joinbox11_rRRLLRRLLL) .s ((9 : ℚ) / 32)
              subsound11_61
              subsound11_62)
            (LRCompactVBoxSound.join (box := joinbox11_rRRLLRRLLR) .s ((9 : ℚ) / 32)
              subsound11_63
              subsound11_64))
          (LRCompactVBoxSound.join (box := joinbox11_rRRLLRRLR) .chi ((61 : ℚ) / 64)
            (LRCompactVBoxSound.join (box := joinbox11_rRRLLRRLRL) .s ((9 : ℚ) / 32)
              subsound11_65
              (LRCompactVBoxSound.join (box := joinbox11_rRRLLRRLRLR) .k ((23 : ℚ) / 48)
                subsound11_66
                subsound11_67))
            (LRCompactVBoxSound.join (box := joinbox11_rRRLLRRLRR) .s ((9 : ℚ) / 32)
              subsound11_68
              subsound11_69)))
        (LRCompactVBoxSound.join (box := joinbox11_rRRLLRRR) .k ((11 : ℚ) / 24)
          (LRCompactVBoxSound.join (box := joinbox11_rRRLLRRRL) .chi ((61 : ℚ) / 64)
            (LRCompactVBoxSound.join (box := joinbox11_rRRLLRRRLL) .s ((11 : ℚ) / 32)
              subsound11_70
              (LRCompactVBoxSound.join (box := joinbox11_rRRLLRRRLLR) .k ((7 : ℚ) / 16)
                subsound11_71
                subsound11_72))
            (LRCompactVBoxSound.join (box := joinbox11_rRRLLRRRLR) .s ((11 : ℚ) / 32)
              subsound11_73
              (LRCompactVBoxSound.join (box := joinbox11_rRRLLRRRLRR) .k ((7 : ℚ) / 16)
                subsound11_74
                subsound11_75)))
          (LRCompactVBoxSound.join (box := joinbox11_rRRLLRRRR) .chi ((61 : ℚ) / 64)
            (LRCompactVBoxSound.join (box := joinbox11_rRRLLRRRRL) .s ((11 : ℚ) / 32)
              (LRCompactVBoxSound.join (box := joinbox11_rRRLLRRRRLL) .k ((23 : ℚ) / 48)
                subsound11_76
                subsound11_77)
              (LRCompactVBoxSound.join (box := joinbox11_rRRLLRRRRLR) .k ((23 : ℚ) / 48)
                subsound11_78
                subsound11_79))
            (LRCompactVBoxSound.join (box := joinbox11_rRRLLRRRRR) .s ((11 : ℚ) / 32)
              (LRCompactVBoxSound.join (box := joinbox11_rRRLLRRRRRL) .k ((23 : ℚ) / 48)
                subsound11_80
                subsound11_81)
              (LRCompactVBoxSound.join (box := joinbox11_rRRLLRRRRRR) .k ((23 : ℚ) / 48)
                subsound11_82
                subsound11_83)))))))

end CourtadeKumar.GeneratedLRCompactVLowR
