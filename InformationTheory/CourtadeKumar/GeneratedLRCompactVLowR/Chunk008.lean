import InformationTheory.CourtadeKumar.LRCompactVBasicReplay

/-! Frozen basic compact-V replay.
Plan SHA-256: ce3f7a498b2b9caf346dcf88ce7861f8cc091af8cd93f5624d7684e21322ecd5
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CourtadeKumar.GeneratedLRCompactVLowR

-- 72 accepted leaves below path rLRRRR.
def box8 : CertificateBox where
  sLo := ((3 : ℚ) / 8)
  sHi := ((1 : ℚ) / 2)
  kLo := ((5 : ℚ) / 12)
  kHi := ((1 : ℚ) / 2)
  chiLo := ((71 : ℚ) / 80)
  chiHi := ((37 : ℚ) / 40)


def subbox8_0 : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((5 : ℚ) / 12), ((7 : ℚ) / 16), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩

theorem checked8_0 :
    LRCompactVLeafParameters.check subbox8_0 .short = true := by decide +kernel

theorem subsound8_0 : LRCompactVBoxSound subbox8_0 :=
  LRCompactVLeafParameters.sound checked8_0


def subbox8_1 : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩

theorem checked8_1 :
    LRCompactVLeafParameters.check subbox8_1 .short = true := by decide +kernel

theorem subsound8_1 : LRCompactVBoxSound subbox8_1 :=
  LRCompactVLeafParameters.sound checked8_1


def subbox8_2 : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((5 : ℚ) / 12), ((7 : ℚ) / 16), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩

theorem checked8_2 :
    LRCompactVLeafParameters.check subbox8_2 .short = true := by decide +kernel

theorem subsound8_2 : LRCompactVBoxSound subbox8_2 :=
  LRCompactVLeafParameters.sound checked8_2


def subbox8_3 : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩

theorem checked8_3 :
    LRCompactVLeafParameters.check subbox8_3 .short = true := by decide +kernel

theorem subsound8_3 : LRCompactVBoxSound subbox8_3 :=
  LRCompactVLeafParameters.sound checked8_3


def subbox8_4 : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((5 : ℚ) / 12), ((7 : ℚ) / 16), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩

theorem checked8_4 :
    LRCompactVLeafParameters.check subbox8_4 .short = true := by decide +kernel

theorem subsound8_4 : LRCompactVBoxSound subbox8_4 :=
  LRCompactVLeafParameters.sound checked8_4


def subbox8_5 : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩

theorem checked8_5 :
    LRCompactVLeafParameters.check subbox8_5 .short = true := by decide +kernel

theorem subsound8_5 : LRCompactVBoxSound subbox8_5 :=
  LRCompactVLeafParameters.sound checked8_5


def subbox8_6 : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((5 : ℚ) / 12), ((7 : ℚ) / 16), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩

theorem checked8_6 :
    LRCompactVLeafParameters.check subbox8_6 .short = true := by decide +kernel

theorem subsound8_6 : LRCompactVBoxSound subbox8_6 :=
  LRCompactVLeafParameters.sound checked8_6


def subbox8_7 : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩

theorem checked8_7 :
    LRCompactVLeafParameters.check subbox8_7 .short = true := by decide +kernel

theorem subsound8_7 : LRCompactVBoxSound subbox8_7 :=
  LRCompactVLeafParameters.sound checked8_7


def subbox8_8 : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩

theorem checked8_8 :
    LRCompactVLeafParameters.check subbox8_8 .short = true := by decide +kernel

theorem subsound8_8 : LRCompactVBoxSound subbox8_8 :=
  LRCompactVLeafParameters.sound checked8_8


def subbox8_9 : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩

theorem checked8_9 :
    LRCompactVLeafParameters.check subbox8_9 .short = true := by decide +kernel

theorem subsound8_9 : LRCompactVBoxSound subbox8_9 :=
  LRCompactVLeafParameters.sound checked8_9


def subbox8_10 : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩

theorem checked8_10 :
    LRCompactVLeafParameters.check subbox8_10 .long = true := by decide +kernel

theorem subsound8_10 : LRCompactVBoxSound subbox8_10 :=
  LRCompactVLeafParameters.sound checked8_10


def subbox8_11 : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩

theorem checked8_11 :
    LRCompactVLeafParameters.check subbox8_11 .long = true := by decide +kernel

theorem subsound8_11 : LRCompactVBoxSound subbox8_11 :=
  LRCompactVLeafParameters.sound checked8_11


def subbox8_12 : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩

theorem checked8_12 :
    LRCompactVLeafParameters.check subbox8_12 .short = true := by decide +kernel

theorem subsound8_12 : LRCompactVBoxSound subbox8_12 :=
  LRCompactVLeafParameters.sound checked8_12


def subbox8_13 : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩

theorem checked8_13 :
    LRCompactVLeafParameters.check subbox8_13 .short = true := by decide +kernel

theorem subsound8_13 : LRCompactVBoxSound subbox8_13 :=
  LRCompactVLeafParameters.sound checked8_13


def subbox8_14 : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩

theorem checked8_14 :
    LRCompactVLeafParameters.check subbox8_14 .short = true := by decide +kernel

theorem subsound8_14 : LRCompactVBoxSound subbox8_14 :=
  LRCompactVLeafParameters.sound checked8_14


def subbox8_15 : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩

theorem checked8_15 :
    LRCompactVLeafParameters.check subbox8_15 .long = true := by decide +kernel

theorem subsound8_15 : LRCompactVBoxSound subbox8_15 :=
  LRCompactVLeafParameters.sound checked8_15


def subbox8_16 : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((5 : ℚ) / 12), ((7 : ℚ) / 16), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩

theorem checked8_16 :
    LRCompactVLeafParameters.check subbox8_16 .long = true := by decide +kernel

theorem subsound8_16 : LRCompactVBoxSound subbox8_16 :=
  LRCompactVLeafParameters.sound checked8_16


def subbox8_17 : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩

theorem checked8_17 :
    LRCompactVLeafParameters.check subbox8_17 .long = true := by decide +kernel

theorem subsound8_17 : LRCompactVBoxSound subbox8_17 :=
  LRCompactVLeafParameters.sound checked8_17


def subbox8_18 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((5 : ℚ) / 12), ((7 : ℚ) / 16), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩

theorem checked8_18 :
    LRCompactVLeafParameters.check subbox8_18 .long = true := by decide +kernel

theorem subsound8_18 : LRCompactVBoxSound subbox8_18 :=
  LRCompactVLeafParameters.sound checked8_18


def subbox8_19 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((71 : ℚ) / 80), ((571 : ℚ) / 640)⟩

theorem checked8_19 :
    LRCompactVLeafParameters.check subbox8_19 .long = true := by decide +kernel

theorem subsound8_19 : LRCompactVBoxSound subbox8_19 :=
  LRCompactVLeafParameters.sound checked8_19


def subbox8_20 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((571 : ℚ) / 640), ((287 : ℚ) / 320)⟩

theorem checked8_20 :
    LRCompactVLeafParameters.check subbox8_20 .long = true := by decide +kernel

theorem subsound8_20 : LRCompactVBoxSound subbox8_20 :=
  LRCompactVLeafParameters.sound checked8_20


def subbox8_21 : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((5 : ℚ) / 12), ((7 : ℚ) / 16), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩

theorem checked8_21 :
    LRCompactVLeafParameters.check subbox8_21 .long = true := by decide +kernel

theorem subsound8_21 : LRCompactVBoxSound subbox8_21 :=
  LRCompactVLeafParameters.sound checked8_21


def subbox8_22 : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩

theorem checked8_22 :
    LRCompactVLeafParameters.check subbox8_22 .long = true := by decide +kernel

theorem subsound8_22 : LRCompactVBoxSound subbox8_22 :=
  LRCompactVLeafParameters.sound checked8_22


def subbox8_23 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((5 : ℚ) / 12), ((7 : ℚ) / 16), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩

theorem checked8_23 :
    LRCompactVLeafParameters.check subbox8_23 .long = true := by decide +kernel

theorem subsound8_23 : LRCompactVBoxSound subbox8_23 :=
  LRCompactVLeafParameters.sound checked8_23


def subbox8_24 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩

theorem checked8_24 :
    LRCompactVLeafParameters.check subbox8_24 .long = true := by decide +kernel

theorem subsound8_24 : LRCompactVBoxSound subbox8_24 :=
  LRCompactVLeafParameters.sound checked8_24


def subbox8_25 : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩

theorem checked8_25 :
    LRCompactVLeafParameters.check subbox8_25 .long = true := by decide +kernel

theorem subsound8_25 : LRCompactVBoxSound subbox8_25 :=
  LRCompactVLeafParameters.sound checked8_25


def subbox8_26 : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩

theorem checked8_26 :
    LRCompactVLeafParameters.check subbox8_26 .long = true := by decide +kernel

theorem subsound8_26 : LRCompactVBoxSound subbox8_26 :=
  LRCompactVLeafParameters.sound checked8_26


def subbox8_27 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((71 : ℚ) / 80), ((571 : ℚ) / 640)⟩

theorem checked8_27 :
    LRCompactVLeafParameters.check subbox8_27 .long = true := by decide +kernel

theorem subsound8_27 : LRCompactVBoxSound subbox8_27 :=
  LRCompactVLeafParameters.sound checked8_27


def subbox8_28 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((571 : ℚ) / 640), ((287 : ℚ) / 320)⟩

theorem checked8_28 :
    LRCompactVLeafParameters.check subbox8_28 .long = true := by decide +kernel

theorem subsound8_28 : LRCompactVBoxSound subbox8_28 :=
  LRCompactVLeafParameters.sound checked8_28


def subbox8_29 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((71 : ℚ) / 80), ((571 : ℚ) / 640)⟩

theorem checked8_29 :
    LRCompactVLeafParameters.check subbox8_29 .long = true := by decide +kernel

theorem subsound8_29 : LRCompactVBoxSound subbox8_29 :=
  LRCompactVLeafParameters.sound checked8_29


def subbox8_30 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((571 : ℚ) / 640), ((287 : ℚ) / 320)⟩

theorem checked8_30 :
    LRCompactVLeafParameters.check subbox8_30 .long = true := by decide +kernel

theorem subsound8_30 : LRCompactVBoxSound subbox8_30 :=
  LRCompactVLeafParameters.sound checked8_30


def subbox8_31 : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩

theorem checked8_31 :
    LRCompactVLeafParameters.check subbox8_31 .long = true := by decide +kernel

theorem subsound8_31 : LRCompactVBoxSound subbox8_31 :=
  LRCompactVLeafParameters.sound checked8_31


def subbox8_32 : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩

theorem checked8_32 :
    LRCompactVLeafParameters.check subbox8_32 .long = true := by decide +kernel

theorem subsound8_32 : LRCompactVBoxSound subbox8_32 :=
  LRCompactVLeafParameters.sound checked8_32


def subbox8_33 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((287 : ℚ) / 320), ((577 : ℚ) / 640)⟩

theorem checked8_33 :
    LRCompactVLeafParameters.check subbox8_33 .long = true := by decide +kernel

theorem subsound8_33 : LRCompactVBoxSound subbox8_33 :=
  LRCompactVLeafParameters.sound checked8_33


def subbox8_34 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((577 : ℚ) / 640), ((29 : ℚ) / 32)⟩

theorem checked8_34 :
    LRCompactVLeafParameters.check subbox8_34 .long = true := by decide +kernel

theorem subsound8_34 : LRCompactVBoxSound subbox8_34 :=
  LRCompactVLeafParameters.sound checked8_34


def subbox8_35 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((287 : ℚ) / 320), ((577 : ℚ) / 640)⟩

theorem checked8_35 :
    LRCompactVLeafParameters.check subbox8_35 .long = true := by decide +kernel

theorem subsound8_35 : LRCompactVBoxSound subbox8_35 :=
  LRCompactVLeafParameters.sound checked8_35


def subbox8_36 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((577 : ℚ) / 640), ((29 : ℚ) / 32)⟩

theorem checked8_36 :
    LRCompactVLeafParameters.check subbox8_36 .long = true := by decide +kernel

theorem subsound8_36 : LRCompactVBoxSound subbox8_36 :=
  LRCompactVLeafParameters.sound checked8_36


def subbox8_37 : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((5 : ℚ) / 12), ((7 : ℚ) / 16), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩

theorem checked8_37 :
    LRCompactVLeafParameters.check subbox8_37 .short = true := by decide +kernel

theorem subsound8_37 : LRCompactVBoxSound subbox8_37 :=
  LRCompactVLeafParameters.sound checked8_37


def subbox8_38 : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩

theorem checked8_38 :
    LRCompactVLeafParameters.check subbox8_38 .short = true := by decide +kernel

theorem subsound8_38 : LRCompactVBoxSound subbox8_38 :=
  LRCompactVLeafParameters.sound checked8_38


def subbox8_39 : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((5 : ℚ) / 12), ((7 : ℚ) / 16), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩

theorem checked8_39 :
    LRCompactVLeafParameters.check subbox8_39 .short = true := by decide +kernel

theorem subsound8_39 : LRCompactVBoxSound subbox8_39 :=
  LRCompactVLeafParameters.sound checked8_39


def subbox8_40 : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩

theorem checked8_40 :
    LRCompactVLeafParameters.check subbox8_40 .short = true := by decide +kernel

theorem subsound8_40 : LRCompactVBoxSound subbox8_40 :=
  LRCompactVLeafParameters.sound checked8_40


def subbox8_41 : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((5 : ℚ) / 12), ((7 : ℚ) / 16), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩

theorem checked8_41 :
    LRCompactVLeafParameters.check subbox8_41 .short = true := by decide +kernel

theorem subsound8_41 : LRCompactVBoxSound subbox8_41 :=
  LRCompactVLeafParameters.sound checked8_41


def subbox8_42 : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩

theorem checked8_42 :
    LRCompactVLeafParameters.check subbox8_42 .short = true := by decide +kernel

theorem subsound8_42 : LRCompactVBoxSound subbox8_42 :=
  LRCompactVLeafParameters.sound checked8_42


def subbox8_43 : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((5 : ℚ) / 12), ((7 : ℚ) / 16), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩

theorem checked8_43 :
    LRCompactVLeafParameters.check subbox8_43 .short = true := by decide +kernel

theorem subsound8_43 : LRCompactVBoxSound subbox8_43 :=
  LRCompactVLeafParameters.sound checked8_43


def subbox8_44 : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩

theorem checked8_44 :
    LRCompactVLeafParameters.check subbox8_44 .short = true := by decide +kernel

theorem subsound8_44 : LRCompactVBoxSound subbox8_44 :=
  LRCompactVLeafParameters.sound checked8_44


def subbox8_45 : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩

theorem checked8_45 :
    LRCompactVLeafParameters.check subbox8_45 .short = true := by decide +kernel

theorem subsound8_45 : LRCompactVBoxSound subbox8_45 :=
  LRCompactVLeafParameters.sound checked8_45


def subbox8_46 : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩

theorem checked8_46 :
    LRCompactVLeafParameters.check subbox8_46 .short = true := by decide +kernel

theorem subsound8_46 : LRCompactVBoxSound subbox8_46 :=
  LRCompactVLeafParameters.sound checked8_46


def subbox8_47 : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩

theorem checked8_47 :
    LRCompactVLeafParameters.check subbox8_47 .short = true := by decide +kernel

theorem subsound8_47 : LRCompactVBoxSound subbox8_47 :=
  LRCompactVLeafParameters.sound checked8_47


def subbox8_48 : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩

theorem checked8_48 :
    LRCompactVLeafParameters.check subbox8_48 .long = true := by decide +kernel

theorem subsound8_48 : LRCompactVBoxSound subbox8_48 :=
  LRCompactVLeafParameters.sound checked8_48


def subbox8_49 : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩

theorem checked8_49 :
    LRCompactVLeafParameters.check subbox8_49 .short = true := by decide +kernel

theorem subsound8_49 : LRCompactVBoxSound subbox8_49 :=
  LRCompactVLeafParameters.sound checked8_49


def subbox8_50 : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩

theorem checked8_50 :
    LRCompactVLeafParameters.check subbox8_50 .short = true := by decide +kernel

theorem subsound8_50 : LRCompactVBoxSound subbox8_50 :=
  LRCompactVLeafParameters.sound checked8_50


def subbox8_51 : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩

theorem checked8_51 :
    LRCompactVLeafParameters.check subbox8_51 .short = true := by decide +kernel

theorem subsound8_51 : LRCompactVBoxSound subbox8_51 :=
  LRCompactVLeafParameters.sound checked8_51


def subbox8_52 : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩

theorem checked8_52 :
    LRCompactVLeafParameters.check subbox8_52 .long = true := by decide +kernel

theorem subsound8_52 : LRCompactVBoxSound subbox8_52 :=
  LRCompactVLeafParameters.sound checked8_52


def subbox8_53 : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((5 : ℚ) / 12), ((7 : ℚ) / 16), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩

theorem checked8_53 :
    LRCompactVLeafParameters.check subbox8_53 .long = true := by decide +kernel

theorem subsound8_53 : LRCompactVBoxSound subbox8_53 :=
  LRCompactVLeafParameters.sound checked8_53


def subbox8_54 : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩

theorem checked8_54 :
    LRCompactVLeafParameters.check subbox8_54 .long = true := by decide +kernel

theorem subsound8_54 : LRCompactVBoxSound subbox8_54 :=
  LRCompactVLeafParameters.sound checked8_54


def subbox8_55 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((5 : ℚ) / 12), ((7 : ℚ) / 16), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩

theorem checked8_55 :
    LRCompactVLeafParameters.check subbox8_55 .long = true := by decide +kernel

theorem subsound8_55 : LRCompactVBoxSound subbox8_55 :=
  LRCompactVLeafParameters.sound checked8_55


def subbox8_56 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩

theorem checked8_56 :
    LRCompactVLeafParameters.check subbox8_56 .long = true := by decide +kernel

theorem subsound8_56 : LRCompactVBoxSound subbox8_56 :=
  LRCompactVLeafParameters.sound checked8_56


def subbox8_57 : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((5 : ℚ) / 12), ((7 : ℚ) / 16), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩

theorem checked8_57 :
    LRCompactVLeafParameters.check subbox8_57 .accurateLog = true := by decide +kernel

theorem subsound8_57 : LRCompactVBoxSound subbox8_57 :=
  LRCompactVLeafParameters.sound checked8_57


def subbox8_58 : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩

theorem checked8_58 :
    LRCompactVLeafParameters.check subbox8_58 .long = true := by decide +kernel

theorem subsound8_58 : LRCompactVBoxSound subbox8_58 :=
  LRCompactVLeafParameters.sound checked8_58


def subbox8_59 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((5 : ℚ) / 12), ((7 : ℚ) / 16), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩

theorem checked8_59 :
    LRCompactVLeafParameters.check subbox8_59 .long = true := by decide +kernel

theorem subsound8_59 : LRCompactVBoxSound subbox8_59 :=
  LRCompactVLeafParameters.sound checked8_59


def subbox8_60 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩

theorem checked8_60 :
    LRCompactVLeafParameters.check subbox8_60 .long = true := by decide +kernel

theorem subsound8_60 : LRCompactVBoxSound subbox8_60 :=
  LRCompactVLeafParameters.sound checked8_60


def subbox8_61 : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩

theorem checked8_61 :
    LRCompactVLeafParameters.check subbox8_61 .long = true := by decide +kernel

theorem subsound8_61 : LRCompactVBoxSound subbox8_61 :=
  LRCompactVLeafParameters.sound checked8_61


def subbox8_62 : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩

theorem checked8_62 :
    LRCompactVLeafParameters.check subbox8_62 .long = true := by decide +kernel

theorem subsound8_62 : LRCompactVBoxSound subbox8_62 :=
  LRCompactVLeafParameters.sound checked8_62


def subbox8_63 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((29 : ℚ) / 32), ((583 : ℚ) / 640)⟩

theorem checked8_63 :
    LRCompactVLeafParameters.check subbox8_63 .long = true := by decide +kernel

theorem subsound8_63 : LRCompactVBoxSound subbox8_63 :=
  LRCompactVLeafParameters.sound checked8_63


def subbox8_64 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((583 : ℚ) / 640), ((293 : ℚ) / 320)⟩

theorem checked8_64 :
    LRCompactVLeafParameters.check subbox8_64 .long = true := by decide +kernel

theorem subsound8_64 : LRCompactVBoxSound subbox8_64 :=
  LRCompactVLeafParameters.sound checked8_64


def subbox8_65 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((29 : ℚ) / 32), ((583 : ℚ) / 640)⟩

theorem checked8_65 :
    LRCompactVLeafParameters.check subbox8_65 .long = true := by decide +kernel

theorem subsound8_65 : LRCompactVBoxSound subbox8_65 :=
  LRCompactVLeafParameters.sound checked8_65


def subbox8_66 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((583 : ℚ) / 640), ((293 : ℚ) / 320)⟩

theorem checked8_66 :
    LRCompactVLeafParameters.check subbox8_66 .long = true := by decide +kernel

theorem subsound8_66 : LRCompactVBoxSound subbox8_66 :=
  LRCompactVLeafParameters.sound checked8_66


def subbox8_67 : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩

theorem checked8_67 :
    LRCompactVLeafParameters.check subbox8_67 .long = true := by decide +kernel

theorem subsound8_67 : LRCompactVBoxSound subbox8_67 :=
  LRCompactVLeafParameters.sound checked8_67


def subbox8_68 : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩

theorem checked8_68 :
    LRCompactVLeafParameters.check subbox8_68 .long = true := by decide +kernel

theorem subsound8_68 : LRCompactVBoxSound subbox8_68 :=
  LRCompactVLeafParameters.sound checked8_68


def subbox8_69 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩

theorem checked8_69 :
    LRCompactVLeafParameters.check subbox8_69 .long = true := by decide +kernel

theorem subsound8_69 : LRCompactVBoxSound subbox8_69 :=
  LRCompactVLeafParameters.sound checked8_69


def subbox8_70 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((293 : ℚ) / 320), ((589 : ℚ) / 640)⟩

theorem checked8_70 :
    LRCompactVLeafParameters.check subbox8_70 .long = true := by decide +kernel

theorem subsound8_70 : LRCompactVBoxSound subbox8_70 :=
  LRCompactVLeafParameters.sound checked8_70


def subbox8_71 : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((589 : ℚ) / 640), ((37 : ℚ) / 40)⟩

theorem checked8_71 :
    LRCompactVLeafParameters.check subbox8_71 .long = true := by decide +kernel

theorem subsound8_71 : LRCompactVBoxSound subbox8_71 :=
  LRCompactVLeafParameters.sound checked8_71


def joinbox8_rLRRRRL : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((1 : ℚ) / 2), ((5 : ℚ) / 12), ((1 : ℚ) / 2), ((71 : ℚ) / 80), ((29 : ℚ) / 32)⟩


def joinbox8_rLRRRRLL : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((7 : ℚ) / 16), ((5 : ℚ) / 12), ((1 : ℚ) / 2), ((71 : ℚ) / 80), ((29 : ℚ) / 32)⟩


def joinbox8_rLRRRRLLL : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((7 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((71 : ℚ) / 80), ((29 : ℚ) / 32)⟩


def joinbox8_rLRRRRLLLL : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((7 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩


def joinbox8_rLRRRRLLLLL : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩


def joinbox8_rLRRRRLLLLR : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩


def joinbox8_rLRRRRLLLR : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((7 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩


def joinbox8_rLRRRRLLLRL : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩


def joinbox8_rLRRRRLLLRR : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩


def joinbox8_rLRRRRLLR : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((71 : ℚ) / 80), ((29 : ℚ) / 32)⟩


def joinbox8_rLRRRRLLRL : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩


def joinbox8_rLRRRRLLRLL : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩


def joinbox8_rLRRRRLLRLR : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩


def joinbox8_rLRRRRLLRR : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩


def joinbox8_rLRRRRLLRRL : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩


def joinbox8_rLRRRRLLRRR : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩


def joinbox8_rLRRRRLR : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((1 : ℚ) / 2), ((5 : ℚ) / 12), ((1 : ℚ) / 2), ((71 : ℚ) / 80), ((29 : ℚ) / 32)⟩


def joinbox8_rLRRRRLRL : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((1 : ℚ) / 2), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((71 : ℚ) / 80), ((29 : ℚ) / 32)⟩


def joinbox8_rLRRRRLRLL : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((1 : ℚ) / 2), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩


def joinbox8_rLRRRRLRLLL : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩


def joinbox8_rLRRRRLRLLR : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩


def joinbox8_rLRRRRLRLLRR : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩


def joinbox8_rLRRRRLRLR : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((1 : ℚ) / 2), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩


def joinbox8_rLRRRRLRLRL : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩


def joinbox8_rLRRRRLRLRR : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩


def joinbox8_rLRRRRLRR : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((1 : ℚ) / 2), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((71 : ℚ) / 80), ((29 : ℚ) / 32)⟩


def joinbox8_rLRRRRLRRL : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((1 : ℚ) / 2), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩


def joinbox8_rLRRRRLRRLL : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩


def joinbox8_rLRRRRLRRLR : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩


def joinbox8_rLRRRRLRRLRL : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩


def joinbox8_rLRRRRLRRLRR : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((71 : ℚ) / 80), ((287 : ℚ) / 320)⟩


def joinbox8_rLRRRRLRRR : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((1 : ℚ) / 2), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩


def joinbox8_rLRRRRLRRRL : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩


def joinbox8_rLRRRRLRRRR : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩


def joinbox8_rLRRRRLRRRRL : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩


def joinbox8_rLRRRRLRRRRR : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((287 : ℚ) / 320), ((29 : ℚ) / 32)⟩


def joinbox8_rLRRRRR : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((1 : ℚ) / 2), ((5 : ℚ) / 12), ((1 : ℚ) / 2), ((29 : ℚ) / 32), ((37 : ℚ) / 40)⟩


def joinbox8_rLRRRRRL : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((7 : ℚ) / 16), ((5 : ℚ) / 12), ((1 : ℚ) / 2), ((29 : ℚ) / 32), ((37 : ℚ) / 40)⟩


def joinbox8_rLRRRRRLL : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((7 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((29 : ℚ) / 32), ((37 : ℚ) / 40)⟩


def joinbox8_rLRRRRRLLL : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((7 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩


def joinbox8_rLRRRRRLLLL : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩


def joinbox8_rLRRRRRLLLR : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩


def joinbox8_rLRRRRRLLR : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((7 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩


def joinbox8_rLRRRRRLLRL : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩


def joinbox8_rLRRRRRLLRR : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩


def joinbox8_rLRRRRRLR : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((29 : ℚ) / 32), ((37 : ℚ) / 40)⟩


def joinbox8_rLRRRRRLRL : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩


def joinbox8_rLRRRRRLRLL : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩


def joinbox8_rLRRRRRLRLR : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩


def joinbox8_rLRRRRRLRR : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩


def joinbox8_rLRRRRRLRRL : CertificateBox :=
  ⟨((3 : ℚ) / 8), ((13 : ℚ) / 32), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩


def joinbox8_rLRRRRRLRRR : CertificateBox :=
  ⟨((13 : ℚ) / 32), ((7 : ℚ) / 16), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩


def joinbox8_rLRRRRRR : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((1 : ℚ) / 2), ((5 : ℚ) / 12), ((1 : ℚ) / 2), ((29 : ℚ) / 32), ((37 : ℚ) / 40)⟩


def joinbox8_rLRRRRRRL : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((1 : ℚ) / 2), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((29 : ℚ) / 32), ((37 : ℚ) / 40)⟩


def joinbox8_rLRRRRRRLL : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((1 : ℚ) / 2), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩


def joinbox8_rLRRRRRRLLL : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩


def joinbox8_rLRRRRRRLLR : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩


def joinbox8_rLRRRRRRLR : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((1 : ℚ) / 2), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩


def joinbox8_rLRRRRRRLRL : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩


def joinbox8_rLRRRRRRLRR : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((5 : ℚ) / 12), ((11 : ℚ) / 24), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩


def joinbox8_rLRRRRRRR : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((1 : ℚ) / 2), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((29 : ℚ) / 32), ((37 : ℚ) / 40)⟩


def joinbox8_rLRRRRRRRL : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((1 : ℚ) / 2), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩


def joinbox8_rLRRRRRRRLL : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩


def joinbox8_rLRRRRRRRLR : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩


def joinbox8_rLRRRRRRRLRL : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((11 : ℚ) / 24), ((23 : ℚ) / 48), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩


def joinbox8_rLRRRRRRRLRR : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((29 : ℚ) / 32), ((293 : ℚ) / 320)⟩


def joinbox8_rLRRRRRRRR : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((1 : ℚ) / 2), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩


def joinbox8_rLRRRRRRRRL : CertificateBox :=
  ⟨((7 : ℚ) / 16), ((15 : ℚ) / 32), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩


def joinbox8_rLRRRRRRRRR : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((11 : ℚ) / 24), ((1 : ℚ) / 2), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩


def joinbox8_rLRRRRRRRRRR : CertificateBox :=
  ⟨((15 : ℚ) / 32), ((1 : ℚ) / 2), ((23 : ℚ) / 48), ((1 : ℚ) / 2), ((293 : ℚ) / 320), ((37 : ℚ) / 40)⟩


theorem sound8 : LRCompactVBoxSound box8 :=
  (LRCompactVBoxSound.join (box := box8) .chi ((29 : ℚ) / 32)
    (LRCompactVBoxSound.join (box := joinbox8_rLRRRRL) .s ((7 : ℚ) / 16)
      (LRCompactVBoxSound.join (box := joinbox8_rLRRRRLL) .k ((11 : ℚ) / 24)
        (LRCompactVBoxSound.join (box := joinbox8_rLRRRRLLL) .chi ((287 : ℚ) / 320)
          (LRCompactVBoxSound.join (box := joinbox8_rLRRRRLLLL) .s ((13 : ℚ) / 32)
            (LRCompactVBoxSound.join (box := joinbox8_rLRRRRLLLLL) .k ((7 : ℚ) / 16)
              subsound8_0
              subsound8_1)
            (LRCompactVBoxSound.join (box := joinbox8_rLRRRRLLLLR) .k ((7 : ℚ) / 16)
              subsound8_2
              subsound8_3))
          (LRCompactVBoxSound.join (box := joinbox8_rLRRRRLLLR) .s ((13 : ℚ) / 32)
            (LRCompactVBoxSound.join (box := joinbox8_rLRRRRLLLRL) .k ((7 : ℚ) / 16)
              subsound8_4
              subsound8_5)
            (LRCompactVBoxSound.join (box := joinbox8_rLRRRRLLLRR) .k ((7 : ℚ) / 16)
              subsound8_6
              subsound8_7)))
        (LRCompactVBoxSound.join (box := joinbox8_rLRRRRLLR) .chi ((287 : ℚ) / 320)
          (LRCompactVBoxSound.join (box := joinbox8_rLRRRRLLRL) .s ((13 : ℚ) / 32)
            (LRCompactVBoxSound.join (box := joinbox8_rLRRRRLLRLL) .k ((23 : ℚ) / 48)
              subsound8_8
              subsound8_9)
            (LRCompactVBoxSound.join (box := joinbox8_rLRRRRLLRLR) .k ((23 : ℚ) / 48)
              subsound8_10
              subsound8_11))
          (LRCompactVBoxSound.join (box := joinbox8_rLRRRRLLRR) .s ((13 : ℚ) / 32)
            (LRCompactVBoxSound.join (box := joinbox8_rLRRRRLLRRL) .k ((23 : ℚ) / 48)
              subsound8_12
              subsound8_13)
            (LRCompactVBoxSound.join (box := joinbox8_rLRRRRLLRRR) .k ((23 : ℚ) / 48)
              subsound8_14
              subsound8_15))))
      (LRCompactVBoxSound.join (box := joinbox8_rLRRRRLR) .k ((11 : ℚ) / 24)
        (LRCompactVBoxSound.join (box := joinbox8_rLRRRRLRL) .chi ((287 : ℚ) / 320)
          (LRCompactVBoxSound.join (box := joinbox8_rLRRRRLRLL) .s ((15 : ℚ) / 32)
            (LRCompactVBoxSound.join (box := joinbox8_rLRRRRLRLLL) .k ((7 : ℚ) / 16)
              subsound8_16
              subsound8_17)
            (LRCompactVBoxSound.join (box := joinbox8_rLRRRRLRLLR) .k ((7 : ℚ) / 16)
              subsound8_18
              (LRCompactVBoxSound.join (box := joinbox8_rLRRRRLRLLRR) .chi ((571 : ℚ) / 640)
                subsound8_19
                subsound8_20)))
          (LRCompactVBoxSound.join (box := joinbox8_rLRRRRLRLR) .s ((15 : ℚ) / 32)
            (LRCompactVBoxSound.join (box := joinbox8_rLRRRRLRLRL) .k ((7 : ℚ) / 16)
              subsound8_21
              subsound8_22)
            (LRCompactVBoxSound.join (box := joinbox8_rLRRRRLRLRR) .k ((7 : ℚ) / 16)
              subsound8_23
              subsound8_24)))
        (LRCompactVBoxSound.join (box := joinbox8_rLRRRRLRR) .chi ((287 : ℚ) / 320)
          (LRCompactVBoxSound.join (box := joinbox8_rLRRRRLRRL) .s ((15 : ℚ) / 32)
            (LRCompactVBoxSound.join (box := joinbox8_rLRRRRLRRLL) .k ((23 : ℚ) / 48)
              subsound8_25
              subsound8_26)
            (LRCompactVBoxSound.join (box := joinbox8_rLRRRRLRRLR) .k ((23 : ℚ) / 48)
              (LRCompactVBoxSound.join (box := joinbox8_rLRRRRLRRLRL) .chi ((571 : ℚ) / 640)
                subsound8_27
                subsound8_28)
              (LRCompactVBoxSound.join (box := joinbox8_rLRRRRLRRLRR) .chi ((571 : ℚ) / 640)
                subsound8_29
                subsound8_30)))
          (LRCompactVBoxSound.join (box := joinbox8_rLRRRRLRRR) .s ((15 : ℚ) / 32)
            (LRCompactVBoxSound.join (box := joinbox8_rLRRRRLRRRL) .k ((23 : ℚ) / 48)
              subsound8_31
              subsound8_32)
            (LRCompactVBoxSound.join (box := joinbox8_rLRRRRLRRRR) .k ((23 : ℚ) / 48)
              (LRCompactVBoxSound.join (box := joinbox8_rLRRRRLRRRRL) .chi ((577 : ℚ) / 640)
                subsound8_33
                subsound8_34)
              (LRCompactVBoxSound.join (box := joinbox8_rLRRRRLRRRRR) .chi ((577 : ℚ) / 640)
                subsound8_35
                subsound8_36))))))
    (LRCompactVBoxSound.join (box := joinbox8_rLRRRRR) .s ((7 : ℚ) / 16)
      (LRCompactVBoxSound.join (box := joinbox8_rLRRRRRL) .k ((11 : ℚ) / 24)
        (LRCompactVBoxSound.join (box := joinbox8_rLRRRRRLL) .chi ((293 : ℚ) / 320)
          (LRCompactVBoxSound.join (box := joinbox8_rLRRRRRLLL) .s ((13 : ℚ) / 32)
            (LRCompactVBoxSound.join (box := joinbox8_rLRRRRRLLLL) .k ((7 : ℚ) / 16)
              subsound8_37
              subsound8_38)
            (LRCompactVBoxSound.join (box := joinbox8_rLRRRRRLLLR) .k ((7 : ℚ) / 16)
              subsound8_39
              subsound8_40))
          (LRCompactVBoxSound.join (box := joinbox8_rLRRRRRLLR) .s ((13 : ℚ) / 32)
            (LRCompactVBoxSound.join (box := joinbox8_rLRRRRRLLRL) .k ((7 : ℚ) / 16)
              subsound8_41
              subsound8_42)
            (LRCompactVBoxSound.join (box := joinbox8_rLRRRRRLLRR) .k ((7 : ℚ) / 16)
              subsound8_43
              subsound8_44)))
        (LRCompactVBoxSound.join (box := joinbox8_rLRRRRRLR) .chi ((293 : ℚ) / 320)
          (LRCompactVBoxSound.join (box := joinbox8_rLRRRRRLRL) .s ((13 : ℚ) / 32)
            (LRCompactVBoxSound.join (box := joinbox8_rLRRRRRLRLL) .k ((23 : ℚ) / 48)
              subsound8_45
              subsound8_46)
            (LRCompactVBoxSound.join (box := joinbox8_rLRRRRRLRLR) .k ((23 : ℚ) / 48)
              subsound8_47
              subsound8_48))
          (LRCompactVBoxSound.join (box := joinbox8_rLRRRRRLRR) .s ((13 : ℚ) / 32)
            (LRCompactVBoxSound.join (box := joinbox8_rLRRRRRLRRL) .k ((23 : ℚ) / 48)
              subsound8_49
              subsound8_50)
            (LRCompactVBoxSound.join (box := joinbox8_rLRRRRRLRRR) .k ((23 : ℚ) / 48)
              subsound8_51
              subsound8_52))))
      (LRCompactVBoxSound.join (box := joinbox8_rLRRRRRR) .k ((11 : ℚ) / 24)
        (LRCompactVBoxSound.join (box := joinbox8_rLRRRRRRL) .chi ((293 : ℚ) / 320)
          (LRCompactVBoxSound.join (box := joinbox8_rLRRRRRRLL) .s ((15 : ℚ) / 32)
            (LRCompactVBoxSound.join (box := joinbox8_rLRRRRRRLLL) .k ((7 : ℚ) / 16)
              subsound8_53
              subsound8_54)
            (LRCompactVBoxSound.join (box := joinbox8_rLRRRRRRLLR) .k ((7 : ℚ) / 16)
              subsound8_55
              subsound8_56))
          (LRCompactVBoxSound.join (box := joinbox8_rLRRRRRRLR) .s ((15 : ℚ) / 32)
            (LRCompactVBoxSound.join (box := joinbox8_rLRRRRRRLRL) .k ((7 : ℚ) / 16)
              subsound8_57
              subsound8_58)
            (LRCompactVBoxSound.join (box := joinbox8_rLRRRRRRLRR) .k ((7 : ℚ) / 16)
              subsound8_59
              subsound8_60)))
        (LRCompactVBoxSound.join (box := joinbox8_rLRRRRRRR) .chi ((293 : ℚ) / 320)
          (LRCompactVBoxSound.join (box := joinbox8_rLRRRRRRRL) .s ((15 : ℚ) / 32)
            (LRCompactVBoxSound.join (box := joinbox8_rLRRRRRRRLL) .k ((23 : ℚ) / 48)
              subsound8_61
              subsound8_62)
            (LRCompactVBoxSound.join (box := joinbox8_rLRRRRRRRLR) .k ((23 : ℚ) / 48)
              (LRCompactVBoxSound.join (box := joinbox8_rLRRRRRRRLRL) .chi ((583 : ℚ) / 640)
                subsound8_63
                subsound8_64)
              (LRCompactVBoxSound.join (box := joinbox8_rLRRRRRRRLRR) .chi ((583 : ℚ) / 640)
                subsound8_65
                subsound8_66)))
          (LRCompactVBoxSound.join (box := joinbox8_rLRRRRRRRR) .s ((15 : ℚ) / 32)
            (LRCompactVBoxSound.join (box := joinbox8_rLRRRRRRRRL) .k ((23 : ℚ) / 48)
              subsound8_67
              subsound8_68)
            (LRCompactVBoxSound.join (box := joinbox8_rLRRRRRRRRR) .k ((23 : ℚ) / 48)
              subsound8_69
              (LRCompactVBoxSound.join (box := joinbox8_rLRRRRRRRRRR) .chi ((589 : ℚ) / 640)
                subsound8_70
                subsound8_71)))))))

end CourtadeKumar.GeneratedLRCompactVLowR
