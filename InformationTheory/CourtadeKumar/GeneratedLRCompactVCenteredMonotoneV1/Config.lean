import InformationTheory.CourtadeKumar.LRCompactVCenteredMonotoneCheckedTreeCore

/-!
Untrusted generated data for the eight-strip centered-monotone replay.
Every arithmetic assertion is checked separately in the generated chunks;
this module contains only fixed data and exact subdivision paths.

Generator SHA-256: a703879482659554171c4155f97a7dabc5b841cf9b3c17e4fc53421536f9e8e8
Design SHA-256: 5b48a177063dc0dde6e42d266b0649b9c338353987a60fb27135c1dc791f1325
Observation SHA-256: 43eaa0d8dd4f406b5b4b1922d9832bfbe70139185d99dbae1079e672982c3421
-/

set_option autoImplicit false

namespace CourtadeKumar
namespace GeneratedLRCompactVCenteredMonotoneV1

open LRCompactVCenteredMonotoneLeaf

def logTerms : ℕ := 34
def halfLogTerms : ℕ := 34
def dTerms : ℕ := 34

abbrev CheckedTree (root : CertificateBox) : Type :=
  LRCompactVCenteredMonotoneCheckedTree.CheckedTree
    logTerms halfLogTerms dTerms root

def rootBox : CertificateBox :=
  LRCompactVCenteredMonotoneConfig.rootBox

def cut1 : ℚ := ((121 : ℚ) / 128)
def cut2 : ℚ := ((487 : ℚ) / 512)
def cut3 : ℚ := ((489 : ℚ) / 512)
def cut4 : ℚ := ((491 : ℚ) / 512)
def cut5 : ℚ := ((493 : ℚ) / 512)
def cut6 : ℚ := ((247 : ℚ) / 256)
def cut7 : ℚ := ((495 : ℚ) / 512)

def boxL : CertificateBox := rootBox.lower .k cut4
def boxR : CertificateBox := rootBox.upper .k cut4
def boxLL : CertificateBox := boxL.lower .k cut2
def boxLR : CertificateBox := boxL.upper .k cut2
def boxRL : CertificateBox := boxR.lower .k cut6
def boxRR : CertificateBox := boxR.upper .k cut6

def box0 : CertificateBox := boxLL.lower .k cut1
def box1 : CertificateBox := boxLL.upper .k cut1
def box2 : CertificateBox := boxLR.lower .k cut3
def box3 : CertificateBox := boxLR.upper .k cut3
def box4 : CertificateBox := boxRL.lower .k cut5
def box5 : CertificateBox := boxRL.upper .k cut5
def box6 : CertificateBox := boxRR.lower .k cut7
def box7 : CertificateBox := boxRR.upper .k cut7

def row0 : Row where
  vLoNum := 74276402357122816493947453440
  vHiNum := 74895372376765506631397015552
  lambdaNum := 13834888887324821975059747083
  head := .n192
  geometry := .tangent 78299707484800302387369607168
  logOnePlusVHi :=
    { exponent := (0 : ℤ)
      mantissa := ((249 : ℚ) / 128) }

def row1 : Row where
  vLoNum := 74895372376765506631397015552
  vHiNum := 75359599891497524234484187136
  lambdaNum := 14960625174002381896681370548
  head := .n128
  geometry := .tangent 78609192494621647456094388224
  logOnePlusVHi :=
    { exponent := (0 : ℤ)
      mantissa := ((999 : ℚ) / 512) }

def row2 : Row where
  vLoNum := 75359599891497524234484187136
  vHiNum := 75669084901318869303208968192
  lambdaNum := 15951159665030050164768612277
  head := .n128
  geometry := .corner
  logOnePlusVHi :=
    { exponent := (0 : ℤ)
      mantissa := ((1001 : ℚ) / 512) }

def row3 : Row where
  vLoNum := 75669084901318869303208968192
  vHiNum := 75978569911140214371933749248
  lambdaNum := 16689861455500656831882410258
  head := .n128
  geometry := .corner
  logOnePlusVHi :=
    { exponent := (0 : ℤ)
      mantissa := ((1003 : ℚ) / 512) }

def row4 : Row where
  vLoNum := 75978569911140214371933749248
  vHiNum := 76288054920961559440658530304
  lambdaNum := 17511123416826155740579640948
  head := .n192
  geometry := .corner
  logOnePlusVHi :=
    { exponent := (0 : ℤ)
      mantissa := ((1005 : ℚ) / 512) }

def row5 : Row where
  vLoNum := 76288054920961559440658530304
  vHiNum := 76442797425872231975020920832
  lambdaNum := 18442945384415776252697960556
  head := .n128
  geometry := .corner
  logOnePlusVHi :=
    { exponent := (0 : ℤ)
      mantissa := ((503 : ℚ) / 256) }

def row6 : Row where
  vLoNum := 76442797425872231975020920832
  vHiNum := 76597539930782904509383311360
  lambdaNum := 18946394230310079465403036085
  head := .n128
  geometry := .corner
  logOnePlusVHi :=
    { exponent := (0 : ℤ)
      mantissa := ((1007 : ℚ) / 512) }

def row7 : Row where
  vLoNum := 76597539930782904509383311360
  vHiNum := 76752282435693577043745701888
  lambdaNum := 19482793518227463114124536054
  head := .n128
  geometry := .corner
  logOnePlusVHi :=
    { exponent := (0 : ℤ)
      mantissa := ((63 : ℚ) / 32) }

end GeneratedLRCompactVCenteredMonotoneV1
end CourtadeKumar
