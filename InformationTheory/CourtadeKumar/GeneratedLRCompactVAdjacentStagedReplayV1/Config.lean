import InformationTheory.CourtadeKumar.LRCompactVStagedGroupedCheckedTree
import InformationTheory.CourtadeKumar.KernelCheckedBoolCommand

/-! Generated from an untrusted exact-Lean plan.  Terminal kernel checks are
the sole arithmetic proof authority.  Plan SHA-256: eca9a4fe9cd47d103689a6d032cfac6a865563e201ac1daac553dc0138372a45. -/

set_option autoImplicit false

namespace CourtadeKumar
namespace GeneratedLRCompactVAdjacentStagedReplayV1

abbrev CheckedTree := LRCompactVStagedGroupedCheckedTree.CheckedTree

def planSha256 : String := "eca9a4fe9cd47d103689a6d032cfac6a865563e201ac1daac553dc0138372a45"

def logTerms : ℕ := 34
def pZeroTerms : ℕ := 64
def wTerms : ℕ := 64
def dTerms : ℕ := 34
def directN : ℕ := 64
def logFuel : ℕ := 16
def fuel : ℕ := 12

def box_r : CertificateBox where
  sLo := ((921 : ℚ) / 1024)
  sHi := ((9 : ℚ) / 10)
  kLo := ((15 : ℚ) / 16)
  kHi := ((31 : ℚ) / 32)
  chiLo := ((63 : ℚ) / 64)
  chiHi := ((127 : ℚ) / 128)

def box_rL : CertificateBox where
  sLo := ((921 : ℚ) / 1024)
  sHi := ((9 : ℚ) / 10)
  kLo := ((15 : ℚ) / 16)
  kHi := ((61 : ℚ) / 64)
  chiLo := ((63 : ℚ) / 64)
  chiHi := ((127 : ℚ) / 128)

def box_rR : CertificateBox where
  sLo := ((921 : ℚ) / 1024)
  sHi := ((9 : ℚ) / 10)
  kLo := ((61 : ℚ) / 64)
  kHi := ((31 : ℚ) / 32)
  chiLo := ((63 : ℚ) / 64)
  chiHi := ((127 : ℚ) / 128)

def box_rLL : CertificateBox where
  sLo := ((921 : ℚ) / 1024)
  sHi := ((9 : ℚ) / 10)
  kLo := ((15 : ℚ) / 16)
  kHi := ((121 : ℚ) / 128)
  chiLo := ((63 : ℚ) / 64)
  chiHi := ((127 : ℚ) / 128)

def box_rLR : CertificateBox where
  sLo := ((921 : ℚ) / 1024)
  sHi := ((9 : ℚ) / 10)
  kLo := ((121 : ℚ) / 128)
  kHi := ((61 : ℚ) / 64)
  chiLo := ((63 : ℚ) / 64)
  chiHi := ((127 : ℚ) / 128)

def box_rRL : CertificateBox where
  sLo := ((921 : ℚ) / 1024)
  sHi := ((9 : ℚ) / 10)
  kLo := ((61 : ℚ) / 64)
  kHi := ((123 : ℚ) / 128)
  chiLo := ((63 : ℚ) / 64)
  chiHi := ((127 : ℚ) / 128)

def box_rRR : CertificateBox where
  sLo := ((921 : ℚ) / 1024)
  sHi := ((9 : ℚ) / 10)
  kLo := ((123 : ℚ) / 128)
  kHi := ((31 : ℚ) / 32)
  chiLo := ((63 : ℚ) / 64)
  chiHi := ((127 : ℚ) / 128)

def box_rLLL : CertificateBox where
  sLo := ((921 : ℚ) / 1024)
  sHi := ((9 : ℚ) / 10)
  kLo := ((15 : ℚ) / 16)
  kHi := ((121 : ℚ) / 128)
  chiLo := ((63 : ℚ) / 64)
  chiHi := ((253 : ℚ) / 256)

def box_rLLR : CertificateBox where
  sLo := ((921 : ℚ) / 1024)
  sHi := ((9 : ℚ) / 10)
  kLo := ((15 : ℚ) / 16)
  kHi := ((121 : ℚ) / 128)
  chiLo := ((253 : ℚ) / 256)
  chiHi := ((127 : ℚ) / 128)

def box_rLRL : CertificateBox where
  sLo := ((921 : ℚ) / 1024)
  sHi := ((9 : ℚ) / 10)
  kLo := ((121 : ℚ) / 128)
  kHi := ((61 : ℚ) / 64)
  chiLo := ((63 : ℚ) / 64)
  chiHi := ((253 : ℚ) / 256)

def box_rLRR : CertificateBox where
  sLo := ((921 : ℚ) / 1024)
  sHi := ((9 : ℚ) / 10)
  kLo := ((121 : ℚ) / 128)
  kHi := ((61 : ℚ) / 64)
  chiLo := ((253 : ℚ) / 256)
  chiHi := ((127 : ℚ) / 128)

def box_rRLL : CertificateBox where
  sLo := ((921 : ℚ) / 1024)
  sHi := ((9 : ℚ) / 10)
  kLo := ((61 : ℚ) / 64)
  kHi := ((123 : ℚ) / 128)
  chiLo := ((63 : ℚ) / 64)
  chiHi := ((253 : ℚ) / 256)

def box_rRLR : CertificateBox where
  sLo := ((921 : ℚ) / 1024)
  sHi := ((9 : ℚ) / 10)
  kLo := ((61 : ℚ) / 64)
  kHi := ((123 : ℚ) / 128)
  chiLo := ((253 : ℚ) / 256)
  chiHi := ((127 : ℚ) / 128)

def box_rRRL : CertificateBox where
  sLo := ((921 : ℚ) / 1024)
  sHi := ((9 : ℚ) / 10)
  kLo := ((123 : ℚ) / 128)
  kHi := ((31 : ℚ) / 32)
  chiLo := ((63 : ℚ) / 64)
  chiHi := ((253 : ℚ) / 256)

def box_rRRR : CertificateBox where
  sLo := ((921 : ℚ) / 1024)
  sHi := ((9 : ℚ) / 10)
  kLo := ((123 : ℚ) / 128)
  kHi := ((31 : ℚ) / 32)
  chiLo := ((253 : ℚ) / 256)
  chiHi := ((127 : ℚ) / 128)

def box_rLLLL : CertificateBox where
  sLo := ((921 : ℚ) / 1024)
  sHi := ((9 : ℚ) / 10)
  kLo := ((15 : ℚ) / 16)
  kHi := ((241 : ℚ) / 256)
  chiLo := ((63 : ℚ) / 64)
  chiHi := ((253 : ℚ) / 256)

def box_rLLLR : CertificateBox where
  sLo := ((921 : ℚ) / 1024)
  sHi := ((9 : ℚ) / 10)
  kLo := ((241 : ℚ) / 256)
  kHi := ((121 : ℚ) / 128)
  chiLo := ((63 : ℚ) / 64)
  chiHi := ((253 : ℚ) / 256)

def box_rLLRL : CertificateBox where
  sLo := ((921 : ℚ) / 1024)
  sHi := ((9 : ℚ) / 10)
  kLo := ((15 : ℚ) / 16)
  kHi := ((241 : ℚ) / 256)
  chiLo := ((253 : ℚ) / 256)
  chiHi := ((127 : ℚ) / 128)

def box_rLLRR : CertificateBox where
  sLo := ((921 : ℚ) / 1024)
  sHi := ((9 : ℚ) / 10)
  kLo := ((241 : ℚ) / 256)
  kHi := ((121 : ℚ) / 128)
  chiLo := ((253 : ℚ) / 256)
  chiHi := ((127 : ℚ) / 128)

def box_rLRLL : CertificateBox where
  sLo := ((921 : ℚ) / 1024)
  sHi := ((9 : ℚ) / 10)
  kLo := ((121 : ℚ) / 128)
  kHi := ((243 : ℚ) / 256)
  chiLo := ((63 : ℚ) / 64)
  chiHi := ((253 : ℚ) / 256)

def box_rLRLR : CertificateBox where
  sLo := ((921 : ℚ) / 1024)
  sHi := ((9 : ℚ) / 10)
  kLo := ((243 : ℚ) / 256)
  kHi := ((61 : ℚ) / 64)
  chiLo := ((63 : ℚ) / 64)
  chiHi := ((253 : ℚ) / 256)

def box_rLRRL : CertificateBox where
  sLo := ((921 : ℚ) / 1024)
  sHi := ((9 : ℚ) / 10)
  kLo := ((121 : ℚ) / 128)
  kHi := ((243 : ℚ) / 256)
  chiLo := ((253 : ℚ) / 256)
  chiHi := ((127 : ℚ) / 128)

def box_rLRRR : CertificateBox where
  sLo := ((921 : ℚ) / 1024)
  sHi := ((9 : ℚ) / 10)
  kLo := ((243 : ℚ) / 256)
  kHi := ((61 : ℚ) / 64)
  chiLo := ((253 : ℚ) / 256)
  chiHi := ((127 : ℚ) / 128)

def box_rRLLL : CertificateBox where
  sLo := ((921 : ℚ) / 1024)
  sHi := ((9 : ℚ) / 10)
  kLo := ((61 : ℚ) / 64)
  kHi := ((245 : ℚ) / 256)
  chiLo := ((63 : ℚ) / 64)
  chiHi := ((253 : ℚ) / 256)

def box_rRLLR : CertificateBox where
  sLo := ((921 : ℚ) / 1024)
  sHi := ((9 : ℚ) / 10)
  kLo := ((245 : ℚ) / 256)
  kHi := ((123 : ℚ) / 128)
  chiLo := ((63 : ℚ) / 64)
  chiHi := ((253 : ℚ) / 256)

def box_rRLRL : CertificateBox where
  sLo := ((921 : ℚ) / 1024)
  sHi := ((9 : ℚ) / 10)
  kLo := ((61 : ℚ) / 64)
  kHi := ((245 : ℚ) / 256)
  chiLo := ((253 : ℚ) / 256)
  chiHi := ((127 : ℚ) / 128)

def box_rRLRR : CertificateBox where
  sLo := ((921 : ℚ) / 1024)
  sHi := ((9 : ℚ) / 10)
  kLo := ((245 : ℚ) / 256)
  kHi := ((123 : ℚ) / 128)
  chiLo := ((253 : ℚ) / 256)
  chiHi := ((127 : ℚ) / 128)

def box_rRRLL : CertificateBox where
  sLo := ((921 : ℚ) / 1024)
  sHi := ((9 : ℚ) / 10)
  kLo := ((123 : ℚ) / 128)
  kHi := ((247 : ℚ) / 256)
  chiLo := ((63 : ℚ) / 64)
  chiHi := ((253 : ℚ) / 256)

def box_rRRLR : CertificateBox where
  sLo := ((921 : ℚ) / 1024)
  sHi := ((9 : ℚ) / 10)
  kLo := ((247 : ℚ) / 256)
  kHi := ((31 : ℚ) / 32)
  chiLo := ((63 : ℚ) / 64)
  chiHi := ((253 : ℚ) / 256)

def box_rRRRL : CertificateBox where
  sLo := ((921 : ℚ) / 1024)
  sHi := ((9 : ℚ) / 10)
  kLo := ((123 : ℚ) / 128)
  kHi := ((247 : ℚ) / 256)
  chiLo := ((253 : ℚ) / 256)
  chiHi := ((127 : ℚ) / 128)

def box_rRRRR : CertificateBox where
  sLo := ((921 : ℚ) / 1024)
  sHi := ((9 : ℚ) / 10)
  kLo := ((247 : ℚ) / 256)
  kHi := ((31 : ℚ) / 32)
  chiLo := ((253 : ℚ) / 256)
  chiHi := ((127 : ℚ) / 128)

def box_rLLLLL : CertificateBox where
  sLo := ((921 : ℚ) / 1024)
  sHi := ((9 : ℚ) / 10)
  kLo := ((15 : ℚ) / 16)
  kHi := ((241 : ℚ) / 256)
  chiLo := ((63 : ℚ) / 64)
  chiHi := ((505 : ℚ) / 512)

def box_rLLLLR : CertificateBox where
  sLo := ((921 : ℚ) / 1024)
  sHi := ((9 : ℚ) / 10)
  kLo := ((15 : ℚ) / 16)
  kHi := ((241 : ℚ) / 256)
  chiLo := ((505 : ℚ) / 512)
  chiHi := ((253 : ℚ) / 256)

def box_rLLLRL : CertificateBox where
  sLo := ((921 : ℚ) / 1024)
  sHi := ((9 : ℚ) / 10)
  kLo := ((241 : ℚ) / 256)
  kHi := ((121 : ℚ) / 128)
  chiLo := ((63 : ℚ) / 64)
  chiHi := ((505 : ℚ) / 512)

def box_rLLLRR : CertificateBox where
  sLo := ((921 : ℚ) / 1024)
  sHi := ((9 : ℚ) / 10)
  kLo := ((241 : ℚ) / 256)
  kHi := ((121 : ℚ) / 128)
  chiLo := ((505 : ℚ) / 512)
  chiHi := ((253 : ℚ) / 256)

def box_rLLRLL : CertificateBox where
  sLo := ((921 : ℚ) / 1024)
  sHi := ((9 : ℚ) / 10)
  kLo := ((15 : ℚ) / 16)
  kHi := ((241 : ℚ) / 256)
  chiLo := ((253 : ℚ) / 256)
  chiHi := ((507 : ℚ) / 512)

def box_rLLRLR : CertificateBox where
  sLo := ((921 : ℚ) / 1024)
  sHi := ((9 : ℚ) / 10)
  kLo := ((15 : ℚ) / 16)
  kHi := ((241 : ℚ) / 256)
  chiLo := ((507 : ℚ) / 512)
  chiHi := ((127 : ℚ) / 128)

def box_rLLRRL : CertificateBox where
  sLo := ((921 : ℚ) / 1024)
  sHi := ((9 : ℚ) / 10)
  kLo := ((241 : ℚ) / 256)
  kHi := ((121 : ℚ) / 128)
  chiLo := ((253 : ℚ) / 256)
  chiHi := ((507 : ℚ) / 512)

def box_rLLRRR : CertificateBox where
  sLo := ((921 : ℚ) / 1024)
  sHi := ((9 : ℚ) / 10)
  kLo := ((241 : ℚ) / 256)
  kHi := ((121 : ℚ) / 128)
  chiLo := ((507 : ℚ) / 512)
  chiHi := ((127 : ℚ) / 128)

def box_rLRLLL : CertificateBox where
  sLo := ((921 : ℚ) / 1024)
  sHi := ((9 : ℚ) / 10)
  kLo := ((121 : ℚ) / 128)
  kHi := ((243 : ℚ) / 256)
  chiLo := ((63 : ℚ) / 64)
  chiHi := ((505 : ℚ) / 512)

def box_rLRLLR : CertificateBox where
  sLo := ((921 : ℚ) / 1024)
  sHi := ((9 : ℚ) / 10)
  kLo := ((121 : ℚ) / 128)
  kHi := ((243 : ℚ) / 256)
  chiLo := ((505 : ℚ) / 512)
  chiHi := ((253 : ℚ) / 256)

def box_rLRLRL : CertificateBox where
  sLo := ((921 : ℚ) / 1024)
  sHi := ((9 : ℚ) / 10)
  kLo := ((243 : ℚ) / 256)
  kHi := ((61 : ℚ) / 64)
  chiLo := ((63 : ℚ) / 64)
  chiHi := ((505 : ℚ) / 512)

def box_rLRLRR : CertificateBox where
  sLo := ((921 : ℚ) / 1024)
  sHi := ((9 : ℚ) / 10)
  kLo := ((243 : ℚ) / 256)
  kHi := ((61 : ℚ) / 64)
  chiLo := ((505 : ℚ) / 512)
  chiHi := ((253 : ℚ) / 256)

def box_rLRRLL : CertificateBox where
  sLo := ((921 : ℚ) / 1024)
  sHi := ((9 : ℚ) / 10)
  kLo := ((121 : ℚ) / 128)
  kHi := ((243 : ℚ) / 256)
  chiLo := ((253 : ℚ) / 256)
  chiHi := ((507 : ℚ) / 512)

def box_rLRRLR : CertificateBox where
  sLo := ((921 : ℚ) / 1024)
  sHi := ((9 : ℚ) / 10)
  kLo := ((121 : ℚ) / 128)
  kHi := ((243 : ℚ) / 256)
  chiLo := ((507 : ℚ) / 512)
  chiHi := ((127 : ℚ) / 128)

def box_rLRRRL : CertificateBox where
  sLo := ((921 : ℚ) / 1024)
  sHi := ((9 : ℚ) / 10)
  kLo := ((243 : ℚ) / 256)
  kHi := ((61 : ℚ) / 64)
  chiLo := ((253 : ℚ) / 256)
  chiHi := ((507 : ℚ) / 512)

def box_rLRRRR : CertificateBox where
  sLo := ((921 : ℚ) / 1024)
  sHi := ((9 : ℚ) / 10)
  kLo := ((243 : ℚ) / 256)
  kHi := ((61 : ℚ) / 64)
  chiLo := ((507 : ℚ) / 512)
  chiHi := ((127 : ℚ) / 128)

def box_rRLLLL : CertificateBox where
  sLo := ((921 : ℚ) / 1024)
  sHi := ((9 : ℚ) / 10)
  kLo := ((61 : ℚ) / 64)
  kHi := ((245 : ℚ) / 256)
  chiLo := ((63 : ℚ) / 64)
  chiHi := ((505 : ℚ) / 512)

def box_rRLLLR : CertificateBox where
  sLo := ((921 : ℚ) / 1024)
  sHi := ((9 : ℚ) / 10)
  kLo := ((61 : ℚ) / 64)
  kHi := ((245 : ℚ) / 256)
  chiLo := ((505 : ℚ) / 512)
  chiHi := ((253 : ℚ) / 256)

def box_rRLLRL : CertificateBox where
  sLo := ((921 : ℚ) / 1024)
  sHi := ((9 : ℚ) / 10)
  kLo := ((245 : ℚ) / 256)
  kHi := ((123 : ℚ) / 128)
  chiLo := ((63 : ℚ) / 64)
  chiHi := ((505 : ℚ) / 512)

def box_rRLLRR : CertificateBox where
  sLo := ((921 : ℚ) / 1024)
  sHi := ((9 : ℚ) / 10)
  kLo := ((245 : ℚ) / 256)
  kHi := ((123 : ℚ) / 128)
  chiLo := ((505 : ℚ) / 512)
  chiHi := ((253 : ℚ) / 256)

def box_rRLRLL : CertificateBox where
  sLo := ((921 : ℚ) / 1024)
  sHi := ((9 : ℚ) / 10)
  kLo := ((61 : ℚ) / 64)
  kHi := ((245 : ℚ) / 256)
  chiLo := ((253 : ℚ) / 256)
  chiHi := ((507 : ℚ) / 512)

def box_rRLRLR : CertificateBox where
  sLo := ((921 : ℚ) / 1024)
  sHi := ((9 : ℚ) / 10)
  kLo := ((61 : ℚ) / 64)
  kHi := ((245 : ℚ) / 256)
  chiLo := ((507 : ℚ) / 512)
  chiHi := ((127 : ℚ) / 128)

def box_rRLRRL : CertificateBox where
  sLo := ((921 : ℚ) / 1024)
  sHi := ((9 : ℚ) / 10)
  kLo := ((245 : ℚ) / 256)
  kHi := ((123 : ℚ) / 128)
  chiLo := ((253 : ℚ) / 256)
  chiHi := ((507 : ℚ) / 512)

def box_rRLRRR : CertificateBox where
  sLo := ((921 : ℚ) / 1024)
  sHi := ((9 : ℚ) / 10)
  kLo := ((245 : ℚ) / 256)
  kHi := ((123 : ℚ) / 128)
  chiLo := ((507 : ℚ) / 512)
  chiHi := ((127 : ℚ) / 128)

def box_rRRLLL : CertificateBox where
  sLo := ((921 : ℚ) / 1024)
  sHi := ((9 : ℚ) / 10)
  kLo := ((123 : ℚ) / 128)
  kHi := ((493 : ℚ) / 512)
  chiLo := ((63 : ℚ) / 64)
  chiHi := ((253 : ℚ) / 256)

def box_rRRLLR : CertificateBox where
  sLo := ((921 : ℚ) / 1024)
  sHi := ((9 : ℚ) / 10)
  kLo := ((493 : ℚ) / 512)
  kHi := ((247 : ℚ) / 256)
  chiLo := ((63 : ℚ) / 64)
  chiHi := ((253 : ℚ) / 256)

def box_rRRLRL : CertificateBox where
  sLo := ((921 : ℚ) / 1024)
  sHi := ((9 : ℚ) / 10)
  kLo := ((247 : ℚ) / 256)
  kHi := ((495 : ℚ) / 512)
  chiLo := ((63 : ℚ) / 64)
  chiHi := ((253 : ℚ) / 256)

def box_rRRLRR : CertificateBox where
  sLo := ((921 : ℚ) / 1024)
  sHi := ((9 : ℚ) / 10)
  kLo := ((495 : ℚ) / 512)
  kHi := ((31 : ℚ) / 32)
  chiLo := ((63 : ℚ) / 64)
  chiHi := ((253 : ℚ) / 256)

def box_rRRRLL : CertificateBox where
  sLo := ((921 : ℚ) / 1024)
  sHi := ((9 : ℚ) / 10)
  kLo := ((123 : ℚ) / 128)
  kHi := ((247 : ℚ) / 256)
  chiLo := ((253 : ℚ) / 256)
  chiHi := ((507 : ℚ) / 512)

def box_rRRRLR : CertificateBox where
  sLo := ((921 : ℚ) / 1024)
  sHi := ((9 : ℚ) / 10)
  kLo := ((123 : ℚ) / 128)
  kHi := ((247 : ℚ) / 256)
  chiLo := ((507 : ℚ) / 512)
  chiHi := ((127 : ℚ) / 128)

def box_rRRRRL : CertificateBox where
  sLo := ((921 : ℚ) / 1024)
  sHi := ((9 : ℚ) / 10)
  kLo := ((247 : ℚ) / 256)
  kHi := ((31 : ℚ) / 32)
  chiLo := ((253 : ℚ) / 256)
  chiHi := ((507 : ℚ) / 512)

def box_rRRRRR : CertificateBox where
  sLo := ((921 : ℚ) / 1024)
  sHi := ((9 : ℚ) / 10)
  kLo := ((247 : ℚ) / 256)
  kHi := ((31 : ℚ) / 32)
  chiLo := ((507 : ℚ) / 512)
  chiHi := ((127 : ℚ) / 128)

def box_rLRLLLL : CertificateBox where
  sLo := ((921 : ℚ) / 1024)
  sHi := ((9 : ℚ) / 10)
  kLo := ((121 : ℚ) / 128)
  kHi := ((485 : ℚ) / 512)
  chiLo := ((63 : ℚ) / 64)
  chiHi := ((505 : ℚ) / 512)

def box_rLRLLLR : CertificateBox where
  sLo := ((921 : ℚ) / 1024)
  sHi := ((9 : ℚ) / 10)
  kLo := ((485 : ℚ) / 512)
  kHi := ((243 : ℚ) / 256)
  chiLo := ((63 : ℚ) / 64)
  chiHi := ((505 : ℚ) / 512)

def box_rLRLRLL : CertificateBox where
  sLo := ((921 : ℚ) / 1024)
  sHi := ((9 : ℚ) / 10)
  kLo := ((243 : ℚ) / 256)
  kHi := ((487 : ℚ) / 512)
  chiLo := ((63 : ℚ) / 64)
  chiHi := ((505 : ℚ) / 512)

def box_rLRLRLR : CertificateBox where
  sLo := ((921 : ℚ) / 1024)
  sHi := ((9 : ℚ) / 10)
  kLo := ((487 : ℚ) / 512)
  kHi := ((61 : ℚ) / 64)
  chiLo := ((63 : ℚ) / 64)
  chiHi := ((505 : ℚ) / 512)

def box_rLRLRRL : CertificateBox where
  sLo := ((921 : ℚ) / 1024)
  sHi := ((9 : ℚ) / 10)
  kLo := ((243 : ℚ) / 256)
  kHi := ((487 : ℚ) / 512)
  chiLo := ((505 : ℚ) / 512)
  chiHi := ((253 : ℚ) / 256)

def box_rLRLRRR : CertificateBox where
  sLo := ((921 : ℚ) / 1024)
  sHi := ((9 : ℚ) / 10)
  kLo := ((487 : ℚ) / 512)
  kHi := ((61 : ℚ) / 64)
  chiLo := ((505 : ℚ) / 512)
  chiHi := ((253 : ℚ) / 256)

def box_rRLLLLL : CertificateBox where
  sLo := ((921 : ℚ) / 1024)
  sHi := ((9 : ℚ) / 10)
  kLo := ((61 : ℚ) / 64)
  kHi := ((489 : ℚ) / 512)
  chiLo := ((63 : ℚ) / 64)
  chiHi := ((505 : ℚ) / 512)

def box_rRLLLLR : CertificateBox where
  sLo := ((921 : ℚ) / 1024)
  sHi := ((9 : ℚ) / 10)
  kLo := ((489 : ℚ) / 512)
  kHi := ((245 : ℚ) / 256)
  chiLo := ((63 : ℚ) / 64)
  chiHi := ((505 : ℚ) / 512)

def box_rRLLLRL : CertificateBox where
  sLo := ((921 : ℚ) / 1024)
  sHi := ((9 : ℚ) / 10)
  kLo := ((61 : ℚ) / 64)
  kHi := ((489 : ℚ) / 512)
  chiLo := ((505 : ℚ) / 512)
  chiHi := ((253 : ℚ) / 256)

def box_rRLLLRR : CertificateBox where
  sLo := ((921 : ℚ) / 1024)
  sHi := ((9 : ℚ) / 10)
  kLo := ((489 : ℚ) / 512)
  kHi := ((245 : ℚ) / 256)
  chiLo := ((505 : ℚ) / 512)
  chiHi := ((253 : ℚ) / 256)

def box_rRLLRLL : CertificateBox where
  sLo := ((921 : ℚ) / 1024)
  sHi := ((9 : ℚ) / 10)
  kLo := ((245 : ℚ) / 256)
  kHi := ((491 : ℚ) / 512)
  chiLo := ((63 : ℚ) / 64)
  chiHi := ((505 : ℚ) / 512)

def box_rRLLRLR : CertificateBox where
  sLo := ((921 : ℚ) / 1024)
  sHi := ((9 : ℚ) / 10)
  kLo := ((491 : ℚ) / 512)
  kHi := ((123 : ℚ) / 128)
  chiLo := ((63 : ℚ) / 64)
  chiHi := ((505 : ℚ) / 512)

def box_rRLLRRL : CertificateBox where
  sLo := ((921 : ℚ) / 1024)
  sHi := ((9 : ℚ) / 10)
  kLo := ((245 : ℚ) / 256)
  kHi := ((491 : ℚ) / 512)
  chiLo := ((505 : ℚ) / 512)
  chiHi := ((253 : ℚ) / 256)

def box_rRLLRRR : CertificateBox where
  sLo := ((921 : ℚ) / 1024)
  sHi := ((9 : ℚ) / 10)
  kLo := ((491 : ℚ) / 512)
  kHi := ((123 : ℚ) / 128)
  chiLo := ((505 : ℚ) / 512)
  chiHi := ((253 : ℚ) / 256)

def box_rRLRLLL : CertificateBox where
  sLo := ((921 : ℚ) / 1024)
  sHi := ((9 : ℚ) / 10)
  kLo := ((61 : ℚ) / 64)
  kHi := ((489 : ℚ) / 512)
  chiLo := ((253 : ℚ) / 256)
  chiHi := ((507 : ℚ) / 512)

def box_rRLRLLR : CertificateBox where
  sLo := ((921 : ℚ) / 1024)
  sHi := ((9 : ℚ) / 10)
  kLo := ((489 : ℚ) / 512)
  kHi := ((245 : ℚ) / 256)
  chiLo := ((253 : ℚ) / 256)
  chiHi := ((507 : ℚ) / 512)

def box_rRLRRLL : CertificateBox where
  sLo := ((921 : ℚ) / 1024)
  sHi := ((9 : ℚ) / 10)
  kLo := ((245 : ℚ) / 256)
  kHi := ((491 : ℚ) / 512)
  chiLo := ((253 : ℚ) / 256)
  chiHi := ((507 : ℚ) / 512)

def box_rRLRRLR : CertificateBox where
  sLo := ((921 : ℚ) / 1024)
  sHi := ((9 : ℚ) / 10)
  kLo := ((491 : ℚ) / 512)
  kHi := ((123 : ℚ) / 128)
  chiLo := ((253 : ℚ) / 256)
  chiHi := ((507 : ℚ) / 512)

def box_rRLRRRL : CertificateBox where
  sLo := ((921 : ℚ) / 1024)
  sHi := ((9 : ℚ) / 10)
  kLo := ((245 : ℚ) / 256)
  kHi := ((491 : ℚ) / 512)
  chiLo := ((507 : ℚ) / 512)
  chiHi := ((127 : ℚ) / 128)

def box_rRLRRRR : CertificateBox where
  sLo := ((921 : ℚ) / 1024)
  sHi := ((9 : ℚ) / 10)
  kLo := ((491 : ℚ) / 512)
  kHi := ((123 : ℚ) / 128)
  chiLo := ((507 : ℚ) / 512)
  chiHi := ((127 : ℚ) / 128)

def box_rRRLLLL : CertificateBox where
  sLo := ((921 : ℚ) / 1024)
  sHi := ((9 : ℚ) / 10)
  kLo := ((123 : ℚ) / 128)
  kHi := ((493 : ℚ) / 512)
  chiLo := ((63 : ℚ) / 64)
  chiHi := ((505 : ℚ) / 512)

def box_rRRLLLR : CertificateBox where
  sLo := ((921 : ℚ) / 1024)
  sHi := ((9 : ℚ) / 10)
  kLo := ((123 : ℚ) / 128)
  kHi := ((493 : ℚ) / 512)
  chiLo := ((505 : ℚ) / 512)
  chiHi := ((253 : ℚ) / 256)

def box_rRRLLRL : CertificateBox where
  sLo := ((921 : ℚ) / 1024)
  sHi := ((9 : ℚ) / 10)
  kLo := ((493 : ℚ) / 512)
  kHi := ((247 : ℚ) / 256)
  chiLo := ((63 : ℚ) / 64)
  chiHi := ((505 : ℚ) / 512)

def box_rRRLLRR : CertificateBox where
  sLo := ((921 : ℚ) / 1024)
  sHi := ((9 : ℚ) / 10)
  kLo := ((493 : ℚ) / 512)
  kHi := ((247 : ℚ) / 256)
  chiLo := ((505 : ℚ) / 512)
  chiHi := ((253 : ℚ) / 256)

def box_rRRLRLL : CertificateBox where
  sLo := ((921 : ℚ) / 1024)
  sHi := ((9 : ℚ) / 10)
  kLo := ((247 : ℚ) / 256)
  kHi := ((495 : ℚ) / 512)
  chiLo := ((63 : ℚ) / 64)
  chiHi := ((505 : ℚ) / 512)

def box_rRRLRLR : CertificateBox where
  sLo := ((921 : ℚ) / 1024)
  sHi := ((9 : ℚ) / 10)
  kLo := ((247 : ℚ) / 256)
  kHi := ((495 : ℚ) / 512)
  chiLo := ((505 : ℚ) / 512)
  chiHi := ((253 : ℚ) / 256)

def box_rRRLRRL : CertificateBox where
  sLo := ((921 : ℚ) / 1024)
  sHi := ((9 : ℚ) / 10)
  kLo := ((495 : ℚ) / 512)
  kHi := ((31 : ℚ) / 32)
  chiLo := ((63 : ℚ) / 64)
  chiHi := ((505 : ℚ) / 512)

def box_rRRLRRR : CertificateBox where
  sLo := ((921 : ℚ) / 1024)
  sHi := ((9 : ℚ) / 10)
  kLo := ((495 : ℚ) / 512)
  kHi := ((31 : ℚ) / 32)
  chiLo := ((505 : ℚ) / 512)
  chiHi := ((253 : ℚ) / 256)

def box_rRRRLLL : CertificateBox where
  sLo := ((921 : ℚ) / 1024)
  sHi := ((9 : ℚ) / 10)
  kLo := ((123 : ℚ) / 128)
  kHi := ((493 : ℚ) / 512)
  chiLo := ((253 : ℚ) / 256)
  chiHi := ((507 : ℚ) / 512)

def box_rRRRLLR : CertificateBox where
  sLo := ((921 : ℚ) / 1024)
  sHi := ((9 : ℚ) / 10)
  kLo := ((493 : ℚ) / 512)
  kHi := ((247 : ℚ) / 256)
  chiLo := ((253 : ℚ) / 256)
  chiHi := ((507 : ℚ) / 512)

def box_rRRRLRL : CertificateBox where
  sLo := ((921 : ℚ) / 1024)
  sHi := ((9 : ℚ) / 10)
  kLo := ((123 : ℚ) / 128)
  kHi := ((493 : ℚ) / 512)
  chiLo := ((507 : ℚ) / 512)
  chiHi := ((127 : ℚ) / 128)

def box_rRRRLRR : CertificateBox where
  sLo := ((921 : ℚ) / 1024)
  sHi := ((9 : ℚ) / 10)
  kLo := ((493 : ℚ) / 512)
  kHi := ((247 : ℚ) / 256)
  chiLo := ((507 : ℚ) / 512)
  chiHi := ((127 : ℚ) / 128)

def box_rRRRRLL : CertificateBox where
  sLo := ((921 : ℚ) / 1024)
  sHi := ((9 : ℚ) / 10)
  kLo := ((247 : ℚ) / 256)
  kHi := ((495 : ℚ) / 512)
  chiLo := ((253 : ℚ) / 256)
  chiHi := ((507 : ℚ) / 512)

def box_rRRRRLR : CertificateBox where
  sLo := ((921 : ℚ) / 1024)
  sHi := ((9 : ℚ) / 10)
  kLo := ((495 : ℚ) / 512)
  kHi := ((31 : ℚ) / 32)
  chiLo := ((253 : ℚ) / 256)
  chiHi := ((507 : ℚ) / 512)

def box_rRRRRRL : CertificateBox where
  sLo := ((921 : ℚ) / 1024)
  sHi := ((9 : ℚ) / 10)
  kLo := ((247 : ℚ) / 256)
  kHi := ((495 : ℚ) / 512)
  chiLo := ((507 : ℚ) / 512)
  chiHi := ((127 : ℚ) / 128)

def box_rRRRRRR : CertificateBox where
  sLo := ((921 : ℚ) / 1024)
  sHi := ((9 : ℚ) / 10)
  kLo := ((495 : ℚ) / 512)
  kHi := ((31 : ℚ) / 32)
  chiLo := ((507 : ℚ) / 512)
  chiHi := ((127 : ℚ) / 128)

def box_rRRLRRLL : CertificateBox where
  sLo := ((921 : ℚ) / 1024)
  sHi := ((9 : ℚ) / 10)
  kLo := ((495 : ℚ) / 512)
  kHi := ((991 : ℚ) / 1024)
  chiLo := ((63 : ℚ) / 64)
  chiHi := ((505 : ℚ) / 512)

def box_rRRLRRLR : CertificateBox where
  sLo := ((921 : ℚ) / 1024)
  sHi := ((9 : ℚ) / 10)
  kLo := ((991 : ℚ) / 1024)
  kHi := ((31 : ℚ) / 32)
  chiLo := ((63 : ℚ) / 64)
  chiHi := ((505 : ℚ) / 512)

def box_rRRLRRRL : CertificateBox where
  sLo := ((921 : ℚ) / 1024)
  sHi := ((9 : ℚ) / 10)
  kLo := ((495 : ℚ) / 512)
  kHi := ((991 : ℚ) / 1024)
  chiLo := ((505 : ℚ) / 512)
  chiHi := ((253 : ℚ) / 256)

def box_rRRLRRRR : CertificateBox where
  sLo := ((921 : ℚ) / 1024)
  sHi := ((9 : ℚ) / 10)
  kLo := ((991 : ℚ) / 1024)
  kHi := ((31 : ℚ) / 32)
  chiLo := ((505 : ℚ) / 512)
  chiHi := ((253 : ℚ) / 256)

def box_rRRRRLRL : CertificateBox where
  sLo := ((921 : ℚ) / 1024)
  sHi := ((9 : ℚ) / 10)
  kLo := ((495 : ℚ) / 512)
  kHi := ((991 : ℚ) / 1024)
  chiLo := ((253 : ℚ) / 256)
  chiHi := ((507 : ℚ) / 512)

def box_rRRRRLRR : CertificateBox where
  sLo := ((921 : ℚ) / 1024)
  sHi := ((9 : ℚ) / 10)
  kLo := ((991 : ℚ) / 1024)
  kHi := ((31 : ℚ) / 32)
  chiLo := ((253 : ℚ) / 256)
  chiHi := ((507 : ℚ) / 512)

abbrev rootBox : CertificateBox := box_r

end GeneratedLRCompactVAdjacentStagedReplayV1
end CourtadeKumar
