import InformationTheory.CourtadeKumar.IntervalSubdivisionCertificateCore
import InformationTheory.CourtadeKumar.LRCompactVFixedDyadicIntervalCore

/-!
# Shared executable data for the adjacent centered-monotone terminals

The eight adjacent compact-`V` strips use one fixed precision, channel
interval, shape interval, and endpoint-kernel enclosure.  Keeping these
constants in a proof-free core module lets both the executable leaf checker
and the later soundness adapter reuse them without putting common data in
every row payload.
-/

set_option autoImplicit false

namespace CourtadeKumar
namespace LRCompactVCenteredMonotoneConfig

open LRCompactVFixedDyadic

/-- Fixed-dyadic precision shared by all eight adjacent terminals. -/
def bits : ℕ := 96

/-- Common rational parent box of the eight adjacent `v` strips. -/
def rootBox : CertificateBox where
  sLo := 921 / 1024
  sHi := 9 / 10
  kLo := 15 / 16
  kHi := 31 / 32
  chiLo := 63 / 64
  chiHi := 127 / 128

/-- Outward 96-bit enclosure of the common channel interval. -/
def rInterval : NatInterval :=
  ⟨71258923511364702073880838144, 71305346262837903834189555303⟩

/-- Exact 96-bit enclosure of the full adjacent `v` range. -/
def vRootInterval : NatInterval :=
  ⟨74276402357122816493947453440, 76752282435693577043745701888⟩

/-- Exact 96-bit enclosure of the common squared-shape interval. -/
def xInterval : NatInterval :=
  ⟨77990222474978957318644826112, 78609192494621647456094388224⟩

/-- Shared endpoint-tight enclosure of `W_R(1)` on `rootBox`. -/
def wOne : NatInterval :=
  ⟨1782141680280723889127714657, 1869861642996119020795856175⟩

end LRCompactVCenteredMonotoneConfig
end CourtadeKumar
