import InformationTheory.CourtadeKumar.LRCompactVStreamingReplay

/-!
# Kernel-checked refinement of the compact-V native pilot

This certificate covers the same box as `NativeReplay.CompactVPilot`, with
coordinates `(R,v,t²)`. Its fixed subdivision has eight chi strips and two
v intervals per strip, giving sixteen leaves. It replaces the native search
with explicit geometry and reduces the logarithm/series lengths from
`34/32/72/32` to `8/12/16/12`. All finite tails are still bounded by the
existing production checker and its soundness theorem.

The arithmetic and the real inequality are checked without native reduction.
This is one bounded region, not a complete historical slab or the full CK
certificate family.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CourtadeKumar.CompactVKernelPilot

def box : CertificateBox where
  sLo := 31 / 64
  sHi := 33 / 64
  kLo := 31 / 64
  kHi := 33 / 64
  chiLo := 57 / 64
  chiHi := 59 / 64

/-- A fixed covering tree; no search or acceptance decision constructs its shape. -/
def stripTree : Nat → CertificateBox →
    SubdivisionCertificate LRCompactVLeafCertificate LRCompactVDiscardCertificate
  | 0, b =>
      .split .k (1 / 2)
        (.accept (LRCompactVLeafCertificate.auto 16 (b.lower .k (1 / 2))))
        (.accept (LRCompactVLeafCertificate.auto 16 (b.upper .k (1 / 2))))
  | n + 1, b =>
      let cut := (b.chiLo + b.chiHi) / 2
      .split .chi cut (stripTree n (b.lower .chi cut))
        (stripTree n (b.upper .chi cut))

def tree := stripTree 3 box

theorem checked : tree.check
    (LRCompactVLeafCertificate.check 8 12 16 12)
    (LRCompactVDiscardCertificate.check 8) box = true := by
  decide +kernel

/-- The original production reserve on every relevant point in the box. -/
theorem certificate_sound {point : CertificatePoint}
    (hpoint : box.Contains point) (hphysical : LRCompactVPhysical point) :
    0 ≤ lrCompactVReserveTarget point :=
  lrCompactVPhysicalSubdivisionCertificate_sound 8 12 16 12
    checked point hpoint hphysical

theorem center_mem_box :
    box.Contains { s := 1 / 2, k := 1 / 2, chi := 29 / 32 } := by
  norm_num [box, CertificateBox.Contains]

end CourtadeKumar.CompactVKernelPilot
