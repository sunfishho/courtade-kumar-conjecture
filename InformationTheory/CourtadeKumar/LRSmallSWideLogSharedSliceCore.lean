import InformationTheory.CourtadeKumar.LRSmallSBridgeCoreIntervalCore

/-!
# Canonical small-`s` slice expressions

The generated small-`s` leaves repeat relatively few `s`/`k` and `chi`
intervals.  This module factors the four corresponding interval expressions
through small endpoint records.  A generated cache can therefore establish a
substantial arithmetic equality once per distinct slice and transport it to a
leaf using only equality of rational endpoints.

There is no executable search or proof shortcut here: all transport theorems
are definitional equalities checked by the kernel.
-/

namespace CourtadeKumar
namespace LRSmallSWideLogSharedSliceCore

open LRSmallSBridgeCoreCertificate

/-- The endpoints on which `kAD`, `outerAD`, and `dArgAD` depend. -/
structure SKSlice where
  sLo : ℚ
  sHi : ℚ
  kLo : ℚ
  kHi : ℚ

/-- The endpoints on which `qChiAD` depends (apart from its log payload). -/
structure ChiSlice where
  lo : ℚ
  hi : ℚ

def SKSlice.ofBox (box : CertificateBox) : SKSlice :=
  { sLo := box.sLo, sHi := box.sHi, kLo := box.kLo, kHi := box.kHi }

def ChiSlice.ofBox (box : CertificateBox) : ChiSlice :=
  { lo := box.chiLo, hi := box.chiHi }

namespace SKSlice

def sAD (slice : SKSlice) : IntervalAD :=
  IntervalAD.variableS ⟨slice.sLo, slice.sHi⟩

def kAD (slice : SKSlice) : IntervalAD :=
  IntervalAD.variableK ⟨slice.kLo, slice.kHi⟩

def rAD (slice : SKSlice) : IntervalAD :=
  IntervalAD.sub (IntervalAD.const 1) slice.sAD

def outerAD (slice : SKSlice) : IntervalAD :=
  IntervalAD.add (IntervalAD.const 1)
    (IntervalAD.mul slice.rAD slice.kAD)

def dArgAD (slice : SKSlice) : IntervalAD :=
  IntervalAD.divPositive slice.outerAD slice.kAD

end SKSlice

namespace ChiSlice

def chiAD (slice : ChiSlice) : IntervalAD :=
  IntervalAD.variableChi ⟨slice.lo, slice.hi⟩

def onePlusAD (slice : ChiSlice) : IntervalAD :=
  IntervalAD.add (IntervalAD.const 1) slice.chiAD

def qChiEndpointRawAD (terms : ℕ) (slice : ChiSlice)
    (logChi : RationalEnclosure.LogIntervalCertificate) : IntervalAD :=
  let hi := IntervalAD.const slice.hi
  if slice.hi = 0 then IntervalAD.const 0
  else IntervalAD.divPositive
    (IntervalAD.mul hi (IntervalAD.log terms logChi hi))
    (IntervalAD.add (IntervalAD.const 1) hi)

def qChiEndpointAD (terms : ℕ) (slice : ChiSlice)
    (logChi : RationalEnclosure.LogIntervalCertificate) : IntervalAD where
  value := ⟨(slice.qChiEndpointRawAD terms logChi).value.lower, 0⟩
  derivS := RationalEnclosure.point 0
  derivK := RationalEnclosure.point 0
  derivChi := RationalEnclosure.point 0

def qChiAD (terms : ℕ) (slice : ChiSlice)
    (logChi : RationalEnclosure.LogIntervalCertificate) : IntervalAD :=
  if slice.lo = 0 then slice.qChiEndpointAD terms logChi
  else
    IntervalAD.divPositive
      (IntervalAD.mul slice.chiAD
        (IntervalAD.log terms logChi slice.chiAD))
      slice.onePlusAD

end ChiSlice

/-! Definitional transports from a leaf box to its canonical slices. -/

@[simp] theorem sAD_eq_slice (box : CertificateBox) :
    LRSmallSBridgeCoreCertificate.sAD box = (SKSlice.ofBox box).sAD := by
  rfl

@[simp] theorem kAD_eq_slice (box : CertificateBox) :
    LRSmallSBridgeCoreCertificate.kAD box = (SKSlice.ofBox box).kAD := by
  rfl

@[simp] theorem rAD_eq_slice (box : CertificateBox) :
    LRSmallSBridgeCoreCertificate.rAD box = (SKSlice.ofBox box).rAD := by
  rfl

@[simp] theorem outerAD_eq_slice (box : CertificateBox) :
    LRSmallSBridgeCoreCertificate.outerAD box =
      (SKSlice.ofBox box).outerAD := by
  rfl

@[simp] theorem dArgAD_eq_slice (box : CertificateBox) :
    LRSmallSBridgeCoreCertificate.dArgAD box =
      (SKSlice.ofBox box).dArgAD := by
  rfl

@[simp] theorem chiAD_eq_slice (box : CertificateBox) :
    LRSmallSBridgeCoreCertificate.chiAD box =
      (ChiSlice.ofBox box).chiAD := by
  rfl

@[simp] theorem onePlusChiAD_eq_slice (box : CertificateBox) :
    LRSmallSBridgeCoreCertificate.onePlusChiAD box =
      (ChiSlice.ofBox box).onePlusAD := by
  rfl

@[simp] theorem qChiAD_eq_slice (terms : ℕ) (box : CertificateBox)
    (certificate : LRSmallSBridgeCoreCertificate) :
    LRSmallSBridgeCoreCertificate.qChiAD terms box certificate =
      (ChiSlice.ofBox box).qChiAD terms certificate.logChi := by
  rfl

/-! Endpoint-equality versions are convenient for generated cache lookups:
the only per-leaf proof is equality of four or two rational endpoints. -/

theorem kAD_eq_of_slice_eq {box : CertificateBox} {slice : SKSlice}
    (h : SKSlice.ofBox box = slice) :
    LRSmallSBridgeCoreCertificate.kAD box = slice.kAD := by
  rw [kAD_eq_slice, h]

theorem outerAD_eq_of_slice_eq {box : CertificateBox} {slice : SKSlice}
    (h : SKSlice.ofBox box = slice) :
    LRSmallSBridgeCoreCertificate.outerAD box = slice.outerAD := by
  rw [outerAD_eq_slice, h]

theorem dArgAD_eq_of_slice_eq {box : CertificateBox} {slice : SKSlice}
    (h : SKSlice.ofBox box = slice) :
    LRSmallSBridgeCoreCertificate.dArgAD box = slice.dArgAD := by
  rw [dArgAD_eq_slice, h]

theorem qChiAD_eq_of_slice_eq
    {terms : ℕ} {box : CertificateBox}
    {certificate : LRSmallSBridgeCoreCertificate} {slice : ChiSlice}
    (h : ChiSlice.ofBox box = slice) :
    LRSmallSBridgeCoreCertificate.qChiAD terms box certificate =
      slice.qChiAD terms certificate.logChi := by
  rw [qChiAD_eq_slice, h]

end LRSmallSWideLogSharedSliceCore
end CourtadeKumar
