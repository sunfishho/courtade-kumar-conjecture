import InformationTheory.CourtadeKumar.IntervalSubdivisionCertificate
import InformationTheory.CourtadeKumar.LRPositiveChartAssembly

/-!
# Cancellation coordinates for the high-shape LR certificates

This file fixes the exact map between the certificate variables `(s,k,χ)`
and the LR flow variables `(R,v,t)`.  The inverse identities ensure that the
finite checker proves the already-defined analytic reserves rather than a
parallel surrogate expression.
-/

open Set

namespace CourtadeKumar

def lrCertificateE (point : CertificatePoint) : ℝ :=
  point.s * point.k

def lrCertificateX (point : CertificatePoint) : ℝ :=
  1 - point.chi * lrCertificateE point

def lrCertificateR (point : CertificatePoint) : ℝ :=
  1 - point.s

noncomputable def lrCertificateT (point : CertificatePoint) : ℝ :=
  Real.sqrt (lrCertificateX point)

noncomputable def lrCertificateV (point : CertificatePoint) : ℝ :=
  Real.sqrt ((1 - lrCertificateE point) / lrCertificateX point)

/-- The midpoint target in the exact normalization used by the replay. -/
noncomputable def lrHighShapeUCertificateTarget
    (point : CertificatePoint) : ℝ :=
  lrFlowNumeratorP (lrCertificateR point)
      (lrFlowM (lrCertificateV point) / 2)
      (lrCertificateV point) (lrCertificateT point) /
    (point.s * lrCertificateE point)

/-- The tangent target expressed through the same flow reserve as the final
positive-chart theorem. -/
noncomputable def lrHighShapeTCertificateTarget
    (point : CertificatePoint) : ℝ :=
  lrFlowTReserve (lrCertificateR point) (lrCertificateV point)
    (lrCertificateT point)

/-- Convert an interior LR flow point to the cancellation coordinates. -/
noncomputable def lrFlowCertificatePoint (R v t : ℝ) : CertificatePoint where
  s := 1 - R
  k := (1 - v ^ 2 * t ^ 2) / (1 - R)
  chi := (1 - t ^ 2) / (1 - v ^ 2 * t ^ 2)

lemma lrCertificateR_flow (R v t : ℝ) :
    lrCertificateR (lrFlowCertificatePoint R v t) = R := by
  unfold lrCertificateR lrFlowCertificatePoint
  ring

lemma lrCertificateE_flow {R v t : ℝ} (hR : R ≠ 1) :
    lrCertificateE (lrFlowCertificatePoint R v t) =
      1 - v ^ 2 * t ^ 2 := by
  unfold lrCertificateE lrFlowCertificatePoint
  have hden : 1 - R ≠ 0 := sub_ne_zero.mpr hR.symm
  field_simp [hden]

lemma lrCertificateX_flow {R v t : ℝ}
    (hR : R ≠ 1) (he : 1 - v ^ 2 * t ^ 2 ≠ 0) :
    lrCertificateX (lrFlowCertificatePoint R v t) = t ^ 2 := by
  unfold lrCertificateX
  rw [lrCertificateE_flow hR]
  unfold lrFlowCertificatePoint
  have he' : 1 - t ^ 2 * v ^ 2 ≠ 0 := by
    simpa [mul_comm] using he
  field_simp [he, he']
  ring

lemma lrCertificateT_flow {R v t : ℝ}
    (hR : R ≠ 1) (he : 1 - v ^ 2 * t ^ 2 ≠ 0) (ht : 0 < t) :
    lrCertificateT (lrFlowCertificatePoint R v t) = t := by
  unfold lrCertificateT
  rw [lrCertificateX_flow hR he, Real.sqrt_sq_eq_abs, abs_of_pos ht]

lemma lrCertificateV_flow {R v t : ℝ}
    (hR : R ≠ 1) (he : 1 - v ^ 2 * t ^ 2 ≠ 0)
    (hv : 0 < v) (ht : 0 < t) :
    lrCertificateV (lrFlowCertificatePoint R v t) = v := by
  unfold lrCertificateV
  rw [lrCertificateE_flow hR, lrCertificateX_flow hR he]
  have htNe : t ^ 2 ≠ 0 := pow_ne_zero 2 ht.ne'
  have hratio : (1 - (1 - v ^ 2 * t ^ 2)) / t ^ 2 = v ^ 2 := by
    field_simp [htNe]
    ring
  rw [hratio, Real.sqrt_sq_eq_abs, abs_of_pos hv]

lemma lrHighShapeUCertificateTarget_flow
    {R v t : ℝ} (hR : R ≠ 1) (he : 1 - v ^ 2 * t ^ 2 ≠ 0)
    (hv : 0 < v) (ht : 0 < t) :
    lrHighShapeUCertificateTarget (lrFlowCertificatePoint R v t) =
      lrFlowNumeratorP R (lrFlowM v / 2) v t /
        ((1 - R) * (1 - v ^ 2 * t ^ 2)) := by
  unfold lrHighShapeUCertificateTarget
  rw [lrCertificateR_flow, lrCertificateV_flow hR he hv ht,
    lrCertificateT_flow hR he ht, lrCertificateE_flow hR]
  rfl

lemma lrHighShapeTCertificateTarget_flow
    {R v t : ℝ} (hR : R ≠ 1) (he : 1 - v ^ 2 * t ^ 2 ≠ 0)
    (hv : 0 < v) (ht : 0 < t) :
    lrHighShapeTCertificateTarget (lrFlowCertificatePoint R v t) =
      lrFlowTReserve R v t := by
  unfold lrHighShapeTCertificateTarget
  rw [lrCertificateR_flow, lrCertificateV_flow hR he hv ht,
    lrCertificateT_flow hR he ht]

theorem lrFlowHalfMidpoint_nonneg_of_certificateTarget
    {R v t : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1) (hv : 0 < v) (ht : 0 < t)
    (he : 0 < 1 - v ^ 2 * t ^ 2)
    (htarget : 0 ≤
      lrHighShapeUCertificateTarget (lrFlowCertificatePoint R v t)) :
    0 ≤ lrFlowNumeratorP R (lrFlowM v / 2) v t := by
  have hRNe : R ≠ 1 := hR.2.ne
  have heNe : 1 - v ^ 2 * t ^ 2 ≠ 0 := he.ne'
  rw [lrHighShapeUCertificateTarget_flow hRNe heNe hv ht] at htarget
  have hden : 0 < (1 - R) * (1 - v ^ 2 * t ^ 2) :=
    mul_pos (sub_pos.mpr hR.2) he
  have hmul := mul_nonneg htarget hden.le
  rw [div_mul_cancel₀ _ hden.ne'] at hmul
  exact hmul

end CourtadeKumar
