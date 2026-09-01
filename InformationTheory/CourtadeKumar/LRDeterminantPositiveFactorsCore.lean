import InformationTheory.CourtadeKumar.LRDeterminantFlowCoordinates

/-!
# Lightweight positive factors for finite determinant replay

The raw D9 sign adapter needs only positivity of the exact scale
`3 * s * H_d`.  Its proof is independent of the low-shape tail bounds used
by the later determinant coefficient analysis, so it lives in this small
core module.
-/

open Set

namespace CourtadeKumar

theorem lrCertificateV_mem_Ioo {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point) :
    lrCertificateV point ∈ Ioo (0 : ℝ) 1 := by
  have he := hinterior.2.1
  have hchi := hinterior.2.2
  have hxPos : 0 < lrCertificateX point := by
    unfold lrCertificateX
    have hprodLt : point.chi * lrCertificateE point < 1 := by
      calc
        point.chi * lrCertificateE point < 1 * lrCertificateE point :=
          mul_lt_mul_of_pos_right hchi.2 he.1
        _ < 1 := by simpa using he.2
    linarith
  have hnumLt : 1 - lrCertificateE point < lrCertificateX point := by
    unfold lrCertificateX
    have hscaled := mul_lt_mul_of_pos_right hchi.2 he.1
    nlinarith
  have hrad : (1 - lrCertificateE point) / lrCertificateX point ∈
      Ioo (0 : ℝ) 1 := by
    constructor
    · exact div_pos (sub_pos.mpr he.2) hxPos
    · rw [div_lt_one hxPos]
      exact hnumLt
  have hvPos : 0 < lrCertificateV point := by
    unfold lrCertificateV
    exact Real.sqrt_pos.2 hrad.1
  have hvSq : lrCertificateV point ^ 2 =
      (1 - lrCertificateE point) / lrCertificateX point := by
    exact Real.sq_sqrt hrad.1.le
  exact ⟨hvPos, by nlinarith [hvSq, hrad.2]⟩

theorem lrCertificateHalfSlope_pos {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point) :
    0 < lrCertificateHalfSlope point := by
  have hR : lrCertificateR point ∈ Ioo (0 : ℝ) 1 := by
    unfold lrCertificateR
    constructor <;> linarith [hinterior.1.1, hinterior.1.2]
  have hv := lrCertificateV_mem_Ioo hinterior
  rw [lrCertificateHalfSlope_eq_flow hinterior.1 hinterior.2.1
    ⟨hinterior.2.2.1.le, hinterior.2.2.2.le⟩]
  exact lrFlowHalfSlope_pos hR hv

theorem lrDeterminantHd_pos {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point) :
    0 < lrDeterminantHd point := by
  unfold lrDeterminantHd
  exact div_pos (lrCertificateHalfSlope_pos hinterior) hinterior.1.1

end CourtadeKumar
