import InformationTheory.CourtadeKumar.LRHighShapeVEvaluator

/-!
# A positive lower bound for the relevant high-shape k coordinate

The logarithmic `k = 0` face is not part of the positive-`J` branch.  More
precisely, expanding `J` in cancellation coordinates shows that `k ≤ s / 4`
forces `J ≤ 0`.  Thus every relevant interior point satisfies `s / 4 < k`.
On the post-small-`s` strip this gives the uniform rational cutoff
`1 / 65536 < k`, making the remaining replay domain compact and separated
from the logarithmic singularity.
-/

open Set

namespace CourtadeKumar

/-- Below the sloping face `k = s / 4`, the determinant coordinate `J` is
nonpositive. -/
theorem lrCertificateJ_nonpositive_of_k_le_quarter_s
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hk : point.k ≤ point.s / 4) :
    lrCertificateJ point ≤ 0 := by
  have hs := hinterior.1
  have he := hinterior.2.1
  have hchi := hinterior.2.2
  have hsPos : 0 < point.s := hs.1
  have hkPos : 0 < point.k := by
    have hproduct : 0 < point.s * point.k := by
      simpa [lrCertificateE] using he.1
    exact pos_of_mul_pos_left (by simpa [mul_comm] using hproduct) hsPos.le
  have hxPos : 0 < lrCertificateX point := by
    unfold lrCertificateX
    have hprod : point.chi * lrCertificateE point < 1 := by
      calc
        point.chi * lrCertificateE point < 1 * lrCertificateE point :=
          mul_lt_mul_of_pos_right hchi.2 he.1
        _ < 1 := by simpa using he.2
    linarith
  have hxLe : lrCertificateX point ≤ 1 := by
    unfold lrCertificateX
    exact sub_le_self _ (mul_nonneg hchi.1.le he.1.le)
  have hratioPos : 0 < (1 - lrCertificateE point) / lrCertificateX point :=
    div_pos (sub_pos.mpr he.2) hxPos
  have hvPos : 0 < lrCertificateV point := by
    unfold lrCertificateV
    exact Real.sqrt_pos.2 hratioPos
  have hratioLe :
      (1 - lrCertificateE point) / lrCertificateX point ≤ 1 := by
    rw [div_le_one hxPos]
    unfold lrCertificateX
    have hchiLe : point.chi ≤ 1 := hchi.2.le
    nlinarith [mul_nonneg (sub_nonneg.mpr hchiLe) he.1.le]
  have hvLe : lrCertificateV point ≤ 1 := by
    unfold lrCertificateV
    rw [Real.sqrt_le_one]
    exact hratioLe
  have hlogOneVNonneg : 0 ≤ Real.log (1 + lrCertificateV point) :=
    Real.log_nonneg (by linarith [hvPos])
  have hlogOneVUpper : Real.log (1 + lrCertificateV point) ≤ Real.log 2 :=
    Real.log_le_log (by linarith [hvPos]) (by linarith [hvLe])
  have hbMem := lrCertificateB_mem_Ioo hs he
  have hsLeB : point.s ≤ lrCertificateB point.s (lrCertificateE point) := by
    unfold lrCertificateB
    exact le_add_of_nonneg_right
      (mul_nonneg (sub_nonneg.mpr hs.2.le) he.1.le)
  have hlogSLeB : Real.log point.s ≤
      Real.log (lrCertificateB point.s (lrCertificateE point)) :=
    Real.log_le_log hsPos hsLeB
  have hlogBNonpos :
      Real.log (lrCertificateB point.s (lrCertificateE point)) ≤ 0 := by
    simpa using Real.log_nonpos hbMem.1.le hbMem.2.le
  have hxLog : lrCertificateX point *
      Real.log (1 + lrCertificateV point) ≤ Real.log 2 := by
    calc
      lrCertificateX point * Real.log (1 + lrCertificateV point) ≤
          1 * Real.log (1 + lrCertificateV point) :=
        mul_le_mul_of_nonneg_right hxLe hlogOneVNonneg
      _ ≤ Real.log 2 := by simpa using hlogOneVUpper
  have hcoeff : (1 + lrCertificateX point) / 2 ≤ 1 := by
    linarith
  have hlogBTerm :
      -((1 + lrCertificateX point) / 2) *
          Real.log (lrCertificateB point.s (lrCertificateE point)) ≤
        -Real.log point.s := by
    have hscale :
        -((1 + lrCertificateX point) / 2) *
            Real.log (lrCertificateB point.s (lrCertificateE point)) ≤
          -Real.log (lrCertificateB point.s (lrCertificateE point)) := by
      have hneg : 0 ≤ -Real.log
          (lrCertificateB point.s (lrCertificateE point)) :=
        neg_nonneg.mpr hlogBNonpos
      nlinarith
    linarith
  have heBound : 4 * lrCertificateE point ≤ point.s ^ 2 := by
    unfold lrCertificateE
    nlinarith
  have hfourEPos : 0 < 4 * lrCertificateE point :=
    mul_pos (by norm_num) he.1
  have hlogEK : Real.log (4 * lrCertificateE point) ≤
      Real.log (point.s ^ 2) := Real.log_le_log hfourEPos heBound
  have hlogCore :
      Real.log 2 + (1 / 2 : ℝ) * Real.log (lrCertificateE point) -
          Real.log point.s ≤ 0 := by
    rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) he.1.ne',
      show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow,
      Real.log_pow] at hlogEK
    norm_num at hlogEK ⊢
    linarith
  have hJExpansion : lrCertificateJ point =
      lrCertificateX point * Real.log (1 + lrCertificateV point) +
        (1 / 2 : ℝ) * Real.log (lrCertificateE point) -
        ((1 + lrCertificateX point) / 2) *
          Real.log (lrCertificateB point.s (lrCertificateE point)) := by
    unfold lrCertificateJ lrCertificateD lrCertificateA lrCertificateAValue
      lrCertificateBFlow lrCertificateBFlowValue
    ring
  rw [hJExpansion]
  linarith

/-- Positive `J` excludes the logarithmically singular `k = 0` face. -/
theorem lrCertificate_k_gt_quarter_s_of_relevant
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hrelevant : LRHighShapeVRelevant point) :
    point.s / 4 < point.k := by
  by_contra h
  have hk : point.k ≤ point.s / 4 := le_of_not_gt h
  have hJ := lrCertificateJ_nonpositive_of_k_le_quarter_s hinterior hk
  exact (not_lt_of_ge hJ) hrelevant.2

/-- Uniform lower cutoff on the bounded strip left after the small-`s`
bridge. -/
theorem lrCertificate_k_gt_one_div_65536_of_postSmallS_relevant
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hrelevant : LRHighShapeVRelevant point)
    (hs : 1 / 16384 < point.s) :
    1 / 65536 < point.k := by
  have hk := lrCertificate_k_gt_quarter_s_of_relevant hinterior hrelevant
  norm_num at hs hk ⊢
  linarith

end CourtadeKumar
