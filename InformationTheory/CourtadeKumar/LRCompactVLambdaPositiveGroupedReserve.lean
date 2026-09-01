import InformationTheory.CourtadeKumar.LRCompactVLambdaPositiveGroupedCore
import InformationTheory.CourtadeKumar.LRCompactVPhysicalDiscard

/-!
# Reserve bridge for a checked positive grouped minorant

This module factors the analytic end of a compact-`V` grouped leaf away from
its arithmetic evaluator.  Once a nonnegative multiplier satisfies
`lambda * B ≤ D` and the corresponding grouped expression is nonnegative,
the reserve target is nonnegative.  Generated fixed-dyadic leaves can
therefore authenticate only their scalar observations; this proof is shared
once by the semantic assembly.
-/

set_option autoImplicit false

open Set

namespace CourtadeKumar

/-- The final grouped reserve argument, assuming the nonnegative augmented
`PW + lambda*C` expression and the budget `lambda*B ≤ D`. -/
theorem lrCompactVReserveTarget_nonneg_of_lambda_budget
    {point : CertificatePoint} (hphysical : LRCompactVPhysical point)
    (lambda : ℝ)
    (hQlambda :
      let t := Real.sqrt point.chi
      0 ≤
        (lrFlowPW point.s point.k t -
          4 * lrWKernel point.s 1 *
            (point.k * t ^ 2 / (1 + point.k))) +
          lambda * lrFlowC point.s point.k t)
    (hlambdaB :
      let t := Real.sqrt point.chi
      lambda * lrFlowB point.s point.k t ≤
        lrFlowD point.s point.k t) :
    0 ≤ lrCompactVReserveTarget point := by
  have hinterior := hphysical.1
  let t := Real.sqrt point.chi
  have ht : t ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · exact Real.sqrt_pos.2 hinterior.2.2.1
    · simpa [t] using
        (Real.sqrt_lt_sqrt_iff hinterior.2.2.1.le).2
          hinterior.2.2.2
  have hBPos : 0 < lrFlowB point.s point.k t := by
    apply lrFlowB_pos hinterior.2.1.1 ht.1.le
    have hsqrtR : Real.sqrt point.s < 1 := by
      simpa using (Real.sqrt_lt_sqrt_iff hinterior.1.1.le).2
        hinterior.1.2
    calc
      Real.sqrt point.s * point.k * t < 1 * point.k * t := by
        exact mul_lt_mul_of_pos_right
          (mul_lt_mul_of_pos_right hsqrtR hinterior.2.1.1) ht.1
      _ < 1 := by
        have := mul_lt_mul_of_pos_right hinterior.2.1.2 ht.1
        nlinarith [ht.2]
  have hC0 := lrFlowC_nonneg_of_compact_series
    hinterior.1 hinterior.2.1 ht
  have htotal :
      0 ≤
        lrFlowB point.s point.k t *
          (lrFlowPW point.s point.k t -
            4 * lrWKernel point.s 1 *
              (point.k * t ^ 2 / (1 + point.k))) +
        lrFlowD point.s point.k t *
          lrFlowC point.s point.k t := by
    calc
      0 ≤
          lrFlowB point.s point.k t *
              ((lrFlowPW point.s point.k t -
                4 * lrWKernel point.s 1 *
                  (point.k * t ^ 2 / (1 + point.k))) +
                lambda * lrFlowC point.s point.k t) +
            (lrFlowD point.s point.k t -
                lambda * lrFlowB point.s point.k t) *
              lrFlowC point.s point.k t :=
        add_nonneg
          (mul_nonneg hBPos.le (by simpa [t] using hQlambda))
          (mul_nonneg
            (sub_nonneg.mpr (by simpa [t] using hlambdaB)) hC0)
      _ =
          lrFlowB point.s point.k t *
            (lrFlowPW point.s point.k t -
              4 * lrWKernel point.s 1 *
                (point.k * t ^ 2 / (1 + point.k))) +
          lrFlowD point.s point.k t *
            lrFlowC point.s point.k t := by ring
  have hvNe : point.k ≠ -1 := by linarith [hinterior.2.1.1]
  rw [lrCompactVReserveTarget,
    lrLowVReserve_eq_compact_grouped hvNe]
  exact htotal

/-- A nonnegative positive-grouped finite minorant supplies the augmented
flow hypothesis needed by `lrCompactVReserveTarget_nonneg_of_lambda_budget`.
-/
theorem lrCompactVReserveTarget_nonneg_of_positiveGroupedFinite
    {point : CertificatePoint} (hphysical : LRCompactVPhysical point)
    {lambda : ℝ} (hlambda : 0 ≤ lambda) (N : ℕ)
    (hfinite :
      0 ≤ lrCompactVLambdaPositiveGroupedFinite
        N lambda point.s point.k point.chi)
    (hlambdaB :
      let t := Real.sqrt point.chi
      lambda * lrFlowB point.s point.k t ≤
        lrFlowD point.s point.k t) :
    0 ≤ lrCompactVReserveTarget point := by
  have hinterior := hphysical.1
  let t := Real.sqrt point.chi
  have ht : t ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · exact Real.sqrt_pos.2 hinterior.2.2.1
    · simpa [t] using
        (Real.sqrt_lt_sqrt_iff hinterior.2.2.1.le).2
          hinterior.2.2.2
  have hsquare : t ^ 2 = point.chi :=
    Real.sq_sqrt hinterior.2.2.1.le
  have hanalytic := lrCompactVLambdaPositiveGroupedFinite_le
    hinterior.1 hinterior.2.1 ht hlambda N
  have hQlambda :
      0 ≤
        (lrFlowPW point.s point.k t -
          4 * lrWKernel point.s 1 *
            (point.k * t ^ 2 / (1 + point.k))) +
          lambda * lrFlowC point.s point.k t := by
    exact hfinite.trans (by simpa [hsquare] using hanalytic)
  exact lrCompactVReserveTarget_nonneg_of_lambda_budget
    hphysical lambda (by simpa [t] using hQlambda) hlambdaB

end CourtadeKumar
