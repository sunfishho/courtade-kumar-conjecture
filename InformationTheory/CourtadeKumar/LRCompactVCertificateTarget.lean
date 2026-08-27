import InformationTheory.CourtadeKumar.LRCompactVSeries
import InformationTheory.CourtadeKumar.IntervalCertificateAssembly

/-!
# Certificate target for the compact high-shape `V` chart

The generic subdivision engine uses `CertificatePoint`; in this module its
three coordinates are interpreted as `(R,v,x)`, where `x=t²`.  Accepted
leaves prove the finite structured lower expression.  The series theorem
then transports that result to the actual analytic reserve `V`.
-/

open Set

namespace CourtadeKumar

/-- Interior of the compact `(R,v,x)` chart. -/
def LRCompactVInterior (point : CertificatePoint) : Prop :=
  point.s ∈ Ioo (0 : ℝ) 1 ∧
    point.k ∈ Ioo (0 : ℝ) 1 ∧
    point.chi ∈ Ioo (0 : ℝ) 1

/-- The finite exact expression to be enclosed at a compact certificate
leaf.  The field names are inherited from the generic three-dimensional
subdivision engine: `s=R`, `k=v`, and `chi=x`. -/
noncomputable def lrCompactVCertificateTarget
    (N : ℕ) (point : CertificatePoint) : ℝ :=
  lrCompactVFiniteLower N point.s point.k (Real.sqrt point.chi)

/-- The actual reserve represented by a compact certificate point. -/
noncomputable def lrCompactVReserveTarget
    (point : CertificatePoint) : ℝ :=
  lrLowVReserve point.s point.k (Real.sqrt point.chi)

theorem lrCompactVReserveTarget_nonneg_of_certificateTarget
    {N : ℕ} {point : CertificatePoint}
    (hpoint : LRCompactVInterior point)
    (htarget : 0 ≤ lrCompactVCertificateTarget N point) :
    0 ≤ lrCompactVReserveTarget point := by
  rcases hpoint with ⟨hR, hv, hx⟩
  have hsqrt : Real.sqrt point.chi ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · exact Real.sqrt_pos.2 hx.1
    · simpa using (Real.sqrt_lt_sqrt_iff hx.1.le).2 hx.2
  exact lrLowVReserve_nonneg_of_compact_finiteLower hR hv hsqrt N htarget

/-- Embed an analytic flow point in the compact certificate chart. -/
def lrCompactVFlowPoint (R v t : ℝ) : CertificatePoint where
  s := R
  k := v
  chi := t ^ 2

@[simp] theorem lrCompactVFlowPoint_s (R v t : ℝ) :
    (lrCompactVFlowPoint R v t).s = R := rfl

@[simp] theorem lrCompactVFlowPoint_k (R v t : ℝ) :
    (lrCompactVFlowPoint R v t).k = v := rfl

@[simp] theorem lrCompactVFlowPoint_chi (R v t : ℝ) :
    (lrCompactVFlowPoint R v t).chi = t ^ 2 := rfl

theorem lrCompactVFlowPoint_interior
    {R v t : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1)
    (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    LRCompactVInterior (lrCompactVFlowPoint R v t) := by
  refine ⟨hR, hv, ?_⟩
  constructor
  · change 0 < t ^ 2
    exact sq_pos_of_pos ht.1
  · change t ^ 2 < 1
    nlinarith [sq_nonneg t, mul_pos ht.1 (sub_pos.mpr ht.2)]

theorem lrCompactVReserveTarget_flow
    {R v t : ℝ} (ht : 0 < t) :
    lrCompactVReserveTarget (lrCompactVFlowPoint R v t) =
      lrLowVReserve R v t := by
  unfold lrCompactVReserveTarget lrCompactVFlowPoint
  rw [Real.sqrt_sq_eq_abs, abs_of_pos ht]

theorem lrCompactVCertificateTarget_flow
    {N : ℕ} {R v t : ℝ} (ht : 0 < t) :
    lrCompactVCertificateTarget N (lrCompactVFlowPoint R v t) =
      lrCompactVFiniteLower N R v t := by
  unfold lrCompactVCertificateTarget lrCompactVFlowPoint
  rw [Real.sqrt_sq_eq_abs, abs_of_pos ht]

/-- End-to-end soundness for any checked compact subdivision evaluator.
The concrete arithmetic evaluator can use any payload representation; only
its kernel-proved enclosure contract and successful Boolean traversal enter
this theorem. -/
theorem lrCompactVSubdivisionCertificate_nonnegative
    {N : ℕ} {Relevant : CertificatePoint → Prop}
    {AcceptData DiscardData : Type}
    {payloadCheck : CertificateBox → AcceptData → Bool}
    {enclose : CertificateBox → AcceptData → RationalEnclosure}
    {discardBox : CertificateBox → DiscardData → Bool}
    (hrelevant : ∀ point, Relevant point → LRCompactVInterior point)
    (encloseSound : CheckedEnclosureLeafEvaluatorSound
      (lrCompactVCertificateTarget N) payloadCheck enclose)
    (discardSound : ∀ box data, discardBox box data = true →
      ∀ point, box.Contains point → ¬ Relevant point)
    {box : CertificateBox}
    {certificate : SubdivisionCertificate AcceptData DiscardData}
    (hcheck : certificate.check
      (checkedEnclosureLeafAccepts payloadCheck enclose)
      discardBox box = true) :
    ∀ point, box.Contains point → Relevant point →
      0 ≤ lrCompactVReserveTarget point := by
  have hfinite := subdivisionCertificate_nonnegative_checkedEnclosure
    encloseSound discardSound hcheck
  intro point hpoint hrel
  exact lrCompactVReserveTarget_nonneg_of_certificateTarget
    (hrelevant point hrel) (hfinite point hpoint hrel)

end CourtadeKumar
