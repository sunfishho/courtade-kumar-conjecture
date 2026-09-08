import InformationTheory.CourtadeKumar.LRCompactVSoundLedger

/-!
# Reusing proved compact-V boxes in the remaining ledger

A partial cover records soundness on an explicit list of rational boxes.
The residual ledger asks for the original compact-V inequality only outside
those boxes. Combining the two recovers the unchanged full ledger interface.
The boxes may overlap, and their soundness may come from different checkers.
-/

namespace CourtadeKumar

/-- Soundness on one closed compact-coordinate box, restricted to physical
interior points as in the production certificate interface. -/
def LRCompactVBoxSound (box : CertificateBox) : Prop :=
  ∀ point, box.Contains point → LRCompactVPhysical point →
    0 ≤ lrCompactVReserveTarget point

/-- Join two proved children without replaying any certificate arithmetic. -/
theorem LRCompactVBoxSound.join {box : CertificateBox}
    (axis : CertificateAxis) (cut : ℚ)
    (lower : LRCompactVBoxSound (box.lower axis cut))
    (upper : LRCompactVBoxSound (box.upper axis cut)) :
    LRCompactVBoxSound box := by
  intro point hpoint hphysical
  rcases box.contains_lower_or_upper hpoint axis cut with hlo | hhi
  · exact lower point hlo hphysical
  · exact upper point hhi hphysical

/-- Every listed box carries a proof for the actual compact-V reserve. -/
def LRCompactVPartialCover (boxes : List CertificateBox) : Prop :=
  ∀ box ∈ boxes, LRCompactVBoxSound box

theorem LRCompactVPartialCover.append {left right : List CertificateBox}
    (hleft : LRCompactVPartialCover left)
    (hright : LRCompactVPartialCover right) :
    LRCompactVPartialCover (left ++ right) := by
  intro box hbox
  rcases List.mem_append.mp hbox with hbox | hbox
  · exact hleft box hbox
  · exact hright box hbox

/-- The exact portion of the original ledger outside a proved partial cover.
No conclusion is assumed inside any listed box. -/
structure LRCompactVResidualLedger (boxes : List CertificateBox) : Prop where
  v_nonnegative :
    ∀ (R v t : ℝ),
      R ∈ Set.Ioo (0 : ℝ) 1 → R ≤ 9 / 10 →
      v ∈ Set.Ioo (0 : ℝ) 1 → 1 / 3 ≤ v →
      t ∈ Set.Ioo (0 : ℝ) 1 → 17 / 20 ≤ t ^ 2 →
      0 < lrFlowJ R v t →
      (∀ box ∈ boxes, ¬ box.Contains (lrCompactVFlowPoint R v t)) →
      0 ≤ lrLowVReserve R v t

/-- Checked coverage and the explicitly remaining region recover the full
compact-V premise used by the Courtade-Kumar assembly. -/
theorem LRCompactVSoundLedger.of_partialCover {boxes : List CertificateBox}
    (cover : LRCompactVPartialCover boxes)
    (remaining : LRCompactVResidualLedger boxes) : LRCompactVSoundLedger := by
  classical
  constructor
  intro R v t hR hRhi hv hvlo ht htsq hJ
  by_cases hcovered : ∃ box ∈ boxes,
      box.Contains (lrCompactVFlowPoint R v t)
  · obtain ⟨box, hbox, hpoint⟩ := hcovered
    have hreserve := cover box hbox _ hpoint
      (lrCompactVFlowPoint_physical hR hv ht hJ)
    simpa only [lrCompactVReserveTarget_flow ht.1] using hreserve
  · apply remaining.v_nonnegative R v t hR hRhi hv hvlo ht htsq hJ
    intro box hbox hpoint
    exact hcovered ⟨box, hbox, hpoint⟩

end CourtadeKumar
