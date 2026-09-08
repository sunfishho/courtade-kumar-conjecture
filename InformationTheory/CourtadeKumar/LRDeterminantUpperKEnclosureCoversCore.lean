import InformationTheory.CourtadeKumar.RationalEnclosureCore

/-!
# Executable outer-containment relation for rational enclosures
-/

namespace CourtadeKumar
namespace LRUpperKMidpointCoarsening

/-- `outer` contains every endpoint interval represented by `inner`. -/
def Covers (outer inner : RationalEnclosure) : Prop :=
  outer.lower ≤ inner.lower ∧ inner.upper ≤ outer.upper

end LRUpperKMidpointCoarsening
end CourtadeKumar
