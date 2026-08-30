import InformationTheory.CourtadeKumar.IntervalSubdivisionCertificate

/-!
# Lightweight outer-containment relation for rational enclosures

This scalar relation is shared by point certificates, dyadic rounding, and
the full midpoint evaluator.  It lives separately so arithmetic-only point
proofs do not import the historical interval-AD evaluator stack.
-/

namespace CourtadeKumar
namespace LRUpperKMidpointCoarsening

/-- `outer` contains every real number contained by `inner`. -/
def Covers (outer inner : RationalEnclosure) : Prop :=
  outer.lower ≤ inner.lower ∧ inner.upper ≤ outer.upper

theorem contains_of_covers {outer inner : RationalEnclosure} {x : ℝ}
    (hcovers : Covers outer inner) (hinner : inner.Contains x) :
    outer.Contains x := by
  constructor
  · exact le_trans (by exact_mod_cast hcovers.1) hinner.1
  · exact le_trans hinner.2 (by exact_mod_cast hcovers.2)

end LRUpperKMidpointCoarsening
end CourtadeKumar
