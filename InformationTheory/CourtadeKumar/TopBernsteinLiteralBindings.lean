import InformationTheory.CourtadeKumar.TopBernsteinFiniteDifferenceData
import InformationTheory.CourtadeKumar.TopCertificateData

/-!
# Kernel-checked literal bindings for the TOP Bernstein transform

This module isolates the expensive but purely finite equalities connecting the
integer replay tables to the production rational tables.  Keeping these checks
separate lets the generic forward-difference semantics rebuild without
re-running thousands of rational normalizations.
-/

namespace CourtadeKumar.TopBernsteinTransformBridge

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

def inputBindingEntry (i j : Nat) : Bool :=
  if hi : i < 48 then
    if hj : j < 61 then
      decide
        (((TopBernsteinFiniteDifferenceData.topScaledCoeff i j : Nat) : ℚ) =
          (TopBernsteinFiniteDifferenceData.commonDenominator : ℚ) *
            topElevatedBernsteinCoeff ⟨i, hi⟩ ⟨j, hj⟩)
    else false
  else false

def inputBindingCheck : Bool :=
  (List.range 48).all fun i =>
    (List.range 61).all fun j => inputBindingEntry i j

def outputBindingEntry (a b : Nat) : Bool :=
  if ha : a < 48 then
    if hb : b < 23 then
      decide
        (((TopBernsteinFiniteDifferenceData.scaledPowerCoeff a b : Int) : ℚ) =
          (TopBernsteinFiniteDifferenceData.commonDenominator : ℚ) *
            topCertificatePowerCoeffRat ⟨a, ha⟩ ⟨b, by omega⟩)
    else false
  else false

def outputBindingCheck : Bool :=
  (List.range 48).all fun a =>
    (List.range 23).all fun b => outputBindingEntry a b

/- Kernel authentication of the 2,928 scaled nonnegative input literals. -/
#kernel_checked_bool inputBinding_reduction inputBindingCheck

/- Kernel authentication of the 1,104 scaled signed output literals. -/
#kernel_checked_bool outputBinding_reduction outputBindingCheck

private theorem all_range_of_all_eq_true {n : Nat} {p : Nat → Bool}
    (h : (List.range n).all p = true) {i : Nat} (hi : i < n) :
    p i = true := by
  exact (List.all_eq_true.mp h) i (List.mem_range.mpr hi)

/-- Pointwise form of the checked input-table binding. -/
theorem topScaledCoeff_decode (i : Fin 48) (j : Fin 61) :
    (((TopBernsteinFiniteDifferenceData.topScaledCoeff i.val j.val : Nat) : ℚ) =
      (TopBernsteinFiniteDifferenceData.commonDenominator : ℚ) *
        topElevatedBernsteinCoeff i j) := by
  have hrow :
      (List.range 61).all (fun j => inputBindingEntry i.val j) = true :=
    all_range_of_all_eq_true (show
      (List.range 48).all (fun i =>
        (List.range 61).all fun j => inputBindingEntry i j) = true from
      inputBinding_reduction) i.isLt
  have hentry : inputBindingEntry i.val j.val = true :=
    all_range_of_all_eq_true hrow j.isLt
  simpa [inputBindingEntry, i.isLt, j.isLt] using hentry

/-- Pointwise form of the checked output-table binding. -/
theorem scaledPowerCoeff_decode (a : Fin 48) (b : Fin 23) :
    (((TopBernsteinFiniteDifferenceData.scaledPowerCoeff a.val b.val : Int) : ℚ) =
      (TopBernsteinFiniteDifferenceData.commonDenominator : ℚ) *
        topCertificatePowerCoeffRat a ⟨b.val, by omega⟩) := by
  have hrow :
      (List.range 23).all (fun b => outputBindingEntry a.val b) = true :=
    all_range_of_all_eq_true (show
      (List.range 48).all (fun a =>
        (List.range 23).all fun b => outputBindingEntry a b) = true from
      outputBinding_reduction) a.isLt
  have hentry : outputBindingEntry a.val b.val = true :=
    all_range_of_all_eq_true hrow b.isLt
  simpa [outputBindingEntry, a.isLt, b.isLt] using hentry

end CourtadeKumar.TopBernsteinTransformBridge
