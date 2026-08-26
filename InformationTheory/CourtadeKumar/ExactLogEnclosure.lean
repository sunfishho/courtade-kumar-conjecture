import InformationTheory.CourtadeKumar.ExactIntervalArithmetic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Exact rational enclosures for logarithms

The interval verifier reduces logarithms to

`(1 / 2) * log ((1 + q) / (1 - q))`

with `0 ≤ q < 1`.  Mathlib's proved positive-series bounds turn a finite
rational sum and rational geometric tail into a kernel-checked enclosure.
-/

open Finset

namespace CourtadeKumar
namespace RationalEnclosure

/-- The first `n` positive terms of the odd logarithm series. -/
def atanhPartial (n : ℕ) (q : ℚ) : ℚ :=
  ∑ i ∈ range n, q ^ (2 * i + 1) / (2 * i + 1)

/-- A geometric upper bound for the omitted positive tail. -/
def atanhTail (n : ℕ) (q : ℚ) : ℚ :=
  q ^ (2 * n + 1) / (1 - q ^ 2)

/-- Exact rational enclosure for the half-log ratio. -/
def halfLogRatioEnclosure (n : ℕ) (q : ℚ) : RationalEnclosure :=
  ⟨atanhPartial n q, atanhPartial n q + atanhTail n q⟩

theorem contains_halfLogRatioEnclosure
    (n : ℕ) {q : ℚ} (hq0 : (0 : ℚ) ≤ q) (hq1 : q < 1) :
    (halfLogRatioEnclosure n q).Contains
      (1 / 2 * Real.log ((1 + (q : ℝ)) / (1 - (q : ℝ)))) := by
  have hq0Real : (0 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq0
  have hq1Real : (q : ℝ) < 1 := by exact_mod_cast hq1
  have hlower := Real.sum_range_le_log_div hq0Real hq1Real n
  have hupper := Real.log_div_le_sum_range_add hq0Real hq1Real n
  constructor
  · simpa [halfLogRatioEnclosure, atanhPartial, Contains] using hlower
  · simpa [halfLogRatioEnclosure, atanhPartial, atanhTail, Contains] using hupper

/-- The standard range-reduction coordinate `q=(r-1)/(r+1)`. -/
def logRatioCoordinate (r : ℚ) : ℚ :=
  (r - 1) / (r + 1)

/-- Enclose `log r` for a positive rational mantissa `1 ≤ r`. -/
def logMantissaEnclosure (n : ℕ) (r : ℚ) : RationalEnclosure :=
  scale 2 (halfLogRatioEnclosure n (logRatioCoordinate r))

theorem contains_logMantissaEnclosure
    (n : ℕ) {r : ℚ} (hr : (1 : ℚ) ≤ r) :
    (logMantissaEnclosure n r).Contains (Real.log (r : ℝ)) := by
  have hrPos : (0 : ℚ) < r := zero_lt_one.trans_le hr
  have hrPlus : (0 : ℚ) < r + 1 := by linarith
  have hq0 : (0 : ℚ) ≤ logRatioCoordinate r := by
    exact div_nonneg (sub_nonneg.mpr hr) hrPlus.le
  have hq1 : logRatioCoordinate r < 1 := by
    rw [logRatioCoordinate, div_lt_one hrPlus]
    linarith
  have hratio :
      ((1 + (logRatioCoordinate r : ℚ)) /
        (1 - logRatioCoordinate r) : ℚ) = r := by
    rw [logRatioCoordinate]
    field_simp
    ring
  have hcontains := contains_scale (2 : ℚ)
    (contains_halfLogRatioEnclosure n hq0 hq1)
  have hratioReal :
      (1 + (logRatioCoordinate r : ℝ)) /
        (1 - (logRatioCoordinate r : ℝ)) = (r : ℝ) := by
    exact_mod_cast hratio
  simpa [logMantissaEnclosure, hratioReal] using hcontains

end RationalEnclosure
end CourtadeKumar
