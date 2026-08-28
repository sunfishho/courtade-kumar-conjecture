import InformationTheory.CourtadeKumar.LRGapBudgetSETailAssembly

/-!
# A nonsingular endpoint minorant for the gap-budget derivative

The exact `e` derivative contains positive `Q'` terms that diverge as their
arguments approach zero.  A two-sided interval enclosure therefore cannot
cover a box touching the endpoint.  This file replaces those terms by the
universal lower bound `Q'(y) >= 1/2` and drops another nonnegative term.  The
resulting minorant is finite as `s,e,chi` approach zero and is suitable for
a separate closed-endpoint interval evaluator.
-/

open Set

namespace CourtadeKumar

/-- The endpoint-safe lower model for `partial_e lrGapBudgetSEChi`. -/
noncomputable def lrGapBudgetSEChiDerivEEndpointMinorant
    (s e chi : ℝ) : ℝ :=
  let x := 1 - chi * e
  let v := Real.sqrt ((1 - e) / x)
  let v' := (chi - 1) / (2 * v * x ^ 2)
  let logFactor := Real.log 2 + Real.log (1 + v) - Real.log (2 + v)
  let logFactor' := v' / (1 + v) - v' / (2 + v)
  let ratio := (1 + v) / v
  let ratio' := -v' / v ^ 2
  (1 - s) * lrCertificateG0Prime v * v' +
      (1 / 2 : ℝ) * (1 - s) * (chi + 1 / v) -
    s * (ratio' * (Real.log 2 + 2 * logFactor) +
      ratio * (2 * logFactor')) +
    2 * v' / (1 + v) ^ 2 *
      (lrCertificateQ s - s * Real.log 2)

/-- The elementary global lower bound used to remove the singular `Q'`
upper enclosure from the endpoint calculation. -/
lemma lrCertificateQPrime_half_le {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    (1 / 2 : ℝ) ≤ lrCertificateQPrime y := by
  let z := Real.sqrt (1 - y)
  have hzPos : 0 < z := Real.sqrt_pos.2 (sub_pos.mpr hy.2)
  have hzLt : z < 1 := by
    have harg : 1 - y ∈ Ioo (0 : ℝ) 1 := by
      constructor <;> linarith [hy.1, hy.2]
    simpa [z] using (Real.sqrt_lt_sqrt_iff harg.1.le).2 harg.2
  have hart : z ≤ Real.artanh z :=
    (self_lt_artanh ⟨hzPos, hzLt⟩).le
  rw [lrCertificateQPrime_eq]
  change (1 / 2 : ℝ) ≤ Real.artanh z / (2 * z)
  rw [le_div_iff₀ (by positivity : 0 < 2 * z)]
  linarith

/-- The endpoint model is a rigorous lower bound for the exact derivative
throughout the open physical cube. -/
theorem lrGapBudgetSEChiDerivEEndpointMinorant_le
    {s e chi : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1)
    (he : e ∈ Ioo (0 : ℝ) 1) (hchi : chi ∈ Ioo (0 : ℝ) 1) :
    lrGapBudgetSEChiDerivEEndpointMinorant s e chi ≤
      lrGapBudgetSEChiDerivE s e chi := by
  have hchiE : chi * e ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · exact mul_pos hchi.1 he.1
    · calc
        chi * e < 1 * e := mul_lt_mul_of_pos_right hchi.2 he.1
        _ = e := one_mul _
        _ < 1 := he.2
  have hby0 := lrCertificateB_mem_Ioo hs hchiE
  have hbe := lrCertificateB_mem_Ioo hs he
  have hqBy0 : (1 / 2 : ℝ) ≤
      lrCertificateQPrime (lrCertificateB s (chi * e)) :=
    lrCertificateQPrime_half_le hby0
  have hqBe : (1 / 2 : ℝ) ≤
      lrCertificateQPrime (lrCertificateB s e) :=
    lrCertificateQPrime_half_le hbe
  have hqBeNonneg : 0 ≤ lrCertificateQ (lrCertificateB s e) :=
    lrCertificateQ_nonneg ⟨hbe.1.le, hbe.2.le⟩
  set x : ℝ := 1 - chi * e with hxDef
  have hxPos : 0 < x := by
    rw [hxDef]
    exact sub_pos.mpr hchiE.2
  set v : ℝ := Real.sqrt ((1 - e) / x) with hvDef
  have hvPos : 0 < v := by
    rw [hvDef]
    exact Real.sqrt_pos.2 (div_pos (sub_pos.mpr he.2) hxPos)
  set v' : ℝ := (chi - 1) / (2 * v * x ^ 2) with hvPrimeDef
  have hvPrimeNonpos : v' ≤ 0 := by
    rw [hvPrimeDef]
    exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hchi.2.le)
      (mul_nonneg (mul_nonneg (by norm_num) hvPos.le) (sq_nonneg x))
  have hfirst : 0 ≤
      (lrCertificateQPrime (lrCertificateB s (chi * e)) - 1 / 2) *
        (1 - s) * chi := by
    exact mul_nonneg
      (mul_nonneg (sub_nonneg.mpr hqBy0) (sub_nonneg.mpr hs.2.le))
      hchi.1.le
  have hsecond : 0 ≤
      (lrCertificateQPrime (lrCertificateB s e) - 1 / 2) *
        (1 - s) / v := by
    exact div_nonneg
      (mul_nonneg (sub_nonneg.mpr hqBe) (sub_nonneg.mpr hs.2.le)) hvPos.le
  have hthird : 0 ≤
      -(lrCertificateQ (lrCertificateB s e) * v' / v ^ 2) := by
    exact neg_nonneg.mpr (div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos hqBeNonneg hvPrimeNonpos)
      (sq_nonneg v))
  have hidentity :
      lrGapBudgetSEChiDerivE s e chi -
          lrGapBudgetSEChiDerivEEndpointMinorant s e chi =
        (lrCertificateQPrime (lrCertificateB s (chi * e)) - 1 / 2) *
            (1 - s) * chi +
          (lrCertificateQPrime (lrCertificateB s e) - 1 / 2) *
            (1 - s) / v -
          lrCertificateQ (lrCertificateB s e) * v' / v ^ 2 := by
    unfold lrGapBudgetSEChiDerivE
      lrGapBudgetSEChiDerivEEndpointMinorant
    dsimp only
    rw [← hxDef, ← hvDef, ← hvPrimeDef]
    field_simp [hvPos.ne']
    ring
  rw [← sub_nonneg]
  rw [hidentity]
  exact add_nonneg (add_nonneg hfirst hsecond) hthird

theorem lrGapBudgetSEChiDerivE_nonnegative_of_endpointMinorant
    {s e chi : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1)
    (he : e ∈ Ioo (0 : ℝ) 1) (hchi : chi ∈ Ioo (0 : ℝ) 1)
    (hminorant : 0 ≤ lrGapBudgetSEChiDerivEEndpointMinorant s e chi) :
    0 ≤ lrGapBudgetSEChiDerivE s e chi :=
  hminorant.trans (lrGapBudgetSEChiDerivEEndpointMinorant_le hs he hchi)

end CourtadeKumar
