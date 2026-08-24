import InformationTheory.CourtadeKumar.TopTailBound

/-! The cap parameterization and the certified lower comparison in the
manuscript's natural `(c,q)` coordinates. -/

open Set

namespace CourtadeKumar

noncomputable def topCapR (c q : ℝ) : ℝ :=
  (1 - c ^ 2) / (1 - c ^ 2 * q)

noncomputable def topCapZeta (c q : ℝ) : ℝ :=
  topCapR c q * q

lemma topCapDen_pos {c q : ℝ}
    (hc : c ∈ Ioo (0 : ℝ) 1) (hq : q ∈ Ioo (0 : ℝ) 1) :
    0 < 1 - c ^ 2 * q := by
  have hc2lt : c ^ 2 < 1 := by nlinarith [hc.1, hc.2]
  have hprod : c ^ 2 * q < 1 := by
    nlinarith [mul_pos (sq_pos_of_pos hc.1) hq.1,
      mul_pos (sub_pos.mpr hc2lt) (sub_pos.mpr hq.2)]
  linarith

lemma topCapR_mem_Ioo {c q : ℝ}
    (hc : c ∈ Ioo (0 : ℝ) 1) (hq : q ∈ Ioo (0 : ℝ) 1) :
    topCapR c q ∈ Ioo (0 : ℝ) 1 := by
  have hden := topCapDen_pos hc hq
  have hnum : 0 < 1 - c ^ 2 := by nlinarith [hc.1, hc.2]
  unfold topCapR
  constructor
  · exact div_pos hnum hden
  · rw [div_lt_one hden]
    nlinarith [mul_pos (sq_pos_of_pos hc.1) (sub_pos.mpr hq.2)]

lemma topCapZeta_mem_Ioo {c q : ℝ}
    (hc : c ∈ Ioo (0 : ℝ) 1) (hq : q ∈ Ioo (0 : ℝ) 1) :
    topCapZeta c q ∈ Ioo (0 : ℝ) 1 := by
  have hR := topCapR_mem_Ioo hc hq
  unfold topCapZeta
  constructor
  · exact mul_pos hR.1 hq.1
  · have hRq : topCapR c q * q < topCapR c q := by
      simpa using mul_lt_mul_of_pos_left hq.2 hR.1
    exact hRq.trans hR.2

lemma topCertR_capCoordinates {c q : ℝ}
    (hc : c ∈ Ioo (0 : ℝ) 1) (hq : q ∈ Ioo (0 : ℝ) 1) :
    topCertR c (topCapZeta c q) = topCapR c q := by
  have hden := (topCapDen_pos hc hq).ne'
  unfold topCertR topCapZeta topCapR
  field_simp [hden]
  ring

lemma topCapQ_capCoordinates {c q : ℝ}
    (hc : c ∈ Ioo (0 : ℝ) 1) (hq : q ∈ Ioo (0 : ℝ) 1) :
    topCapQ c (topCapZeta c q) = q := by
  have hR := (topCapR_mem_Ioo hc hq).1.ne'
  unfold topCapQ
  rw [topCertR_capCoordinates hc hq]
  unfold topCapZeta
  exact mul_div_cancel_left₀ q hR

/-- The exact expression bounded by the cap certificate, now viewed as a
function of `(c,q)`.  The logarithmic cross-ratio is kept in its already
verified certificate form for the moment. -/
noncomputable def topCapJLower (c q : ℝ) : ℝ :=
  let R := topCapR c q
  let z := topCapZeta c q
  (R * Real.log 2 - topPhi (Real.sqrt R)) / (1 - R) +
    Real.log (topCertX c z) / (2 * c ^ 2 * q) + topCapETail c z

/-- Uniform strict margin supplied by the audited Bernstein certificate in
the manuscript's cap coordinates. -/
theorem topCapJLower_ge_margin {c q : ℝ}
    (hc : c ∈ Ioo (0 : ℝ) 1) (hq : q ∈ Ioo (0 : ℝ) 1) :
    (1 : ℝ) / 100 ≤ topCapJLower c q := by
  have h := topFiniteClaim_with_capETail hc (topCapZeta_mem_Ioo hc hq)
  unfold topCapJLower
  dsimp only
  simpa only [topCertR_capCoordinates hc hq,
    topCapQ_capCoordinates hc hq] using h

end CourtadeKumar
