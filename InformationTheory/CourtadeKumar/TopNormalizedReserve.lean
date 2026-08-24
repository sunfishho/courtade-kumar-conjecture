import InformationTheory.CourtadeKumar.TopCapComparison

/-! The normalized corrected TOP reserve and its exact relation to the
manuscript's channel coordinates. -/

open Set

namespace CourtadeKumar

/-- The perspective quotient `Q(c,q)` in the normalized reserve. -/
noncomputable def topNormalizedQ (c q : ℝ) : ℝ :=
  topPerspectiveTerm c (Real.sqrt q) / (c * q)

/-- The channel coefficient `w(R) = (R log 2 - Phi(sqrt R))/(1-R)`. -/
noncomputable def topChannelW (R : ℝ) : ℝ :=
  (R * Real.log 2 - topPhi (Real.sqrt R)) / (1 - R)

/-- The normalized energy term `k(R,q)`. -/
noncomputable def topChannelK (R q : ℝ) : ℝ :=
  (R * topPhi (Real.sqrt q) -
      topPhi (Real.sqrt R * Real.sqrt q)) / ((1 - R) * q)

/-- The normalized corrected reserve with `(R,q)` held fixed. -/
noncomputable def topChannelH (R c q : ℝ) : ℝ :=
  topNormalizedQ c q - c * topChannelW R + topChannelK R q

/-- Multiplying the normalized reserve by its positive scale recovers the
corrected TOP reserve exactly. -/
theorem topReserve_eq_scale_mul_topChannelH
    {R c q : ℝ} (hR0 : 0 ≤ R) (hq0 : 0 ≤ q)
    (hR1 : R ≠ 1) (hc : c ≠ 0) (hq : q ≠ 0) :
    topReserve (Real.sqrt R) c (Real.sqrt q) =
      (1 - R) * c * q * topChannelH R c q := by
  have hsqrtR : Real.sqrt R ^ 2 = R := Real.sq_sqrt hR0
  have hsqrtq : Real.sqrt q ^ 2 = q := Real.sq_sqrt hq0
  have hs : 1 - R ≠ 0 := sub_ne_zero.mpr hR1.symm
  unfold topReserve topS topEll topEnergy topChannelH
    topNormalizedQ topChannelW topChannelK
  simp only [topR, hsqrtR, hsqrtq]
  field_simp [hs, hc, hq]
  ring

/-- The logarithmic cross-ratio appearing in the full-tail comparison. -/
noncomputable def topCapCrossRatio (c q : ℝ) : ℝ :=
  (1 - c ^ 2 * q) / (1 - q * (c / (2 - c)) ^ 2)

lemma topCapCrossRatio_den_pos {c q : ℝ}
    (hc : c ∈ Ioo (0 : ℝ) 1) (hq : q ∈ Ioo (0 : ℝ) 1) :
    0 < 1 - q * (c / (2 - c)) ^ 2 := by
  have htwo : 0 < 2 - c := by linarith [hc.2]
  have ht0 : 0 < c / (2 - c) := div_pos hc.1 htwo
  have ht1 : c / (2 - c) < 1 := by
    rw [div_lt_one htwo]
    linarith [hc.2]
  have ht2 : (c / (2 - c)) ^ 2 < 1 := by nlinarith
  have hprod : q * (c / (2 - c)) ^ 2 < 1 := by
    nlinarith [mul_pos (sub_pos.mpr hq.2) (sub_pos.mpr ht2)]
  linarith

lemma topCapCrossRatio_pos {c q : ℝ}
    (hc : c ∈ Ioo (0 : ℝ) 1) (hq : q ∈ Ioo (0 : ℝ) 1) :
    0 < topCapCrossRatio c q := by
  exact div_pos (topCapDen_pos hc hq) (topCapCrossRatio_den_pos hc hq)

/-- The rational cross-ratio already verified by the finite certificate is
exactly the analytic cap cross-ratio. -/
theorem topCertX_capCoordinates {c q : ℝ}
    (hc : c ∈ Ioo (0 : ℝ) 1) (hq : q ∈ Ioo (0 : ℝ) 1) :
    topCertX c (topCapZeta c q) = topCapCrossRatio c q := by
  have hcapDen := topCapDen_pos hc hq
  have htwo : 2 - c ≠ 0 := by linarith [hc.2]
  have hcrossDen := topCapCrossRatio_den_pos hc hq
  have hz := topCapZeta_mem_Ioo hc hq
  have hcertDen : topCertD c + topCertB c (topCapZeta c q) ≠ 0 :=
    (add_pos (topCertD_pos hc) (topCertB_pos hc hz)).ne'
  unfold topCertX topCapCrossRatio
  rw [div_eq_div_iff hcertDen hcrossDen.ne']
  unfold topCertD topCertB topCapZeta topCapR
  field_simp [hcapDen.ne', htwo]
  ring

/-- The certificate lower expression in cap coordinates, with its
logarithmic factor displayed in the manuscript's analytic form. -/
theorem topCapJLower_eq_crossRatio {c q : ℝ}
    (hc : c ∈ Ioo (0 : ℝ) 1) (hq : q ∈ Ioo (0 : ℝ) 1) :
    topCapJLower c q =
      topChannelW (topCapR c q) +
        Real.log (topCapCrossRatio c q) / (2 * c ^ 2 * q) +
          topCapETail c (topCapZeta c q) := by
  unfold topCapJLower topChannelW
  dsimp only
  rw [topCertX_capCoordinates hc hq]

end CourtadeKumar
