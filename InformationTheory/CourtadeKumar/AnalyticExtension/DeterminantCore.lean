import InformationTheory.CourtadeKumar.AnalyticExtension.DeterminantRemainder
import InformationTheory.CourtadeKumar.AnalyticExtension.DeterminantCompensation

/-! A cancellation-preserving rational target for the finite determinant. -/
namespace CourtadeKumar.LRAnalyticDeterminant

noncomputable def rationalP (s k c : ℝ) : ℝ :=
  1 - s + s * k * (1 - c) / 2 + LRAnalyticMidpoint.rationalAlpha s k c

noncomputable def modelCost (s k c : ℝ) : ℝ :=
  2 * ((LRAnalyticMidpoint.rationalD s k) ^ 3 / 24) *
    (1 + 2 * (s * k) / (3 * (1 + c)))

noncomputable def totalCost (s k c C : ℝ) : ℝ :=
  radialCost s (s * k) c + modelCost s k c + entropyCost s (s * k) c C

lemma p_factor_lower {p : CertificatePoint} (hi : LRHighShapeInterior p) :
    rationalP p.s p.k p.chi ≤ pFactor p := by
  have h1 := LRAnalyticMidpoint.beta_gap_lower hi
  have h2 := LRAnalyticMidpoint.alpha_lower hi
  unfold rationalP pFactor
  linarith

lemma model_cost_upper {p : CertificatePoint} (hi : LRHighShapeInterior p)
    (hs : p.s ≤ 1 / 10) (hk : p.k ≤ 4) :
    2 * modelGap p * (1 + lrLowRatioBWeight p / (1 + p.chi)) ≤ modelCost p.s p.k p.chi := by
  have hw := finite_weight_bounds hi hs hk
  have hc : 0 < 1 + p.chi := by linarith [hi.2.2.1]
  have hgap0 : 0 ≤ modelGap p := sub_nonneg.mpr (lrDeterminantD1_le_D hi)
  have hgap : modelGap p ≤ (LRAnalyticMidpoint.rationalD p.s p.k) ^ 3 / 24 := d_gap_cubic hi
  have hcf : 1 + lrLowRatioBWeight p / (1 + p.chi) ≤
      1 + 2 * (p.s * p.k) / (3 * (1 + p.chi)) := by
    have h := div_le_div_of_nonneg_right hw.2.1 hc.le
    change lrLowRatioBWeight p / (1 + p.chi) ≤ (2 / 3 * (p.s * p.k)) / (1 + p.chi) at h
    convert add_le_add_left h 1 using 1 <;> field_simp [hc.ne'] <;> ring
  have hcf0 : 0 ≤ 1 + lrLowRatioBWeight p / (1 + p.chi) := by
    have h := div_nonneg hw.1 hc.le
    linarith
  have hm := mul_le_mul hgap hcf hcf0 (hgap0.trans hgap)
  unfold modelCost
  nlinarith

theorem first_lower {p : CertificatePoint} (hi : LRHighShapeInterior p)
    (hr : LRHighShapeVRelevant p) (hs : p.s ≤ 1 / 10) (hk : p.k ≤ 4) :
    lrLowRatioNormalization p * (lrDeterminantD1 p * rationalP p.s p.k p.chi -
      lrCertificateBFlow p * (LRAnalyticMidpoint.loss p + totalCost p.s p.k p.chi (Real.log (4 / p.s)))) ≤
    lrDeterminantFirstBracket (lrCertificateBFlow p) (lrDeterminantD1 p)
      (lrCertificateGShape p) (lrDeterminantPsi p) (lrDeterminantDelta p) (lrCertificateW p) := by
  have hq := qcore_lower hi hs hk
  have hr0 := rcore_lower hi hr hs hk
  have hn := (lrLowRatioNormalization_pos hi).le
  have hB := (lrCertificateBFlow_pos hi).le
  have hP := mul_le_mul_of_nonneg_left (p_factor_lower hi) (lrDeterminantD1_nonnegative hi)
  have hM := mul_le_mul_of_nonneg_left (model_cost_upper hi hs hk) hB
  have hPN := mul_le_mul_of_nonneg_left hP hn
  have hMN := mul_le_mul_of_nonneg_left hM hn
  rw [lrLowRatioFirstBracket_eq_q0_add_r0_add_atom, lrCertificateW_eq_smallSBridge_split]
  unfold totalCost
  dsimp [lrCertificateE] at hq hr0
  nlinarith

/-- A small rational expression is sufficient for the original cleared branch. -/
theorem cleared_of_rational {p : CertificatePoint} {g lossBound dLower : ℝ}
    (hi : LRHighShapeInterior p) (hr : LRHighShapeVRelevant p)
    (hs : p.s ≤ 1 / 10) (hk : p.k ≤ 4)
    (hg : g ≤ lrDeterminantC0 p * lrDeterminantT p / lrLowRatioNormalization p)
    (hl : LRAnalyticMidpoint.loss p ≤ lossBound)
    (hd : dLower ≤ lrDeterminantD1 p)
    (hp : 0 ≤ rationalP p.s p.k p.chi - g)
    (hcheck : 0 ≤ dLower * (rationalP p.s p.k p.chi - g) + lrCertificateBFlow p *
      (lrCertificateX p * g - lossBound - totalCost p.s p.k p.chi (Real.log (4 / p.s)))) :
    LRDeterminantClearedSingularAt p := by
  have hn := lrLowRatioNormalization_pos hi
  have hB := (lrCertificateBFlow_pos hi).le
  have hJ : 0 ≤ lrCertificateBFlow p * lrCertificateX p - lrDeterminantD1 p := by
    have h := hr.2
    unfold lrCertificateJ at h
    linarith [lrDeterminantD1_le_D hi]
  have hfirst := first_lower hi hr hs hk
  have hD := mul_le_mul_of_nonneg_right hd hp
  have hLoss := mul_le_mul_of_nonneg_left hl hB
  have hDs := mul_le_mul_of_nonneg_left hD hn.le
  have hLs := mul_le_mul_of_nonneg_left hLoss hn.le
  have hcs := mul_nonneg hn.le hcheck
  have hgN : lrLowRatioNormalization p * g ≤ lrDeterminantC0 p * lrDeterminantT p := by
    rw [le_div_iff₀ hn] at hg
    nlinarith
  have hgJ := mul_le_mul_of_nonneg_right hgN hJ
  change 0 ≤ lrDeterminantClearedSingular _ _ _ _ _ _ _ _ _
  rw [lrDeterminantClearedSingular_eq_firstBracket]
  nlinarith

end CourtadeKumar.LRAnalyticDeterminant
