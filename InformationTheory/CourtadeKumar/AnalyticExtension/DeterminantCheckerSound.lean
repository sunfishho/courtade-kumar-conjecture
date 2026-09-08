import InformationTheory.CourtadeKumar.AnalyticExtension.DeterminantCheckerEndpoints
import InformationTheory.CourtadeKumar.AnalyticExtension.DeterminantCore

/-! Soundness of the reduced rational checker for the original determinant. -/
namespace CourtadeKumar.LRDeterminantReducedCertificate
open LRMidpointReducedCertificate LRAnalyticDeterminant

noncomputable def lossValue (p : CertificatePoint) (d : Leaf) : ℝ :=
  if d.useTangent then
    ((d.tangentPoint : ℝ) + p.chi * ((d.logTangent.upper : ℝ) - 1)) / (1 + p.chi) -
      LRAnalyticMidpoint.rationalAlpha p.s p.k p.chi
  else LRAnalyticMidpoint.rationalT p.s p.k p.chi / (1 + p.chi)

lemma Leaf.loss_bound {p : CertificatePoint} {d : Leaf} (hi : LRHighShapeInterior p)
    (ha : 0 < d.tangentPoint) (ht : d.logTangent.check (1 / d.tangentPoint) = true) :
    LRAnalyticMidpoint.loss p ≤ lossValue p d := by
  have haR : (0 : ℝ) < d.tangentPoint := by exact_mod_cast ha
  unfold lossValue
  split
  · have hlog := (RoundedLog.sound ht).2
    norm_num only [Rat.cast_div, Rat.cast_one] at hlog
    rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) haR.ne', Real.log_one, zero_sub] at hlog
    have h := loss_tangent hi haR
    have hc : 0 < 1 + p.chi := by linarith [hi.2.2.1]
    have hm := mul_le_mul_of_nonneg_left hlog hi.2.2.1.le
    have hdiv : ((d.tangentPoint : ℝ) - p.chi * (1 + Real.log (d.tangentPoint : ℝ))) / (1 + p.chi) ≤
        ((d.tangentPoint : ℝ) + p.chi * ((d.logTangent.upper : ℝ) - 1)) / (1 + p.chi) := by
      exact div_le_div_of_nonneg_right (by nlinarith) hc.le
    linarith
  · exact LRAnalyticMidpoint.loss_upper hi

lemma eval_p (p : CertificatePoint) (b : CertificateBox) (d : Leaf) :
    pExpr.eval (values p b d) = rationalP p.s p.k p.chi := by
  simp [pExpr, alphaExpr, Expr.eval, values, rationalP, LRAnalyticMidpoint.rationalAlpha]

lemma eval_g (p : CertificatePoint) (b : CertificateBox) (d : Leaf) :
    gExpr.eval (values p b d) = gapFactorH p.s (Real.log (4 / p.s)) (d.hCap b : ℝ) := by
  simp [gExpr, Expr.eval, values, gapFactorH]

lemma eval_cost (p : CertificatePoint) (b : CertificateBox) (d : Leaf) :
    costExpr.eval (values p b d) = totalCost p.s p.k p.chi (Real.log (4 / p.s)) := by
  simp [costExpr, dExpr, Expr.eval, values, totalCost, radialCost, modelCost,
    entropyCost, LRAnalyticMidpoint.rationalD]
  ring

lemma eval_loss (p : CertificatePoint) (b : CertificateBox) (d : Leaf) :
    (lossExpr d.useTangent).eval (values p b d) = lossValue p d := by
  cases h : d.useTangent <;>
    simp [lossExpr, lossValue, h, alphaExpr, tExpr, Expr.eval, values,
      LRAnalyticMidpoint.rationalT, LRAnalyticMidpoint.rationalAlpha]

lemma eval_coefficient (p : CertificatePoint) (b : CertificateBox) (d : Leaf) :
    coefficientExpr.eval (values p b d) =
      rationalP p.s p.k p.chi - gapFactorH p.s (Real.log (4 / p.s)) (d.hCap b : ℝ) := by
  simp [coefficientExpr, Expr.eval, eval_p, eval_g]

lemma eval_lower (p : CertificatePoint) (b : CertificateBox) (d : Leaf) :
    (lowerExpr d.useTangent).eval (values p b d) =
      (d.dLower b : ℝ) * (rationalP p.s p.k p.chi - gapFactorH p.s (Real.log (4 / p.s)) (d.hCap b : ℝ)) +
      lrCertificateBFlow p * (lrCertificateX p * gapFactorH p.s (Real.log (4 / p.s)) (d.hCap b : ℝ) -
        lossValue p d - totalCost p.s p.k p.chi (Real.log (4 / p.s))) := by
  simp [lowerExpr, Expr.eval, eval_coefficient, eval_g, eval_loss, eval_cost,
    values, lrCertificateX, lrCertificateE]

theorem Leaf.sound (b : CertificateBox) (d : Leaf) (hcheck : d.check b = true)
    (p : CertificatePoint) (hp : b.Contains p)
    (hi : LRHighShapeInterior p) (hr : LRHighShapeVRelevant p) :
    LRDeterminantClearedSingularAt p := by
  have hparts : BoxValid b ∧
      d.logCLo.check (4 / b.sHi) = true ∧ d.logCHi.check (4 / b.sLo) = true ∧
      d.logALo.check (1 + (1 - b.sHi) * b.kLo) = true ∧
      d.logAHi.check (1 + (1 - b.sLo) * b.kHi) = true ∧
      d.logD.check ((1 + lowerY b) / 2) = true ∧
      (0 < d.tangentPoint ∧ d.tangentPoint ≤ 1) ∧
      d.logTangent.check (1 / d.tangentPoint) = true ∧
      coefficientExpr.valid (d.inputs b) = true ∧ 0 ≤ (coefficientExpr.enclose (d.inputs b)).lower ∧
      (lowerExpr d.useTangent).valid (d.inputs b) = true ∧
      0 ≤ ((lowerExpr d.useTangent).enclose (d.inputs b)).lower := by
    simpa only [Leaf.check, Bool.and_eq_true, decide_eq_true_eq] using hcheck
  rcases hparts with ⟨hv, hcl, hch, hal, hah, hd, ha, ht, hpValid, hpLo, hlValid, hlLo⟩
  rcases d.endpoint_bounds hv hp hi hcl hch hal hah hd with ⟨henv, hD, hH, hs, hk⟩
  have hpc := coefficientExpr.sound henv hpValid
  have hlc := (lowerExpr d.useTangent).sound henv hlValid
  rw [eval_coefficient] at hpc
  rw [eval_lower] at hlc
  have hp0 : 0 ≤ rationalP p.s p.k p.chi - gapFactorH p.s (Real.log (4 / p.s)) (d.hCap b : ℝ) :=
    (show (0 : ℝ) ≤ ((coefficientExpr.enclose (d.inputs b)).lower : ℝ) by exact_mod_cast hpLo).trans hpc.1
  have hl0 : 0 ≤ (d.dLower b : ℝ) *
      (rationalP p.s p.k p.chi - gapFactorH p.s (Real.log (4 / p.s)) (d.hCap b : ℝ)) +
      lrCertificateBFlow p * (lrCertificateX p * gapFactorH p.s (Real.log (4 / p.s)) (d.hCap b : ℝ) -
        lossValue p d - totalCost p.s p.k p.chi (Real.log (4 / p.s))) :=
    (show (0 : ℝ) ≤ (((lowerExpr d.useTangent).enclose (d.inputs b)).lower : ℝ) by exact_mod_cast hlLo).trans hlc.1
  exact cleared_of_rational hi hr hs hk (compensation_lower_h hi hs hk hH)
    (d.loss_bound hi ha.1 ht) hD hp0 hl0

theorem box_sound (b : CertificateBox) (tree : Tree) (hcheck : checkTree b tree = true)
    (p : CertificatePoint) (hp : b.Contains p)
    (hi : LRHighShapeInterior p) (hr : LRHighShapeVRelevant p) :
    LRDeterminantClearedSingularAt p := by
  have h := subdivisionCertificate_sound
    (Relevant := fun _ => True)
    (Property := fun q => LRHighShapeInterior q → LRHighShapeVRelevant q → LRDeterminantClearedSingularAt q)
    (acceptBox := Leaf.check) (discardBox := fun _ (_ : Unit) => false)
    Leaf.sound (by intro _ _ h; simp at h) hcheck p hp trivial
  exact h hi hr

end CourtadeKumar.LRDeterminantReducedCertificate
