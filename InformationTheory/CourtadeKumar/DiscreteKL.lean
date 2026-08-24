import InformationTheory.CourtadeKumar.Entropy

open MeasureTheory InformationTheory
open scoped ENNReal NNReal BigOperators

namespace CourtadeKumar

variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]

/-- A PMF is the density `p / q` with respect to `q` when its support lies in that of `q`. -/
lemma pmf_toMeasure_eq_withDensity_ratio (p q : PMF α)
    (h : ∀ x, q x = 0 → p x = 0) :
    p.toMeasure = q.toMeasure.withDensity (fun x ↦ p x / q x) := by
  apply Measure.ext_of_singleton
  intro x
  rw [PMF.toMeasure_apply_singleton p x (MeasurableSet.singleton _),
    withDensity_apply _ (MeasurableSet.singleton _),
    MeasureTheory.lintegral_singleton,
    PMF.toMeasure_apply_singleton q x (MeasurableSet.singleton _)]
  by_cases hx : q x = 0
  · simp [hx, h x hx]
  · exact (ENNReal.div_mul_cancel hx (q.apply_ne_top x)).symm

/-- Pointwise PMF ratios realize the Radon--Nikodym derivative almost everywhere. -/
lemma pmf_rnDeriv_eq_ratio_ae (p q : PMF α)
    (h : ∀ x, q x = 0 → p x = 0) :
    p.toMeasure.rnDeriv q.toMeasure =ᵐ[q.toMeasure] fun x ↦ p x / q x := by
  rw [pmf_toMeasure_eq_withDensity_ratio p q h]
  exact Measure.rnDeriv_withDensity _ (by fun_prop)

/-- Support containment of finite PMFs implies absolute continuity of their measures. -/
lemma pmf_toMeasure_absolutelyContinuous (p q : PMF α)
    (h : ∀ x, q x = 0 → p x = 0) :
    p.toMeasure ≪ q.toMeasure := by
  rw [pmf_toMeasure_eq_withDensity_ratio p q h]
  exact withDensity_absolutelyContinuous _ _

/-- The ordinary-real finite sum underlying KL divergence. -/
noncomputable def pmfKLReal (p q : PMF α) : ℝ :=
  ∑ x, (p x).toReal * Real.log ((p x / q x).toReal)

/-- Mathlib's measure-theoretic KL divergence reduces to the usual finite PMF sum. -/
lemma klDiv_toMeasure_eq_ofReal_pmfKLReal (p q : PMF α)
    (h : ∀ x, q x = 0 → p x = 0) :
    klDiv p.toMeasure q.toMeasure = ENNReal.ofReal (pmfKLReal p q) := by
  have hac : p.toMeasure ≪ q.toMeasure := pmf_toMeasure_absolutelyContinuous p q h
  have hint : Integrable (llr p.toMeasure q.toMeasure) p.toMeasure := Integrable.of_finite
  rw [klDiv_of_ac_of_integrable hac hint]
  have hrn := pmf_rnDeriv_eq_ratio_ae p q h
  have hllr :
      llr p.toMeasure q.toMeasure =ᵐ[p.toMeasure]
        fun x ↦ Real.log ((p x / q x).toReal) := by
    filter_upwards [hac.ae_le hrn] with x hx
    simpa [llr_def] using congrArg (fun z : ℝ≥0∞ ↦ Real.log z.toReal) hx
  rw [integral_congr_ae hllr, PMF.integral_eq_sum]
  simp [pmfKLReal]

/-- The base-2 KL divergence is the finite PMF sum scaled by `1 / log 2`. -/
lemma klDivBase2_toMeasure_eq_ofReal_pmfKLReal (p q : PMF α)
    (h : ∀ x, q x = 0 → p x = 0) :
    InformationQuantities.klDivBase2 p.toMeasure q.toMeasure =
      ENNReal.ofReal
        (Real.logb 2 (Real.exp 1) * pmfKLReal p q) := by
  have hcoeff : 0 ≤ Real.logb 2 (Real.exp 1) := by
    rw [Real.logb, Real.log_exp]
    positivity
  rw [InformationQuantities.klDivBase2,
    klDiv_toMeasure_eq_ofReal_pmfKLReal p q h, mul_comm,
    ← ENNReal.ofReal_mul hcoeff]

end CourtadeKumar
