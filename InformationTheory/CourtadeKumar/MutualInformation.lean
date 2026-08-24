import InformationTheory.CourtadeKumar.CubeSplit
import InformationTheory.CourtadeKumar.DiscreteKL

open MeasureTheory InformationTheory
open scoped ENNReal NNReal BigOperators

namespace CourtadeKumar

variable {α β : Type*}

/-- The independent product of the two marginals of a joint PMF. -/
noncomputable def independentMarginalsPMF (p : PMF (α × β)) : PMF (α × β) :=
  pmfProd (p.map Prod.fst) (p.map Prod.snd)

/-- Every joint atom lies in the support of the product of its marginals. -/
lemma independentMarginalsPMF_eq_zero_imp (p : PMF (α × β)) (z : α × β) :
    independentMarginalsPMF p z = 0 → p z = 0 := by
  rcases z with ⟨a, b⟩
  rw [independentMarginalsPMF, pmfProd_apply]
  intro hzero
  rcases mul_eq_zero.mp hzero with hfst | hsnd
  · rw [PMF.map_apply, ENNReal.tsum_eq_zero] at hfst
    simpa using hfst (a, b)
  · rw [PMF.map_apply, ENNReal.tsum_eq_zero] at hsnd
    simpa using hsnd (a, b)

variable [Fintype α] [Fintype β]
  [MeasurableSpace α] [MeasurableSpace β]
  [MeasurableSingletonClass α] [MeasurableSingletonClass β]

/-- The PMF product of the marginals realizes the product of the marginal measures. -/
lemma independentMarginalsPMF_toMeasure (p : PMF (α × β)) :
    (independentMarginalsPMF p).toMeasure =
      p.toMeasure.fst.prod p.toMeasure.snd := by
  have hfst : p.toMeasure.fst = (p.map Prod.fst).toMeasure := by
    rw [Measure.fst, PMF.toMeasure_map (f := Prod.fst) p measurable_fst]
  have hsnd : p.toMeasure.snd = (p.map Prod.snd).toMeasure := by
    rw [Measure.snd, PMF.toMeasure_map (f := Prod.snd) p measurable_snd]
  rw [hfst, hsnd]
  apply Measure.ext_of_singleton
  rintro ⟨a, b⟩
  rw [PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton _),
    independentMarginalsPMF, pmfProd_apply]
  rw [show ({(a, b)} : Set (α × β)) = {a} ×ˢ {b} by ext z; simp,
    Measure.prod_prod,
    PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton _),
    PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton _)]

/-- Measure-theoretic mutual information of a finite joint law is its finite PMF KL sum. -/
lemma mutualInformation_toMeasure_eq_ofReal_pmfKLReal (p : PMF (α × β)) :
    InformationQuantities.mutual_information p.toMeasure =
      ENNReal.ofReal
        (Real.logb 2 (Real.exp 1) * pmfKLReal p (independentMarginalsPMF p)) := by
  rw [InformationQuantities.mutual_information]
  rw [← independentMarginalsPMF_toMeasure p]
  exact klDivBase2_toMeasure_eq_ofReal_pmfKLReal p (independentMarginalsPMF p)
    (independentMarginalsPMF_eq_zero_imp p)

end CourtadeKumar
