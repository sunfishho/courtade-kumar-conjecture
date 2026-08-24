import InformationTheory.CourtadeKumar.MutualInformation

open scoped ENNReal NNReal BigOperators

namespace CourtadeKumar

variable {α β : Type*}

/-- The natural-log entropy sum of a finite PMF, before conversion to bits. -/
noncomputable def pmfEntropyNatReal {γ : Type*} [Fintype γ] (p : PMF γ) : ℝ :=
  ∑ x, Real.negMulLog (p x).toReal

/-- One KL summand splits into its joint and marginal entropy terms. -/
lemma pmfKLTerm_independentMarginals (p : PMF (α × β)) (z : α × β) :
    (p z).toReal *
        Real.log ((p z / independentMarginalsPMF p z).toReal) =
      -Real.negMulLog (p z).toReal -
        (p z).toReal * Real.log ((p.map Prod.fst) z.1).toReal -
        (p z).toReal * Real.log ((p.map Prod.snd) z.2).toReal := by
  by_cases hp : p z = 0
  · simp [hp]
  have hprod : independentMarginalsPMF p z ≠ 0 :=
    mt (independentMarginalsPMF_eq_zero_imp p z) hp
  have hprod' := hprod
  rw [independentMarginalsPMF, pmfProd_apply] at hprod'
  have hmarg : (p.map Prod.fst) z.1 ≠ 0 ∧ (p.map Prod.snd) z.2 ≠ 0 := by
    exact mul_ne_zero_iff.mp hprod'
  have hpReal : (p z).toReal ≠ 0 :=
    ENNReal.toReal_ne_zero.mpr ⟨hp, p.apply_ne_top z⟩
  have hfstReal : ((p.map Prod.fst) z.1).toReal ≠ 0 :=
    ENNReal.toReal_ne_zero.mpr ⟨hmarg.1, (p.map Prod.fst).apply_ne_top z.1⟩
  have hsndReal : ((p.map Prod.snd) z.2).toReal ≠ 0 :=
    ENNReal.toReal_ne_zero.mpr ⟨hmarg.2, (p.map Prod.snd).apply_ne_top z.2⟩
  rw [independentMarginalsPMF, pmfProd_apply, ENNReal.toReal_div,
    ENNReal.toReal_mul, Real.log_div hpReal (mul_ne_zero hfstReal hsndReal),
    Real.log_mul hfstReal hsndReal]
  simp only [Real.negMulLog_eq_neg]
  ring

variable [Fintype α] [Fintype β]

/-- A first marginal atom is the sum of the corresponding row of the joint PMF. -/
lemma map_fst_apply_eq_sum (p : PMF (α × β)) (a : α) :
    (p.map Prod.fst) a = ∑ b : β, p (a, b) := by
  classical
  rw [PMF.map_apply, tsum_fintype, Fintype.sum_prod_type]
  calc
    (∑ x : α, ∑ y : β, if a = x then p (x, y) else 0) =
        ∑ x : α, if a = x then ∑ y : β, p (x, y) else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases hax : a = x <;> simp [hax]
    _ = ∑ y : β, p (a, y) := by simp

/-- A second marginal atom is the sum of the corresponding column of the joint PMF. -/
lemma map_snd_apply_eq_sum (p : PMF (α × β)) (b : β) :
    (p.map Prod.snd) b = ∑ a : α, p (a, b) := by
  classical
  rw [PMF.map_apply, tsum_fintype, Fintype.sum_prod_type]
  simp

lemma map_fst_toReal_eq_sum (p : PMF (α × β)) (a : α) :
    ((p.map Prod.fst) a).toReal = ∑ b : β, (p (a, b)).toReal := by
  rw [map_fst_apply_eq_sum, ENNReal.toReal_sum]
  intro b _
  exact p.apply_ne_top (a, b)

lemma map_snd_toReal_eq_sum (p : PMF (α × β)) (b : β) :
    ((p.map Prod.snd) b).toReal = ∑ a : α, (p (a, b)).toReal := by
  rw [map_snd_apply_eq_sum, ENNReal.toReal_sum]
  intro a _
  exact p.apply_ne_top (a, b)

lemma sum_joint_mul_fst (p : PMF (α × β)) (f : α → ℝ) :
    (∑ z : α × β, (p z).toReal * f z.1) =
      ∑ a : α, ((p.map Prod.fst) a).toReal * f a := by
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  change (∑ y : β, (p (a, y)).toReal * f a) =
    ((p.map Prod.fst) a).toReal * f a
  rw [← Finset.sum_mul, ← map_fst_toReal_eq_sum]

lemma sum_joint_mul_snd (p : PMF (α × β)) (f : β → ℝ) :
    (∑ z : α × β, (p z).toReal * f z.2) =
      ∑ b : β, ((p.map Prod.snd) b).toReal * f b := by
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  change (∑ x : α, (p (x, b)).toReal * f b) =
    ((p.map Prod.snd) b).toReal * f b
  rw [← Finset.sum_mul, ← map_snd_toReal_eq_sum]

/-- KL against the independent marginals is the entropy defect. -/
lemma pmfKLReal_independentMarginals (p : PMF (α × β)) :
    pmfKLReal p (independentMarginalsPMF p) =
      pmfEntropyNatReal (p.map Prod.fst) +
        pmfEntropyNatReal (p.map Prod.snd) - pmfEntropyNatReal p := by
  rw [pmfKLReal]
  simp_rw [pmfKLTerm_independentMarginals]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  have hfst := sum_joint_mul_fst p
    (fun a ↦ Real.log ((p.map Prod.fst) a).toReal)
  have hsnd := sum_joint_mul_snd p
    (fun b ↦ Real.log ((p.map Prod.snd) b).toReal)
  rw [hfst, hsnd]
  simp only [pmfEntropyNatReal, Real.negMulLog_eq_neg, Finset.sum_neg_distrib]
  ring

end CourtadeKumar
