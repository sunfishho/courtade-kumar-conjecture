import InformationTheory.CourtadeKumar.Basic

open MeasureTheory
open scoped ENNReal NNReal

namespace CourtadeKumar

/-- Split a Boolean word into its first `n` coordinates and its last coordinate. -/
def bitVecSuccEquiv (n : ℕ) : BitVec (n + 1) ≃ BitVec n × Bool :=
  Fin.succFunEquiv Bool n

@[simp]
lemma bitVecSuccEquiv_apply_fst (n : ℕ) (x : BitVec (n + 1)) (i : Fin n) :
    (bitVecSuccEquiv n x).1 i = x i.castSucc := by
  rfl

@[simp]
lemma bitVecSuccEquiv_apply_snd (n : ℕ) (x : BitVec (n + 1)) :
    (bitVecSuccEquiv n x).2 = x (Fin.last n) := by
  rfl

lemma bitVecSuccEquiv_apply (n : ℕ) (x : BitVec (n + 1)) :
    bitVecSuccEquiv n x = (fun i ↦ x i.castSucc, x (Fin.last n)) := by
  apply Prod.ext
  · funext i
    rfl
  · rfl

@[simp]
lemma bitVecSuccEquiv_symm_apply_castSucc (n : ℕ) (x : BitVec n) (b : Bool)
    (i : Fin n) :
    (bitVecSuccEquiv n).symm (x, b) i.castSucc = x i := by
  change Fin.append x (Function.const (Fin 1) b) i.castSucc = x i
  convert Fin.append_left x (Function.const (Fin 1) b) i using 1

@[simp]
lemma bitVecSuccEquiv_symm_apply_last (n : ℕ) (x : BitVec n) (b : Bool) :
    (bitVecSuccEquiv n).symm (x, b) (Fin.last n) = b := by
  change Fin.append x (Function.const (Fin 1) b) (Fin.last n) = b
  convert Fin.append_right x (Function.const (Fin 1) b) (0 : Fin 1) using 1

lemma bitVecSuccEquiv_symm_apply (n : ℕ) (x : BitVec n) (b : Bool) :
    (bitVecSuccEquiv n).symm (x, b) = Fin.snoc x b := by
  change Fin.append x (Function.const (Fin 1) b) = Fin.snoc x b
  rw [Fin.append_right_eq_snoc]
  rfl

@[simp]
lemma bitVecSuccEquiv_xorVec (n : ℕ) (x z : BitVec (n + 1)) :
    bitVecSuccEquiv n (xorVec x z) =
      (xorVec (bitVecSuccEquiv n x).1 (bitVecSuccEquiv n z).1,
        Bool.xor (bitVecSuccEquiv n x).2 (bitVecSuccEquiv n z).2) := by
  apply Prod.ext
  · funext i
    simp [xorVec]
  · simp [xorVec]

/-- XOR by a fixed Boolean is a self-inverse equivalence. -/
def boolXorEquiv (a : Bool) : Bool ≃ Bool where
  toFun := Bool.xor a
  invFun := Bool.xor a
  left_inv b := by cases a <;> cases b <;> rfl
  right_inv b := by cases a <;> cases b <;> rfl

@[simp]
lemma boolXorEquiv_symm_apply (a b : Bool) :
    (boolXorEquiv a).symm b = Bool.xor a b := rfl

/-- The independent product of two probability mass functions. -/
noncomputable def pmfProd {α β : Type*} (p : PMF α) (q : PMF β) : PMF (α × β) :=
  p.bind fun a ↦ q.map fun b ↦ (a, b)

lemma map_equiv_apply {α β : Type*} (p : PMF α) (e : α ≃ β) (b : β) :
    p.map e b = p (e.symm b) := by
  rw [PMF.map_apply, tsum_eq_single (e.symm b)]
  · simp
  · intro a ha
    have hne : b ≠ e a := by
      intro h
      apply ha
      exact e.injective (by simpa using h.symm)
    simp [hne]

open scoped Classical in
lemma map_prodMk_apply {α β : Type*} (q : PMF β) (a a' : α) (b : β) :
    q.map (fun b' ↦ (a, b')) (a', b) = if a' = a then q b else 0 := by
  rw [PMF.map_apply]
  by_cases h : a' = a
  · subst a'
    rw [tsum_eq_single b]
    · simp
    · intro b' hb'
      simp [hb'.symm]
  · simp [h]

open scoped Classical in
@[simp]
lemma pmfProd_apply {α β : Type*} (p : PMF α) (q : PMF β) (a : α) (b : β) :
    pmfProd p q (a, b) = p a * q b := by
  rw [pmfProd, PMF.bind_apply, tsum_eq_single a]
  · rw [map_prodMk_apply]
    simp
  · intro a' ha'
    rw [map_prodMk_apply]
    simp [ha'.symm]

/-- The uniform law on one Boolean coordinate. -/
noncomputable def uniformBoolPMF : PMF Bool :=
  PMF.uniformOfFintype Bool

@[simp]
lemma uniformBoolPMF_apply (b : Bool) : uniformBoolPMF b = (2 : ℝ≥0∞)⁻¹ := by
  rw [uniformBoolPMF, PMF.uniformOfFintype_apply]
  norm_num

theorem uniformBoolPMF_eq_bernoulliHalf :
    uniformBoolPMF = PMF.bernoulli (1 / 2 : ℝ≥0) (by norm_num) := by
  ext b
  cases b <;> simp [uniformBoolPMF_apply, PMF.bernoulli_apply]

theorem uniformInputPMF_map_bitVecSuccEquiv (n : ℕ) :
    (uniformInputPMF (n + 1)).map (bitVecSuccEquiv n) =
      pmfProd (uniformInputPMF n) uniformBoolPMF := by
  ext xb
  rcases xb with ⟨x, b⟩
  rw [map_equiv_apply, pmfProd_apply, uniformInputPMF_apply,
    uniformInputPMF_apply, uniformBoolPMF_apply]
  rw [pow_succ]
  rw [ENNReal.mul_inv (Or.inl (by positivity)) (Or.inl (by simp))]

theorem iidBernoulliPMF_map_bitVecSuccEquiv (n : ℕ) (p : ℝ≥0) (hp : p ≤ 1) :
    (iidBernoulliPMF (n + 1) p hp).map (bitVecSuccEquiv n) =
      pmfProd (iidBernoulliPMF n p hp) (PMF.bernoulli p hp) := by
  ext xb
  rcases xb with ⟨x, b⟩
  rw [map_equiv_apply, pmfProd_apply, iidBernoulliPMF_apply,
    iidBernoulliPMF_apply, Fin.prod_univ_castSucc]
  simp

theorem bscOutputPMF_map_bitVecSuccEquiv (n : ℕ) (p : ℝ≥0) (hp : p ≤ 1)
    (x : BitVec (n + 1)) :
    (bscOutputPMF (n + 1) p hp x).map (bitVecSuccEquiv n) =
      pmfProd
        (bscOutputPMF n p hp (bitVecSuccEquiv n x).1)
        ((PMF.bernoulli p hp).map (boolXorEquiv (bitVecSuccEquiv n x).2)) := by
  ext ub
  rcases ub with ⟨u, b⟩
  rw [map_equiv_apply, pmfProd_apply, bscOutputPMF_apply,
    bscOutputPMF_apply, map_equiv_apply, iidBernoulliPMF_apply,
    iidBernoulliPMF_apply, Fin.prod_univ_castSucc]
  simp [xorVec]

end CourtadeKumar
