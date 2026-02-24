import Mathlib
import InformationTheory.Discrete.DiscreteInformationQuantities
import InformationTheory.Discrete.Utilities

-- Theorem 1.7 in Information Theory: From Coding to Learning (Han's inequality)
-- Cursor-aided

open DiscreteInformationQuantities MeasureTheory ProbabilityTheory

variable {S : Type*} [Countable S]

noncomputable def indices_to_entropy {n : ℕ+} (joint_pmf : PMF (Fin n → S))
    (indices_subset : Finset (Fin n)) : ℝ :=
  discrete_entropy <|
    PMF.map
      (fun x : Fin n → S =>
        (fun i : (↑indices_subset) => x i.1))
      joint_pmf

-- note that 1 ≤ k ≤ n
noncomputable def avg_entropy_k_subset_coords {n : ℕ+} (k : {k : ℕ // 0 < k ∧ k ≤ n}) (joint_pmf : PMF (Fin n → S)):
    ℝ :=
  (Finset.sum ((Finset.univ : Finset (Fin n)).powersetCard (k : ℕ)) fun indices_subset =>
        indices_to_entropy joint_pmf indices_subset) /
    (Nat.choose (n : ℕ) (k : ℕ) : ℝ)

def mkK {n : ℕ+} (k : ℕ) (hkpos : 0 < k) (hkle : k ≤ (n : ℕ)) : {k : ℕ // 0 < k ∧ k ≤ n} :=
  ⟨k, ⟨hkpos, hkle⟩⟩

lemma pos_of_one_le_sub_one {k : ℕ} (h : 1 ≤ k - 1) : 0 < k := by
  cases k with
  | zero => simp at h
  | succ k => exact Nat.succ_pos _

/-- Han's inequality -/
theorem hans_inequality {n : ℕ+} (joint_pmf : PMF (Fin n → S)) :
  (∀ k : {k : ℕ // 0 < k ∧ k < n},
      let k0 : {k : ℕ // 0 < k ∧ k ≤ n} :=
        mkK (n := n) (k := (k : ℕ)) k.2.1 (Nat.le_of_lt k.2.2)
      let k1 : {k : ℕ // 0 < k ∧ k ≤ n} :=
        mkK (n := n) (k := (k : ℕ) + 1) (Nat.succ_pos _) (Nat.succ_le_of_lt k.2.2)
      1 / (k : ℝ) * avg_entropy_k_subset_coords k0 joint_pmf
        ≤
        1 / ((k : ℕ) + 1 : ℝ) * avg_entropy_k_subset_coords k1 joint_pmf) ∧
    (∀ k : {k : ℕ // k + 1 ≤ n ∧ k - 1 ≥ 1},
        let hkplus : (k : ℕ) + 1 ≤ (n : ℕ) := k.2.1
        let hkminus : 1 ≤ (k : ℕ) - 1 := k.2.2
        let hkpos : 0 < (k : ℕ) := pos_of_one_le_sub_one hkminus
        let hk_le_n : (k : ℕ) ≤ (n : ℕ) := Nat.le_trans (Nat.le_succ (k : ℕ)) hkplus
        let k0 : {k : ℕ // 0 < k ∧ k ≤ n} := mkK (n := n) (k := (k : ℕ)) hkpos hk_le_n
        let k1 : {k : ℕ // 0 < k ∧ k ≤ n} :=
          mkK (n := n) (k := (k : ℕ) + 1) (Nat.succ_pos _) hkplus
        let km1 : {k : ℕ // 0 < k ∧ k ≤ n} :=
          mkK (n := n) (k := (k : ℕ) - 1) (lt_of_lt_of_le (Nat.succ_pos 0) hkminus)
            (Nat.le_trans (Nat.sub_le (k : ℕ) 1) hk_le_n)
        avg_entropy_k_subset_coords k1 joint_pmf
          - avg_entropy_k_subset_coords k0 joint_pmf
        ≤
        avg_entropy_k_subset_coords k0 joint_pmf - avg_entropy_k_subset_coords km1 joint_pmf) := by
  sorry
