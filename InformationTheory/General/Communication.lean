import Mathlib
import InformationTheory.General.InformationQuantities

/- Goals of this file:
 - Define a discrete channel
 - Define the Shannon capacity of a discrete channel
 - State the Shannon capacity theorem (sorryed)
 -/

open ProbabilityTheory MeasureTheory InformationQuantities

structure StationaryMemorylessChannel (Ω₁ Ω₂ : Type*)
[MeasurableSpace Ω₁] [StandardBorelSpace Ω₁] [MeasurableSpace Ω₂] [StandardBorelSpace Ω₂] where
  K : Kernel Ω₁ Ω₂
  isMarkov: IsMarkovKernel K

namespace MemorylessChannel

variable {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [StandardBorelSpace Ω₁] [MeasurableSpace Ω₂] [StandardBorelSpace Ω₂] (N : ℕ+) (M : ℕ+)

/-- Used for error probability calculation. -/
noncomputable def uniform_input_measure (M : ℕ+) : ProbabilityMeasure (Fin M) :=
  ⟨uniformOn (Set.univ : Set (Fin M)),
  by
     classical
     -- uniformOn_isProbabilityMeasure has been deprecated in lean 2.7.0
     exact ProbabilityTheory.uniformOn_isProbabilityMeasure
       (s := (Set.univ : Set (Fin M)))
       (hs  := (Set.finite_univ : Set.Finite (Set.univ : Set (Fin M))))
       (hs' := (Set.univ_nonempty : Set.Nonempty (Set.univ : Set (Fin M))))⟩

-- Produces output measure upon applying a channel on input measure
noncomputable def apply_channel_to_measure (C : StationaryMemorylessChannel Ω₁ Ω₂) (μ : Measure Ω₁)
[IsProbabilityMeasure μ] : Measure Ω₂ :=
  μ.bind C.K

-- Produces codewords given message from [M]. Deterministic.
def encoder (Ω : Type*) (N : ℕ+) (M : ℕ+) := Fin M → Fin N → Ω

-- Produces codeword given output of channel. Deterministic.
def decoder (Ω : Type*) (N : ℕ+) (M : ℕ+) := (Fin N → Ω) → Fin M

/- The encoder-decoder pair are encoded in this struct,
which also encodes blocklength (N) and number of possible messages (M) -/
structure CodingScheme (C : StationaryMemorylessChannel Ω₁ Ω₂) where
  N : ℕ+
  M : ℕ+
  encoder : encoder Ω₁ N M
  decoder : decoder Ω₂ N M

/-- Calculate the rate of a coding scheme as log_2 M/N -/
noncomputable def rate (C : StationaryMemorylessChannel Ω₁ Ω₂)
(CS : CodingScheme C) : ℝ :=
  (Real.logb 2 CS.M) / CS.N

/-- Create output block from product of independent kernels -/
noncomputable def blockOutputMeasure
    (K : Kernel Ω₁ Ω₂) (N : ℕ) (x : Fin N → Ω₁) :
    Measure (Fin N → Ω₂) :=
by
  classical
  exact Measure.pi (fun i : Fin N => K (x i))

/-- Calculate the average error probability of a coding scheme -/
noncomputable def error_probability (C : StationaryMemorylessChannel Ω₁ Ω₂)
(CS : CodingScheme C) : ℝ := by
  classical
  let M := CS.M
  let N := CS.N
  let μ := uniform_input_measure M
  let codeword_error_prob : Fin M → ℝ := fun m =>
    let x := CS.encoder m
    let output_distribution := blockOutputMeasure C.K N x
    let x_hat := output_distribution.map CS.decoder
    1 - (x_hat {m}).toReal
  exact (1 / M : ℝ) * (∑ m : Fin M, codeword_error_prob m)

def achievable_M (C : StationaryMemorylessChannel Ω₁ Ω₂) (N : ℕ+) (ε : ℝ) (M : ℕ+) : Prop :=
  ∃ CS : CodingScheme C, error_probability C CS ≤ ε ∧ CS.N = N ∧ CS.M = M

/-- defining M*(n,ε) -/
noncomputable def M_avg
  (C : StationaryMemorylessChannel Ω₁ Ω₂) (N : ℕ+) (ε : ℝ) : WithTop ℕ := by
  classical
  exact sSup { m : WithTop ℕ | ∃ M : ℕ+, (M : WithTop ℕ) = m ∧ achievable_M C N ε M }


/-- defining R*(n,ε) -/
noncomputable def R_star
  (C : StationaryMemorylessChannel Ω₁ Ω₂) (N : ℕ+) (ε : ℝ) : WithTop ℝ :=
by
  classical
  match M_avg (Ω₁:=Ω₁) (Ω₂:=Ω₂) C N ε with
  | ⊤ => exact ⊤
  | (M : ℕ) =>
      exact (((Real.logb 2 (M : ℝ)) / (N : ℝ) : ℝ) : WithTop ℝ)

noncomputable def R_epsilon
  (C : StationaryMemorylessChannel Ω₁ Ω₂) (ε : ℝ) : WithTop ℝ :=
  Filter.limsup (fun N : ℕ => R_star (Ω₁ := Ω₁) (Ω₂ := Ω₂) C (⟨N + 1, Nat.succ_pos _⟩) ε)
    Filter.atTop

noncomputable def shannon_capacity
  (C : StationaryMemorylessChannel Ω₁ Ω₂) : EReal :=
  ⨅ (ε : {ε : ℝ // 0 < ε}),
    (WithBot.some (R_epsilon (Ω₁ := Ω₁) (Ω₂ := Ω₂) C ε.1) : EReal)

noncomputable def information_capacity
  (C : StationaryMemorylessChannel Ω₁ Ω₂) : EReal :=
by
  classical
  let joint_μ (μ : ProbabilityMeasure Ω₁) : ProbabilityMeasure (Ω₁ × Ω₂) :=
    letI : IsProbabilityMeasure μ.toMeasure := μ.prop
    letI : IsMarkovKernel C.K := C.isMarkov
    ⟨μ.toMeasure.compProd C.K, inferInstance⟩
  let ENNReal_to_WithTopReal (d : ENNReal) : WithTop ℝ :=
    if d = ⊤ then ⊤ else (d.toReal : WithTop ℝ)
  exact sSup ((fun μ : ProbabilityMeasure Ω₁ =>
    (mutual_information (joint_μ μ).toMeasure)) '' Set.univ)

theorem shannon_capacity_theorem (C : StationaryMemorylessChannel Ω₁ Ω₂) :
    information_capacity (Ω₁ := Ω₁) (Ω₂ := Ω₂) C = shannon_capacity (Ω₁ := Ω₁) (Ω₂ := Ω₂) C := by
  sorry

end MemorylessChannel
