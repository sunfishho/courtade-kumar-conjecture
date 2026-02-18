import Mathlib
import InformationTheory.General.InformationQuantities

/- Goals of this file:
 - Define a discrete channel
 - Define the Shannon capacity of a discrete channel
 - State the Shannon capacity theorem (sorryed)
 -/

open ProbabilityTheory MeasureTheory InformationQuantities

structure DiscreteMemorylessChannel (inp_alphabet out_alphabet: ℕ+) where
  K : Kernel (Fin inp_alphabet) (Fin out_alphabet)
  isMarkov: IsMarkovKernel K

namespace DiscreteMemorylessChannel

variable {inp_alphabet out_alphabet : ℕ+}

/-- Used for error probability calculation. -/
noncomputable def uniform_input_measure (num_msgs : ℕ+) : ProbabilityMeasure (Fin num_msgs) :=
  ⟨uniformOn (Set.univ : Set (Fin num_msgs)),
  by
     classical
     -- uniformOn_isProbabilityMeasure has been deprecated in lean 2.7.0
     exact ProbabilityTheory.uniformOn_isProbabilityMeasure
       (s := (Set.univ : Set (Fin num_msgs)))
       (hs  := (Set.finite_univ : Set.Finite (Set.univ : Set (Fin num_msgs))))
       (hs' := (Set.univ_nonempty : Set.Nonempty (Set.univ : Set (Fin num_msgs))))⟩

-- Produces output measure upon applying a channel on input measure
noncomputable def apply_channel_to_probability_measure {inp_alphabet out_alphabet : ℕ+} (DMC : DiscreteMemorylessChannel inp_alphabet out_alphabet) (μ : ProbabilityMeasure (Fin inp_alphabet)) : ProbabilityMeasure (Fin out_alphabet) :=
  let : ProbabilityTheory.IsMarkovKernel DMC.K := DMC.isMarkov
  ⟨μ.toMeasure.bind DMC.K, inferInstance⟩

-- Produces codewords given message from [M]. Deterministic.
def Encoder (inp_alphabet num_uses num_msgs : ℕ+) := Fin num_msgs → Fin num_uses → Fin inp_alphabet

-- Produces codeword given output of channel. Deterministic.
def Decoder (out_alphabet num_uses num_msgs : ℕ+) := (Fin num_uses → Fin out_alphabet) → Fin num_msgs

/- The encoder-decoder pair are encoded in this struct,
which also encodes blocklength (N) and number of possible messages (M) -/
structure CodingScheme (num_uses num_msgs : ℕ+) (DMC : DiscreteMemorylessChannel inp_alphabet out_alphabet) where
  num_uses : ℕ+
  num_msgs : ℕ+
  encoder : Encoder inp_alphabet num_uses num_msgs
  decoder : Decoder out_alphabet num_uses num_msgs

/-- Calculate the rate of a coding scheme as log_2 M/N -/
noncomputable def rate {inp_alphabet out_alphabet : ℕ+} (DMC : DiscreteMemorylessChannel inp_alphabet out_alphabet) {num_uses num_msgs : ℕ+}
(CS : CodingScheme num_uses num_msgs DMC) : ℝ :=
  (Real.logb 2 CS.num_msgs) / CS.num_uses

/-- Create output block from product of independent kernels -/
noncomputable def blockOutputMeasure
    (K : Kernel (Fin inp_alphabet) (Fin out_alphabet)) (num_uses : ℕ) (x : Fin num_uses → Fin inp_alphabet) :
    Measure (Fin num_uses → Fin out_alphabet) :=
by
  classical
  exact Measure.pi (fun i : Fin num_uses => K (x i))

/-- Calculate the average error probability of a coding scheme -/
noncomputable def error_probability {inp_alphabet out_alphabet : ℕ+} (DMC : DiscreteMemorylessChannel inp_alphabet out_alphabet) {num_uses num_msgs : ℕ+}
(CS : CodingScheme num_uses num_msgs DMC) : ℝ := by
  classical
  let M := CS.num_msgs
  let N := CS.num_uses
  let μ := uniform_input_measure M
  let codeword_error_prob : Fin M → ℝ := fun m =>
    let x := CS.encoder m
    let output_distribution := blockOutputMeasure DMC.K N x
    let x_hat := output_distribution.map CS.decoder
    1 - (x_hat {m}).toReal
  exact (1 / M : ℝ) * (∑ m : Fin M, codeword_error_prob m)

def achievable_M {inp_alphabet out_alphabet : ℕ+} (DMC : DiscreteMemorylessChannel inp_alphabet out_alphabet) (num_uses num_msgs : ℕ+) (ε : ℝ) : Prop :=
  ∃ CS : CodingScheme num_uses num_msgs DMC, error_probability DMC CS ≤ ε ∧ CS.num_uses = num_uses ∧ CS.num_msgs = num_msgs

/-- defining M*(n,ε) -/
noncomputable def M_avg {inp_alphabet out_alphabet : ℕ+} (DMC : DiscreteMemorylessChannel inp_alphabet out_alphabet) (num_uses : ℕ+) (ε : ℝ) : WithTop ℕ := by
  exact sSup { num_msgs : WithTop ℕ | ∃ num_msgs : ℕ+, achievable_M DMC num_uses num_msgs ε}

/-- defining R*(n,ε) -/
noncomputable def R_star
  {inp_alphabet out_alphabet : ℕ+} (DMC : DiscreteMemorylessChannel inp_alphabet out_alphabet) (num_uses : ℕ+) (ε : ℝ) : WithTop ℝ :=
by
  match M_avg DMC num_uses ε with
  | ⊤ => exact ⊤
  | (num_msgs : ℕ) =>
      exact (((Real.logb 2 (num_msgs : ℝ)) / (num_uses : ℝ) : ℝ) : WithTop ℝ)

noncomputable def R_epsilon
  {inp_alphabet out_alphabet : ℕ+} (DMC : DiscreteMemorylessChannel inp_alphabet out_alphabet) (ε : ℝ) : WithTop ℝ :=
  Filter.limsup (fun N : ℕ => R_star DMC (⟨N + 1, Nat.succ_pos _⟩) ε)
    Filter.atTop

noncomputable def shannon_capacity {inp_alphabet out_alphabet : ℕ+} (DMC : DiscreteMemorylessChannel inp_alphabet out_alphabet): EReal :=
  ⨅ (ε : {ε : ℝ // 0 < ε}),
    (WithBot.some (R_epsilon DMC ε.1) : EReal)


noncomputable def information_capacity {inp_alphabet out_alphabet : ℕ+} (DMC : DiscreteMemorylessChannel inp_alphabet out_alphabet) : EReal :=
by
  let joint_μ (μ : ProbabilityMeasure (Fin inp_alphabet)) : ProbabilityMeasure (Fin inp_alphabet × Fin out_alphabet) :=
    letI : IsProbabilityMeasure μ.toMeasure := μ.prop
    letI : IsMarkovKernel DMC.K := DMC.isMarkov
    ⟨μ.toMeasure.compProd DMC.K, inferInstance⟩
  let ENNReal_to_WithTopReal (d : ENNReal) : WithTop ℝ :=
    if d = ⊤ then ⊤ else (d.toReal : WithTop ℝ)
  exact sSup ((fun μ : ProbabilityMeasure (Fin inp_alphabet) =>
    (mutual_information (joint_μ μ))) '' Set.univ)

theorem shannon_capacity_theorem {inp_alphabet out_alphabet : ℕ+} (DMC : DiscreteMemorylessChannel inp_alphabet out_alphabet) :
    information_capacity DMC = shannon_capacity DMC := by
  sorry

end DiscreteMemorylessChannel
