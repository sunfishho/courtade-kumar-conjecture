import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import InformationTheory.Discrete.DiscreteRandomVariable
import InformationTheory.General.RandomVariable
import InformationTheory.Discrete.DiscreteInformationQuantities
import Mathlib.Probability.Kernel.Defs

/- Goals of this file:
 - Define a discrete channel
 - Define the Shannon capacity of a discrete channel
 - State the Shannon capacity theorem (sorryed)
 -/

open ProbabilityTheory
open MeasureTheory

structure StationaryMemorylessChannel (Ω₁ Ω₂ : Type*)
[MeasurableSpace Ω₁] [MeasurableSpace Ω₂] where
  K : Kernel Ω₁ Ω₂
  isMarkov: IsMarkovKernel K

namespace MemorylessChannel

variable {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]

-- Produces output measure upon applying a channel on input measure
noncomputable def apply_channel_to_measure (C : StationaryMemorylessChannel Ω₁ Ω₂) (μ : Measure Ω₁)
[IsProbabilityMeasure μ] : Measure Ω₂ :=
  μ.bind C.K

-- Produces codewords given message from [M]. Deterministic.
def encoder (Ω : Type*) (N : ℕ+) (M : ℕ+) := Fin M → Vector Ω N

-- Produces codeword given output of channel. Deterministic.
def decoder (Ω : Type*) (N : ℕ+) (M : ℕ+) := Vector Ω N → Fin M

/- The encoder-decoder pair are encoded in this struct,
which also encodes blocklength (N) and number of possible messages (M) -/
structure CodingScheme (C : StationaryMemorylessChannel Ω₁ Ω₂) where
  N : ℕ+
  M : ℕ+
  encoder : encoder Ω₁ N M
  decoder : decoder Ω₂ N M

-- Calculate the rate of a coding scheme as log_2 M/N
noncomputable def rate (C : StationaryMemorylessChannel Ω₁ Ω₂)
(CS : CodingScheme C) : ℝ :=
  (Real.logb 2 CS.M) / CS.N

-- Calculate the average error probability assuming a uniform distribution on input messages
noncomputable def avg_error_prob (C : StationaryMemorylessChannel Ω₁ Ω₂)
(CS : CodingScheme C) : ℝ :=

end MemorylessChannel

-- noncomputable def ShannonCapacity {Ω₁ Ω₂ : Type*}
