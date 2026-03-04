import Mathlib
import InformationTheory.General.InformationQuantities

-- Theorem 2.17 in Information Theory: From Coding to Learning

open InformationQuantities MeasureTheory ProbabilityTheory

variable (X Y : Type*) [MeasurableSpace X] [MeasurableSpace Y] [StandardBorelSpace Y] [StandardBorelSpace X]

theorem kl_dpi
  (Px : Measure X)
  [IsProbabilityMeasure Px]
  (Qx : Measure X)
  [IsProbabilityMeasure Qx]
  (Pyx : Kernel X Y)
  [IsMarkovKernel Pyx]
  [Nonempty X]
  [Nonempty Y] :
  let Py := Px.bind Pyx
  let Qy := Qx.bind Pyx
  let Pxy := Pyx † Px
  let Qxy := Pyx † Qx
  klDivBase2 Px Qx ≥ klDivBase2 Py Qy
  ∧ klDivBase2 Px Qx = klDivBase2 Py Qy ↔ conditionalklDivBase2 (Py.compProd Pxy) (Py.compProd Qxy) = 0 := by
sorry
