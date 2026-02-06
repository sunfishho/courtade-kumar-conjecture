import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import InformationTheory.Discrete.DiscreteRandomVariable
import InformationTheory.General.RandomVariable
import InformationTheory.Discrete.DiscreteInformationQuantities
import Mathlib.Probability.Kernel.Defs

import Mathlib

namespace InformationQuantities

-- I(P_X, P_{Y|X}) = D(P_{X,Y}||P_XP_Y)
noncomputable def mutual_information
  {Ω: Type u}
