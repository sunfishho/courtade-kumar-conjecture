import Mathlib
import InformationTheory.General.InformationQuantities
import InformationTheory.General.Utilities

open InformationQuantities MeasureTheory ProbabilityTheory

-- File to prove IsProbabilityMeasure for all of the projection instances that are used

variable (X Y Z : Type*) [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z] [StandardBorelSpace X] [StandardBorelSpace Y] [StandardBorelSpace Z] (Pxy : Measure (X × Y)) [IsProbabilityMeasure Pxy] (Pxyz : Measure (X × Y × Z)) [IsProbabilityMeasure Pxyz]

-- (X,Y) -> X
instance : IsProbabilityMeasure (Pxy.map (fun p : X × Y => p.1)) :=
  Measure.isProbabilityMeasure_map (by fun_prop)

-- (X,Y) -> Y
instance : IsProbabilityMeasure (Pxy.map (fun p : X × Y => p.2)) :=
  Measure.isProbabilityMeasure_map (by fun_prop)

-- (X,Y) -> (Y,X)
instance : IsProbabilityMeasure (Pxy.map Prod.swap) :=
  Measure.isProbabilityMeasure_map (by fun_prop)

-- (X,Y,Z) -> Y
instance : IsProbabilityMeasure (Pxyz.map (fun p : X × Y × Z => p.2)) :=
  Measure.isProbabilityMeasure_map (by fun_prop)

-- (X,Y,Z) -> (X, Y)
instance : IsProbabilityMeasure (Pxyz.map (fun p : X × Y × Z => (p.1, p.2.1))) :=
  Measure.isProbabilityMeasure_map (by fun_prop)

-- (X,Y,Z) -> (X,Z)
instance : IsProbabilityMeasure (Pxyz.map (fun p : X × Y × Z => (p.1, p.2.2))) :=
  Measure.isProbabilityMeasure_map (by fun_prop)

-- (X,Y,Z) -> ((X,Y),Z)
instance : IsProbabilityMeasure (Pxyz.map (fun p : X × Y × Z => ((p.1, p.2.1), p.2.2))) :=
  Measure.isProbabilityMeasure_map (by fun_prop)

-- (X,Y,Z) -> (X, Z, Y)
instance : IsProbabilityMeasure (Pxyz.map (fun p : X × Y × Z => (p.1, p.2.2, p.2.1))) :=
  Measure.isProbabilityMeasure_map (by fun_prop)

-- (X,Y,Z) -> (Y,Z,X)
instance : IsProbabilityMeasure (Pxyz.map (fun p : X × Y × Z => (p.2.1, p.2.2, p.1))) :=
  Measure.isProbabilityMeasure_map (by fun_prop)
