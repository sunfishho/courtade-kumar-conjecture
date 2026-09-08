import InformationTheory.CourtadeKumar.ExactIntervalArithmeticCore

/-!
# Executable interval automatic differentiation

This module contains only the exact-rational data and computations for a
value and its three partial derivatives.  Their real-valued containment
relation and chain-rule theorems remain in `IntervalADArithmetic`.
-/

namespace CourtadeKumar

structure IntervalAD where
  value : RationalEnclosure
  derivS : RationalEnclosure
  derivK : RationalEnclosure
  derivChi : RationalEnclosure

namespace IntervalAD

def const (q : ℚ) : IntervalAD where
  value := RationalEnclosure.point q
  derivS := RationalEnclosure.point 0
  derivK := RationalEnclosure.point 0
  derivChi := RationalEnclosure.point 0

def variableS (value : RationalEnclosure) : IntervalAD where
  value := value
  derivS := RationalEnclosure.point 1
  derivK := RationalEnclosure.point 0
  derivChi := RationalEnclosure.point 0

def variableK (value : RationalEnclosure) : IntervalAD where
  value := value
  derivS := RationalEnclosure.point 0
  derivK := RationalEnclosure.point 1
  derivChi := RationalEnclosure.point 0

def variableChi (value : RationalEnclosure) : IntervalAD where
  value := value
  derivS := RationalEnclosure.point 0
  derivK := RationalEnclosure.point 0
  derivChi := RationalEnclosure.point 1

def add (a b : IntervalAD) : IntervalAD where
  value := RationalEnclosure.add a.value b.value
  derivS := RationalEnclosure.add a.derivS b.derivS
  derivK := RationalEnclosure.add a.derivK b.derivK
  derivChi := RationalEnclosure.add a.derivChi b.derivChi

def neg (a : IntervalAD) : IntervalAD where
  value := RationalEnclosure.neg a.value
  derivS := RationalEnclosure.neg a.derivS
  derivK := RationalEnclosure.neg a.derivK
  derivChi := RationalEnclosure.neg a.derivChi

def sub (a b : IntervalAD) : IntervalAD :=
  add a (neg b)

def mul (a b : IntervalAD) : IntervalAD where
  value := RationalEnclosure.mul a.value b.value
  derivS := RationalEnclosure.add
    (RationalEnclosure.mul a.derivS b.value)
    (RationalEnclosure.mul a.value b.derivS)
  derivK := RationalEnclosure.add
    (RationalEnclosure.mul a.derivK b.value)
    (RationalEnclosure.mul a.value b.derivK)
  derivChi := RationalEnclosure.add
    (RationalEnclosure.mul a.derivChi b.value)
    (RationalEnclosure.mul a.value b.derivChi)

/-- Generic unary chain-rule constructor.  The caller supplies independently
verified enclosures for the output value and scalar derivative. -/
def unary (output slope : RationalEnclosure) (a : IntervalAD) : IntervalAD where
  value := output
  derivS := RationalEnclosure.mul slope a.derivS
  derivK := RationalEnclosure.mul slope a.derivK
  derivChi := RationalEnclosure.mul slope a.derivChi

/-- Reciprocal AD rule for a value interval bounded strictly above zero. -/
def invPositive (a : IntervalAD) : IntervalAD :=
  let squareValue := RationalEnclosure.mulNonnegative a.value a.value
  { value := RationalEnclosure.invPositive a.value
    derivS := RationalEnclosure.neg (RationalEnclosure.div a.derivS squareValue)
    derivK := RationalEnclosure.neg (RationalEnclosure.div a.derivK squareValue)
    derivChi := RationalEnclosure.neg (RationalEnclosure.div a.derivChi squareValue) }

def divPositive (a b : IntervalAD) : IntervalAD :=
  mul a (invPositive b)

end IntervalAD
end CourtadeKumar
