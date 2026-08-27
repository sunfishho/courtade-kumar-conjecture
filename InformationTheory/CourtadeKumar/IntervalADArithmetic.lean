import InformationTheory.CourtadeKumar.IntervalDerivativeCertificate

/-!
# Verified interval automatic differentiation

The executable AD objects in this file carry a rational enclosure of a value
and of its three partial derivatives.  The accompanying semantic relation and
closure theorems verify the ordinary chain rules over `ℝ`.
-/

namespace CourtadeKumar

structure IntervalAD where
  value : RationalEnclosure
  derivS : RationalEnclosure
  derivK : RationalEnclosure
  derivChi : RationalEnclosure

/-- Semantic containment of a value and its three real partial derivatives. -/
def IntervalAD.Contains (ad : IntervalAD)
    (value derivS derivK derivChi : ℝ) : Prop :=
  ad.value.Contains value ∧ ad.derivS.Contains derivS ∧
    ad.derivK.Contains derivK ∧ ad.derivChi.Contains derivChi

namespace IntervalAD

def const (q : ℚ) : IntervalAD where
  value := RationalEnclosure.point q
  derivS := RationalEnclosure.point 0
  derivK := RationalEnclosure.point 0
  derivChi := RationalEnclosure.point 0

theorem contains_const (q : ℚ) :
    (const q).Contains (q : ℝ) 0 0 0 := by
  simp only [Contains, const]
  have hzero : (RationalEnclosure.point (0 : ℚ)).Contains (0 : ℝ) := by
    norm_num [RationalEnclosure.point, RationalEnclosure.Contains]
  exact ⟨RationalEnclosure.contains_point q,
    hzero, hzero, hzero⟩

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

theorem contains_variableS {interval : RationalEnclosure} {x : ℝ}
    (hx : interval.Contains x) :
    (variableS interval).Contains x 1 0 0 :=
  by
    simp only [Contains, variableS]
    have hone : (RationalEnclosure.point (1 : ℚ)).Contains (1 : ℝ) := by
      norm_num [RationalEnclosure.point, RationalEnclosure.Contains]
    have hzero : (RationalEnclosure.point (0 : ℚ)).Contains (0 : ℝ) := by
      norm_num [RationalEnclosure.point, RationalEnclosure.Contains]
    exact ⟨hx, hone, hzero, hzero⟩

theorem contains_variableK {interval : RationalEnclosure} {x : ℝ}
    (hx : interval.Contains x) :
    (variableK interval).Contains x 0 1 0 :=
  by
    simp only [Contains, variableK]
    have hone : (RationalEnclosure.point (1 : ℚ)).Contains (1 : ℝ) := by
      norm_num [RationalEnclosure.point, RationalEnclosure.Contains]
    have hzero : (RationalEnclosure.point (0 : ℚ)).Contains (0 : ℝ) := by
      norm_num [RationalEnclosure.point, RationalEnclosure.Contains]
    exact ⟨hx, hzero, hone, hzero⟩

theorem contains_variableChi {interval : RationalEnclosure} {x : ℝ}
    (hx : interval.Contains x) :
    (variableChi interval).Contains x 0 0 1 :=
  by
    simp only [Contains, variableChi]
    have hone : (RationalEnclosure.point (1 : ℚ)).Contains (1 : ℝ) := by
      norm_num [RationalEnclosure.point, RationalEnclosure.Contains]
    have hzero : (RationalEnclosure.point (0 : ℚ)).Contains (0 : ℝ) := by
      norm_num [RationalEnclosure.point, RationalEnclosure.Contains]
    exact ⟨hx, hzero, hzero, hone⟩

def add (a b : IntervalAD) : IntervalAD where
  value := RationalEnclosure.add a.value b.value
  derivS := RationalEnclosure.add a.derivS b.derivS
  derivK := RationalEnclosure.add a.derivK b.derivK
  derivChi := RationalEnclosure.add a.derivChi b.derivChi

theorem contains_add {a b : IntervalAD}
    {av as ak ac bv bs bk bc : ℝ}
    (ha : a.Contains av as ak ac) (hb : b.Contains bv bs bk bc) :
    (add a b).Contains (av + bv) (as + bs) (ak + bk) (ac + bc) := by
  exact ⟨RationalEnclosure.contains_add ha.1 hb.1,
    RationalEnclosure.contains_add ha.2.1 hb.2.1,
    RationalEnclosure.contains_add ha.2.2.1 hb.2.2.1,
    RationalEnclosure.contains_add ha.2.2.2 hb.2.2.2⟩

def neg (a : IntervalAD) : IntervalAD where
  value := RationalEnclosure.neg a.value
  derivS := RationalEnclosure.neg a.derivS
  derivK := RationalEnclosure.neg a.derivK
  derivChi := RationalEnclosure.neg a.derivChi

theorem contains_neg {a : IntervalAD} {av as ak ac : ℝ}
    (ha : a.Contains av as ak ac) :
    (neg a).Contains (-av) (-as) (-ak) (-ac) := by
  exact ⟨RationalEnclosure.contains_neg ha.1,
    RationalEnclosure.contains_neg ha.2.1,
    RationalEnclosure.contains_neg ha.2.2.1,
    RationalEnclosure.contains_neg ha.2.2.2⟩

def sub (a b : IntervalAD) : IntervalAD :=
  add a (neg b)

theorem contains_sub {a b : IntervalAD}
    {av as ak ac bv bs bk bc : ℝ}
    (ha : a.Contains av as ak ac) (hb : b.Contains bv bs bk bc) :
    (sub a b).Contains (av - bv) (as - bs) (ak - bk) (ac - bc) := by
  simpa [sub_eq_add_neg] using contains_add ha (contains_neg hb)

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

theorem contains_mul {a b : IntervalAD}
    {av as ak ac bv bs bk bc : ℝ}
    (ha : a.Contains av as ak ac) (hb : b.Contains bv bs bk bc) :
    (mul a b).Contains (av * bv)
      (as * bv + av * bs) (ak * bv + av * bk) (ac * bv + av * bc) := by
  exact ⟨RationalEnclosure.contains_mul ha.1 hb.1,
    RationalEnclosure.contains_add
      (RationalEnclosure.contains_mul ha.2.1 hb.1)
      (RationalEnclosure.contains_mul ha.1 hb.2.1),
    RationalEnclosure.contains_add
      (RationalEnclosure.contains_mul ha.2.2.1 hb.1)
      (RationalEnclosure.contains_mul ha.1 hb.2.2.1),
    RationalEnclosure.contains_add
      (RationalEnclosure.contains_mul ha.2.2.2 hb.1)
      (RationalEnclosure.contains_mul ha.1 hb.2.2.2)⟩

/-- Generic unary chain-rule constructor.  The caller supplies independently
verified enclosures for the output value and scalar derivative. -/
def unary (output slope : RationalEnclosure) (a : IntervalAD) : IntervalAD where
  value := output
  derivS := RationalEnclosure.mul slope a.derivS
  derivK := RationalEnclosure.mul slope a.derivK
  derivChi := RationalEnclosure.mul slope a.derivChi

theorem contains_unary {output slope : RationalEnclosure} {a : IntervalAD}
    {out derivative av as ak ac : ℝ}
    (hout : output.Contains out) (hslope : slope.Contains derivative)
    (ha : a.Contains av as ak ac) :
    (unary output slope a).Contains out
      (derivative * as) (derivative * ak) (derivative * ac) := by
  exact ⟨hout,
    RationalEnclosure.contains_mul hslope ha.2.1,
    RationalEnclosure.contains_mul hslope ha.2.2.1,
    RationalEnclosure.contains_mul hslope ha.2.2.2⟩

/-- Reciprocal AD rule for a value interval bounded strictly above zero. -/
def invPositive (a : IntervalAD) : IntervalAD :=
  let squareValue := RationalEnclosure.mulNonnegative a.value a.value
  { value := RationalEnclosure.invPositive a.value
    derivS := RationalEnclosure.neg (RationalEnclosure.div a.derivS squareValue)
    derivK := RationalEnclosure.neg (RationalEnclosure.div a.derivK squareValue)
    derivChi := RationalEnclosure.neg (RationalEnclosure.div a.derivChi squareValue) }

theorem contains_invPositive {a : IntervalAD} {av as ak ac : ℝ}
    (hlower : (0 : ℚ) < a.value.lower)
    (ha : a.Contains av as ak ac) :
    (invPositive a).Contains av⁻¹
      (-as / av ^ 2) (-ak / av ^ 2) (-ac / av ^ 2) := by
  have hlowerNonneg : (0 : ℚ) ≤ a.value.lower := hlower.le
  let squareValue := RationalEnclosure.mulNonnegative a.value a.value
  have hsquare : squareValue.Contains (av ^ 2) := by
    simpa [squareValue, pow_two] using
      RationalEnclosure.contains_mulNonnegative
        hlowerNonneg hlowerNonneg ha.1 ha.1
  have hsquareLower : (0 : ℚ) < squareValue.lower := by
    dsimp [squareValue, RationalEnclosure.mulNonnegative]
    positivity
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [invPositive] using
      RationalEnclosure.contains_invPositive hlower ha.1
  · simpa [invPositive, squareValue, neg_div] using
      RationalEnclosure.contains_neg
        (RationalEnclosure.contains_div hsquareLower ha.2.1 hsquare)
  · simpa [invPositive, squareValue, neg_div] using
      RationalEnclosure.contains_neg
        (RationalEnclosure.contains_div hsquareLower ha.2.2.1 hsquare)
  · simpa [invPositive, squareValue, neg_div] using
      RationalEnclosure.contains_neg
        (RationalEnclosure.contains_div hsquareLower ha.2.2.2 hsquare)

def divPositive (a b : IntervalAD) : IntervalAD :=
  mul a (invPositive b)

theorem contains_divPositive {a b : IntervalAD}
    {av as ak ac bv bs bk bc : ℝ}
    (hlower : (0 : ℚ) < b.value.lower)
    (ha : a.Contains av as ak ac) (hb : b.Contains bv bs bk bc) :
    (divPositive a b).Contains (av / bv)
      ((as * bv - av * bs) / bv ^ 2)
      ((ak * bv - av * bk) / bv ^ 2)
      ((ac * bv - av * bc) / bv ^ 2) := by
  have h := contains_mul ha (contains_invPositive hlower hb)
  convert h using 1 <;> field_simp <;> ring

end IntervalAD
end CourtadeKumar
