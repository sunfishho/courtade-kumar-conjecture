import InformationTheory.CourtadeKumar.LRCompactVLambdaCenteredPolynomial

/-!
# Derivatives of the centered compact-`V` polynomial

This module gives named real expressions for `U'`, `U''`, and all five
first/second `(v,x)` partial derivatives used by the centered-Taylor interval
evaluator.  The definitions intentionally mirror the finite sums that a
rational interval checker will execute later.
-/

set_option autoImplicit false

open scoped BigOperators

namespace CourtadeKumar

/-- First derivative of `lrCompactVCenteredU`. -/
def lrCompactVCenteredUDeriv (v : ℝ) (n : ℕ) : ℝ :=
  let m := 2 * n - 1
  1 + v ^ m + (1 + v) * (m : ℝ) * v ^ (m - 1)

/-- Second derivative of `lrCompactVCenteredU`.  Natural-number products
keep the evaluator coefficients manifestly integral, including at `m=0`. -/
def lrCompactVCenteredUSecondDeriv (v : ℝ) (n : ℕ) : ℝ :=
  let m := 2 * n - 1
  2 * (m : ℝ) * v ^ (m - 1) +
    (1 + v) * (m * (m - 1) : ℕ) * v ^ (m - 2)

theorem hasDerivAt_lrCompactVCenteredU (v : ℝ) (n : ℕ) :
    HasDerivAt (fun q ↦ lrCompactVCenteredU q n)
      (lrCompactVCenteredUDeriv v n) v := by
  let m := 2 * n - 1
  have hleft : HasDerivAt (fun q : ℝ ↦ 1 + q) 1 v := by
    simpa using (hasDerivAt_const v 1).add (hasDerivAt_id v)
  have hpower : HasDerivAt (fun q : ℝ ↦ q ^ m)
      ((m : ℝ) * v ^ (m - 1)) v := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id v).pow m
  have hright : HasDerivAt (fun q : ℝ ↦ 1 + q ^ m)
      ((m : ℝ) * v ^ (m - 1)) v := by
    simpa only [Pi.add_apply, zero_add] using
      (hasDerivAt_const v 1).add hpower
  convert hleft.mul hright using 1
  simp only [lrCompactVCenteredUDeriv, m, one_mul]
  ring

theorem hasDerivAt_lrCompactVCenteredUDeriv (v : ℝ) (n : ℕ) :
    HasDerivAt (fun q ↦ lrCompactVCenteredUDeriv q n)
      (lrCompactVCenteredUSecondDeriv v n) v := by
  let m := 2 * n - 1
  have hleft : HasDerivAt (fun q : ℝ ↦ 1 + q) 1 v := by
    simpa using (hasDerivAt_const v 1).add (hasDerivAt_id v)
  have hpower : HasDerivAt (fun q : ℝ ↦ q ^ m)
      ((m : ℝ) * v ^ (m - 1)) v := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id v).pow m
  have hweightedPower :
      HasDerivAt (fun q : ℝ ↦ (m : ℝ) * q ^ (m - 1))
        ((m : ℝ) * ((m - 1 : ℕ) : ℝ) * v ^ (m - 2)) v := by
    convert ((hasDerivAt_id v).pow (m - 1)).const_mul (m : ℝ) using 1
    simp only [id_eq, mul_one,
      show m - 1 - 1 = m - 2 by omega]
    ring
  have hfirst : HasDerivAt (fun q : ℝ ↦ 1 + q ^ m)
      ((m : ℝ) * v ^ (m - 1)) v := by
    simpa only [Pi.add_apply, zero_add] using
      (hasDerivAt_const v 1).add hpower
  convert hfirst.add (hleft.mul hweightedPower) using 1
  · funext q
    simp only [lrCompactVCenteredUDeriv, m, Pi.add_apply, Pi.mul_apply]
    ring
  · simp only [lrCompactVCenteredUSecondDeriv, m, one_mul, Nat.cast_mul]
    ring

/-- `v` derivative of one polynomialized head term. -/
noncomputable def lrCompactVLambdaCenteredPolynomialTermV
    (lambda R v x : ℝ) (n : ℕ) : ℝ :=
  lrLowA n *
    (lrCompactVLambdaCenteredA lambda R n * x ^ n *
      lrCompactVCenteredUDeriv v n)

/-- `x` derivative of one polynomialized head term. -/
noncomputable def lrCompactVLambdaCenteredPolynomialTermX
    (lambda R v x : ℝ) (n : ℕ) : ℝ :=
  lrLowA n *
    (lrCompactVLambdaCenteredA lambda R n * (n : ℝ) * x ^ (n - 1) *
      lrCompactVCenteredU v n)

/-- `vv` derivative of one polynomialized head term. -/
noncomputable def lrCompactVLambdaCenteredPolynomialTermVV
    (lambda R v x : ℝ) (n : ℕ) : ℝ :=
  lrLowA n *
    (lrCompactVLambdaCenteredA lambda R n * x ^ n *
      lrCompactVCenteredUSecondDeriv v n)

/-- Mixed `vx` derivative of one polynomialized head term. -/
noncomputable def lrCompactVLambdaCenteredPolynomialTermVX
    (lambda R v x : ℝ) (n : ℕ) : ℝ :=
  lrLowA n *
    (lrCompactVLambdaCenteredA lambda R n * (n : ℝ) * x ^ (n - 1) *
      lrCompactVCenteredUDeriv v n)

/-- `xx` derivative of one polynomialized head term. -/
noncomputable def lrCompactVLambdaCenteredPolynomialTermXX
    (lambda R v x : ℝ) (n : ℕ) : ℝ :=
  lrLowA n *
    (lrCompactVLambdaCenteredA lambda R n *
      ((n * (n - 1) : ℕ) : ℝ) * x ^ (n - 2) *
      lrCompactVCenteredU v n)

/-- Evaluator-facing `v` partial of the finite polynomial. -/
noncomputable def lrCompactVLambdaCenteredPolynomialV
    (N : ℕ) (lambda R v x : ℝ) : ℝ :=
  (∑ j ∈ Finset.range N,
      lrCompactVLambdaCenteredPolynomialTermV
        lambda R v x (j + 1)) -
    4 * x * lrWKernel R 1

/-- Evaluator-facing `x` partial of the finite polynomial. -/
noncomputable def lrCompactVLambdaCenteredPolynomialX
    (N : ℕ) (lambda R v x : ℝ) : ℝ :=
  (∑ j ∈ Finset.range N,
      lrCompactVLambdaCenteredPolynomialTermX
        lambda R v x (j + 1)) -
    4 * v * lrWKernel R 1

/-- Evaluator-facing `vv` partial of the finite polynomial. -/
noncomputable def lrCompactVLambdaCenteredPolynomialVV
    (N : ℕ) (lambda R v x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range N,
    lrCompactVLambdaCenteredPolynomialTermVV
      lambda R v x (j + 1)

/-- Evaluator-facing mixed `vx` partial of the finite polynomial. -/
noncomputable def lrCompactVLambdaCenteredPolynomialVX
    (N : ℕ) (lambda R v x : ℝ) : ℝ :=
  (∑ j ∈ Finset.range N,
      lrCompactVLambdaCenteredPolynomialTermVX
        lambda R v x (j + 1)) -
    4 * lrWKernel R 1

/-- Evaluator-facing `xx` partial of the finite polynomial. -/
noncomputable def lrCompactVLambdaCenteredPolynomialXX
    (N : ℕ) (lambda R v x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range N,
    lrCompactVLambdaCenteredPolynomialTermXX
      lambda R v x (j + 1)

theorem hasDerivAt_lrCompactVLambdaCenteredPolynomialTerm_v
    (lambda R v x : ℝ) (n : ℕ) :
    HasDerivAt
      (fun q ↦ lrCompactVLambdaCenteredPolynomialTerm lambda R q x n)
      (lrCompactVLambdaCenteredPolynomialTermV lambda R v x n) v := by
  have hU := hasDerivAt_lrCompactVCenteredU v n
  have hvariable := hU.const_mul
    (lrCompactVLambdaCenteredA lambda R n * x ^ n)
  have hconstant := hasDerivAt_const v
    (4 * lambda * (1 - lrCompactVScore R n))
  have h := (hvariable.add hconstant).const_mul (lrLowA n)
  convert h using 1 <;>
    simp [lrCompactVLambdaCenteredPolynomialTerm,
      lrCompactVLambdaCenteredPolynomialTermV] <;> ring

theorem hasDerivAt_lrCompactVLambdaCenteredPolynomialTerm_x
    (lambda R v x : ℝ) (n : ℕ) :
    HasDerivAt
      (fun q ↦ lrCompactVLambdaCenteredPolynomialTerm lambda R v q n)
      (lrCompactVLambdaCenteredPolynomialTermX lambda R v x n) x := by
  have hpower := (hasDerivAt_id x).pow n
  have hvariable := hpower.const_mul
    (lrCompactVLambdaCenteredA lambda R n * lrCompactVCenteredU v n)
  have hconstant := hasDerivAt_const x
    (4 * lambda * (1 - lrCompactVScore R n))
  have h := (hvariable.add hconstant).const_mul (lrLowA n)
  convert h using 1
  · funext q
    simp only [lrCompactVLambdaCenteredPolynomialTerm,
      Pi.add_apply, Pi.mul_apply, Pi.pow_apply, id_eq]
    ring
  · simp only [lrCompactVLambdaCenteredPolynomialTermX,
      id_eq, mul_one, add_zero]
    ring

theorem hasDerivAt_lrCompactVLambdaCenteredPolynomialTermV_v
    (lambda R v x : ℝ) (n : ℕ) :
    HasDerivAt
      (fun q ↦ lrCompactVLambdaCenteredPolynomialTermV lambda R q x n)
      (lrCompactVLambdaCenteredPolynomialTermVV lambda R v x n) v := by
  have hU := hasDerivAt_lrCompactVCenteredUDeriv v n
  have h := hU.const_mul
    (lrLowA n * lrCompactVLambdaCenteredA lambda R n * x ^ n)
  convert h using 1 <;>
    simp [lrCompactVLambdaCenteredPolynomialTermV,
      lrCompactVLambdaCenteredPolynomialTermVV] <;> ring

theorem hasDerivAt_lrCompactVLambdaCenteredPolynomialTermV_x
    (lambda R v x : ℝ) (n : ℕ) :
    HasDerivAt
      (fun q ↦ lrCompactVLambdaCenteredPolynomialTermV lambda R v q n)
      (lrCompactVLambdaCenteredPolynomialTermVX lambda R v x n) x := by
  have hpower := (hasDerivAt_id x).pow n
  have h := hpower.const_mul
    (lrLowA n * lrCompactVLambdaCenteredA lambda R n *
      lrCompactVCenteredUDeriv v n)
  convert h using 1
  · funext q
    simp only [lrCompactVLambdaCenteredPolynomialTermV,
      Pi.mul_apply, Pi.pow_apply, id_eq]
    ring
  · simp only [lrCompactVLambdaCenteredPolynomialTermVX,
      id_eq, mul_one]
    ring

theorem hasDerivAt_lrCompactVLambdaCenteredPolynomialTermX_v
    (lambda R v x : ℝ) (n : ℕ) :
    HasDerivAt
      (fun q ↦ lrCompactVLambdaCenteredPolynomialTermX lambda R q x n)
      (lrCompactVLambdaCenteredPolynomialTermVX lambda R v x n) v := by
  have hU := hasDerivAt_lrCompactVCenteredU v n
  have h := hU.const_mul
    (lrLowA n * lrCompactVLambdaCenteredA lambda R n *
      (n : ℝ) * x ^ (n - 1))
  convert h using 1 <;>
    simp [lrCompactVLambdaCenteredPolynomialTermX,
      lrCompactVLambdaCenteredPolynomialTermVX] <;> ring

theorem hasDerivAt_lrCompactVLambdaCenteredPolynomialTermX_x
    (lambda R v x : ℝ) (n : ℕ) :
    HasDerivAt
      (fun q ↦ lrCompactVLambdaCenteredPolynomialTermX lambda R v q n)
      (lrCompactVLambdaCenteredPolynomialTermXX lambda R v x n) x := by
  have hpower := (hasDerivAt_id x).pow (n - 1)
  have h := hpower.const_mul
    (lrLowA n * lrCompactVLambdaCenteredA lambda R n *
      (n : ℝ) * lrCompactVCenteredU v n)
  convert h using 1
  · funext q
    simp only [lrCompactVLambdaCenteredPolynomialTermX,
      Pi.mul_apply, Pi.pow_apply, id_eq]
    ring
  · simp only [lrCompactVLambdaCenteredPolynomialTermXX,
      id_eq, mul_one, Nat.cast_mul,
      show n - 1 - 1 = n - 2 by omega]
    ring

theorem hasDerivAt_lrCompactVLambdaCenteredPolynomialFinite_v
    (N : ℕ) (lambda R v x : ℝ) :
    HasDerivAt
      (fun q ↦ lrCompactVLambdaCenteredPolynomialFinite N lambda R q x)
      (lrCompactVLambdaCenteredPolynomialV N lambda R v x) v := by
  have hsum := HasDerivAt.fun_sum (u := Finset.range N) fun j _ ↦
    hasDerivAt_lrCompactVLambdaCenteredPolynomialTerm_v
      lambda R v x (j + 1)
  have hend := (hasDerivAt_id v).mul_const
    (4 * x * lrWKernel R 1)
  convert hsum.sub hend using 1
  · funext q
    simp only [lrCompactVLambdaCenteredPolynomialFinite,
      lrCompactVLambdaCenteredPolynomialHead,
      Pi.sub_apply, Pi.mul_apply, id_eq]
    ring
  · simp only [lrCompactVLambdaCenteredPolynomialV, one_mul]

theorem hasDerivAt_lrCompactVLambdaCenteredPolynomialFinite_x
    (N : ℕ) (lambda R v x : ℝ) :
    HasDerivAt
      (fun q ↦ lrCompactVLambdaCenteredPolynomialFinite N lambda R v q)
      (lrCompactVLambdaCenteredPolynomialX N lambda R v x) x := by
  have hsum := HasDerivAt.fun_sum (u := Finset.range N) fun j _ ↦
    hasDerivAt_lrCompactVLambdaCenteredPolynomialTerm_x
      lambda R v x (j + 1)
  have hend := (hasDerivAt_id x).mul_const
    (4 * v * lrWKernel R 1)
  convert hsum.sub hend using 1
  · funext q
    simp only [lrCompactVLambdaCenteredPolynomialFinite,
      lrCompactVLambdaCenteredPolynomialHead,
      Pi.sub_apply, Pi.mul_apply, id_eq]
    ring
  · simp only [lrCompactVLambdaCenteredPolynomialX, one_mul]

theorem hasDerivAt_lrCompactVLambdaCenteredPolynomialV_v
    (N : ℕ) (lambda R v x : ℝ) :
    HasDerivAt
      (fun q ↦ lrCompactVLambdaCenteredPolynomialV N lambda R q x)
      (lrCompactVLambdaCenteredPolynomialVV N lambda R v x) v := by
  have hsum := HasDerivAt.fun_sum (u := Finset.range N) fun j _ ↦
    hasDerivAt_lrCompactVLambdaCenteredPolynomialTermV_v
      lambda R v x (j + 1)
  change HasDerivAt
    (fun q ↦
      (∑ j ∈ Finset.range N,
        lrCompactVLambdaCenteredPolynomialTermV
          lambda R q x (j + 1)) - 4 * x * lrWKernel R 1)
    (∑ j ∈ Finset.range N,
      lrCompactVLambdaCenteredPolynomialTermVV
        lambda R v x (j + 1)) v
  simpa only [Pi.sub_apply, sub_zero] using
    hsum.sub (hasDerivAt_const v (4 * x * lrWKernel R 1))

theorem hasDerivAt_lrCompactVLambdaCenteredPolynomialV_x
    (N : ℕ) (lambda R v x : ℝ) :
    HasDerivAt
      (fun q ↦ lrCompactVLambdaCenteredPolynomialV N lambda R v q)
      (lrCompactVLambdaCenteredPolynomialVX N lambda R v x) x := by
  have hsum := HasDerivAt.fun_sum (u := Finset.range N) fun j _ ↦
    hasDerivAt_lrCompactVLambdaCenteredPolynomialTermV_x
      lambda R v x (j + 1)
  have hend := (hasDerivAt_id x).mul_const (4 * lrWKernel R 1)
  convert hsum.sub hend using 1
  · funext q
    simp only [lrCompactVLambdaCenteredPolynomialV,
      Pi.sub_apply, Pi.mul_apply, id_eq]
    ring
  · simp only [lrCompactVLambdaCenteredPolynomialVX, one_mul]

theorem hasDerivAt_lrCompactVLambdaCenteredPolynomialX_v
    (N : ℕ) (lambda R v x : ℝ) :
    HasDerivAt
      (fun q ↦ lrCompactVLambdaCenteredPolynomialX N lambda R q x)
      (lrCompactVLambdaCenteredPolynomialVX N lambda R v x) v := by
  have hsum := HasDerivAt.fun_sum (u := Finset.range N) fun j _ ↦
    hasDerivAt_lrCompactVLambdaCenteredPolynomialTermX_v
      lambda R v x (j + 1)
  have hend := (hasDerivAt_id v).mul_const (4 * lrWKernel R 1)
  convert hsum.sub hend using 1
  · funext q
    simp only [lrCompactVLambdaCenteredPolynomialX,
      Pi.sub_apply, Pi.mul_apply, id_eq]
    ring
  · simp only [lrCompactVLambdaCenteredPolynomialVX, one_mul]

theorem hasDerivAt_lrCompactVLambdaCenteredPolynomialX_x
    (N : ℕ) (lambda R v x : ℝ) :
    HasDerivAt
      (fun q ↦ lrCompactVLambdaCenteredPolynomialX N lambda R v q)
      (lrCompactVLambdaCenteredPolynomialXX N lambda R v x) x := by
  have hsum := HasDerivAt.fun_sum (u := Finset.range N) fun j _ ↦
    hasDerivAt_lrCompactVLambdaCenteredPolynomialTermX_x
      lambda R v x (j + 1)
  change HasDerivAt
    (fun q ↦
      (∑ j ∈ Finset.range N,
        lrCompactVLambdaCenteredPolynomialTermX
          lambda R v q (j + 1)) - 4 * v * lrWKernel R 1)
    (∑ j ∈ Finset.range N,
      lrCompactVLambdaCenteredPolynomialTermXX
        lambda R v x (j + 1)) x
  simpa only [Pi.sub_apply, sub_zero] using
    hsum.sub (hasDerivAt_const x (4 * v * lrWKernel R 1))

end CourtadeKumar
