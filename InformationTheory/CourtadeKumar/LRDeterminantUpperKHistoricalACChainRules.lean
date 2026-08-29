import InformationTheory.CourtadeKumar.LRDeterminantUpperKReplayEvaluator

/-!
# Real chain rules for the historical sharp `A/C` upper-`K` nodes

This file isolates the real-variable calculus behind the derivative fields in
`LRUpperKHistoricalACAD`.  Put

* `A_s(y) = aPrimitive s y`,
* `C_s(y) = cPrimitive s y = A_s(y) - Q(y)`,
* `F_s(y) = s * (Q''(s) - (1-y)^2 * Q''(b_s(y)))`, and
* `M_s(y) = Q'(b_s(y)) - s*(1-s)*(1-y)*Q''(b_s(y))`.

Then, along an arbitrary differentiable path `(s,y)` with velocity `(s',y')`,

`A' = s' * F_s(y) + M_s(y) * y'`

and

`C' = s' * F_s(y) + M_s(y) * y' - Q'(y) * y'`.

The remaining theorems specialize these identities to
`e = s^2*K` and `y0 = e*h^2`.  The `h` specialization is intentionally stated
only for `0 < h < 1`.  On that open chart it also identifies the ordinary
chain-rule term `Q'(y0) * 2*h*e` with the historical regularized expression
`2*sqrt(e)*(sqrt(y0)*Q'(y0))`.  No endpoint differentiability assertion at
`h = 0` is made here.
-/

open Set

namespace CourtadeKumar
namespace LRUpperKHistoricalACChainRules

open LRUpperKReplayCertificate

/-! ## The two scalar derivative components -/

/-- The derivative of `A_s(y)` with respect to `s` while `y` is fixed. -/
noncomputable def fixedYPartialS (s y : ℝ) : ℝ :=
  s * (lrCertificateQSecond s -
    (1 - y) ^ 2 * lrCertificateQSecond (lrCertificateB s y))

/-- The coefficient of the moving-`y` derivative in `A_s(y)`. -/
noncomputable def movingYCoefficient (s y : ℝ) : ℝ :=
  lrCertificateQPrime (lrCertificateB s y) -
    s * (1 - s) * (1 - y) *
      lrCertificateQSecond (lrCertificateB s y)

/-- Exact algebraic decomposition used by every sharp `A` partial. -/
theorem aPrimitiveDeriv_eq_fixed_add_moving
    (s y s' y' : ℝ) :
    aPrimitiveDeriv s y s' y' =
      s' * fixedYPartialS s y + movingYCoefficient s y * y' := by
  unfold aPrimitiveDeriv fixedYPartialS movingYCoefficient
    lrCertificateOmegaDeriv lrCertificateBDeriv lrCertificateB
  dsimp only
  simp only [mul_zero, add_zero, sub_zero, neg_zero, zero_mul, one_mul]
  ring

/-- Exact algebraic decomposition used by every sharp `C` partial. -/
theorem cPrimitiveDeriv_eq_fixed_add_moving_sub_q
    (s y s' y' : ℝ) :
    cPrimitiveDeriv s y s' y' =
      s' * fixedYPartialS s y + movingYCoefficient s y * y' -
        lrCertificateQPrime y * y' := by
  unfold cPrimitiveDeriv fixedYPartialS movingYCoefficient
    lrCertificateOmegaDeriv lrCertificateBDeriv lrCertificateB
  dsimp only
  simp only [mul_zero, add_zero, sub_zero, neg_zero, zero_mul, one_mul]
  ring

/-! ## Calculus along an arbitrary path -/

/-- Differentiability of `A` along a path, with its derivative already put in
the historical `fixed + moving` form. -/
theorem hasDerivAt_aPrimitive_along_decomposed
    {z s y s' y' : ℝ} {sfun yfun : ℝ → ℝ}
    (hs : HasDerivAt sfun s' z) (hy : HasDerivAt yfun y' z)
    (hsz : sfun z = s) (hyz : yfun z = y)
    (hsMem : s ∈ Ioo (0 : ℝ) 1) (hyMem : y ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun q ↦ aPrimitive (sfun q) (yfun q))
      (s' * fixedYPartialS s y + movingYCoefficient s y * y') z := by
  have hyMem' : yfun z ∈ Ioo (0 : ℝ) 1 := by
    simpa only [hyz] using hyMem
  have hq := (hasDerivAt_lrCertificateQ hyMem').comp z hy
  have homega := hasDerivAt_lrCertificateOmega_along
    hs hy hsz hyz hsMem hyMem
  have hzero := hasDerivAt_lrCertificateOmega_zero_along hs hsz hsMem
  have h := (hq.add homega).sub hzero
  have hraw :
      HasDerivAt (fun q ↦ aPrimitive (sfun q) (yfun q))
        (aPrimitiveDeriv s y s' y') z := by
    convert h using 1
    rw [aPrimitiveDeriv_identity, hyz]
  simpa only [aPrimitiveDeriv_eq_fixed_add_moving] using hraw

/-- Differentiability of `C` along a path, with the `Q` derivative visibly
subtracted from the corresponding `A` derivative. -/
theorem hasDerivAt_cPrimitive_along_decomposed
    {z s y s' y' : ℝ} {sfun yfun : ℝ → ℝ}
    (hs : HasDerivAt sfun s' z) (hy : HasDerivAt yfun y' z)
    (hsz : sfun z = s) (hyz : yfun z = y)
    (hsMem : s ∈ Ioo (0 : ℝ) 1) (hyMem : y ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun q ↦ cPrimitive (sfun q) (yfun q))
      (s' * fixedYPartialS s y + movingYCoefficient s y * y' -
        lrCertificateQPrime y * y') z := by
  have homega := hasDerivAt_lrCertificateOmega_along
    hs hy hsz hyz hsMem hyMem
  have hzero := hasDerivAt_lrCertificateOmega_zero_along hs hsz hsMem
  have h := homega.sub hzero
  have hraw :
      HasDerivAt (fun q ↦ cPrimitive (sfun q) (yfun q))
        (cPrimitiveDeriv s y s' y') z := by
    simpa [cPrimitive] using h
  simpa only [cPrimitiveDeriv_eq_fixed_add_moving_sub_q] using hraw

/-! ## The `(s,K,h)` chart and its exact coordinate velocities -/

def chartE (s K : ℝ) : ℝ := s ^ 2 * K

def chartY0 (s K h : ℝ) : ℝ := chartE s K * h ^ 2

noncomputable def chartEPartialS (s K : ℝ) : ℝ := 2 * chartE s K / s

noncomputable def chartEPartialK (s K : ℝ) : ℝ := chartE s K / K

noncomputable def chartY0PartialS (s K h : ℝ) : ℝ :=
  2 * chartY0 s K h / s

noncomputable def chartY0PartialK (s K h : ℝ) : ℝ :=
  chartY0 s K h / K

def chartY0PartialH (s K h : ℝ) : ℝ :=
  2 * h * chartE s K

theorem hasDerivAt_chartE_s {s K : ℝ} (hs : s ≠ 0) :
    HasDerivAt (fun q ↦ chartE q K) (chartEPartialS s K) s := by
  have hsq : HasDerivAt (fun q : ℝ ↦ q ^ 2) (2 * s) s := by
    simpa [mul_comm] using (hasDerivAt_id s).pow 2
  have hraw := hsq.mul_const K
  convert hraw using 1
  unfold chartEPartialS chartE
  field_simp [hs]

theorem hasDerivAt_chartE_K {s K : ℝ} (hK : K ≠ 0) :
    HasDerivAt (fun q ↦ chartE s q) (chartEPartialK s K) K := by
  have hraw := (hasDerivAt_id K).const_mul (s ^ 2)
  convert hraw using 1
  unfold chartEPartialK chartE
  field_simp [hK]

theorem hasDerivAt_chartY0_s {s K h : ℝ} (hs : s ≠ 0) :
    HasDerivAt (fun q ↦ chartY0 q K h)
      (chartY0PartialS s K h) s := by
  have he := hasDerivAt_chartE_s (K := K) hs
  have hraw := he.mul_const (h ^ 2)
  convert hraw using 1
  unfold chartY0PartialS chartY0 chartEPartialS
  field_simp [hs]

theorem hasDerivAt_chartY0_K {s K h : ℝ} (hK : K ≠ 0) :
    HasDerivAt (fun q ↦ chartY0 s q h)
      (chartY0PartialK s K h) K := by
  have he := hasDerivAt_chartE_K (s := s) hK
  have hraw := he.mul_const (h ^ 2)
  convert hraw using 1
  unfold chartY0PartialK chartY0 chartEPartialK
  field_simp [hK]

/-- The `h` derivative is only used on the open chart `0 < h < 1`. -/
theorem hasDerivAt_chartY0_h {s K h : ℝ} (hh : h ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun q ↦ chartY0 s K q)
      (chartY0PartialH s K h) h := by
  have hsq : HasDerivAt (fun q : ℝ ↦ q ^ 2) (2 * h) h := by
    simpa [mul_comm] using (hasDerivAt_id h).pow 2
  have hraw := hsq.const_mul (chartE s K)
  convert hraw using 1
  unfold chartY0PartialH
  ring

/-! ## Explicit regularized `Q(y0)` partial in the `h` coordinate -/

noncomputable def qY0PartialS (s K h : ℝ) : ℝ :=
  lrCertificateQPrime (chartY0 s K h) * chartY0PartialS s K h

noncomputable def qY0PartialK (s K h : ℝ) : ℝ :=
  lrCertificateQPrime (chartY0 s K h) * chartY0PartialK s K h

noncomputable def qY0PartialH (s K h : ℝ) : ℝ :=
  lrCertificateQPrime (chartY0 s K h) * chartY0PartialH s K h

/-- The exact expression evaluated by the historical regularized `h` node. -/
noncomputable def qY0PartialHRegularized (s K h : ℝ) : ℝ :=
  2 * Real.sqrt (chartE s K) *
    (Real.sqrt (chartY0 s K h) *
      lrCertificateQPrime (chartY0 s K h))

theorem sqrt_chartY0 {s K h : ℝ}
    (he : 0 ≤ chartE s K) (hh : h ∈ Ioo (0 : ℝ) 1) :
    Real.sqrt (chartY0 s K h) = Real.sqrt (chartE s K) * h := by
  unfold chartY0
  rw [Real.sqrt_mul he, Real.sqrt_sq_eq_abs, abs_of_pos hh.1]

/-- On `0 < h < 1`, the singular-looking ordinary chain-rule product is
exactly the finite regularized product used by the interval checker. -/
theorem qY0PartialH_eq_regularized {s K h : ℝ}
    (he : 0 ≤ chartE s K) (hh : h ∈ Ioo (0 : ℝ) 1) :
    qY0PartialH s K h = qY0PartialHRegularized s K h := by
  have hsqrt := sqrt_chartY0 he hh
  have hsqrtSq : Real.sqrt (chartE s K) ^ 2 = chartE s K :=
    Real.sq_sqrt he
  unfold qY0PartialH qY0PartialHRegularized chartY0PartialH
  rw [hsqrt]
  calc
    lrCertificateQPrime (chartY0 s K h) * (2 * h * chartE s K) =
        chartE s K *
          (2 * h * lrCertificateQPrime (chartY0 s K h)) := by ring
    _ = Real.sqrt (chartE s K) ^ 2 *
          (2 * h * lrCertificateQPrime (chartY0 s K h)) := by
      rw [hsqrtSq]
    _ = 2 * Real.sqrt (chartE s K) *
          (Real.sqrt (chartE s K) * h *
            lrCertificateQPrime (chartY0 s K h)) := by ring

/-! ## `A/C` partials at `y0 = s^2*K*h^2` -/

theorem hasDerivAt_aY0_s {s K h : ℝ}
    (hs : s ∈ Ioo (0 : ℝ) 1)
    (hy : chartY0 s K h ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun q ↦ aPrimitive q (chartY0 q K h))
      (fixedYPartialS s (chartY0 s K h) +
        movingYCoefficient s (chartY0 s K h) *
          chartY0PartialS s K h) s := by
  have h := hasDerivAt_aPrimitive_along_decomposed
    (hasDerivAt_id s) (hasDerivAt_chartY0_s (K := K) (h := h) hs.1.ne')
    rfl rfl hs hy
  simpa using h

theorem hasDerivAt_cY0_s {s K h : ℝ}
    (hs : s ∈ Ioo (0 : ℝ) 1)
    (hy : chartY0 s K h ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun q ↦ cPrimitive q (chartY0 q K h))
      (fixedYPartialS s (chartY0 s K h) +
        movingYCoefficient s (chartY0 s K h) *
          chartY0PartialS s K h - qY0PartialS s K h) s := by
  have h := hasDerivAt_cPrimitive_along_decomposed
    (hasDerivAt_id s) (hasDerivAt_chartY0_s (K := K) (h := h) hs.1.ne')
    rfl rfl hs hy
  simpa [qY0PartialS] using h

theorem hasDerivAt_aY0_K {s K h : ℝ}
    (hs : s ∈ Ioo (0 : ℝ) 1) (hK : 0 < K)
    (hy : chartY0 s K h ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun q ↦ aPrimitive s (chartY0 s q h))
      (movingYCoefficient s (chartY0 s K h) *
        chartY0PartialK s K h) K := by
  have h := hasDerivAt_aPrimitive_along_decomposed
    (hasDerivAt_const K s)
    (hasDerivAt_chartY0_K (s := s) (h := h) hK.ne')
    rfl rfl hs hy
  simpa using h

theorem hasDerivAt_cY0_K {s K h : ℝ}
    (hs : s ∈ Ioo (0 : ℝ) 1) (hK : 0 < K)
    (hy : chartY0 s K h ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun q ↦ cPrimitive s (chartY0 s q h))
      (movingYCoefficient s (chartY0 s K h) *
        chartY0PartialK s K h - qY0PartialK s K h) K := by
  have h := hasDerivAt_cPrimitive_along_decomposed
    (hasDerivAt_const K s)
    (hasDerivAt_chartY0_K (s := s) (h := h) hK.ne')
    rfl rfl hs hy
  simpa [qY0PartialK] using h

theorem hasDerivAt_aY0_h {s K h : ℝ}
    (hs : s ∈ Ioo (0 : ℝ) 1) (hh : h ∈ Ioo (0 : ℝ) 1)
    (hy : chartY0 s K h ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun q ↦ aPrimitive s (chartY0 s K q))
      (movingYCoefficient s (chartY0 s K h) *
        chartY0PartialH s K h) h := by
  have hderiv := hasDerivAt_aPrimitive_along_decomposed
    (hasDerivAt_const h s) (hasDerivAt_chartY0_h (s := s) (K := K) hh)
    rfl rfl hs hy
  simpa using hderiv

/-- Positive-`h` derivative of `C(y0)`, in precisely the regularized form
enclosed by `qPartialHI`. -/
theorem hasDerivAt_cY0_h_regularized {s K h : ℝ}
    (hs : s ∈ Ioo (0 : ℝ) 1) (hK : 0 < K)
    (hh : h ∈ Ioo (0 : ℝ) 1)
    (hy : chartY0 s K h ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun q ↦ cPrimitive s (chartY0 s K q))
      (movingYCoefficient s (chartY0 s K h) *
        chartY0PartialH s K h - qY0PartialHRegularized s K h) h := by
  have hderiv := hasDerivAt_cPrimitive_along_decomposed
    (hasDerivAt_const h s) (hasDerivAt_chartY0_h (s := s) (K := K) hh)
    rfl rfl hs hy
  have he : 0 ≤ chartE s K := by
    simpa only [chartE] using (mul_pos (sq_pos_of_pos hs.1) hK).le
  rw [← qY0PartialH_eq_regularized he hh]
  simpa [qY0PartialH] using hderiv

/-! ## The parallel `e = s^2*K` branch -/

noncomputable def qEPartialS (s K : ℝ) : ℝ :=
  lrCertificateQPrime (chartE s K) * chartEPartialS s K

noncomputable def qEPartialK (s K : ℝ) : ℝ :=
  lrCertificateQPrime (chartE s K) * chartEPartialK s K

theorem hasDerivAt_aE_s {s K : ℝ}
    (hs : s ∈ Ioo (0 : ℝ) 1)
    (he : chartE s K ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun q ↦ aPrimitive q (chartE q K))
      (fixedYPartialS s (chartE s K) +
        movingYCoefficient s (chartE s K) * chartEPartialS s K) s := by
  have h := hasDerivAt_aPrimitive_along_decomposed
    (hasDerivAt_id s) (hasDerivAt_chartE_s (K := K) hs.1.ne')
    rfl rfl hs he
  simpa using h

theorem hasDerivAt_cE_s {s K : ℝ}
    (hs : s ∈ Ioo (0 : ℝ) 1)
    (he : chartE s K ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun q ↦ cPrimitive q (chartE q K))
      (fixedYPartialS s (chartE s K) +
        movingYCoefficient s (chartE s K) * chartEPartialS s K -
          qEPartialS s K) s := by
  have h := hasDerivAt_cPrimitive_along_decomposed
    (hasDerivAt_id s) (hasDerivAt_chartE_s (K := K) hs.1.ne')
    rfl rfl hs he
  simpa [qEPartialS] using h

theorem hasDerivAt_aE_K {s K : ℝ}
    (hs : s ∈ Ioo (0 : ℝ) 1) (hK : 0 < K)
    (he : chartE s K ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun q ↦ aPrimitive s (chartE s q))
      (movingYCoefficient s (chartE s K) * chartEPartialK s K) K := by
  have h := hasDerivAt_aPrimitive_along_decomposed
    (hasDerivAt_const K s) (hasDerivAt_chartE_K (s := s) hK.ne')
    rfl rfl hs he
  simpa using h

theorem hasDerivAt_cE_K {s K : ℝ}
    (hs : s ∈ Ioo (0 : ℝ) 1) (hK : 0 < K)
    (he : chartE s K ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun q ↦ cPrimitive s (chartE s q))
      (movingYCoefficient s (chartE s K) * chartEPartialK s K -
        qEPartialK s K) K := by
  have h := hasDerivAt_cPrimitive_along_decomposed
    (hasDerivAt_const K s) (hasDerivAt_chartE_K (s := s) hK.ne')
    rfl rfl hs he
  simpa [qEPartialK] using h

/-- Both `e` primitives are constant in the third chart coordinate. -/
theorem hasDerivAt_aE_h (s K h : ℝ) :
    HasDerivAt (fun _q : ℝ ↦ aPrimitive s (chartE s K)) 0 h :=
  hasDerivAt_const h _

theorem hasDerivAt_cE_h (s K h : ℝ) :
    HasDerivAt (fun _q : ℝ ↦ cPrimitive s (chartE s K)) 0 h :=
  hasDerivAt_const h _

end LRUpperKHistoricalACChainRules
end CourtadeKumar
