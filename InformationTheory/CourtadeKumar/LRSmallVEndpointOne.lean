import InformationTheory.CourtadeKumar.LRSmallVEndpointDerivative

/-!
# The terminal value of the small-odds endpoint envelope

At `t = 1` the endpoint envelope is an elementary one-variable function.
Its derivative is nonpositive on `v ≤ 1/3`, and its value at `1/3` is
exactly zero.
-/

open Set

namespace CourtadeKumar

noncomputable def lrSmallVEndpointOne (v : ℝ) : ℝ :=
  Real.log (1 + v) - Real.log 2 - Real.log v -
    (1 - v) / v * Real.artanh v

lemma lrLowVStarEnvelopeActual_one
    {v : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1) :
    lrLowVStarEnvelopeActual v 1 = lrSmallVEndpointOne v := by
  have hfull : v ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hv.1], hv.2⟩
  have hp : 1 + v ≠ 0 := by linarith [hv.1]
  have hm : 1 - v ≠ 0 := by linarith [hv.2]
  have hv0 : v ≠ 0 := hv.1.ne'
  unfold lrLowVStarEnvelopeActual lrSmallVEndpointOne lrGShape
  rw [lrFlowA_at_one_eq_artanh hv, topPhi_one]
  norm_num only [mul_one, one_pow]
  rw [topPhi_eq_mul_artanh_add_log hfull]
  unfold lrG
  rw [Real.artanh_eq_half_log ⟨hfull.1.le, hfull.2.le⟩,
    Real.log_div hp hm,
    show 1 - v ^ 2 = (1 + v) * (1 - v) by ring,
    Real.log_mul hp hm]
  field_simp [hv0, hp, hm]
  ring

theorem hasDerivAt_lrSmallVEndpointOne
    {v : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt lrSmallVEndpointOne
      ((Real.artanh v - 2 * v / (1 + v)) / v ^ 2) v := by
  have hv0 : v ≠ 0 := hv.1.ne'
  have hp : 1 + v ≠ 0 := by linarith [hv.1]
  have hart := hasDerivAt_artanh
    (show v ∈ Ioo (-1 : ℝ) 1 from ⟨by linarith [hv.1], hv.2⟩)
  have hlogPlus : HasDerivAt (fun x : ℝ ↦ Real.log (1 + x))
      (1 / (1 + v)) v := by
    have harg := (hasDerivAt_const v 1).add (hasDerivAt_id v)
    simpa only [Pi.add_apply, id_eq, zero_add] using harg.log hp
  have hlogV := (hasDerivAt_id v).log hv0
  have hcoef : HasDerivAt (fun x : ℝ ↦ (1 - x) / x)
      (-1 / v ^ 2) v := by
    have hnum := (hasDerivAt_const v 1).sub (hasDerivAt_id v)
    convert hnum.div (hasDerivAt_id v) hv0 using 1 <;>
      simp only [id_eq, Pi.sub_apply] <;> field_simp [hv0] <;> ring
  have h := ((hlogPlus.sub_const (Real.log 2)).sub hlogV).sub
    (hcoef.mul hart)
  unfold lrSmallVEndpointOne
  convert h using 1
  simp only [id_eq]
  have hden : 1 - v ^ 2 ≠ 0 := by nlinarith [hv.1, hv.2]
  field_simp [hv0, hp, hden]
  ring

theorem lrSmallVEndpointOne_deriv_nonpos
    {v : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1) (hvSmall : v ≤ 1 / 3) :
    deriv lrSmallVEndpointOne v ≤ 0 := by
  rw [(hasDerivAt_lrSmallVEndpointOne hv).deriv]
  have hart := artanh_le_cubicPade
    (show v ∈ Icc (0 : ℝ) (1 / 3) from ⟨hv.1.le, hvSmall⟩)
  have htarget : Real.artanh v ≤ 2 * v / (1 + v) := by
    have hdenA : 0 < 3 * (1 - v ^ 2) := by
      nlinarith [sq_nonneg v,
        mul_nonneg (sub_nonneg.mpr hvSmall) (by linarith [hv.1] : 0 ≤ 1 / 3 + v)]
    have hdenV : 0 < 1 + v := by linarith [hv.1]
    have hdenBase : 1 - v ^ 2 ≠ 0 := by nlinarith [hv.1, hv.2]
    have hcubic : v + v ^ 3 / (3 * (1 - v ^ 2)) ≤
        2 * v / (1 + v) := by
      have hpoly : 0 ≤ 2 * v ^ 2 - 6 * v + 3 := by
        nlinarith [sq_nonneg v]
      have hid :
          2 * v / (1 + v) - (v + v ^ 3 / (3 * (1 - v ^ 2))) =
            v * (2 * v ^ 2 - 6 * v + 3) / (3 * (1 - v ^ 2)) := by
        field_simp [hdenV.ne', hdenBase]
        ring
      rw [← sub_nonneg, hid]
      exact div_nonneg (mul_nonneg hv.1.le hpoly) hdenA.le
    exact hart.trans hcubic
  exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr htarget) (sq_nonneg v)

lemma lrSmallVEndpointOne_one_third :
    lrSmallVEndpointOne (1 / 3 : ℝ) = 0 := by
  have hv : (1 / 3 : ℝ) ∈ Icc (-1 : ℝ) 1 := by norm_num
  unfold lrSmallVEndpointOne
  rw [Real.artanh_eq_half_log hv,
    show 1 + (1 / 3 : ℝ) = 4 / 3 by ring,
    show 1 - (1 / 3 : ℝ) = 2 / 3 by ring]
  norm_num
  rw [
    Real.log_div (by norm_num : (4 : ℝ) ≠ 0) (by norm_num),
    Real.log_div (by norm_num : (1 : ℝ) ≠ 0) (by norm_num),
    Real.log_one, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
  norm_num
  ring

theorem lrSmallVEndpointOne_nonneg
    {v : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1) (hvSmall : v ≤ 1 / 3) :
    0 ≤ lrSmallVEndpointOne v := by
  have hanti : AntitoneOn lrSmallVEndpointOne (Icc v (1 / 3 : ℝ)) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc v (1 / 3 : ℝ))
    · intro x hx
      have hxMem : x ∈ Ioo (0 : ℝ) 1 :=
        ⟨hv.1.trans_le hx.1, hx.2.trans_lt (by norm_num)⟩
      exact (hasDerivAt_lrSmallVEndpointOne hxMem).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      exact (hasDerivAt_lrSmallVEndpointOne
        ⟨hv.1.trans hx.1, hx.2.trans (by norm_num)⟩).differentiableAt
          |>.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      exact lrSmallVEndpointOne_deriv_nonpos
        ⟨hv.1.trans hx.1, hx.2.trans (by norm_num)⟩ hx.2.le
  have hcompare := hanti
    (show v ∈ Icc v (1 / 3 : ℝ) from ⟨le_rfl, hvSmall⟩)
    (show (1 / 3 : ℝ) ∈ Icc v (1 / 3 : ℝ) from ⟨hvSmall, le_rfl⟩)
    hvSmall
  rw [lrSmallVEndpointOne_one_third] at hcompare
  exact hcompare

end CourtadeKumar
