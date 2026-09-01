import InformationTheory.CourtadeKumar.LRCertificateQSecondMonotonicity
import InformationTheory.CourtadeKumar.LRDeterminantUpperKReplayEvaluator

noncomputable section

open Set

namespace CourtadeKumar
namespace LRUpperKReplayCertificate

/-!
This module derives the upper-`K` `A`/`C` monotonicity and corner rules from
`MonotoneOn lrCertificateQSecond (Ioo 0 1)`.  The imported curvature theorem
discharges that input, while the algebraic and one-variable-calculus reductions
remain explicit here.
-/

private def acB (s y : ℝ) : ℝ :=
  s + (1 - s) * y

private def acA (s y : ℝ) : ℝ :=
  lrCertificateQ (acB s y) -
    s * (1 - y) * lrCertificateQPrime (acB s y) -
    (lrCertificateQ s - s * lrCertificateQPrime s)

private def acC (s y : ℝ) : ℝ :=
  acA s y - lrCertificateQ y

private lemma acB_mem_Ioo
    {s y : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) (hy : y ∈ Ioo (0 : ℝ) 1) :
    acB s y ∈ Ioo (0 : ℝ) 1 := by
  constructor
  · have hnonneg : 0 ≤ (1 - s) * y :=
      mul_nonneg (sub_nonneg.mpr (le_of_lt hs.2)) (le_of_lt hy.1)
    simpa only [acB] using add_pos_of_pos_of_nonneg hs.1 hnonneg
  · have hpos : 0 < (1 - s) * (1 - y) :=
      mul_pos (sub_pos.mpr hs.2) (sub_pos.mpr hy.2)
    dsimp [acB]
    nlinarith

private lemma acB_mem_Ioo_of_Ico
    {s y : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) (hy : y ∈ Ico (0 : ℝ) 1) :
    acB s y ∈ Ioo (0 : ℝ) 1 := by
  constructor
  · have hnonneg : 0 ≤ (1 - s) * y :=
      mul_nonneg (sub_nonneg.mpr hs.2.le) hy.1
    simpa only [acB] using add_pos_of_pos_of_nonneg hs.1 hnonneg
  · have hpos : 0 < (1 - s) * (1 - y) :=
      mul_pos (sub_pos.mpr hs.2) (sub_pos.mpr hy.2)
    dsimp [acB]
    nlinarith

private lemma s_lt_acB
    {s y : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) (hy : y ∈ Ioo (0 : ℝ) 1) :
    s < acB s y := by
  have hpos : 0 < (1 - s) * y :=
    mul_pos (sub_pos.mpr hs.2) hy.1
  dsimp [acB]
  linarith

private lemma y_lt_acB
    {s y : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) (hy : y ∈ Ioo (0 : ℝ) 1) :
    y < acB s y := by
  have hpos : 0 < s * (1 - y) :=
    mul_pos hs.1 (sub_pos.mpr hy.2)
  dsimp [acB]
  nlinarith

private lemma aPrimitive_eq_acA (s y : ℝ) :
    aPrimitive s y = acA s y := by
  simp [aPrimitive, acA, lrCertificateOmega, lrCertificateB, acB]
  ring

private lemma cPrimitive_eq_acC (s y : ℝ) :
    cPrimitive s y = acC s y := by
  simp [cPrimitive, acC, acA, lrCertificateOmega, lrCertificateB, acB]
  ring

private lemma hasDerivAt_acB_s (s y : ℝ) :
    HasDerivAt (fun u => acB u y) (1 - y) s := by
  convert (hasDerivAt_id s).add
    (((hasDerivAt_const (x := s) (c := (1 : ℝ))).sub
      (hasDerivAt_id s)).mul_const y) using 1 <;>
    simp [acB] <;> ring

private lemma hasDerivAt_acB_y (s y : ℝ) :
    HasDerivAt (acB s) (1 - s) y := by
  convert
    (hasDerivAt_const (x := y) (c := s)).add
      ((hasDerivAt_id y).const_mul (1 - s)) using 1 <;>
    simp [acB] <;> ring

private lemma hasDerivAt_acA_s
    {s y : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) (hy : y ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun u => acA u y)
      (s * (lrCertificateQSecond s -
        (1 - y) ^ 2 * lrCertificateQSecond (acB s y))) s := by
  have hb : acB s y ∈ Ioo (0 : ℝ) 1 := acB_mem_Ioo hs hy
  have hB := hasDerivAt_acB_s s y
  have hQb := (hasDerivAt_lrCertificateQ hb).comp s hB
  have hQpb := (hasDerivAt_lrCertificateQPrime hb).comp s hB
  have hcoef := (hasDerivAt_id s).mul_const (1 - y)
  have hQs := hasDerivAt_lrCertificateQ hs
  have hsQps := (hasDerivAt_id s).mul (hasDerivAt_lrCertificateQPrime hs)
  convert (hQb.sub (hcoef.mul hQpb)).sub (hQs.sub hsQps) using 1 <;>
    simp [acA, acB] <;> ring

private lemma hasDerivAt_acA_y_closed
    {s y : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) (hy : y ∈ Ico (0 : ℝ) 1) :
    HasDerivAt (acA s)
      (lrCertificateQPrime (acB s y) -
        s * (1 - s) * (1 - y) * lrCertificateQSecond (acB s y)) y := by
  have hb : acB s y ∈ Ioo (0 : ℝ) 1 := acB_mem_Ioo_of_Ico hs hy
  have hB := hasDerivAt_acB_y s y
  have hQb := (hasDerivAt_lrCertificateQ hb).comp y hB
  have hQpb := (hasDerivAt_lrCertificateQPrime hb).comp y hB
  have hcoef :=
    (hasDerivAt_const (x := y) (c := s)).mul
      ((hasDerivAt_const (x := y) (c := (1 : ℝ))).sub (hasDerivAt_id y))
  convert
    (hQb.sub (hcoef.mul hQpb)).sub_const
      (lrCertificateQ s - s * lrCertificateQPrime s) using 1 <;>
    simp [acA, acB] <;> ring

private lemma hasDerivAt_acA_y
    {s y : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) (hy : y ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (acA s)
      (lrCertificateQPrime (acB s y) -
        s * (1 - s) * (1 - y) * lrCertificateQSecond (acB s y)) y :=
  hasDerivAt_acA_y_closed hs ⟨hy.1.le, hy.2⟩

private lemma hasDerivAt_acC_s
    {s y : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) (hy : y ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun u => acC u y)
      (s * (lrCertificateQSecond s -
        (1 - y) ^ 2 * lrCertificateQSecond (acB s y))) s := by
  simpa [acC] using (hasDerivAt_acA_s hs hy).sub_const (lrCertificateQ y)

private lemma hasDerivAt_acC_y
    {s y : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) (hy : y ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (acC s)
      (lrCertificateQPrime (acB s y) - lrCertificateQPrime y -
        s * (1 - s) * (1 - y) * lrCertificateQSecond (acB s y)) y := by
  change HasDerivAt (fun u => acA s u - lrCertificateQ u) _ y
  convert (hasDerivAt_acA_y hs hy).sub (hasDerivAt_lrCertificateQ hy) using 1 <;>
    ring

private lemma topPsiSlopeGap_pos
    {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    0 < topPsiSlopeGap x := by
  have hmono : StrictMonoOn topPsiSlopeGap (Icc (0 : ℝ) x) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc (0 : ℝ) x)
    · intro y hy
      have hyOpen : y ∈ Ioo (-1 : ℝ) 1 :=
        ⟨by linarith [hy.1], hy.2.trans_lt hx.2⟩
      exact
        (hasDerivAt_topPsiSlopeGap hyOpen).continuousAt.continuousWithinAt
    · intro y hy
      rw [interior_Icc] at hy
      have hyOpen : y ∈ Ioo (-1 : ℝ) 1 :=
        ⟨by linarith [hy.1], hy.2.trans hx.2⟩
      rw [(hasDerivAt_topPsiSlopeGap hyOpen).deriv]
      exact div_pos (mul_pos (by norm_num) (sq_pos_of_pos hy.1))
        (sq_pos_of_pos (by nlinarith [hyOpen.1, hyOpen.2]))
  have h := hmono
    (show (0 : ℝ) ∈ Icc 0 x from ⟨le_rfl, hx.1.le⟩)
    (show x ∈ Icc (0 : ℝ) x from ⟨hx.1.le, le_rfl⟩) hx.1
  simpa [topPsiSlopeGap] using h

private lemma qSecond_neg
    {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    lrCertificateQSecond x < 0 := by
  have hR : 1 - x ∈ Ioo (0 : ℝ) 1 := by
    constructor <;> linarith [hx.1, hx.2]
  have hz : Real.sqrt (1 - x) ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · exact Real.sqrt_pos.2 hR.1
    · simpa using (Real.sqrt_lt_sqrt_iff hR.1.le).2 hR.2
  have hden : 0 < 4 * Real.sqrt (1 - x) ^ 3 :=
    mul_pos (by norm_num) (pow_pos hz.1 3)
  unfold lrCertificateQSecond topPsiDeriv2
  exact neg_neg_of_pos (div_pos (topPsiSlopeGap_pos hz) hden)

private lemma qPrime_right_tangent
    (hQ2 : MonotoneOn lrCertificateQSecond (Ioo (0 : ℝ) 1))
    {x z : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1)
    (hz : z ∈ Ioo (0 : ℝ) 1) (hxz : x < z) :
    lrCertificateQPrime z - lrCertificateQPrime x ≤
      (z - x) * lrCertificateQSecond z := by
  have hmono : MonotoneOn lrCertificateQSecond (Icc x z) := by
    intro u hu v hv huv
    apply hQ2
    · exact ⟨lt_of_lt_of_le hx.1 hu.1, lt_of_le_of_lt hu.2 hz.2⟩
    · exact ⟨lt_of_lt_of_le hx.1 hv.1, lt_of_le_of_lt hv.2 hz.2⟩
    · exact huv
  have hconv : ConvexOn ℝ (Icc x z) lrCertificateQPrime := by
    apply MonotoneOn.convexOn_of_deriv (convex_Icc x z)
    · intro u hu
      have hu' : u ∈ Ioo (0 : ℝ) 1 :=
        ⟨lt_of_lt_of_le hx.1 hu.1, lt_of_le_of_lt hu.2 hz.2⟩
      exact (hasDerivAt_lrCertificateQPrime hu').continuousAt.continuousWithinAt
    · intro u hu
      have huClosed : u ∈ Icc x z := interior_subset hu
      have hu' : u ∈ Ioo (0 : ℝ) 1 :=
        ⟨lt_of_lt_of_le hx.1 huClosed.1,
          lt_of_le_of_lt huClosed.2 hz.2⟩
      exact (hasDerivAt_lrCertificateQPrime hu').differentiableAt.differentiableWithinAt
    · intro u hu v hv huv
      have huClosed : u ∈ Icc x z := interior_subset hu
      have hvClosed : v ∈ Icc x z := interior_subset hv
      have hu' : u ∈ Ioo (0 : ℝ) 1 :=
        ⟨lt_of_lt_of_le hx.1 huClosed.1,
          lt_of_le_of_lt huClosed.2 hz.2⟩
      have hv' : v ∈ Ioo (0 : ℝ) 1 :=
        ⟨lt_of_lt_of_le hx.1 hvClosed.1,
          lt_of_le_of_lt hvClosed.2 hz.2⟩
      rw [(hasDerivAt_lrCertificateQPrime hu').deriv,
        (hasDerivAt_lrCertificateQPrime hv').deriv]
      exact hmono huClosed hvClosed huv
  have hslope := hconv.slope_le_of_hasDerivAt
    (show x ∈ Icc x z from ⟨le_rfl, hxz.le⟩)
    (show z ∈ Icc x z from ⟨hxz.le, le_rfl⟩)
    hxz (hasDerivAt_lrCertificateQPrime hz)
  rw [slope_def_field, div_le_iff₀ (sub_pos.mpr hxz)] at hslope
  simpa only [mul_comm] using hslope

private lemma acA_s_deriv_neg
    (hQ2 : MonotoneOn lrCertificateQSecond (Ioo (0 : ℝ) 1))
    {s y : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) (hy : y ∈ Ioo (0 : ℝ) 1) :
    s * (lrCertificateQSecond s -
      (1 - y) ^ 2 * lrCertificateQSecond (acB s y)) < 0 := by
  have hb : acB s y ∈ Ioo (0 : ℝ) 1 := acB_mem_Ioo hs hy
  have hsb : s ≤ acB s y := le_of_lt (s_lt_acB hs hy)
  have hmono : lrCertificateQSecond s ≤ lrCertificateQSecond (acB s y) :=
    hQ2 hs hb hsb
  have hneg : lrCertificateQSecond (acB s y) < 0 := qSecond_neg hb
  have hsq : (1 - y) ^ 2 < (1 : ℝ) := by
    have hd0 : 0 < 1 - y := sub_pos.mpr hy.2
    have hd1 : 1 - y < 1 := sub_lt_self 1 hy.1
    nlinarith [sq_nonneg (1 - y)]
  have hscale :
      lrCertificateQSecond (acB s y) <
        (1 - y) ^ 2 * lrCertificateQSecond (acB s y) := by
    have := mul_lt_mul_of_neg_right hsq hneg
    simpa using this
  exact mul_neg_of_pos_of_neg hs.1 (sub_neg.mpr (lt_of_le_of_lt hmono hscale))

private lemma acA_y_deriv_pos
    {s y : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) (hy : y ∈ Ioo (0 : ℝ) 1) :
    0 < lrCertificateQPrime (acB s y) -
      s * (1 - s) * (1 - y) * lrCertificateQSecond (acB s y) := by
  have hb : acB s y ∈ Ioo (0 : ℝ) 1 := acB_mem_Ioo hs hy
  have hp : 0 < lrCertificateQPrime (acB s y) := lrCertificateQPrime_pos hb
  have hq : lrCertificateQSecond (acB s y) ≤ 0 :=
    lrCertificateQSecond_nonpos hb
  have hc : 0 ≤ s * (1 - s) * (1 - y) := by
    exact mul_nonneg
      (mul_nonneg hs.1.le (sub_nonneg.mpr hs.2.le))
      (sub_nonneg.mpr hy.2.le)
  have hprod := mul_nonpos_of_nonneg_of_nonpos hc hq
  linarith

private lemma acC_y_deriv_neg
    (hQ2 : MonotoneOn lrCertificateQSecond (Ioo (0 : ℝ) 1))
    {s y : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) (hy : y ∈ Ioo (0 : ℝ) 1) :
    lrCertificateQPrime (acB s y) - lrCertificateQPrime y -
      s * (1 - s) * (1 - y) * lrCertificateQSecond (acB s y) < 0 := by
  have hb : acB s y ∈ Ioo (0 : ℝ) 1 := acB_mem_Ioo hs hy
  have hyb : y < acB s y := y_lt_acB hs hy
  have ht := qPrime_right_tangent hQ2 hy hb hyb
  have hneg : lrCertificateQSecond (acB s y) < 0 := qSecond_neg hb
  calc
    lrCertificateQPrime (acB s y) - lrCertificateQPrime y -
        s * (1 - s) * (1 - y) * lrCertificateQSecond (acB s y)
        ≤ (acB s y - y) * lrCertificateQSecond (acB s y) -
            s * (1 - s) * (1 - y) * lrCertificateQSecond (acB s y) := by
          linarith
    _ = s ^ 2 * (1 - y) * lrCertificateQSecond (acB s y) := by
          dsimp [acB]
          ring
    _ < 0 := by
      exact mul_neg_of_pos_of_neg
        (mul_pos (sq_pos_of_pos hs.1) (sub_pos.mpr hy.2)) hneg

private lemma continuous_lrCertificateQ : Continuous lrCertificateQ := by
  rw [show lrCertificateQ = fun y : ℝ ↦
      Real.log 2 - topPhi (Real.sqrt (1 - y)) from
    funext lrCertificateQ_eq]
  exact continuous_const.sub
    (continuous_topPhi.comp
      (Real.continuous_sqrt.comp (continuous_const.sub continuous_id)))

/-- Conditional form of the historical rule: for fixed open-domain `y`, `A`
strictly decreases with `s`.  The only analytic input is monotonicity of `Q''`. -/
theorem aPrimitive_strictAntiOn_s_of_qSecond_monotone
    (hQ2 : MonotoneOn lrCertificateQSecond (Ioo (0 : ℝ) 1))
    {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    StrictAntiOn (fun s => aPrimitive s y) (Ioo (0 : ℝ) 1) := by
  rw [show (fun s => aPrimitive s y) = (fun s => acA s y) by
    funext s
    exact aPrimitive_eq_acA s y]
  apply strictAntiOn_of_deriv_neg (convex_Ioo (0 : ℝ) 1)
  · intro s hs
    exact (hasDerivAt_acA_s hs hy).continuousAt.continuousWithinAt
  · intro s hs
    rw [interior_Ioo] at hs
    rw [(hasDerivAt_acA_s hs hy).deriv]
    exact acA_s_deriv_neg hQ2 hs hy

/-- Closed-at-zero version of the fixed-`y` rule.  At `y = 0` the
primitive is identically zero in `s`; at every positive `y` the preceding
strict rule applies. -/
theorem aPrimitive_antitoneOn_s_of_qSecond_monotone
    (hQ2 : MonotoneOn lrCertificateQSecond (Ioo (0 : ℝ) 1))
    {y : ℝ} (hy : y ∈ Ico (0 : ℝ) 1) :
    AntitoneOn (fun s => aPrimitive s y) (Ioo (0 : ℝ) 1) := by
  rcases eq_or_lt_of_le hy.1 with rfl | hyPos
  · intro s₁ hs₁ s₂ hs₂ hs₁s₂
    simp [aPrimitive]
  · exact
      (aPrimitive_strictAntiOn_s_of_qSecond_monotone hQ2
        ⟨hyPos, hy.2⟩).antitoneOn

/-- Fixed-`s` monotonicity of the historical `A` primitive. -/
theorem aPrimitive_strictMonoOn_y
    {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    StrictMonoOn (aPrimitive s) (Ico (0 : ℝ) 1) := by
  rw [show aPrimitive s = acA s by
    funext y
    exact aPrimitive_eq_acA s y]
  apply strictMonoOn_of_deriv_pos (convex_Ico (0 : ℝ) 1)
  · intro y hy
    exact (hasDerivAt_acA_y_closed hs hy).continuousAt.continuousWithinAt
  · intro y hy
    rw [interior_Ico] at hy
    rw [(hasDerivAt_acA_y hs hy).deriv]
    exact acA_y_deriv_pos hs hy

/-- Conditional fixed-`s` monotonicity of the historical `C` primitive. -/
theorem cPrimitive_strictAntiOn_y_of_qSecond_monotone
    (hQ2 : MonotoneOn lrCertificateQSecond (Ioo (0 : ℝ) 1))
    {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    StrictAntiOn (cPrimitive s) (Ico (0 : ℝ) 1) := by
  rw [show cPrimitive s = acC s by
    funext y
    exact cPrimitive_eq_acC s y]
  apply strictAntiOn_of_deriv_neg (convex_Ico (0 : ℝ) 1)
  · intro y hy
    change ContinuousWithinAt (fun u => acA s u - lrCertificateQ u)
      (Ico (0 : ℝ) 1) y
    exact ((hasDerivAt_acA_y_closed hs hy).continuousAt.sub
      continuous_lrCertificateQ.continuousAt).continuousWithinAt
  · intro y hy
    rw [interior_Ico] at hy
    rw [(hasDerivAt_acC_y hs hy).deriv]
    exact acC_y_deriv_neg hQ2 hs hy

/-- `C` has the same `s` derivative as `A`, hence the same fixed-`y`
monotonicity. -/
theorem cPrimitive_strictAntiOn_s_of_qSecond_monotone
    (hQ2 : MonotoneOn lrCertificateQSecond (Ioo (0 : ℝ) 1))
    {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    StrictAntiOn (fun s => cPrimitive s y) (Ioo (0 : ℝ) 1) := by
  rw [show (fun s => cPrimitive s y) = (fun s => acC s y) by
    funext s
    exact cPrimitive_eq_acC s y]
  apply strictAntiOn_of_deriv_neg (convex_Ioo (0 : ℝ) 1)
  · intro s hs
    exact (hasDerivAt_acC_s hs hy).continuousAt.continuousWithinAt
  · intro s hs
    rw [interior_Ioo] at hs
    rw [(hasDerivAt_acC_s hs hy).deriv]
    exact acA_s_deriv_neg hQ2 hs hy

/-- Closed-at-zero version of the fixed-`y` rule for `C`.  As for `A`, the
`y = 0` primitive is identically zero in `s`. -/
theorem cPrimitive_antitoneOn_s_of_qSecond_monotone
    (hQ2 : MonotoneOn lrCertificateQSecond (Ioo (0 : ℝ) 1))
    {y : ℝ} (hy : y ∈ Ico (0 : ℝ) 1) :
    AntitoneOn (fun s => cPrimitive s y) (Ioo (0 : ℝ) 1) := by
  rcases eq_or_lt_of_le hy.1 with rfl | hyPos
  · intro s₁ hs₁ s₂ hs₂ hs₁s₂
    simp [cPrimitive]
  · exact
      (cPrimitive_strictAntiOn_s_of_qSecond_monotone hQ2
        ⟨hyPos, hy.2⟩).antitoneOn

/-- The corner rule used by the historical enclosure for `A`.  It remains
valid when the lower `y` endpoint is zero. -/
theorem aPrimitive_corner_bounds_of_qSecond_monotone
    (hQ2 : MonotoneOn lrCertificateQSecond (Ioo (0 : ℝ) 1))
    {sLo s sHi yLo y yHi : ℝ}
    (hsLo : sLo ∈ Ioo (0 : ℝ) 1)
    (hs : s ∈ Ioo (0 : ℝ) 1)
    (hsHi : sHi ∈ Ioo (0 : ℝ) 1)
    (hyLo : yLo ∈ Ico (0 : ℝ) 1)
    (hy : y ∈ Ico (0 : ℝ) 1)
    (hyHi : yHi ∈ Ico (0 : ℝ) 1)
    (hsLo_le : sLo ≤ s) (hs_le_hi : s ≤ sHi)
    (hyLo_le : yLo ≤ y) (hy_le_hi : y ≤ yHi) :
    aPrimitive sHi yLo ≤ aPrimitive s y ∧
      aPrimitive s y ≤ aPrimitive sLo yHi := by
  constructor
  · exact
      ((aPrimitive_antitoneOn_s_of_qSecond_monotone hQ2 hyLo)
        hs hsHi hs_le_hi).trans
      ((aPrimitive_strictMonoOn_y hs).monotoneOn hyLo hy hyLo_le)
  · exact
      ((aPrimitive_strictMonoOn_y hs).monotoneOn hy hyHi hy_le_hi).trans
      ((aPrimitive_antitoneOn_s_of_qSecond_monotone hQ2 hyHi)
        hsLo hs hsLo_le)

/-- The corresponding corner rule for `C`: both coordinate directions are
antitone, including the closed face `y = 0`. -/
theorem cPrimitive_corner_bounds_of_qSecond_monotone
    (hQ2 : MonotoneOn lrCertificateQSecond (Ioo (0 : ℝ) 1))
    {sLo s sHi yLo y yHi : ℝ}
    (hsLo : sLo ∈ Ioo (0 : ℝ) 1)
    (hs : s ∈ Ioo (0 : ℝ) 1)
    (hsHi : sHi ∈ Ioo (0 : ℝ) 1)
    (hyLo : yLo ∈ Ico (0 : ℝ) 1)
    (hy : y ∈ Ico (0 : ℝ) 1)
    (hyHi : yHi ∈ Ico (0 : ℝ) 1)
    (hsLo_le : sLo ≤ s) (hs_le_hi : s ≤ sHi)
    (hyLo_le : yLo ≤ y) (hy_le_hi : y ≤ yHi) :
    cPrimitive sHi yHi ≤ cPrimitive s y ∧
      cPrimitive s y ≤ cPrimitive sLo yLo := by
  constructor
  · exact
      ((cPrimitive_strictAntiOn_y_of_qSecond_monotone hQ2 hsHi).antitoneOn
        hy hyHi hy_le_hi).trans
      ((cPrimitive_antitoneOn_s_of_qSecond_monotone hQ2 hy)
        hs hsHi hs_le_hi)
  · exact
      ((cPrimitive_strictAntiOn_y_of_qSecond_monotone hQ2 hs).antitoneOn
        hyLo hy hyLo_le).trans
      ((cPrimitive_antitoneOn_s_of_qSecond_monotone hQ2 hyLo)
        hsLo hs hsLo_le)

/-! ## Unconditional exports from the checked curvature theorem -/

/-- The fixed-`y` contribution to the `s` derivative is nonpositive on the
closed-at-zero physical `y` domain.  This is the analytic fact used to soundly
intersect its interval enclosure with `(-∞, 0]`. -/
theorem fixedYPartialS_nonpos
    {s y : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) (hy : y ∈ Ico (0 : ℝ) 1) :
    s * (lrCertificateQSecond s -
      (1 - y) ^ 2 *
        lrCertificateQSecond (lrCertificateB s y)) ≤ 0 := by
  rcases eq_or_lt_of_le hy.1 with rfl | hyPos
  · simp [lrCertificateB]
  · have hneg := acA_s_deriv_neg lrCertificateQSecond_monotoneOn
      hs ⟨hyPos, hy.2⟩
    simpa [acB, lrCertificateB] using hneg.le

theorem aPrimitive_antitoneOn_s
    {y : ℝ} (hy : y ∈ Ico (0 : ℝ) 1) :
    AntitoneOn (fun s => aPrimitive s y) (Ioo (0 : ℝ) 1) :=
  aPrimitive_antitoneOn_s_of_qSecond_monotone
    lrCertificateQSecond_monotoneOn hy

theorem cPrimitive_antitoneOn_s
    {y : ℝ} (hy : y ∈ Ico (0 : ℝ) 1) :
    AntitoneOn (fun s => cPrimitive s y) (Ioo (0 : ℝ) 1) :=
  cPrimitive_antitoneOn_s_of_qSecond_monotone
    lrCertificateQSecond_monotoneOn hy

theorem cPrimitive_strictAntiOn_y
    {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    StrictAntiOn (cPrimitive s) (Ico (0 : ℝ) 1) :=
  cPrimitive_strictAntiOn_y_of_qSecond_monotone
    lrCertificateQSecond_monotoneOn hs

theorem aPrimitive_corner_bounds
    {sLo s sHi yLo y yHi : ℝ}
    (hsLo : sLo ∈ Ioo (0 : ℝ) 1)
    (hs : s ∈ Ioo (0 : ℝ) 1)
    (hsHi : sHi ∈ Ioo (0 : ℝ) 1)
    (hyLo : yLo ∈ Ico (0 : ℝ) 1)
    (hy : y ∈ Ico (0 : ℝ) 1)
    (hyHi : yHi ∈ Ico (0 : ℝ) 1)
    (hsLo_le : sLo ≤ s) (hs_le_hi : s ≤ sHi)
    (hyLo_le : yLo ≤ y) (hy_le_hi : y ≤ yHi) :
    aPrimitive sHi yLo ≤ aPrimitive s y ∧
      aPrimitive s y ≤ aPrimitive sLo yHi :=
  aPrimitive_corner_bounds_of_qSecond_monotone
    lrCertificateQSecond_monotoneOn hsLo hs hsHi hyLo hy hyHi
      hsLo_le hs_le_hi hyLo_le hy_le_hi

theorem cPrimitive_corner_bounds
    {sLo s sHi yLo y yHi : ℝ}
    (hsLo : sLo ∈ Ioo (0 : ℝ) 1)
    (hs : s ∈ Ioo (0 : ℝ) 1)
    (hsHi : sHi ∈ Ioo (0 : ℝ) 1)
    (hyLo : yLo ∈ Ico (0 : ℝ) 1)
    (hy : y ∈ Ico (0 : ℝ) 1)
    (hyHi : yHi ∈ Ico (0 : ℝ) 1)
    (hsLo_le : sLo ≤ s) (hs_le_hi : s ≤ sHi)
    (hyLo_le : yLo ≤ y) (hy_le_hi : y ≤ yHi) :
    cPrimitive sHi yHi ≤ cPrimitive s y ∧
      cPrimitive s y ≤ cPrimitive sLo yLo :=
  cPrimitive_corner_bounds_of_qSecond_monotone
    lrCertificateQSecond_monotoneOn hsLo hs hsHi hyLo hy hyHi
      hsLo_le hs_le_hi hyLo_le hy_le_hi

end LRUpperKReplayCertificate
end CourtadeKumar
