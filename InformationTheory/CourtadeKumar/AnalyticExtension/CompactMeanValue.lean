import InformationTheory.CourtadeKumar.AnalyticExtension.CompactADSound
import Mathlib.Analysis.Calculus.MeanValue

/-! A derivative enclosure certifies a whole box through its center value. -/
open Set
namespace CourtadeKumar.LRCompactReducedCertificate

lemma derivative_product_bound {a : RationalEnclosure} {d w radius : ℝ}
    (hd : a.Contains d) (hw : |w| ≤ radius) :
    -radius*(absBound a : ℝ) ≤ d*w := by
  have habs := contains_absBound hd
  have hr : 0 ≤ radius := (abs_nonneg _).trans hw
  have hmul := mul_le_mul habs hw (abs_nonneg _) (by exact_mod_cast
    (le_trans (abs_nonneg a.lower) (le_max_left (abs a.lower) (abs a.upper))))
  rw [← abs_mul] at hmul
  have hlo := (neg_abs_le (d*w))
  nlinarith

theorem Jet.center_lower {a : Jet} {f : ℝ → ℝ} {r v t rs rv rt lower : ℝ}
    (hf : ∀ z ∈ Icc (0 : ℝ) 1, a.Models f z r v t)
    (hr : |r| ≤ rs) (hv : |v| ≤ rv) (ht : |t| ≤ rt)
    (hpoint : lower ≤ f 0)
    (hcheck : 0 ≤ lower - (rs*(absBound a.bounds.derivS : ℝ) +
      rv*(absBound a.bounds.derivK : ℝ) + rt*(absBound a.bounds.derivChi : ℝ))) :
    0 ≤ f 1 := by
  let loss := rs*(absBound a.bounds.derivS : ℝ) +
      rv*(absBound a.bounds.derivK : ℝ) + rt*(absBound a.bounds.derivChi : ℝ)
  have hd (z : ℝ) (hz : z ∈ Icc (0 : ℝ) 1) :
      ∃ d, HasDerivAt f d z ∧ -loss ≤ d := by
    rcases hf z hz with ⟨ds,dk,dc,hval,hderiv⟩
    refine ⟨ds*r+dk*v+dc*t,hderiv,?_⟩
    have h1 := derivative_product_bound hval.2.1 hr
    have h2 := derivative_product_bound hval.2.2.1 hv
    have h3 := derivative_product_bound hval.2.2.2 ht
    dsimp [loss]
    linarith
  have hg (z : ℝ) (hz : z ∈ Icc (0 : ℝ) 1) :
      ∃ d, HasDerivAt (fun x => f x + loss*x) d z ∧ 0 ≤ d := by
    rcases hd z hz with ⟨d,hderiv,hle⟩
    refine ⟨d+loss,?_,by linarith⟩
    simpa using hderiv.add ((hasDerivAt_id z).const_mul loss)
  have hm : MonotoneOn (fun x => f x + loss*x) (Icc (0 : ℝ) 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc (0 : ℝ) 1)
    · intro z hz
      rcases hg z hz with ⟨d,hd,_⟩
      exact hd.continuousAt.continuousWithinAt
    · intro z hz
      rcases hg z (interior_subset hz) with ⟨d,hd,_⟩
      exact hd.differentiableAt.differentiableWithinAt
    · intro z hz
      rcases hg z (interior_subset hz) with ⟨d,hd,hpos⟩
      rw [hd.deriv]
      exact hpos
  have h := hm (by norm_num) (by norm_num) (by norm_num : (0:ℝ) ≤ 1)
  dsimp [loss] at h
  nlinarith

noncomputable def line (a x z : ℝ) : ℝ := a + z*(x-a)

lemma line_mem {a x l u z : ℝ} (ha : a ∈ Icc l u) (hx : x ∈ Icc l u)
    (hz : z ∈ Icc (0 : ℝ) 1) : line a x z ∈ Icc l u := by
  unfold line
  constructor
  · nlinarith [mul_nonneg hz.1 (sub_nonneg.mpr hx.1),
      mul_nonneg (sub_nonneg.mpr hz.2) (sub_nonneg.mpr ha.1)]
  · nlinarith [mul_nonneg hz.1 (sub_nonneg.mpr hx.2),
      mul_nonneg (sub_nonneg.mpr hz.2) (sub_nonneg.mpr ha.2)]

lemma hasDerivAt_line (a x z : ℝ) : HasDerivAt (line a x) (x-a) z := by
  change HasDerivAt (fun u => a+u*(x-a)) (x-a) z
  simpa only [one_mul] using ((hasDerivAt_id z).mul_const (x-a)).const_add a

end CourtadeKumar.LRCompactReducedCertificate
