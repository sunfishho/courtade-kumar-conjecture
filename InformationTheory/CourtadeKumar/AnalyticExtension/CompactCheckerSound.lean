import InformationTheory.CourtadeKumar.AnalyticExtension.CompactBoxSound
import InformationTheory.CourtadeKumar.AnalyticExtension.CompactEnvelope

/-! Soundness of both terminal cases and the complete compact-V subdivision. -/
open Set
namespace CourtadeKumar.LRCompactReducedCertificate
open LRAnalyticCompact

theorem Leaf.sound {b : CertificateBox} {d : Leaf} {L : RationalEnclosure}
    {R v t : ℝ} (hL : L.Contains (Real.log 2)) (hc : d.check L b = true)
    (hp : b.Contains ⟨R,v,t⟩) (hR : R ∈ Ioc (0:ℝ) (9/10))
    (hv : v ∈ Ioo (0:ℝ) 1) (hvthird : 1/3 ≤ v) (ht : t ∈ Ioo (0:ℝ) 1) :
    0 ≤ lrLowVReserve R v t := by
  have hpre : d.precheck b = true :=
    (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hc).1).1).1
  have htan : d.tangent.check (RationalEnclosure.center (boxT b))
      (RationalEnclosure.center (boxV b)*RationalEnclosure.center (boxT b)) = true := by
    have h := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hpre).1).1
    exact (Bool.and_eq_true_iff.mp h).2
  have hs := TangentData.sound htan
  have he := Leaf.expression_nonneg hL hc hp
  have hb : bValue R v t = lrFlowB R v t := by
    exact (flowB_formula hR.1.le ht.1.le).symm
  rw [hb] at he
  exact he.trans (target_le_reserve 24 8 (by decide) hR hv hvthird ht
    hs.1 hs.2.1 hs.2.2.1 hs.2.2.2.1 hs.2.2.2.2)

theorem discard_sound {b : CertificateBox} {R v t : ℝ}
    (hc : discard b () = true) (hp : b.Contains ⟨R,v,t⟩)
    (hR : R ∈ Ioc (0:ℝ) (9/10)) (hv : v ∈ Ioo (0:ℝ) 1)
    (ht : t ∈ Ioo (0:ℝ) 1) : lrFlowJ R v t ≤ 0 := by
  have hcheck : BoxValid b ∧ (1+b.kHi)^2*(1-b.kLo^2*b.chiLo^2) ≤
      (1-b.sHi*(b.kHi^2*b.chiHi^2))^2 := by
    simpa only [discard, Bool.and_eq_true, decide_eq_true_eq] using hc
  rcases hcheck.1 with ⟨hr0,hr,hr1,hv0,hvv,hv1,ht0,htt,ht1⟩
  have hrl : (0:ℝ) ≤ b.sLo := by exact_mod_cast hr0
  have hrh : (b.sHi:ℝ) ≤ 9/10 := by
    have h : (b.sHi:ℝ) ≤ ((9/10:ℚ):ℝ) := Rat.cast_le.mpr hr1
    norm_num at h ⊢
    exact h
  have hvl : (0:ℝ) ≤ b.kLo := by exact_mod_cast (show (0:ℚ) ≤ b.kLo by linarith)
  have htl : (0:ℝ) ≤ b.chiLo := by exact_mod_cast (show (0:ℚ) ≤ b.chiLo by linarith)
  have hvh1 : (b.kHi:ℝ) ≤ 1 := by exact_mod_cast hv1
  have hth1 : (b.chiHi:ℝ) ≤ 1 := by exact_mod_cast ht1
  have hvh0 : (0:ℝ) ≤ b.kHi := hv.1.le.trans hp.2.2.2.1
  have hth0 : (0:ℝ) ≤ b.chiHi := ht.1.le.trans hp.2.2.2.2.2
  have hrh0 : (0:ℝ) ≤ b.sHi := hR.1.le.trans hp.2.1
  have hy := squared_shape_bounds hv ht
  have hylo : (b.kLo:ℝ)^2*(b.chiLo:ℝ)^2 ≤ v^2*t^2 :=
    mul_le_mul (pow_le_pow_left₀ hvl hp.2.2.1 2)
      (pow_le_pow_left₀ htl hp.2.2.2.2.1 2) (sq_nonneg _) (sq_nonneg _)
  have hyhi : v^2*t^2 ≤ (b.kHi:ℝ)^2*(b.chiHi:ℝ)^2 :=
    mul_le_mul (pow_le_pow_left₀ hv.1.le hp.2.2.2.1 2)
      (pow_le_pow_left₀ ht.1.le hp.2.2.2.2.2 2) (sq_nonneg _) (sq_nonneg _)
  have hyhi1 : (b.kHi:ℝ)^2*(b.chiHi:ℝ)^2 ≤ 1 := by
    have h1 : (b.kHi:ℝ)^2 ≤ 1 := by nlinarith
    have h2 : (b.chiHi:ℝ)^2 ≤ 1 := by nlinarith
    nlinarith [mul_le_mul h1 h2 (sq_nonneg (b.chiHi:ℝ)) zero_le_one]
  have hlo0 : 0 ≤ 1-(b.sHi:ℝ)*((b.kHi:ℝ)^2*(b.chiHi:ℝ)^2) := by
    have h := mul_le_mul_of_nonneg_left hyhi1 hrh0
    nlinarith
  have hRy := mul_le_mul hp.2.1 hyhi hy.1 hrh0
  have hrhs := pow_le_pow_left₀ hlo0 (sub_le_sub_left hRy 1) 2
  have hlhs : (1+v)^2*(1-v^2*t^2) ≤
      (1+(b.kHi:ℝ))^2*(1-(b.kLo:ℝ)^2*(b.chiLo:ℝ)^2) :=
    mul_le_mul (pow_le_pow_left₀ (by linarith [hv.1]) (by linarith [hp.2.2.2.1]) 2)
      (sub_le_sub_left hylo 1) (by linarith [hy.2]) (sq_nonneg _)
  have hpoly : (1+(b.kHi:ℝ))^2*(1-(b.kLo:ℝ)^2*(b.chiLo:ℝ)^2) ≤
      (1-(b.sHi:ℝ)*((b.kHi:ℝ)^2*(b.chiHi:ℝ)^2))^2 := by exact_mod_cast hcheck.2
  exact j_nonpositive_of_polynomial ⟨hR.1.le,hR.2⟩ hv ht (hlhs.trans (hpoly.trans hrhs))

/-- The relevant interior points use t as their third coordinate. -/
def Physical (p : CertificatePoint) : Prop :=
  p.s ∈ Ioc (0:ℝ) (9/10) ∧ p.k ∈ Ioo (0:ℝ) 1 ∧ 1/3 ≤ p.k ∧
    p.chi ∈ Ioo (0:ℝ) 1 ∧ 0 < lrFlowJ p.s p.k p.chi

theorem checkTree_sound {L : RationalEnclosure} {b : CertificateBox} {tree : Tree}
    (hL : L.Contains (Real.log 2)) (hc : checkTree L b tree = true) :
    ∀ p, b.Contains p → Physical p → 0 ≤ lrLowVReserve p.s p.k p.chi := by
  have hs := subdivisionCertificate_sound
    (Relevant := Physical) (Property := fun p => Physical p → 0 ≤ lrLowVReserve p.s p.k p.chi)
    (accept_sound := fun b d h p hp hphys =>
      Leaf.sound hL h hp hphys.1 hphys.2.1 hphys.2.2.1 hphys.2.2.2.1)
    (discard_sound := fun b d h p hp hphys =>
      not_lt_of_ge (discard_sound (by cases d; exact h) hp hphys.1 hphys.2.1 hphys.2.2.2.1)
        hphys.2.2.2.2) hc
  intro p hp hphys
  exact hs p hp hphys hphys

end CourtadeKumar.LRCompactReducedCertificate
