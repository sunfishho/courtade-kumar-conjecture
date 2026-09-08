import InformationTheory.CourtadeKumar.AnalyticExtension.CompactIntegerCheckerCore
import InformationTheory.CourtadeKumar.AnalyticExtension.CompactIntegerSharedSound
import InformationTheory.CourtadeKumar.AnalyticExtension.CompactCheckerSound

open Set
namespace CourtadeKumar.LRCompactIntegerCertificate
open LRCompactReducedCertificate
theorem expression_nonneg {b : CertificateBox} {d : Leaf} {L : RationalEnclosure}
    {R v t : ℝ} (hL : L.Contains (Real.log 2))
    (hc : checkLeaf L b d = true) (hp : b.Contains ⟨R,v,t⟩) :
    0 ≤ (targetExpr 24 8).eval
      (realEnv R v t (bValue R v t) d.tangent.aT d.tangent.au d.tangent.ac (Real.log 2)) := by
  have hcheck : ((d.precheck b = true ∧
      (sharedTarget (inputs b d L) 24 8).decode.valid = true) ∧
      (sharedTarget (pointInputs b d L) 24 8).decode.valid = true) ∧
      0 ≤ (sharedTarget (pointInputs b d L) 24 8).decode.bounds.value.lower -
        boxLoss b (sharedTarget (inputs b d L) 24 8).decode := by
    simpa only [checkLeaf, Bool.and_eq_true, decide_eq_true_eq] using hc
  have hpre : (BoxValid b ∧ d.tangent.check (RationalEnclosure.center (boxT b))
      (RationalEnclosure.center (boxV b)*RationalEnclosure.center (boxT b)) = true) ∧
      d.wholeB.check (rJet b) (vJet b) (tJet b) = true ∧
      d.pointB.check (rPoint b) (vPoint b) (tPoint b) = true := by
    simpa only [Leaf.precheck, Bool.and_eq_true, decide_eq_true_eq, and_assoc] using hcheck.1.1.1
  have hbox := hpre.1.1
  have hR : (boxR b).Contains R := ⟨hp.1,hp.2.1⟩
  have hv : (boxV b).Contains v := ⟨hp.2.2.1,hp.2.2.2.1⟩
  have ht : (boxT b).Contains t := hp.2.2.2.2
  let cr : ℝ := RationalEnclosure.center (boxR b)
  let cv : ℝ := RationalEnclosure.center (boxV b)
  let ct : ℝ := RationalEnclosure.center (boxT b)
  let f : ℝ → ℝ := fun z => (targetExpr 24 8).eval
    (realEnv (line cr R z) (line cv v z) (line ct t z)
      (bValue (line cr R z) (line cv v z) (line ct t z))
      d.tangent.aT d.tangent.au d.tangent.ac (Real.log 2))
  have hf (z : ℝ) (hz : z ∈ Icc (0 : ℝ) 1) :
      (sharedTarget (inputs b d L) 24 8).decode.Models f z (R-cr) (v-cv) (t-ct) := by
    rw [sharedTarget_eq]
    apply enclose_models _ _ (by simpa only [← sharedTarget_eq] using hcheck.1.1.2)
    intro i
    apply Jet.models_fromRat
    apply Leaf.inputs_models hbox hL _ _ _ hpre.2.1 i
    · exact variableR_models (line_mem (center_contains hbox.2.1) hR hz) (hasDerivAt_line cr R z)
    · exact variableV_models (line_mem (center_contains hbox.2.2.2.2.1) hv hz) (hasDerivAt_line cv v z)
    · exact variableT_models (line_mem (center_contains hbox.2.2.2.2.2.2.2.1) ht hz) (hasDerivAt_line ct t z)
  have hpoint := enclose_models (targetExpr 24 8)
    (fun i => Jet.models_fromRat (Leaf.pointInputs_models hbox hL hpre.2.2 i))
    (show (enclose (pointInputs b d L) (targetExpr 24 8)).valid = true by
      simpa only [← sharedTarget_eq] using hcheck.1.2)
  rw [← sharedTarget_eq] at hpoint
  rcases hpoint with ⟨ds,dk,dc,hval,_⟩
  have h0 : ((sharedTarget (pointInputs b d L) 24 8).decode.bounds.value.lower : ℝ) ≤ f 0 := by
    simpa [f,line,cr,cv,ct] using hval.1.1
  have hnum : 0 ≤ ((sharedTarget (pointInputs b d L) 24 8).decode.bounds.value.lower : ℝ) -
      (RationalEnclosure.radius (boxR b) : ℝ)*
        (LRCompactReducedCertificate.absBound (sharedTarget (inputs b d L) 24 8).decode.bounds.derivS : ℝ) -
      (RationalEnclosure.radius (boxV b) : ℝ)*
        (LRCompactReducedCertificate.absBound (sharedTarget (inputs b d L) 24 8).decode.bounds.derivK : ℝ) -
      (RationalEnclosure.radius (boxT b) : ℝ)*
        (LRCompactReducedCertificate.absBound (sharedTarget (inputs b d L) 24 8).decode.bounds.derivChi : ℝ) := by
    have hh := hcheck.2
    unfold boxLoss at hh
    have hh' : (0:ℝ) ≤ ((sharedTarget (pointInputs b d L) 24 8).decode.bounds.value.lower : ℝ) -
      ((RationalEnclosure.radius (boxR b) : ℝ)*
        (LRCompactReducedCertificate.absBound (sharedTarget (inputs b d L) 24 8).decode.bounds.derivS : ℝ) +
       (RationalEnclosure.radius (boxV b) : ℝ)*
        (LRCompactReducedCertificate.absBound (sharedTarget (inputs b d L) 24 8).decode.bounds.derivK : ℝ) +
       (RationalEnclosure.radius (boxT b) : ℝ)*
        (LRCompactReducedCertificate.absBound (sharedTarget (inputs b d L) 24 8).decode.bounds.derivChi : ℝ)) := by exact_mod_cast hh
    linarith
  have hresult := LRCompactReducedCertificate.Jet.center_lower hf
    (RationalEnclosure.abs_sub_center_le_radius hR)
    (RationalEnclosure.abs_sub_center_le_radius hv)
    (RationalEnclosure.abs_sub_center_le_radius ht) h0 (by linarith [hnum])
  simpa [f,line] using hresult



open LRAnalyticCompact
theorem leaf_sound {b : CertificateBox} {d : Leaf} {L : RationalEnclosure}
    {R v t : ℝ} (hL : L.Contains (Real.log 2)) (hc : checkLeaf L b d = true)
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
  have he := expression_nonneg hL hc hp
  have hb : bValue R v t = lrFlowB R v t := by
    exact (flowB_formula hR.1.le ht.1.le).symm
  rw [hb] at he
  exact he.trans (target_le_reserve 24 8 (by decide) hR hv hvthird ht
    hs.1 hs.2.1 hs.2.2.1 hs.2.2.2.1 hs.2.2.2.2)


theorem checkTree_sound {L : RationalEnclosure} {b : CertificateBox} {tree : Tree}
    (hL : L.Contains (Real.log 2)) (hc : checkTree L b tree = true) :
    ∀ p, b.Contains p → Physical p → 0 ≤ lrLowVReserve p.s p.k p.chi := by
  have hs := subdivisionCertificate_sound
    (Relevant := Physical) (Property := fun p => Physical p → 0 ≤ lrLowVReserve p.s p.k p.chi)
    (accept_sound := fun b d h p hp hphys =>
      leaf_sound hL h hp hphys.1 hphys.2.1 hphys.2.2.1 hphys.2.2.2.1)
    (discard_sound := fun b d h p hp hphys =>
      not_lt_of_ge (discard_sound (by cases d; exact h) hp hphys.1 hphys.2.1 hphys.2.2.2.1)
        hphys.2.2.2.2) hc
  intro p hp hphys
  exact hs p hp hphys hphys


end CourtadeKumar.LRCompactIntegerCertificate
