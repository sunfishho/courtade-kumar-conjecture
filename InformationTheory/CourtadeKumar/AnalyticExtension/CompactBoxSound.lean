import InformationTheory.CourtadeKumar.AnalyticExtension.CompactLogSound
import InformationTheory.CourtadeKumar.AnalyticExtension.CompactMeanValue

/-! From the executable leaf check to a real inequality throughout its box. -/
open Set
namespace CourtadeKumar.LRCompactReducedCertificate

lemma center_contains {a : RationalEnclosure} (h : a.lower ≤ a.upper) :
    a.Contains (RationalEnclosure.center a : ℝ) := by
  have h' : (a.lower : ℝ) ≤ a.upper := by exact_mod_cast h
  constructor <;> simp only [RationalEnclosure.center, Rat.cast_div, Rat.cast_add,
    Rat.cast_ofNat] <;> linarith

lemma variableR_models {a : RationalEnclosure} {f : ℝ → ℝ} {z r v t : ℝ}
    (hx : a.Contains (f z)) (hd : HasDerivAt f r z) :
    (⟨IntervalAD.variableS a,true⟩ : Jet).Models f z r v t := by
  refine ⟨1,0,0,IntervalAD.contains_variableS hx,?_⟩
  simpa using hd
lemma variableV_models {a : RationalEnclosure} {f : ℝ → ℝ} {z r v t : ℝ}
    (hx : a.Contains (f z)) (hd : HasDerivAt f v z) :
    (⟨IntervalAD.variableK a,true⟩ : Jet).Models f z r v t := by
  refine ⟨0,1,0,IntervalAD.contains_variableK hx,?_⟩
  simpa using hd
lemma variableT_models {a : RationalEnclosure} {f : ℝ → ℝ} {z r v t : ℝ}
    (hx : a.Contains (f z)) (hd : HasDerivAt f t z) :
    (⟨IntervalAD.variableChi a,true⟩ : Jet).Models f z r v t := by
  refine ⟨0,0,1,IntervalAD.contains_variableChi hx,?_⟩
  simpa using hd

lemma box_nonnegative {b : CertificateBox} (h : BoxValid b) :
    0 ≤ b.kLo ∧ 0 ≤ b.chiLo ∧
    0 ≤ RationalEnclosure.center (boxV b) ∧ 0 ≤ RationalEnclosure.center (boxT b) := by
  rcases h with ⟨hR0,hR,hR1,hv0,hv,hv1,ht0,ht,ht1⟩
  dsimp [RationalEnclosure.center,boxV,boxT]
  constructor; linarith
  constructor; linarith
  constructor <;> linarith

lemma Leaf.inputs_models {b : CertificateBox} {d : Leaf} {L : RationalEnclosure}
    {fR fv ft : ℝ → ℝ} {z wr wv wt : ℝ}
    (hbox : BoxValid b) (hL : L.Contains (Real.log 2))
    (hR : (rJet b).Models fR z wr wv wt) (hv : (vJet b).Models fv z wr wv wt)
    (ht : (tJet b).Models ft z wr wv wt)
    (hb : d.wholeB.check (rJet b) (vJet b) (tJet b) = true) :
    ∀ i, (d.inputs b L i).Models
      (fun x => realEnv (fR x) (fv x) (ft x) (bValue (fR x) (fv x) (ft x))
        d.tangent.aT d.tangent.au d.tangent.ac (Real.log 2) i) z wr wv wt := by
  have hn := box_nonnegative hbox
  have hB := BData.models hR hv ht hn.1 hn.2.1 hb
  intro i
  rcases i with _|i
  · exact hR
  rcases i with _|i
  · exact hv
  rcases i with _|i
  · exact ht
  rcases i with _|i
  · exact hB
  rcases i with _|i
  · exact Jet.models_const _
  rcases i with _|i
  · exact Jet.models_const _
  rcases i with _|i
  · exact Jet.models_const _
  rcases i with _|i
  · exact constInterval_models hL
  simpa only [Leaf.inputs, realEnv, Rat.cast_zero] using
    (Jet.models_const (z := z) (r := wr) (v := wv) (t := wt) 0)

lemma Leaf.pointInputs_models {b : CertificateBox} {d : Leaf} {L : RationalEnclosure}
    (hbox : BoxValid b) (hL : L.Contains (Real.log 2))
    (hb : d.pointB.check (rPoint b) (vPoint b) (tPoint b) = true) :
    ∀ i, (d.pointInputs b L i).Models
      (fun _ => realEnv (RationalEnclosure.center (boxR b))
        (RationalEnclosure.center (boxV b)) (RationalEnclosure.center (boxT b))
        (bValue (RationalEnclosure.center (boxR b))
          (RationalEnclosure.center (boxV b)) (RationalEnclosure.center (boxT b)))
        d.tangent.aT d.tangent.au d.tangent.ac (Real.log 2) i) 0 0 0 0 := by
  have hn := box_nonnegative hbox
  have hB := BData.models (z := 0) (wr := 0) (wv := 0) (wt := 0) (Jet.models_const (RationalEnclosure.center (boxR b)))
    (Jet.models_const (RationalEnclosure.center (boxV b)))
    (Jet.models_const (RationalEnclosure.center (boxT b))) hn.2.2.1 hn.2.2.2 hb
  intro i
  rcases i with _|i
  · exact Jet.models_const _
  rcases i with _|i
  · exact Jet.models_const _
  rcases i with _|i
  · exact Jet.models_const _
  rcases i with _|i
  · exact hB
  rcases i with _|i
  · exact Jet.models_const _
  rcases i with _|i
  · exact Jet.models_const _
  rcases i with _|i
  · exact Jet.models_const _
  rcases i with _|i
  · exact constInterval_models hL
  simpa only [Leaf.pointInputs, realEnv, Rat.cast_zero] using
    (Jet.models_const (z := 0) (r := 0) (v := 0) (t := 0) 0)

theorem Leaf.expression_nonneg {b : CertificateBox} {d : Leaf} {L : RationalEnclosure}
    {R v t : ℝ} (hL : L.Contains (Real.log 2))
    (hc : d.check L b = true) (hp : b.Contains ⟨R,v,t⟩) :
    0 ≤ (targetExpr 24 8).eval
      (realEnv R v t (bValue R v t) d.tangent.aT d.tangent.au d.tangent.ac (Real.log 2)) := by
  have hcheck : ((d.precheck b = true ∧
      ((targetExpr 24 8).enclose (d.inputs b L)).valid = true) ∧
      ((targetExpr 24 8).enclose (d.pointInputs b L)).valid = true) ∧
      0 ≤ ((targetExpr 24 8).enclose (d.pointInputs b L)).bounds.value.lower -
        boxLoss b ((targetExpr 24 8).enclose (d.inputs b L)) := by
    simpa only [Leaf.check, Bool.and_eq_true, decide_eq_true_eq] using hc
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
      ((targetExpr 24 8).enclose (d.inputs b L)).Models f z (R-cr) (v-cv) (t-ct) := by
    apply Expr.models _ _ hcheck.1.1.2
    apply Leaf.inputs_models hbox hL _ _ _ hpre.2.1
    · exact variableR_models (line_mem (center_contains hbox.2.1) hR hz) (hasDerivAt_line cr R z)
    · exact variableV_models (line_mem (center_contains hbox.2.2.2.2.1) hv hz) (hasDerivAt_line cv v z)
    · exact variableT_models (line_mem (center_contains hbox.2.2.2.2.2.2.2.1) ht hz) (hasDerivAt_line ct t z)
  have hpoint := Expr.models (targetExpr 24 8)
    (Leaf.pointInputs_models hbox hL hpre.2.2) hcheck.1.2
  rcases hpoint with ⟨ds,dk,dc,hval,_⟩
  have h0 : (((targetExpr 24 8).enclose (d.pointInputs b L)).bounds.value.lower : ℝ) ≤ f 0 := by
    simpa [f,line,cr,cv,ct] using hval.1.1
  have hnum : 0 ≤ (((targetExpr 24 8).enclose (d.pointInputs b L)).bounds.value.lower : ℝ) -
      (RationalEnclosure.radius (boxR b) : ℝ)*
        (absBound ((targetExpr 24 8).enclose (d.inputs b L)).bounds.derivS : ℝ) -
      (RationalEnclosure.radius (boxV b) : ℝ)*
        (absBound ((targetExpr 24 8).enclose (d.inputs b L)).bounds.derivK : ℝ) -
      (RationalEnclosure.radius (boxT b) : ℝ)*
        (absBound ((targetExpr 24 8).enclose (d.inputs b L)).bounds.derivChi : ℝ) := by
    have hh := hcheck.2
    unfold boxLoss at hh
    have hh' : (0:ℝ) ≤ (((targetExpr 24 8).enclose (d.pointInputs b L)).bounds.value.lower : ℝ) -
      ((RationalEnclosure.radius (boxR b) : ℝ)*
        (absBound ((targetExpr 24 8).enclose (d.inputs b L)).bounds.derivS : ℝ) +
       (RationalEnclosure.radius (boxV b) : ℝ)*
        (absBound ((targetExpr 24 8).enclose (d.inputs b L)).bounds.derivK : ℝ) +
       (RationalEnclosure.radius (boxT b) : ℝ)*
        (absBound ((targetExpr 24 8).enclose (d.inputs b L)).bounds.derivChi : ℝ)) := by exact_mod_cast hh
    linarith
  have hresult := Jet.center_lower hf
    (RationalEnclosure.abs_sub_center_le_radius hR)
    (RationalEnclosure.abs_sub_center_le_radius hv)
    (RationalEnclosure.abs_sub_center_le_radius ht) h0 (by linarith [hnum])
  simpa [f,line] using hresult

end CourtadeKumar.LRCompactReducedCertificate
