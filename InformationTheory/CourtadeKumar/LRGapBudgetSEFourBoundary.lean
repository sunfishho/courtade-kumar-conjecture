import InformationTheory.CourtadeKumar.LRGapBudgetSEEndpointValueCertificate
import InformationTheory.CourtadeKumar.LRGapBudgetSEFourBoundaryModelCertificate

/-!
# Checked subdivision on the `e = 4s` boundary

The noncompact high-shape argument begins at `k = 4`, hence at the diagonal
`e = s*k = 4s` in bounded coordinates.  A generic three-dimensional split
would lose this correlation.  This file provides a two-dimensional rational
box and tree whose `s` split simultaneously tightens the hull for `e = 4s`.
-/

namespace CourtadeKumar
namespace LRGapBudgetSEFourBoundary

structure Box where
  sLo : ℚ
  sHi : ℚ
  chiLo : ℚ
  chiHi : ℚ
  deriving Repr

def Box.Contains (box : Box) (s chi : ℝ) : Prop :=
  (box.sLo : ℝ) ≤ s ∧ s ≤ (box.sHi : ℝ) ∧
    (box.chiLo : ℝ) ≤ chi ∧ chi ≤ (box.chiHi : ℝ)

/-- The tight coordinatewise hull of the diagonal portion in a boundary box. -/
def Box.hull (box : Box) : CertificateBox where
  sLo := box.sLo
  sHi := box.sHi
  kLo := 4 * box.sLo
  kHi := 4 * box.sHi
  chiLo := box.chiLo
  chiHi := box.chiHi

theorem Box.hull_contains {box : Box} {s chi : ℝ}
    (hpoint : box.Contains s chi) :
    box.hull.Contains { s := s, k := 4 * s, chi := chi } := by
  rcases hpoint with ⟨hsLo, hsHi, hchiLo, hchiHi⟩
  refine ⟨hsLo, hsHi, ?_, ?_, hchiLo, hchiHi⟩
  · have h : (4 : ℝ) * (box.sLo : ℝ) ≤ 4 * s :=
      mul_le_mul_of_nonneg_left hsLo (by norm_num)
    exact_mod_cast h
  · have h : 4 * s ≤ (4 : ℝ) * (box.sHi : ℝ) :=
      mul_le_mul_of_nonneg_left hsHi (by norm_num)
    exact_mod_cast h

inductive Axis where
  | s
  | chi
  deriving DecidableEq, Repr

def Box.lower (box : Box) (axis : Axis) (cut : ℚ) : Box :=
  match axis with
  | .s => { box with sHi := cut }
  | .chi => { box with chiHi := cut }

def Box.upper (box : Box) (axis : Axis) (cut : ℚ) : Box :=
  match axis with
  | .s => { box with sLo := cut }
  | .chi => { box with chiLo := cut }

theorem Box.contains_lower_or_upper {box : Box} {s chi : ℝ}
    (hpoint : box.Contains s chi) (axis : Axis) (cut : ℚ) :
    (box.lower axis cut).Contains s chi ∨
      (box.upper axis cut).Contains s chi := by
  rcases hpoint with ⟨hsLo, hsHi, hchiLo, hchiHi⟩
  cases axis with
  | s =>
      rcases le_total s (cut : ℝ) with hs | hs
      · exact Or.inl ⟨hsLo, hs, hchiLo, hchiHi⟩
      · exact Or.inr ⟨hs, hsHi, hchiLo, hchiHi⟩
  | chi =>
      rcases le_total chi (cut : ℝ) with hchi | hchi
      · exact Or.inl ⟨hsLo, hsHi, hchiLo, hchi⟩
      · exact Or.inr ⟨hsLo, hsHi, hchi, hchiHi⟩

/-- The only physical restriction that can remove part of the `k=4` root. -/
def Relevant (s chi : ℝ) : Prop :=
  4 * chi * s ≤ 3 / 20

inductive DiscardData where
  | xBelowHighShape
  deriving DecidableEq, Repr

def discardCheck (box : Box) : DiscardData → Bool
  | .xBelowHighShape => decide
      (0 ≤ box.sLo ∧ 0 ≤ box.chiLo ∧
        3 / 20 < 4 * box.chiLo * box.sLo)

theorem discardCheck_sound (box : Box) (data : DiscardData)
    (hcheck : discardCheck box data = true) :
    ∀ s chi, box.Contains s chi → ¬ Relevant s chi := by
  intro s chi hpoint hrelevant
  rcases hpoint with ⟨hsLo, _hsHi, hchiLo, _hchiHi⟩
  cases data with
  | xBelowHighShape =>
      have hrat : (0 : ℚ) ≤ box.sLo ∧ (0 : ℚ) ≤ box.chiLo ∧
          (3 / 20 : ℚ) < 4 * box.chiLo * box.sLo := by
        simpa [discardCheck] using hcheck
      have hreal : (3 / 20 : ℝ) <
          4 * (box.chiLo : ℝ) * (box.sLo : ℝ) := by
        have hcast : (((3 / 20 : ℚ) : ℝ)) <
            ((4 * box.chiLo * box.sLo : ℚ) : ℝ) := by
          exact_mod_cast hrat.2.2
        norm_num at hcast ⊢
        exact hcast
      have hsLoNonneg : (0 : ℝ) ≤ (box.sLo : ℝ) := by
        exact_mod_cast hrat.1
      have hchiLoNonneg : (0 : ℝ) ≤ (box.chiLo : ℝ) := by
        exact_mod_cast hrat.2.1
      have hsNonneg : (0 : ℝ) ≤ s := hsLoNonneg.trans hsLo
      have hchiNonneg : (0 : ℝ) ≤ chi := hchiLoNonneg.trans hchiLo
      have hprod : (box.chiLo : ℝ) * (box.sLo : ℝ) ≤ chi * s :=
        mul_le_mul hchiLo hsLo hsLoNonneg hchiNonneg
      have hmono : 4 * (box.chiLo : ℝ) * (box.sLo : ℝ) ≤
          4 * chi * s := by nlinarith
      exact (not_le_of_gt (hreal.trans_le hmono)) hrelevant

def endpointAcceptCheck (terms sqrtFuel logFuel : ℕ) (box : Box) : Bool :=
  LRGapBudgetSEEndpointValueCertificate.autoAccepts
    terms sqrtFuel logFuel box.hull

theorem endpointAcceptCheck_sound (terms sqrtFuel logFuel : ℕ) (box : Box)
    (hcheck : endpointAcceptCheck terms sqrtFuel logFuel box = true) :
    ∀ s chi, box.Contains s chi →
      0 ≤ lrGapBudgetSEChi s (4 * s) chi := by
  intro s chi hpoint
  have h := LRGapBudgetSEEndpointValueCertificate.autoAccepts_sound
    terms sqrtFuel logFuel box.hull hcheck
  have hhull := box.hull_contains hpoint
  exact h s (4 * s) chi
    ⟨hhull.1, hhull.2.1⟩
    ⟨hhull.2.2.1, hhull.2.2.2.1⟩
    ⟨hhull.2.2.2.2.1, hhull.2.2.2.2.2⟩

def analyticAcceptCheck (terms sqrtFuel logFuel : ℕ) (box : Box) : Bool :=
  decide (0 ≤ box.sLo ∧ box.sHi ≤ 1 / 10 ∧
      0 ≤ box.chiLo ∧ box.chiHi ≤ 1) &&
    LRGapBudgetSEFourBoundaryModelCertificate.autoAccepts
      terms sqrtFuel logFuel box.hull.sInterval box.hull.chiInterval

lemma boundary_value_zero (chi : ℝ) :
    lrGapBudgetSEChi 0 (4 * 0) chi = 0 := by
  simp [lrGapBudgetSEChi, lrCertificateG0, lrCertificateQ,
    lrCertificateB, topJ]
  norm_num

theorem analyticAcceptCheck_sound (terms sqrtFuel logFuel : ℕ) (box : Box)
    (hcheck : analyticAcceptCheck terms sqrtFuel logFuel box = true) :
    ∀ s chi, box.Contains s chi →
      0 ≤ lrGapBudgetSEChi s (4 * s) chi := by
  have hparts :
      (0 ≤ box.sLo ∧ box.sHi ≤ 1 / 10 ∧
        0 ≤ box.chiLo ∧ box.chiHi ≤ 1) ∧
      LRGapBudgetSEFourBoundaryModelCertificate.autoAccepts
        terms sqrtFuel logFuel box.hull.sInterval
          box.hull.chiInterval = true := by
    simpa [analyticAcceptCheck] using hcheck
  intro s chi hpoint
  have hhull := box.hull_contains hpoint
  have hlower :=
    LRGapBudgetSEFourBoundaryModelCertificate.autoAccepts_sound
      terms sqrtFuel logFuel box.hull.sInterval box.hull.chiInterval
      hparts.2 s chi ⟨hhull.1, hhull.2.1⟩
        ⟨hhull.2.2.2.2.1, hhull.2.2.2.2.2⟩
  have hsNonnegRat : (0 : ℚ) ≤ box.sLo := hparts.1.1
  have hsHiRat : box.sHi ≤ (1 / 10 : ℚ) := hparts.1.2.1
  have hchiLoRat : (0 : ℚ) ≤ box.chiLo := hparts.1.2.2.1
  have hchiHiRat : box.chiHi ≤ (1 : ℚ) := hparts.1.2.2.2
  have hsNonneg : (0 : ℝ) ≤ s := by
    have hlo : (0 : ℝ) ≤ (box.sLo : ℝ) := by exact_mod_cast hsNonnegRat
    exact hlo.trans hpoint.1
  have hsLe : s ≤ (1 / 10 : ℝ) := by
    have hcast : (box.sHi : ℝ) ≤ (((1 / 10 : ℚ) : ℝ)) := by
      exact_mod_cast hsHiRat
    have hhi : (box.sHi : ℝ) ≤ (1 / 10 : ℝ) := by
      norm_num at hcast ⊢
      exact hcast
    exact hpoint.2.1.trans hhi
  have hchiMem : chi ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · have hlo : (0 : ℝ) ≤ (box.chiLo : ℝ) := by exact_mod_cast hchiLoRat
      exact hlo.trans hpoint.2.2.1
    · have hhi : (box.chiHi : ℝ) ≤ 1 := by exact_mod_cast hchiHiRat
      exact hpoint.2.2.2.trans hhi
  rcases hsNonneg.eq_or_lt with rfl | hsPos
  · rw [boundary_value_zero]
  · exact LRGapBudgetSEFourBoundaryAnalytic.gap_nonnegative_of_lowerModel
      ⟨hsPos, hsLe⟩ hchiMem hlower

def acceptCheck (terms sqrtFuel logFuel : ℕ) (box : Box) : Bool :=
  endpointAcceptCheck terms sqrtFuel logFuel box ||
    analyticAcceptCheck terms sqrtFuel logFuel box

theorem acceptCheck_sound (terms sqrtFuel logFuel : ℕ) (box : Box)
    (hcheck : acceptCheck terms sqrtFuel logFuel box = true) :
    ∀ s chi, box.Contains s chi →
      0 ≤ lrGapBudgetSEChi s (4 * s) chi := by
  have hparts : endpointAcceptCheck terms sqrtFuel logFuel box = true ∨
      analyticAcceptCheck terms sqrtFuel logFuel box = true := by
    simpa [acceptCheck, Bool.or_eq_true] using hcheck
  rcases hparts with hendpoint | hanalytic
  · exact endpointAcceptCheck_sound terms sqrtFuel logFuel box hendpoint
  · exact analyticAcceptCheck_sound terms sqrtFuel logFuel box hanalytic

inductive Tree where
  | accept
  | discard (data : DiscardData)
  | split (axis : Axis) (cut : ℚ) (lower upper : Tree)
  deriving DecidableEq, Repr

def Tree.check (terms sqrtFuel logFuel : ℕ) : Box → Tree → Bool
  | box, .accept => acceptCheck terms sqrtFuel logFuel box
  | box, .discard data => discardCheck box data
  | box, .split axis cut lower upper =>
      check terms sqrtFuel logFuel (box.lower axis cut) lower &&
        check terms sqrtFuel logFuel (box.upper axis cut) upper

theorem Tree.sound (terms sqrtFuel logFuel : ℕ)
    {box : Box} {tree : Tree}
    (hcheck : tree.check terms sqrtFuel logFuel box = true) :
    ∀ s chi, box.Contains s chi → Relevant s chi →
      0 ≤ lrGapBudgetSEChi s (4 * s) chi := by
  induction tree generalizing box with
  | accept =>
      intro s chi hpoint _hrelevant
      exact acceptCheck_sound terms sqrtFuel logFuel box
        (by simpa [Tree.check] using hcheck) s chi hpoint
  | discard data =>
      intro s chi hpoint hrelevant
      exact (discardCheck_sound box data
        (by simpa [Tree.check] using hcheck) s chi hpoint hrelevant).elim
  | split axis cut lower upper lowerIH upperIH =>
      have hchildren :
          lower.check terms sqrtFuel logFuel (box.lower axis cut) = true ∧
          upper.check terms sqrtFuel logFuel (box.upper axis cut) = true := by
        simpa [Tree.check] using hcheck
      intro s chi hpoint hrelevant
      rcases box.contains_lower_or_upper hpoint axis cut with hlo | hhi
      · exact lowerIH hchildren.1 s chi hlo hrelevant
      · exact upperIH hchildren.2 s chi hhi hrelevant

def root : Box where
  sLo := 0
  sHi := 1 / 10
  chiLo := 0
  chiHi := 1

theorem root_contains {s chi : ℝ}
    (hs : s ∈ Set.Ioo (0 : ℝ) (1 / 10))
    (hchi : chi ∈ Set.Icc (0 : ℝ) 1) :
    root.Contains s chi := by
  have h : (0 : ℝ) ≤ s ∧ s ≤ 1 / 10 ∧
      (0 : ℝ) ≤ chi ∧ chi ≤ 1 :=
    ⟨hs.1.le, hs.2.le, hchi.1, hchi.2⟩
  simpa [root, Box.Contains] using h

def autoDiscard (box : Box) : Option DiscardData :=
  if discardCheck box .xBelowHighShape then
    some .xBelowHighShape
  else none

theorem autoDiscard_check_of_eq (box : Box) (data : DiscardData)
    (hdiscard : autoDiscard box = some data) :
    discardCheck box data = true := by
  by_cases hx : discardCheck box .xBelowHighShape = true
  · simp [autoDiscard, hx] at hdiscard
    cases hdiscard
    exact hx
  · have hxFalse := Bool.eq_false_of_not_eq_true hx
    simp [autoDiscard, hxFalse] at hdiscard

def chooseAxis (box : Box) : Axis :=
  if 10 * (box.sHi - box.sLo) ≥ box.chiHi - box.chiLo ∧
      box.sLo < box.sHi then .s
  else .chi

def axisCut (box : Box) : Axis → ℚ
  | .s => (box.sLo + box.sHi) / 2
  | .chi => (box.chiLo + box.chiHi) / 2

def buildTree (terms sqrtFuel logFuel : ℕ) : ℕ → Box → Option Tree
  | 0, box =>
      if acceptCheck terms sqrtFuel logFuel box then some .accept
      else match autoDiscard box with
        | some data => some (.discard data)
        | none => none
  | fuel + 1, box =>
      if acceptCheck terms sqrtFuel logFuel box then some .accept
      else match autoDiscard box with
        | some data => some (.discard data)
        | none =>
            let axis := chooseAxis box
            let cut := axisCut box axis
            match buildTree terms sqrtFuel logFuel fuel (box.lower axis cut) with
            | none => none
            | some lower =>
                match buildTree terms sqrtFuel logFuel fuel
                    (box.upper axis cut) with
                | none => none
                | some upper => some (.split axis cut lower upper)

def Tree.nodes : Tree → ℕ
  | .accept => 1
  | .discard _ => 1
  | .split _ _ lower upper => 1 + lower.nodes + upper.nodes

theorem Tree.check_split_iff (terms sqrtFuel logFuel : ℕ)
    (box : Box) (axis : Axis) (cut : ℚ) (lower upper : Tree) :
    (Tree.split axis cut lower upper).check terms sqrtFuel logFuel box = true ↔
      lower.check terms sqrtFuel logFuel (box.lower axis cut) = true ∧
        upper.check terms sqrtFuel logFuel (box.upper axis cut) = true := by
  simp only [Tree.check, Bool.and_eq_true]

theorem buildTree_check_of_eq (terms sqrtFuel logFuel fuel : ℕ)
    (box : Box) (tree : Tree)
    (hbuild : buildTree terms sqrtFuel logFuel fuel box = some tree) :
    tree.check terms sqrtFuel logFuel box = true := by
  induction fuel generalizing box tree with
  | zero =>
      change (if acceptCheck terms sqrtFuel logFuel box then some .accept
        else match autoDiscard box with
          | some data => some (.discard data)
          | none => none) = some tree at hbuild
      by_cases haccept : acceptCheck terms sqrtFuel logFuel box = true
      · simp [haccept] at hbuild
        subst tree
        simpa [Tree.check] using haccept
      · have hacceptFalse := Bool.eq_false_of_not_eq_true haccept
        simp only [hacceptFalse, Bool.false_eq_true, ↓reduceIte] at hbuild
        generalize hdiscard : autoDiscard box = discardOption
        cases discardOption with
        | none => simp [hdiscard] at hbuild
        | some data =>
            simp only [hdiscard, Option.some.injEq] at hbuild
            subst tree
            simpa [Tree.check] using autoDiscard_check_of_eq box data hdiscard
  | succ fuel ih =>
      change (if acceptCheck terms sqrtFuel logFuel box then some .accept
        else match autoDiscard box with
          | some data => some (.discard data)
          | none =>
              let axis := chooseAxis box
              let cut := axisCut box axis
              match buildTree terms sqrtFuel logFuel fuel
                  (box.lower axis cut) with
              | none => none
              | some lower =>
                  match buildTree terms sqrtFuel logFuel fuel
                      (box.upper axis cut) with
                  | none => none
                  | some upper => some (.split axis cut lower upper)) =
        some tree at hbuild
      by_cases haccept : acceptCheck terms sqrtFuel logFuel box = true
      · simp [haccept] at hbuild
        subst tree
        simpa [Tree.check] using haccept
      · have hacceptFalse := Bool.eq_false_of_not_eq_true haccept
        simp only [hacceptFalse, Bool.false_eq_true, ↓reduceIte] at hbuild
        generalize hdiscard : autoDiscard box = discardOption
        cases discardOption with
        | some data =>
            simp only [hdiscard, Option.some.injEq] at hbuild
            subst tree
            simpa [Tree.check] using autoDiscard_check_of_eq box data hdiscard
        | none =>
            let axis := chooseAxis box
            let cut := axisCut box axis
            generalize hlower : buildTree terms sqrtFuel logFuel fuel
              (box.lower axis cut) = lowerOption
            cases lowerOption with
            | none => simp [hdiscard, axis, cut, hlower] at hbuild
            | some lower =>
                generalize hupper : buildTree terms sqrtFuel logFuel fuel
                  (box.upper axis cut) = upperOption
                cases upperOption with
                | none =>
                    simp [hdiscard, axis, cut, hlower, hupper] at hbuild
                | some upper =>
                    simp only [hdiscard, axis, cut, hlower, hupper,
                      Option.some.injEq] at hbuild
                    subst tree
                    simp only [Tree.check, Bool.and_eq_true]
                    exact ⟨ih _ _ hlower, ih _ _ hupper⟩

end LRGapBudgetSEFourBoundary
end CourtadeKumar
