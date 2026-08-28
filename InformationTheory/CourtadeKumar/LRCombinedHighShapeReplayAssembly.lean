import InformationTheory.CourtadeKumar.LRCombinedHighShapeAutoTree

/-!
# Finite replay interface for the combined high-shape certificate

The generator may choose any finite family of rational root boxes and any
checked subdivision tree on each root.  Lean separately checks every tree
and the geometric coverage statement.  Thus the root-selection and tree
generation algorithms are outside the trusted base.
-/

namespace CourtadeKumar

structure LRCombinedHighShapeCheckedRoot where
  box : CertificateBox
  tree : LRCombinedHighShapeAutoTree.Tree

namespace LRCombinedHighShapeCheckedRoot

def check (terms : ℕ) (root : LRCombinedHighShapeCheckedRoot) : Bool :=
  root.tree.check (LRHighShapeCombinedAcceptData.check terms)
    (lrHighShapeVDiscardCheck terms) root.box

theorem sound (terms : ℕ) {root : LRCombinedHighShapeCheckedRoot}
    (hcheck : root.check terms = true) :
    ∀ point, root.box.Contains point → LRHighShapeVRelevant point →
      LRHighShapeCertificateAlternative point := by
  exact lrHighShapeCombinedSubdivisionCertificate_sound terms hcheck

end LRCombinedHighShapeCheckedRoot

namespace LRCombinedHighShapeReplay

def check (terms : ℕ) : List LRCombinedHighShapeCheckedRoot → Bool
  | [] => true
  | root :: roots => root.check terms && check terms roots

/-- Generate one checked tree per proposed rational root.  Returning `none`
is merely generator failure; returning data is followed by a kernel proof
that every generated tree passes its executable checker. -/
def build (terms sqrtFuel logFuel fuel : ℕ) :
    List CertificateBox → Option (List LRCombinedHighShapeCheckedRoot)
  | [] => some []
  | box :: boxes =>
      match LRCombinedHighShapeAutoTree.buildTree
          terms sqrtFuel logFuel fuel box with
      | none => none
      | some tree =>
          match build terms sqrtFuel logFuel fuel boxes with
          | none => none
          | some roots => some ({ box := box, tree := tree } :: roots)

theorem build_check_of_eq
    (terms sqrtFuel logFuel fuel : ℕ) (boxes : List CertificateBox)
    (roots : List LRCombinedHighShapeCheckedRoot)
    (hbuild : build terms sqrtFuel logFuel fuel boxes = some roots) :
    check terms roots = true := by
  induction boxes generalizing roots with
  | nil =>
      simp [build] at hbuild
      subst roots
      rfl
  | cons box boxes ih =>
      generalize htree : LRCombinedHighShapeAutoTree.buildTree
        terms sqrtFuel logFuel fuel box = treeOption
      cases treeOption with
      | none =>
          simp [build, htree] at hbuild
      | some tree =>
          generalize hroots : build terms sqrtFuel logFuel fuel boxes =
            rootsOption
          cases rootsOption with
          | none =>
              simp [build, htree, hroots] at hbuild
          | some tail =>
              simp only [build, htree, hroots, Option.some.injEq] at hbuild
              subst roots
              simp only [check, Bool.and_eq_true]
              exact ⟨
                LRCombinedHighShapeAutoTree.buildTree_check_of_eq
                  terms sqrtFuel logFuel fuel box tree htree,
                ih tail hroots⟩

def Covers (roots : List LRCombinedHighShapeCheckedRoot)
    (point : CertificatePoint) : Prop :=
  ∃ root ∈ roots, root.box.Contains point

theorem checked_of_mem (terms : ℕ)
    {roots : List LRCombinedHighShapeCheckedRoot}
    (hcheck : check terms roots = true)
    {root : LRCombinedHighShapeCheckedRoot} (hmem : root ∈ roots) :
    root.check terms = true := by
  induction roots with
  | nil => simp at hmem
  | cons head tail ih =>
      have hparts : head.check terms = true ∧ check terms tail = true := by
        simpa [check] using hcheck
      rcases List.mem_cons.mp hmem with rfl | htail
      · exact hparts.1
      · exact ih hparts.2 htail

theorem alternative_of_covers (terms : ℕ)
    {roots : List LRCombinedHighShapeCheckedRoot}
    (hcheck : check terms roots = true)
    {point : CertificatePoint} (hcover : Covers roots point)
    (hrelevant : LRHighShapeVRelevant point) :
    LRHighShapeCertificateAlternative point := by
  rcases hcover with ⟨root, hmem, hcontains⟩
  exact root.sound terms (checked_of_mem terms hcheck hmem)
    point hcontains hrelevant

/-- A finite checked replay plus a geometric coverage proof supplies the
entire near-endpoint coordinate interface consumed by the analytic flow
assembly. -/
theorem nearEndpointTheorem_of_checked_replay
    (terms : ℕ) {roots : List LRCombinedHighShapeCheckedRoot}
    (hcheck : check terms roots = true)
    (hcoverage : ∀ point : CertificatePoint,
      LRHighShapeInterior point →
      LRHighShapeVRelevant point →
      point.s < 1 / 10 → Covers roots point) :
    LRHighShapeNearEndpointCombinedCoordinateTheorem := by
  intro point hinterior hrelevant hs
  exact alternative_of_covers terms hcheck
    (hcoverage point hinterior hrelevant hs) hrelevant

/-- Direct end-to-end use of generated replay data: once the compact ledger,
the aggregate Boolean check, and rational-root coverage are supplied, the
exact LR flow numerator is nonnegative. -/
theorem lrFlowNumeratorP_nonneg_target_of_compactV_and_checkedReplay
    (ledger : LRCompactVR910ReplayLedger)
    (terms : ℕ) {roots : List LRCombinedHighShapeCheckedRoot}
    (hcheck : check terms roots = true)
    (hcoverage : ∀ point : CertificatePoint,
      LRHighShapeInterior point →
      LRHighShapeVRelevant point →
      point.s < 1 / 10 → Covers roots point)
    {R p v t : ℝ} (hR : R ∈ Set.Ioo (0 : ℝ) 1)
    (hp : p ∈ Set.Ioc (0 : ℝ) (1 / 2 : ℝ))
    (hv : v ∈ Set.Ioo (0 : ℝ) 1) (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (htarget : lrPrefixEll R p = lrSquareTarget R v t) :
    0 ≤ lrFlowNumeratorP R p v t := by
  exact
    lrFlowNumeratorP_nonneg_target_of_compactV_and_combinedEndpoint
      ledger (nearEndpointTheorem_of_checked_replay terms hcheck hcoverage)
      hR hp hv ht htarget

end LRCombinedHighShapeReplay
end CourtadeKumar
