import InformationTheory.CourtadeKumar.LRSmallSBridgeFinalAssembly

/-!
# Generated small-`s` replay data

The tree-building program and its correctness theorem are fully kernel
checked.  The single `native_decide` below is deliberately isolated: it
certifies only that four concrete, bounded generator runs return `some`.
It is the exact temporary computation to replace by a transparent replay.
-/

namespace CourtadeKumar
namespace LRSmallSBridgeCoreCertificate

def generatedTerms : ℕ := 8
def generatedSqrtFuel : ℕ := 16
def generatedLogFuel : ℕ := 16

def generatedTree0 : SubdivisionCertificate Unit Unit :=
  (buildTree generatedTerms generatedSqrtFuel generatedLogFuel 10
    (rootBox (1 / 4) (1 / 2))).getD (.accept ())

def generatedTree1 : SubdivisionCertificate Unit Unit :=
  (buildTree generatedTerms generatedSqrtFuel generatedLogFuel 12
    (rootBox (1 / 2) 1)).getD (.accept ())

def generatedTree2 : SubdivisionCertificate Unit Unit :=
  (buildTree generatedTerms generatedSqrtFuel generatedLogFuel 12
    (rootBox 1 2)).getD (.accept ())

def generatedTree3 : SubdivisionCertificate Unit Unit :=
  (buildTree generatedTerms generatedSqrtFuel generatedLogFuel 16
    (rootBox 2 4)).getD (.accept ())

/-- Temporary closed computation.  No theorem about real numbers depends
directly on native evaluation; the returned trees are passed through the
proved `buildTree_check_of_eq` theorem below. -/
theorem generated_builds_are_some :
    (buildTree generatedTerms generatedSqrtFuel generatedLogFuel 10
      (rootBox (1 / 4) (1 / 2))).isSome = true ∧
    (buildTree generatedTerms generatedSqrtFuel generatedLogFuel 12
      (rootBox (1 / 2) 1)).isSome = true ∧
    (buildTree generatedTerms generatedSqrtFuel generatedLogFuel 12
      (rootBox 1 2)).isSome = true ∧
    (buildTree generatedTerms generatedSqrtFuel generatedLogFuel 16
      (rootBox 2 4)).isSome = true := by
  set_option maxRecDepth 1000000 in
    native_decide

lemma option_eq_some_getD_of_isSome
    {α : Type} (fallback : α) {value : Option α}
    (h : value.isSome = true) : value = some (value.getD fallback) := by
  cases value <;> simp_all

theorem generatedTree0_build :
    buildTree generatedTerms generatedSqrtFuel generatedLogFuel 10
        (rootBox (1 / 4) (1 / 2)) = some generatedTree0 := by
  exact option_eq_some_getD_of_isSome (.accept ()) generated_builds_are_some.1

theorem generatedTree1_build :
    buildTree generatedTerms generatedSqrtFuel generatedLogFuel 12
        (rootBox (1 / 2) 1) = some generatedTree1 := by
  exact option_eq_some_getD_of_isSome (.accept ()) generated_builds_are_some.2.1

theorem generatedTree2_build :
    buildTree generatedTerms generatedSqrtFuel generatedLogFuel 12
        (rootBox 1 2) = some generatedTree2 := by
  exact option_eq_some_getD_of_isSome (.accept ()) generated_builds_are_some.2.2.1

theorem generatedTree3_build :
    buildTree generatedTerms generatedSqrtFuel generatedLogFuel 16
        (rootBox 2 4) = some generatedTree3 := by
  exact option_eq_some_getD_of_isSome (.accept ()) generated_builds_are_some.2.2.2

theorem generatedTree0_check :
    generatedTree0.check
      (autoAccepts generatedTerms generatedSqrtFuel generatedLogFuel)
      noDiscard (rootBox (1 / 4) (1 / 2)) = true :=
  buildTree_check_of_eq _ _ _ _ _ _ generatedTree0_build

theorem generatedTree1_check :
    generatedTree1.check
      (autoAccepts generatedTerms generatedSqrtFuel generatedLogFuel)
      noDiscard (rootBox (1 / 2) 1) = true :=
  buildTree_check_of_eq _ _ _ _ _ _ generatedTree1_build

theorem generatedTree2_check :
    generatedTree2.check
      (autoAccepts generatedTerms generatedSqrtFuel generatedLogFuel)
      noDiscard (rootBox 1 2) = true :=
  buildTree_check_of_eq _ _ _ _ _ _ generatedTree2_build

theorem generatedTree3_check :
    generatedTree3.check
      (autoAccepts generatedTerms generatedSqrtFuel generatedLogFuel)
      noDiscard (rootBox 2 4) = true :=
  buildTree_check_of_eq _ _ _ _ _ _ generatedTree3_build

/-- Closed small-`s` bridge after instantiating all four generated roots. -/
theorem generated_halfMidpoint
    {s k chi : ℝ}
    (hs : s ∈ Set.Ioc (0 : ℝ) (1 / 16384))
    (hk : k ∈ Set.Icc (1 / 4 : ℝ) 4)
    (hchi : chi ∈ Set.Icc (0 : ℝ) 1) :
    (13 / 20 : ℝ) <
      lrCertificateHalfMidpointNumerator
        (⟨s, k, chi⟩ : CertificatePoint) / s :=
  halfMidpoint_of_four_roots generatedTerms generatedSqrtFuel generatedLogFuel
    generatedTree0_check generatedTree1_check generatedTree2_check
    generatedTree3_check hs hk hchi

/-- The generated small-`s` replay discharges the removed strip in the
middle-core theorem, leaving only the compact post-bridge obligation. -/
theorem generated_middleCoreCoordinate_of_postSmallSBridge
    (hpost : LRHighShapePostSmallSBridgeMidpointCoordinateTheorem) :
    LRHighShapeMiddleCoreMidpointCoordinateTheorem :=
  middleCoreCoordinate_of_postSmallSBridge_and_four_roots
    generatedTerms generatedSqrtFuel generatedLogFuel
    generatedTree0_check generatedTree1_check generatedTree2_check
    generatedTree3_check hpost

end LRSmallSBridgeCoreCertificate
end CourtadeKumar
