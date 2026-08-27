import InformationTheory.CourtadeKumar.LRCompactVCorrelatedGeneratedCertificate

/-!
# Compact replay ledger through `R=9/10`

The five high-channel Boolean replay obligations use the audited truncation
length `N=64` and slab depths `33,33,34,34,34`.  This module assembles their
soundness with the earlier ledger through `R=17/20`.
-/

namespace CourtadeKumar

def lrCompactVR1720R78Generated := generateLRCompactVCorrelatedCertificate
  34 64 72 64 16 33 lrCompactVR1720R78Root

def lrCompactVR1720R78Replay : Prop :=
  lrCompactVR1720R78Generated.check
    (LRCompactVCorrelatedLeafCertificate.check 34 64 72 64)
    (LRCompactVDiscardCertificate.check 34)
    lrCompactVR1720R78Root = true

def lrCompactVR78R113128Generated := generateLRCompactVCorrelatedCertificate
  34 64 72 64 16 33 lrCompactVR78R113128Root

def lrCompactVR78R113128Replay : Prop :=
  lrCompactVR78R113128Generated.check
    (LRCompactVCorrelatedLeafCertificate.check 34 64 72 64)
    (LRCompactVDiscardCertificate.check 34)
    lrCompactVR78R113128Root = true

def lrCompactVR113128R227256Generated :=
  generateLRCompactVCorrelatedCertificate
    34 64 72 64 16 34 lrCompactVR113128R227256Root

def lrCompactVR113128R227256Replay : Prop :=
  lrCompactVR113128R227256Generated.check
    (LRCompactVCorrelatedLeafCertificate.check 34 64 72 64)
    (LRCompactVDiscardCertificate.check 34)
    lrCompactVR113128R227256Root = true

def lrCompactVR227256R9211024Generated :=
  generateLRCompactVCorrelatedCertificate
    34 64 72 64 16 34 lrCompactVR227256R9211024Root

def lrCompactVR227256R9211024Replay : Prop :=
  lrCompactVR227256R9211024Generated.check
    (LRCompactVCorrelatedLeafCertificate.check 34 64 72 64)
    (LRCompactVDiscardCertificate.check 34)
    lrCompactVR227256R9211024Root = true

def lrCompactVR9211024R910Generated :=
  generateLRCompactVCorrelatedCertificate
    34 64 72 64 16 34 lrCompactVR9211024R910Root

def lrCompactVR9211024R910Replay : Prop :=
  lrCompactVR9211024R910Generated.check
    (LRCompactVCorrelatedLeafCertificate.check 34 64 72 64)
    (LRCompactVDiscardCertificate.check 34)
    lrCompactVR9211024R910Root = true

structure LRCompactVR910ReplayLedger : Prop where
  through_r1720 : LRCompactVR1720ReplayLedger
  r1720_r78 : lrCompactVR1720R78Replay
  r78_r113128 : lrCompactVR78R113128Replay
  r113128_r227256 : lrCompactVR113128R227256Replay
  r227256_r9211024 : lrCompactVR227256R9211024Replay
  r9211024_r910 : lrCompactVR9211024R910Replay

theorem LRCompactVR910ReplayLedger.v_nonnegative
    (ledger : LRCompactVR910ReplayLedger) :
    ∀ (R v t : ℝ),
      R ∈ Set.Ioo (0 : ℝ) 1 → R ≤ 9 / 10 →
      v ∈ Set.Ioo (0 : ℝ) 1 → 1 / 3 ≤ v →
      t ∈ Set.Ioo (0 : ℝ) 1 → 17 / 20 ≤ t ^ 2 →
      0 < lrFlowJ R v t →
      0 ≤ lrLowVReserve R v t := by
  intro R v t hR hRUpper hv hvLower ht htLower hJ
  by_cases hR1720 : R ≤ 17 / 20
  · exact ledger.through_r1720.v_nonnegative
      R v t hR hR1720 hv hvLower ht htLower hJ
  by_cases hR78 : R ≤ 7 / 8
  · exact generatedLRCompactVCorrelatedSlab_sound
      34 64 72 64 16 33 (17 / 20) (7 / 8)
      ledger.r1720_r78 R v t hR (by norm_num; linarith)
      (by norm_num at hR78 ⊢; exact hR78)
      hv hvLower ht htLower hJ
  by_cases hR113128 : R ≤ 113 / 128
  · exact generatedLRCompactVCorrelatedSlab_sound
      34 64 72 64 16 33 (7 / 8) (113 / 128)
      ledger.r78_r113128 R v t hR (by norm_num; linarith)
      (by norm_num at hR113128 ⊢; exact hR113128)
      hv hvLower ht htLower hJ
  by_cases hR227256 : R ≤ 227 / 256
  · exact generatedLRCompactVCorrelatedSlab_sound
      34 64 72 64 16 34 (113 / 128) (227 / 256)
      ledger.r113128_r227256 R v t hR (by norm_num; linarith)
      (by norm_num at hR227256 ⊢; exact hR227256)
      hv hvLower ht htLower hJ
  by_cases hR9211024 : R ≤ 921 / 1024
  · exact generatedLRCompactVCorrelatedSlab_sound
      34 64 72 64 16 34 (227 / 256) (921 / 1024)
      ledger.r227256_r9211024 R v t hR (by norm_num; linarith)
      (by norm_num at hR9211024 ⊢; exact hR9211024)
      hv hvLower ht htLower hJ
  · exact generatedLRCompactVCorrelatedSlab_sound
      34 64 72 64 16 34 (921 / 1024) (9 / 10)
      ledger.r9211024_r910 R v t hR (by norm_num; linarith)
      (by norm_num at hRUpper ⊢; exact hRUpper)
      hv hvLower ht htLower hJ

end CourtadeKumar
