import InformationTheory.CourtadeKumar.LRSmallSBridgeChi

/-!
# Algebraic core of the frozen small-`s` bridge

This file contains only the definitions and exact identity needed by interval
certificate replay.  The affine endpoint reduction, which additionally uses
the global positivity theorem for `lrSmallSBridgeLCoeff`, remains in
`LRSmallSBridgeFrozen`.
-/

namespace CourtadeKumar

noncomputable def lrSmallSBridgeAR (s k chi : ℝ) : ℝ :=
  (chi * Real.log (1 + (1 - s) * k * chi) +
    Real.log (1 + (1 - s) * k)) / (1 + chi)

noncomputable def lrSmallSBridgeP (s k chi L : ℝ) : ℝ :=
  L + 2 * Real.log 2 + 1 - s - lrSmallSBridgeAR s k chi

noncomputable def lrSmallSBridgeG (k chi L : ℝ) : ℝ :=
  L - Real.log k + 2 * Real.log 2 + 1 - lrSmallSBridgeQChi chi

noncomputable def lrSmallSBridgeS (s k chi L : ℝ) : ℝ :=
  lrSmallSBridgeP s k chi L - lrSmallSBridgeG k chi L

noncomputable def lrSmallSBridgeD (s k : ℝ) : ℝ :=
  Real.log ((1 + (1 - s) * k) / k) / 2

/-- The frozen normalized reserve.  `b` denotes the `L`-independent part
of the exact outer coefficient `B = L/2+b`; its precise formula is irrelevant
for the affine reduction. -/
noncomputable def lrSmallSBridgeFrozen
    (s k chi L b : ℝ) : ℝ :=
  k * (1 + chi) / 4 *
      (lrSmallSBridgeD s k * lrSmallSBridgeP s k chi L +
        (L / 2 + b) * lrSmallSBridgeS s k chi L) +
    ((L / 2 + b) - lrSmallSBridgeD s k) / 4

lemma lrSmallSBridgeS_eq
    (s k chi L : ℝ) :
    lrSmallSBridgeS s k chi L =
      Real.log k - s - lrSmallSBridgeAR s k chi +
        lrSmallSBridgeQChi chi := by
  unfold lrSmallSBridgeS lrSmallSBridgeP lrSmallSBridgeG
  ring

end CourtadeKumar
