import AgentRootRatioNaturalGeometry
import AgentRootRatioNaturalQS
import AgentRootRatioNaturalQE
import AgentRootRatioNaturalQY
import AgentRootRatioNaturalQBe
import AgentRootRatioNaturalQBy

/-! Direct natural interval Cbase/Psi proof on the original depth-eight box.
Every entropy and logarithm enclosure is checked independently. There are no
corner monotonicity premises or automatic-evaluator payload assumptions. -/
set_option autoImplicit false
namespace CourtadeKumar.RootRatioNaturalComponents
open RationalEnclosure RootRatioBaseFaceD1Standalone RootRatioBaseFaceBStandalone
open RootRatioNaturalGeometry

theorem s_input_eq : RootRatioNaturalQS.input = sI := by
  norm_num [RootRatioNaturalQS.input, sI, point]
theorem e_input_eq : RootRatioNaturalQE.input = eI := by
  norm_num [RootRatioNaturalQE.input, eI, sI, kI, mul, point, center, radius]
theorem y_input_eq : RootRatioNaturalQY.input = yBounds := by
  norm_num [RootRatioNaturalQY.input, yBounds, chiI, eI, sI, kI,
    mulNonnegative, mul, point, center, radius]
theorem be_input_eq : RootRatioNaturalQBe.input = beI := by
  norm_num [RootRatioNaturalQBe.input, beI_eq]
theorem by_input_eq : RootRatioNaturalQBy.input = byBounds := by
  norm_num [RootRatioNaturalQBy.input, byBounds, yBounds, chiI, eI, sI, kI,
    mulNonnegative, mul, sub, add, neg, point, center, radius]

def wI : RationalEnclosure :=
  sub RootRatioNaturalQS.qBounds (mul sI RootRatioNaturalQS.primeBounds)
def ayI : RationalEnclosure :=
  sub (sub RootRatioNaturalQBy.qBounds
    (mul (mul sI (sub (point 1) yBounds)) RootRatioNaturalQBy.primeBounds)) wI
def aeI : RationalEnclosure :=
  sub (sub RootRatioNaturalQBe.qBounds
    (mul (mul sI (sub (point 1) eI)) RootRatioNaturalQBe.primeBounds)) wI
def cyI : RationalEnclosure := sub ayI RootRatioNaturalQY.qBounds
def ceI : RationalEnclosure := sub aeI RootRatioNaturalQE.qBounds
def onePlusI : RationalEnclosure := add (point 1) vBounds
def kappaI : RationalEnclosure := div
  (mul (sub (point 1) vBounds) (sub (point 1) vBounds)) (mul vBounds onePlusI)
def deltaI : RationalEnclosure :=
  div (sub (point 1) (mul vBounds xI)) onePlusI
def cI : RationalEnclosure := add (add cyI (div ceI vBounds))
  (mul (add kappaI (scale 4 deltaI)) wI)
def psiI : RationalEnclosure := add (add (add g0Bounds ayI) (div aeI vBounds))
  (mul kappaI wI)
def cBounds : RationalEnclosure := ⟨(-12235 / 524288), (-346487 / 16777216)⟩
def psiBounds : RationalEnclosure := ⟨(2277261 / 8388608), (4595613 / 16777216)⟩

theorem onePlus_positive : (0 : ℚ) < onePlusI.lower := by
  norm_num [onePlusI, vBounds, vPayload, SqrtCertificate.enclosure, add, point]
theorem vOnePlus_positive : (0 : ℚ) < (mul vBounds onePlusI).lower := by
  norm_num [onePlusI, vBounds, vPayload, SqrtCertificate.enclosure,
    mul, add, point, center, radius]

theorem c_cover : cBounds.lower ≤ cI.lower ∧ cI.upper ≤ cBounds.upper := by
  norm_num [cBounds, cI, cyI, ceI, ayI, aeI, wI, kappaI, deltaI, onePlusI,
    RootRatioNaturalQS.qBounds, RootRatioNaturalQS.primeBounds,
    RootRatioNaturalQY.qBounds, RootRatioNaturalQE.qBounds,
    RootRatioNaturalQBy.qBounds, RootRatioNaturalQBy.primeBounds,
    RootRatioNaturalQBe.qBounds, RootRatioNaturalQBe.primeBounds,
    vBounds, vPayload, SqrtCertificate.enclosure, xI_eq,
    yBounds, chiI, eI, sI, kI, mulNonnegative,
    div, invPositive, scale, mul, sub, add, neg, point, center, radius]
theorem psi_cover : psiBounds.lower ≤ psiI.lower ∧ psiI.upper ≤ psiBounds.upper := by
  norm_num [psiBounds, psiI, ayI, aeI, wI, kappaI, onePlusI, g0Bounds,
    RootRatioNaturalQS.qBounds, RootRatioNaturalQS.primeBounds,
    RootRatioNaturalQBy.qBounds, RootRatioNaturalQBy.primeBounds,
    RootRatioNaturalQBe.qBounds, RootRatioNaturalQBe.primeBounds,
    vBounds, vPayload, SqrtCertificate.enclosure,
    yBounds, chiI, eI, sI, kI, mulNonnegative,
    div, invPositive, scale, mul, sub, add, neg, point, center, radius]

noncomputable def wValue (s : ℝ) : ℝ := lrCertificateQ s - s * lrCertificateQPrime s
noncomputable def aValue (s y : ℝ) : ℝ :=
  lrCertificateQ (s + (1 - s) * y) -
    (s * (1 - y)) * lrCertificateQPrime (s + (1 - s) * y) - wValue s
noncomputable def cScalar (s y : ℝ) : ℝ := aValue s y - lrCertificateQ y
noncomputable def kappaValue (v : ℝ) : ℝ := ((1 - v) * (1 - v)) / (v * (1 + v))
noncomputable def deltaValue (v x : ℝ) : ℝ := (1 - v * x) / (1 + v)
noncomputable def cValue (s k chi : ℝ) : ℝ :=
  cScalar s (chi * (s * k)) + cScalar s (s * k) / vValue s k chi +
    (kappaValue (vValue s k chi) + 4 * deltaValue (vValue s k chi) (1 - chi * (s * k))) *
      wValue s
noncomputable def psiValue (s k chi : ℝ) : ℝ :=
  g0Value (vValue s k chi) + aValue s (chi * (s * k)) +
    aValue s (s * k) / vValue s k chi + kappaValue (vValue s k chi) * wValue s

theorem w_contains {s : ℝ} (hs : sI.Contains s) : wI.Contains (wValue s) := by
  have hinput : RootRatioNaturalQS.input.Contains s := by simpa only [s_input_eq] using hs
  exact contains_sub (RootRatioNaturalQS.q_contains hinput)
    (contains_mul hs (RootRatioNaturalQS.prime_contains hinput))

theorem ay_contains {s k chi : ℝ}
    (hs : sI.Contains s) (hk : kI.Contains k) (hc : chiI.Contains chi) :
    ayI.Contains (aValue s (chi * (s * k))) := by
  have hOne : (point 1).Contains (1 : ℝ) := by norm_num [point, Contains]
  have hby : RootRatioNaturalQBy.input.Contains (s + (1 - s) * (chi * (s * k))) := by
    simpa only [by_input_eq] using by_contains hs hk hc
  exact contains_sub (contains_sub (RootRatioNaturalQBy.q_contains hby)
    (contains_mul (contains_mul hs (contains_sub hOne (y_contains hs hk hc)))
      (RootRatioNaturalQBy.prime_contains hby))) (w_contains hs)

theorem ae_contains {s k : ℝ} (hs : sI.Contains s) (hk : kI.Contains k) :
    aeI.Contains (aValue s (s * k)) := by
  have hOne : (point 1).Contains (1 : ℝ) := by norm_num [point, Contains]
  have he : eI.Contains (s * k) := contains_mul hs hk
  have hbe : RootRatioNaturalQBe.input.Contains (s + (1 - s) * (s * k)) := by
    rw [be_input_eq]
    exact contains_add hs (contains_mul (contains_sub hOne hs) he)
  exact contains_sub (contains_sub (RootRatioNaturalQBe.q_contains hbe)
    (contains_mul (contains_mul hs (contains_sub hOne he))
      (RootRatioNaturalQBe.prime_contains hbe))) (w_contains hs)

theorem kappa_contains {v : ℝ} (hv : vBounds.Contains v) :
    kappaI.Contains (kappaValue v) := by
  have hOne : (point 1).Contains (1 : ℝ) := by norm_num [point, Contains]
  exact contains_div vOnePlus_positive
    (contains_mul (contains_sub hOne hv) (contains_sub hOne hv))
    (contains_mul hv (contains_add hOne hv))

theorem delta_contains {v x : ℝ} (hv : vBounds.Contains v) (hx : xI.Contains x) :
    deltaI.Contains (deltaValue v x) := by
  have hOne : (point 1).Contains (1 : ℝ) := by norm_num [point, Contains]
  exact contains_div onePlus_positive
    (contains_sub hOne (contains_mul hv hx)) (contains_add hOne hv)

theorem c_raw_contains {s k chi : ℝ}
    (hs : sI.Contains s) (hk : kI.Contains k) (hc : chiI.Contains chi) :
    cI.Contains (cValue s k chi) := by
  have hFour : (point 4).Contains (4 : ℝ) := by norm_num [point, Contains]
  have hv := v_contains hs hk hc
  have he : RootRatioNaturalQE.input.Contains (s * k) := by
    rw [e_input_eq]; exact contains_mul hs hk
  have hy : RootRatioNaturalQY.input.Contains (chi * (s * k)) := by
    simpa only [y_input_eq] using y_contains hs hk hc
  have hcy : cyI.Contains (cScalar s (chi * (s * k))) :=
    contains_sub (ay_contains hs hk hc) (RootRatioNaturalQY.q_contains hy)
  have hce : ceI.Contains (cScalar s (s * k)) :=
    contains_sub (ae_contains hs hk) (RootRatioNaturalQE.q_contains he)
  exact contains_add (contains_add hcy (contains_div v_positive hce hv))
    (contains_mul (contains_add (kappa_contains hv)
      (contains_mul hFour (delta_contains hv (x_contains hs hk hc)))) (w_contains hs))

theorem psi_raw_contains {s k chi : ℝ}
    (hs : sI.Contains s) (hk : kI.Contains k) (hc : chiI.Contains chi) :
    psiI.Contains (psiValue s k chi) := by
  have hv := v_contains hs hk hc
  exact contains_add
    (contains_add (contains_add (g0_contains hv) (ay_contains hs hk hc))
      (contains_div v_positive (ae_contains hs hk) hv))
    (contains_mul (kappa_contains hv) (w_contains hs))

theorem c_contains {s k chi : ℝ}
    (hs : sI.Contains s) (hk : kI.Contains k) (hc : chiI.Contains chi) :
    cBounds.Contains (cValue s k chi) := by
  have h := c_raw_contains hs hk hc
  have hlo : (cBounds.lower : ℝ) ≤ (cI.lower : ℝ) := by exact_mod_cast c_cover.1
  have hhi : (cI.upper : ℝ) ≤ (cBounds.upper : ℝ) := by exact_mod_cast c_cover.2
  exact ⟨hlo.trans h.1, h.2.trans hhi⟩

theorem psi_contains {s k chi : ℝ}
    (hs : sI.Contains s) (hk : kI.Contains k) (hc : chiI.Contains chi) :
    psiBounds.Contains (psiValue s k chi) := by
  have h := psi_raw_contains hs hk hc
  have hlo : (psiBounds.lower : ℝ) ≤ (psiI.lower : ℝ) := by exact_mod_cast psi_cover.1
  have hhi : (psiI.upper : ℝ) ≤ (psiBounds.upper : ℝ) := by exact_mod_cast psi_cover.2
  exact ⟨hlo.trans h.1, h.2.trans hhi⟩

#print axioms CourtadeKumar.RootRatioNaturalComponents.c_contains
#print axioms CourtadeKumar.RootRatioNaturalComponents.psi_contains
end CourtadeKumar.RootRatioNaturalComponents
