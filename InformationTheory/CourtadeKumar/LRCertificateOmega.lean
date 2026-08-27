import InformationTheory.CourtadeKumar.LRCertificateQAD
import InformationTheory.CourtadeKumar.LRHighShapeCertificateCoordinates

/-!
# The cancellation-safe LR noise kernel

The exact certificate evaluates the manuscript primitive
`omega_s(y) = Q(b_s(y)) - Q(y) - s(1-y)Q'(b_s(y))`.
This file supplies its verified interval-AD node and identifies it with the
existing analytic `lrWKernel` after `y = 1-z²`, `R = 1-s`.
-/

open Set

namespace CourtadeKumar

def lrCertificateB (s y : ℝ) : ℝ :=
  s + (1 - s) * y

noncomputable def lrCertificateOmega (s y : ℝ) : ℝ :=
  lrCertificateQ (lrCertificateB s y) - lrCertificateQ y -
    s * (1 - y) * lrCertificateQPrime (lrCertificateB s y)

def lrCertificateBDeriv (s y s' y' : ℝ) : ℝ :=
  s' + (-s') * y + (1 - s) * y'

noncomputable def lrCertificateOmegaDeriv
    (s y s' y' : ℝ) : ℝ :=
  let b := lrCertificateB s y
  let b' := lrCertificateBDeriv s y s' y'
  lrCertificateQPrime b * b' - lrCertificateQPrime y * y' -
    (s' * (1 - y) * lrCertificateQPrime b +
      s * (-y') * lrCertificateQPrime b +
      s * (1 - y) * (lrCertificateQSecond b * b'))

def lrCertificateBAD (s y : IntervalAD) : IntervalAD :=
  IntervalAD.add s
    (IntervalAD.mul (IntervalAD.sub (IntervalAD.const 1) s) y)

theorem lrCertificateBAD_sound {sAD yAD : IntervalAD}
    {s y sS sK sChi yS yK yChi : ℝ}
    (hs : sAD.Contains s sS sK sChi)
    (hy : yAD.Contains y yS yK yChi) :
    (lrCertificateBAD sAD yAD).Contains (lrCertificateB s y)
      (lrCertificateBDeriv s y sS yS)
      (lrCertificateBDeriv s y sK yK)
      (lrCertificateBDeriv s y sChi yChi) := by
  have honeMinus := IntervalAD.contains_sub (IntervalAD.contains_const 1) hs
  have hprod := IntervalAD.contains_mul honeMinus hy
  have h := IntervalAD.contains_add hs hprod
  unfold lrCertificateBAD lrCertificateB lrCertificateBDeriv
  convert h using 1 <;> ring

/-- The three scalar certificate nodes needed for one `omega` evaluation. -/
structure LROmegaADCertificate where
  qAtB : LRQADCertificate
  qAtY : LRQADCertificate
  qPrimeAtB : LRQPrimeADCertificate

namespace LROmegaADCertificate

def check (s y : IntervalAD) (certificate : LROmegaADCertificate) : Bool :=
  certificate.qAtB.check (lrCertificateBAD s y).value &&
    certificate.qAtY.check y.value &&
    certificate.qPrimeAtB.check (lrCertificateBAD s y).value

def evaluate (terms : ℕ) (certificate : LROmegaADCertificate)
    (s y : IntervalAD) : IntervalAD :=
  let b := lrCertificateBAD s y
  let qb := certificate.qAtB.evaluate terms b
  let qy := certificate.qAtY.evaluate terms y
  let qpb := certificate.qPrimeAtB.evaluate terms b
  IntervalAD.sub (IntervalAD.sub qb qy)
    (IntervalAD.mul (IntervalAD.mul s
      (IntervalAD.sub (IntervalAD.const 1) y)) qpb)

theorem sound (terms : ℕ) {certificate : LROmegaADCertificate}
    {sAD yAD : IntervalAD} {s y sS sK sChi yS yK yChi : ℝ}
    (hcheck : certificate.check sAD yAD = true)
    (hs : sAD.Contains s sS sK sChi)
    (hy : yAD.Contains y yS yK yChi) :
    (certificate.evaluate terms sAD yAD).Contains
      (lrCertificateOmega s y)
      (lrCertificateOmegaDeriv s y sS yS)
      (lrCertificateOmegaDeriv s y sK yK)
      (lrCertificateOmegaDeriv s y sChi yChi) := by
  let bAD := lrCertificateBAD sAD yAD
  have hraw :
      (certificate.qAtB.check bAD.value = true ∧
        certificate.qAtY.check yAD.value = true) ∧
      certificate.qPrimeAtB.check bAD.value = true := by
    simpa [check, bAD] using hcheck
  have hb := lrCertificateBAD_sound hs hy
  have hqb := certificate.qAtB.sound terms hraw.1.1 hb
  have hqy := certificate.qAtY.sound terms hraw.1.2 hy
  have hqpb := certificate.qPrimeAtB.sound terms hraw.2 hb
  have honeMinusY := IntervalAD.contains_sub (IntervalAD.contains_const 1) hy
  have hfactor := IntervalAD.contains_mul hs honeMinusY
  have hcorrection := IntervalAD.contains_mul hfactor hqpb
  have h := IntervalAD.contains_sub (IntervalAD.contains_sub hqb hqy) hcorrection
  unfold evaluate lrCertificateOmega lrCertificateOmegaDeriv
    lrCertificateBDeriv
  dsimp only
  simp only [lrCertificateBDeriv] at h
  convert h using 1 <;> ring

end LROmegaADCertificate

/-- The certificate primitive is exactly the analytic `W` kernel in squared
complement coordinates. -/
theorem lrCertificateOmega_one_sub_sq
    {s z : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) (hz : z ∈ Ioc (0 : ℝ) 1) :
    lrCertificateOmega s (1 - z ^ 2) = lrWKernel (1 - s) z := by
  have hzPos : 0 < z := hz.1
  have hb : lrCertificateB s (1 - z ^ 2) =
      1 - (1 - s) * z ^ 2 := by
    unfold lrCertificateB
    ring
  have hsqrtY : Real.sqrt (1 - (1 - z ^ 2)) = z := by
    rw [show 1 - (1 - z ^ 2) = z ^ 2 by ring,
      Real.sqrt_sq_eq_abs, abs_of_pos hzPos]
  have hsqrtB :
      Real.sqrt (1 - lrCertificateB s (1 - z ^ 2)) =
        Real.sqrt (1 - s) * z := by
    rw [hb, show 1 - (1 - (1 - s) * z ^ 2) = (1 - s) * z ^ 2 by ring,
      Real.sqrt_mul (sub_nonneg.mpr hs.2.le), Real.sqrt_sq_eq_abs,
      abs_of_pos hzPos]
  have hsqrtRPos : 0 < Real.sqrt (1 - s) := Real.sqrt_pos.2 (sub_pos.mpr hs.2)
  unfold lrCertificateOmega
  rw [lrCertificateQ_eq, lrCertificateQ_eq,
    lrCertificateQPrime_eq, hsqrtY, hsqrtB]
  unfold lrWKernel
  field_simp [hsqrtRPos.ne', hzPos.ne']
  ring

end CourtadeKumar
