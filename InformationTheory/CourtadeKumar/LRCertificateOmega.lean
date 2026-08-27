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

lemma lrCertificateB_mem_Ioo {s y : ℝ}
    (hs : s ∈ Ioo (0 : ℝ) 1) (hy : y ∈ Ioo (0 : ℝ) 1) :
    lrCertificateB s y ∈ Ioo (0 : ℝ) 1 := by
  unfold lrCertificateB
  constructor
  · have hnonneg : 0 ≤ (1 - s) * y :=
      mul_nonneg (sub_nonneg.mpr hs.2.le) hy.1.le
    exact add_pos_of_pos_of_nonneg hs.1 hnonneg
  · nlinarith [mul_pos (sub_pos.mpr hs.2) (sub_pos.mpr hy.2)]

theorem hasDerivAt_lrCertificateB_along
    {z s y s' y' : ℝ} {sfun yfun : ℝ → ℝ}
    (hs : HasDerivAt sfun s' z) (hy : HasDerivAt yfun y' z)
    (hsz : sfun z = s) (hyz : yfun z = y) :
    HasDerivAt (fun q ↦ lrCertificateB (sfun q) (yfun q))
      (lrCertificateBDeriv s y s' y') z := by
  have h := hs.add (((hasDerivAt_const z 1).sub hs).mul hy)
  unfold lrCertificateB lrCertificateBDeriv
  convert h using 1 <;>
    simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, hsz, hyz] <;> ring

theorem hasDerivAt_lrCertificateOmega_along
    {z s y s' y' : ℝ} {sfun yfun : ℝ → ℝ}
    (hs : HasDerivAt sfun s' z) (hy : HasDerivAt yfun y' z)
    (hsz : sfun z = s) (hyz : yfun z = y)
    (hsMem : s ∈ Ioo (0 : ℝ) 1) (hyMem : y ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun q ↦ lrCertificateOmega (sfun q) (yfun q))
      (lrCertificateOmegaDeriv s y s' y') z := by
  have hb := hasDerivAt_lrCertificateB_along hs hy hsz hyz
  have hbMem := lrCertificateB_mem_Ioo hsMem hyMem
  have hbMem' : lrCertificateB (sfun z) (yfun z) ∈ Ioo (0 : ℝ) 1 := by
    simpa [hsz, hyz] using hbMem
  have hyMem' : yfun z ∈ Ioo (0 : ℝ) 1 := by simpa [hyz] using hyMem
  have hqb := (hasDerivAt_lrCertificateQ hbMem').comp z hb
  have hqy := (hasDerivAt_lrCertificateQ hyMem').comp z hy
  have hqpb := (hasDerivAt_lrCertificateQPrime hbMem').comp z hb
  have honeMinusY := (hasDerivAt_const z 1).sub hy
  have hfactor := (hs.mul honeMinusY).mul hqpb
  have h := (hqb.sub hqy).sub hfactor
  unfold lrCertificateOmega lrCertificateOmegaDeriv
  dsimp only
  convert h using 1 <;>
    simp only [Pi.mul_apply, Pi.sub_apply, Function.comp_apply, hsz, hyz] <;>
    ring

/-- Endpoint-safe specialization used by `W = omega_s(0)`.  It never
differentiates `Q` at zero; that term is constant along the path. -/
theorem hasDerivAt_lrCertificateOmega_zero_along
    {z s s' : ℝ} {sfun : ℝ → ℝ}
    (hs : HasDerivAt sfun s' z) (hsz : sfun z = s)
    (hsMem : s ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun q ↦ lrCertificateOmega (sfun q) 0)
      (lrCertificateOmegaDeriv s 0 s' 0) z := by
  have hsMem' : sfun z ∈ Ioo (0 : ℝ) 1 := by simpa [hsz] using hsMem
  have hqs := (hasDerivAt_lrCertificateQ hsMem').comp z hs
  have hqps := (hasDerivAt_lrCertificateQPrime hsMem').comp z hs
  have hqzero : HasDerivAt (fun _q : ℝ ↦ lrCertificateQ 0) 0 z :=
    hasDerivAt_const z _
  have hfactor := (hs.mul (hasDerivAt_const z 1)).mul hqps
  have h := (hqs.sub hqzero).sub hfactor
  unfold lrCertificateOmega lrCertificateOmegaDeriv lrCertificateB
    lrCertificateBDeriv
  dsimp only
  convert h using 1
  · funext q
    simp only [Pi.mul_apply, Pi.sub_apply, Function.comp_apply]
    ring
  · simp only [Pi.mul_apply, Function.comp_apply, hsz]
    ring

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
