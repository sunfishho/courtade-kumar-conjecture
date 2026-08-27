import InformationTheory.CourtadeKumar.LRHighShapeCoordinateAD

/-!
# Verified interval AD for the scalar `g₀(v)`

The cancellation-safe high-shape expression separates
`G_t(v) = g₀(v) + Q(y₀) + Q(e)/v`.  This module checks the three
logarithms in `g₀` and proves its exact derivative.
-/

namespace CourtadeKumar

noncomputable def lrCertificateG0 (v : ℝ) : ℝ :=
  (1 + 1 / v) * (Real.log (1 + v) - Real.log 2) - Real.log v

noncomputable def lrCertificateG0Prime (v : ℝ) : ℝ :=
  (Real.log 2 - Real.log (1 + v)) / v ^ 2

lemma lrCertificateG0_eq_lrG (v : ℝ) :
    lrCertificateG0 v = lrG v - (1 + 1 / v) * Real.log 2 := by
  unfold lrCertificateG0 lrG
  ring

/-- Untrusted range-reduction data for the three logarithm nodes. -/
structure LRG0ADCertificate where
  logV : RationalEnclosure.LogIntervalCertificate
  logOnePlusV : RationalEnclosure.LogIntervalCertificate
  logTwo : RationalEnclosure.LogIntervalCertificate

namespace LRG0ADCertificate

def onePlusV (v : IntervalAD) : IntervalAD :=
  IntervalAD.add (IntervalAD.const 1) v

def evaluate (terms : ℕ) (certificate : LRG0ADCertificate)
    (v : IntervalAD) : IntervalAD :=
  let logV := IntervalAD.log terms certificate.logV v
  let logOnePlus := IntervalAD.log terms certificate.logOnePlusV
    (onePlusV v)
  let logTwo := IntervalAD.log terms certificate.logTwo (IntervalAD.const 2)
  let factor := IntervalAD.add (IntervalAD.const 1) (IntervalAD.invPositive v)
  IntervalAD.sub (IntervalAD.mul factor (IntervalAD.sub logOnePlus logTwo)) logV

def check (v : IntervalAD) (certificate : LRG0ADCertificate) : Bool :=
  decide (
    certificate.logV.check v.value = true ∧
    certificate.logOnePlusV.check (onePlusV v).value = true ∧
    certificate.logTwo.check (IntervalAD.const 2).value = true ∧
    (0 : ℚ) < v.value.lower)

theorem sound (terms : ℕ) {certificate : LRG0ADCertificate}
    {vAD : IntervalAD} {v vS vK vChi : ℝ}
    (hcheck : certificate.check vAD = true)
    (hv : vAD.Contains v vS vK vChi) :
    (certificate.evaluate terms vAD).Contains (lrCertificateG0 v)
      (lrCertificateG0Prime v * vS)
      (lrCertificateG0Prime v * vK)
      (lrCertificateG0Prime v * vChi) := by
  have hparts :
      certificate.logV.check vAD.value = true ∧
      certificate.logOnePlusV.check (onePlusV vAD).value = true ∧
      certificate.logTwo.check (IntervalAD.const 2).value = true ∧
      (0 : ℚ) < vAD.value.lower := by
    simpa [check] using hcheck
  have hvPos : 0 < v := by
    have hlower : (0 : ℝ) < (vAD.value.lower : ℝ) := by
      exact_mod_cast hparts.2.2.2
    exact hlower.trans_le hv.1.1
  have honePlus := IntervalAD.contains_add (IntervalAD.contains_const 1) hv
  have hlogV := IntervalAD.contains_log terms hparts.1 hv
  have hlogOnePlus := IntervalAD.contains_log terms hparts.2.1 honePlus
  have hlogTwo := IntervalAD.contains_log terms hparts.2.2.1
    (IntervalAD.contains_const 2)
  have hinv := IntervalAD.contains_invPositive hparts.2.2.2 hv
  have hfactor := IntervalAD.contains_add (IntervalAD.contains_const 1) hinv
  have hdelta := IntervalAD.contains_sub hlogOnePlus hlogTwo
  have hprod := IntervalAD.contains_mul hfactor hdelta
  have h := IntervalAD.contains_sub hprod hlogV
  unfold evaluate lrCertificateG0 lrCertificateG0Prime onePlusV
  dsimp only
  convert h using 1 <;> field_simp [hvPos.ne'] <;> ring_nf

end LRG0ADCertificate
end CourtadeKumar
