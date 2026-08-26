#!/usr/bin/env python3
"""Generate the exact Lean Bernstein certificate for the V endpoint."""

from math import comb
from pathlib import Path
import sys

import sympy as sp

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
import verify_lr_x85_UV_certificate as verifier  # noqa: E402


def lean_rat(q):
    q = sp.Rational(q)
    return str(q.p) if q.q == 1 else f"({q.p}/{q.q})"


def add_tree(items):
    if not items:
        return "0"
    if len(items) == 1:
        return items[0]
    cut = len(items) // 2
    return f"({add_tree(items[:cut])} + {add_tree(items[cut:])})"


def main():
    verifier.install_bounds()
    base = verifier.base
    v = verifier.v
    radial = (1 + v) ** 9 * (2 + v) ** 9
    positive_base = radial * (20 - 17 * v**2)
    expression = base.endpoint_minorant()
    numerator = base.positive_numerator(expression, positive_base)
    denominator = sp.fraction(sp.factor(sp.together(expression)))[1]
    quotient = sp.factor(denominator / positive_base)
    if quotient < 0:
        quotient = -quotient
    assert quotient == 6450271027200000000000000

    poly = sp.Poly(sp.expand(numerator), v)
    degree = poly.degree()
    assert degree == 44
    power = [poly.coeff_monomial(v**i) for i in range(degree + 1)]
    bernstein = [
        sum(
            power[j] * sp.Rational(comb(i, j), comb(degree, j))
            for j in range(i + 1)
        )
        for i in range(degree + 1)
    ]
    assert all(q > 0 for q in bernstein)

    bern_terms = [
        f"{lean_rat(q)} * bernsteinBasis {degree} {i} v"
        for i, q in enumerate(bernstein)
    ]
    power_terms = [
        f"{lean_rat(q)} * v ^ {i}" for i, q in enumerate(power) if q
    ]
    out = [
        "import InformationTheory.CourtadeKumar.LRLowShapeVGCertificate",
        "",
        "/-! Exact Bernstein certificate for the low-shape V endpoint. -/",
        "",
        "open Set",
        "open scoped BigOperators",
        "",
        "namespace CourtadeKumar",
        "",
        "noncomputable def lrLowVPhiEndpointFirstUpper : ℝ :=",
        "  (∑ k ∈ Finset.range 12, lrLowA (k + 1) * (17 / 20 : ℝ) ^ (k + 1)) +",
        "    lrLowA 13 * (17 / 20 : ℝ) ^ 13 / (1 - 17 / 20)",
        "",
        "noncomputable def lrLowVPhiEndpointSecondUpper (v : ℝ) : ℝ :=",
        "  (∑ k ∈ Finset.range 12,",
        "    lrLowA (k + 1) * (17 / 20 : ℝ) ^ (k + 1) *",
        "      v ^ (2 * (k + 1) - 1)) +",
        "    lrLowA 13 * (17 / 20 : ℝ) ^ 13 * v ^ 25 /",
        "      (1 - (17 / 20 : ℝ) * v ^ 2)",
        "",
        "noncomputable def lrLowVLEndpointUpper (v : ℝ) : ℝ :=",
        "  (∑ k ∈ Finset.range 12,",
        "    ((17 / 20 : ℝ) * v ^ 2) ^ (k + 1) / (2 * (k + 1))) +",
        "    ((17 / 20 : ℝ) * v ^ 2) ^ 13 /",
        "      (26 * (1 - (17 / 20 : ℝ) * v ^ 2))",
        "",
        "noncomputable def lrLowVBetaEndpointUpper (v : ℝ) : ℝ :=",
        "  lrAtanh5 (v / (2 + v)) +",
        "    v ^ 11 / (22 * (1 + v) * (2 + v) ^ 9)",
        "",
        "noncomputable def lrLowVEndpointMinorant (v : ℝ) : ℝ :=",
        "  lrLowGLower v - lrLowVPhiEndpointFirstUpper -",
        "    lrLowVPhiEndpointSecondUpper v -",
        "    2 * (1 - (17 / 20 : ℝ) * v ^ 2) *",
        "      (lrLowVBetaEndpointUpper v + lrLowVLEndpointUpper v) /",
        "      (v * (1 + v))",
        "",
        "noncomputable def lrLowVEndpointCertificateBase (v : ℝ) : ℝ :=",
        "  (1 + v) ^ 9 * (2 + v) ^ 9 *",
        "    (20 * (1 - (17 / 20 : ℝ) * v ^ 2))",
        "",
        "noncomputable def lrLowVEndpointBernstein (v : ℝ) : ℝ :=",
        f"  {add_tree(bern_terms)}",
        "",
        "lemma lrLowVEndpointBernstein_nonneg",
        "    {v : ℝ} (hv : v ∈ Icc (0 : ℝ) 1) :",
        "    0 ≤ lrLowVEndpointBernstein v := by",
        "  unfold lrLowVEndpointBernstein",
        "  repeat' apply add_nonneg",
        "  all_goals exact mul_nonneg (by norm_num) (bernsteinBasis_nonneg hv)",
        "",
        "noncomputable def lrLowVEndpointPowerEval (v : ℝ) : ℝ :=",
        f"  {add_tree(power_terms)}",
        "",
        "set_option maxRecDepth 100000 in",
        "set_option maxHeartbeats 8000000 in",
        "lemma lrLowVEndpointBernstein_eq_power (v : ℝ) :",
        "    lrLowVEndpointBernstein v = lrLowVEndpointPowerEval v := by",
        "  unfold lrLowVEndpointBernstein lrLowVEndpointPowerEval bernsteinBasis",
        "  norm_num [Nat.choose]",
        "  ring",
        "",
        "set_option maxRecDepth 100000 in",
        "set_option maxHeartbeats 20000000 in",
        "lemma lrLowVEndpoint_certificate_identity",
        "    {v : ℝ} (hv : v ∈ Ioc (0 : ℝ) 1) :",
        "    lrLowVEndpointMinorant v * lrLowVEndpointCertificateBase v *",
        f"        {quotient} =",
        "      lrLowVEndpointPowerEval v := by",
        "  have hv0 : v ≠ 0 := hv.1.ne'",
        "  have h1 : 1 + v ≠ 0 := by linarith [hv.1]",
        "  have h2 : 2 + v ≠ 0 := by linarith [hv.1]",
        "  have hvSq : v ^ 2 ≤ 1 := by",
        "    nlinarith [mul_nonneg (sub_nonneg.mpr hv.2)",
        "      (by linarith [hv.1] : 0 ≤ 1 + v)]",
        "  have hqPos : 0 < 1 - (17 / 20 : ℝ) * v ^ 2 := by",
        "    nlinarith",
        "  have hq : 1 - (17 / 20 : ℝ) * v ^ 2 ≠ 0 := hqPos.ne'",
        "  have hq20 : 20 - v ^ 2 * 17 ≠ 0 := by nlinarith [hvSq]",
        "  unfold lrLowVEndpointMinorant lrLowVPhiEndpointFirstUpper",
        "    lrLowVPhiEndpointSecondUpper lrLowVLEndpointUpper",
        "    lrLowVBetaEndpointUpper",
        "    lrLowVEndpointCertificateBase lrLowVEndpointPowerEval",
        "    lrLowGLower lrLowBetaLower lrLowMinusLogLower lrAtanh5 lrLowA",
        "  norm_num [Finset.sum_range_succ, Nat.choose]",
        "  field_simp [hv0, h1, h2, hq, hq20]",
        "  ring_nf",
        "",
        "theorem lrLowVEndpointMinorant_nonneg",
        "    {v : ℝ} (hv : v ∈ Ioc (0 : ℝ) 1) :",
        "    0 ≤ lrLowVEndpointMinorant v := by",
        "  have hbern := lrLowVEndpointBernstein_nonneg",
        "    (show v ∈ Icc (0 : ℝ) 1 from ⟨hv.1.le, hv.2⟩)",
        "  have hpower : 0 ≤ lrLowVEndpointPowerEval v := by",
        "    rw [← lrLowVEndpointBernstein_eq_power]",
        "    exact hbern",
        "  have hid := lrLowVEndpoint_certificate_identity hv",
        "  have hbase : 0 < lrLowVEndpointCertificateBase v := by",
        "    unfold lrLowVEndpointCertificateBase",
        "    have hvSq : v ^ 2 ≤ 1 := by",
        "      nlinarith [mul_nonneg (sub_nonneg.mpr hv.2)",
        "        (by linarith [hv.1] : 0 ≤ 1 + v)]",
        "    have hqPos : 0 < 1 - (17 / 20 : ℝ) * v ^ 2 := by nlinarith",
        "    exact mul_pos",
        "      (mul_pos (pow_pos (by linarith [hv.1]) _)",
        "        (pow_pos (by linarith [hv.1]) _))",
        "      (mul_pos (by norm_num) hqPos)",
        "  have hscale : 0 < lrLowVEndpointCertificateBase v *",
        f"      ({quotient} : ℝ) := mul_pos hbase (by norm_num)",
        "  have hprod : 0 ≤ (lrLowVEndpointCertificateBase v *",
        f"      {quotient}) * lrLowVEndpointMinorant v := by",
        "    rw [mul_comm, ← mul_assoc, hid]",
        "    exact hpower",
        "  exact nonneg_of_mul_nonneg_right hprod hscale",
        "",
        "end CourtadeKumar",
        "",
    ]
    target = Path(__file__).resolve().parents[1] / "InformationTheory/CourtadeKumar/LRLowShapeVEndpointCertificate.lean"
    target.write_text("\n".join(out))


if __name__ == "__main__":
    main()
