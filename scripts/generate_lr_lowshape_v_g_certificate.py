#!/usr/bin/env python3
"""Generate the exact Lean tensor-Bernstein certificate for `G_lower`."""

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


def tensor_rows(poly):
    p = sp.Poly(sp.expand(poly), verifier.v, verifier.z)
    dv, dz = p.degree_list()
    monomials = p.as_dict()
    return [
        [
            sum(
                monomials.get((av, az), 0)
                * sp.Rational(comb(i, av), comb(dv, av))
                * sp.Rational(comb(j, az), comb(dz, az))
                for av in range(i + 1)
                for az in range(j + 1)
            )
            for j in range(dz + 1)
        ]
        for i in range(dv + 1)
    ]


def add_tree(items):
    if not items:
        return "0"
    if len(items) == 1:
        return items[0]
    cut = len(items) // 2
    return f"({add_tree(items[:cut])} + {add_tree(items[cut:])})"


def bernstein_to_power(row):
    """Convert one degree-d Bernstein coefficient row to power coefficients."""
    degree = len(row) - 1
    return [
        sum(
            row[j] * comb(degree, j) * comb(degree - j, s - j)
            * (-1) ** (s - j)
            for j in range(s + 1)
        )
        for s in range(degree + 1)
    ]


def main():
    verifier.install_bounds()
    base = verifier.base
    v, z = verifier.v, verifier.z
    radial = (1 + v) ** 9 * (2 + v) ** 9
    positive_base = radial * (20 - 17 * z) * (20 - 17 * v**2 * z)
    numerator = base.positive_numerator(base.G_lower, positive_base)
    rows = tensor_rows(numerator)
    assert len(rows) == 44 and all(len(row) == 15 for row in rows)
    assert all(q >= 0 for row in rows for q in row)

    out = [
        "import InformationTheory.CourtadeKumar.LRLowShapeVMinorantBridge",
        "",
        "/-! Generated exact tensor-Bernstein certificate for the low-shape `G` minorant. -/",
        "",
        "open Set",
        "namespace CourtadeKumar",
        "",
    ]
    for i, row in enumerate(rows):
        terms = [
            f"{lean_rat(q)} * bernsteinBasis 14 {j} z"
            for j, q in enumerate(row) if q
        ]
        out += [
            f"noncomputable def lrLowVGLowerBernsteinRow{i} (z : ℝ) : ℝ :=",
            f"  {add_tree(terms)}",
            "",
            f"lemma lrLowVGLowerBernsteinRow{i}_nonneg",
            "    {z : ℝ} (hz : z ∈ Icc (0 : ℝ) 1) :",
            f"    0 ≤ lrLowVGLowerBernsteinRow{i} z := by",
            f"  unfold lrLowVGLowerBernsteinRow{i}",
            "  repeat' apply add_nonneg",
            "  all_goals exact mul_nonneg (by norm_num) (bernsteinBasis_nonneg hz)",
            "",
        ]
    outer = [
        f"lrLowVGLowerBernsteinRow{i} z * bernsteinBasis 43 {i} v"
        for i in range(44)
    ]
    out += [
        "noncomputable def lrLowVGLowerBernstein (v z : ℝ) : ℝ :=",
        f"  {add_tree(outer)}",
        "",
        "lemma lrLowVGLowerBernstein_nonneg",
        "    {v z : ℝ} (hv : v ∈ Icc (0 : ℝ) 1) (hz : z ∈ Icc (0 : ℝ) 1) :",
        "    0 ≤ lrLowVGLowerBernstein v z := by",
        "  unfold lrLowVGLowerBernstein",
        "  repeat' apply add_nonneg",
        *[
            f"  · exact mul_nonneg (lrLowVGLowerBernsteinRow{i}_nonneg hz) "
            f"(bernsteinBasis_nonneg hv)"
            for i in range(44)
        ],
        "",
        "end CourtadeKumar",
        "",
    ]
    target = Path(__file__).resolve().parents[1] / "InformationTheory/CourtadeKumar/LRLowShapeVGCertificateData.lean"
    target.write_text("\n".join(out))

    power_rows = [bernstein_to_power(row) for row in rows]
    poly = sp.Poly(sp.expand(numerator), v, z)
    monomials = poly.as_dict()
    out = [
        "import InformationTheory.CourtadeKumar.LRLowShapeVGCertificateData",
        "",
        "/-! Separable exact reconstruction of the low-shape `G` certificate. -/",
        "",
        "namespace CourtadeKumar",
        "",
    ]
    for i, row in enumerate(power_rows):
        terms = [f"{lean_rat(q)} * z ^ {s}" for s, q in enumerate(row) if q]
        out += [
            f"noncomputable def lrLowVGZPowerEvalRow{i} (z : ℝ) : ℝ :=",
            f"  {add_tree(terms)}",
            "",
            "set_option maxHeartbeats 2000000 in",
            f"lemma lrLowVGBernsteinRow{i}_eq_power (z : ℝ) :",
            f"    lrLowVGLowerBernsteinRow{i} z = lrLowVGZPowerEvalRow{i} z := by",
            f"  unfold lrLowVGLowerBernsteinRow{i} lrLowVGZPowerEvalRow{i} bernsteinBasis",
            "  norm_num [Nat.choose]",
            "  ring",
            "",
        ]
    outer = [
        f"lrLowVGZPowerEvalRow{i} z * bernsteinBasis 43 {i} v"
        for i in range(44)
    ]
    out += [
        "noncomputable def lrLowVGZPowerRowsEval (v z : ℝ) : ℝ :=",
        f"  {add_tree(outer)}",
        "",
        "lemma lrLowVGBernstein_eq_zPowerRows (v z : ℝ) :",
        "    lrLowVGLowerBernstein v z = lrLowVGZPowerRowsEval v z := by",
        "  unfold lrLowVGLowerBernstein lrLowVGZPowerRowsEval",
    ]
    for start in range(0, 44, 8):
        names = ", ".join(
            f"lrLowVGBernsteinRow{i}_eq_power"
            for i in range(start, min(start + 8, 44))
        )
        out.append(f"  rw [{names}]")

    for s in range(15):
        q_terms = [
            f"{lean_rat(power_rows[i][s])} * bernsteinBasis 43 {i} v"
            for i in range(44) if power_rows[i][s]
        ]
        p_terms = [
            f"{lean_rat(monomials.get((r, s), 0))} * v ^ {r}"
            for r in range(44) if monomials.get((r, s), 0)
        ]
        out += [
            "",
            f"noncomputable def lrLowVGZPowerEvalCol{s} (v : ℝ) : ℝ :=",
            f"  {add_tree(q_terms)}",
            "",
            f"noncomputable def lrLowVGVPowerEvalCol{s} (v : ℝ) : ℝ :=",
            f"  {add_tree(p_terms)}",
        ]

    z_columns = [f"lrLowVGZPowerEvalCol{s} v * z ^ {s}" for s in range(15)]
    v_columns = [f"lrLowVGVPowerEvalCol{s} v * z ^ {s}" for s in range(15)]
    out += [
        "",
        "noncomputable def lrLowVGZPowerColsEval (v z : ℝ) : ℝ :=",
        f"  {add_tree(z_columns)}",
        "",
        "noncomputable def lrLowVGPowerEval (v z : ℝ) : ℝ :=",
        f"  {add_tree(v_columns)}",
        "",
        "set_option maxHeartbeats 8000000 in",
        "lemma lrLowVGZPowerRows_eq_cols (v z : ℝ) :",
        "    lrLowVGZPowerRowsEval v z = lrLowVGZPowerColsEval v z := by",
        "  unfold lrLowVGZPowerRowsEval lrLowVGZPowerColsEval",
    ]
    out += [f"  unfold lrLowVGZPowerEvalRow{i}" for i in range(44)]
    out += [f"  unfold lrLowVGZPowerEvalCol{s}" for s in range(15)]
    out.append("  ring")

    for s in range(15):
        out += [
            "",
            "set_option maxHeartbeats 8000000 in",
            f"lemma lrLowVGZPowerEvalCol{s}_eq_power (v : ℝ) :",
            f"    lrLowVGZPowerEvalCol{s} v = lrLowVGVPowerEvalCol{s} v := by",
            f"  unfold lrLowVGZPowerEvalCol{s} lrLowVGVPowerEvalCol{s} bernsteinBasis",
            "  norm_num [Nat.choose]",
            "  ring",
        ]
    out += [
        "",
        "lemma lrLowVGZPowerCols_eq_power (v z : ℝ) :",
        "    lrLowVGZPowerColsEval v z = lrLowVGPowerEval v z := by",
        "  unfold lrLowVGZPowerColsEval lrLowVGPowerEval",
    ]
    for start in range(0, 15, 8):
        names = ", ".join(
            f"lrLowVGZPowerEvalCol{s}_eq_power"
            for s in range(start, min(start + 8, 15))
        )
        out.append(f"  rw [{names}]")
    out += [
        "",
        "theorem lrLowVGBernstein_eq_power (v z : ℝ) :",
        "    lrLowVGLowerBernstein v z = lrLowVGPowerEval v z := by",
        "  rw [lrLowVGBernstein_eq_zPowerRows, lrLowVGZPowerRows_eq_cols,",
        "    lrLowVGZPowerCols_eq_power]",
        "",
        "end CourtadeKumar",
        "",
    ]
    power_target = Path(__file__).resolve().parents[1] / "InformationTheory/CourtadeKumar/LRLowShapeVGPower.lean"
    power_target.write_text("\n".join(out))


if __name__ == "__main__":
    main()
