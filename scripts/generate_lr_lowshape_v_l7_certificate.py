#!/usr/bin/env python3
"""Generate the exact Lean tensor-Bernstein certificate for low-shape `L_7`."""

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
    numerator = base.positive_numerator(base.lower_comparison(7), positive_base)
    rows = tensor_rows(numerator)
    degree_v = len(rows) - 1
    degree_z = len(rows[0]) - 1
    assert (degree_v, degree_z) == (67, 26)
    assert all(q >= 0 for row in rows for q in row)

    out = [
        "import InformationTheory.CourtadeKumar.LRLowShapeVMinorantBridge",
        "",
        "/-! Generated exact tensor-Bernstein certificate for the low-shape `L_7` minorant. -/",
        "",
        "open Set",
        "namespace CourtadeKumar",
        "",
    ]
    for i, row in enumerate(rows):
        terms = [
            f"{lean_rat(q)} * bernsteinBasis {degree_z} {j} z"
            for j, q in enumerate(row) if q
        ]
        proof = ([
            f"  unfold lrLowVL7BernsteinRow{i}",
            "  repeat' apply add_nonneg",
            "  all_goals exact mul_nonneg (by norm_num) (bernsteinBasis_nonneg hz)",
        ] if terms else [f"  simp [lrLowVL7BernsteinRow{i}]"])
        out += [
            f"noncomputable def lrLowVL7BernsteinRow{i} (z : ℝ) : ℝ :=",
            f"  {add_tree(terms)}",
            "",
            f"lemma lrLowVL7BernsteinRow{i}_nonneg",
            "    {z : ℝ} (hz : z ∈ Icc (0 : ℝ) 1) :",
            f"    0 ≤ lrLowVL7BernsteinRow{i} z := by",
            *proof,
            "",
        ]
    outer = [
        f"lrLowVL7BernsteinRow{i} z * bernsteinBasis {degree_v} {i} v"
        for i in range(degree_v + 1)
    ]
    out += [
        "noncomputable def lrLowVL7Bernstein (v z : ℝ) : ℝ :=",
        f"  {add_tree(outer)}",
        "",
        "lemma lrLowVL7Bernstein_nonneg",
        "    {v z : ℝ} (hv : v ∈ Icc (0 : ℝ) 1) (hz : z ∈ Icc (0 : ℝ) 1) :",
        "    0 ≤ lrLowVL7Bernstein v z := by",
        "  unfold lrLowVL7Bernstein",
        "  repeat' apply add_nonneg",
        *[
            f"  · exact mul_nonneg (lrLowVL7BernsteinRow{i}_nonneg hz) "
            f"(bernsteinBasis_nonneg hv)"
            for i in range(degree_v + 1)
        ],
        "",
        "end CourtadeKumar",
        "",
    ]
    target = Path(__file__).resolve().parents[1] / "InformationTheory/CourtadeKumar/LRLowShapeVL7CertificateData.lean"
    target.write_text("\n".join(out))

    power_rows = [bernstein_to_power(row) for row in rows]
    poly = sp.Poly(sp.expand(numerator), v, z)
    monomials = poly.as_dict()
    out = [
        "import InformationTheory.CourtadeKumar.LRLowShapeVL7CertificateData",
        "",
        "/-! Separable exact reconstruction of the low-shape `L_7` certificate. -/",
        "",
        "namespace CourtadeKumar",
        "",
    ]
    for i, row in enumerate(power_rows):
        terms = [f"{lean_rat(q)} * z ^ {s}" for s, q in enumerate(row) if q]
        proof = ([
            f"  unfold lrLowVL7BernsteinRow{i} lrLowVL7ZPowerEvalRow{i} bernsteinBasis",
            "  norm_num [Nat.choose]",
            "  ring",
        ] if terms else [
            f"  simp [lrLowVL7BernsteinRow{i}, lrLowVL7ZPowerEvalRow{i}]"
        ])
        out += [
            f"noncomputable def lrLowVL7ZPowerEvalRow{i} (z : ℝ) : ℝ :=",
            f"  {add_tree(terms)}",
            "",
            "set_option maxHeartbeats 2000000 in",
            f"lemma lrLowVL7BernsteinRow{i}_eq_power (z : ℝ) :",
            f"    lrLowVL7BernsteinRow{i} z = lrLowVL7ZPowerEvalRow{i} z := by",
            *proof,
            "",
        ]
    outer = [
        f"lrLowVL7ZPowerEvalRow{i} z * bernsteinBasis {degree_v} {i} v"
        for i in range(degree_v + 1)
    ]
    out += [
        "noncomputable def lrLowVL7ZPowerRowsEval (v z : ℝ) : ℝ :=",
        f"  {add_tree(outer)}",
        "",
        "lemma lrLowVL7Bernstein_eq_zPowerRows (v z : ℝ) :",
        "    lrLowVL7Bernstein v z = lrLowVL7ZPowerRowsEval v z := by",
        "  unfold lrLowVL7Bernstein lrLowVL7ZPowerRowsEval",
    ]
    for start in range(0, degree_v + 1, 8):
        names = ", ".join(
            f"lrLowVL7BernsteinRow{i}_eq_power"
            for i in range(start, min(start + 8, degree_v + 1))
        )
        out.append(f"  rw [{names}]")

    for s in range(degree_z + 1):
        q_terms = [
            f"{lean_rat(power_rows[i][s])} * bernsteinBasis {degree_v} {i} v"
            for i in range(degree_v + 1) if power_rows[i][s]
        ]
        p_terms = [
            f"{lean_rat(monomials.get((r, s), 0))} * v ^ {r}"
            for r in range(degree_v + 1) if monomials.get((r, s), 0)
        ]
        out += [
            "",
            f"noncomputable def lrLowVL7ZPowerEvalCol{s} (v : ℝ) : ℝ :=",
            f"  {add_tree(q_terms)}",
            "",
            f"noncomputable def lrLowVL7VPowerEvalCol{s} (v : ℝ) : ℝ :=",
            f"  {add_tree(p_terms)}",
        ]

    z_columns = [f"lrLowVL7ZPowerEvalCol{s} v * z ^ {s}" for s in range(degree_z + 1)]
    v_columns = [f"lrLowVL7VPowerEvalCol{s} v * z ^ {s}" for s in range(degree_z + 1)]
    out += [
        "",
        "noncomputable def lrLowVL7ZPowerColsEval (v z : ℝ) : ℝ :=",
        f"  {add_tree(z_columns)}",
        "",
        "noncomputable def lrLowVL7PowerEval (v z : ℝ) : ℝ :=",
        f"  {add_tree(v_columns)}",
        "",
        "set_option maxHeartbeats 8000000 in",
        "lemma lrLowVL7ZPowerRows_eq_cols (v z : ℝ) :",
        "    lrLowVL7ZPowerRowsEval v z = lrLowVL7ZPowerColsEval v z := by",
        "  unfold lrLowVL7ZPowerRowsEval lrLowVL7ZPowerColsEval",
    ]
    out += [f"  unfold lrLowVL7ZPowerEvalRow{i}" for i in range(degree_v + 1)]
    out += [f"  unfold lrLowVL7ZPowerEvalCol{s}" for s in range(degree_z + 1)]
    out.append("  ring")

    for s in range(degree_z + 1):
        col_is_zero = not any(power_rows[i][s] for i in range(degree_v + 1))
        out += [
            "",
            "set_option maxHeartbeats 8000000 in",
            f"lemma lrLowVL7ZPowerEvalCol{s}_eq_power (v : ℝ) :",
            f"    lrLowVL7ZPowerEvalCol{s} v = lrLowVL7VPowerEvalCol{s} v := by",
            *([f"  simp [lrLowVL7ZPowerEvalCol{s}, lrLowVL7VPowerEvalCol{s}]"]
              if col_is_zero else [
                f"  unfold lrLowVL7ZPowerEvalCol{s} lrLowVL7VPowerEvalCol{s} bernsteinBasis",
                "  norm_num [Nat.choose]",
                "  ring",
              ]),
        ]
    out += [
        "",
        "lemma lrLowVL7ZPowerCols_eq_power (v z : ℝ) :",
        "    lrLowVL7ZPowerColsEval v z = lrLowVL7PowerEval v z := by",
        "  unfold lrLowVL7ZPowerColsEval lrLowVL7PowerEval",
    ]
    for start in range(0, degree_z + 1, 8):
        names = ", ".join(
            f"lrLowVL7ZPowerEvalCol{s}_eq_power"
            for s in range(start, min(start + 8, degree_z + 1))
        )
        out.append(f"  rw [{names}]")
    out += [
        "",
        "theorem lrLowVL7Bernstein_eq_power (v z : ℝ) :",
        "    lrLowVL7Bernstein v z = lrLowVL7PowerEval v z := by",
        "  rw [lrLowVL7Bernstein_eq_zPowerRows, lrLowVL7ZPowerRows_eq_cols,",
        "    lrLowVL7ZPowerCols_eq_power]",
        "",
        "end CourtadeKumar",
        "",
    ]
    power_target = Path(__file__).resolve().parents[1] / "InformationTheory/CourtadeKumar/LRLowShapeVL7Power.lean"
    power_target.write_text("\n".join(out))


if __name__ == "__main__":
    main()
