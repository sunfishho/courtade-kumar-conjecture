#!/usr/bin/env python3
"""Generate an exact rectangle certificate for the V-star envelope."""

from pathlib import Path
import sys

import sympy as sp

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
import verify_lr_x85_UV_certificate as verifier  # noqa: E402

from generate_lr_lowshape_v_g_certificate import (  # noqa: E402
    add_tree,
    bernstein_to_power,
    lean_rat,
    tensor_rows,
)


def main():
    verifier.install_bounds()
    base = verifier.base
    v, z = verifier.v, verifier.z
    q = v**2 * base.x
    expression = sp.factor(sp.together(
        base.G_lower
        - 2 * (1 - q) * (base.beta_upper + base.L_upper) / (v * (1 + v))
    ))
    positive_base = (
        (1 + v) ** 9 * (2 + v) ** 9
        * (20 - 17 * z) * (20 - 17 * v**2 * z)
    )
    numerator = base.positive_numerator(expression, positive_base)
    denominator = sp.fraction(sp.factor(sp.together(expression)))[1]
    quotient = sp.factor(denominator / positive_base)
    assert quotient == 6450271027200000000000000

    rows = tensor_rows(numerator)
    assert len(rows) == 45 and all(len(row) == 16 for row in rows)
    assert all(value > 0 for row in rows for value in row)

    data = [
        "import InformationTheory.CourtadeKumar.LRLowShapeVEndpointCertificate",
        "",
        "/-! Generated exact tensor-Bernstein data for the V-star envelope. -/",
        "",
        "open Set",
        "namespace CourtadeKumar",
        "",
    ]
    for i, row in enumerate(rows):
        terms = [
            f"{lean_rat(value)} * bernsteinBasis 15 {j} z"
            for j, value in enumerate(row)
        ]
        data += [
            f"noncomputable def lrLowVEBernsteinRow{i} (z : ℝ) : ℝ :=",
            f"  {add_tree(terms)}",
            "",
            f"lemma lrLowVEBernsteinRow{i}_nonneg",
            "    {z : ℝ} (hz : z ∈ Icc (0 : ℝ) 1) :",
            f"    0 ≤ lrLowVEBernsteinRow{i} z := by",
            f"  unfold lrLowVEBernsteinRow{i}",
            "  repeat' apply add_nonneg",
            "  all_goals exact mul_nonneg (by norm_num) (bernsteinBasis_nonneg hz)",
            "",
        ]
    outer = [
        f"lrLowVEBernsteinRow{i} z * bernsteinBasis 44 {i} v"
        for i in range(45)
    ]
    data += [
        "noncomputable def lrLowVEBernstein (v z : ℝ) : ℝ :=",
        f"  {add_tree(outer)}",
        "",
        "lemma lrLowVEBernstein_nonneg",
        "    {v z : ℝ} (hv : v ∈ Icc (0 : ℝ) 1) (hz : z ∈ Icc (0 : ℝ) 1) :",
        "    0 ≤ lrLowVEBernstein v z := by",
        "  unfold lrLowVEBernstein",
        "  repeat' apply add_nonneg",
    ]
    data += [
        f"  · exact mul_nonneg (lrLowVEBernsteinRow{i}_nonneg hz) "
        f"(bernsteinBasis_nonneg hv)"
        for i in range(45)
    ]
    data += ["", "end CourtadeKumar", ""]
    data_target = Path(__file__).resolve().parents[1] / (
        "InformationTheory/CourtadeKumar/LRLowShapeVStarCertificateData.lean"
    )
    data_target.write_text("\n".join(data))

    power_rows = [bernstein_to_power(row) for row in rows]
    poly = sp.Poly(sp.expand(numerator), v, z)
    monomials = poly.as_dict()
    power = [
        "import InformationTheory.CourtadeKumar.LRLowShapeVStarCertificateData",
        "",
        "/-! Separable exact reconstruction of the V-star envelope certificate. -/",
        "",
        "namespace CourtadeKumar",
        "",
    ]
    for i, row in enumerate(power_rows):
        terms = [f"{lean_rat(value)} * z ^ {j}" for j, value in enumerate(row) if value]
        power += [
            f"noncomputable def lrLowVEZPowerEvalRow{i} (z : ℝ) : ℝ :=",
            f"  {add_tree(terms)}",
            "",
            "set_option maxHeartbeats 2000000 in",
            f"lemma lrLowVEBernsteinRow{i}_eq_power (z : ℝ) :",
            f"    lrLowVEBernsteinRow{i} z = lrLowVEZPowerEvalRow{i} z := by",
            f"  unfold lrLowVEBernsteinRow{i} lrLowVEZPowerEvalRow{i} bernsteinBasis",
            "  norm_num [Nat.choose]",
            "  ring",
            "",
        ]
    row_terms = [
        f"lrLowVEZPowerEvalRow{i} z * bernsteinBasis 44 {i} v"
        for i in range(45)
    ]
    power += [
        "noncomputable def lrLowVEZPowerRowsEval (v z : ℝ) : ℝ :=",
        f"  {add_tree(row_terms)}",
        "",
        "lemma lrLowVEBernstein_eq_zPowerRows (v z : ℝ) :",
        "    lrLowVEBernstein v z = lrLowVEZPowerRowsEval v z := by",
        "  unfold lrLowVEBernstein lrLowVEZPowerRowsEval",
    ]
    for start in range(0, 45, 8):
        names = ", ".join(
            f"lrLowVEBernsteinRow{i}_eq_power"
            for i in range(start, min(start + 8, 45))
        )
        power.append(f"  rw [{names}]")

    for j in range(16):
        z_terms = [
            f"{lean_rat(power_rows[i][j])} * bernsteinBasis 44 {i} v"
            for i in range(45) if power_rows[i][j]
        ]
        v_terms = [
            f"{lean_rat(monomials.get((i, j), 0))} * v ^ {i}"
            for i in range(45) if monomials.get((i, j), 0)
        ]
        power += [
            "",
            f"noncomputable def lrLowVEZPowerEvalCol{j} (v : ℝ) : ℝ :=",
            f"  {add_tree(z_terms)}",
            "",
            f"noncomputable def lrLowVEVPowerEvalCol{j} (v : ℝ) : ℝ :=",
            f"  {add_tree(v_terms)}",
        ]
    z_cols = [f"lrLowVEZPowerEvalCol{j} v * z ^ {j}" for j in range(16)]
    v_cols = [f"lrLowVEVPowerEvalCol{j} v * z ^ {j}" for j in range(16)]
    power += [
        "",
        "noncomputable def lrLowVEZPowerColsEval (v z : ℝ) : ℝ :=",
        f"  {add_tree(z_cols)}",
        "",
        "noncomputable def lrLowVEPowerEval (v z : ℝ) : ℝ :=",
        f"  {add_tree(v_cols)}",
        "",
        "set_option maxHeartbeats 8000000 in",
        "lemma lrLowVEZPowerRows_eq_cols (v z : ℝ) :",
        "    lrLowVEZPowerRowsEval v z = lrLowVEZPowerColsEval v z := by",
        "  unfold lrLowVEZPowerRowsEval lrLowVEZPowerColsEval",
    ]
    power += [f"  unfold lrLowVEZPowerEvalRow{i}" for i in range(45)]
    power += [f"  unfold lrLowVEZPowerEvalCol{j}" for j in range(16)]
    power.append("  ring")
    for j in range(16):
        power += [
            "",
            "set_option maxHeartbeats 8000000 in",
            f"lemma lrLowVEZPowerEvalCol{j}_eq_power (v : ℝ) :",
            f"    lrLowVEZPowerEvalCol{j} v = lrLowVEVPowerEvalCol{j} v := by",
            f"  unfold lrLowVEZPowerEvalCol{j} lrLowVEVPowerEvalCol{j} bernsteinBasis",
            "  norm_num [Nat.choose]",
            "  ring",
        ]
    power += [
        "",
        "lemma lrLowVEZPowerCols_eq_power (v z : ℝ) :",
        "    lrLowVEZPowerColsEval v z = lrLowVEPowerEval v z := by",
        "  unfold lrLowVEZPowerColsEval lrLowVEPowerEval",
    ]
    for start in range(0, 16, 8):
        names = ", ".join(
            f"lrLowVEZPowerEvalCol{j}_eq_power"
            for j in range(start, min(start + 8, 16))
        )
        power.append(f"  rw [{names}]")
    power += [
        "",
        "theorem lrLowVEBernstein_eq_power (v z : ℝ) :",
        "    lrLowVEBernstein v z = lrLowVEPowerEval v z := by",
        "  rw [lrLowVEBernstein_eq_zPowerRows, lrLowVEZPowerRows_eq_cols,",
        "    lrLowVEZPowerCols_eq_power]",
        "",
        "end CourtadeKumar",
        "",
    ]
    power_target = Path(__file__).resolve().parents[1] / (
        "InformationTheory/CourtadeKumar/LRLowShapeVStarPower.lean"
    )
    power_target.write_text("\n".join(power))


if __name__ == "__main__":
    main()
