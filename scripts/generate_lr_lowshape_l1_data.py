#!/usr/bin/env python3
"""Reconstruct the exact low-shape ``L1`` Bernstein certificate.

This is a small standard-library-only replay of the corresponding SymPy
verifier in the audited proof package.  Polynomials are sparse dictionaries
with ``Fraction`` coefficients; no floating-point arithmetic is used.
"""

from __future__ import annotations

from fractions import Fraction as F
from math import comb, gcd
from functools import reduce
import argparse


class Poly:
    def __init__(self, terms=None):
        self.terms = {k: F(v) for k, v in (terms or {}).items() if v}

    @staticmethod
    def constant(q):
        return Poly({(0, 0): F(q)})

    def __add__(self, other):
        other = as_poly(other)
        out = dict(self.terms)
        for key, value in other.terms.items():
            out[key] = out.get(key, F(0)) + value
            if not out[key]:
                del out[key]
        return Poly(out)

    __radd__ = __add__

    def __neg__(self):
        return Poly({key: -value for key, value in self.terms.items()})

    def __sub__(self, other):
        return self + (-as_poly(other))

    def __rsub__(self, other):
        return as_poly(other) - self

    def __mul__(self, other):
        other = as_poly(other)
        out = {}
        for (i, j), a in self.terms.items():
            for (k, ell), b in other.terms.items():
                key = (i + k, j + ell)
                out[key] = out.get(key, F(0)) + a * b
        return Poly(out)

    __rmul__ = __mul__

    def __pow__(self, exponent):
        result = Poly.constant(1)
        base = self
        n = exponent
        while n:
            if n & 1:
                result = result * base
            base = base * base
            n //= 2
        return result

    def coefficient(self, i, j):
        return self.terms.get((i, j), F(0))

    @property
    def degree(self):
        return (
            max(i for i, _ in self.terms),
            max(j for _, j in self.terms),
        )


def as_poly(value):
    return value if isinstance(value, Poly) else Poly.constant(value)


v = Poly({(1, 0): F(1)})
z = Poly({(0, 1): F(1)})
one = Poly.constant(1)
X = F(17, 20)


def a(n):
    return F(1, 2 * n * (2 * n - 1))


def reconstruct_l1_numerator():
    vp2 = v + 2
    vp1 = v + 1

    # beta_- = beta_num / (2+v)^9.
    beta_num = sum(
        F(2, 2 * k + 1) * v ** (2 * k + 1) * vp2 ** (8 - 2 * k)
        for k in range(5)
    )
    assert all(i >= 1 for i, _ in beta_num.terms)
    beta_num_div_v = Poly({(i - 1, j): q for (i, j), q in beta_num.terms.items()})

    # zeta_- = minus_log_num / (1+v)^9.
    minus_log_num = sum(
        F(2, 2 * k + 1) * (one - v) ** (2 * k + 1) * vp1 ** (8 - 2 * k)
        for k in range(5)
    )

    # beta_+ = beta_upper_num / ((1+v)(2+v)^9).
    beta_upper_num = beta_num * vp1 + F(1, 22) * v ** 11

    x = X * z
    p1_lower = sum(
        a(m) * x**m * (one + v ** (2 * m - 1))
        for m in range(2, 13)
    )
    base = vp1**9 * vp2**9
    b1_upper = F(693148, 10**6) - F(1, 2)

    # Each line is the corresponding term of L1 multiplied by `base`.
    numerator = (
        beta_num_div_v * vp1**10
        + minus_log_num * vp2**9
        - a(1) * x * (one + v) * base
        - b1_upper * (4 + 2 * v) * vp1**8 * vp2**9
        + 2 * beta_num * p1_lower * vp1**9
        - 4 * b1_upper * v * x * beta_upper_num * vp1**7
    )
    return numerator


def low_shape_components():
    """Exact polynomial pieces shared by the five W-head certificates."""
    vp2 = v + 2
    vp1 = v + 1
    beta_num = sum(
        F(2, 2 * k + 1) * v ** (2 * k + 1) * vp2 ** (8 - 2 * k)
        for k in range(5)
    )
    beta_num_div_v = Poly(
        {(i - 1, j): q for (i, j), q in beta_num.terms.items()}
    )
    minus_log_num = sum(
        F(2, 2 * k + 1) * (one - v) ** (2 * k + 1) * vp1 ** (8 - 2 * k)
        for k in range(5)
    )
    beta_upper_num = beta_num * vp1 + F(1, 22) * v ** 11
    radial = vp1**9 * vp2**9
    g_radial_num = beta_num_div_v * vp1**10 + minus_log_num * vp2**9
    x = X * z
    xi = v**2 * x
    denominator_xi = 20 - 17 * v**2 * z
    l_lower = sum(xi**r * F(1, 2 * r) for r in range(1, 13))
    a_lower_radial_num = beta_num * vp1**9 + l_lower * radial
    return {
        "vp1": vp1,
        "vp2": vp2,
        "beta_upper_num": beta_upper_num,
        "radial": radial,
        "g_radial_num": g_radial_num,
        "x": x,
        "xi": xi,
        "denominator_xi": denominator_xi,
        "l_lower": l_lower,
        "a_lower_radial_num": a_lower_radial_num,
    }


def reconstruct_w_numerator(n):
    """Numerator of W_n over the verifier's positive common base."""
    assert 1 <= n <= 5
    c = low_shape_components()
    vp1 = c["vp1"]
    vp2 = c["vp2"]
    radial = c["radial"]
    x = c["x"]
    xi = c["xi"]
    denominator_xi = c["denominator_xi"]
    l_lower = c["l_lower"]

    b_upper = F(693148, 10**6) - sum(a(m) for m in range(1, n + 1))
    prefix = sum(
        a(m) * x**m * (one + v ** (2 * m - 1))
        for m in range(1, n + 1)
    )
    p_lower = sum(
        a(m) * x**m * (one + v ** (2 * m - 1))
        for m in range(n + 1, 13)
    )
    h_head = sum(xi**j for j in range(1, n + 1))

    brace_radial_num = (
        c["g_radial_num"]
        - prefix * radial
        - b_upper * (4 + 2 * v) * vp1**8 * vp2**9
    )
    positive_num = 2 * n * c["a_lower_radial_num"] * p_lower

    # Expand A_+ * d directly against radial*(20-17*v^2*z).
    beta_d_num = (
        2 * v * x * c["beta_upper_num"] * vp1**7 * denominator_xi
    )
    l_head_d_num = 2 * v * x * l_lower * vp1**8 * vp2**9 * denominator_xi
    # xi^13/(26(1-xi)) = (10/13)*xi^13/(20-17*v^2*z).
    l_tail_d_num = F(20, 13) * v * x * xi**13 * vp1**8 * vp2**9
    negative_num = 2 * n * b_upper * (
        beta_d_num + l_head_d_num + l_tail_d_num
    )

    return (
        h_head * brace_radial_num * denominator_xi
        + positive_num * denominator_xi
        - negative_num
    )


def tensor_bernstein(poly):
    degree_v, degree_z = poly.degree
    rows = []
    for i in range(degree_v + 1):
        row = []
        for j in range(degree_z + 1):
            value = F(0)
            for r in range(i + 1):
                for s in range(j + 1):
                    value += (
                        poly.coefficient(r, s)
                        * F(comb(i, r), comb(degree_v, r))
                        * F(comb(j, s), comb(degree_z, s))
                    )
            row.append(value)
        rows.append(row)
    return rows


def lcm(a, b):
    return abs(a * b) // gcd(a, b)


def primitive_integer_scale(values):
    denominator = reduce(lcm, (q.denominator for q in values), 1)
    integers = [q.numerator * (denominator // q.denominator) for q in values]
    divisor = reduce(gcd, (abs(n) for n in integers if n), 0)
    return F(denominator, divisor)


def endpoint_quotient(poly):
    """Return Q with P(v,1)B(1)-P(1,1)B(v)=(1-v)Q(v)."""
    power = {}
    for (i, _j), value in poly.terms.items():
        power[i] = power.get(i, F(0)) + value
    base = (one + v) ** 9 * (2 + v) ** 9
    base_power = {i: value for (i, _j), value in base.terms.items()}
    p_one = sum(power.values())
    base_one = sum(base_power.values())
    degree = max(max(power), max(base_power))
    difference = [
        power.get(i, F(0)) * base_one - p_one * base_power.get(i, F(0))
        for i in range(degree + 1)
    ]
    quotient = []
    previous = F(0)
    for coefficient in difference[:-1]:
        previous += coefficient
        quotient.append(previous)
    assert difference[-1] + previous == 0
    while quotient and quotient[-1] == 0:
        quotient.pop()
    return quotient


def univariate_bernstein(power):
    degree = len(power) - 1
    return [
        sum(
            power[r] * F(comb(i, r), comb(degree, r))
            for r in range(i + 1)
        )
        for i in range(degree + 1)
    ]


def lean_rat(q):
    if q.denominator == 1:
        return str(q.numerator)
    return f"({q.numerator}/{q.denominator})"


def balanced_sum(terms):
    if not terms:
        return "0"
    current = terms
    while len(current) > 1:
        current = [
            f"({current[i]} + {current[i + 1]})"
            if i + 1 < len(current) else current[i]
            for i in range(0, len(current), 2)
        ]
    return current[0]


def emit_w_rows_patch(n, start, stop, target):
    rows = tensor_bernstein(reconstruct_w_numerator(n))
    definitions = []
    for i in range(start, stop):
        terms = [
            f"{lean_rat(q)} * bernsteinBasis 25 {j} z"
            for j, q in enumerate(rows[i]) if q
        ]
        value = balanced_sum(terms)
        if terms:
            proof = f"""by
  unfold lrLowW{n}BernsteinRow{i}
  repeat' apply add_nonneg
  all_goals exact mul_nonneg (by norm_num) (bernsteinBasis_nonneg hz)"""
        else:
            proof = f"by simp [lrLowW{n}BernsteinRow{i}]"
        definitions.append(
            f"noncomputable def lrLowW{n}BernsteinRow{i} (z : ℝ) : ℝ :=\n"
            f"  {value}\n\n"
            f"lemma lrLowW{n}BernsteinRow{i}_nonneg\n"
            f"    {{z : ℝ}} (hz : z ∈ Icc (0 : ℝ) 1) :\n"
            f"    0 ≤ lrLowW{n}BernsteinRow{i} z := {proof}"
        )
    payload = "\n\n".join(definitions)
    print("*** Begin Patch")
    print(f"*** Update File: {target}")
    print("@@")
    print("--- ROW_DEFINITIONS_END")
    for line in payload.splitlines():
        print("+" + line)
    print("+")
    print("+-- ROW_DEFINITIONS_END")
    print("*** End Patch")


def emit_w_total_patch(n, target):
    terms = [
        f"lrLowW{n}BernsteinRow{i} z * bernsteinBasis 67 {i} v"
        for i in range(68)
    ]
    value = balanced_sum(terms)
    nonneg = "\n".join(
        f"  have h{i} : 0 ≤ lrLowW{n}BernsteinRow{i} z * "
        f"bernsteinBasis 67 {i} v := "
        f"mul_nonneg (lrLowW{n}BernsteinRow{i}_nonneg hz) "
        f"(bernsteinBasis_nonneg hv)"
        for i in range(68)
    )
    all_names = ", ".join(f"h{i}" for i in range(68))
    payload = f"""noncomputable def lrLowW{n}Bernstein (v z : ℝ) : ℝ :=
  {value}

lemma lrLowW{n}Bernstein_nonneg
    {{v z : ℝ}} (hv : v ∈ Icc (0 : ℝ) 1) (hz : z ∈ Icc (0 : ℝ) 1) :
    0 ≤ lrLowW{n}Bernstein v z := by
{nonneg}
  unfold lrLowW{n}Bernstein
  positivity [{all_names}]"""
    print("*** Begin Patch")
    print(f"*** Update File: {target}")
    print("@@")
    print("--- TOTAL_DEFINITION_END")
    for line in payload.splitlines():
        print("+" + line)
    print("+")
    print("+-- TOTAL_DEFINITION_END")
    print("*** End Patch")


def emit_endpoint_lean(poly):
    quotient = endpoint_quotient(poly)
    bernstein = univariate_bernstein(quotient)
    assert len(bernstein) == 41
    assert all(q > 0 for q in bernstein)
    for i, q in enumerate(bernstein):
        suffix = " +" if i + 1 < len(bernstein) else ""
        print(f"  {lean_rat(q)} * bernsteinBasis 40 {i} v{suffix}")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--emit-endpoint-lean", action="store_true")
    parser.add_argument("--w-head", type=int, choices=range(1, 6))
    parser.add_argument("--emit-w-rows", nargs=3, metavar=("N", "START", "STOP"))
    parser.add_argument("--emit-w-total", type=int, choices=range(1, 6))
    parser.add_argument("--target")
    args = parser.parse_args()
    if args.emit_w_rows is not None:
        if args.target is None:
            parser.error("--emit-w-rows requires --target")
        n, start, stop = map(int, args.emit_w_rows)
        emit_w_rows_patch(n, start, stop, args.target)
        return
    if args.emit_w_total is not None:
        if args.target is None:
            parser.error("--emit-w-total requires --target")
        emit_w_total_patch(args.emit_w_total, args.target)
        return
    poly = reconstruct_l1_numerator()
    assert poly.degree == (41, 12)
    assert len(poly.terms) == 371
    rows = tensor_bernstein(poly)
    flat = [q for row in rows for q in row]
    assert len(flat) == 42 * 13
    assert all(q > 0 for q in flat)

    scale = primitive_integer_scale([*poly.terms.values()])
    primitive = [q * scale for q in flat]
    minimum_raw = min(flat)
    minimum_index = next(
        (i, j) for i, row in enumerate(rows) for j, q in enumerate(row)
        if q == minimum_raw
    )
    expected = F(17565518749422468464640000000)
    assert min(primitive) == expected

    print("degree", poly.degree)
    print("monomials", len(poly.terms))
    print("coefficients", len(flat))
    print("zeros", sum(q == 0 for q in flat))
    print("primitive scale", scale)
    print("smallest raw coefficient", minimum_raw)
    print("smallest coefficient index", minimum_index)
    print("scale matching audited numerator", expected / minimum_raw)
    if args.emit_endpoint_lean:
        emit_endpoint_lean(poly)
    if args.w_head is not None:
        w_poly = reconstruct_w_numerator(args.w_head)
        rows = tensor_bernstein(w_poly)
        flat = [q for row in rows for q in row]
        print(f"W{args.w_head} degree", w_poly.degree)
        print(f"W{args.w_head} monomials", len(w_poly.terms))
        print(f"W{args.w_head} coefficients", len(flat))
        print(f"W{args.w_head} zeros", sum(q == 0 for q in flat))
        print(f"W{args.w_head} negatives", sum(q < 0 for q in flat))
        positive = [(q, i, j) for i, row in enumerate(rows)
                    for j, q in enumerate(row) if q > 0]
        print(f"W{args.w_head} minimum raw", min(positive))


if __name__ == "__main__":
    main()
