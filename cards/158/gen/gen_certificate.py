"""Exact Q(sqrt3, sqrt11) certificate for Lemma (Seven-point certificate),
family 158, "The Euclidean plane is not five-colorable", angular.tex.

For each Moser vertex g, the placed point z_g = (35+12i)/37 * (g + (-290+149i)/250)
must satisfy 0 < l < 4 and P < P', where l = xi^2 + ups^2,
P = ups^2 (3 xi^2 - ups^2)^2 and P' = l^3 (1 - l/4) (l - 1)^2.

We write every quantity in the basis {1, s, t, s*t} with s = sqrt 3, t = sqrt 11
and emit the exact rational coefficients. HOL then checks each normal form by
REAL_RING and each sign by linear arithmetic from rational bounds on
sqrt 3, sqrt 11 and sqrt 33.
"""
import json
import os
import sys

import sympy as sp

s, t = sp.symbols("s t", positive=True)
I = sp.I

A = (s + I) / 2
B = (s - I) / 2
T = s
u = (5 + I * t) / 6
G = {"O": sp.Integer(0), "A": A, "B": B, "T": T, "UA": u * A, "UB": u * B, "UT": u * T}
EDGES = [("O", "A"), ("O", "B"), ("A", "B"), ("T", "A"), ("T", "B"),
         ("O", "UA"), ("O", "UB"), ("UA", "UB"), ("UT", "UA"), ("UT", "UB"),
         ("T", "UT")]

ROT = sp.Rational(35, 37) + I * sp.Rational(12, 37)
SHIFT = sp.Rational(int(os.environ.get("SHIFT_X", "-290")), 250) + I * sp.Rational(149, 250)


def reduce_st(expr):
    """Reduce a polynomial in s, t modulo s^2 = 3, t^2 = 11 to a + b s + c t + d s t."""
    p = sp.Poly(sp.expand(expr), s, t)
    out = {(0, 0): 0, (1, 0): 0, (0, 1): 0, (1, 1): 0}
    for (i, j), c in p.terms():
        coeff = c * sp.Integer(3) ** (i // 2) * sp.Integer(11) ** (j // 2)
        out[(i % 2, j % 2)] += coeff
    coeffs = [sp.Rational(out[k]) for k in ((0, 0), (1, 0), (0, 1), (1, 1))]
    assert all(c.is_Rational for c in coeffs), coeffs
    return coeffs


def coords(z):
    z = sp.expand(z)
    return sp.expand(sp.re(z)), sp.expand(sp.im(z))


def main():
    out = {"points": {}, "edges": {}}
    placed = {}
    for name, g in G.items():
        x, y = coords(ROT * (g + SHIFT))
        placed[name] = (x, y)
        l = x ** 2 + y ** 2
        P = y ** 2 * (3 * x ** 2 - y ** 2) ** 2
        Pp = l ** 3 * (1 - l / 4) * (l - 1) ** 2
        rec = {
            "xi": [str(c) for c in reduce_st(x)],
            "ups": [str(c) for c in reduce_st(y)],
            "l": [str(c) for c in reduce_st(l)],
            "gap": [str(c) for c in reduce_st(Pp - P)],
        }
        num = {k: float(sp.N(sum(sp.Rational(c) * m for c, m in zip(rec[k], [1, sp.sqrt(3), sp.sqrt(11), sp.sqrt(33)])), 30))
               for k in ("xi", "ups", "l", "gap")}
        rec["numeric"] = num
        out["points"][name] = rec
    for a, b in EDGES:
        (xa, ya), (xb, yb) = placed[a], placed[b]
        d2 = reduce_st((xa - xb) ** 2 + (ya - yb) ** 2)
        out["edges"][f"{a}-{b}"] = [str(c) for c in d2]
    json.dump(out, sys.stdout, indent=1)


if __name__ == "__main__":
    main()
