"""Exact finite checks for the coefficient-descent and period calculations."""

import argparse
from itertools import product
from math import isqrt
from pathlib import Path


def require(condition, message):
    if not condition:
        raise ValueError(message)


def norm_k(x, y):
    """Norm of x + y (1 + sqrt(-23))/2 in the quadratic field."""
    return x * x + x * y + 6 * y * y


def finite_checks():
    # Coprime quadratic discriminants give the integral basis (1, w, u, wu),
    # with w^2 = w - 6 and u^2 = u - 1. The two quotient maps send u to 2.
    residues = list(product(range(3), repeat=4))
    kernels = []
    for root in (0, 1):
        kernel = {
            (a, b, c, d) for a, b, c, d in residues
            if (a + b * root + 2 * c + 2 * d * root) % 3 == 0
        }
        kernels.append(kernel)

    # Multiply (a + bw) + (c + dw)u by 2u - 1 = sqrt(-3).
    image = {
        ((-a - 2 * c) % 3, (-b - 2 * d) % 3,
         (2 * a + c) % 3, (2 * b + d) % 3)
        for a, b, c, d in residues
    }
    require(kernels[0] != kernels[1], "The two primes must be distinct")
    require(image == kernels[0] & kernels[1], "Wrong product ideal modulo 3")
    # All three ideals contain 3 O_E since (sqrt(-3))^2 = -3.
    require(len(image) == 9 and all(len(k) == 27 for k in kernels),
            "The required additive index is three in either prime")

    # 4 N(x+yw) = (2x+y)^2 + 23 y^2. Norm three forces y=0.
    require(23 > 4 * 3 and isqrt(3) ** 2 != 3, "Norm-three obstruction failed")
    require(norm_k(1, 2) == 3 ** 3, "Wrong norm of 2 + sqrt(-23)")
    require([(1 + 2 * r) % 3 for r in (0, 1)] == [1, 0],
            "The cube must be supported at precisely the second prime")
    require(25 ** 2 - 69 * 3 ** 2 == 4, "The proposed real unit has wrong norm")
    d = 983
    require(d % 24 == 23 and all(d % j for j in range(2, isqrt(d) + 1)),
            "The fixed-degree control needs a prime in the stated progression")
    require(4 * 3 ** 5 < d + 1, "Degree five should fail the necessary inequality")

    print("The two prime ideals each have 27 residues. Their product has 9.")
    print("The index of (sqrt(-3)) in either line is 3. Its log correction is log(3)/2.")
    print("The norm-27 element singles out one prime. The real unit has norm 1.")
    print("At d = 983 the norm bound rules out degrees 1 through 5.")


def graph_check(path):
    from check_geometry_witness import USED_DIGEST, check_file, graph_rows

    check_file(path, USED_DIGEST)
    kernel = "Formalism.L2.Ker."
    jets = "GlobalTheory.Mem.Col2."
    step = jets + "JetEx.finAlg_step"
    field = jets + "JetFin.finAlg_jetSet"
    original = jets + "JetEx.jetSet"
    algebraic = "GlobalTheory.T.vacuum_entire_and_normalizedJets_algebraic"
    roots = "GlobalTheory.T.exists_finite_extension_capitulation_complex"
    edges = {
        kernel + "Amb.jetK": (kernel + "desc", kernel + "jetC"),
        original: (kernel + "jetC",),
        step: (original, field, algebraic),
        "GlobalTheory.Mem.Top.ReW.jetsIn_of_isTw": (step, original),
        jets + "AmbEx.exists_dgen": (roots,),
    }
    names = set(edges).union(*edges.values(), {
        "GlobalTheory.ColRows.fieldOfDefinition_of_stdKer",
        "GlobalTheory.KerT.RatLaw.jetMap_congr",
        "GlobalTheory.MeanPeriodGenerator.mean_logMet_eq",
        "GlobalTheory.KernelHalfS.kerSide_chainS",
        "GlobalTheory.CompProport.growth_eq_top_self_intersection",
    })
    nodes = {row["name"]: row for row in graph_rows(path) if row["name"] in names}
    require(set(nodes) == names, "A declaration is missing from the RH graph")
    for caller, targets in edges.items():
        for target in targets:
            require(nodes[target]["id"] in nodes[caller]["uses_in_body"],
                    f"Missing body dependency: {caller} -> {target}")
    require(nodes[kernel + "desc"]["id"] not in nodes[original]["uses_in_body"],
            "Recheck whether the jet set uses descended coefficients")
    for name in sorted(nodes):
        row = nodes[name]
        print(f"{row['steps_below_riemannHypothesis']:2} edges below RH  {name}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--graph", type=Path, help="published gzipped RH-reachable graph")
    args = parser.parse_args()
    finite_checks()
    if args.graph:
        graph_check(args.graph)
