"""Exact arithmetic for Turn 2. Optional graph and compiled-term checks use the original release."""
import argparse
from array import array
from collections import Counter, defaultdict
from fractions import Fraction
from hashlib import sha256
from itertools import chain, combinations, permutations
import json
from math import comb, factorial
from pathlib import Path
import subprocess

from check_geometry_witness import FULL_DIGEST, GEO, RELEASE, USED_DIGEST, check_file, graph_rows
from check_sources import require


INTER = "GlobalTheory.interNum"
WITNESS = "Formalism.L2.Geo.geoDegenerate"
PACKAGE = "Formalism.L2.Geo.AlgPkg"
WEYL = "Formalism.L2.Geo.WeylPolynomialAlgebra.weyl_coeff"
MORSE = "GlobalTheory.MorseNum.morse_A_sq"
GROWTH_BOUND = "GlobalTheory.T.top_intersection_growth_bound"
SHIFT = "RootFieldNumerics.test_polynomial_shift_values"
JPOS = "RootFieldNumerics.TF.jPos"
GROWTH = "GlobalTheory.CompProport.growth_eq_covolume"
SHARE = "Formalism.MainNotions.HeightShare."
CONTROL_MODULE = "Formalism.SharpRestriction.Divisibility.HeightShare"
ROOTS = (WEYL, JPOS, SHIFT, MORSE, GROWTH_BOUND, GROWTH)
OBSERVATIONS = (GEO, PACKAGE, WITNESS, "Formalism.L2.Geo.flagDegZ", INTER,
                "GlobalTheory.topSelfIntersection", "Formalism.DegreeFormula.flagDeg",
                "Formalism.DegreeFormula.degFl", "GlobalTheory.CompHt.growthOn")
CONTROL_NAMES = tuple(SHARE + n for n in ("AsymptoticRiemannRoch", "GloballyGeneratedNef", "AdmG", "inter1"))


def multiply(p, q):
    result = [0] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        for j, b in enumerate(q):
            result[i + j] += a * b
    return result


def flag_integral(weights):
    """Apply the release's alternating coefficient functional to three linear classes."""
    require(len(weights) == 3 and all(len(w) == 3 for w in weights), "Expected three rank-three weights")
    terms = {(0, 0, 0): 1}
    for w in weights:
        updated = Counter()
        for exponents, coefficient in terms.items():
            for i, value in enumerate(w):
                powers = list(exponents)
                powers[i] += 1
                updated[tuple(powers)] -= coefficient * value
        terms = updated
    total = 0
    for perm in permutations(range(3)):
        inversions = sum(perm[i] > perm[j] for i, j in combinations(range(3), 2))
        exponent = tuple(2 - v for v in perm)
        total += (-1) ** inversions * terms.get(exponent, 0)
    return (-1) ** 3 * total


def chi(weight):
    """Euler characteristic of O(a,b) for all integer bidegrees on P¹ × P¹."""
    a, b = weight
    return (a + 1) * (b + 1)


def inter_num(a, b):
    # interNum uses inverse tensor products for the alternating sum over subsets.
    neg_a, neg_b = tuple(-x for x in a), tuple(-x for x in b)
    total = chi((0, 0)) - chi(neg_a) - chi(neg_b) + chi(tuple(x + y for x, y in zip(neg_a, neg_b)))
    require(total == a[0] * b[1] + a[1] * b[0], "Ruling-class intersection differs")
    return total


def surface_trial(q):
    # d=1, A=N=(1,1), b=q, c=1, M=N+cA and L=qN+bA in the release notation.
    a, m, line = (1, 1), (2, 2), (2 * q, 2 * q)
    gate = 4 * inter_num(a, m)
    wrong_gate = 4 * inter_num(a, a)
    mixed = inter_num((2, 2), line)
    self_intersection = inter_num(line, line)
    require(mixed == 2 * inter_num(a, line), "Doubling the first line bundle failed")
    return {"q": q, "true_gate_lhs": gate, "first_slot_gate_lhs": wrong_gate,
            "true_gate_passes": gate < q, "first_slot_gate_passes": wrong_gate < q,
            "conclusion_lhs": 2 * mixed, "conclusion_rhs": self_intersection,
            "conclusion_holds": 2 * mixed < self_intersection}


def arithmetic():
    mu, nu = (0, -1, -1), (2, 1, 0)
    coeffs = [comb(3, i) * flag_integral([mu] * (3 - i) + [nu] * i) for i in range(4)]
    # Independent evaluation of the rank-three Weyl product as an exact polynomial.
    weyl = [Fraction(factorial(3))]
    for i, j in combinations(range(3), 2):
        weyl = multiply(weyl, [Fraction(mu[i] - mu[j], j - i), Fraction(nu[i] - nu[j], j - i)])
    require(coeffs == weyl == [0, 3, 9, 6], "Coefficient and Weyl calculations disagree")
    mixed = flag_integral([mu, mu, nu])
    require(mixed == flag_integral([nu, mu, mu]) == 1, "Mixed degree changed with order")
    trials = [surface_trial(q) for q in (9, 16, 17)]
    require([x["true_gate_passes"] for x in trials] == [False, False, True], "Unexpected strict cutoff")
    require(trials[-1]["conclusion_lhs"] == 272 and trials[-1]["conclusion_rhs"] == 2312,
            "Unexpected admissible inequality")
    # A finite illustration of the universal counterexample proved in FlagGrowth.lean.
    constant, power = 10, 13
    degree = inter_num((1, 1), (1, 1))
    model_sections = 1
    discrepancy = abs(model_sections - degree * power ** 2 // factorial(2))
    require(discrepancy > constant * power, "Section growth illustration failed")
    return {"growth_example": {"C": constant, "power": power, "model_sections": model_sections,
                               "classical_sections": (power + 1) ** 2, "absolute_error": discrepancy,
                               "allowed_error": constant * power},
            "weyl": {"mu": mu, "nu": nu, "coefficients_constant_first": coeffs,
                     "mixed_degree": mixed, "first_slot_mu_first": flag_integral([mu] * 3),
                     "first_slot_nu_first": flag_integral([nu] * 3)}, "surface": trials}


def upward_closure(root, parents):
    reached = {root}
    todo = [root]
    while todo:
        for parent in parents[todo.pop()]:
            if parent not in reached:
                reached.add(parent)
                todo.append(parent)
    return reached


def graph_check(used, full):
    check_file(used, USED_DIGEST)
    check_file(full, FULL_DIGEST)
    requested = set(ROOTS + OBSERVATIONS + CONTROL_NAMES)
    live = {}
    offsets = array("I", [0])
    edges = array("I")
    parents = [[] for _ in range(806982)]
    for node in graph_rows(used):
        require(node["id"] + 1 == len(offsets), "Unexpected node order")
        if node["name"] in requested:
            live[node["name"]] = node
        children = set(chain(node["uses_in_body"], node["uses_in_signature"]))
        for child in children:
            parents[child].append(node["id"])
        edges.extend(children)
        offsets.append(len(edges))
    require(len(offsets) == 806983 and set(ROOTS + OBSERVATIONS) <= live.keys(), "Incomplete RH graph")
    full_records = {node["name"]: node for node in graph_rows(full) if node["name"] in requested}
    require(set(full_records) == requested, "A requested declaration is missing from the full graph")
    for name, node in live.items():
        ref = full_records[name]
        require((ref["id"], ref["file"], ref["line"]) ==
                (node["id_in_full_graph"], node["file"], node["line"]), name)
    require(not (set(CONTROL_NAMES) & live.keys()), "A control is on the RH path in this snapshot")

    closures = {}
    for name in ROOTS:
        todo = [live[name]["id"]]
        reached = set(todo)
        while todo:
            n = todo.pop()
            for child in edges[offsets[n]:offsets[n + 1]]:
                if child not in reached:
                    reached.add(child)
                    todo.append(child)
        closures[name] = {"size_including_root": len(reached),
                          "observed": [x for x in OBSERVATIONS if live[x]["id"] in reached]}

    witness_users = upward_closure(live[WITNESS]["id"], parents)
    joints = {}
    needed_ids = set()
    for name in (JPOS, GROWTH_BOUND, GROWTH):
        estimate_users = upward_closure(live[name]["id"], parents)
        both = witness_users & estimate_users
        first = []
        for node in sorted(both):
            children = set(edges[offsets[node]:offsets[node + 1]])
            if children.isdisjoint(both):
                via_witness = sorted(children & witness_users)
                via_estimate = sorted(children & estimate_users)
                first.append((node, via_witness, via_estimate))
                needed_ids.update([node, *via_witness, *via_estimate])
        joints[name] = (len(both), first)

    owners = {live[GEO]["id"], live[PACKAGE]["id"]}
    labels = {}
    modules = set()
    for node in graph_rows(used):
        if node["id"] in needed_ids:
            labels[node["id"]] = node["name"]
        if owners.intersection(node["uses_in_body"]) or owners.intersection(node["uses_in_signature"]):
            modules.add(node["file"].removesuffix(".lean").replace("/", "."))
    depths = {n: live[n]["steps_below_riemannHypothesis"] if n in live else None for n in sorted(requested)}
    meetings = {
        name: {"shared_users": count, "first_shared_users": [
            {"declaration": labels[n], "witness_dependencies": sorted(labels[w] for w in left),
             "estimate_dependencies": sorted(labels[w] for w in right)}
            for n, left, right in first]}
        for name, (count, first) in joints.items()}
    return {"depths": depths, "dependency_closures": closures,
            "first_shared_users_with_geoDegenerate": meetings,
            "rh_referrer_modules": sorted(modules), "off_path_control_module": CONTROL_MODULE}


def term_check(lean, root, graph):
    version = subprocess.check_output([str(lean), "--version"], text=True).strip()
    require("version 4.33.1," in version, "Use the release's matching Lean 4.33.1 reader")
    modules = sorted(set(graph["rh_referrer_modules"]) | {CONTROL_MODULE})
    script = Path(__file__).with_name("InspectIntersection.lean").resolve()
    cmd = [str(lean), "--run", str(script), str(root.resolve()), *modules]
    run = subprocess.run(cmd, capture_output=True, check=True)
    rows = [json.loads(line) for line in run.stdout.splitlines() if line]
    counts = {r["scanned"]: r["declarations"] for r in rows if "scanned" in r}
    require(set(counts) == set(modules), "Missing module scan")
    shapes = defaultdict(set)
    for row in rows:
        for hit in row.get("hits", ()):
            if hit["field"] == GEO + ".inter":
                shapes[hit["form"]].add(row["decl"])
            if hit["field"] == GEO + ".H0" and hit["form"] == "under-rank":
                shapes["section_space_under_rank"].add(row["decl"])
    require(SHARE + "inter1" in shapes["slot-dependent-lambda"], "Mixed positive control was missed")
    require(SHARE + "AsymptoticRiemannRoch" in shapes["section_space_under_rank"], "Rank control was missed")
    objects = {}
    for module in modules:
        path = root.joinpath(*module.split(".")).with_suffix(".olean")
        with path.open("rb") as f:
            digest = sha256()
            while chunk := f.read(1024 * 1024):
                digest.update(chunk)
        objects[module] = digest.hexdigest()
    return {"native_reader_version": version, "module_count": len(modules),
            "declarations_in_modules": sum(counts.values()), "modules_sha256": objects,
            "calibrations": [r for r in rows if "calibration" in r],
            "field_results_by_distinct_raw_declaration": {k: sorted(v) for k, v in sorted(shapes.items())}}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--graphs", nargs=2, type=Path, metavar=("RH_GRAPH", "FULL_GRAPH"))
    parser.add_argument("--oleans", type=Path, help="module root of a built original release")
    parser.add_argument("--lean", type=Path, default=Path("lean"), help="matching Lean 4.33.1 executable")
    args = parser.parse_args()
    if args.oleans and not args.graphs:
        parser.error("--oleans uses the module selection from --graphs")
    result = {"release": RELEASE, "arithmetic": arithmetic()}
    if args.graphs:
        result["graph"] = graph_check(*args.graphs)
    if args.oleans:
        result["compiled"] = term_check(args.lean, args.oleans, result["graph"])
    print(json.dumps(result, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
