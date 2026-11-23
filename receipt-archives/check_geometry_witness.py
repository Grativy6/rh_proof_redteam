"""Reproduce work key 01's arithmetic and its bounded compiled-graph check."""
import argparse
from bisect import bisect_right
from collections import Counter, defaultdict
import gzip
import hashlib
from itertools import permutations, product
import json
from pathlib import Path
import re

from check_sources import git, read_sources, require


RELEASE = "40e56bab026552e089d7afcfeff08d2defb9c005"
RELEASE_TREE = "e517b335d21898fd2506ad538a1e1775c0aaa4e4"
USED_DIGEST = "82c88d25d909a1399c754b87ce298e1939ab0908aeb4766fdac8a57387c71dc5"
FULL_DIGEST = "e36b1a4774c55d042706f5f3bacdefc411d5baa9b7c2d32c51855bcfcfca4c96"
GEO = "Formalism.BasicNotions.DV.Geo"
QUERIES = (
    "riemannHypothesis",
    GEO,
    "Formalism.L2.Geo.geoDegenerate",
    "Formalism.L2.Geo.flagDegZ",
    "Formalism.L2.Geo.AlgPkg",
    "Formalism.L2.Geo.algDegenerate",
    "Formalism.L2.Geo.divXFl",
    "Formalism.L2.Geo.geoFl_inter",
    "Formalism.MainNotions.HeightShare.inter1",
    "GlobalTheory.Mem.Top.Bl.anyGeometry",
    "GlobalTheory.Mem.Top.Bl.geoOf",
    "GlobalTheory.Mem.Top.Bl.OAt",
    "GlobalTheory.Mem.Top.Bl.LamAre",
    "GlobalTheory.Mem.Top.DivRec.x0",
    "GlobalTheory.Mem.Top.DivRec.exists_divT",
    "GlobalTheory.Mem.Top.DivRec.divEx_prov",
    "GlobalTheory.Mem.Top.Closing.divEx_geoCl",
    "GlobalTheory.ShFam.Pad.HasTrueSurf",
    "GlobalTheory.ShFam.Pad.HasTrueSurf.degCh2_eq_zero",
    "Formalism.MainNotions.WeightThresholdDefs.Conclusion4a",
    "Formalism.MainNotions.WeightThresholdDefs.Conclusion4b",
    "GlobalTheory.T.parameter_of_discrete_series_ray",
    "GlobalTheory.T.parameter_of_discrete_series_ray_alt",
    "UpperTheory.Lit.hypsE₂",
    "UpperTheory.Lit.nonempty_hyps_definite_side_of_closed_bound",
)


def flag_degree(weight):
    """Integer coefficient formula for two copies of Fin 2 (total dimension 2).

    The four entries are ordered by (copy, coordinate). Expand the square of
    the negative linear form, then apply the two permutation signs per copy.
    """
    coefficients = Counter()
    for i, j in product(range(4), repeat=2):
        monomial = [0] * 4
        monomial[i] += 1
        monomial[j] += 1
        coefficients[tuple(monomial)] += (-weight[i]) * (-weight[j])
    degree = 0
    for left, right in product(permutations(range(2)), repeat=2):
        target = tuple(1 - idx for idx in left + right)
        left_sign = 1 if left == (0, 1) else -1
        right_sign = 1 if right == (0, 1) else -1
        degree += left_sign * right_sign * coefficients[target]
    return degree


def genuine_mixed(left, right):
    """Bilinear intersection on P¹ × P¹ in its two ruling classes."""
    a, b = left[0] - left[1], left[2] - left[3]
    c, d = right[0] - right[1], right[2] - right[3]
    return a * d + b * c


def arithmetic():
    weights = {"L": (1, 0, 1, 0), "2L": (2, 0, 2, 0), "0": (0, 0, 0, 0)}
    cases = []
    for first, second in [("L", "L"), ("2L", "2L"), ("L", "2L"), ("2L", "L"), ("L", "0"), ("0", "L")]:
        left, right = weights[first], weights[second]
        # geoDegenerate.inter in positive dimension calls flagDegZ on slot 0.
        supplied = flag_degree(left)
        expected = genuine_mixed(left, right)
        combined = tuple(a + b for a, b in zip(left, right))
        require(flag_degree(combined) - flag_degree(left) - flag_degree(right) == 2 * expected,
                "The direct ruling calculation disagrees with polarization")
        cases.append({"inputs": [first, second], "supplied": supplied, "classical": expected})
    require([(r["supplied"], r["classical"]) for r in cases] ==
            [(2, 2), (8, 8), (2, 4), (8, 4), (2, 0), (0, 0)], "Flag-degree controls failed")
    return cases


def graph_rows(path):
    # The publisher encodes one node per line inside a single JSON object.
    with gzip.open(path, "rb") as graph:
        for line in graph:
            if line.startswith(b'{"id":'):
                yield json.loads(line.strip().rstrip(b","))


def check_file(path, expected):
    with path.open("rb") as stream:
        require(hashlib.file_digest(stream, "sha256").hexdigest() == expected,
                f"Unexpected graph digest: {path.name}")


def trace(release, used, full):
    actual_tree = git(release, "rev-parse", RELEASE + "^{tree}").decode().strip()
    require(actual_tree == RELEASE_TREE, "Unexpected release tree")
    check_file(used, USED_DIGEST)
    check_file(full, FULL_DIGEST)

    reachable = {}
    used_count = 0
    for node in graph_rows(used):
        used_count += 1
        if node["name"] in QUERIES:
            reachable[node["name"]] = node
    require(used_count == 806982, "Unexpected reachability graph size")

    # The graph folds projections into their owning structure. Over-include
    # all direct referrers to DV.Geo, then inspect their original source spans.
    geo_id = reachable[GEO]["id"]
    candidates = defaultdict(lambda: defaultdict(list))
    for node in graph_rows(used):
        if geo_id in node["uses_in_body"] or geo_id in node["uses_in_signature"]:
            candidates[node["file"]][node["line"]].append(node["name"])

    full_nodes = {}
    starts = defaultdict(set)
    full_count = 0
    for node in graph_rows(full):
        full_count += 1
        if node["name"] in QUERIES:
            full_nodes[node["name"]] = node
        if node["file"] in candidates:
            starts[node["file"]].add(node["line"])
    require(full_count == 1063440 and set(full_nodes) == set(QUERIES), "Incomplete full graph")

    pins = {"src/" + file for file in candidates}
    pins.update("src/" + node["file"] for node in full_nodes.values())
    sources = read_sources(release, RELEASE, pins)
    membership = []
    for name in QUERIES:
        node = full_nodes[name]
        hit = reachable.get(name)
        if hit is not None:
            require((hit["id_in_full_graph"], hit["file"], hit["line"]) ==
                    (node["id"], node["file"], node["line"]), name)
        membership.append({"name": name, "file": node["file"], "line": node["line"],
                           "distance_from_rh": hit["steps_below_riemannHypothesis"] if hit else None})

    sites = []
    inter = re.compile(r"\binter\b")
    for file in sorted(candidates):
        ordered = sorted(starts[file])
        lines = sources["src/" + file][1].decode("utf-8").splitlines()
        for first, names in sorted(candidates[file].items()):
            next_index = bisect_right(ordered, first)
            stop = ordered[next_index] - 1 if next_index < len(ordered) else len(lines)
            for line_number in range(first, stop + 1):
                line = lines[line_number - 1]
                if inter.search(line):
                    sites.append({"declarations": sorted(names), "file": file, "line": line_number})
    return {"rh_graph_declarations": used_count, "full_graph_declarations": full_count,
            "queried_declarations": membership,
            "direct_referrers_examined": sum(len(names) for f in candidates.values() for names in f.values()),
            "files_with_direct_referrers": len(candidates),
            "explicit_inter_lines": sites}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--graphs", nargs=3, type=Path, metavar=("RELEASE", "RH_GRAPH", "FULL_GRAPH"),
                        help="also check the pinned Git mirror and the two downloaded .json.gz graphs")
    args = parser.parse_args()
    result = {"release": RELEASE, "integer_cases": arithmetic()}
    if args.graphs:
        result["graph_audit"] = trace(*args.graphs)
    print(json.dumps(result, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
