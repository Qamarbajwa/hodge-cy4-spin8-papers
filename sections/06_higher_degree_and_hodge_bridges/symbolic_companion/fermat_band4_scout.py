"""Phase 1 (Wall 2) Exact Integer Fermat Fourfold Band-4 Census & Sporadic Scout.

Strictly float-free. Mirrors the Lean 4 definitions in
`ShiodaFormalConjectures.lean`, `ShiodaInductiveCycleSynthesis.lean`, and
`HigherDegreeSporadicBand4.lean` to survey m >= 19, group Band 4 representatives
into (Z/mZ)^x Galois orbits, test glued surface-to-surface joins
(X_m^2 #_c X_m^2), proper-divisor pullbacks, half/third vanishing sums, and
isolate any strictly indecomposable sporadic orbits.
"""

from __future__ import annotations

import json
import math
import sys
import time
from math import factorial
from pathlib import Path
from typing import Any, Dict, List, Tuple

sys.path.insert(0, str(Path(__file__).resolve().parent))
from gpu_exact_linalg import gpu_filter_hodge22_batch  # noqa: E402


def coprime_units(m: int) -> List[int]:
    return [t for t in range(1, m) if math.gcd(t, m) == 1]


def s6_orbit_size(a: Tuple[int, ...]) -> int:
    counts: Dict[int, int] = {}
    for x in a:
        counts[x] = counts.get(x, 0) + 1
    denom = 1
    for c in counts.values():
        denom *= factorial(c)
    return 720 // denom


_PAIRINGS_6 = [
    ((0, 1), (2, 3), (4, 5)), ((0, 1), (2, 4), (3, 5)), ((0, 1), (2, 5), (3, 4)),
    ((0, 2), (1, 3), (4, 5)), ((0, 2), (1, 4), (3, 5)), ((0, 2), (1, 5), (3, 4)),
    ((0, 3), (1, 2), (4, 5)), ((0, 3), (1, 4), (2, 5)), ((0, 3), (1, 5), (2, 4)),
    ((0, 4), (1, 2), (3, 5)), ((0, 4), (1, 3), (2, 5)), ((0, 4), (1, 5), (2, 3)),
    ((0, 5), (1, 2), (3, 4)), ((0, 5), (1, 3), (2, 4)), ((0, 5), (1, 4), (2, 3)),
]

_TRIPLE_SPLITS = [
    ((0, 1, 2), (3, 4, 5)), ((0, 1, 3), (2, 4, 5)), ((0, 1, 4), (2, 3, 5)),
    ((0, 1, 5), (2, 3, 4)), ((0, 2, 3), (1, 4, 5)), ((0, 2, 4), (1, 3, 5)),
    ((0, 2, 5), (1, 3, 4)), ((0, 3, 4), (1, 2, 5)), ((0, 3, 5), (1, 2, 4)),
    ((0, 4, 5), (1, 2, 3)),
]

_ALL_PAIRS = [(i, j) for i in range(6) for j in range(i + 1, 6)]


def is_band1(m: int, a: Tuple[int, ...]) -> bool:
    for (i1, j1), (i2, j2), (i3, j3) in _PAIRINGS_6:
        if a[i1] + a[j1] == m and a[i2] + a[j2] == m and a[i3] + a[j3] == m:
            return True
    return False


def is_band2(m: int, a: Tuple[int, ...]) -> bool:
    if is_band1(m, a):
        return False
    m2 = 2 * m
    for t1, t2 in _TRIPLE_SPLITS:
        s1 = a[t1[0]] + a[t1[1]] + a[t1[2]]
        s2 = a[t2[0]] + a[t2[1]] + a[t2[2]]
        if (s1 == m and s2 == m2) or (s1 == m2 and s2 == m):
            return True
    return False


def is_band3(m: int, a: Tuple[int, ...]) -> bool:
    if is_band1(m, a) or is_band2(m, a):
        return False
    for i, j in _ALL_PAIRS:
        if a[i] + a[j] == m:
            return True
    return False


def is_paired_diagonal(a: Tuple[int, ...]) -> bool:
    return a[0] == a[1] and a[2] == a[3] and a[4] == a[5]


def is_surface_hodge11(m: int, s: Tuple[int, int, int, int], units: List[int]) -> bool:
    target = 2 * m
    for t in units:
        if ((t * s[0]) % m + (t * s[1]) % m + (t * s[2]) % m + (t * s[3]) % m) != target:
            return False
    return True


def glued_surface_join_witness(m: int, a: Tuple[int, ...], units: List[int]) -> Dict[str, Any] | None:
    """Finds first (t1, t2, c) satisfying isShiodaSurfaceHodge11 on t1+[c] and t2+[m-c]."""
    for idx1, idx2 in _TRIPLE_SPLITS:
        t1 = (a[idx1[0]], a[idx1[1]], a[idx1[2]])
        t2 = (a[idx2[0]], a[idx2[1]], a[idx2[2]])
        for c in range(1, m):
            if is_surface_hodge11(m, (*t1, c), units) and is_surface_hodge11(m, (*t2, m - c), units):
                return {"t1": list(t1), "t2": list(t2), "c": c}
    return None


def sorted_hodge22_tuples(m: int) -> List[Tuple[int, ...]]:
    units = coprime_units(m)
    m3 = 3 * m
    out: List[Tuple[int, ...]] = []
    # Fast check: check t in units \ {1}, and precompute residues per unit if needed
    other_units = [t for t in units if t != 1]
    for a0 in range(1, m // 2 + 1):
        for a1 in range(a0, m):
            if a0 + 5 * a1 > m3:
                break
            for a2 in range(a1, m):
                if a0 + a1 + 4 * a2 > m3:
                    break
                for a3 in range(a2, m):
                    if a0 + a1 + a2 + 3 * a3 > m3:
                        break
                    for a4 in range(a3, m):
                        s = a0 + a1 + a2 + a3 + a4
                        if s + a4 > m3:
                            break
                        a5 = m3 - s
                        if a5 >= m:
                            continue
                        ok = True
                        for t in other_units:
                            if ((t * a0) % m + (t * a1) % m + (t * a2) % m +
                                    (t * a3) % m + (t * a4) % m + (t * a5) % m) != m3:
                                ok = False
                                break
                        if ok:
                            out.append((a0, a1, a2, a3, a4, a5))
    return out


def has_prime_ap_vanish(m: int, a: Tuple[int, ...]) -> int:
    """Returns smallest prime p | m such that `a` contains a full p-term AP mod m of step m/p, else 0."""
    mm = m
    d = 2
    primes: List[int] = []
    while d * d <= mm:
        if mm % d == 0:
            primes.append(d)
            while mm % d == 0:
                mm //= d
        d += 1
    if mm > 1:
        primes.append(mm)
    aset = set(a)
    for p in primes:
        step = m // p
        for x in a:
            if all(((x + k * step) % m) in aset for k in range(p)):
                return p
    return 0


def mixed_surface_join_witness(
    m: int, a: Tuple[int, ...], units: List[int]
) -> Dict[str, Any] | None:
    """Finds (t1, t2, c) decomposing `a` on X_m^2 #_c X_m^2 across mixed Hodge types (1,3),(2,2),(3,1)."""
    import itertools

    for idxs1 in itertools.combinations(range(6), 3):
        idxs2 = tuple(i for i in range(6) if i not in idxs1)
        t1 = [a[i] for i in idxs1]
        t2 = [a[i] for i in idxs2]
        for c in range(1, m):
            ok = True
            hodge_types = set()
            for u in units:
                s1 = sum((u * x) % m for x in t1) + (u * c) % m
                s2 = sum((u * x) % m for x in t2) + (u * (m - c)) % m
                if not (s1 % m == 0 and s2 % m == 0 and s1 in (m, 2 * m, 3 * m) and s1 + s2 == 4 * m):
                    ok = False
                    break
                hodge_types.add((s1 // m, s2 // m))
            if ok:
                return {"t1": t1, "t2": t2, "c": c, "hodge_types": sorted(hodge_types)}
    return None


def analyze_degree(m: int) -> Dict[str, Any]:
    t0 = time.time()
    units = coprime_units(m)
    reps = sorted_hodge22_tuples(m)
    gpu_matched, gpu_stats = gpu_filter_hodge22_batch(reps, units, m, target_weight=3)
    if len(gpu_matched) != len(reps):
        raise RuntimeError(f"GPU Galois batch filter mismatch at m={m}: {len(gpu_matched)} vs {len(reps)}")
    h22 = b1 = b2 = b3 = b4 = 0
    band4_reps: List[Tuple[int, ...]] = []
    for r in reps:
        w = s6_orbit_size(r)
        h22 += w
        if is_band1(m, r):
            b1 += w
        elif is_band2(m, r):
            b2 += w
        elif is_band3(m, r):
            b3 += w
        else:
            b4 += w
            band4_reps.append(r)

    paired_weight = 0
    glued_weight = 0
    prime_ap_weight = 0
    mixed_surf_weight = 0
    strict_sporadic: List[Dict[str, Any]] = []
    truly_open: List[Dict[str, Any]] = []
    glued_examples: List[Dict[str, Any]] = []
    paired_reps: List[List[int]] = []

    seen_galois = set()
    galois_orbits: List[Dict[str, Any]] = []
    for r in band4_reps:
        w = s6_orbit_size(r)
        is_pd = is_paired_diagonal(r)
        glued = None if is_pd else glued_surface_join_witness(m, r, units)
        all_div = math.gcd(*r, m) > 1
        any_div = any(math.gcd(x, m) > 1 for x in r)
        half_diff = (m % 2 == 0) and any((x + m // 2) in r for x in r)
        if is_pd:
            paired_weight += w
            paired_reps.append(list(r))
        elif glued is not None:
            glued_weight += w
            if len(glued_examples) < 5:
                glued_examples.append({"rep": list(r), "weight": w, "witness": glued})
        else:
            p_ap = has_prime_ap_vanish(m, r)
            mixed = None if p_ap > 0 else mixed_surface_join_witness(m, r, units)
            strict_sporadic.append({
                "rep": list(r),
                "weight": w,
                "common_gcd_gt1": all_div,
                "any_gcd_gt1": any_div,
                "half_diff": half_diff,
                "prime_ap": p_ap,
                "mixed_surface_join": mixed,
            })
            if p_ap > 0:
                prime_ap_weight += w
            elif mixed is not None:
                mixed_surf_weight += w
            else:
                truly_open.append({"rep": list(r), "weight": w})

        if r not in seen_galois:
            orbit = sorted({tuple(sorted((t * x) % m for x in r)) for t in units})
            for o in orbit:
                seen_galois.add(o)
            galois_orbits.append({
                "canonical": list(r),
                "galois_size": len(orbit),
                "total_weight": sum(s6_orbit_size(o) for o in orbit),
                "paired": is_pd,
                "glued_surface_join": glued is not None,
            })

    return {
        "m": m,
        "elapsed_sec": round(time.time() - t0, 3),
        "gpu_galois_filter": gpu_stats,
        "h22_prim": h22,
        "band1": b1,
        "band2": b2,
        "band3": b3,
        "band4": b4,
        "band4_sorted_rep_count": len(band4_reps),
        "band4_galois_orbit_count": len(galois_orbits),
        "band4_paired_weight": paired_weight,
        "band4_glued_surface_join_weight": glued_weight,
        "band4_non_glued_non_paired_count": len(strict_sporadic),
        "band4_non_glued_non_paired_weight": sum(x["weight"] for x in strict_sporadic),
        "band4_prime_ap_weight": prime_ap_weight,
        "band4_mixed_surface_join_weight": mixed_surf_weight,
        "band4_unexplained_count": len(truly_open),
        "band4_unexplained_weight": sum(x["weight"] for x in truly_open),
        "strict_sporadic_sample": strict_sporadic[:15],
        "glued_examples": glued_examples,
        "galois_orbits_summary": galois_orbits[:10],
    }


def main() -> int:
    out_dir = Path(__file__).resolve().parents[2] / "reports" / "millennium_ext"
    out_dir.mkdir(parents=True, exist_ok=True)
    degrees_30 = [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 30]
    report_30 = [analyze_degree(m) for m in degrees_30]
    (out_dir / "fermat_band4_m18_to_m30.json").write_text(
        json.dumps(report_30, indent=2), encoding="utf-8"
    )

    degrees_60 = list(range(18, 61))
    report_60 = [analyze_degree(m) for m in degrees_60]
    (out_dir / "fermat_band4_m18_to_m60.json").write_text(
        json.dumps(report_60, indent=2), encoding="utf-8"
    )
    for r in report_60:
        if r["band4_non_glued_non_paired_count"] > 0 or r["m"] in (18, 19, 20, 21, 22, 23, 24, 30):
            print(
                f"m={r['m']}: h22={r['h22_prim']} b4={r['band4']} "
                f"non_glued={r['band4_non_glued_non_paired_count']} "
                f"prime_ap_w={r['band4_prime_ap_weight']} "
                f"mixed_surf_w={r['band4_mixed_surface_join_weight']} "
                f"unexplained={r['band4_unexplained_count']} ({r['elapsed_sec']}s)"
            )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
