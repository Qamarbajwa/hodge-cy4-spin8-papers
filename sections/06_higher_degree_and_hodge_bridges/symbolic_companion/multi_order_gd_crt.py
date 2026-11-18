"""Phase 2 (Wall 1): Multi-Order Griffiths-Dwork Jet Transport (mod t^k, k <= 8)
and Rational Reconstruction via 3-Prime CRT.

Strictly float-free. Generalizes `GaussManinJetTransport.lean` and
`blind_gauss_manin_jet_reconstructor.py` to arbitrary jet order k >= 4 over F_p
using three 62-bit primes, exact Wang rational reconstruction, and Macaulay
annihilator rank stabilization checks across Bands 1, 2, and 3.
"""

from __future__ import annotations

import json
import math
import sys
from fractions import Fraction
from pathlib import Path
from typing import Dict, List, Tuple

sys.path.insert(0, str(Path(__file__).resolve().parent))
from gpu_exact_linalg import gpu_crt_3prime_rank  # noqa: E402


PRIMES_62 = (
    4611686018427387847,  # 2^62 - 57
    4611686018427387817,  # 2^62 - 87
    4611686018427387787,  # 2^62 - 117
)

Monom6 = Tuple[int, int, int, int, int, int]
PolyMod = Dict[Monom6, int]


def poly_mul_mod(a: PolyMod, b: PolyMod, p: int) -> PolyMod:
    out: PolyMod = {}
    for m1, c1 in a.items():
        for m2, c2 in b.items():
            m = tuple(m1[i] + m2[i] for i in range(6))  # type: ignore[assignment]
            val = (out.get(m, 0) + c1 * c2) % p
            if val:
                out[m] = val
            else:
                out.pop(m, None)
    return out


def poly_add_mod(a: PolyMod, b: PolyMod, p: int) -> PolyMod:
    out = dict(a)
    for m, c in b.items():
        val = (out.get(m, 0) + c) % p
        if val:
            out[m] = val
        else:
            out.pop(m, None)
    return out


def gd_reduce_18_to_12_mod(
    m: Monom6, c: int, p: int, strict_pole_lowering: bool = True
) -> PolyMod:
    for i in range(6):
        if m[i] >= 5:
            if m[i] == 5:
                return {}
            factor = (m[i] - 5) % p
            coeff = (c * factor) % p
            if coeff == 0:
                return {}
            nm = list(m)
            nm[i] -= 6
            out_m = tuple(nm)  # type: ignore[assignment]
            if any(e >= 5 for e in out_m):
                return {}
            return {out_m: coeff}
    if strict_pole_lowering or any(e >= 5 for e in m):
        return {}
    return {m: c % p} if (c % p) else {}


def gauss_manin_step_mod(
    w_dir: PolyMod, prev_lam: PolyMod, p: int, strict_pole_lowering: bool = True
) -> PolyMod:
    prod = poly_mul_mod(w_dir, prev_lam, p)
    acc: PolyMod = {}
    for m, c in prod.items():
        acc = poly_add_mod(
            acc, gd_reduce_18_to_12_mod(m, c, p, strict_pole_lowering=strict_pole_lowering), p
        )
    return acc


def monomials6(deg: int) -> List[Monom6]:
    res: List[Monom6] = []
    for a0 in range(min(4, deg) + 1):
        for a1 in range(min(4, deg - a0) + 1):
            for a2 in range(min(4, deg - a0 - a1) + 1):
                for a3 in range(min(4, deg - a0 - a1 - a2) + 1):
                    for a4 in range(min(4, deg - a0 - a1 - a2 - a3) + 1):
                        a5 = deg - (a0 + a1 + a2 + a3 + a4)
                        if 0 <= a5 <= 4:
                            res.append((a0, a1, a2, a3, a4, a5))
    return res


def rref_rank_mod(rows: List[List[int]], p: int) -> int:
    if not rows:
        return 0
    mat = [r[:] for r in rows]
    n_rows = len(mat)
    n_cols = len(mat[0])
    r = 0
    for c in range(n_cols):
        piv = -1
        for i in range(r, n_rows):
            if mat[i][c] % p != 0:
                piv = i
                break
        if piv < 0:
            continue
        mat[r], mat[piv] = mat[piv], mat[r]
        inv = pow(mat[r][c], p - 2, p)
        mat[r] = [(x * inv) % p for x in mat[r]]
        for i in range(n_rows):
            if i != r and mat[i][c] % p != 0:
                fac = mat[i][c]
                mat[i] = [(mat[i][j] - fac * mat[r][j]) % p for j in range(n_cols)]
        r += 1
        if r == n_rows:
            break
    return r


def joint_jet_ranks_mod(jet: List[PolyMod], p: int, max_d: int = 6) -> List[int]:
    ranks: List[int] = []
    for d in range(max_d + 1):
        basis = monomials6(d)
        cols_map: Dict[Tuple[int, Monom6], int] = {}
        sparse_rows: List[Dict[int, int]] = []
        for m in basis:
            row_d: Dict[int, int] = {}
            for k, lam in enumerate(jet):
                for lm, lc in lam.items():
                    pm = tuple(m[i] + lm[i] for i in range(6))  # type: ignore[assignment]
                    if all(e <= 4 for e in pm):
                        key = (k, pm)
                        col_idx = cols_map.setdefault(key, len(cols_map))
                        row_d[col_idx] = (row_d.get(col_idx, 0) + lc) % p
            if row_d:
                sparse_rows.append(row_d)
        n_cols = len(cols_map)
        if not sparse_rows or n_cols == 0:
            ranks.append(0)
        else:
            dense = [[rd.get(j, 0) for j in range(n_cols)] for rd in sparse_rows]
            ranks.append(rref_rank_mod(dense, p))
    return ranks


def crt_lift_and_wang(residues: List[int], primes: Tuple[int, ...]) -> Fraction:
    big_p = 1
    for p in primes:
        big_p *= p
    acc = 0
    for a, p in zip(residues, primes):
        mi = big_p // p
        inv = pow(mi % p, p - 2, p)
        acc = (acc + a * mi * inv) % big_p
    bound = math.isqrt(big_p // 2)
    r0, r1 = big_p, acc
    t0, t1 = 0, 1
    while r1 >= bound:
        q = r0 // r1
        r0, r1 = r1, r0 - q * r1
        t0, t1 = t1, t0 - q * t1
    if t1 < 0:
        r1, t1 = -r1, -t1
    return Fraction(r1, t1)


def run_multi_order_jet_audit(max_order: int = 7) -> Dict[str, object]:
    cases = {
        "band1_quadric": (
            {(4, 0, 4, 0, 4, 0): 1},
            {(2, 4, 0, 0, 0, 0): 1, (3, 3, 0, 0, 0, 0): 1, (4, 2, 0, 0, 0, 0): 1},
        ),
        "band2_curve_join": (
            {(2, 2, 2, 2, 2, 2): 1},
            {(4, 1, 0, 1, 0, 0): 1, (0, 0, 1, 4, 1, 0): 1, (0, 1, 0, 0, 1, 4): 1},
        ),
        "band3_surface_curve": (
            {(4, 2, 2, 2, 1, 1): 1},
            {(0, 4, 0, 0, 1, 1): 1, (0, 0, 4, 0, 1, 1): 1, (0, 0, 0, 4, 1, 1): 1},
        ),
    }

    summary: Dict[str, object] = {}
    for name, (lam0_raw, w_raw) in cases.items():
        prime_results = []
        shadow_results = []
        for p in PRIMES_62:
            lam0 = {m: c % p for m, c in lam0_raw.items()}
            wdir = {m: c % p for m, c in w_raw.items()}
            jet_strict = [lam0]
            jet_shadow = [lam0]
            for _ in range(max_order):
                jet_strict.append(
                    gauss_manin_step_mod(wdir, jet_strict[-1], p, strict_pole_lowering=True)
                )
                jet_shadow.append(
                    gauss_manin_step_mod(wdir, jet_shadow[-1], p, strict_pole_lowering=False)
                )
            ranks_strict = {
                f"t^{k}": joint_jet_ranks_mod(jet_strict[: k + 1], p, 6)
                for k in range(max_order + 1)
            }
            ranks_shadow = {
                f"t^{k}": joint_jet_ranks_mod(jet_shadow[: k + 1], p, 6)
                for k in range(max_order + 1)
            }
            prime_results.append(
                {"p": p, "terms": [len(j) for j in jet_strict], "ranks": ranks_strict}
            )
            shadow_results.append(
                {"p": p, "terms": [len(j) for j in jet_shadow], "ranks": ranks_shadow}
            )

        consistent = (
            prime_results[0]["ranks"] == prime_results[1]["ranks"] == prime_results[2]["ranks"]
        )
        conventions_rank_match = prime_results[0]["ranks"] == shadow_results[0]["ranks"]
        if not conventions_rank_match:
            raise RuntimeError(f"Rank mismatch between strict and unreduced conventions for {name}")
        lam_top_crt: Dict[str, str] = {}
        jets_p = []
        for p in PRIMES_62:
            j = [{m: c % p for m, c in lam0_raw.items()}]
            wdir = {m: c % p for m, c in w_raw.items()}
            for _ in range(max_order):
                j.append(gauss_manin_step_mod(wdir, j[-1], p, strict_pole_lowering=True))
            jets_p.append(j[-1])
        all_keys = sorted(set(jets_p[0]) | set(jets_p[1]) | set(jets_p[2]))
        for key in all_keys[:6]:
            frac = crt_lift_and_wang([jp.get(key, 0) for jp in jets_p], PRIMES_62)
            lam_top_crt[str(list(key))] = str(frac)

        # Run RTX A2000 3-prime int64 CUDA CRT verification on top-order d=6 jet matrix
        top_basis = monomials6(6)
        t_cols_map: Dict[Tuple[int, Monom6], int] = {}
        t_sparse: List[Dict[int, int]] = []
        j_int = [{m: c for m, c in lam0_raw.items()}]
        w_int = {m: c for m, c in w_raw.items()}
        for _ in range(max_order):
            # Build exact integer step via mod 0 reduction formula
            prod_int: Dict[Monom6, int] = {}
            for m1, c1 in w_int.items():
                for m2, c2 in j_int[-1].items():
                    pm = tuple(m1[i] + m2[i] for i in range(6))  # type: ignore[assignment]
                    prod_int[pm] = prod_int.get(pm, 0) + c1 * c2
            nxt: Dict[Monom6, int] = {}
            for pm, pc in prod_int.items():
                for i in range(6):
                    if pm[i] >= 5:
                        if pm[i] > 5:
                            nm = list(pm)
                            nm[i] -= 6
                            out_m = tuple(nm)  # type: ignore[assignment]
                            if all(e <= 4 for e in out_m):
                                nxt[out_m] = nxt.get(out_m, 0) + pc * (pm[i] - 5)
                        break
            j_int.append({k: v for k, v in nxt.items() if v != 0})
        for m in top_basis:
            rd: Dict[int, int] = {}
            for k_idx, lam in enumerate(j_int):
                for lm, lc in lam.items():
                    pm = tuple(m[i] + lm[i] for i in range(6))  # type: ignore[assignment]
                    if all(e <= 4 for e in pm):
                        cidx = t_cols_map.setdefault((k_idx, pm), len(t_cols_map))
                        rd[cidx] = rd.get(cidx, 0) + lc
            if rd:
                t_sparse.append(rd)
        n_tcols = len(t_cols_map)
        dense_int = [[rd.get(j, 0) for j in range(n_tcols)] for rd in t_sparse]
        gpu_d6 = gpu_crt_3prime_rank(dense_int)

        summary[name] = {
            "max_order": max_order,
            "crt_3prime_rank_agreement": consistent,
            "conventions_rank_match": conventions_rank_match,
            "strict_term_counts_by_order": prime_results[0]["terms"],
            "unreduced_shadow_term_counts_by_order": shadow_results[0]["terms"],
            "term_counts_by_order": prime_results[0]["terms"],
            "joint_ranks_by_order": prime_results[0]["ranks"],
            "top_order_crt_sample": lam_top_crt,
            "gpu_t7_d6_crt_verification": gpu_d6,
        }
    return summary


def main() -> int:
    res = run_multi_order_jet_audit(max_order=7)
    out_dir = Path(__file__).resolve().parents[2] / "reports" / "millennium_ext"
    out_dir.mkdir(parents=True, exist_ok=True)
    out_path = out_dir / "multi_order_gd_crt_t8.json"
    out_path.write_text(json.dumps(res, indent=2), encoding="utf-8")
    for name, info in res.items():
        print(
            f"{name}: crt_agree={info['crt_3prime_rank_agreement']} "
            f"terms={info['term_counts_by_order']} "
            f"r(t^0)={info['joint_ranks_by_order']['t^0']} "
            f"r(t^7)={info['joint_ranks_by_order']['t^7']}"
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
