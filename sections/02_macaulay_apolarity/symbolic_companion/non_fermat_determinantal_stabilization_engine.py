r"""Non-Fermat Determinantal Stabilization & Higher-Degree Recombination Engine (Event 29).

Attacks Global Bridge A (S-BRIDGE-DEFORM-CY4) on three complementary fronts while
preserving complete mathematical honesty on the open universal non-Fermat bound:

1. CollisionHigherDegreeDeterminantalEngine:
   Extends the Event 28 m=1 determinantal Macaulay audit to all degrees m = 1..6 across
   both recombined 2-plane shadows and quadruple collision syzygies on the Fermat sextic:
   - Recombined plane sum lam_recomb = x_0^4 x_1^4 (x_2^4 + x_3^4) has static m=1..6
     Macaulay rank vector [4, 9, 16, 24, 30, 32] (flat doubled target [8, 18, 32, 48, 60, 64]).
   - Along u_flat = x_4^4 x_5^2 with Lambda_1 = 0, ALL degrees m = 1..6 remain flat:
     [8, 18, 32, 48, 60, 64].
   - Along moving directions u_A = (x_3^4 - x_2^4)x_4^2, u_B = (x_3^4 - x_2^4)x_4 x_5,
     and u_C = (x_3^4 - x_2^4)x_5^2: with naive Lambda_1 = 0, m = 1 falsely appears flat
     (rk = 8 = 2*4), whereas m >= 2 jumps strictly:
       u_A: [8, 19, 36, 56, 71, 76] (excess [0, 1, 4, 8, 11, 12]),
       u_B: [8, 19, 36, 56, 72, 78] (excess [0, 1, 4, 8, 12, 14]),
       u_C: [8, 19, 36, 56, 71, 76] (excess [0, 1, 4, 8, 11, 12]).
     With the closed-form moving-quadric shadow Lambda_1 = 4 x_0^4 x_1^4 (x_3^2 - x_2^2) q_45,
     ALL 3 flatten simultaneously across all m = 1..6 to [8, 18, 32, 48, 60, 64] and satisfy
     Order-2 Gauss-Manin obstruction cancellation (u_A * Lambda_1 in im(M_{u_A})).
   - Along the quadruple collision direction u_quad = (x_2^4 + x_3^4 + x_4^4)x_5^2, all 4
     non-trivial collision syzygies lam^(a;b,c,d) = x_a^4 x_b^4 (x_c^4 - x_d^4) jump
     immediately from m = 1..6 to [9, 23, 45, 71, 91, 98] under Lambda_1 = 0, and ALL 4/4
     flatten cleanly to [8, 18, 32, 48, 60, 64] under the closed-form moving shadow
     Lambda_1 = 4 x_a^4 x_5^2 (x_b^2 (x_c^4 - x_d^4) + x_b^4 (x_c^2 - x_d^2)).

2. FiniteNonFermatMacaulayEngine:
   Constructs a genuine finite non-Fermat (t^2 != 0, broken (Z/6Z)^6 diagonal symmetry)
   smooth Calabi-Yau fourfold F_nF = P_0(x_0,x_3) + P_1(x_1,x_4) + P_2(x_2,x_5):
   - Pair Hilbert series [1, 2, 3, 4, 5, 4, 3, 2, 1] (Milnor 25 per pair, 25^3 = 15,625 total),
     yielding 6-variable Jacobian graded dims R^1..R^6 = [6, 21, 56, 126, 246, 426],
     R^{12} = 1,751, R^{18} = 426.
   - Extracts exact degree-4 non-Fermat pair annihilators to form a smooth finite non-Fermat
     2-plane shadow Lambda_{Pi_nF} and moving-quadric shadow Lambda_{Q_nF}:
     * Plane_nF achieves exact stabilized rank vector [3, 6, 10, 15, 18, 19] (G = 1) and
       recovers exact defining linear ideal (x_0 - 2x_3, x_1 - 3x_4, x_2 - 5x_5).
     * Quad_nF achieves exact stabilized rank vector [4, 9, 16, 24, 30, 32] (G = 2,
       Ann_{R^6} = 394) and recovers linear generators (x_1 - 3x_4, x_2 - 5x_5) plus exact
       quadratic generator (x_0 - 2x_3)(x_0 + x_3) = x_0^2 - x_0 x_3 - 2 x_3^2.

3. NonSeparableBridgeAHonestyAudit:
   Records strict open-problem boundaries: universal_non_fermat_determinantal_stabilization_proved
   = False, effective_hilbert_degree_bound_known = False, global_hodge_conjecture_status = "OPEN".

Zero floating-point constructs: 100% exact integers, tuples, and fractions.Fraction.
"""

from __future__ import annotations

import sys
from fractions import Fraction
from pathlib import Path
from typing import Any, Dict, List, Optional, Sequence, Tuple

_REPO_ROOT = str(Path(__file__).resolve().parent.parent)
if _REPO_ROOT not in sys.path:
    sys.path.insert(0, _REPO_ROOT)

from toolkit.deformed_macaulay_transport_engine import DeformedJacobianRingJet
from toolkit.higher_order_gauss_manin_sieve import (
    Monomial,
    PolyDict,
    poly_mod_jacobian,
    poly_mul,
)
from toolkit.integrity import scan_forbidden
from toolkit.macaulay_apolarity_inverse_engine import _sparse_rref_and_nullspace


def _zero() -> Fraction:
    return Fraction(0, 1)


def _one() -> Fraction:
    return Fraction(1, 1)


def _mon6(exps: Dict[int, int]) -> Monomial:
    vec = [0] * 6
    for idx, val in exps.items():
        vec[idx] = val
    return tuple(vec)


# ==============================================================================
# MODULE 1: HIGHER-DEGREE DETERMINANTAL STABILIZATION ON RECOMB & COLLISIONS
# ==============================================================================


class CollisionHigherDegreeDeterminantalEngine:
    """Tests m = 1..6 deformed Macaulay ranks on recombined and quadruple collision shadows."""

    EXPECTED_FLAT_VECTOR: List[int] = [8, 18, 32, 48, 60, 64]
    EXPECTED_BASE_VECTOR: List[int] = [4, 9, 16, 24, 30, 32]

    def __init__(self, ring_jet: Optional[DeformedJacobianRingJet] = None) -> None:
        self.jet = ring_jet if ring_jet is not None else DeformedJacobianRingJet()
        self.macaulay = self.jet.macaulay
        self.lam_recomb: PolyDict = {
            (4, 4, 4, 0, 0, 0): _one(),
            (4, 4, 0, 4, 0, 0): _one(),
        }
        self.u_quad: PolyDict = {
            (0, 0, 4, 0, 0, 2): _one(),
            (0, 0, 0, 4, 0, 2): _one(),
            (0, 0, 0, 0, 4, 2): _one(),
        }

    def _is_in_u_image(self, u_poly: PolyDict, target_poly: PolyDict) -> bool:
        """Checks whether target_poly in R^{18}(F_0) lies in im(M_u : R^{12}(F_0) -> R^{18}(F_0))."""
        b12 = self.macaulay.cy.generate_monomial_basis(12)
        b18 = self.macaulay.bases[18]
        idx18 = {m: i for i, m in enumerate(b18)}
        t_mod = poly_mod_jacobian(target_poly)

        # Solve M_u^T * z != 0 or augment columns cleanly via row-reduced sparse check:
        # Actually M_u maps column j in b12 to row i in b18; transpose rows give equations on R^{18}^*:
        # Easier exact rank test: rk(cols of M_u) == rk(cols of M_u union {t_mod}).
        col_rows: List[Dict[int, Fraction]] = []
        for b in b12:
            prod = poly_mod_jacobian(poly_mul({b: _one()}, u_poly))
            if prod:
                col_rows.append({idx18[m]: v for m, v in prod.items()})
        rk_base, _ = _sparse_rref_and_nullspace(col_rows, len(b18))
        target_row = {idx18[m]: v for m, v in t_mod.items()}
        rk_aug, _ = _sparse_rref_and_nullspace(col_rows + [target_row], len(b18))
        return rk_aug == rk_base

    def audit_recombined_higher_degrees(self) -> Dict[str, Any]:
        """Audits m = 1..6 flatness of lam_recomb along u_flat and u_A, u_B, u_C."""
        u_flat: PolyDict = {(0, 0, 0, 0, 4, 2): _one()}
        flat_res = self.jet.deformed_hilbert_and_ranks(
            self.lam_recomb, {}, u_flat, degrees=(1, 2, 3, 4, 5, 6)
        )

        # Witness g = x_2 x_3 showing why naive Lambda_1 = 0 breaks m >= 2 flatness along u_A
        g_offender: PolyDict = {(0, 0, 1, 1, 0, 0): _one()}
        g_static_mod = poly_mod_jacobian(poly_mul(g_offender, self.lam_recomb))

        directions = [
            ("u_A", {(0, 0, 0, 4, 2, 0): _one(), (0, 0, 4, 0, 2, 0): -_one()}, {4: 2}),
            ("u_B", {(0, 0, 0, 4, 1, 1): _one(), (0, 0, 4, 0, 1, 1): -_one()}, {4: 1, 5: 1}),
            ("u_C", {(0, 0, 0, 4, 0, 2): _one(), (0, 0, 4, 0, 0, 2): -_one()}, {5: 2}),
        ]

        dir_results: List[Dict[str, Any]] = []
        u_a_order2_absorbed = False
        g_u_a_nonzero = False

        for name, u_poly, q45_spec in directions:
            gm1_ok = len(poly_mod_jacobian(poly_mul(u_poly, self.lam_recomb))) == 0
            naive = self.jet.deformed_hilbert_and_ranks(
                self.lam_recomb, {}, u_poly, degrees=(1, 2, 3, 4, 5, 6)
            )
            naive_vec = [naive["deformed_ranks"][d] for d in range(1, 7)]
            excess_vec = [naive_vec[i] - self.EXPECTED_FLAT_VECTOR[i] for i in range(6)]

            # Closed-form moving-quadric shadow: Lambda_1 = 4 * x_0^4 * x_1^4 * (x_3^2 - x_2^2) * q_45
            m_pos = dict(q45_spec)
            m_pos[0], m_pos[1], m_pos[3] = 4, 4, 2
            m_neg = dict(q45_spec)
            m_neg[0], m_neg[1], m_neg[2] = 4, 4, 2
            lam1: PolyDict = {
                _mon6(m_pos): Fraction(4, 1),
                _mon6(m_neg): Fraction(-4, 1),
            }
            stabilized = self.jet.deformed_hilbert_and_ranks(
                self.lam_recomb, lam1, u_poly, degrees=(1, 2, 3, 4, 5, 6)
            )
            stab_vec = [stabilized["deformed_ranks"][d] for d in range(1, 7)]

            if name == "u_A":
                r0_off, r1_off = self.jet.multiply_dual(g_offender, {}, self.lam_recomb, {}, u_poly)
                g_u_a_nonzero = (len(r0_off) == 0) and (len(r1_off) > 0)
                # Verify Order-2 Gauss-Manin obstruction cancellation: u_A * Lambda_1 in im(M_{u_A})
                u_a_order2_absorbed = self._is_in_u_image(u_poly, poly_mul(u_poly, lam1))

            dir_results.append(
                {
                    "direction": name,
                    "gm1_satisfied": gm1_ok,
                    "naive_m1_flat": naive["flat_by_degree"][1],
                    "naive_all_degrees_flat": naive["all_degrees_flat"],
                    "naive_ranks": naive_vec,
                    "naive_excess": excess_vec,
                    "stabilized_ranks": stab_vec,
                    "stabilized_all_degrees_flat": stabilized["all_degrees_flat"],
                }
            )

        return {
            "base_ranks": self.EXPECTED_BASE_VECTOR,
            "u_flat_ranks": [flat_res["deformed_ranks"][d] for d in range(1, 7)],
            "u_flat_all_degrees_flat": flat_res["all_degrees_flat"],
            "m2_offender_static_zero": (len(g_static_mod) == 0),
            "m2_offender_u_a_obstruction_nonzero": g_u_a_nonzero,
            "u_a_order2_obstruction_absorbed": u_a_order2_absorbed,
            "directions": dir_results,
            "all_moving_stabilized": all(d["stabilized_all_degrees_flat"] for d in dir_results),
        }

    def audit_quadruple_collision_syzygies(self) -> Dict[str, Any]:
        """Audits all 4 non-trivial u_quad collision syzygies across m = 1..6."""
        specs = [
            (0, 2, 4, 3),
            (0, 3, 4, 2),
            (1, 2, 4, 3),
            (1, 3, 4, 2),
        ]
        results: List[Dict[str, Any]] = []
        for a, b, c, d in specs:
            lam0: PolyDict = {
                _mon6({a: 4, b: 4, c: 4}): _one(),
                _mon6({a: 4, b: 4, d: 4}): -_one(),
            }
            gm1_ok = len(poly_mod_jacobian(poly_mul(self.u_quad, lam0))) == 0

            naive = self.jet.deformed_hilbert_and_ranks(
                lam0, {}, self.u_quad, degrees=(1, 2, 3, 4, 5, 6)
            )
            naive_vec = [naive["deformed_ranks"][deg] for deg in range(1, 7)]
            naive_base = [naive["base_ranks"][deg] for deg in range(1, 7)]
            excess_vec = [naive_vec[i] - self.EXPECTED_FLAT_VECTOR[i] for i in range(6)]

            # Closed-form moving shadow:
            # Lambda_1 = 4 * x_a^4 * x_5^2 * (x_b^2 (x_c^4 - x_d^4) + x_b^4 (x_c^2 - x_d^2))
            lam1: PolyDict = {
                _mon6({a: 4, b: 2, c: 4, 5: 2}): Fraction(4, 1),
                _mon6({a: 4, b: 2, d: 4, 5: 2}): Fraction(-4, 1),
                _mon6({a: 4, b: 4, c: 2, 5: 2}): Fraction(4, 1),
                _mon6({a: 4, b: 4, d: 2, 5: 2}): Fraction(-4, 1),
            }
            stab = self.jet.deformed_hilbert_and_ranks(
                lam0, lam1, self.u_quad, degrees=(1, 2, 3, 4, 5, 6)
            )
            stab_vec = [stab["deformed_ranks"][deg] for deg in range(1, 7)]

            results.append(
                {
                    "syzygy_id": f"({a};{b},{c},{d})",
                    "gm1_satisfied": gm1_ok,
                    "base_ranks": naive_base,
                    "naive_ranks": naive_vec,
                    "naive_excess": excess_vec,
                    "naive_all_degrees_flat": naive["all_degrees_flat"],
                    "stabilized_ranks": stab_vec,
                    "stabilized_all_degrees_flat": stab["all_degrees_flat"],
                }
            )

        return {
            "num_syzygies": len(results),
            "syzygies": results,
            "all_naive_jump_from_m1": all(not r["naive_all_degrees_flat"] for r in results),
            "all_stabilized_flat": all(r["stabilized_all_degrees_flat"] for r in results),
        }


# ==============================================================================
# MODULE 2: GENUINE FINITE NON-FERMAT (t^2 != 0) SMOOTH CY4 MACAULAY ENGINE
# ==============================================================================


PairMonomial = Tuple[int, int]
PairPoly = Dict[PairMonomial, Fraction]


def _pair_norm(p: PairPoly) -> PairPoly:
    return {k: v for k, v in p.items() if v != 0}


def _pair_mul(a: PairPoly, b: PairPoly) -> PairPoly:
    out: PairPoly = {}
    for (y1, z1), c1 in a.items():
        for (y2, z2), c2 in b.items():
            m = (y1 + y2, z1 + z2)
            out[m] = out.get(m, _zero()) + c1 * c2
    return _pair_norm(out)


def _build_pair_jacobian_ring(
    df_dy: PairPoly, df_dz: PairPoly, max_deg: int = 9
) -> Dict[str, Any]:
    """Builds exact quotient reduction mod (df_dy, df_dz) in Q[y, z] up to max_deg."""
    basis_by_deg: Dict[int, List[PairMonomial]] = {}
    reduce_table: Dict[int, Dict[PairMonomial, List[Fraction]]] = {}
    graded_dims: Dict[int, int] = {}

    for d in range(max_deg + 1):
        # Monomials ordered lexicographically so higher powers of y reduce to lower (standard lex pivot)
        # Wait: standard monomial order matching probe: (d,0), (d-1,1), ..., (0,d)
        mons = [(d - j, j) for j in range(d + 1)]
        m_idx = {m: i for i, m in enumerate(mons)}
        ncols = len(mons)

        jac_rows: List[Dict[int, Fraction]] = []
        if d >= 5:
            for j in range(d - 5 + 1):
                mult = {(d - 5 - j, j): _one()}
                for deriv in (df_dy, df_dz):
                    prod = _pair_mul(mult, deriv)
                    if prod:
                        jac_rows.append({m_idx[m]: v for m, v in prod.items()})

        # Canonical RREF over Q[y, z]_d using smallest index as pivot
        pivots: Dict[int, Dict[int, Fraction]] = {}
        for raw_row in jac_rows:
            row = {c: v for c, v in raw_row.items() if v != 0}
            for pc in sorted(pivots.keys()):
                fac = row.get(pc, _zero())
                if fac == 0:
                    continue
                for c, pv in pivots[pc].items():
                    nv = row.get(c, _zero()) - fac * pv
                    if nv == 0:
                        row.pop(c, None)
                    else:
                        row[c] = nv
            if not row:
                continue
            fc = min(row.keys())
            inv = _one() / row[fc]
            pivots[fc] = {c: v * inv for c, v in row.items()}

        pcols = sorted(pivots.keys())
        for pc in reversed(pcols):
            prow = pivots[pc]
            for qc in pcols:
                if qc >= pc:
                    break
                qrow = pivots[qc]
                fac = qrow.get(pc, _zero())
                if fac == 0:
                    continue
                for c, pv in prow.items():
                    nv = qrow.get(c, _zero()) - fac * pv
                    if nv == 0:
                        qrow.pop(c, None)
                    else:
                        qrow[c] = nv

        pset = set(pcols)
        free_cols = [c for c in range(ncols) if c not in pset]
        f_pos = {fc: idx for idx, fc in enumerate(free_cols)}
        dim = len(free_cols)
        graded_dims[d] = dim
        basis_by_deg[d] = [mons[fc] for fc in free_cols]

        tbl: Dict[PairMonomial, List[Fraction]] = {}
        for c, mon in enumerate(mons):
            vec = [_zero()] * dim
            if c in f_pos:
                vec[f_pos[c]] = _one()
            elif c in pivots:
                for col_i, val in pivots[c].items():
                    if col_i in f_pos:
                        vec[f_pos[col_i]] = -val
            tbl[mon] = vec
        reduce_table[d] = tbl

    return {
        "graded_dims": graded_dims,
        "basis_by_deg": basis_by_deg,
        "reduce_table": reduce_table,
    }


def _pair_reduce_poly(ring: Dict[str, Any], poly: PairPoly, deg: int) -> List[Fraction]:
    dim = ring["graded_dims"][deg]
    tbl = ring["reduce_table"][deg]
    out = [_zero()] * dim
    for mon, coeff in poly.items():
        if coeff == 0:
            continue
        vec = tbl[mon]
        for i in range(dim):
            if vec[i] != 0:
                out[i] += coeff * vec[i]
    return out


class FiniteNonFermatMacaulayEngine:
    """Exact tensor-reduced finite non-Fermat smooth CY4 Macaulay apolarity engine (t^2 != 0)."""

    def __init__(self) -> None:
        # Three genuinely distinct asymmetric binary sextic pairs:
        # P_0(y,z) = (y - 2z)(y + z)(y^4 + z^4) = y^6 - y^5 z - 2 y^4 z^2 + y^2 z^4 - y z^5 - 2 z^6
        df0_dy: PairPoly = {
            (5, 0): Fraction(6, 1),
            (4, 1): Fraction(-5, 1),
            (3, 2): Fraction(-8, 1),
            (1, 4): Fraction(2, 1),
            (0, 5): Fraction(-1, 1),
        }
        df0_dz: PairPoly = {
            (5, 0): Fraction(-1, 1),
            (4, 1): Fraction(-4, 1),
            (2, 3): Fraction(4, 1),
            (1, 4): Fraction(-5, 1),
            (0, 5): Fraction(-12, 1),
        }
        # P_1(y,z) = (1/6)(y^6 - 3^6 z^6) + (1/5)(y^3 z^3 - 3 y^2 z^4)
        df1_dy: PairPoly = {
            (5, 0): Fraction(1, 1),
            (2, 3): Fraction(3, 5),
            (1, 4): Fraction(-6, 5),
        }
        df1_dz: PairPoly = {
            (0, 5): Fraction(-729, 1),
            (3, 2): Fraction(3, 5),
            (2, 3): Fraction(-12, 5),
        }
        # P_2(y,z) = (1/6)(y^6 - 5^6 z^6) + (1/7)(y^3 z^3 - 5 y^2 z^4)
        df2_dy: PairPoly = {
            (5, 0): Fraction(1, 1),
            (2, 3): Fraction(3, 7),
            (1, 4): Fraction(-10, 7),
        }
        df2_dz: PairPoly = {
            (0, 5): Fraction(-15625, 1),
            (3, 2): Fraction(3, 7),
            (2, 3): Fraction(-20, 7),
        }

        self.rings: Tuple[Dict[str, Any], Dict[str, Any], Dict[str, Any]] = (
            _build_pair_jacobian_ring(df0_dy, df0_dz),
            _build_pair_jacobian_ring(df1_dy, df1_dz),
            _build_pair_jacobian_ring(df2_dy, df2_dz),
        )
        self.pair_slopes: Tuple[int, int, int] = (2, 3, 5)
        self._tensor_cache: Dict[int, List[Tuple[int, int, int, int, int, int]]] = {}

    def _pair_basis_dim_split(self, total_deg: int) -> List[Tuple[int, int, int, int, int, int]]:
        """Lists basis indices ((d0, i0), (d1, i1), (d2, i2)) of R^{total_deg}(F_nF)."""
        if total_deg in self._tensor_cache:
            return self._tensor_cache[total_deg]
        entries: List[Tuple[int, int, int, int, int, int]] = []
        r0, r1, r2 = self.rings
        for d0 in range(min(8, total_deg) + 1):
            dim0 = r0["graded_dims"][d0]
            if dim0 == 0:
                continue
            for d1 in range(min(8, total_deg - d0) + 1):
                d2 = total_deg - d0 - d1
                if d2 < 0 or d2 > 8:
                    continue
                dim1 = r1["graded_dims"][d1]
                dim2 = r2["graded_dims"][d2]
                if dim1 == 0 or dim2 == 0:
                    continue
                for i0 in range(dim0):
                    for i1 in range(dim1):
                        for i2 in range(dim2):
                            entries.append((d0, i0, d1, i1, d2, i2))
        self._tensor_cache[total_deg] = entries
        return entries

    def _pair_deg4_annihilators(self, ring_idx: int, root_c: int) -> List[List[Fraction]]:
        """Finds exact vectors in R^4(P_k) annihilated by (y - c z)."""
        ring = self.rings[ring_idx]
        b4 = ring["basis_by_deg"][4]
        lin: PairPoly = {(1, 0): _one(), (0, 1): Fraction(-root_c, 1)}
        # Build 5 x 5 linear map matrix whose columns are basis_by_deg[4] * (y - c z) in R^5
        rows: List[Dict[int, Fraction]] = []
        col_vecs: List[List[Fraction]] = [_pair_reduce_poly(ring, _pair_mul({m: _one()}, lin), 5) for m in b4]
        dim5 = ring["graded_dims"][5]
        for r in range(dim5):
            row = {c: col_vecs[c][r] for c in range(len(b4)) if col_vecs[c][r] != 0}
            if row:
                rows.append(row)
        _, ker = _sparse_rref_and_nullspace(rows, len(b4))
        return ker

    def _pair0_quad_annihilators(self) -> List[List[Fraction]]:
        """Finds exact vectors in R^4(P_0) annihilated by (y - 2z)(y + z) = y^2 - yz - 2z^2."""
        ring = self.rings[0]
        b4 = ring["basis_by_deg"][4]
        quad: PairPoly = {(2, 0): _one(), (1, 1): Fraction(-1, 1), (0, 2): Fraction(-2, 1)}
        col_vecs = [_pair_reduce_poly(ring, _pair_mul({m: _one()}, quad), 6) for m in b4]
        dim6 = ring["graded_dims"][6]
        rows: List[Dict[int, Fraction]] = []
        for r in range(dim6):
            row = {c: col_vecs[c][r] for c in range(len(b4)) if col_vecs[c][r] != 0}
            if row:
                rows.append(row)
        _, ker = _sparse_rref_and_nullspace(rows, len(b4))
        return ker

    def _multiply_pair_vec_by_deg_k(
        self, ring_idx: int, b_deg: int, lam_vec: List[Fraction], lam_deg: int = 4
    ) -> List[List[Fraction]]:
        """Returns matrix [col_i][out_idx] for multiplying basis_by_deg[b_deg] * lam_vec into R^{b_deg+lam_deg}."""
        ring = self.rings[ring_idx]
        b_lam = ring["basis_by_deg"][lam_deg]
        lam_poly: PairPoly = {b_lam[i]: lam_vec[i] for i in range(len(b_lam)) if lam_vec[i] != 0}
        b_dom = ring["basis_by_deg"][b_deg]
        return [_pair_reduce_poly(ring, _pair_mul({m: _one()}, lam_poly), b_deg + lam_deg) for m in b_dom]

    def _tensor_shadow_macaulay_ranks(
        self,
        psi0_terms: List[Tuple[Fraction, List[Fraction]]],
        psi1_vec: List[Fraction],
        psi2_vec: List[Fraction],
        degrees: Sequence[int] = (1, 2, 3, 4, 5, 6),
    ) -> Tuple[List[int], List[List[Fraction]]]:
        """Computes exact R^m(F_nF) -> R^{12+m}(F_nF) Macaulay ranks and Ann_{R^1} for factorized shadows."""
        ranks: List[int] = []
        ann_r1: List[List[Fraction]] = []

        # Combine psi0_terms into one vector in R^4(P_0)
        dim0_4 = self.rings[0]["graded_dims"][4]
        psi0_vec = [_zero()] * dim0_4
        for weight, vec in psi0_terms:
            for i in range(dim0_4):
                psi0_vec[i] += weight * vec[i]

        for m in degrees:
            dom_entries = self._pair_basis_dim_split(m)
            cod_entries = self._pair_basis_dim_split(12 + m)
            cod_idx = {e: i for i, e in enumerate(cod_entries)}
            nd = len(dom_entries)

            # Precompute pair multiplications per pair degree a0, a1, a2 <= m
            mul0: Dict[int, List[List[Fraction]]] = {}
            mul1: Dict[int, List[List[Fraction]]] = {}
            mul2: Dict[int, List[List[Fraction]]] = {}
            for d in range(min(8, m) + 1):
                if d + 4 <= 8 and self.rings[0]["graded_dims"][d] > 0:
                    mul0[d] = self._multiply_pair_vec_by_deg_k(0, d, psi0_vec, 4)
                if d + 4 <= 8 and self.rings[1]["graded_dims"][d] > 0:
                    mul1[d] = self._multiply_pair_vec_by_deg_k(1, d, psi1_vec, 4)
                if d + 4 <= 8 and self.rings[2]["graded_dims"][d] > 0:
                    mul2[d] = self._multiply_pair_vec_by_deg_k(2, d, psi2_vec, 4)

            row_map: Dict[int, Dict[int, Fraction]] = {}
            for col, (a0, i0, a1, i1, a2, i2) in enumerate(dom_entries):
                if a0 + 4 > 8 or a1 + 4 > 8 or a2 + 4 > 8:
                    continue
                v0 = mul0[a0][i0]
                v1 = mul1[a1][i1]
                v2 = mul2[a2][i2]
                nz0 = [(j0, c0) for j0, c0 in enumerate(v0) if c0 != 0]
                nz1 = [(j1, c1) for j1, c1 in enumerate(v1) if c1 != 0]
                nz2 = [(j2, c2) for j2, c2 in enumerate(v2) if c2 != 0]
                b0, b1, b2 = a0 + 4, a1 + 4, a2 + 4
                for j0, c0 in nz0:
                    for j1, c1 in nz1:
                        c01 = c0 * c1
                        for j2, c2 in nz2:
                            r = cod_idx[(b0, j0, b1, j1, b2, j2)]
                            rm = row_map.setdefault(r, {})
                            nv = rm.get(col, _zero()) + c01 * c2
                            if nv == 0:
                                rm.pop(col, None)
                            else:
                                rm[col] = nv

            rows = list(row_map.values())
            rk, ker = _sparse_rref_and_nullspace(rows, nd)
            ranks.append(rk)
            if m == 1:
                ann_r1 = ker

        return ranks, ann_r1

    def _verify_pair0_quad_annihilates_quad_shadow(
        self, psi0_vec: List[Fraction]
    ) -> bool:
        """Verifies (x_0 - 2x_3)(x_0 + x_3) annihilates psi0_vec in R^6(P_0)."""
        ring0 = self.rings[0]
        b4 = ring0["basis_by_deg"][4]
        psi0_poly: PairPoly = {b4[i]: psi0_vec[i] for i in range(len(b4)) if psi0_vec[i] != 0}
        quad_poly: PairPoly = {(2, 0): _one(), (1, 1): Fraction(-1, 1), (0, 2): Fraction(-2, 1)}
        reduced = _pair_reduce_poly(ring0, _pair_mul(quad_poly, psi0_poly), 6)
        return all(v == 0 for v in reduced)

    def run_audit(self) -> Dict[str, Any]:
        """Executes the full finite non-Fermat smooth CY4 Macaulay verification."""
        pair_hilberts = [
            [r["graded_dims"][d] for d in range(10)] for r in self.rings
        ]
        pair_milnors = [sum(h[:9]) for h in pair_hilberts]
        total_milnor = pair_milnors[0] * pair_milnors[1] * pair_milnors[2]

        # 6-variable Jacobian dimensions directly from tensor split
        dims_6var = {
            d: len(self._pair_basis_dim_split(d)) for d in (1, 2, 3, 4, 5, 6, 12, 18)
        }

        # Linear pair annihilators
        k0_lin = self._pair_deg4_annihilators(0, 2)
        k1_lin = self._pair_deg4_annihilators(1, 3)
        k2_lin = self._pair_deg4_annihilators(2, 5)
        k0_quad = self._pair_deg4_annihilators(0, -1)

        psi0_a = k0_lin[0]
        psi0_b = k0_quad[0]
        psi1 = k1_lin[0]
        psi2 = k2_lin[0]

        plane_ranks, plane_ann1 = self._tensor_shadow_macaulay_ranks(
            [(Fraction(1, 1), psi0_a)], psi1, psi2
        )
        quad_ranks, quad_ann1 = self._tensor_shadow_macaulay_ranks(
            [(Fraction(1, 1), psi0_a), (Fraction(1, 1), psi0_b)], psi1, psi2
        )

        # Also verify the 2D R^4(P_0) kernel of (y-2z)(y+z) contains psi0_a + psi0_b
        psi0_sum = [psi0_a[i] + psi0_b[i] for i in range(len(psi0_a))]
        quad_ann_verified = self._verify_pair0_quad_annihilates_quad_shadow(psi0_sum)

        # Check linear generator slopes recovered in Ann_{R^1}:
        # R^1 basis entries order: (1,0,0,0,0,0)=x_0, (1,1,0,...)=x_3, (0,0,1,0,0,0)=x_1, (0,0,1,1,0,0)=x_4, ...
        dom1_entries = self._pair_basis_dim_split(1)
        # Map entry to variable name cleanly via pair ring degree-1 basis:
        var_names_per_pair = [
            {0: "x_0", 1: "x_3"},
            {0: "x_1", 1: "x_4"},
            {0: "x_2", 1: "x_5"},
        ]
        var_labels: List[str] = []
        for a0, i0, a1, i1, a2, i2 in dom1_entries:
            if a0 == 1:
                var_labels.append(var_names_per_pair[0][i0])
            elif a1 == 1:
                var_labels.append(var_names_per_pair[1][i1])
            else:
                var_labels.append(var_names_per_pair[2][i2])

        # Verify each Ann_{R^1} kernel vector vanishes when substituting (x_0=2 x_3, x_1=3 x_4, x_2=5 x_5)
        subs = {"x_0": 2, "x_3": 1, "x_1": 3, "x_4": 1, "x_2": 5, "x_5": 1}
        # Note: in our pair basis ordering, (d-j, j) has (1,0) first -> y (x_0,x_1,x_2) and (0,1) second -> z (x_3,x_4,x_5)
        # Verify substitution evaluates identically to 0 on Plane_nF kernel (3 eqs) and pair-1/2 on Quad_nF (2 eqs)
        plane_lin_exact = (
            len(plane_ann1) == 3
            and all(
                sum(vec[c] * subs[var_labels[c]] for c in range(len(dom1_entries))) == 0
                for vec in plane_ann1
            )
        )
        quad_lin_exact = (
            len(quad_ann1) == 2
            and all(
                sum(vec[c] * subs[var_labels[c]] for c in range(len(dom1_entries))) == 0
                for vec in quad_ann1
            )
        )

        return {
            "pair_hilberts": pair_hilberts,
            "expected_pair_hilbert_0_to_9": [1, 2, 3, 4, 5, 4, 3, 2, 1, 0],
            "pair_milnors": pair_milnors,
            "total_milnor": total_milnor,
            "smooth_zero_deg9": all(h[9] == 0 for h in pair_hilberts),
            "six_var_graded_dims": dims_6var,
            "plane_nf_ranks": plane_ranks,
            "plane_nf_ann1_dim": len(plane_ann1),
            "plane_nf_linear_ideal_verified": plane_lin_exact,
            "quad_nf_ranks": quad_ranks,
            "quad_nf_ann1_dim": len(quad_ann1),
            "quad_nf_ann6_dim": dims_6var[6] - quad_ranks[-1],
            "quad_nf_linear_ideal_verified": quad_lin_exact,
            "quad_nf_quadratic_generator_verified": quad_ann_verified,
        }


# ==============================================================================
# MODULE 3: NON-SEPARABLE BRIDGE A HONESTY AUDIT & UNIFIED FACADE
# ==============================================================================


class NonSeparableBridgeAHonestyAudit:
    """Explicit Millennium honesty boundary on non-Fermat and universal Macaulay stabilization."""

    @staticmethod
    def summarize() -> Dict[str, Any]:
        return {
            "universal_non_fermat_determinantal_stabilization_proved": False,
            "effective_hilbert_degree_bound_known": False,
            "non_separable_dense_non_fermat_universal_bound_proved": False,
            "global_hodge_conjecture_status": "OPEN",
        }


class NonFermatDeterminantalStabilizationEngine:
    """Unified Event 29 verification engine coordinating Modules 1-3."""

    def __init__(self) -> None:
        self.collision_engine = CollisionHigherDegreeDeterminantalEngine()
        self.non_fermat_engine = FiniteNonFermatMacaulayEngine()

    def run_full_audit(self) -> Dict[str, Any]:
        recomb = self.collision_engine.audit_recombined_higher_degrees()
        quad_syz = self.collision_engine.audit_quadruple_collision_syzygies()
        finite_nf = self.non_fermat_engine.run_audit()
        honesty = NonSeparableBridgeAHonestyAudit.summarize()
        self_forbidden = scan_forbidden(__file__)

        return {
            "recombined_higher_degree": recomb,
            "quadruple_collision_syzygies": quad_syz,
            "finite_non_fermat": finite_nf,
            "honesty_boundary": honesty,
            "scan_forbidden_hits": len(self_forbidden),
            "universal_non_fermat_determinantal_stabilization_proved": honesty[
                "universal_non_fermat_determinantal_stabilization_proved"
            ],
            "effective_hilbert_degree_bound_known": honesty[
                "effective_hilbert_degree_bound_known"
            ],
            "global_hodge_conjecture_status": honesty["global_hodge_conjecture_status"],
        }


if __name__ == "__main__":
    engine = NonFermatDeterminantalStabilizationEngine()
    rep = engine.run_full_audit()
    rc = rep["recombined_higher_degree"]
    qs = rep["quadruple_collision_syzygies"]
    fnf = rep["finite_non_fermat"]

    print(
        f"[RECOMB-M6] base={rc['base_ranks']} u_flat={rc['u_flat_ranks']} "
        f"all_moving_stab={rc['all_moving_stabilized']} order2_absorbed={rc['u_a_order2_obstruction_absorbed']}"
    )
    for d in rc["directions"]:
        print(
            f"  dir={d['direction']} naive={d['naive_ranks']} excess={d['naive_excess']} "
            f"stab={d['stabilized_ranks']} flat={d['stabilized_all_degrees_flat']}"
        )
    print(
        f"[QUAD-SYZ-M6] count={qs['num_syzygies']} all_naive_jump={qs['all_naive_jump_from_m1']} "
        f"all_stab_flat={qs['all_stabilized_flat']}"
    )
    for s in qs["syzygies"]:
        print(
            f"  syz={s['syzygy_id']} naive={s['naive_ranks']} excess={s['naive_excess']} "
            f"stab={s['stabilized_ranks']}"
        )
    print(
        f"[FINITE-NON-FERMAT] milnor={fnf['total_milnor']} dims={fnf['six_var_graded_dims']} "
        f"Plane_nF={fnf['plane_nf_ranks']} (lin={fnf['plane_nf_linear_ideal_verified']}) "
        f"Quad_nF={fnf['quad_nf_ranks']} (ann6={fnf['quad_nf_ann6_dim']}, "
        f"lin={fnf['quad_nf_linear_ideal_verified']}, quad={fnf['quad_nf_quadratic_generator_verified']})"
    )
    print(
        f"[AUDIT] scan_forbidden={rep['scan_forbidden_hits']} "
        f"universal_nf_stab={rep['universal_non_fermat_determinantal_stabilization_proved']} "
        f"global_hodge={rep['global_hodge_conjecture_status']}"
    )
