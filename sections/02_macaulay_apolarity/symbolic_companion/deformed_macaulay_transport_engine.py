r"""Deformed Macaulay Transport Engine & Infinitesimal Gotzmann Persistence Audit.

Formalizes exact polynomial arithmetic and Macaulay apolarity transport inside the
first-order deformed Jacobian ring
    R(F_t) = Q[x_0, ..., x_5][t] / (t^2, dF_t/dx_0, ..., dF_t/dx_5),
where F_0 = 1/6 sum_{i=0}^5 x_i^6 and F_t = F_0 + t u for u in R^6(F_0).

Modules:
  1. DeformedJacobianRingJet:
     Exact canonical normal-form reduction mod (J(F_t), t^2) via the relation
     x_i^5 === -t du/dx_i (mod d_i F_t, t^2), dual-number polynomial multiplication,
     and deformed graded multiplication operators M~^{(m)}_{lambda_t} over Q[t]/(t^2).
  2. MovingApolarityFlatnessVerifier:
     Proves exact deformed Jacobian cancellation (x_i * lambda_0) + t (x_i * lambda_1(u))
     === 0 (mod J(F_t), t^2) for i in {0,1,2} across all 18 quadratic moving-plane
     directions u = x_i^2 r(x_3, x_4, x_5) (a_3+a_4+a_5 = 4, a_3,a_4,a_5 <= 2) even
     though static x_i * lambda_1(u) != 0 (mod J(F_0)_{13}); verifies diagonal
     fixed-ideal transport across all 359 directions with S^{(2)}(u) in J(F_0)_{18}
     and full multi-degree ideal transport across the 260 codimension>=2 directions
     (including all 56 canonical fixed-plane directions) plus all 54 u_i>=2 one-axis
     directions; and proves no lambda_1 in R^{12}(F_0) preserves deformed IVHS
     annihilators along obstructed directions on lambda_chain and lambda_stealth.
  3. GotzmannDeformationPersistenceAudit:
     Proves flat deformed Macaulay Hilbert vector H(m) = (1, 3, 6, 10, 15, 18, 19)
     (total dimension 72, binomial Gotzmann growth G_t = 1 on m = 0..4) across all 18
     quadratic moving-plane and 56 canonical fixed-plane directions, while strictly
     enforcing the open Bridge A boundary (disconnected Hodge loci Sigma_gamma away
     from F_0 remain outside formal jets Q[[t]] around F_0).

Zero-Float Guardrail: Strictly integer, tuple, and fractions.Fraction arithmetic.
"""

from __future__ import annotations

import itertools
import sys
from fractions import Fraction
from pathlib import Path
from typing import Any, Dict, List, Optional, Sequence, Tuple

_REPO_ROOT = str(Path(__file__).resolve().parent.parent)
if _REPO_ROOT not in sys.path:
    sys.path.insert(0, _REPO_ROOT)

from toolkit.calabi_yau_jacobian_engine import CalabiYauJacobianEngine
from toolkit.erdos_fourier_incidence_engine import FourierShadowDetector
from toolkit.exact_linalg import ExactColumnSpan
from toolkit.higher_order_gauss_manin_sieve import (
    GaussManinJetTower,
    Monomial,
    PolyDict,
    _SparseTrackedSpan,
    poly_add,
    poly_mod_jacobian,
    poly_mul,
    poly_neg,
    poly_partial,
)
from toolkit.macaulay_apolarity_inverse_engine import (
    MacaulayApolarityTower,
    _sparse_rref_and_nullspace,
)


def _zero() -> Fraction:
    return Fraction(0, 1)


def _one() -> Fraction:
    return Fraction(1, 1)


def _norm_poly(poly: Dict[Monomial, Any]) -> PolyDict:
    out: PolyDict = {}
    for mon, coeff in poly.items():
        fc = coeff if isinstance(coeff, Fraction) else Fraction(int(coeff), 1)
        if fc != 0:
            out[mon] = fc
    return out


# ==============================================================================
# MODULE 1: DEFORMED JACOBIAN RING R(F_t) = Q[x][t]/(t^2, dF_t/dx_i)
# ==============================================================================

class DeformedJacobianRingJet:
    """Exact dual-number arithmetic and graded Macaulay maps in R(F_t)."""

    FLAT_HILBERT_VECTOR: Tuple[int, ...] = (1, 3, 6, 10, 15, 18, 19)
    FLAT_HILBERT_SUM: int = 72
    LAM_PI: PolyDict = {(4, 4, 4, 0, 0, 0): Fraction(1, 1)}
    LAM_CHAIN: PolyDict = {(4, 3, 3, 2, 0, 0): Fraction(1, 1), (2, 3, 3, 4, 0, 0): Fraction(1, 1)}
    LAM_STEALTH: PolyDict = {(4, 3, 3, 2, 0, 0): Fraction(1, 1), (0, 3, 4, 1, 4, 0): Fraction(1, 1)}

    def __init__(
        self,
        macaulay_tower: Optional[MacaulayApolarityTower] = None,
        jet_tower: Optional[GaussManinJetTower] = None,
    ) -> None:
        self.cy = CalabiYauJacobianEngine()
        self.jac_deg = self.cy.jac_deg
        self.num_vars = self.cy.num_vars
        self.macaulay = (
            macaulay_tower if macaulay_tower is not None else MacaulayApolarityTower()
        )
        self.jet_tower = (
            jet_tower if jet_tower is not None else GaussManinJetTower(self.cy)
        )

    def reduce_mod_deformed_jacobian(
        self,
        poly_0: Dict[Monomial, Any],
        poly_1: Dict[Monomial, Any],
        u_poly: Dict[Monomial, Any],
    ) -> Tuple[PolyDict, PolyDict]:
        """Canonically reduces P_0 + t P_1 modulo (d_i F_0 + t d_i u, t^2).

        Uses exact identity x_i^5 === -t d_i u (mod d_i F_t, t^2):
        - Any monomial in P_0 with two distinct coordinates >= 5 or any coordinate >= 10
          vanishes identically mod t^2.
        - Any monomial in P_0 with a unique coordinate i in [5, 9] transfers
          -coeff * x^{m - 5 e_i} * (d_i u) into the t^1 component.
        - Because t * x_i^5 === 0 (mod d_i F_t, t^2), the total t^1 component is reduced
          canonically mod J(F_0) = (x_0^5, ..., x_5^5).
        """
        p0 = _norm_poly(poly_0)
        t1_accum = _norm_poly(poly_1)
        u_norm = _norm_poly(u_poly)
        dus = [poly_partial(u_norm, i) for i in range(self.num_vars)]

        r0: PolyDict = {}
        for mon, coeff in p0.items():
            if coeff == 0:
                continue
            ge_indices = [i for i in range(self.num_vars) if mon[i] >= self.jac_deg]
            if not ge_indices:
                r0[mon] = r0.get(mon, _zero()) + coeff
                if r0[mon] == 0:
                    r0.pop(mon)
                continue
            if len(ge_indices) == 1 and mon[ge_indices[0]] < 2 * self.jac_deg:
                idx = ge_indices[0]
                du_i = dus[idx]
                if not du_i:
                    continue
                rem = list(mon)
                rem[idx] -= self.jac_deg
                rem_t: Monomial = (rem[0], rem[1], rem[2], rem[3], rem[4], rem[5])
                transfer = poly_mul({rem_t: -coeff}, du_i)
                t1_accum = poly_add(t1_accum, transfer)
            # Otherwise >=2 factors of x_i^5 give t^2 == 0 identically.

        r1 = poly_mod_jacobian(t1_accum, self.jac_deg)
        return r0, r1

    def multiply_dual(
        self,
        a0: Dict[Monomial, Any],
        a1: Dict[Monomial, Any],
        b0: Dict[Monomial, Any],
        b1: Dict[Monomial, Any],
        u_poly: Dict[Monomial, Any],
    ) -> Tuple[PolyDict, PolyDict]:
        """Multiplies (a0 + t a1) * (b0 + t b1) mod (J(F_t), t^2)."""
        a0n, a1n = _norm_poly(a0), _norm_poly(a1)
        b0n, b1n = _norm_poly(b0), _norm_poly(b1)
        prod0 = poly_mul(a0n, b0n)
        prod1 = poly_add(poly_mul(a0n, b1n), poly_mul(a1n, b0n))
        return self.reduce_mod_deformed_jacobian(prod0, prod1, u_poly)

    def deformed_multiplication_sparse_rows(
        self,
        lam0_poly: Dict[Monomial, Any],
        lam1_poly: Dict[Monomial, Any],
        u_poly: Dict[Monomial, Any],
        m: int,
    ) -> Tuple[int, int, List[Dict[int, Fraction]]]:
        """Builds Q-linear 2 d_{12+m} x 2 d_m matrix for M~^{(m)}_{lambda_t} over Q[t]/(t^2)."""
        if m not in self.macaulay.DOMAIN_DEGREES:
            raise ValueError(f"Degree m must be in 1..6, got {m}")
        dom = self.macaulay.bases[m]
        cod = self.macaulay.bases[12 + m]
        cidx = self.macaulay.base_indices[12 + m]
        nd = len(dom)
        nc = len(cod)

        lam0 = _norm_poly(lam0_poly)
        lam1 = _norm_poly(lam1_poly)
        u_norm = _norm_poly(u_poly)

        row_map: Dict[int, Dict[int, Fraction]] = {}
        for col, b in enumerate(dom):
            b_poly: PolyDict = {b: _one()}
            # Column (b, 0): M~^{(m)}(b + 0*t) = b*lam0 + t*(b*lam1) mod (J(F_t), t^2)
            r0, r1 = self.multiply_dual(b_poly, {}, lam0, lam1, u_norm)
            for mon, val in r0.items():
                rr = cidx[mon]
                e_top = row_map.setdefault(rr, {})
                nv = e_top.get(col, _zero()) + val
                if nv == 0:
                    e_top.pop(col, None)
                else:
                    e_top[col] = nv
                # Column (0, b): M~^{(m)}(0 + t*b) = 0 + t*(b*lam0 mod J(F_0))
                e_bot_b = row_map.setdefault(nc + rr, {})
                col_b = nd + col
                nv_b = e_bot_b.get(col_b, _zero()) + val
                if nv_b == 0:
                    e_bot_b.pop(col_b, None)
                else:
                    e_bot_b[col_b] = nv_b

            for mon, val in r1.items():
                rr = cidx[mon]
                e_bot_a = row_map.setdefault(nc + rr, {})
                nv_a = e_bot_a.get(col, _zero()) + val
                if nv_a == 0:
                    e_bot_a.pop(col, None)
                else:
                    e_bot_a[col] = nv_a

        rows = [r for r in row_map.values() if r]
        return 2 * nc, 2 * nd, rows

    def deformed_hilbert_and_ranks(
        self,
        lam0_poly: Dict[Monomial, Any],
        lam1_poly: Dict[Monomial, Any],
        u_poly: Dict[Monomial, Any],
        degrees: Sequence[int] = (1, 2, 3, 4, 5, 6),
    ) -> Dict[str, Any]:
        """Computes exact Q-ranks rk(M~^{(m)}) and compares against 2 * rk(M_0^{(m)})."""
        base_ranks: Dict[int, int] = {}
        deformed_ranks: Dict[int, int] = {}
        flat_by_degree: Dict[int, bool] = {}

        for deg in degrees:
            _, nd0, rows0 = self.macaulay.multiplication_sparse_rows(lam0_poly, deg)
            rk0, _ = _sparse_rref_and_nullspace(rows0, nd0)
            _, nd_def, rows_def = self.deformed_multiplication_sparse_rows(
                lam0_poly, lam1_poly, u_poly, deg
            )
            rk_def, _ = _sparse_rref_and_nullspace(rows_def, nd_def)
            base_ranks[deg] = rk0
            deformed_ranks[deg] = rk_def
            flat_by_degree[deg] = (rk_def == 2 * rk0)

        return {
            "base_ranks": base_ranks,
            "deformed_ranks": deformed_ranks,
            "flat_by_degree": flat_by_degree,
            "all_degrees_flat": all(flat_by_degree.values()),
        }


# ==============================================================================
# MODULE 2: MOVING APOLARITY FLATNESS VERIFIER & OBSTRUCTION ENGINE
# ==============================================================================

class MovingApolarityFlatnessVerifier:
    """Verifies exact moving-plane Jacobian cancellation, fixed directions, and obstructions."""

    def __init__(self, ring_jet: Optional[DeformedJacobianRingJet] = None) -> None:
        self.jet = ring_jet if ring_jet is not None else DeformedJacobianRingJet()
        self.macaulay = self.jet.macaulay
        self.tower = self.jet.jet_tower
        self.lam_pi = self.jet.LAM_PI

        # Precompute exact im(M^{(m)}_{lambda_Pi}) spans & ker(M^{(m)}_{lambda_Pi}) bases for fast sweep
        self._pi_base_ranks: Dict[int, int] = {}
        self._pi_im_spans: Dict[int, ExactColumnSpan] = {}
        self._pi_ker_monomials: Dict[int, List[Monomial]] = {}
        for deg in self.macaulay.DOMAIN_DEGREES:
            dom = self.macaulay.bases[deg]
            cod = self.macaulay.bases[12 + deg]
            cidx = self.macaulay.base_indices[12 + deg]
            _, _, r0 = self.macaulay.multiplication_sparse_rows(self.lam_pi, deg)
            rk0, kb0 = _sparse_rref_and_nullspace(r0, len(dom))
            self._pi_base_ranks[deg] = rk0
            ker_mons: List[Monomial] = []
            for vec in kb0:
                nz = [j for j, val in enumerate(vec) if val != 0]
                assert len(nz) == 1
                ker_mons.append(dom[nz[0]])
            self._pi_ker_monomials[deg] = ker_mons

            im_cols: List[List[Fraction]] = []
            for b in dom:
                p = poly_mod_jacobian(poly_mul({b: _one()}, self.lam_pi), self.jet.jac_deg)
                if p:
                    col_vec = [_zero()] * len(cod)
                    for mon, val in p.items():
                        col_vec[cidx[mon]] = val
                    im_cols.append(col_vec)
            transposed = [[im_cols[c][r] for c in range(len(im_cols))] for r in range(len(cod))]
            self._pi_im_spans[deg] = ExactColumnSpan(transposed)

    @staticmethod
    def enumerate_quadratic_moving_plane_directions() -> List[Dict[str, Any]]:
        """Generates all 18 directions u = x_i^2 r(x_3, x_4, x_5), sum a=4, max a<=2."""
        r_exps: List[Tuple[int, int, int]] = []
        for a3 in (2, 1, 0):
            for a4 in (2, 1, 0):
                for a5 in (2, 1, 0):
                    if a3 + a4 + a5 == 4:
                        r_exps.append((a3, a4, a5))
        assert len(r_exps) == 6

        directions: List[Dict[str, Any]] = []
        for i in (0, 1, 2):
            for a3, a4, a5 in r_exps:
                u_list = [0, 0, 0, a3, a4, a5]
                u_list[i] = 2
                u_mon: Monomial = (u_list[0], u_list[1], u_list[2], u_list[3], u_list[4], u_list[5])

                l1_list = [4, 4, 4, a3, a4, a5]
                l1_list[i] = 0
                l1_mon: Monomial = (l1_list[0], l1_list[1], l1_list[2], l1_list[3], l1_list[4], l1_list[5])

                directions.append(
                    {
                        "index_i": i,
                        "r_exp": (a3, a4, a5),
                        "u_monomial": u_mon,
                        "lam1_monomial": l1_mon,
                        "lam1_poly": {l1_mon: Fraction(2, 1)},
                    }
                )
        assert len(directions) == 18
        return directions

    def check_block_flatness_pi(
        self,
        u_poly: Dict[Monomial, Any],
        lam1_poly: Dict[Monomial, Any],
    ) -> bool:
        """Exact criterion: rk(M~^{(m)}) == 2 rk(M_0^{(m)}) iff K^{(m)}(ker M_0) subset im(M_0)."""
        u_norm = _norm_poly(u_poly)
        lam1_norm = _norm_poly(lam1_poly)
        for deg in self.macaulay.DOMAIN_DEGREES:
            cod = self.macaulay.bases[12 + deg]
            cidx = self.macaulay.base_indices[12 + deg]
            im_span = self._pi_im_spans[deg]
            for b in self._pi_ker_monomials[deg]:
                _, r1 = self.jet.multiply_dual({b: _one()}, {}, self.lam_pi, lam1_norm, u_norm)
                if not r1:
                    continue
                dense = [_zero()] * len(cod)
                for mon, val in r1.items():
                    dense[cidx[mon]] = val
                if not im_span.contains(dense):
                    return False
        return True

    def verify_quadratic_moving_plane_directions(self) -> Dict[str, Any]:
        """Verifies exact deformed cancellation & m=1..6 flatness across all 18 directions."""
        directions = self.enumerate_quadratic_moving_plane_directions()
        per_direction: List[Dict[str, Any]] = []
        static_nonzero_count = 0
        deformed_cancel_all3_count = 0
        all_deg_block_flat_count = 0

        # Also run full explicit 2*d_m x 2*d_m RREF on canonical representative for i = 0, 1, 2
        direct_rref_witnesses: List[Dict[str, Any]] = []
        seen_i = set()

        for item in directions:
            i = item["index_i"]
            u_mon: Monomial = item["u_monomial"]
            lam1_poly: PolyDict = item["lam1_poly"]
            u_poly: PolyDict = {u_mon: _one()}

            # 1. Static check: x_i * lambda_1(u) != 0 mod J(F_0)_{13}
            x_i = tuple(1 if k == i else 0 for k in range(6))
            static_prod = poly_mod_jacobian(poly_mul({x_i: _one()}, lam1_poly), self.jet.jac_deg)
            static_nonzero = bool(static_prod)
            if static_nonzero:
                static_nonzero_count += 1

            # 2. Deformed check: (x_j * lam_Pi) + t (x_j * lam1(u)) === 0 mod (J(F_t), t^2) for j in {0,1,2}
            deformed_ok = True
            for j in (0, 1, 2):
                x_j = tuple(1 if k == j else 0 for k in range(6))
                r0, r1 = self.jet.multiply_dual({x_j: _one()}, {}, self.lam_pi, lam1_poly, u_poly)
                if r0 or r1:
                    deformed_ok = False
                    break
            if deformed_ok:
                deformed_cancel_all3_count += 1

            # 3. Full degree m=1..6 block flatness
            block_flat = self.check_block_flatness_pi(u_poly, lam1_poly)
            if block_flat:
                all_deg_block_flat_count += 1

            if i not in seen_i:
                seen_i.add(i)
                rref_res = self.jet.deformed_hilbert_and_ranks(
                    self.lam_pi, lam1_poly, u_poly
                )
                assert rref_res["all_degrees_flat"]
                direct_rref_witnesses.append(
                    {
                        "index_i": i,
                        "u_monomial": u_mon,
                        "lam1_monomial": item["lam1_monomial"],
                        "deformed_ranks": rref_res["deformed_ranks"],
                        "all_degrees_flat": rref_res["all_degrees_flat"],
                    }
                )

            per_direction.append(
                {
                    "index_i": i,
                    "u_monomial": u_mon,
                    "lam1_monomial": item["lam1_monomial"],
                    "static_xi_lam1_nonzero": static_nonzero,
                    "deformed_all_x012_cancelled": deformed_ok,
                    "full_m1_to_m6_flat": block_flat,
                }
            )

        assert static_nonzero_count == 18
        assert deformed_cancel_all3_count == 18
        assert all_deg_block_flat_count == 18

        return {
            "total_directions": len(directions),
            "static_xi_lam1_nonzero_count": static_nonzero_count,
            "deformed_x012_exact_cancellation_count": deformed_cancel_all3_count,
            "full_m1_to_m6_flat_count": all_deg_block_flat_count,
            "direct_full_rref_witness_count": len(direct_rref_witnesses),
            "direct_rref_witnesses": direct_rref_witnesses,
            "directions": per_direction,
        }

    def verify_fixed_ideal_directions(self) -> Dict[str, Any]:
        """Audits all 359 fixed-S^{(2)} directions (S^{(2)}(u) in J(F_0)_{18}) plus 54 u_i>=2 lifts."""
        ker6 = self.tower.ivhs_kernel_basis(self.lam_pi)
        assert len(ker6) == 407

        fixed_359: List[Monomial] = []
        canonical_fixed_56: List[Monomial] = []
        diagonal_u_dot_lam0_zero_count = 0
        full_ideal_flat_lam1_zero_count = 0
        canonical_56_full_ideal_flat_count = 0
        one_axis_u_ge_2_count = 0
        one_axis_u_ge_2_explicit_lam1_flat_count = 0
        linear_u_eq_1_residual_count = 0

        for u in ker6:
            u_poly: PolyDict = {u: _one()}
            A1 = self.tower.extract_koszul_syzygy(poly_mul(u_poly, self.lam_pi))
            S2 = self.tower.contract_with_du(A1, u_poly)
            if poly_mod_jacobian(S2, self.jet.jac_deg):
                continue
            fixed_359.append(u)

            # Diagonal transport: (u + 0*t) * (lam_Pi + 0*t) === 0 mod (J(F_t), t^2)
            r0_u, r1_u = self.jet.multiply_dual(u_poly, {}, self.lam_pi, {}, u_poly)
            if not r0_u and not r1_u:
                diagonal_u_dot_lam0_zero_count += 1

            # Full m=1..6 ideal flatness with lam1 = 0
            is_flat_0 = self.check_block_flatness_pi(u_poly, {})
            if is_flat_0:
                full_ideal_flat_lam1_zero_count += 1

            if u[0] >= 1 and u[1] >= 1 and u[2] >= 1:
                canonical_fixed_56.append(u)
                assert is_flat_0
                canonical_56_full_ideal_flat_count += 1
            elif sum(1 for k in range(3) if u[k] >= 1) == 1:
                max_a = max(u[0], u[1], u[2])
                if max_a >= 2:
                    one_axis_u_ge_2_count += 1
                    idx = [k for k in range(3) if u[k] >= 2][0]
                    ui = u[idx]
                    l1_exp = list(u)
                    l1_exp[idx] = ui - 2
                    for k in range(3):
                        if k != idx:
                            l1_exp[k] = 4
                    lam1_u: PolyDict = {tuple(l1_exp): Fraction(ui, 1)}  # type: ignore[dict-item]
                    # Check all x_0, x_1, x_2 cancel & full m=1..6 flatness
                    ok_all = self.check_block_flatness_pi(u_poly, lam1_u)
                    assert ok_all
                    one_axis_u_ge_2_explicit_lam1_flat_count += 1
                else:
                    linear_u_eq_1_residual_count += 1

        assert len(fixed_359) == 359
        assert len(canonical_fixed_56) == 56
        assert diagonal_u_dot_lam0_zero_count == 359
        assert full_ideal_flat_lam1_zero_count == 260
        assert canonical_56_full_ideal_flat_count == 56
        assert one_axis_u_ge_2_count == 54
        assert one_axis_u_ge_2_explicit_lam1_flat_count == 54
        assert linear_u_eq_1_residual_count == 45

        # Explicit full 2*d_m x 2*d_m RREF witness on a canonical fixed direction
        canonical_witness_u: Monomial = (1, 1, 1, 3, 0, 0)
        assert canonical_witness_u in canonical_fixed_56
        canonical_rref = self.jet.deformed_hilbert_and_ranks(
            self.lam_pi, {}, {canonical_witness_u: _one()}
        )
        assert canonical_rref["all_degrees_flat"]

        return {
            "fixed_s2_directions_total": len(fixed_359),
            "diagonal_u_dot_lam0_vanishes_count": diagonal_u_dot_lam0_zero_count,
            "full_m1_to_m6_flat_with_lam1_zero_count": full_ideal_flat_lam1_zero_count,
            "canonical_fixed_56_total": len(canonical_fixed_56),
            "canonical_fixed_56_flat_count": canonical_56_full_ideal_flat_count,
            "one_axis_u_ge_2_flat_with_explicit_lam1_count": one_axis_u_ge_2_explicit_lam1_flat_count,
            "linear_u_eq_1_monomial_nonflat_count": linear_u_eq_1_residual_count,
            "canonical_witness_u": canonical_witness_u,
            "canonical_witness_deformed_ranks": canonical_rref["deformed_ranks"],
        }

    def prove_no_lam1_preserves_kernel_along_u(
        self,
        lam0_poly: Dict[Monomial, Any],
        u_monomial: Monomial,
    ) -> Dict[str, Any]:
        """Proves NO lambda_1 in R^{12}(F_0) solves r_1(u * lambda_0) + u * lambda_1 in im(M^{(6)}_{lambda_0}).

        Because rk(M~^{(6)}_{lambda_t}) == 2 * rk(M^{(6)}_{lambda_0}) requires K^{(6)}(b) in im(M^{(6)})
        for every b in ker(M^{(6)}), restricting to b = u already proves infeasibility whenever
        r_1(u * lambda_0) not in im(M^{(6)}_{lambda_0}) + u * R^{12}(F_0).
        """
        lam0 = _norm_poly(lam0_poly)
        u_poly: PolyDict = {u_monomial: _one()}

        # Verify u belongs to ker(M^{(6)}_{lam0})
        u_lam0_mod = poly_mod_jacobian(poly_mul(u_poly, lam0), self.jet.jac_deg)
        assert not u_lam0_mod, f"Expected u in ker(M^(6)), got residual {u_lam0_mod}"

        # Compute exact r_1(u * lam0) mod J(F_0)_{18}
        r0_check, r1_u = self.jet.multiply_dual(u_poly, {}, lam0, {}, u_poly)
        assert not r0_check

        # Build exact span im(M^{(6)}_{lam0}) + u * R^{12}(F_0)
        im_span = self.tower.build_im_span(lam0)
        ext_span = self.tower.extend_span_with_u_r12(im_span, u_monomial)

        target_vec = {self.tower.m18_idx[m]: c for m, c in r1_u.items()}
        solvable, _ = ext_span.solve(target_vec)
        assert not solvable, (
            f"Expected no lambda_1 solution in R^12 for {u_monomial}, but span solve succeeded"
        )

        # Also verify directly at lambda_1 = 0 that full 2*d_6 RREF strictly exceeds 2 * base_rank
        rref_lam1_zero = self.jet.deformed_hilbert_and_ranks(
            lam0, {}, u_poly, degrees=(6,)
        )
        base_rk6 = rref_lam1_zero["base_ranks"][6]
        def_rk6_zero = rref_lam1_zero["deformed_ranks"][6]
        assert def_rk6_zero > 2 * base_rk6

        return {
            "u_monomial": u_monomial,
            "u_in_ker_M6": True,
            "base_rank_m6": base_rk6,
            "deformed_rank_m6_lam1_zero": def_rk6_zero,
            "expected_flat_double_rank_m6": 2 * base_rk6,
            "im_M6_plus_uR12_rank": ext_span.rank,
            "no_lam1_in_R12_preserves_kernel": (not solvable),
            "r1_u_lam0_monomial_count": len(r1_u),
        }

    def audit_artificial_class_obstructions(self) -> Dict[str, Any]:
        """Audits pruned obstructed directions on lambda_chain and lambda_stealth."""
        u_obs: Monomial = (0, 0, 2, 0, 2, 2)
        chain_res = self.prove_no_lam1_preserves_kernel_along_u(self.jet.LAM_CHAIN, u_obs)
        stealth_res = self.prove_no_lam1_preserves_kernel_along_u(self.jet.LAM_STEALTH, u_obs)

        return {
            "obstructed_witness_u": u_obs,
            "lambda_chain": chain_res,
            "lambda_stealth": stealth_res,
            "both_provably_unliftable_in_R12": (
                chain_res["no_lam1_in_R12_preserves_kernel"]
                and stealth_res["no_lam1_in_R12_preserves_kernel"]
            ),
        }


# ==============================================================================
# MODULE 3: GOTZMANN DEFORMATION PERSISTENCE & HONESTY BOUNDARY AUDIT
# ==============================================================================

class GotzmannDeformationPersistenceAudit:
    """Verifies flat Gotzmann Hilbert growth G_t = 1 vs. disconnected Hodge loci."""

    def __init__(self, ring_jet: Optional[DeformedJacobianRingJet] = None) -> None:
        self.jet = ring_jet if ring_jet is not None else DeformedJacobianRingJet()
        self.verifier = MovingApolarityFlatnessVerifier(self.jet)

    @staticmethod
    def compute_gotzmann_decomposition(hilbert_vector: Sequence[int]) -> Dict[str, Any]:
        """Checks binomial growth H(m) = binom(m + 2, 2) on m = 0..4 (G_t = 1)."""
        binomial_0_to_4 = [(m + 2) * (m + 1) // 2 for m in range(5)]
        matches_binomial_up_to_4 = list(hilbert_vector[:5]) == binomial_0_to_4
        total_dim = sum(hilbert_vector)
        return {
            "hilbert_vector": tuple(hilbert_vector),
            "hilbert_sum": total_dim,
            "binomial_2_plane_0_to_4": tuple(binomial_0_to_4),
            "matches_binomial_up_to_deg4": matches_binomial_up_to_4,
            "gotzmann_constant_Gt": 1 if matches_binomial_up_to_4 else None,
        }

    def audit(
        self,
        quad_report: Dict[str, Any],
        fixed_report: Dict[str, Any],
        obstruction_report: Dict[str, Any],
    ) -> Dict[str, Any]:
        base_hilb = self.compute_gotzmann_decomposition(self.jet.FLAT_HILBERT_VECTOR)
        # Verify deformed quotient ranks at every degree m=1..6 equal H_base(m)
        witness = quad_report["direct_rref_witnesses"][0]
        deformed_hilb_m1_6 = [witness["deformed_ranks"][m] // 2 for m in range(1, 7)]
        deformed_hilb_full = [1] + deformed_hilb_m1_6
        deformed_gotzmann = self.compute_gotzmann_decomposition(deformed_hilb_full)

        assert deformed_gotzmann["hilbert_vector"] == self.jet.FLAT_HILBERT_VECTOR
        assert deformed_gotzmann["hilbert_sum"] == 72
        assert deformed_gotzmann["gotzmann_constant_Gt"] == 1

        all_18_quad_flat = quad_report["full_m1_to_m6_flat_count"] == 18
        all_56_fixed_flat = fixed_report["canonical_fixed_56_flat_count"] == 56
        all_260_plus_54_flat = (
            fixed_report["full_m1_to_m6_flat_with_lam1_zero_count"] == 260
            and fixed_report["one_axis_u_ge_2_flat_with_explicit_lam1_count"] == 54
        )
        assert all_18_quad_flat and all_56_fixed_flat and all_260_plus_54_flat

        return {
            "bridge_id": "S-BRIDGE-DEFORM-CY4",
            "bridge_a_status": "ADVERSARIALLY_BLOCKED_OPEN_BRIDGE",
            "global_hodge_conjecture_status": "OPEN",
            "release_authorized": False,
            "theorem_progress": "UNKNOWN",
            "infinitesimal_macaulay_flatness_verified": True,
            "gotzmann_persistence_gt_1_verified": True,
            "gotzmann_base": base_hilb,
            "gotzmann_deformed_witness": deformed_gotzmann,
            "quadratic_moving_flat_18_of_18": all_18_quad_flat,
            "canonical_fixed_flat_56_of_56": all_56_fixed_flat,
            "total_full_ideal_flat_directions_verified": 260 + 54 + 18,
            "effective_hilbert_degree_bound_known": False,
            "disconnected_hodge_loci_solved": False,
            "obstruction_contrast_verified": obstruction_report["both_provably_unliftable_in_R12"],
            "millennium_boundary_statement": (
                "Infinitesimal Macaulay-Gotzmann flatness (G_t = 1, Hilbert vector "
                "(1, 3, 6, 10, 15, 18, 19), sum 72) holds in Q[t]/(t^2) across all 18 "
                "quadratic moving-plane directions (via lambda_1(u)) and all 56 canonical "
                "fixed-plane directions (260+54+18 = 332 full-ideal-flat directions in "
                "ker(M_Pi)). This establishes formal local apolarity flatness near the "
                "Fermat locus F_0, NOT global algebraicity across disconnected "
                "Noether-Lefschetz Hodge loci Sigma_gamma that do not intersect F_0."
            ),
        }


# ==============================================================================
# MODULE 4: CYCLOTOMIC 2-PLANE WAVEPACKET & NON-NILPOTENT PLANE IDEAL
# ==============================================================================

class CyclotomicPlaneWavepacketEngine:
    """Constructs and certifies the 125-monomial Band-1 geometric 2-plane wavepacket.

    Lambda_{Pi_true} = prod_{k=0}^2 (x_k^4 + x_k^3 x_{k+3} + x_k^2 x_{k+3}^2 + x_k x_{k+3}^3 + x_{k+3}^4)
    Recovers the non-nilpotent plane ideal I_{Pi_true} = (x_0 - x_3, x_1 - x_4, x_2 - x_5)
    with rank vector (3, 6, 10, 15, 18, 19) and Gotzmann constant G = 1.
    """

    def __init__(self, ring_jet: Optional[DeformedJacobianRingJet] = None) -> None:
        self.jet = ring_jet if ring_jet is not None else DeformedJacobianRingJet()
        self.macaulay = self.jet.macaulay
        self.detector = FourierShadowDetector()

    @staticmethod
    def build_cyclotomic_wavepacket() -> Tuple[PolyDict, List[PolyDict]]:
        """Constructs Lambda_{Pi_true} (125 monomials) and generators [x_k - x_{k+3}]."""
        factors: List[PolyDict] = []
        generators: List[PolyDict] = []
        for k in range(3):
            fac: PolyDict = {}
            for a in range(5):
                exp = [0, 0, 0, 0, 0, 0]
                exp[k] = 4 - a
                exp[k + 3] = a
                fac[(exp[0], exp[1], exp[2], exp[3], exp[4], exp[5])] = _one()
            factors.append(fac)

            xk = [0, 0, 0, 0, 0, 0]
            xk[k] = 1
            yk = [0, 0, 0, 0, 0, 0]
            yk[k + 3] = 1
            generators.append(
                {
                    (xk[0], xk[1], xk[2], xk[3], xk[4], xk[5]): _one(),
                    (yk[0], yk[1], yk[2], yk[3], yk[4], yk[5]): Fraction(-1, 1),
                }
            )

        lam_true = poly_mul(poly_mul(factors[0], factors[1]), factors[2])
        assert len(lam_true) == 125
        return lam_true, generators

    def verify_wavepacket_invariants(self) -> Dict[str, Any]:
        """Verifies 125-monomial Band-1 support, telescoping annihilation, & Gotzmann rank vector."""
        lam_true, generators = self.build_cyclotomic_wavepacket()

        band1_count = 0
        pair_sum_4_count = 0
        for mon, coeff in lam_true.items():
            assert coeff == Fraction(1, 1)
            assert sum(mon) == 12 and max(mon) <= 4
            if mon[0] + mon[3] == 4 and mon[1] + mon[4] == 4 and mon[2] + mon[5] == 4:
                pair_sum_4_count += 1
            if self.detector.classify_monomial(mon) == "2-PLANE_PAIRABLE":
                band1_count += 1
        assert pair_sum_4_count == 125
        assert band1_count == 125

        # Telescoping check: (x_k - x_{k+3}) * Lambda_{Pi_true} === 0 mod J(F_0)_{13}
        # and exact unquotiented expansion checks x_k^5 - x_{k+3}^5 divisible
        telescoping_verified = []
        for idx, gk in enumerate(generators):
            prod_raw = poly_mul(gk, lam_true)
            prod_mod = poly_mod_jacobian(prod_raw, self.jet.jac_deg)
            assert not prod_mod, f"Generator {idx} did not annihilate wavepacket mod J(F_0)"
            # Verify every surviving monomial in raw product lies in (x_idx^5, x_{idx+3}^5)
            for mon in prod_raw:
                assert mon[idx] == 5 or mon[idx + 3] == 5
            telescoping_verified.append(f"x_{idx} - x_{idx + 3}")

        # Graded Macaulay ranks m = 1..6 & R^1 annihilator kernel recovery
        ranks_by_deg: List[int] = []
        ann_r1_vecs: List[List[Fraction]] = []
        for deg in self.macaulay.DOMAIN_DEGREES:
            _, nd, rows = self.macaulay.multiplication_sparse_rows(lam_true, deg)
            rk, kb = _sparse_rref_and_nullspace(rows, nd)
            ranks_by_deg.append(rk)
            if deg == 1:
                ann_r1_vecs = kb

        expected_ranks = [3, 6, 10, 15, 18, 19]
        assert ranks_by_deg == expected_ranks
        assert len(ann_r1_vecs) == 3

        # Confirm Ann_{R^1}(Lambda_{Pi_true}) matches span(x_0 - x_3, x_1 - x_4, x_2 - x_5)
        gen_cols = [[_zero()] * 6 for _ in range(3)]
        for k in range(3):
            gen_cols[k][k] = _one()
            gen_cols[k][k + 3] = Fraction(-1, 1)
        gen_span = ExactColumnSpan([[gen_cols[c][r] for c in range(3)] for r in range(6)])
        ann_span = ExactColumnSpan([[ann_r1_vecs[c][r] for c in range(3)] for r in range(6)])
        assert gen_span.rank == 3 and ann_span.rank == 3
        for c in range(3):
            assert gen_span.contains(ann_r1_vecs[c])
            assert ann_span.contains(gen_cols[c])

        # Verify ideal I_{Pi_true} in R^6(F_0) has dim 407 == ker(M^(6))
        b5 = self.macaulay.bases[5]
        b6_idx = self.macaulay.base_indices[6]
        ideal_span_r6 = _SparseTrackedSpan()
        for gk in generators:
            for h in b5:
                ph = poly_mod_jacobian(poly_mul(gk, {h: _one()}), self.jet.jac_deg)
                if ph:
                    ideal_span_r6.add_column((id(gk), h), {b6_idx[m]: v for m, v in ph.items()})
        assert ideal_span_r6.rank == 407

        hilbert_vec = [1] + ranks_by_deg
        gotzmann = GotzmannDeformationPersistenceAudit.compute_gotzmann_decomposition(hilbert_vec)
        assert gotzmann["gotzmann_constant_Gt"] == 1
        assert gotzmann["hilbert_sum"] == 72

        return {
            "monomial_count": len(lam_true),
            "band1_pairable_count": band1_count,
            "pair_sum_4_count": pair_sum_4_count,
            "annihilator_generators": telescoping_verified,
            "ann_R1_dim": len(ann_r1_vecs),
            "ann_R1_exact_plane_ideal_match": True,
            "ideal_deg6_dim": ideal_span_r6.rank,
            "macaulay_rank_vector": tuple(ranks_by_deg),
            "hilbert_vector": tuple(hilbert_vec),
            "hilbert_sum": gotzmann["hilbert_sum"],
            "gotzmann_G": gotzmann["gotzmann_constant_Gt"],
        }


# ==============================================================================
# MODULE 5: JOINT GENERATOR-SHADOW DEFORMATION SOLVER
# ==============================================================================

class JointGeneratorShadowSolver:
    """Solves (g_k(0) + t delta_g_k)(Lambda_0 + t Lambda_1) === 0 mod (J(F_t), t^2).

    Contrasts stationary-generator transport (delta_g_k = 0) against joint
    generator tilting (delta_g_k in R^1(F_0), Lambda_1 in R^{12}(F_0)), demonstrating
    that non-nilpotent Lambda_{Pi_true} unlocks strictly +6 normal directions whereas
    the degenerate nilpotent limit x_0^4 x_1^4 x_2^4 yields +0 gain.
    """

    def __init__(self, ring_jet: Optional[DeformedJacobianRingJet] = None) -> None:
        self.jet = ring_jet if ring_jet is not None else DeformedJacobianRingJet()
        self.macaulay = self.jet.macaulay
        self.wave = CyclotomicPlaneWavepacketEngine(self.jet)

    def _build_spans(
        self,
        lam0: PolyDict,
        generators: Sequence[PolyDict],
    ) -> Tuple[_SparseTrackedSpan, _SparseTrackedSpan]:
        b12 = self.jet.cy.generate_monomial_basis(12)
        b13_idx = self.macaulay.base_indices[13]
        nb13 = len(self.macaulay.bases[13])
        b1 = self.macaulay.bases[1]

        stat_span = _SparseTrackedSpan()
        for idx, alpha in enumerate(b12):
            col: Dict[int, Fraction] = {}
            ap: PolyDict = {alpha: _one()}
            for k, gk in enumerate(generators):
                prod = poly_mod_jacobian(poly_mul(gk, ap), self.jet.jac_deg)
                off = k * nb13
                for mon, val in prod.items():
                    if val != 0:
                        col[off + b13_idx[mon]] = val
            if col:
                stat_span.add_column(("l1", idx), col)

        joint_span = stat_span.copy()
        for k in range(len(generators)):
            for var_mon in b1:
                col = {}
                prod = poly_mod_jacobian(poly_mul({var_mon: _one()}, lam0), self.jet.jac_deg)
                off = k * nb13
                for mon, val in prod.items():
                    if val != 0:
                        col[off + b13_idx[mon]] = val
                if col:
                    joint_span.add_column(("dg", (k, var_mon)), col)
        return stat_span, joint_span

    def _compute_rhs(
        self,
        lam0: PolyDict,
        generators: Sequence[PolyDict],
        u_poly: PolyDict,
    ) -> Dict[int, Fraction]:
        b13_idx = self.macaulay.base_indices[13]
        nb13 = len(self.macaulay.bases[13])
        rhs: Dict[int, Fraction] = {}
        for k, gk in enumerate(generators):
            r0, r1 = self.jet.multiply_dual(gk, {}, lam0, {}, u_poly)
            assert not r0
            off = k * nb13
            for mon, val in r1.items():
                if val != 0:
                    rhs[off + b13_idx[mon]] = -val
        return rhs

    def solve_for_direction(
        self,
        lam0: PolyDict,
        generators: Sequence[PolyDict],
        u_poly: PolyDict,
        spans: Optional[Tuple[_SparseTrackedSpan, _SparseTrackedSpan]] = None,
    ) -> Dict[str, Any]:
        """Solves stationary vs. joint generator-shadow equation for a single u."""
        b12 = self.jet.cy.generate_monomial_basis(12)
        stat_span, joint_span = spans if spans is not None else self._build_spans(lam0, generators)
        rhs = self._compute_rhs(lam0, generators, u_poly)

        ok_stat, _ = stat_span.solve(rhs)
        ok_joint, sol_joint = joint_span.solve(rhs)

        lam1: PolyDict = {}
        delta_g: List[PolyDict] = [{} for _ in generators]
        if ok_joint:
            for key, val in sol_joint.items():
                if val == 0:
                    continue
                if key[0] == "l1":
                    lam1 = poly_add(lam1, {b12[key[1]]: val})
                else:
                    k_idx, var_mon = key[1]
                    delta_g[k_idx] = poly_add(delta_g[k_idx], {var_mon: val})

            # Explicit dual-ring verification across every deformed generator g_k + t delta_g_k
            for k, gk in enumerate(generators):
                r0_chk, r1_chk = self.jet.multiply_dual(gk, delta_g[k], lam0, lam1, u_poly)
                assert not r0_chk and not r1_chk

        return {
            "stationary_solvable": ok_stat,
            "joint_solvable": ok_joint,
            "requires_generator_tilting": (not ok_stat) and ok_joint,
            "lam1": lam1,
            "delta_g": delta_g,
        }

    def run_joint_transport_audit(self) -> Dict[str, Any]:
        """Benchmarks stationary vs. joint transport on Lambda_{Pi_true} vs nilpotent lam_Pi."""
        lam_true, g0_true = self.wave.build_cyclotomic_wavepacket()
        stat_true, joint_true = self._build_spans(lam_true, g0_true)

        # 1. Operator rank expansion on non-nilpotent wavepacket: 1750 -> 1756 (+6)
        assert stat_true.rank == 1750
        assert joint_true.rank == 1756

        # 2. Subspace dimension inside ker(M^{(6)}_{lam_true}) (dim 407)
        _, nd6, r6_true = self.macaulay.multiplication_sparse_rows(lam_true, 6)
        rk6_true, ker6_true = _sparse_rref_and_nullspace(r6_true, nd6)
        assert rk6_true == 19 and len(ker6_true) == 407

        b6 = self.macaulay.bases[6]
        ext_stat_true = stat_true.copy()
        ext_joint_true = joint_true.copy()
        tilting_witnesses: List[Dict[str, Any]] = []

        for idx, vec in enumerate(ker6_true):
            up = {b6[i]: vec[i] for i in range(nd6) if vec[i] != 0}
            rhs = self._compute_rhs(lam_true, g0_true, up)
            if not rhs:
                continue
            ext_stat_true.add_column(("u", idx), rhs)
            ext_joint_true.add_column(("u", idx), rhs)

        dim_stat_true = len(ker6_true) - (ext_stat_true.rank - stat_true.rank)
        dim_joint_true = len(ker6_true) - (ext_joint_true.rank - joint_true.rank)
        assert dim_stat_true == 353
        assert dim_joint_true == 359

        # 3. Verify canonical tilting witnesses (u fails stationary, succeeds jointly with flat m=1..6 ranks)
        witness_monomials: List[Monomial] = [
            (0, 0, 1, 0, 1, 4),
            (0, 0, 1, 1, 0, 4),
            (0, 1, 0, 0, 4, 1),
        ]
        for w_idx, u_mon in enumerate(witness_monomials):
            u_poly: PolyDict = {u_mon: _one()}
            solved = self.solve_for_direction(
                lam_true, g0_true, u_poly, spans=(stat_true, joint_true)
            )
            assert solved["requires_generator_tilting"] is True
            non_zero_dg_slots = [k for k, dgk in enumerate(solved["delta_g"]) if dgk]
            assert len(non_zero_dg_slots) >= 1

            witness_entry: Dict[str, Any] = {
                "u_monomial": u_mon,
                "stationary_solvable": solved["stationary_solvable"],
                "joint_solvable": solved["joint_solvable"],
                "nonzero_delta_g_generators": non_zero_dg_slots,
                "lam1_monomial_count": len(solved["lam1"]),
            }
            if w_idx == 0:
                # Full 2*d_m x 2*d_m sparse RREF flatness check across m=1..6
                ranks_res = self.jet.deformed_hilbert_and_ranks(
                    lam_true, solved["lam1"], u_poly
                )
                assert ranks_res["all_degrees_flat"] is True
                assert ranks_res["deformed_ranks"] == {1: 6, 2: 12, 3: 20, 4: 30, 5: 36, 6: 38}
                witness_entry["full_m1_to_m6_deformed_ranks"] = ranks_res["deformed_ranks"]
                witness_entry["all_degrees_flat"] = ranks_res["all_degrees_flat"]
            tilting_witnesses.append(witness_entry)

        # 4. Nilpotent limit contrast: x_0^4 x_1^4 x_2^4 with g_k = x_k gives ZERO tilting gain
        g0_nil: List[PolyDict] = [
            {tuple(1 if i == k else 0 for i in range(6)): _one()} for k in range(3)
        ]
        stat_nil, joint_nil = self._build_spans(self.jet.LAM_PI, g0_nil)
        assert stat_nil.rank == 1750
        assert joint_nil.rank == 1750

        return {
            "wavepacket_stat_operator_rank": stat_true.rank,
            "wavepacket_joint_operator_rank": joint_true.rank,
            "wavepacket_operator_rank_gain": joint_true.rank - stat_true.rank,
            "wavepacket_ker6_dim": len(ker6_true),
            "wavepacket_stationary_subspace_dim": dim_stat_true,
            "wavepacket_joint_subspace_dim": dim_joint_true,
            "wavepacket_subspace_gain_by_tilting": dim_joint_true - dim_stat_true,
            "wavepacket_remaining_higher_deg_normal_gap": len(ker6_true) - dim_joint_true,
            "nilpotent_stat_operator_rank": stat_nil.rank,
            "nilpotent_joint_operator_rank": joint_nil.rank,
            "nilpotent_tilting_gain": joint_nil.rank - stat_nil.rank,
            "tilting_witnesses": tilting_witnesses,
        }


# ==============================================================================
# UNIFIED EVENT-22 / EVENT-23 ENGINE
# ==============================================================================

class DeformedMacaulayTransportEngine:
    """Unified Event-22 & Event-23 Deformed Macaulay, Wavepacket, & Joint Transport Engine."""

    def __init__(self) -> None:
        self.jet = DeformedJacobianRingJet()
        self.verifier = MovingApolarityFlatnessVerifier(self.jet)
        self.gotzmann = GotzmannDeformationPersistenceAudit(self.jet)
        self.wavepacket = CyclotomicPlaneWavepacketEngine(self.jet)
        self.joint_solver = JointGeneratorShadowSolver(self.jet)

    def run_full_audit(self) -> Dict[str, Any]:
        quad_report = self.verifier.verify_quadratic_moving_plane_directions()
        fixed_report = self.verifier.verify_fixed_ideal_directions()
        obstruction_report = self.verifier.audit_artificial_class_obstructions()
        gotzmann_report = self.gotzmann.audit(
            quad_report, fixed_report, obstruction_report
        )
        wave_report = self.wavepacket.verify_wavepacket_invariants()
        joint_report = self.joint_solver.run_joint_transport_audit()

        return {
            "engine": "DeformedMacaulayTransportEngine",
            "event_id": 23,
            "quadratic_moving_plane_audit": quad_report,
            "fixed_ideal_audit": fixed_report,
            "artificial_obstruction_audit": obstruction_report,
            "gotzmann_persistence_audit": gotzmann_report,
            "cyclotomic_wavepacket_audit": wave_report,
            "joint_generator_transport_audit": joint_report,
            "bridge_a_status": gotzmann_report["bridge_a_status"],
            "global_hodge_conjecture_status": gotzmann_report["global_hodge_conjecture_status"],
            "release_authorized": gotzmann_report["release_authorized"],
        }


def main() -> None:
    engine = DeformedMacaulayTransportEngine()
    res = engine.run_full_audit()
    q = res["quadratic_moving_plane_audit"]
    f = res["fixed_ideal_audit"]
    o = res["artificial_obstruction_audit"]
    g = res["gotzmann_persistence_audit"]
    w = res["cyclotomic_wavepacket_audit"]
    j = res["joint_generator_transport_audit"]
    print("=" * 72)
    print("DEFORMED MACAULAY TRANSPORT & CYCLOTOMIC WAVEPACKET ENGINE (EVENT 23)")
    print("=" * 72)
    print(
        f"[Moving Plane]    18/18 quadratic dirs: static!=0={q['static_xi_lam1_nonzero_count']}/18, "
        f"deformed_cancel={q['deformed_x012_exact_cancellation_count']}/18, "
        f"flat_m1..6={q['full_m1_to_m6_flat_count']}/18"
    )
    print(
        f"[Fixed Ideal]     359/359 diag_u_lam0=0={f['diagonal_u_dot_lam0_vanishes_count']}/359, "
        f"56/56 canonical_flat={f['canonical_fixed_56_flat_count']}/56, "
        f"260_lam1=0 + 54_explicit_lam1 = 314 full-flat"
    )
    print(
        f"[Obstructions]    u={o['obstructed_witness_u']}: "
        f"chain unliftable={o['lambda_chain']['no_lam1_in_R12_preserves_kernel']} "
        f"(rk6: 2*{o['lambda_chain']['base_rank_m6']}={o['lambda_chain']['expected_flat_double_rank_m6']} "
        f"< {o['lambda_chain']['deformed_rank_m6_lam1_zero']}), "
        f"stealth unliftable={o['lambda_stealth']['no_lam1_in_R12_preserves_kernel']} "
        f"(rk6: 2*{o['lambda_stealth']['base_rank_m6']}={o['lambda_stealth']['expected_flat_double_rank_m6']} "
        f"< {o['lambda_stealth']['deformed_rank_m6_lam1_zero']})"
    )
    print(
        f"[Gotzmann]        H={g['gotzmann_deformed_witness']['hilbert_vector']}, "
        f"sum={g['gotzmann_deformed_witness']['hilbert_sum']}, "
        f"G_t={g['gotzmann_deformed_witness']['gotzmann_constant_Gt']}"
    )
    print(
        f"[Wavepacket]      monomials={w['monomial_count']} (Band1={w['band1_pairable_count']}), "
        f"ranks={w['macaulay_rank_vector']}, Ann_R1={w['annihilator_generators']}, G={w['gotzmann_G']}"
    )
    print(
        f"[Joint Transport] op_rank: {j['wavepacket_stat_operator_rank']} -> {j['wavepacket_joint_operator_rank']} "
        f"(+{j['wavepacket_operator_rank_gain']}), ker6_subspace: {j['wavepacket_stationary_subspace_dim']} -> "
        f"{j['wavepacket_joint_subspace_dim']} (+{j['wavepacket_subspace_gain_by_tilting']}), "
        f"nilpotent_gain=+{j['nilpotent_tilting_gain']}, Bridge A={res['bridge_a_status']}, Global={res['global_hodge_conjecture_status']}"
    )


if __name__ == "__main__":
    main()
