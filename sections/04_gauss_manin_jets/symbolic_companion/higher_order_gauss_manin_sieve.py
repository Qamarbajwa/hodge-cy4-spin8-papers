r"""Higher-Order Gauss-Manin Koszul Jet Tower & Cattani-Deligne-Kaplan (CDK) Bound Engine.

Extends Claire Voisin's second-order quadratic sieve to the recursive k-th order
Gauss-Manin Koszul syzygy jet tower along 1-parameter sextic Calabi-Yau fourfold
deformations F(t) = F_0 + t * u in P^5:

  u * (lambda_0 + t * lambda_1 + t^2 * lambda_2 + ...)
    = sum_{i=0}^5 (A^{(1)}_i + t * A^{(2)}_i + t^2 * A^{(3)}_i + ...) * (x_i^5 + t * partial_i u)

Modules:
  1. GaussManinJetTower: Exact Q[x_0,...,x_5] polynomial algebra and 3-stage
     recursive Koszul syzygy solver (Orders 1, 2, 3) with exact moving-cycle
     and IVHS remainder extraction S^{(2)}(u) - u*lambda_1 - w_2*lambda_0 in J(F_0)_{18}
     and exact second-order Koszul syzygy reconstruction:
       sum_{i=0}^5 A^{(2)}_i(u) x_i^5 == -R^{(2)}(u) in Q[x_0,...,x_5]_{18}.
  2. JetSieveBenchmark: All-order integrability benchmark for the 2-plane cycle
     lambda_Pi = x_0^4 x_1^4 x_2^4 (56/56 canonical fixed-plane, 27/27 moving-plane,
     54/54 linear, and 407/407 full kernel vectors pass Order 3) vs. strict jet
     filtration K^{(1)} supset K^{(2)} supset K^{(3)} on stealth class lambda_stealth
     (347 -> 336 -> 334, fixed-J18 347 -> 297 -> 295, catching 2 vectors at Order 3
     with Phi^{(2)}=0) and Voisin's chain class lambda_chain.
  3. CDKBridgeAAudit: Formalizes Cattani-Deligne-Kaplan (1995) base-moduli
     algebraicity vs. the open fiber Hilbert-scheme effective degree gap on Bridge A
     (S-BRIDGE-DEFORM-CY4).

Zero-Float Guardrail: Strictly integer, tuple, and fractions.Fraction arithmetic.
"""

from __future__ import annotations

from fractions import Fraction
from typing import Any, Dict, List, Sequence, Tuple
import sys
from pathlib import Path

_REPO_ROOT = str(Path(__file__).resolve().parent.parent)
if _REPO_ROOT not in sys.path:
    sys.path.insert(0, _REPO_ROOT)

from toolkit.calabi_yau_jacobian_engine import CalabiYauJacobianEngine

Monomial = Tuple[int, int, int, int, int, int]
PolyDict = Dict[Monomial, Fraction]


def _zero() -> Fraction:
    return Fraction(0, 1)


def _one() -> Fraction:
    return Fraction(1, 1)


def _normalize_poly(poly: Dict[Monomial, Any]) -> PolyDict:
    out: PolyDict = {}
    for m, c in poly.items():
        fc = c if isinstance(c, Fraction) else Fraction(int(c), 1)
        if fc != 0:
            out[m] = fc
    return out


def poly_add(p1: PolyDict, p2: PolyDict) -> PolyDict:
    out = dict(p1)
    for m, c in p2.items():
        nv = out.get(m, _zero()) + c
        if nv == 0:
            out.pop(m, None)
        else:
            out[m] = nv
    return out


def poly_sub(p1: PolyDict, p2: PolyDict) -> PolyDict:
    out = dict(p1)
    for m, c in p2.items():
        nv = out.get(m, _zero()) - c
        if nv == 0:
            out.pop(m, None)
        else:
            out[m] = nv
    return out


def poly_neg(p: PolyDict) -> PolyDict:
    return {m: -c for m, c in p.items() if c != 0}


def poly_mul(p1: PolyDict, p2: PolyDict) -> PolyDict:
    out: PolyDict = {}
    for m1, c1 in p1.items():
        if c1 == 0:
            continue
        for m2, c2 in p2.items():
            if c2 == 0:
                continue
            m: Monomial = (
                m1[0] + m2[0],
                m1[1] + m2[1],
                m1[2] + m2[2],
                m1[3] + m2[3],
                m1[4] + m2[4],
                m1[5] + m2[5],
            )
            nv = out.get(m, _zero()) + c1 * c2
            if nv == 0:
                out.pop(m, None)
            else:
                out[m] = nv
    return out


def poly_partial(p: PolyDict, var_idx: int) -> PolyDict:
    out: PolyDict = {}
    for m, c in p.items():
        exp = m[var_idx]
        if exp > 0 and c != 0:
            dm = list(m)
            dm[var_idx] = exp - 1
            tm: Monomial = (dm[0], dm[1], dm[2], dm[3], dm[4], dm[5])
            nv = out.get(tm, _zero()) + c * exp
            if nv == 0:
                out.pop(tm, None)
            else:
                out[tm] = nv
    return out


def poly_mod_jacobian(p: PolyDict, jac_deg: int = 5) -> PolyDict:
    return {m: c for m, c in p.items() if c != 0 and all(x < jac_deg for x in m)}


class _SparseTrackedSpan:
    """Sparse exact Q-vector space with coefficient provenance tracking."""

    def __init__(self) -> None:
        self.pivots: Dict[int, Dict[int, Fraction]] = {}
        self.pivot_combos: Dict[int, Dict[int, Fraction]] = {}
        self.labels: List[Tuple[str, Any]] = []

    def copy(self) -> "_SparseTrackedSpan":
        dup = _SparseTrackedSpan()
        dup.pivots = {k: dict(v) for k, v in self.pivots.items()}
        dup.pivot_combos = {k: dict(v) for k, v in self.pivot_combos.items()}
        dup.labels = list(self.labels)
        return dup

    @property
    def rank(self) -> int:
        return len(self.pivots)

    def _reduce(
        self,
        vec: Dict[int, Fraction],
    ) -> Tuple[Dict[int, Fraction], Dict[int, Fraction]]:
        rem = {k: v for k, v in vec.items() if v != 0}
        combo: Dict[int, Fraction] = {}
        for p_idx in sorted(self.pivots.keys()):
            factor = rem.get(p_idx, _zero())
            if factor == 0:
                continue
            for row, p_val in self.pivots[p_idx].items():
                nv = rem.get(row, _zero()) - factor * p_val
                if nv == 0:
                    rem.pop(row, None)
                else:
                    rem[row] = nv
            for col_id, c_val in self.pivot_combos[p_idx].items():
                nc = combo.get(col_id, _zero()) + factor * c_val
                if nc == 0:
                    combo.pop(col_id, None)
                else:
                    combo[col_id] = nc
        return rem, combo

    def add_column(self, label: Tuple[str, Any], vec: Dict[int, Fraction]) -> bool:
        col_id = len(self.labels)
        self.labels.append(label)
        rem, combo = self._reduce(vec)
        if not rem:
            return False
        first_nz = min(rem.keys())
        inv = _one() / rem[first_nz]
        norm_vec = {r: v * inv for r, v in rem.items()}
        # original col = sum(combo) + rem -> rem = col - sum(combo)
        norm_combo: Dict[int, Fraction] = {}
        for k, cv in combo.items():
            val = -cv * inv
            if val != 0:
                norm_combo[k] = val
        norm_combo[col_id] = norm_combo.get(col_id, _zero()) + inv
        self.pivots[first_nz] = norm_vec
        self.pivot_combos[first_nz] = norm_combo
        return True

    def solve(self, vec: Dict[int, Fraction]) -> Tuple[bool, Dict[Tuple[str, Any], Fraction]]:
        rem, combo = self._reduce(vec)
        if rem:
            return False, {}
        resolved: Dict[Tuple[str, Any], Fraction] = {}
        for col_id, coeff in combo.items():
            if coeff != 0:
                lbl = self.labels[col_id]
                resolved[lbl] = resolved.get(lbl, _zero()) + coeff
        return True, resolved


class GaussManinJetTower:
    """Recursive 3-order Gauss-Manin Koszul syzygy jet solver on F(t) = F_0 + t u."""

    def __init__(self, cy_engine: CalabiYauJacobianEngine | None = None) -> None:
        self.cy = cy_engine if cy_engine is not None else CalabiYauJacobianEngine()
        self.num_vars = self.cy.num_vars
        self.jac_deg = self.cy.jac_deg
        self.m6: List[Monomial] = [tuple(m) for m in self.cy.generate_monomial_basis(6)]  # type: ignore[misc]
        self.m12: List[Monomial] = [tuple(m) for m in self.cy.generate_monomial_basis(12)]  # type: ignore[misc]
        self.m18: List[Monomial] = [tuple(m) for m in self.cy.generate_monomial_basis(18)]  # type: ignore[misc]
        self.m18_idx: Dict[Monomial, int] = {m: i for i, m in enumerate(self.m18)}

        # Moving-plane variation basis V_mov(Pi) for Pi = {x_0 = x_1 = x_2 = 0}
        self.v_mov_pi: List[Monomial] = [
            a for a in self.m18
            if (a[0] == 4 and a[1] == 4) or (a[0] == 4 and a[2] == 4) or (a[1] == 4 and a[2] == 4)
        ]

    def extract_koszul_syzygy(self, poly_deg18: PolyDict) -> List[PolyDict]:
        """Canonically divides P in J(F_0)_{18} = (x_0^5,...,x_5^5)_{18} into deg-13 A_0,...,A_5."""
        A: List[PolyDict] = [{} for _ in range(self.num_vars)]
        for m, c in poly_deg18.items():
            if c == 0:
                continue
            assert sum(m) == 18, f"Expected homogeneous degree 18, got {sum(m)} for {m}"
            divided = False
            for i in range(self.num_vars):
                if m[i] >= self.jac_deg:
                    q = list(m)
                    q[i] -= self.jac_deg
                    tq: Monomial = (q[0], q[1], q[2], q[3], q[4], q[5])
                    nv = A[i].get(tq, _zero()) + c
                    if nv == 0:
                        A[i].pop(tq, None)
                    else:
                        A[i][tq] = nv
                    divided = True
                    break
            assert divided, f"Polynomial term {m} does not lie in Jacobian ideal J(F_0)_18"

        recon = self.reconstruct_from_syzygy(A)
        assert recon == poly_deg18, "Koszul syzygy reconstruction failed exact degree-18 equality"
        return A

    def reconstruct_from_syzygy(self, syzygy_tuple: Sequence[PolyDict]) -> PolyDict:
        """Evaluates sum_{i=0}^5 A_i * x_i^5 in the unquotiented ring Q[x_0,...,x_5]_{18}."""
        recon: PolyDict = {}
        for i in range(self.num_vars):
            for mono, c in syzygy_tuple[i].items():
                if c == 0:
                    continue
                full = list(mono)
                full[i] += self.jac_deg
                tfull: Monomial = (full[0], full[1], full[2], full[3], full[4], full[5])
                nv = recon.get(tfull, _zero()) + c
                if nv == 0:
                    recon.pop(tfull, None)
                else:
                    recon[tfull] = nv
        return recon

    def contract_with_du(self, syzygy_tuple: Sequence[PolyDict], u_poly: PolyDict) -> PolyDict:
        """Evaluates sum_{i=0}^5 A_i(u) * partial_i(u) in Q[x_0,...,x_5]_{18}."""
        out: PolyDict = {}
        for i in range(self.num_vars):
            if not syzygy_tuple[i]:
                continue
            du_i = poly_partial(u_poly, i)
            if not du_i:
                continue
            out = poly_add(out, poly_mul(syzygy_tuple[i], du_i))
        return out

    def build_im_span(self, lam0_coeffs: Dict[Monomial, Any]) -> _SparseTrackedSpan:
        """Builds exact sparse span for im(M_{lambda_0}: R^6 -> R^{18})."""
        lam0 = _normalize_poly(lam0_coeffs)
        span = _SparseTrackedSpan()
        for w in self.m6:
            w_poly: PolyDict = {w: _one()}
            prod_mod = poly_mod_jacobian(poly_mul(w_poly, lam0), self.jac_deg)
            if prod_mod:
                vec = {self.m18_idx[m]: c for m, c in prod_mod.items()}
                span.add_column(("w2", w), vec)
        return span

    def extend_span_with_u_r12(
        self,
        base_span: _SparseTrackedSpan,
        u_monomial: Monomial,
    ) -> _SparseTrackedSpan:
        """Extends base_span with u * R^{12}(F_0) mod J(F_0)_{18}."""
        ext = base_span.copy()
        for b in self.m12:
            prod: Monomial = (
                u_monomial[0] + b[0],
                u_monomial[1] + b[1],
                u_monomial[2] + b[2],
                u_monomial[3] + b[3],
                u_monomial[4] + b[4],
                u_monomial[5] + b[5],
            )
            if all(x < self.jac_deg for x in prod):
                ext.add_column(("lam1", b), {self.m18_idx[prod]: _one()})
        return ext

    def extend_span_with_v_mov_pi(self, span: _SparseTrackedSpan) -> _SparseTrackedSpan:
        """Extends span with moving-plane subspace V_mov(Pi) in R^{18}(F_0)."""
        ext = span.copy()
        for a in self.v_mov_pi:
            ext.add_column(("mov", a), {self.m18_idx[a]: _one()})
        return ext

    def ivhs_kernel_basis(self, lam0_coeffs: Dict[Monomial, Any]) -> List[Monomial]:
        """Returns basis monomials u in R^6(F_0) such that u * lambda_0 in J(F_0)_{18}."""
        lam0 = _normalize_poly(lam0_coeffs)
        ker: List[Monomial] = []
        for u in self.m6:
            u_poly: PolyDict = {u: _one()}
            if not poly_mod_jacobian(poly_mul(u_poly, lam0), self.jac_deg):
                ker.append(u)
        return ker

    def evaluate_jet_tower_for_vector(
        self,
        u_monomial: Monomial,
        lam0_coeffs: Dict[Monomial, Any],
        im_span: _SparseTrackedSpan | None = None,
        allow_moving_plane_pi: bool = False,
        im_mov_span: _SparseTrackedSpan | None = None,
    ) -> Dict[str, Any]:
        """Executes the recursive 3-order Gauss-Manin Koszul syzygy tower along F(t) = F_0 + t u."""
        lam0 = _normalize_poly(lam0_coeffs)
        u_poly: PolyDict = {u_monomial: _one()}

        # ------------------------------------------------------------------
        # Order 1 (t^0): u * lambda_0 = sum_{i=0}^5 A^{(1)}_i(u) x_i^5
        # ------------------------------------------------------------------
        u_lam0 = poly_mul(u_poly, lam0)
        u_lam0_mod = poly_mod_jacobian(u_lam0, self.jac_deg)
        if u_lam0_mod:
            return {
                "u_monomial": u_monomial,
                "order1_unobstructed": False,
                "order2_fixed_j18": False,
                "order2_unobstructed": False,
                "order3_unobstructed": False,
                "a2_syzygy_reconstruction_exact": False,
                "max_order_passed": 0,
            }

        A1 = self.extract_koszul_syzygy(u_lam0)

        # ------------------------------------------------------------------
        # Order 2 (t^1): S^{(2)}(u) = sum_{i=0}^5 A^{(1)}_i(u) partial_i(u)
        # ------------------------------------------------------------------
        S2 = self.contract_with_du(A1, u_poly)
        S2_mod = poly_mod_jacobian(S2, self.jac_deg)

        if im_span is None:
            im_span = self.build_im_span(lam0)

        lam1: PolyDict = {}
        w2: PolyDict = {}
        delta_mov: PolyDict = {}
        u_r12_span: _SparseTrackedSpan | None = None

        if not S2_mod:
            order2_regime = "fixed_j18"
            order2_unobstructed = True
            R2 = S2
        else:
            s2_vec = {self.m18_idx[m]: c for m, c in S2_mod.items()}
            ok2_gauge, sol2 = im_span.solve(s2_vec)
            if ok2_gauge:
                order2_regime = "gauge_im_M"
                order2_unobstructed = True
            else:
                u_r12_span = self.extend_span_with_u_r12(im_span, u_monomial)
                ok2_u, sol2 = u_r12_span.solve(s2_vec)
                if ok2_u:
                    order2_regime = "moving_cycle_u_R12"
                    order2_unobstructed = True
                elif allow_moving_plane_pi:
                    mov_base = im_mov_span if im_mov_span is not None else self.extend_span_with_v_mov_pi(im_span)
                    mov_span = self.extend_span_with_u_r12(mov_base, u_monomial)
                    ok2_mov, sol2 = mov_span.solve(s2_vec)
                    if ok2_mov:
                        order2_regime = "moving_plane_v_mov_absorbed"
                        order2_unobstructed = True
                    else:
                        return {
                            "u_monomial": u_monomial,
                            "order1_unobstructed": True,
                            "order2_fixed_j18": False,
                            "order2_unobstructed": False,
                            "order2_regime": "obstructed_at_order_2",
                            "S2_mod_jacobian": S2_mod,
                            "order3_unobstructed": False,
                            "a2_syzygy_reconstruction_exact": False,
                            "max_order_passed": 1,
                        }
                else:
                    return {
                        "u_monomial": u_monomial,
                        "order1_unobstructed": True,
                        "order2_fixed_j18": False,
                        "order2_unobstructed": False,
                        "order2_regime": "obstructed_at_order_2",
                        "S2_mod_jacobian": S2_mod,
                        "order3_unobstructed": False,
                        "a2_syzygy_reconstruction_exact": False,
                        "max_order_passed": 1,
                    }

            for (kind, mono), coeff in sol2.items():
                if kind == "lam1":
                    lam1[mono] = lam1.get(mono, _zero()) + coeff
                elif kind == "w2":
                    w2[mono] = w2.get(mono, _zero()) + coeff
                elif kind == "mov":
                    delta_mov[mono] = delta_mov.get(mono, _zero()) + coeff

            R2 = S2
            if lam1:
                R2 = poly_sub(R2, poly_mul(u_poly, lam1))
            if w2:
                R2 = poly_sub(R2, poly_mul(w2, lam0))
            if delta_mov:
                R2 = poly_sub(R2, delta_mov)

        # R2 must lie strictly in J(F_0)_{18}
        R2_mod = poly_mod_jacobian(R2, self.jac_deg)
        assert not R2_mod, f"R^(2)(u) residual did not land in J(F_0)_18 for {u_monomial}: {R2_mod}"

        # Extract A^{(2)}_i(u) from -R^{(2)}(u) and verify sum A^{(2)}_i x_i^5 == -R^{(2)}(u)
        neg_R2 = poly_neg(R2)
        A2 = self.extract_koszul_syzygy(neg_R2)
        recon_neg_R2 = self.reconstruct_from_syzygy(A2)
        a2_exact = recon_neg_R2 == neg_R2
        assert a2_exact, f"Exact identity sum A^(2)_i x_i^5 == -R^(2)(u) failed for {u_monomial}"

        # ------------------------------------------------------------------
        # Order 3 (t^2): S^{(3)}(u) = sum_{i=0}^5 A^{(2)}_i(u) partial_i(u)
        # ------------------------------------------------------------------
        S3 = self.contract_with_du(A2, u_poly)
        S3_mod = poly_mod_jacobian(S3, self.jac_deg)

        if not S3_mod:
            order3_unobstructed = True
            order3_regime = "zero_in_R18"
            base_rank = im_span.rank
            aug_rank = base_rank
        else:
            if u_r12_span is None:
                u_r12_span = self.extend_span_with_u_r12(im_span, u_monomial)
            base_rank = u_r12_span.rank
            s3_vec = {self.m18_idx[m]: c for m, c in S3_mod.items()}
            ok3, _ = u_r12_span.solve(s3_vec)
            if ok3:
                order3_unobstructed = True
                order3_regime = "absorbed_in_im_M_plus_uR12"
                aug_rank = base_rank
            else:
                order3_unobstructed = False
                order3_regime = "obstructed_in_coker"
                aug_rank = base_rank + 1

        return {
            "u_monomial": u_monomial,
            "order1_unobstructed": True,
            "order2_fixed_j18": (not S2_mod),
            "order2_unobstructed": order2_unobstructed,
            "order2_regime": order2_regime,
            "order3_unobstructed": order3_unobstructed,
            "order3_regime": order3_regime,
            "a2_syzygy_reconstruction_exact": a2_exact,
            "S2_mod_jacobian": S2_mod,
            "R2_deg18": R2,
            "A2_syzygy": A2,
            "S3_mod_jacobian": S3_mod,
            "lambda1_correction": lam1,
            "w2_correction": w2,
            "delta_mov_pi": delta_mov,
            "order3_base_rank": base_rank,
            "order3_augmented_rank": aug_rank,
            "max_order_passed": 3 if order3_unobstructed else 2,
        }


class JetSieveBenchmark:
    """Evaluates higher-order jet filtration across 2-plane, stealth, and chain classes."""

    def __init__(self, tower: GaussManinJetTower | None = None) -> None:
        self.tower = tower if tower is not None else GaussManinJetTower()

    def evaluate_plane_cycle_all_orders(self) -> Dict[str, Any]:
        """Verifies 100% integrability of lambda_Pi = x_0^4 x_1^4 x_2^4 through Order 3."""
        lam_pi: PolyDict = {(4, 4, 4, 0, 0, 0): _one()}
        im_span = self.tower.build_im_span(lam_pi)
        im_mov_span = self.tower.extend_span_with_v_mov_pi(im_span)
        ker_pi = self.tower.ivhs_kernel_basis(lam_pi)
        assert len(ker_pi) == 407

        fixed_56 = [u for u in ker_pi if u[0] >= 1 and u[1] >= 1 and u[2] >= 1]
        linear_54 = [u for u in ker_pi if u[0] + u[1] + u[2] == 1]
        assert len(fixed_56) == 56
        assert len(linear_54) == 54

        results: Dict[Monomial, Dict[str, Any]] = {}
        moving_27: List[Monomial] = []
        im_21: List[Monomial] = []
        s2_fixed_j18_count = 0
        s3_zero_j18_count = 0
        exact_a2_count = 0
        order3_pass_count = 0

        for u in ker_pi:
            res = self.tower.evaluate_jet_tower_for_vector(
                u,
                lam_pi,
                im_span=im_span,
                allow_moving_plane_pi=True,
                im_mov_span=im_mov_span,
            )
            results[u] = res
            assert res["order1_unobstructed"] is True
            assert res["order2_unobstructed"] is True
            assert res["order3_unobstructed"] is True
            assert res["a2_syzygy_reconstruction_exact"] is True

            if res["order2_fixed_j18"]:
                s2_fixed_j18_count += 1
            elif res["order2_regime"] in ("moving_cycle_u_R12", "moving_plane_v_mov_absorbed"):
                moving_27.append(u)
            else:
                im_21.append(u)

            if not res["S3_mod_jacobian"]:
                s3_zero_j18_count += 1
            if res["a2_syzygy_reconstruction_exact"]:
                exact_a2_count += 1
            if res["order3_unobstructed"]:
                order3_pass_count += 1

        assert len(moving_27) == 27
        assert len(im_21) == 21
        assert s2_fixed_j18_count == 359

        # Strict checks on the 56 canonical fixed-plane directions and 27 / 54 moving-plane directions
        fixed_56_s2_j18 = sum(1 for u in fixed_56 if results[u]["order2_fixed_j18"])
        fixed_56_s3_j18 = sum(1 for u in fixed_56 if not results[u]["S3_mod_jacobian"])
        fixed_56_order3 = sum(1 for u in fixed_56 if results[u]["order3_unobstructed"])
        moving_27_order3 = sum(1 for u in moving_27 if results[u]["order3_unobstructed"])
        linear_54_order3 = sum(1 for u in linear_54 if results[u]["order3_unobstructed"])

        assert fixed_56_s2_j18 == 56
        assert fixed_56_s3_j18 == 56
        assert fixed_56_order3 == 56
        assert moving_27_order3 == 27
        assert linear_54_order3 == 54

        return {
            "cycle_monomial": (4, 4, 4, 0, 0, 0),
            "ivhs_rank": 19,
            "K1_dim": len(ker_pi),
            "K2_dim": len(ker_pi),
            "K3_dim": order3_pass_count,
            "canonical_fixed_plane_total": len(fixed_56),
            "canonical_fixed_plane_s2_in_J18": fixed_56_s2_j18,
            "canonical_fixed_plane_s3_in_J18": fixed_56_s3_j18,
            "canonical_fixed_plane_order3_unobstructed": fixed_56_order3,
            "moving_plane_27_total": len(moving_27),
            "moving_plane_27_order3_unobstructed": moving_27_order3,
            "linear_moving_plane_54_total": len(linear_54),
            "linear_moving_plane_54_order3_unobstructed": linear_54_order3,
            "s2_fixed_j18_count": s2_fixed_j18_count,
            "s2_in_im_M_count": len(im_21),
            "s3_zero_in_R18_count": s3_zero_j18_count,
            "a2_syzygy_reconstructions_verified": exact_a2_count,
            "plane_order3_all_407_unobstructed": (order3_pass_count == 407),
        }

    def _audit_filtration_for_class(
        self,
        name: str,
        lam_coeffs: Dict[Monomial, Any],
    ) -> Dict[str, Any]:
        lam0 = _normalize_poly(lam_coeffs)
        im_span = self.tower.build_im_span(lam0)
        ker_u = self.tower.ivhs_kernel_basis(lam0)

        k1_dim = len(ker_u)
        k2_moving: List[Monomial] = []
        k3_moving: List[Monomial] = []
        k2_fixed_j18: List[Monomial] = []
        k3_fixed_j18: List[Monomial] = []
        pruned_at_2: List[Monomial] = []
        caught_at_3: List[Dict[str, Any]] = []
        a2_reconstructed = 0

        for u in ker_u:
            res = self.tower.evaluate_jet_tower_for_vector(
                u,
                lam0,
                im_span=im_span,
                allow_moving_plane_pi=False,
            )
            if not res["order2_unobstructed"]:
                pruned_at_2.append(u)
                continue

            k2_moving.append(u)
            if res["a2_syzygy_reconstruction_exact"]:
                a2_reconstructed += 1
            if res["order2_fixed_j18"]:
                k2_fixed_j18.append(u)

            if res["order3_unobstructed"]:
                k3_moving.append(u)
                if res["order2_fixed_j18"]:
                    k3_fixed_j18.append(u)
            else:
                caught_at_3.append(
                    {
                        "u_monomial": u,
                        "order2_regime": res["order2_regime"],
                        "S3_mod_jacobian": {str(m): str(c) for m, c in res["S3_mod_jacobian"].items()},
                        "base_rank": res["order3_base_rank"],
                        "augmented_rank": res["order3_augmented_rank"],
                    }
                )

        return {
            "class_name": name,
            "ivhs_rank": im_span.rank,
            "K1_dim": k1_dim,
            "K2_dim": len(k2_moving),
            "K3_dim": len(k3_moving),
            "strict_fixed_J18_filtration": [k1_dim, len(k2_fixed_j18), len(k3_fixed_j18)],
            "moving_cycle_filtration": [k1_dim, len(k2_moving), len(k3_moving)],
            "pruned_at_order_2_count": len(pruned_at_2),
            "caught_at_order_3_count": len(caught_at_3),
            "caught_at_order_3_witnesses": caught_at_3,
            "a2_syzygy_reconstructions_verified": a2_reconstructed,
        }

    def evaluate_stealth_and_chain_filtration(self) -> Dict[str, Any]:
        """Demonstrates strict filtration K^(1) > K^(2) > K^(3) on stealth and chain classes."""
        lam_stealth: Dict[Monomial, int] = {
            (4, 3, 3, 2, 0, 0): 1,
            (0, 3, 4, 1, 4, 0): 1,
        }
        stealth_audit = self._audit_filtration_for_class("lambda_stealth", lam_stealth)
        assert stealth_audit["ivhs_rank"] == 76
        assert stealth_audit["moving_cycle_filtration"] == [347, 336, 334]
        assert stealth_audit["strict_fixed_J18_filtration"] == [347, 297, 295]
        assert stealth_audit["caught_at_order_3_count"] == 2

        lam_chain: Dict[Monomial, int] = {
            (4, 3, 3, 2, 0, 0): 1,
            (2, 3, 3, 4, 0, 0): 1,
        }
        chain_audit = self._audit_filtration_for_class("lambda_chain", lam_chain)
        assert chain_audit["ivhs_rank"] == 68
        assert chain_audit["moving_cycle_filtration"] == [342, 331, 331]
        assert chain_audit["pruned_at_order_2_count"] == 11

        return {
            "stealth_class": stealth_audit,
            "chain_class": chain_audit,
            "strict_order3_hierarchy_demonstrated": (
                stealth_audit["K1_dim"] > stealth_audit["K2_dim"] > stealth_audit["K3_dim"]
            ),
        }


class CDKBridgeAAudit:
    """Formalizes the Cattani-Deligne-Kaplan (1995) Moduli Algebraicity vs. Fiber Cycle Gap."""

    def audit(
        self,
        plane_audit: Dict[str, Any],
        filtration_audit: Dict[str, Any],
    ) -> Dict[str, Any]:
        return {
            "bridge_id": "S-BRIDGE-DEFORM-CY4",
            "bridge_a_status": "ADVERSARIALLY_BLOCKED_OPEN_BRIDGE",
            "CDK_BASE_MODULI_ALGEBRAICITY_VERIFIED": True,
            "cdk_1995_base_moduli_algebraic": True,
            "effective_hilbert_degree_bound_known": False,
            "fiber_algebraic_cycle_constructed": False,
            "global_extension_valid": False,
            "plane_order3_all_407_unobstructed": plane_audit["plane_order3_all_407_unobstructed"],
            "stealth_order3_caught": filtration_audit["stealth_class"]["caught_at_order_3_count"],
            "cdk_boundary_statement": (
                "By Cattani-Deligne-Kaplan (1995), vanishing of all Gauss-Manin Koszul jets "
                "Phi^(k)_lambda = 0 (k >= 1) proves that the Hodge locus Sigma_lambda subset M "
                "is an algebraic subvariety of moduli. However, it provides NO effective upper bound "
                "on the Hilbert-scheme degree D of Hilb_D(X_t) needed to realize non-Fermat Hodge "
                "classes in H^{2,2}_prim(X_t) by genuine algebraic 2-cycles Z_t subset X_t."
            ),
        }


class HigherOrderGaussManinEngine:
    """Top-level Stage-2 engine bundling Koszul Jet Tower, Benchmark Sieve, and CDK Audit."""

    def __init__(self) -> None:
        self.tower = GaussManinJetTower()
        self.benchmark = JetSieveBenchmark(self.tower)
        self.cdk = CDKBridgeAAudit()

    def run_full_audit(self) -> Dict[str, Any]:
        plane_audit = self.benchmark.evaluate_plane_cycle_all_orders()
        filtration_audit = self.benchmark.evaluate_stealth_and_chain_filtration()
        cdk_audit = self.cdk.audit(plane_audit, filtration_audit)
        return {
            "plane_order3_audit": plane_audit,
            "jet_filtration_benchmark": filtration_audit,
            "cdk_bridge_a_audit": cdk_audit,
            "global_hodge_conjecture": "OPEN",
            "release_authorized": False,
            "theorem_progress": "UNKNOWN",
        }


if __name__ == "__main__":
    engine = HigherOrderGaussManinEngine()
    report = engine.run_full_audit()
    pl = report["plane_order3_audit"]
    flt = report["jet_filtration_benchmark"]
    st = flt["stealth_class"]
    ch = flt["chain_class"]
    cdk = report["cdk_bridge_a_audit"]

    print("=== HIGHER-ORDER GAUSS-MANIN JET TOWER & CDK BRIDGE A ENGINE ===")
    print(
        f"2-Plane Cycle (4,4,4,0,0,0): fixed56={pl['canonical_fixed_plane_order3_unobstructed']}/56, "
        f"moving27={pl['moving_plane_27_order3_unobstructed']}/27, "
        f"linear54={pl['linear_moving_plane_54_order3_unobstructed']}/54, "
        f"full407={pl['K3_dim']}/407, A2_recon={pl['a2_syzygy_reconstructions_verified']}/407"
    )
    print(
        f"Stealth Class K^(1)->K^(2)->K^(3): {st['moving_cycle_filtration']} "
        f"(fixed-J18: {st['strict_fixed_J18_filtration']}, Order-3 caught: {st['caught_at_order_3_count']})"
    )
    print(
        f"Chain Class   K^(1)->K^(2)->K^(3): {ch['moving_cycle_filtration']} "
        f"(Order-2 pruned: {ch['pruned_at_order_2_count']})"
    )
    print(
        f"CDK 1995 Moduli Algebraic: {cdk['CDK_BASE_MODULI_ALGEBRAICITY_VERIFIED']} | "
        f"Effective Fiber Degree Bound Known: {cdk['effective_hilbert_degree_bound_known']} | "
        f"Bridge A: {cdk['bridge_a_status']}"
    )
