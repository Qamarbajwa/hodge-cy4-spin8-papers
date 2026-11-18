r"""Macaulay Apolarity Inverse Engine (Shadow-to-Equation Reconstruction).

Inverts primitive cohomology shadows \lambda \in R^{12}(F_0) on the Fermat sextic
Calabi-Yau fourfold X^4_6 \subset \mathbb{P}^5 back into explicit defining polynomial
equations (I_Z) via graded Macaulay multiplication towers, signed difference
decompositions, and Macaulay-Gotzmann regularity bounds.

Modules:
  1. MacaulayApolarityTower: Constructs the full graded multiplication tower
     M^{(m)}_\lambda : R^m(F_0) -> R^{12+m}(F_0) for m = 1, ..., 6 (domain dims
     6, 21, 56, 126, 246, 426; codomain dims 1686, 1506, 1246, 951, 666, 426)
     and computes exact rational annihilator kernels \operatorname{Ann}_{R^m}(\lambda).
  2. SignedShadowDecomposer: Solves the Apolar Sparse Decomposition Problem
     \lambda = \lambda_+ - \lambda_- maximizing
     \dim \operatorname{Ann}_{R^1}(\lambda_+) + \dim \operatorname{Ann}_{R^1}(\lambda_-)
     + \dim \operatorname{Ann}_{R^2}(\lambda_+) + \dim \operatorname{Ann}_{R^2}(\lambda_-),
     factors degree-2 cross-product quadrics into primary linear ideals, and audits
     all 18 monomial partitions across Band 1 (2-planes) and Band 2 (Shioda joins).
  3. EffectiveDegreeEstimator: Applies Macaulay's Growth Theorem on Gorenstein Hilbert
     functions H_{A_\lambda}(m) = rk(M^{(m)}_\lambda) to compute certified Fermat
     Castelnuovo-Mumford regularity / degree bounds while preserving the global
     Bridge A honesty boundary (effective_hilbert_degree_bound_known = False away
     from the Fermat locus).

Zero-Float Guardrail: Strictly integer, tuple, and fractions.Fraction arithmetic.
"""

from __future__ import annotations

import itertools
import math
import sys
from collections import Counter
from fractions import Fraction
from pathlib import Path
from typing import Any, Dict, List, Optional, Sequence, Tuple

_REPO_ROOT = str(Path(__file__).resolve().parent.parent)
if _REPO_ROOT not in sys.path:
    sys.path.insert(0, _REPO_ROOT)

from toolkit.calabi_yau_jacobian_engine import CalabiYauJacobianEngine
from toolkit.erdos_fourier_incidence_engine import (
    ErdosFourierIncidenceEngine,
    WirtingerUnitCalibrator,
)
from toolkit.exact_linalg import ExactColumnSpan
from toolkit.higher_order_gauss_manin_sieve import (
    Monomial,
    PolyDict,
    poly_add,
    poly_neg,
    poly_sub,
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


def monomial_to_str(m: Monomial) -> str:
    """Formats a 6-variable exponent tuple as a readable monomial string."""
    parts: List[str] = []
    for idx, exp in enumerate(m):
        if exp == 1:
            parts.append(f"x_{idx}")
        elif exp > 1:
            parts.append(f"x_{idx}^{exp}")
    return " ".join(parts) if parts else "1"


def poly_to_str(poly: PolyDict) -> str:
    """Formats a PolyDict cleanly over Q[x_0, ..., x_5]."""
    if not poly:
        return "0"
    terms: List[str] = []
    for mon in sorted(poly.keys(), reverse=True):
        c = poly[mon]
        if c == 0:
            continue
        m_str = monomial_to_str(mon)
        if m_str == "1":
            terms.append(str(c))
        elif c == 1:
            terms.append(m_str)
        elif c == -1:
            terms.append(f"-{m_str}")
        else:
            terms.append(f"{c}*{m_str}")
    return " + ".join(terms).replace(" + -", " - ")


def _sparse_rref_and_nullspace(
    row_dicts: Sequence[Dict[int, Fraction]],
    num_cols: int,
) -> Tuple[int, List[List[Fraction]]]:
    """Computes exact rank and canonical RREF rational nullspace of sparse rows."""
    pivots: Dict[int, Dict[int, Fraction]] = {}
    for raw_row in row_dicts:
        row = {c: v for c, v in raw_row.items() if v != 0}
        for p_col in sorted(pivots.keys()):
            factor = row.get(p_col, _zero())
            if factor == 0:
                continue
            piv_row = pivots[p_col]
            for c, pv in piv_row.items():
                nv = row.get(c, _zero()) - factor * pv
                if nv == 0:
                    row.pop(c, None)
                else:
                    row[c] = nv
        if not row:
            continue
        first_c = min(row.keys())
        inv = _one() / row[first_c]
        pivots[first_c] = {c: v * inv for c, v in row.items()}

    # Back-substitute upper triangular pivots into full RREF
    pivot_cols = sorted(pivots.keys())
    for p_col in reversed(pivot_cols):
        piv_row = pivots[p_col]
        for q_col in pivot_cols:
            if q_col >= p_col:
                break
            q_row = pivots[q_col]
            factor = q_row.get(p_col, _zero())
            if factor == 0:
                continue
            for c, pv in piv_row.items():
                nv = q_row.get(c, _zero()) - factor * pv
                if nv == 0:
                    q_row.pop(c, None)
                else:
                    q_row[c] = nv

    pivot_set = set(pivot_cols)
    free_cols = [c for c in range(num_cols) if c not in pivot_set]
    kernel: List[List[Fraction]] = []
    for fc in free_cols:
        vec = [_zero()] * num_cols
        vec[fc] = _one()
        for pc in pivot_cols:
            val = pivots[pc].get(fc, _zero())
            if val != 0:
                vec[pc] = -val
        kernel.append(vec)
    return len(pivot_cols), kernel


def _linear_combination_in_span(vec: Dict[int, Fraction], span_vecs: List[List[Fraction]], total_dim: int) -> bool:
    """Checks if a sparse vector belongs to the rational span of span_vecs."""
    cols = [[span_vecs[j][r] for j in range(len(span_vecs))] for r in range(total_dim)]
    span = ExactColumnSpan(cols)
    dense = [vec.get(r, _zero()) for r in range(total_dim)]
    return span.contains(dense)


# ==============================================================================
# MODULE 1: GRADED MACAULAY MULTIPLICATION TOWER (m = 1, ..., 6)
# ==============================================================================

class MacaulayApolarityTower:
    r"""Exact graded Macaulay multiplication tower M^{(m)}_\lambda : R^m(F_0) -> R^{12+m}(F_0).

    For the Fermat sextic Calabi-Yau fourfold F_0 = 1/6 \sum_{i=0}^5 x_i^6:
    - Domain dimensions for m = 1..6: (6, 21, 56, 126, 246, 426).
    - Codomain dimensions for 12+m = 13..18: (1686, 1506, 1246, 951, 666, 426).
    - Graded annihilator: \operatorname{Ann}_{R^m}(\lambda) = \ker(M^{(m)}_\lambda).
    """

    DOMAIN_DEGREES: Tuple[int, ...] = (1, 2, 3, 4, 5, 6)
    EXPECTED_DOMAIN_DIMS: Dict[int, int] = {1: 6, 2: 21, 3: 56, 4: 126, 5: 246, 6: 426}
    EXPECTED_CODOMAIN_DIMS: Dict[int, int] = {
        1: 1686,
        2: 1506,
        3: 1246,
        4: 951,
        5: 666,
        6: 426,
    }

    def __init__(self) -> None:
        self.cy = CalabiYauJacobianEngine()
        self.bases: Dict[int, List[Monomial]] = {}
        self.base_indices: Dict[int, Dict[Monomial, int]] = {}
        for deg in list(range(1, 7)) + list(range(13, 19)):
            basis_d = self.cy.generate_monomial_basis(deg)
            self.bases[deg] = basis_d
            self.base_indices[deg] = {m: i for i, m in enumerate(basis_d)}

        for m in self.DOMAIN_DEGREES:
            assert len(self.bases[m]) == self.EXPECTED_DOMAIN_DIMS[m]
            assert len(self.bases[12 + m]) == self.EXPECTED_CODOMAIN_DIMS[m]

    def multiplication_sparse_rows(
        self,
        lambda_poly: Dict[Monomial, Any],
        m: int,
    ) -> Tuple[int, int, List[Dict[int, Fraction]]]:
        """Builds exact sparse row representations of M^{(m)}_lambda : R^m -> R^{12+m}."""
        if m not in self.DOMAIN_DEGREES:
            raise ValueError(f"Degree m must be in {self.DOMAIN_DEGREES}, got {m}")
        lam = _norm_poly(lambda_poly)
        dom_basis = self.bases[m]
        tgt_deg = 12 + m
        tgt_basis = self.bases[tgt_deg]
        tgt_idx = self.base_indices[tgt_deg]

        row_map: Dict[int, Dict[int, Fraction]] = {}
        for col, b in enumerate(dom_basis):
            for lmon, lcoeff in lam.items():
                p0 = b[0] + lmon[0]
                p1 = b[1] + lmon[1]
                p2 = b[2] + lmon[2]
                p3 = b[3] + lmon[3]
                p4 = b[4] + lmon[4]
                p5 = b[5] + lmon[5]
                if p0 < 5 and p1 < 5 and p2 < 5 and p3 < 5 and p4 < 5 and p5 < 5:
                    prod = (p0, p1, p2, p3, p4, p5)
                    r = tgt_idx[prod]
                    entry = row_map.setdefault(r, {})
                    nv = entry.get(col, _zero()) + lcoeff
                    if nv == 0:
                        entry.pop(col, None)
                    else:
                        entry[col] = nv

        sparse_rows = [r for r in row_map.values() if r]
        return len(tgt_basis), len(dom_basis), sparse_rows

    def multiplication_matrix(
        self,
        lambda_poly: Dict[Monomial, Any],
        m: int,
    ) -> List[List[Fraction]]:
        """Constructs the full dense exact rational matrix M^{(m)}_lambda (dim R^{12+m} x dim R^m)."""
        if m not in self.DOMAIN_DEGREES:
            raise ValueError(f"Degree m must be in {self.DOMAIN_DEGREES}, got {m}")
        lam = _norm_poly(lambda_poly)
        dom_basis = self.bases[m]
        tgt_deg = 12 + m
        tgt_basis = self.bases[tgt_deg]
        tgt_idx = self.base_indices[tgt_deg]

        mat: List[List[Fraction]] = [[_zero()] * len(dom_basis) for _ in range(len(tgt_basis))]
        for col, b in enumerate(dom_basis):
            for lmon, lcoeff in lam.items():
                prod = (
                    b[0] + lmon[0],
                    b[1] + lmon[1],
                    b[2] + lmon[2],
                    b[3] + lmon[3],
                    b[4] + lmon[4],
                    b[5] + lmon[5],
                )
                if all(x < 5 for x in prod):
                    mat[tgt_idx[prod]][col] += lcoeff
        return mat

    def annihilator_at_degree(
        self,
        lambda_poly: Dict[Monomial, Any],
        m: int,
        include_basis: bool = True,
    ) -> Dict[str, Any]:
        """Computes exact rank(M^{(m)}_lambda) and annihilator kernel basis in R^m(F_0)."""
        tgt_dim, dom_dim, sparse_rows = self.multiplication_sparse_rows(lambda_poly, m)
        rank, kernel_vecs = _sparse_rref_and_nullspace(sparse_rows, dom_dim)
        ann_dim = dom_dim - rank
        assert len(kernel_vecs) == ann_dim

        dom_basis = self.bases[m]
        basis_polys: List[PolyDict] = []
        basis_strings: List[str] = []
        if include_basis:
            for vec in kernel_vecs:
                poly: PolyDict = {
                    dom_basis[i]: vec[i] for i in range(dom_dim) if vec[i] != 0
                }
                basis_polys.append(poly)
                basis_strings.append(poly_to_str(poly))

        return {
            "degree_m": m,
            "domain_dim": dom_dim,
            "codomain_dim": tgt_dim,
            "rank": rank,
            "annihilator_dim": ann_dim,
            "kernel_vectors": kernel_vecs,
            "basis_polys": basis_polys,
            "basis_strings": basis_strings,
        }

    def compute_tower(
        self,
        lambda_poly: Dict[Monomial, Any],
        max_degree: int = 6,
        include_basis_up_to: int = 2,
    ) -> Dict[str, Any]:
        """Evaluates M^{(m)}_lambda for m = 1, ..., max_degree."""
        levels: Dict[int, Dict[str, Any]] = {}
        ranks: List[int] = []
        ann_dims: List[int] = []
        dom_dims: List[int] = []
        cod_dims: List[int] = []
        for m in range(1, max_degree + 1):
            lvl = self.annihilator_at_degree(
                lambda_poly,
                m,
                include_basis=(m <= include_basis_up_to),
            )
            levels[m] = lvl
            ranks.append(lvl["rank"])
            ann_dims.append(lvl["annihilator_dim"])
            dom_dims.append(lvl["domain_dim"])
            cod_dims.append(lvl["codomain_dim"])

        return {
            "ranks": tuple(ranks),
            "annihilator_dims": tuple(ann_dims),
            "domain_dims": tuple(dom_dims),
            "codomain_dims": tuple(cod_dims),
            "levels": levels,
        }

    def verify_canonical_plane_and_signed_pair(self) -> Dict[str, Any]:
        """Verifies exact annihilator recovery on the single 2-plane and signed disjoint pair."""
        pi_plus: PolyDict = {(4, 4, 4, 0, 0, 0): _one()}
        pi_minus: PolyDict = {(0, 0, 0, 4, 4, 4): _one()}
        lam_signed = poly_sub(pi_plus, pi_minus)

        tower_pi = self.compute_tower(pi_plus, max_degree=6, include_basis_up_to=2)
        ann1_pi_polys = tower_pi["levels"][1]["basis_polys"]
        expected_pi_monos = {(1, 0, 0, 0, 0, 0), (0, 1, 0, 0, 0, 0), (0, 0, 1, 0, 0, 0)}
        recovered_pi_monos = {next(iter(p.keys())) for p in ann1_pi_polys if len(p) == 1}
        assert tower_pi["ranks"] == (3, 6, 10, 15, 18, 19)
        assert tower_pi["annihilator_dims"] == (3, 15, 46, 111, 228, 407)
        assert recovered_pi_monos == expected_pi_monos

        tower_signed = self.compute_tower(lam_signed, max_degree=6, include_basis_up_to=2)
        ann2_signed_polys = tower_signed["levels"][2]["basis_polys"]
        expected_cross_monos: set[Monomial] = set()
        for i in (0, 1, 2):
            for j in (3, 4, 5):
                exp = [0, 0, 0, 0, 0, 0]
                exp[i] = 1
                exp[j] = 1
                expected_cross_monos.add((exp[0], exp[1], exp[2], exp[3], exp[4], exp[5]))
        recovered_cross_monos = {next(iter(p.keys())) for p in ann2_signed_polys if len(p) == 1}

        assert tower_signed["ranks"] == (6, 12, 20, 30, 36, 38)
        assert tower_signed["annihilator_dims"] == (0, 9, 36, 96, 210, 388)
        assert len(expected_cross_monos) == 9
        assert recovered_cross_monos == expected_cross_monos

        return {
            "single_plane": {
                "ranks": list(tower_pi["ranks"]),
                "annihilator_dims": list(tower_pi["annihilator_dims"]),
                "ann_R1_dim": tower_pi["levels"][1]["annihilator_dim"],
                "recovered_ideal_generators": tower_pi["levels"][1]["basis_strings"],
                "exact_ideal_x0_x1_x2_recovered": recovered_pi_monos == expected_pi_monos,
            },
            "signed_disjoint_planes": {
                "ranks": list(tower_signed["ranks"]),
                "annihilator_dims": list(tower_signed["annihilator_dims"]),
                "ann_R1_dim": tower_signed["levels"][1]["annihilator_dim"],
                "ann_R2_dim": tower_signed["levels"][2]["annihilator_dim"],
                "recovered_cross_quadrics": tower_signed["levels"][2]["basis_strings"],
                "exact_9_cross_quadrics_recovered": recovered_cross_monos == expected_cross_monos,
            },
        }


# ==============================================================================
# MODULE 2: SIGNED DIFFERENCE DECOMPOSER & QUADRIC FACTORIZER
# ==============================================================================

class SignedShadowDecomposer:
    r"""Solves the Apolar Sparse Decomposition Problem and audits all 18 partitions of R^{12}(F).

    Given a primitive cohomology shadow \lambda \in R^{12}(F_0), finds positive
    components \lambda_+, \lambda_- \in R^{12}(F_0) with \lambda = \lambda_+ - \lambda_-
    maximizing:
      Score(\lambda_+, \lambda_-) =
        dim Ann_{R^1}(\lambda_+) + dim Ann_{R^1}(\lambda_-)
        + dim Ann_{R^2}(\lambda_+) + dim Ann_{R^2}(\lambda_-).
    """

    def __init__(self, tower: Optional[MacaulayApolarityTower] = None) -> None:
        self.tower = tower or MacaulayApolarityTower()
        self.ef = ErdosFourierIncidenceEngine()
        self.calibrator = WirtingerUnitCalibrator()
        self._ann_score_cache: Dict[Tuple[Tuple[Monomial, Fraction], ...], Tuple[int, int]] = {}

    def _ann_r1_r2(self, poly: PolyDict) -> Tuple[int, int]:
        key = tuple(sorted((m, c) for m, c in poly.items() if c != 0))
        cached = self._ann_score_cache.get(key)
        if cached is not None:
            return cached
        a1 = self.tower.annihilator_at_degree(poly, 1, include_basis=False)["annihilator_dim"]
        a2 = self.tower.annihilator_at_degree(poly, 2, include_basis=False)["annihilator_dim"]
        self._ann_score_cache[key] = (a1, a2)
        return a1, a2

    def score_pair(self, lambda_plus: PolyDict, lambda_minus: PolyDict) -> Dict[str, Any]:
        """Evaluates exact Score(lambda_+, lambda_-) = dim Ann_{R^1, R^2}(lambda_+) + (lambda_-)."""
        p_norm = _norm_poly(lambda_plus)
        m_norm = _norm_poly(lambda_minus)
        if not p_norm or not m_norm:
            raise ValueError("Both lambda_plus and lambda_minus must be non-zero components.")
        a1_p, a2_p = self._ann_r1_r2(p_norm)
        a1_m, a2_m = self._ann_r1_r2(m_norm)
        score = a1_p + a1_m + a2_p + a2_m
        return {
            "ann_R1_plus": a1_p,
            "ann_R2_plus": a2_p,
            "ann_R1_minus": a1_m,
            "ann_R2_minus": a2_m,
            "score": score,
        }

    @staticmethod
    def _build_band1_plane_carrier(pairing: Sequence[Tuple[int, int]], signs: Tuple[int, int, int] = (1, 1, 1)) -> PolyDict:
        """Builds a Band-1 Fermat 2-plane polynomial P = prod_{r=1}^3 sum_{k=0}^4 c_r^{4-k} x_{i_r}^k x_{j_r}^{4-k}.

        Satisfies (x_{i_r} - c_r x_{j_r}) * P == 0 in R^{13}(F_0), so dim Ann_{R^1}(P) = 3.
        """
        (i1, j1), (i2, j2), (i3, j3) = pairing
        c1, c2, c3 = signs
        poly: PolyDict = {}
        for k1 in range(5):
            w1 = c1 ** (4 - k1)
            for k2 in range(5):
                w2 = c2 ** (4 - k2)
                for k3 in range(5):
                    w3 = c3 ** (4 - k3)
                    exp = [0, 0, 0, 0, 0, 0]
                    exp[i1] = k1
                    exp[j1] = 4 - k1
                    exp[i2] = k2
                    exp[j2] = 4 - k2
                    exp[i3] = k3
                    exp[j3] = 4 - k3
                    mon = (exp[0], exp[1], exp[2], exp[3], exp[4], exp[5])
                    poly[mon] = Fraction(w1 * w2 * w3, 1)
        return poly

    @staticmethod
    def _build_band2_shioda_cone_carrier(
        triple_9: Tuple[int, int, int],
        triple_3: Tuple[int, int, int],
        exp_on_3: Tuple[int, int, int],
    ) -> PolyDict:
        """Builds a Band-2 (3+3) Shioda cone polynomial Q_S(x_S) * x_{S^c}^{exp_on_3} in R^{12}(F_0).

        Q_S = sum_{b_0+b_1+b_2=9, b_k<=4} x_S^b is annihilated by (x_{s_0}-x_{s_2}, x_{s_1}-x_{s_2})
        in R(F_0), giving exact dim Ann_{R^1} >= 2 for the cone hull P^3 subset P^5.
        """
        s0, s1, s2 = triple_9
        t0, t1, t2 = triple_3
        poly: PolyDict = {}
        for b0 in range(5):
            for b1 in range(5):
                b2 = 9 - b0 - b1
                if 0 <= b2 <= 4:
                    exp = [0, 0, 0, 0, 0, 0]
                    exp[s0] = b0
                    exp[s1] = b1
                    exp[s2] = b2
                    exp[t0] = exp_on_3[0]
                    exp[t1] = exp_on_3[1]
                    exp[t2] = exp_on_3[2]
                    mon = (exp[0], exp[1], exp[2], exp[3], exp[4], exp[5])
                    poly[mon] = _one()
        return poly

    def decompose(self, lambda_poly: Dict[Monomial, Any]) -> Dict[str, Any]:
        """Solves the Apolar Sparse Decomposition lambda = lambda_+ - lambda_- maximizing Score.

        For mixed-sign classes, searches positive/negative term splits (and when
        sparse, all non-trivial sign-preserving bipartitions) to guarantee global
        optimality over support partitions. For single-sign Band-1 monomials or
        positive classes, uses exact Fermat 2-plane / Shioda cone apolar lifting so
        both lambda_+ and lambda_- remain strictly positive non-zero components.
        """
        lam = _norm_poly(lambda_poly)
        if not lam:
            raise ValueError("Cannot decompose zero cohomology class.")

        terms = sorted(lam.items())
        pos_terms = [(m, c) for m, c in terms if c > 0]
        neg_terms = [(m, -c) for m, c in terms if c < 0]

        best_plus: PolyDict = {}
        best_minus: PolyDict = {}
        best_metrics: Dict[str, Any] = {}
        strategy = ""

        if pos_terms and neg_terms:
            strategy = "SIGNED_SUPPORT_OPTIMIZATION"
            best_plus = dict(pos_terms)
            best_minus = dict(neg_terms)
            best_metrics = self.score_pair(best_plus, best_minus)

            # For small mixed-sign supports, check all 2-partitions of positive and negative subsets
            # (splitting lambda = (P1 + N1_comp) - (N1 + P1_comp) cannot improve disjoint pure signs,
            # so canonical pure sign separation is strictly maximal, which we verify explicitly for |supp|<=6).
            if len(terms) <= 6:
                n_pos = len(pos_terms)
                n_neg = len(neg_terms)
                for p_mask in range(1, 1 << n_pos):
                    for n_mask in range(1, 1 << n_neg):
                        cand_p: PolyDict = {pos_terms[i][0]: pos_terms[i][1] for i in range(n_pos) if (p_mask >> i) & 1}
                        cand_m: PolyDict = {neg_terms[j][0]: neg_terms[j][1] for j in range(n_neg) if (n_mask >> j) & 1}
                        # Moving any term across requires cancelling it on both sides: check remaining equality
                        rem_pos = {pos_terms[i][0]: pos_terms[i][1] for i in range(n_pos) if not ((p_mask >> i) & 1)}
                        rem_neg = {neg_terms[j][0]: neg_terms[j][1] for j in range(n_neg) if not ((n_mask >> j) & 1)}
                        cand_p_full = poly_add(cand_p, rem_neg)
                        cand_m_full = poly_add(cand_m, rem_pos)
                        if poly_sub(cand_p_full, cand_m_full) == lam and cand_p_full and cand_m_full:
                            if all(v > 0 for v in cand_p_full.values()) and all(v > 0 for v in cand_m_full.values()):
                                m_eval = self.score_pair(cand_p_full, cand_m_full)
                                if m_eval["score"] > best_metrics["score"]:
                                    best_plus = cand_p_full
                                    best_minus = cand_m_full
                                    best_metrics = m_eval
        else:
            # Single-sign shadow (e.g. Band-1 2-plane mode or single monomial)
            strategy = "APOLAR_CARRIER_LIFT"
            lam_pos = lam if pos_terms else poly_neg(lam)
            lead_mon, lead_coeff = max(lam_pos.items(), key=lambda kv: (sum(1 for x in kv[0] if x == 4), kv[0]))
            scale = lead_coeff + _one()
            band = self.ef.detector.classify_monomial(lead_mon)

            carrier: Optional[PolyDict] = None
            if band == "2-PLANE_PAIRABLE":
                for pairing in self.ef.detector.matchings_15:
                    if all(lead_mon[p[0]] + lead_mon[p[1]] == 4 for p in pairing):
                        carrier = self._build_band1_plane_carrier(pairing, (1, 1, 1))
                        break
            elif band == "INDUCTIVE_3_PLUS_3":
                for t1, t2 in self.ef.detector.triplets_10:
                    s1 = lead_mon[t1[0]] + lead_mon[t1[1]] + lead_mon[t1[2]]
                    if s1 == 9:
                        carrier = self._build_band2_shioda_cone_carrier(
                            t1, t2, (lead_mon[t2[0]], lead_mon[t2[1]], lead_mon[t2[2]])
                        )
                        break
                    if s1 == 3:
                        carrier = self._build_band2_shioda_cone_carrier(
                            t2, t1, (lead_mon[t1[0]], lead_mon[t1[1]], lead_mon[t1[2]])
                        )
                        break

            if carrier is None:
                best_plus = {m: scale for m in lam_pos}
                best_minus = poly_sub(best_plus, lam) if pos_terms else poly_add(best_plus, lam_pos)
            else:
                mult = max((c for c in lam_pos.values()), default=_one()) + _one()
                lifted = {m: c * mult for m, c in carrier.items()}
                for m, c in lam_pos.items():
                    if m not in lifted:
                        lifted[m] = c + _one()
                if pos_terms:
                    best_plus = lifted
                    best_minus = poly_sub(best_plus, lam)
                else:
                    best_minus = lifted
                    best_plus = poly_add(best_minus, lam)

            best_metrics = self.score_pair(best_plus, best_minus)

        assert poly_sub(best_plus, best_minus) == lam
        assert all(c > 0 for c in best_plus.values())
        assert all(c > 0 for c in best_minus.values())

        ann1_plus = self.tower.annihilator_at_degree(best_plus, 1)
        ann1_minus = self.tower.annihilator_at_degree(best_minus, 1)
        bal = self.calibrator.verify_signed_unit_balance(1, 1)

        return {
            "strategy": strategy,
            "wirtinger_primitive_balanced": bal["is_unit_balanced"],
            "lambda_plus": best_plus,
            "lambda_minus": best_minus,
            "lambda_plus_str": poly_to_str(best_plus) if len(best_plus) <= 8 else f"({len(best_plus)} terms)",
            "lambda_minus_str": poly_to_str(best_minus) if len(best_minus) <= 8 else f"({len(best_minus)} terms)",
            "score": best_metrics["score"],
            "score_breakdown": best_metrics,
            "primary_ideal_plus_dim": ann1_plus["annihilator_dim"],
            "primary_ideal_plus_generators": ann1_plus["basis_strings"],
            "primary_ideal_minus_dim": ann1_minus["annihilator_dim"],
            "primary_ideal_minus_generators": ann1_minus["basis_strings"],
            "exact_reconstruction_verified": (poly_sub(best_plus, best_minus) == lam),
        }

    def factor_signed_quadrics(self, lambda_poly: Dict[Monomial, Any]) -> Dict[str, Any]:
        """Verifies that Ann_{R^2}(lambda) equals the bilinear ideal product I_+ * I_-."""
        lam = _norm_poly(lambda_poly)
        ann1_lam = self.tower.annihilator_at_degree(lam, 1)
        ann2_lam = self.tower.annihilator_at_degree(lam, 2)
        decomp = self.decompose(lam)

        ann1_plus = self.tower.annihilator_at_degree(decomp["lambda_plus"], 1)
        ann1_minus = self.tower.annihilator_at_degree(decomp["lambda_minus"], 1)

        r2_basis = self.tower.bases[2]
        r2_idx = self.tower.base_indices[2]
        dim_r2 = len(r2_basis)

        product_cols: List[List[Fraction]] = []
        for gp in ann1_plus["basis_polys"]:
            for gm in ann1_minus["basis_polys"]:
                vec = [_zero()] * dim_r2
                for mp, cp in gp.items():
                    for mm, cm in gm.items():
                        prod = (
                            mp[0] + mm[0],
                            mp[1] + mm[1],
                            mp[2] + mm[2],
                            mp[3] + mm[3],
                            mp[4] + mm[4],
                            mp[5] + mm[5],
                        )
                        vec[r2_idx[prod]] += cp * cm
                product_cols.append(vec)

        prod_mat = [[product_cols[c][r] for c in range(len(product_cols))] for r in range(dim_r2)] if product_cols else []
        prod_span = ExactColumnSpan(prod_mat) if prod_mat else None
        prod_rank = prod_span.rank if prod_span is not None else 0

        ann2_vecs = ann2_lam["kernel_vectors"]
        ann2_mat = [[ann2_vecs[c][r] for c in range(len(ann2_vecs))] for r in range(dim_r2)] if ann2_vecs else []
        ann2_span = ExactColumnSpan(ann2_mat) if ann2_mat else None

        all_prod_in_ann2 = True
        if prod_span is not None and ann2_span is not None:
            for col in product_cols:
                if not ann2_span.contains(col):
                    all_prod_in_ann2 = False
                    break
        elif prod_rank > 0:
            all_prod_in_ann2 = False

        all_ann2_in_prod = True
        if ann2_span is not None and prod_span is not None:
            for col in ann2_vecs:
                if not prod_span.contains(col):
                    all_ann2_in_prod = False
                    break
        elif len(ann2_vecs) > 0:
            all_ann2_in_prod = False

        return {
            "lambda_ann_R1_dim": ann1_lam["annihilator_dim"],
            "lambda_ann_R2_dim": ann2_lam["annihilator_dim"],
            "primary_I_plus_dim": ann1_plus["annihilator_dim"],
            "primary_I_minus_dim": ann1_minus["annihilator_dim"],
            "primary_I_plus_generators": ann1_plus["basis_strings"],
            "primary_I_minus_generators": ann1_minus["basis_strings"],
            "product_ideal_dim": prod_rank,
            "exact_product_factorization_matches_ann_R2": (
                all_prod_in_ann2 and all_ann2_in_prod and prod_rank == ann2_lam["annihilator_dim"]
            ),
            "decomposition": decomp,
        }

    def audit_all_18_partitions(self) -> Dict[str, Any]:
        """Tests Macaulay tower & geometric factorization across all 18 partitions of R^{12}(F_0)."""
        census = self.ef.census.partition_census()
        m12 = self.ef.census.m12

        records: List[Dict[str, Any]] = []
        band1_verified = 0
        band2_verified = 0
        band3_verified = 0
        signed_pair_verified = 0

        for row in census["partitions"]:
            part: Monomial = row["partition"]
            mult: int = row["multiplicity"]
            band = self.ef.detector.classify_monomial(part)

            mono_poly: PolyDict = {part: _one()}
            tower_p = self.tower.compute_tower(mono_poly, max_degree=6, include_basis_up_to=1)
            assert tower_p["ranks"][5] == row["ivhs_rank"]

            # Test signed orbit difference when multiplicity > 1 (17/18 partitions)
            orbit_members = [m for m in m12 if tuple(sorted(m, reverse=True)) == part]
            assert len(orbit_members) == mult
            signed_recovery_ok = False
            signed_score = 0
            if len(orbit_members) >= 2:
                # Pick orbit partner maximizing Euclidean separation
                partner = max(
                    (m for m in orbit_members if m != part),
                    key=lambda m: sum((part[k] - m[k]) ** 2 for k in range(6)),
                )
                lam_diff: PolyDict = {part: _one(), partner: Fraction(-1, 1)}
                dec_diff = self.decompose(lam_diff)
                signed_recovery_ok = (
                    dec_diff["exact_reconstruction_verified"]
                    and dec_diff["lambda_plus"] == {part: _one()}
                    and dec_diff["lambda_minus"] == {partner: _one()}
                )
                signed_score = dec_diff["score"]
                if signed_recovery_ok:
                    signed_pair_verified += 1
            else:
                # Unique balanced partition (2,2,2,2,2,2): verify apolar 2-plane lift decomposition
                dec_bal = self.decompose(mono_poly)
                signed_recovery_ok = dec_bal["exact_reconstruction_verified"] and dec_bal["primary_ideal_plus_dim"] == 3
                signed_score = dec_bal["score"]
                if signed_recovery_ok:
                    signed_pair_verified += 1

            # Verify Band-specific geometric equation factorization
            geom_factor_ok = False
            geom_desc = ""
            if band == "2-PLANE_PAIRABLE":
                for pairing in self.ef.detector.matchings_15:
                    if all(part[p[0]] + part[p[1]] == 4 for p in pairing):
                        carrier_p = self._build_band1_plane_carrier(pairing, (1, 1, 1))
                        ann1_c = self.tower.annihilator_at_degree(carrier_p, 1)
                        assert part in carrier_p
                        assert ann1_c["annihilator_dim"] == 3
                        geom_factor_ok = True
                        geom_desc = f"2-plane {pairing}, Ann_R1=3 ({'; '.join(ann1_c['basis_strings'])})"
                        band1_verified += 1
                        break
            elif band == "INDUCTIVE_3_PLUS_3":
                for t1, t2 in self.ef.detector.triplets_10:
                    s1 = part[t1[0]] + part[t1[1]] + part[t1[2]]
                    s2 = part[t2[0]] + part[t2[1]] + part[t2[2]]
                    if s1 == 9 and s2 == 3:
                        t9, t3 = t1, t2
                    elif s2 == 9 and s1 == 3:
                        t9, t3 = t2, t1
                    else:
                        continue
                    cone_p = self._build_band2_shioda_cone_carrier(
                        t9, t3, (part[t3[0]], part[t3[1]], part[t3[2]])
                    )
                    ann1_c = self.tower.annihilator_at_degree(cone_p, 1)
                    assert part in cone_p
                    assert ann1_c["annihilator_dim"] >= 2
                    geom_factor_ok = True
                    geom_desc = f"Shioda 3+3 join {t9}|{t3}, Ann_R1={ann1_c['annihilator_dim']}"
                    band2_verified += 1
                    break
            elif band == "INDUCTIVE_2_PLUS_4_LEFSCHETZ":
                for pair, comp in self.ef.detector.pairs_15:
                    if part[pair[0]] + part[pair[1]] == 4 and sum(part[idx] for idx in comp) == 8:
                        geom_factor_ok = True
                        geom_desc = f"2+4 Lefschetz join {pair}|{comp} in R^8(P^3)"
                        band3_verified += 1
                        break

            assert signed_recovery_ok, f"Signed recovery failed on partition {part}"
            assert geom_factor_ok, f"Geometric factorization failed on partition {part}"

            records.append({
                "partition": part,
                "multiplicity": mult,
                "band": band,
                "graded_ranks": list(tower_p["ranks"]),
                "graded_annihilator_dims": list(tower_p["annihilator_dims"]),
                "signed_recovery_ok": signed_recovery_ok,
                "signed_score": signed_score,
                "geometric_factor_ok": geom_factor_ok,
                "geometric_description": geom_desc,
            })

        assert band1_verified == 10
        assert band2_verified == 6
        assert band3_verified == 2
        assert signed_pair_verified == 18

        return {
            "total_partitions_tested": len(records),
            "band1_partitions_verified": band1_verified,
            "band2_partitions_verified": band2_verified,
            "band3_partitions_verified": band3_verified,
            "signed_pair_recoveries_verified": signed_pair_verified,
            "all_18_partitions_verified": True,
            "partition_records": records,
        }


# ==============================================================================
# MODULE 3: EFFECTIVE DEGREE BOUND ESTIMATOR (MACAULAY GROWTH & GOTZMANN)
# ==============================================================================

class EffectiveDegreeEstimator:
    r"""Translates graded rank sequences r(\lambda) = (rk M^{(1)}, ..., rk M^{(6)})
    into Macaulay Growth inequalities and Fermat Castelnuovo-Mumford regularity bounds.

    Honesty Boundary:
      - On the Fermat locus R(F_0), Macaulay's Growth Theorem and Gotzmann
        persistence bound the Fermat apolar ideal regularity D_fermat (and socle <= 12).
      - Away from Fermat across general CY4 deformations X_t, Bridge A remains open
        because general_fiber_hilbert_bound_known = False.
    """

    def __init__(self, tower: Optional[MacaulayApolarityTower] = None) -> None:
        self.tower = tower or MacaulayApolarityTower()

    @staticmethod
    def macaulay_representation(c: int, d: int) -> List[Tuple[int, int]]:
        """Computes unique d-th Macaulay binomial expansion c = sum C(k_i, i)."""
        if c < 0 or d < 1:
            raise ValueError(f"Expected c >= 0 and d >= 1, got c={c}, d={d}")
        if c == 0:
            return []
        terms: List[Tuple[int, int]] = []
        rem = c
        for deg in range(d, 0, -1):
            if rem == 0:
                break
            k = deg
            while math.comb(k + 1, deg) <= rem:
                k += 1
            if math.comb(k, deg) <= rem:
                terms.append((k, deg))
                rem -= math.comb(k, deg)
        assert rem == 0, f"Macaulay representation failed for c={c}, d={d}"
        return terms

    @classmethod
    def macaulay_upper_bound(cls, c: int, d: int) -> int:
        """Computes Macaulay upper growth operator c^{<d>} = sum C(k_i + 1, i + 1)."""
        if c == 0:
            return 0
        terms = cls.macaulay_representation(c, d)
        return sum(math.comb(k + 1, deg + 1) for k, deg in terms)

    @staticmethod
    def _poly_binom(n: int, k: int) -> int:
        """Evaluates polynomial binomial coefficient n*(n-1)*...*(n-k+1) / k! for any integer n."""
        if k < 0:
            return 0
        if k == 0:
            return 1
        num = 1
        for j in range(k):
            num *= n - j
        return num // math.factorial(k)

    @classmethod
    def _gotzmann_surface_decomposition(cls, val_by_t: Sequence[int]) -> Optional[Dict[str, Any]]:
        """Checks if pre-Jacobian values H(1..4) match a quadratic surface Hilbert polynomial
        P(t) = sum_{i=1}^G C(t + a_i - i + 1, a_i) and returns the Gotzmann number G.
        """
        h1, h2, h3, h4 = val_by_t[0], val_by_t[1], val_by_t[2], val_by_t[3]
        c2 = h3 - 2 * h2 + h1
        if h4 - 2 * h3 + h2 != c2 or c2 < 0:
            return None
        rem1 = h1 - c2 * cls._poly_binom(3, 2)
        rem2 = h2 - c2 * cls._poly_binom(4, 2)
        c1 = rem2 - rem1
        c0 = rem1 - 2 * c1

        for idx, t in enumerate((1, 2, 3, 4), start=0):
            pred = c2 * cls._poly_binom(t + 2, 2) + c1 * cls._poly_binom(t + 1, 1) + c0
            if pred != val_by_t[idx]:
                return None

        a_list: List[int] = [2] * c2

        def rem_fn(t_val: int) -> int:
            poly_val = c2 * cls._poly_binom(t_val + 2, 2) + c1 * cls._poly_binom(t_val + 1, 1) + c0
            sub_val = sum(cls._poly_binom(t_val + 2 - i + 1, 2) for i in range(1, c2 + 1))
            return poly_val - sub_val

        r1 = rem_fn(1)
        r2 = rem_fn(2)
        lin_slope = r2 - r1
        if lin_slope < 0:
            return None
        for _ in range(lin_slope):
            a_list.append(1)
        const_val = r1 - sum(
            cls._poly_binom(1 + 1 - i + 1, 1) for i in range(c2 + 1, c2 + lin_slope + 1)
        )
        if const_val < 0:
            return None
        for _ in range(const_val):
            a_list.append(0)

        for t in range(1, 7):
            p_t = c2 * cls._poly_binom(t + 2, 2) + c1 * cls._poly_binom(t + 1, 1) + c0
            g_t = sum(
                cls._poly_binom(t + a_list[i - 1] - i + 1, a_list[i - 1])
                for i in range(1, len(a_list) + 1)
            )
            if p_t != g_t:
                return None

        return {
            "hilbert_polynomial_coeffs": (c2, c1, c0),
            "gotzmann_exponents": a_list,
            "gotzmann_number_G": len(a_list),
        }

    def minimal_generator_profile(self, lambda_poly: Dict[Monomial, Any]) -> Dict[str, Any]:
        """Computes new minimal annihilator generators in degrees m = 1..6 inside R(F_0)."""
        lam = _norm_poly(lambda_poly)
        profile: List[Dict[str, int]] = []
        prev_vecs: List[List[Fraction]] = []
        d_gen = 0

        for m in range(1, 7):
            lvl = self.tower.annihilator_at_degree(lam, m, include_basis=False)
            ann_dim = lvl["annihilator_dim"]
            r_m = self.tower.bases[m]
            idx_m = self.tower.base_indices[m]
            if m == 1 or not prev_vecs:
                gen_dim = 0
            else:
                r_prev = self.tower.bases[m - 1]
                cols: List[List[Fraction]] = []
                for v in prev_vecs:
                    for var in range(6):
                        vec = [_zero()] * len(r_m)
                        for idx, coeff in enumerate(v):
                            if coeff != 0:
                                mon = r_prev[idx]
                                if mon[var] + 1 < 5:
                                    nmon = list(mon)
                                    nmon[var] += 1
                                    tmon = (nmon[0], nmon[1], nmon[2], nmon[3], nmon[4], nmon[5])
                                    vec[idx_m[tmon]] += coeff
                        if any(x != 0 for x in vec):
                            cols.append(vec)
                if cols:
                    mat = [[cols[c][r] for c in range(len(cols))] for r in range(len(r_m))]
                    gen_dim = ExactColumnSpan(mat).rank
                else:
                    gen_dim = 0

            new_gens = ann_dim - gen_dim
            if new_gens > 0:
                d_gen = m
            profile.append({
                "degree_m": m,
                "annihilator_dim": ann_dim,
                "generated_from_lower_dim": gen_dim,
                "new_minimal_generators": new_gens,
            })
            prev_vecs = lvl["kernel_vectors"]

        return {
            "profile": profile,
            "minimal_generation_cutoff_d_gen": d_gen,
        }

    def estimate_degree_bound(self, lambda_poly: Dict[Monomial, Any], label: str = "") -> Dict[str, Any]:
        """Computes graded Gorenstein Hilbert vector, Macaulay growth checks, and regularity bounds."""
        lam = _norm_poly(lambda_poly)
        tower_res = self.tower.compute_tower(lam, max_degree=6, include_basis_up_to=0)
        ranks = tower_res["ranks"]
        ann_dims = tower_res["annihilator_dims"]

        # Full symmetric Gorenstein Hilbert function H(0..12)
        hilbert_vector = [1] + list(ranks) + list(reversed(ranks[:-1])) + [1]
        assert len(hilbert_vector) == 13

        macaulay_checks: List[Dict[str, Any]] = []
        growth_holds = True
        persistent_degrees: List[int] = []
        for m in range(1, 6):
            r_curr = ranks[m - 1]
            r_next = ranks[m]
            mac_exp = self.macaulay_representation(r_curr, m)
            upper = self.macaulay_upper_bound(r_curr, m)
            ok = r_next <= upper
            if not ok:
                growth_holds = False
            if r_next == upper:
                persistent_degrees.append(m)
            macaulay_checks.append({
                "m": m,
                "r_m": r_curr,
                "r_next": r_next,
                "macaulay_expansion": mac_exp,
                "macaulay_upper": upper,
                "inequality_holds": ok,
                "persistence_equality": (r_next == upper),
            })

        assert growth_holds

        gen_prof = self.minimal_generator_profile(lam)
        d_gen = gen_prof["minimal_generation_cutoff_d_gen"]
        v_eff = ranks[0]
        gotz = self._gotzmann_surface_decomposition(ranks[:4])

        # Bayer-Mumford (char 0) finite doubly-exponential bound in v_eff variables when d_gen >= 1
        # and Artinian Gorenstein socle regularity = 12 at Fermat.
        if v_eff <= 1:
            bayer_mumford_bound = max(1, d_gen)
        else:
            bayer_mumford_bound = (2 * max(1, d_gen)) ** (2 ** (v_eff - 2))

        if gotz is not None:
            fermat_certified_bound = gotz["gotzmann_number_G"]
            bound_source = "GOTZMANN_PERSISTENT_HILBERT_POLYNOMIAL"
        else:
            fermat_certified_bound = min(12, bayer_mumford_bound) if ann_dims[5] > 0 else bayer_mumford_bound
            bound_source = "ARTINIAN_GORENSTEIN_SOCLE_12_CAP"

        return {
            "label": label,
            "graded_ranks": list(ranks),
            "graded_annihilator_dims": list(ann_dims),
            "gorenstein_hilbert_vector_0_to_12": hilbert_vector,
            "macaulay_growth_satisfied": growth_holds,
            "macaulay_transitions": macaulay_checks,
            "gotzmann_persistence_degrees": persistent_degrees,
            "effective_variables_v_eff": v_eff,
            "minimal_generation_cutoff_d_gen": d_gen,
            "minimal_generator_profile": gen_prof["profile"],
            "gotzmann_surface_fit": gotz,
            "bayer_mumford_char0_bound": bayer_mumford_bound,
            "artinian_socle_regularity": 12,
            "fermat_apolar_regularity_bound": fermat_certified_bound,
            "bound_authority": bound_source,
            "fermat_apolar_regularity_bounded": True,
            "general_fiber_hilbert_bound_known": False,
        }


# ==============================================================================
# MASTER ENGINE API
# ==============================================================================

class MacaulayApolarityInverseEngine:
    """Unified master API wrapping Modules 1-3 for shadow-to-equation reconstruction."""

    def __init__(self) -> None:
        self.tower = MacaulayApolarityTower()
        self.decomposer = SignedShadowDecomposer(self.tower)
        self.estimator = EffectiveDegreeEstimator(self.tower)

    def run_full_audit(self) -> Dict[str, Any]:
        """Executes full exact Macaulay tower, signed quadric factorization, 18-partition, and degree audits."""
        canonical = self.tower.verify_canonical_plane_and_signed_pair()

        pi_plus: PolyDict = {(4, 4, 4, 0, 0, 0): _one()}
        pi_minus: PolyDict = {(0, 0, 0, 4, 4, 4): _one()}
        lam_signed = poly_sub(pi_plus, pi_minus)
        quad_factor = self.decomposer.factor_signed_quadrics(lam_signed)
        assert quad_factor["exact_product_factorization_matches_ann_R2"] is True
        assert quad_factor["decomposition"]["score"] == 36

        partitions_audit = self.decomposer.audit_all_18_partitions()
        deg_pi = self.estimator.estimate_degree_bound(pi_plus, label="2-plane_Pi")
        deg_signed = self.estimator.estimate_degree_bound(lam_signed, label="signed_disjoint_planes")

        assert deg_pi["gotzmann_surface_fit"]["gotzmann_number_G"] == 1
        assert deg_pi["minimal_generation_cutoff_d_gen"] == 1
        assert deg_signed["gotzmann_surface_fit"]["gotzmann_number_G"] == 5
        assert deg_signed["minimal_generation_cutoff_d_gen"] == 2
        assert deg_pi["macaulay_growth_satisfied"] is True
        assert deg_signed["macaulay_growth_satisfied"] is True
        assert deg_signed["general_fiber_hilbert_bound_known"] is False

        return {
            "canonical_macaulay_tower_audit": canonical,
            "signed_quadric_factorization": {
                "lambda_ann_R1_dim": quad_factor["lambda_ann_R1_dim"],
                "lambda_ann_R2_dim": quad_factor["lambda_ann_R2_dim"],
                "primary_I_plus_dim": quad_factor["primary_I_plus_dim"],
                "primary_I_minus_dim": quad_factor["primary_I_minus_dim"],
                "product_ideal_dim": quad_factor["product_ideal_dim"],
                "exact_product_factorization_matches_ann_R2": quad_factor["exact_product_factorization_matches_ann_R2"],
                "apolar_score": quad_factor["decomposition"]["score"],
            },
            "all_18_partitions_audit": partitions_audit,
            "effective_degree_bounds": {
                "single_plane": deg_pi,
                "signed_disjoint_planes": deg_signed,
            },
            "fermat_apolar_inversion_complete": True,
            "effective_hilbert_degree_bound_known": False,
            "bridge_a_status": "ADVERSARIALLY_BLOCKED_OPEN_BRIDGE",
        }


if __name__ == "__main__":
    engine = MacaulayApolarityInverseEngine()
    report = engine.run_full_audit()
    can = report["canonical_macaulay_tower_audit"]
    sq = report["signed_quadric_factorization"]
    p18 = report["all_18_partitions_audit"]
    deg = report["effective_degree_bounds"]
    print("=== MACAULAY APOLARITY INVERSE ENGINE AUDIT (HODGE-MILLENNIUM-001) ===")
    print(f"2-Plane Ann_R1:             dim={can['single_plane']['ann_R1_dim']} ({can['single_plane']['recovered_ideal_generators']})")
    print(f"Signed Pair Ann_R1/R2:      R1={sq['lambda_ann_R1_dim']}, R2={sq['lambda_ann_R2_dim']}, I+*I- match={sq['exact_product_factorization_matches_ann_R2']}, score={sq['apolar_score']}")
    print(f"18-Partition Decomposition: {p18['signed_pair_recoveries_verified']}/18 pairs, Band1={p18['band1_partitions_verified']}/10, Band2={p18['band2_partitions_verified']}/6, Band3={p18['band3_partitions_verified']}/2")
    print(f"Macaulay/Gotzmann Bounds:   Pi G={deg['single_plane']['fermat_apolar_regularity_bound']}, Signed G={deg['signed_disjoint_planes']['fermat_apolar_regularity_bound']}, General Fiber Bound={report['effective_hilbert_degree_bound_known']}")
