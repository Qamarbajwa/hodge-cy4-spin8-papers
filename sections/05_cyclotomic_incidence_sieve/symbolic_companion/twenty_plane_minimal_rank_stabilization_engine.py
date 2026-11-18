r"""20-Plane Minimal-Rank Recombination & Determinantal Macaulay Stabilization Engine (Event 28).

Formalizes three exact algebraic theorems attacking Global Bridge A (S-BRIDGE-DEFORM-CY4)
on the Fermat sextic Calabi-Yau fourfold X^4_6 \subset \mathbb{P}^5 while preserving strict
honesty on the non-Fermat determinantal stabilization boundary:

1. TwentyPlaneIncidenceAndCollisionEngine:
   Analyzes the 20 coordinate 2-planes V_{20} = \operatorname{span}\{x_i^4 x_j^4 x_k^4\}
   inside R^{12}(F_0) under all 426 first-order deformation directions u \in R^6(F_0):
   - Total non-vanishing monomial incidences across B_6 \times P_{20} = 20 * 19 = 380.
   - Exact target image dimension dim W_{target} = 245 = 200 (three 4s, mult 1) + 45 (four 4s, mult 4),
     yielding 200 * 1 + 45 * 4 = 380 incidences and 380 - 245 = 135 multi-plane collisions.
   - Complementary 181D High-Support Annihilation (426 = 245 + 181): every high-support
     direction (|supp(b)| in {4, 5, 6}, counts 150 + 30 + 1 = 181) gives rk(M_u|_{V_{20}}) = 0
     and ker(M_u|_{V_{20}}) = 20/20 identically.
   - Quadruple support-2 collision witness u_{quad} = x_2^4 x_5^2 + x_3^4 x_5^2 + x_4^4 x_5^2:
     9 coordinate planes have non-zero individual obstructions and 11 vanish individually;
     their 9 non-zero obstructions collide into 5 four-4s target modes, giving
     rk(M_{u_{quad}}|_{V_{20}}) = 5, ker(M_{u_{quad}}|_{V_{20}}) = 15 = 11 + 4,
     and 4 non-trivial collision-cancellation syzygies among the 9 active planes.

2. FifteenMatchingBandOneBlockEngine:
   Decomposes the 1,001-dimensional Band-1 2-plane Fourier subspace of R^{12}(F_0) into the
   union of 15 perfect-matching coordinate-pair blocks of size 125 = 5^3 each:
   - Total block incidences: 15 * 125 = 1,875.
   - Exact union cardinality: 1,001 (exact match to FourierShadowDetector Band 1),
     yielding overlap excess 1,875 - 1,001 = 874.
   - Exact block-multiplicity distribution over the 1,001 Band-1 monomials:
     {1: 360, 2: 540, 3: 60, 6: 40, 15: 1}, with central monomial (2,2,2,2,2,2) appearing in
     all 15 matchings (360 + 540 + 60 + 40 + 1 = 1,001; 1*360 + 2*540 + 3*60 + 6*40 + 15*1 = 1,875).

3. DeterminantalMacaulayStabilizationAudit:
   Inspects the degree-1 Macaulay multiplication block M^{(1)} : R^1 -> R^{13} and its
   dual-number deformed block \widetilde{M}^{(1)} : R^1(F_t) -> R^{13}(F_t) (t^2 = 0):
   - Geometric 2-plane wavepacket \Pi_{true}: r_1 = 3, Ann_{R^1} = 3; deformed block rank
     6 = 2 * 3 (flat) along both fixed u = x_3^4 x_4^2 (Lambda_1 = 0) and moving
     u = x_0^2 x_3^2 x_4^2 (Lambda_1 = 2 x_1^4 x_2^4 x_3^2 x_4^2).
   - Recombined plane sum \Pi_1 + \Pi_2: r_1 = 4, Ann_{R^1} = 2; deformed block rank
     8 = 2 * 4 (flat) along u = x_4^4 x_5^2.
   - Dense generic shadow: r_1 = 6, Ann_{R^1} = 0 (complete loss of linear annihilators).
   - Honesty boundary: universal_non_fermat_determinantal_stabilization_proved = False.

Zero floating-point constructs: 100% exact integers, tuples, and fractions.Fraction.
"""

from __future__ import annotations

import itertools
import sys
from collections import Counter
from fractions import Fraction
from pathlib import Path
from typing import Any, Dict, List, Optional, Sequence, Tuple

_REPO_ROOT = str(Path(__file__).resolve().parent.parent)
if _REPO_ROOT not in sys.path:
    sys.path.insert(0, _REPO_ROOT)

from toolkit.calabi_yau_jacobian_engine import CalabiYauJacobianEngine
from toolkit.deformed_macaulay_transport_engine import DeformedJacobianRingJet
from toolkit.erdos_fourier_incidence_engine import FourierShadowDetector
from toolkit.higher_order_gauss_manin_sieve import (
    Monomial,
    PolyDict,
    poly_add,
    poly_mod_jacobian,
    poly_mul,
)
from toolkit.integrity import scan_forbidden
from toolkit.macaulay_apolarity_inverse_engine import _sparse_rref_and_nullspace
from toolkit.universal_obstruction_cancellation_engine import REPS_9_SHIFTED


def _zero() -> Fraction:
    return Fraction(0, 1)


def _one() -> Fraction:
    return Fraction(1, 1)


def _add_exps(a: Monomial, b: Monomial) -> Monomial:
    return tuple(x + y for x, y in zip(a, b))


def _is_reduced_jac(m: Monomial) -> bool:
    return all(e <= 4 for e in m)


def _support_size(m: Monomial) -> int:
    return sum(1 for e in m if e > 0)


# ==============================================================================
# MODULE 1: 20-PLANE INCIDENCE, 426 = 245 + 181 SPLIT & QUADRUPLE COLLISIONS
# ==============================================================================


class TwentyPlaneIncidenceAndCollisionEngine:
    """Exact incidence, 181D high-support annihilation, and quadruple collision engine on V_{20}."""

    EXPECTED_TOTAL_INCIDENCES: int = 380
    EXPECTED_TARGET_DIM: int = 245
    EXPECTED_THREE_FOUR_TARGETS: int = 200
    EXPECTED_FOUR_FOUR_TARGETS: int = 45
    EXPECTED_COLLISION_EXCESS: int = 135
    EXPECTED_HIGH_SUPPORT_DIM: int = 181

    def __init__(self, cy_engine: Optional[CalabiYauJacobianEngine] = None) -> None:
        self.cy = cy_engine if cy_engine is not None else CalabiYauJacobianEngine()
        self.basis_6: List[Monomial] = self.cy.generate_monomial_basis(6)
        self.basis_12: List[Monomial] = self.cy.generate_monomial_basis(12)
        self.basis_18: List[Monomial] = self.cy.generate_monomial_basis(18)
        self.plane_triples: List[Tuple[int, int, int]] = list(
            itertools.combinations(range(6), 3)
        )
        self.plane_monomials: List[Monomial] = [
            tuple(4 if k in tri else 0 for k in range(6))
            for tri in self.plane_triples
        ]

    def _restrict_v20_matrix(
        self, u_poly: PolyDict
    ) -> Tuple[int, List[List[Fraction]], int, List[Monomial]]:
        """Builds exact sparse map M_u|_{V_{20}} -> R^{18}(F_0) and returns (rk, ker, active_cnt, targets)."""
        target_rows: Dict[Monomial, Dict[int, Fraction]] = {}
        active_plane_count = 0
        for col_idx, plane_mon in enumerate(self.plane_monomials):
            prod = poly_mul(u_poly, {plane_mon: _one()})
            reduced = poly_mod_jacobian(prod, jac_deg=5)
            if reduced:
                active_plane_count += 1
            for mon, coeff in reduced.items():
                row = target_rows.setdefault(mon, {})
                row[col_idx] = coeff

        ordered_targets = sorted(target_rows.keys())
        rows = [target_rows[m] for m in ordered_targets]
        rk, kernel = _sparse_rref_and_nullspace(rows, len(self.plane_monomials))
        return rk, kernel, active_plane_count, ordered_targets

    def analyze_incidence_and_high_support(self) -> Dict[str, Any]:
        """Certifies 380 = 245 + 135 collision law and 181D high-support annihilation on V_{20}."""
        per_plane_hits: List[int] = [0] * len(self.plane_monomials)
        target_hit_counts: Counter = Counter()
        support_dist: Counter = Counter()
        monomial_ranks: Counter = Counter()
        low_support_zero_hits = 0
        high_support_zero_hits = 0
        high_support_nonzero_hits = 0
        low_support_plane_hit_counts: Dict[int, List[int]] = {2: [], 3: []}

        for b in self.basis_6:
            supp = _support_size(b)
            support_dist[supp] += 1
            hit_planes = 0
            for p_idx, p_mon in enumerate(self.plane_monomials):
                prod = _add_exps(b, p_mon)
                if _is_reduced_jac(prod):
                    hit_planes += 1
                    per_plane_hits[p_idx] += 1
                    target_hit_counts[prod] += 1

            monomial_ranks[hit_planes] += 1
            if supp <= 3:
                low_support_plane_hit_counts[supp].append(hit_planes)
                if hit_planes == 0:
                    low_support_zero_hits += 1
            else:
                if hit_planes == 0:
                    high_support_zero_hits += 1
                else:
                    high_support_nonzero_hits += 1

        three_4_targets = sum(1 for m in target_hit_counts if m.count(4) == 3)
        four_4_targets = sum(1 for m in target_hit_counts if m.count(4) == 4)
        other_targets = sum(
            1 for m in target_hit_counts if m.count(4) not in (3, 4)
        )
        multiplicity_dist = dict(sorted(Counter(target_hit_counts.values()).items()))
        total_incidences = sum(per_plane_hits)
        target_subspace_dim = len(target_hit_counts)
        collision_excess = total_incidences - target_subspace_dim

        # 9-partition V_{20} rank census using REPS_9_SHIFTED
        partition_v20_census: Dict[Tuple[int, ...], Dict[str, Any]] = {}
        for mon in REPS_9_SHIFTED:
            part = tuple(sorted((e for e in mon if e > 0), reverse=True))
            rk, ker, act, _ = self._restrict_v20_matrix({mon: _one()})
            partition_v20_census[part] = {
                "representative": mon,
                "rank_on_v20": rk,
                "kernel_on_v20": len(ker),
                "active_planes": act,
            }

        return {
            "num_coordinate_planes": len(self.plane_monomials),
            "per_plane_incidence_set": sorted(set(per_plane_hits)),
            "total_incidences": total_incidences,
            "target_subspace_dim": target_subspace_dim,
            "three_4_targets": three_4_targets,
            "four_4_targets": four_4_targets,
            "other_targets": other_targets,
            "multiplicity_distribution": multiplicity_dist,
            "collision_excess": collision_excess,
            "support_distribution": dict(sorted(support_dist.items())),
            "low_support_total": support_dist[2] + support_dist[3],
            "high_support_total": support_dist[4] + support_dist[5] + support_dist[6],
            "high_support_counts": {k: support_dist[k] for k in (4, 5, 6)},
            "low_support_counts": {k: support_dist[k] for k in (2, 3)},
            "low_support_hit_sets": {
                k: sorted(set(v)) for k, v in low_support_plane_hit_counts.items()
            },
            "low_support_zero_hits": low_support_zero_hits,
            "high_support_zero_count": high_support_zero_hits,
            "high_support_all_zero_on_v20": (
                high_support_zero_hits == 181 and high_support_nonzero_hits == 0
            ),
            "monomial_v20_rank_histogram": dict(sorted(monomial_ranks.items())),
            "partition_v20_census": partition_v20_census,
        }

    def analyze_quadruple_witness(self) -> Dict[str, Any]:
        """Verifies quadruple support-2 witness u_{quad} = x_2^4 x_5^2 + x_3^4 x_5^2 + x_4^4 x_5^2."""
        u_quad: PolyDict = {
            (0, 0, 4, 0, 0, 2): _one(),
            (0, 0, 0, 4, 0, 2): _one(),
            (0, 0, 0, 0, 4, 2): _one(),
        }
        rk, kernel, active_planes, targets = self._restrict_v20_matrix(u_quad)
        individually_zero_planes = len(self.plane_monomials) - active_planes
        nontrivial_collision_syzygies = len(kernel) - individually_zero_planes

        # Explicitly verify every rational kernel vector annihilates u_quad mod J(F_0)
        active_indices = set()
        for col_idx, p_mon in enumerate(self.plane_monomials):
            if poly_mod_jacobian(poly_mul(u_quad, {p_mon: _one()}), jac_deg=5):
                active_indices.add(col_idx)

        all_kernel_vectors_verified = True
        nontrivial_syzygy_vectors: List[List[Fraction]] = []
        for vec in kernel:
            combined: PolyDict = {}
            for col_idx, coeff in enumerate(vec):
                if coeff != 0:
                    p_mon = self.plane_monomials[col_idx]
                    combined = poly_add(combined, {p_mon: coeff})
            ann_check = poly_mod_jacobian(poly_mul(u_quad, combined), jac_deg=5)
            if ann_check:
                all_kernel_vectors_verified = False
            if any(vec[col_idx] != 0 for col_idx in active_indices):
                nontrivial_syzygy_vectors.append(vec)

        four_4_targets = sum(1 for m in targets if m.count(4) == 4)
        three_4_targets = sum(1 for m in targets if m.count(4) == 3)

        return {
            "quad_active_planes": active_planes,
            "quad_individually_zero_planes": individually_zero_planes,
            "quad_target_count": len(targets),
            "quad_four_4_targets": four_4_targets,
            "quad_three_4_targets": three_4_targets,
            "quad_v20_rank": rk,
            "quad_v20_kernel_dim": len(kernel),
            "quad_nontrivial_collision_syzygies": nontrivial_collision_syzygies,
            "quad_active_syzygy_basis_count": len(nontrivial_syzygy_vectors),
            "all_kernel_vectors_annihilate_u_quad": all_kernel_vectors_verified,
        }


# ==============================================================================
# MODULE 2: 15-MATCHING BAND-1 BLOCK DECOMPOSITION & MULTIPLICITY LAW
# ==============================================================================


class FifteenMatchingBandOneBlockEngine:
    """Certifies the 15 x 125 = 1,875 -> 1,001 perfect-matching Band-1 decomposition."""

    EXPECTED_NUM_MATCHINGS: int = 15
    EXPECTED_MODES_PER_BLOCK: int = 125
    EXPECTED_TOTAL_INCIDENCES: int = 1875
    EXPECTED_UNION_SIZE: int = 1001
    EXPECTED_OVERLAP_EXCESS: int = 874
    EXPECTED_MULTIPLICITY_HIST: Dict[int, int] = {1: 360, 2: 540, 3: 60, 6: 40, 15: 1}
    CENTRAL_MONOMIAL: Monomial = (2, 2, 2, 2, 2, 2)

    def __init__(self, cy_engine: Optional[CalabiYauJacobianEngine] = None) -> None:
        self.cy = cy_engine if cy_engine is not None else CalabiYauJacobianEngine()
        self.basis_12: List[Monomial] = self.cy.generate_monomial_basis(12)
        self.matchings_15: List[List[Tuple[int, int]]] = (
            FourierShadowDetector._generate_all_15_matchings()
        )
        self.detector = FourierShadowDetector()

    @staticmethod
    def _matching_block_monomials(matching: List[Tuple[int, int]]) -> List[Monomial]:
        """Generates the exact 125 Band-1 monomials (a_{i_r} + a_{j_r} = 4, 0 <= a <= 4)."""
        (i1, j1), (i2, j2), (i3, j3) = matching
        block: List[Monomial] = []
        for a1 in range(5):
            for a2 in range(5):
                for a3 in range(5):
                    vec = [0] * 6
                    vec[i1], vec[j1] = a1, 4 - a1
                    vec[i2], vec[j2] = a2, 4 - a2
                    vec[i3], vec[j3] = a3, 4 - a3
                    block.append(tuple(vec))
        return block

    def analyze_blocks(self) -> Dict[str, Any]:
        """Computes all 15 blocks, verifies exact Band-1 union (1,001), and records multiplicity."""
        block_sizes: List[int] = []
        occ_counts: Counter = Counter()

        for matching in self.matchings_15:
            block = self._matching_block_monomials(matching)
            block_sizes.append(len(block))
            for mon in set(block):
                occ_counts[mon] += 1

        band1_ref = {
            m for m in self.basis_12 if self.detector.classify_monomial(m) == "2-PLANE_PAIRABLE"
        }
        union_set = set(occ_counts.keys())
        mult_hist = dict(sorted(Counter(occ_counts.values()).items()))
        total_incidences = sum(block_sizes)
        union_size = len(union_set)
        weighted_sum = sum(mult * cnt for mult, cnt in mult_hist.items())

        return {
            "num_matchings": len(self.matchings_15),
            "modes_per_block_set": sorted(set(block_sizes)),
            "modes_per_block": block_sizes[0],
            "total_incidences": total_incidences,
            "union_size": union_size,
            "band1_reference_size": len(band1_ref),
            "band1_exact_match": (union_set == band1_ref),
            "overlap_excess": total_incidences - union_size,
            "multiplicity_histogram": mult_hist,
            "weighted_multiplicity_sum": weighted_sum,
            "central_monomial": self.CENTRAL_MONOMIAL,
            "central_monomial_multiplicity": occ_counts[self.CENTRAL_MONOMIAL],
            "mult_15_monomials": sorted(m for m, c in occ_counts.items() if c == 15),
        }


# ==============================================================================
# MODULE 3: DETERMINANTAL MACAULAY STABILIZATION AUDIT (STATIC + DEFORMED m=1)
# ==============================================================================


class DeterminantalMacaulayStabilizationAudit:
    """Inspects exact m=1 static/deformed Macaulay block ranks and global honesty boundary."""

    def __init__(self, ring_jet: Optional[DeformedJacobianRingJet] = None) -> None:
        self.jet = ring_jet if ring_jet is not None else DeformedJacobianRingJet()
        self.macaulay = self.jet.macaulay
        self.lam_pi: PolyDict = self.jet.LAM_PI
        # Recombined 2-plane sum Pi_1 + Pi_2 = x_0^4 x_1^4 (x_2^4 + x_3^4)
        self.lam_recomb: PolyDict = {
            (4, 4, 4, 0, 0, 0): _one(),
            (4, 4, 0, 4, 0, 0): _one(),
        }
        # Generic 6-plane dense sum spanning all 6 variables cleanly
        self.lam_generic: PolyDict = {
            (4, 4, 4, 0, 0, 0): Fraction(1, 1),
            (0, 4, 4, 4, 0, 0): Fraction(2, 1),
            (0, 0, 4, 4, 4, 0): Fraction(3, 1),
            (0, 0, 0, 4, 4, 4): Fraction(5, 1),
            (4, 0, 0, 0, 4, 4): Fraction(7, 1),
            (4, 4, 0, 0, 0, 4): Fraction(11, 1),
        }

    def _static_deg1(self, lam_poly: PolyDict) -> Tuple[int, int]:
        _, nd, rows = self.macaulay.multiplication_sparse_rows(lam_poly, 1)
        rk, kernel = _sparse_rref_and_nullspace(rows, nd)
        return rk, len(kernel)

    def run_audit(self) -> Dict[str, Any]:
        """Runs static and dual-number deformed determinantal checks across Pi, Pi_1+Pi_2, generic."""
        # 1. Single geometric 2-plane wavepacket Pi
        pi_r1, pi_ann1 = self._static_deg1(self.lam_pi)
        u_fixed: PolyDict = {(0, 0, 0, 4, 2, 0): _one()}  # x_3^4 x_4^2
        pi_fixed_def = self.jet.deformed_hilbert_and_ranks(
            self.lam_pi, {}, u_fixed, degrees=(1,)
        )

        # Moving 2-plane deformation: u = x_0^2 x_3^2 x_4^2 with Lambda_1 = 2 x_1^4 x_2^4 x_3^2 x_4^2
        u_moving: PolyDict = {(2, 0, 0, 2, 2, 0): _one()}
        lam1_moving: PolyDict = {(0, 4, 4, 2, 2, 0): Fraction(2, 1)}
        pi_moving_def = self.jet.deformed_hilbert_and_ranks(
            self.lam_pi, lam1_moving, u_moving, degrees=(1,)
        )

        # 2. Recombined pair Pi_1 + Pi_2 = x_0^4 x_1^4 (x_2^4 + x_3^4)
        recomb_r1, recomb_ann1 = self._static_deg1(self.lam_recomb)
        u_recomb: PolyDict = {(0, 0, 0, 0, 4, 2): _one()}  # x_4^4 x_5^2
        recomb_def = self.jet.deformed_hilbert_and_ranks(
            self.lam_recomb, {}, u_recomb, degrees=(1,)
        )

        # 3. Generic full-rank dense shadow
        gen_r1, gen_ann1 = self._static_deg1(self.lam_generic)

        return {
            "pi_static_r1": pi_r1,
            "pi_static_ann1": pi_ann1,
            "pi_fixed_def_r1": pi_fixed_def["deformed_ranks"][1],
            "pi_fixed_flat": pi_fixed_def["flat_by_degree"][1],
            "pi_moving_def_r1": pi_moving_def["deformed_ranks"][1],
            "pi_moving_flat": pi_moving_def["flat_by_degree"][1],
            "recomb_static_r1": recomb_r1,
            "recomb_static_ann1": recomb_ann1,
            "recomb_def_r1": recomb_def["deformed_ranks"][1],
            "recomb_flat": recomb_def["flat_by_degree"][1],
            "generic_static_r1": gen_r1,
            "generic_static_ann1": gen_ann1,
            "universal_non_fermat_determinantal_stabilization_proved": False,
            "global_hodge_conjecture_status": "OPEN",
        }


# ==============================================================================
# FACADE: TWENTY-PLANE MINIMAL-RANK STABILIZATION ENGINE
# ==============================================================================


class TwentyPlaneMinimalRankStabilizationEngine:
    """Unified Event 28 verification engine coordinating Modules 1-3."""

    def __init__(self) -> None:
        self.v20_engine = TwentyPlaneIncidenceAndCollisionEngine()
        self.matching_engine = FifteenMatchingBandOneBlockEngine(cy_engine=self.v20_engine.cy)
        self.macaulay_audit = DeterminantalMacaulayStabilizationAudit()

    def run_full_audit(self) -> Dict[str, Any]:
        """Executes all Event 28 exact computations and verifies self scan_forbidden."""
        inc = self.v20_engine.analyze_incidence_and_high_support()
        quad = self.v20_engine.analyze_quadruple_witness()
        blocks = self.matching_engine.analyze_blocks()
        det = self.macaulay_audit.run_audit()
        self_forbidden = scan_forbidden(__file__)

        return {
            "incidence": inc,
            "quadruple_witness": quad,
            "fifteen_matchings": blocks,
            "determinantal_macaulay": det,
            "scan_forbidden_hits": len(self_forbidden),
            "universal_non_fermat_determinantal_stabilization_proved": det[
                "universal_non_fermat_determinantal_stabilization_proved"
            ],
            "global_hodge_conjecture_status": det["global_hodge_conjecture_status"],
        }


if __name__ == "__main__":
    engine = TwentyPlaneMinimalRankStabilizationEngine()
    report = engine.run_full_audit()
    inc = report["incidence"]
    quad = report["quadruple_witness"]
    blk = report["fifteen_matchings"]
    det = report["determinantal_macaulay"]

    print(
        f"[V20] planes={inc['num_coordinate_planes']} incidences={inc['total_incidences']} "
        f"target_dim={inc['target_subspace_dim']} (three4={inc['three_4_targets']}, four4={inc['four_4_targets']}) "
        f"collisions={inc['collision_excess']} high_supp_zero={inc['high_support_zero_count']}/{inc['high_support_total']}"
    )
    print(
        f"[QUAD] active={quad['quad_active_planes']} zero={quad['quad_individually_zero_planes']} "
        f"four4_targets={quad['quad_four_4_targets']} rk={quad['quad_v20_rank']} "
        f"ker={quad['quad_v20_kernel_dim']} nontrivial_collisions={quad['quad_nontrivial_collision_syzygies']} "
        f"verified={quad['all_kernel_vectors_annihilate_u_quad']}"
    )
    print(
        f"[BAND1-15] matchings={blk['num_matchings']} block={blk['modes_per_block']} "
        f"total={blk['total_incidences']} union={blk['union_size']} excess={blk['overlap_excess']} "
        f"hist={blk['multiplicity_histogram']} central_mult={blk['central_monomial_multiplicity']}"
    )
    print(
        f"[DET-M1] Pi=({det['pi_static_r1']}, Ann={det['pi_static_ann1']}, "
        f"fixed_def={det['pi_fixed_def_r1']}, moving_def={det['pi_moving_def_r1']}) "
        f"Recomb=({det['recomb_static_r1']}, Ann={det['recomb_static_ann1']}, def={det['recomb_def_r1']}) "
        f"Generic=({det['generic_static_r1']}, Ann={det['generic_static_ann1']})"
    )
    print(
        f"[AUDIT] scan_forbidden={report['scan_forbidden_hits']} "
        f"global_hodge={report['global_hodge_conjecture_status']}"
    )
