r"""Universal Obstruction-Cancellation & Gorenstein Moduli Duality Engine (Event 26).

Formalizes three exact structural theorems on the Fermat sextic Calabi-Yau fourfold
X^4_6 \subset \mathbb{P}^5 and its 426-dimensional complex deformation space R^6(F_0):
1. UniversalRankNullityCancellationEngine:
   For ANY deformation u \in R^6(F_0), the Carlson-Griffiths multiplication operator
   M_u : V -> R^{18}(F_0) (\dim R^{18}(F_0) = 426) has kernel lower bounds:
     - Full R^{12}(F_0) (dim 1,751): \dim \ker(M_u) >= 1,751 - 426 = 1,325.
     - Band-1 (dim 1,001): \dim(\ker(M_u) \cap V_{Band-1}) >= 1,001 - 426 = 575.
     - Band-2 (dim 630): \dim(\ker(M_u) \cap V_{Band-2}) >= 630 - 426 = 204.
   Verified constructively on a symmetry-breaking 9-partition dense deformation u_{dense}
   using exact sparse rational elimination over Q.
2. GorensteinModuliRankCensus:
   Exhaustive census of all 426 basis monomials x^b \in R^6(F_0) across all 9 unordered
   exponent partitions, proving Gorenstein complement duality (a'_i = 4 - b_i - a_i)
   and exact matrix rank range rk(M_{x^b}) \in [155, 336], \dim \ker \in [1415, 1596].
3. TuranCoordinatePlaneCoverageEngine:
   Exact analysis across all \binom{6}{3} = 20 coordinate 2-planes and all 426 monomials,
   proving max obstructed planes = 4 (min surviving = 16) and the Pigeonhole K = 5
   coverage law across all \binom{20}{5} = 15,504 subsets (0 / 6,604,704 uncovered pairs).

Zero floating-point constructs: 100% exact integers, tuples, and fractions.Fraction.
Scientific Honesty Boundary: GLOBAL_HODGE_CONJECTURE remains OPEN; universal
first-order cancellation does not establish bounded-regularity all-order lifting.
"""

from __future__ import annotations

from collections import Counter
from fractions import Fraction
import itertools
import math
from pathlib import Path
import sys
from typing import Any, Dict, List, Optional, Sequence, Tuple

ROOT = Path(__file__).resolve().parent.parent
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from toolkit.calabi_yau_jacobian_engine import CalabiYauJacobianEngine
from toolkit.erdos_fourier_incidence_engine import FourierShadowDetector
from toolkit.integrity import scan_forbidden


REPS_9_SHIFTED: List[Tuple[int, ...]] = [
    (4, 2, 0, 0, 0, 0),
    (0, 4, 1, 1, 0, 0),
    (0, 0, 3, 3, 0, 0),
    (1, 0, 0, 3, 2, 0),
    (1, 1, 0, 0, 3, 1),
    (0, 2, 0, 2, 0, 2),
    (1, 0, 2, 2, 0, 1),
    (1, 1, 1, 0, 2, 1),
    (1, 1, 1, 1, 1, 1),
]


def fast_exact_sparse_rank(
    basis_12: Sequence[Tuple[int, ...]],
    u_poly: Dict[Tuple[int, ...], int],
    m18_idx: Dict[Tuple[int, ...], int],
) -> int:
    """Computes the exact rational rank of M_u : Span(basis_12) -> R^{18}(F_0) over Q.

    Uses sparse column sorting by non-zero count and shortest-pivot elimination over
    exact fractions.Fraction, avoiding dense fraction denominator growth.
    """
    cols: List[Dict[int, Fraction]] = []
    for a in basis_12:
        col: Dict[int, Fraction] = {}
        for b, coeff in u_poly.items():
            if coeff == 0:
                continue
            s = (
                a[0] + b[0],
                a[1] + b[1],
                a[2] + b[2],
                a[3] + b[3],
                a[4] + b[4],
                a[5] + b[5],
            )
            if s in m18_idx:
                row_idx = m18_idx[s]
                nv = col.get(row_idx, Fraction(0, 1)) + Fraction(coeff, 1)
                if nv == 0:
                    col.pop(row_idx, None)
                else:
                    col[row_idx] = nv
        if col:
            cols.append(col)

    cols.sort(key=len)
    pivots: Dict[int, Dict[int, Fraction]] = {}
    for col in cols:
        v = dict(col)
        while v:
            matching = [r for r in v if r in pivots]
            if not matching:
                break
            p_idx = min(matching, key=lambda r: len(pivots[r]))
            factor = v.pop(p_idx)
            for k, p_val in pivots[p_idx].items():
                nv = v.get(k, Fraction(0, 1)) - factor * p_val
                if nv == 0:
                    v.pop(k, None)
                else:
                    v[k] = nv
        if v:
            first_nz = min(v.keys())
            inv = Fraction(1, 1) / v.pop(first_nz)
            pivots[first_nz] = {k: val * inv for k, val in v.items()}
    return len(pivots)


# ==============================================================================
# MODULE 1: UNIVERSAL RANK-NULLITY OBSTRUCTION-CANCELLATION BOUNDS
# ==============================================================================


class UniversalRankNullityCancellationEngine:
    """Proves universal Rank-Nullity cancellation lower bounds across all u in R^6(F_0)."""

    def __init__(
        self,
        cy_engine: Optional[CalabiYauJacobianEngine] = None,
        fsd: Optional[FourierShadowDetector] = None,
    ) -> None:
        self.cy = cy_engine or CalabiYauJacobianEngine()
        self.fsd = fsd or FourierShadowDetector()
        self.m6 = self.cy.generate_monomial_basis(6)
        self.m12 = self.cy.generate_monomial_basis(12)
        self.m18 = self.cy.generate_monomial_basis(18)
        self.m18_idx = {e: i for i, e in enumerate(self.m18)}

        self.band1 = [a for a in self.m12 if self.fsd.classify_monomial(a) == "2-PLANE_PAIRABLE"]
        self.band2 = [a for a in self.m12 if self.fsd.classify_monomial(a) == "INDUCTIVE_3_PLUS_3"]
        self.band3 = [
            a for a in self.m12 if self.fsd.classify_monomial(a) == "INDUCTIVE_2_PLUS_4_LEFSCHETZ"
        ]

    def run_audit(self) -> Dict[str, Any]:
        dim_r6 = len(self.m6)
        dim_r12 = len(self.m12)
        dim_r18 = len(self.m18)
        dim_band1 = len(self.band1)
        dim_band2 = len(self.band2)
        dim_band3 = len(self.band3)
        dim_band4 = dim_r12 - (dim_band1 + dim_band2 + dim_band3)

        assert dim_r6 == 426
        assert dim_r12 == 1751
        assert dim_r18 == 426
        assert dim_band1 == 1001
        assert dim_band2 == 630
        assert dim_band3 == 120
        assert dim_band4 == 0

        univ_total_lb = dim_r12 - dim_r18
        univ_band1_lb = dim_band1 - dim_r18
        univ_band2_lb = dim_band2 - dim_r18
        assert univ_total_lb == 1325
        assert univ_band1_lb == 575
        assert univ_band2_lb == 204

        u_dense = {r: idx + 1 for idx, r in enumerate(REPS_9_SHIFTED)}
        assert len(u_dense) == 9
        for r in u_dense:
            assert r in self.m6

        rk_full = fast_exact_sparse_rank(self.m12, u_dense, self.m18_idx)
        rk_b1 = fast_exact_sparse_rank(self.band1, u_dense, self.m18_idx)
        rk_b2 = fast_exact_sparse_rank(self.band2, u_dense, self.m18_idx)
        rk_b3 = fast_exact_sparse_rank(self.band3, u_dense, self.m18_idx)

        ker_full = dim_r12 - rk_full
        ker_b1 = dim_band1 - rk_b1
        ker_b2 = dim_band2 - rk_b2
        ker_b3 = dim_band3 - rk_b3

        assert rk_full == 426 and ker_full == 1325 and ker_full >= univ_total_lb
        assert rk_b1 == 408 and ker_b1 == 593 and ker_b1 >= univ_band1_lb
        assert rk_b2 == 338 and ker_b2 == 292 and ker_b2 >= univ_band2_lb
        assert rk_b3 == 114 and ker_b3 == 6

        return {
            "dim_R6": dim_r6,
            "dim_R12": dim_r12,
            "dim_R18": dim_r18,
            "dim_band1": dim_band1,
            "dim_band2": dim_band2,
            "dim_band3": dim_band3,
            "dim_band4": dim_band4,
            "universal_total_kernel_lower_bound": univ_total_lb,
            "universal_band1_kernel_lower_bound": univ_band1_lb,
            "universal_band2_kernel_lower_bound": univ_band2_lb,
            "dense_u_partitions_combined": len(u_dense),
            "dense_full_rank": rk_full,
            "dense_full_kernel_dim": ker_full,
            "dense_band1_rank": rk_b1,
            "dense_band1_kernel_dim": ker_b1,
            "dense_band2_rank": rk_b2,
            "dense_band2_kernel_dim": ker_b2,
            "dense_band3_rank": rk_b3,
            "dense_band3_kernel_dim": ker_b3,
            "universal_bounds_satisfied": True,
            "all_order_castelnuovo_mumford_bound_proved": False,
        }


# ==============================================================================
# MODULE 2: COMPLETE 9-PARTITION GORENSTEIN MODULI RANK CENSUS
# ==============================================================================


class GorensteinModuliRankCensus:
    """Computes the exact 9-partition moduli rank & Gorenstein duality census over R^6(F_0)."""

    def __init__(
        self,
        m6: Optional[List[Tuple[int, ...]]] = None,
        m12: Optional[List[Tuple[int, ...]]] = None,
        m18: Optional[List[Tuple[int, ...]]] = None,
    ) -> None:
        cy = CalabiYauJacobianEngine()
        self.m6 = m6 if m6 is not None else cy.generate_monomial_basis(6)
        self.m12 = m12 if m12 is not None else cy.generate_monomial_basis(12)
        self.m18 = m18 if m18 is not None else cy.generate_monomial_basis(18)
        self.m18_idx = {e: i for i, e in enumerate(self.m18)}

    def run_audit(self) -> Dict[str, Any]:
        part_counts = Counter(tuple(sorted(b, reverse=True)) for b in self.m6)
        assert len(part_counts) == 9
        assert sum(part_counts.values()) == 426

        records: List[Dict[str, Any]] = []
        duality_verified_count = 0
        matrix_matches_all = True

        for part in sorted(part_counts.keys(), reverse=True):
            mult = part_counts[part]
            cap = tuple(4 - x for x in part)
            deg12_count = sum(1 for a in self.m12 if all(a[i] <= cap[i] for i in range(6)))
            deg6_dual_count = sum(1 for ap in self.m6 if all(ap[i] <= cap[i] for i in range(6)))

            # Verify bijection a -> (4 - b_i - a_i) between deg-12 and deg-6 bounded monomials
            dual_images = {
                tuple(cap[i] - a[i] for i in range(6))
                for a in self.m12
                if all(a[i] <= cap[i] for i in range(6))
            }
            deg6_bounded = {ap for ap in self.m6 if all(ap[i] <= cap[i] for i in range(6))}
            assert dual_images == deg6_bounded
            assert deg12_count == deg6_dual_count
            duality_verified_count += 1

            # Verify exact sparse matrix rank of M_{x^b} matches combinatorial capacity count
            rk_mat = fast_exact_sparse_rank(self.m12, {part: 1}, self.m18_idx)
            if rk_mat != deg12_count:
                matrix_matches_all = False
            assert rk_mat == deg12_count

            ker_dim = len(self.m12) - rk_mat
            records.append(
                {
                    "partition": part,
                    "multiplicity": mult,
                    "rank": rk_mat,
                    "gorenstein_dual_deg6_count": deg6_dual_count,
                    "kernel_dim": ker_dim,
                }
            )

        assert duality_verified_count == 9
        assert matrix_matches_all is True

        min_rec = min(records, key=lambda r: r["rank"])
        max_rec = max(records, key=lambda r: r["rank"])
        assert min_rec["rank"] == 155 and min_rec["kernel_dim"] == 1596
        assert min_rec["partition"] == (4, 2, 0, 0, 0, 0)
        assert max_rec["rank"] == 336 and max_rec["kernel_dim"] == 1415
        assert max_rec["partition"] == (1, 1, 1, 1, 1, 1)

        return {
            "total_moduli_monomials": len(self.m6),
            "total_moduli_partitions": len(records),
            "partitions": records,
            "gorenstein_complement_duality_verified_count": duality_verified_count,
            "gorenstein_complement_duality_holds_all_9": duality_verified_count == 9,
            "global_min_rank": min_rec["rank"],
            "global_min_rank_partition": min_rec["partition"],
            "global_max_rank": max_rec["rank"],
            "global_max_rank_partition": max_rec["partition"],
            "global_min_kernel_dim": max_rec["kernel_dim"],
            "global_max_kernel_dim": min_rec["kernel_dim"],
            "matrix_rank_matches_capacity_all_9": matrix_matches_all,
        }


# ==============================================================================
# MODULE 3: K = 5 TURAN / PIGEONHOLE COORDINATE 2-PLANE COVERAGE LAW
# ==============================================================================


class TuranCoordinatePlaneCoverageEngine:
    """Proves the K = 5 Pigeonhole Coordinate 2-Plane Coverage Law over all 426 directions."""

    def __init__(
        self,
        m6: Optional[List[Tuple[int, ...]]] = None,
        m12: Optional[List[Tuple[int, ...]]] = None,
    ) -> None:
        cy = CalabiYauJacobianEngine()
        self.m6 = m6 if m6 is not None else cy.generate_monomial_basis(6)
        self.m12 = m12 if m12 is not None else cy.generate_monomial_basis(12)
        self.planes = [a for a in self.m12 if a.count(4) == 3]
        assert len(self.planes) == 20

    def run_audit(self) -> Dict[str, Any]:
        # Bitmask of obstructed coordinate 2-planes per monomial x^b in R^6(F_0)
        obs_masks: List[int] = []
        supp_2_cnt = 0
        supp_3_cnt = 0
        supp_ge4_cnt = 0
        max_obstructed = 0
        min_surviving = 20

        for b in self.m6:
            supp_size = sum(1 for x in b if x > 0)
            mask = 0
            obs_count = 0
            for idx, p in enumerate(self.planes):
                if all(b[i] + p[i] <= 4 for i in range(6)):
                    mask |= 1 << idx
                    obs_count += 1
            assert obs_count == math.comb(6 - supp_size, 3)
            obs_masks.append(mask)

            if supp_size == 2:
                supp_2_cnt += 1
                assert obs_count == 4
            elif supp_size == 3:
                supp_3_cnt += 1
                assert obs_count == 1
            else:
                assert supp_size >= 4
                supp_ge4_cnt += 1
                assert obs_count == 0

            max_obstructed = max(max_obstructed, obs_count)
            min_surviving = min(min_surviving, 20 - obs_count)

        assert supp_2_cnt == 45
        assert supp_3_cnt == 200
        assert supp_ge4_cnt == 181
        assert max_obstructed == 4
        assert min_surviving == 16

        # Unique obstructed bitmasks (deduped for fast exact universal subset verification)
        unique_mask_counts = Counter(obs_masks)

        # K = 5 Pigeonhole check across all C(20, 5) = 15,504 subsets x 426 directions = 6,604,704 incidences
        k5_subsets_tested = 0
        k5_uncovered = 0
        for sub in itertools.combinations(range(20), 5):
            k5_subsets_tested += 1
            sub_mask = (1 << sub[0]) | (1 << sub[1]) | (1 << sub[2]) | (1 << sub[3]) | (1 << sub[4])
            for m_val, mult in unique_mask_counts.items():
                if (sub_mask & m_val) == sub_mask:
                    k5_uncovered += mult

        assert k5_subsets_tested == 15504
        assert k5_subsets_tested * len(self.m6) == 6604704
        assert k5_uncovered == 0

        # K = 4 failure count: each of the 45 support-2 monomials fails its unique 4-obstructed subset
        k4_subsets_tested = 0
        k4_failing = 0
        for sub in itertools.combinations(range(20), 4):
            k4_subsets_tested += 1
            sub_mask = (1 << sub[0]) | (1 << sub[1]) | (1 << sub[2]) | (1 << sub[3])
            for m_val, mult in unique_mask_counts.items():
                if (sub_mask & m_val) == sub_mask:
                    k4_failing += mult

        assert k4_subsets_tested == 4845
        assert k4_failing == 45

        return {
            "coordinate_planes_count": len(self.planes),
            "moduli_monomials_count": len(self.m6),
            "support_2_monomials_count": supp_2_cnt,
            "support_2_obstructed_planes": 4,
            "support_2_surviving_planes": 16,
            "support_3_monomials_count": supp_3_cnt,
            "support_3_obstructed_planes": 1,
            "support_3_surviving_planes": 19,
            "support_ge4_monomials_count": supp_ge4_cnt,
            "support_ge4_obstructed_planes": 0,
            "support_ge4_surviving_planes": 20,
            "max_obstructed_planes_per_monomial": max_obstructed,
            "min_surviving_planes_per_monomial": min_surviving,
            "pigeonhole_min_K": 5,
            "k5_subsets_tested": k5_subsets_tested,
            "k5_total_incidences_tested": k5_subsets_tested * len(self.m6),
            "k5_uncovered_incidences": k5_uncovered,
            "k4_failing_incidences_count": k4_failing,
            "pigeonhole_k5_coverage_verified": k5_uncovered == 0,
        }


# ==============================================================================
# UNIFIED EVENT-26 ENGINE FACADE
# ==============================================================================


class UniversalObstructionCancellationEngine:
    """Unified Event-26 Universal Obstruction-Cancellation & Gorenstein Moduli Duality Engine."""

    def __init__(self) -> None:
        self.cy = CalabiYauJacobianEngine()
        self.fsd = FourierShadowDetector()
        self.rank_nullity = UniversalRankNullityCancellationEngine(self.cy, self.fsd)
        self.moduli_census = GorensteinModuliRankCensus(
            self.rank_nullity.m6, self.rank_nullity.m12, self.rank_nullity.m18
        )
        self.turan_coverage = TuranCoordinatePlaneCoverageEngine(
            self.rank_nullity.m6, self.rank_nullity.m12
        )

    def run_full_audit(self) -> Dict[str, Any]:
        rn = self.rank_nullity.run_audit()
        mc = self.moduli_census.run_audit()
        tc = self.turan_coverage.run_audit()

        return {
            "engine": "UniversalObstructionCancellationEngine",
            "event_id": 26,
            "universal_rank_nullity": rn,
            "gorenstein_moduli_census": mc,
            "turan_plane_coverage": tc,
            "honesty_boundary": {
                "GLOBAL_HODGE_CONJECTURE": "OPEN",
                "release_authorized": False,
                "theorem_progress": "UNKNOWN",
                "bridge_a_status": "ADVERSARIALLY_BLOCKED_OPEN_BRIDGE",
                "bridge_b_status": "ADVERSARIALLY_BLOCKED_OPEN_BRIDGE",
                "all_order_castelnuovo_mumford_bound_proved": False,
            },
        }


def main() -> None:
    hits = scan_forbidden(str(Path(__file__).resolve()))
    assert hits == [], f"Forbidden pattern hits: {hits}"

    engine = UniversalObstructionCancellationEngine()
    res = engine.run_full_audit()
    rn = res["universal_rank_nullity"]
    mc = res["gorenstein_moduli_census"]
    tc = res["turan_plane_coverage"]
    hb = res["honesty_boundary"]
    print("=" * 72)
    print("UNIVERSAL OBSTRUCTION-CANCELLATION & GORENSTEIN DUALITY ENGINE (EVENT 26)")
    print("=" * 72)
    print(
        f"[Universal Bounds]    R12 ker>={rn['universal_total_kernel_lower_bound']} "
        f"(dense u: rk={rn['dense_full_rank']}, ker={rn['dense_full_kernel_dim']}), "
        f"Band1>={rn['universal_band1_kernel_lower_bound']} ({rn['dense_band1_kernel_dim']}), "
        f"Band2>={rn['universal_band2_kernel_lower_bound']} ({rn['dense_band2_kernel_dim']})"
    )
    print(
        f"[Gorenstein Census]   partitions={mc['total_moduli_partitions']} "
        f"({mc['total_moduli_monomials']} modes), "
        f"rk in [{mc['global_min_rank']}, {mc['global_max_rank']}], "
        f"ker in [{mc['global_min_kernel_dim']}, {mc['global_max_kernel_dim']}], "
        f"duality={mc['gorenstein_complement_duality_verified_count']}/9"
    )
    print(
        f"[Turan Coverage K=5]  max_obstructed={tc['max_obstructed_planes_per_monomial']}, "
        f"min_surviving={tc['min_surviving_planes_per_monomial']}/20, "
        f"K=5 uncovered={tc['k5_uncovered_incidences']}/{tc['k5_total_incidences_tested']} "
        f"(K=4 fails={tc['k4_failing_incidences_count']})"
    )
    print(
        f"[Honesty Boundary]    Bridge A={hb['bridge_a_status']}, "
        f"Bridge B={hb['bridge_b_status']}, Global={hb['GLOBAL_HODGE_CONJECTURE']}, "
        f"release_authorized={hb['release_authorized']}"
    )


if __name__ == "__main__":
    main()
