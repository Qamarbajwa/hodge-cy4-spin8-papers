"""Exact rational and integer linear algebra engine for mathematical verification.

Replaces floating-point and heuristic rank approximations (e.g., numpy.linalg.matrix_rank,
scipy.linalg.svd) with exact Gaussian elimination, reduced row echelon form (RREF),
kernel basis computation, and fast cached subspace membership testing over Q.
"""

from __future__ import annotations
from fractions import Fraction
from typing import Dict, List, Sequence, Tuple, Union
import numpy as np


RationalNumber = Union[int, Fraction, float]


def _to_fraction(val: RationalNumber) -> Fraction:
    if isinstance(val, Fraction):
        return val
    if isinstance(val, (int, np.integer)):
        return Fraction(int(val), 1)
    if isinstance(val, (float, np.floating)):
        if float(val).is_integer():
            return Fraction(int(val), 1)
        return Fraction(val).limit_denominator(10**12)
    return Fraction(str(val))


def to_fraction_matrix(M: Union[Sequence[Sequence[RationalNumber]], np.ndarray]) -> List[List[Fraction]]:
    """Converts any 2D array-like structure into an exact matrix of Fractions."""
    if isinstance(M, np.ndarray):
        rows, cols = M.shape
        return [[_to_fraction(M[i, j]) for j in range(cols)] for i in range(rows)]
    return [[_to_fraction(val) for val in row] for row in M]


def exact_rref(
    M: Union[Sequence[Sequence[RationalNumber]], np.ndarray]
) -> Tuple[List[List[Fraction]], List[int]]:
    """Computes the Reduced Row Echelon Form (RREF) of matrix M over Q.

    Optimized for sparse matrices by skipping zero multipliers and zero elements.

    Returns:
        rref_matrix: The matrix in reduced row echelon form.
        pivot_columns: List of pivot column indices (length equals exact rank).
    """
    A = to_fraction_matrix(M)
    num_rows = len(A)
    if num_rows == 0:
        return [], []
    num_cols = len(A[0])
    if num_cols == 0:
        return [[] for _ in range(num_rows)], []

    r = 0
    c = 0
    pivot_cols: List[int] = []

    while r < num_rows and c < num_cols:
        pivot_row = None
        for i in range(r, num_rows):
            if A[i][c] != 0:
                pivot_row = i
                break
        if pivot_row is None:
            c += 1
            continue

        if pivot_row != r:
            A[r], A[pivot_row] = A[pivot_row], A[r]

        pivot_val = A[r][c]
        if pivot_val != 1:
            inv = Fraction(1, 1) / pivot_val
            for j in range(c, num_cols):
                if A[r][j] != 0:
                    A[r][j] *= inv

        # Track non-zero columns in pivot row for sparse elimination
        nz_cols = [j for j in range(c, num_cols) if A[r][j] != 0]

        for i in range(num_rows):
            if i != r and A[i][c] != 0:
                factor = A[i][c]
                for j in nz_cols:
                    A[i][j] -= factor * A[r][j]

        pivot_cols.append(c)
        r += 1
        c += 1

    return A, pivot_cols


def exact_matrix_rank(M: Union[Sequence[Sequence[RationalNumber]], np.ndarray]) -> int:
    """Computes the exact mathematical rank of matrix M over Q."""
    _, pivot_cols = exact_rref(M)
    return len(pivot_cols)


class ExactColumnSpan:
    """Pre-reduced exact column-space basis over Q for O(rank * nnz) membership testing."""

    def __init__(self, M: Union[Sequence[Sequence[RationalNumber]], np.ndarray]):
        mat = to_fraction_matrix(M)
        self.num_rows = len(mat)
        self.num_cols = len(mat[0]) if self.num_rows > 0 else 0
        # Build echelon basis over columns (treating columns as row vectors for fast pivot reduction)
        self.pivots: Dict[int, Dict[int, Fraction]] = {}

        for j in range(self.num_cols):
            col_vec = {i: mat[i][j] for i in range(self.num_rows) if mat[i][j] != 0}
            self._reduce_and_insert(col_vec)

    def _reduce(self, vec_dict: Dict[int, Fraction]) -> Dict[int, Fraction]:
        v = dict(vec_dict)
        # Reduce v against stored pivots
        # Sort pivot indices to reduce canonically
        for p_idx in sorted(self.pivots.keys()):
            if p_idx in v and v[p_idx] != 0:
                factor = v[p_idx]
                p_vec = self.pivots[p_idx]
                for k, p_val in p_vec.items():
                    new_val = v.get(k, Fraction(0, 1)) - factor * p_val
                    if new_val == 0:
                        v.pop(k, None)
                    else:
                        v[k] = new_val
        return v

    def _reduce_and_insert(self, vec_dict: Dict[int, Fraction]) -> bool:
        rem = self._reduce(vec_dict)
        if not rem:
            return False
        first_nz = min(rem.keys())
        inv = Fraction(1, 1) / rem[first_nz]
        norm_vec = {k: val * inv for k, val in rem.items()}
        self.pivots[first_nz] = norm_vec
        return True

    @property
    def rank(self) -> int:
        return len(self.pivots)

    def contains(self, vec: Union[Sequence[RationalNumber], np.ndarray]) -> bool:
        """Returns True iff `vec` lies in the exact rational column span."""
        v_dict = {}
        for i, val in enumerate(vec):
            fv = _to_fraction(val)
            if fv != 0:
                v_dict[i] = fv
        rem = self._reduce(v_dict)
        return len(rem) == 0


def exact_vector_in_span(
    subspace_cols: Union[Sequence[Sequence[RationalNumber]], np.ndarray],
    vec: Union[Sequence[RationalNumber], np.ndarray],
) -> bool:
    """Tests if `vec` lies in the exact column span of `subspace_cols` over Q."""
    span = ExactColumnSpan(subspace_cols)
    return span.contains(vec)


def exact_kernel_basis(
    M: Union[Sequence[Sequence[RationalNumber]], np.ndarray]
) -> List[List[Fraction]]:
    """Computes an exact basis of the rational nullspace (kernel) of M: {x in Q^n : M x = 0}."""
    rref_mat, pivot_cols = exact_rref(M)
    num_rows = len(rref_mat)
    if num_rows == 0:
        return []
    num_cols = len(rref_mat[0])

    pivot_set = set(pivot_cols)
    free_cols = [c for c in range(num_cols) if c not in pivot_set]

    kernel_basis: List[List[Fraction]] = []
    for free_c in free_cols:
        x = [Fraction(0, 1)] * num_cols
        x[free_c] = Fraction(1, 1)
        for r, pivot_c in enumerate(pivot_cols):
            x[pivot_c] = -rref_mat[r][free_c]
        kernel_basis.append(x)

    return kernel_basis
