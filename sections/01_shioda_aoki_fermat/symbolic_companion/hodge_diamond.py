"""Hodge Diamond and Cohomology Engine.

Computes exact Hodge numbers h^{p,q}(X) and primitive cohomology dimensions
for smooth projective hypersurfaces and complete intersections using Griffiths
residue calculus and the Jacobian / Milnor algebra.
"""

from typing import Dict, List, Tuple
from sympy import symbols, expand, Poly


def hypersurface_jacobian_hilbert_poly(dim_n: int, deg_d: int) -> List[int]:
    """Computes the coefficients of the Hilbert-Poincare series of the Jacobian ideal

    for a smooth degree d hypersurface X in P^{n+1}.
    P(T) = ((1 - T^{d-1}) / (1 - T))^{n+2} = (1 + T + ... + T^{d-2})^{n+2}
    """
    T = symbols("T")
    poly_factor = sum(T**k for k in range(deg_d - 1))
    full_poly = expand(poly_factor ** (dim_n + 2))
    p = Poly(full_poly, T)
    coeffs = p.all_coeffs()
    coeffs.reverse()  # coeffs[k] is coefficient of T^k
    return [int(c) for c in coeffs]


def hypersurface_primitive_hodge_numbers(dim_n: int, deg_d: int) -> Dict[Tuple[int, int], int]:
    """Computes primitive Hodge numbers h^{p, n-p}_prim(X) for a smooth degree d

    hypersurface of complex dimension n in P^{n+1}.
    By Griffiths residue theorem:
    h^{p, n-p}_prim(X) = dim (C[x_0, ..., x_{n+1}] / J(F))_{(n - p + 1)*d - (n + 2)}
    """
    coeffs = hypersurface_jacobian_hilbert_poly(dim_n, deg_d)
    max_deg = len(coeffs) - 1
    prim_hodge = {}

    for p in range(dim_n + 1):
        target_deg = (dim_n - p + 1) * deg_d - (dim_n + 2)
        if 0 <= target_deg <= max_deg:
            dim_val = coeffs[target_deg]
        else:
            dim_val = 0
        prim_hodge[(p, dim_n - p)] = dim_val

    return prim_hodge


def hypersurface_full_hodge_diamond(dim_n: int, deg_d: int) -> Dict[Tuple[int, int], int]:
    """Computes full Hodge diamond h^{p,q}(X) for a smooth degree d hypersurface

    in P^{n+1}.
    By Lefschetz hyperplane theorem:
    - For p + q != n:
        h^{p,p} = 1 for 0 <= 2p <= 2n, and h^{p,q} = 0 for p != q.
    - In middle dimension p + q = n:
        h^{p, n-p} = h^{p, n-p}_prim + (1 if p = n-p else 0).
    """
    prim = hypersurface_primitive_hodge_numbers(dim_n, deg_d)
    full_diamond = {}

    for k in range(2 * dim_n + 1):
        for p in range(k + 1):
            q = k - p
            if p > dim_n or q > dim_n:
                continue

            if k != dim_n:
                # Lefschetz hyperplane theorem: matches ambient P^{n+1}
                full_diamond[(p, q)] = 1 if (p == q) else 0
            else:
                # Middle dimension
                is_middle_even = (p == q and dim_n % 2 == 0)
                base = 1 if is_middle_even else 0
                full_diamond[(p, q)] = prim.get((p, q), 0) + base

    return full_diamond


def hodge_classes_dimension(dim_n: int, deg_d: int) -> int:
    """Returns the dimension of the space of Hodge classes Hdg^{2p}(X)

    in the middle dimension when n = 2p is even.
    """
    if dim_n % 2 != 0:
        raise ValueError(f"Middle dimension requires even n; got n={dim_n}")
    p = dim_n // 2
    diamond = hypersurface_full_hodge_diamond(dim_n, deg_d)
    return diamond.get((p, p), 0)


def print_hodge_diamond(dim_n: int, deg_d: int) -> str:
    """Formats the Hodge diamond nicely as a string."""
    diamond = hypersurface_full_hodge_diamond(dim_n, deg_d)
    lines = [f"=== Hodge Diamond for Hypersurface dim(X)={dim_n}, deg={deg_d} in P^{dim_n+1} ==="]
    for row in range(2 * dim_n + 1):
        row_entries = []
        for p in range(dim_n + 1):
            q = row - p
            if 0 <= q <= dim_n:
                row_entries.append(f"h^{p},{q}={diamond.get((p, q), 0)}")
        lines.append(f"k={row:2d}: " + " | ".join(row_entries))
    return "\n".join(lines)


if __name__ == "__main__":
    # Test on K3 surface (dim=2, deg=4)
    print(print_hodge_diamond(2, 4))
    print()
    # Test on Cubic Fourfold (dim=4, deg=3)
    print(print_hodge_diamond(4, 3))
    print()
    # Test on Quartic Fourfold (dim=4, deg=4)
    print(print_hodge_diamond(4, 4))
