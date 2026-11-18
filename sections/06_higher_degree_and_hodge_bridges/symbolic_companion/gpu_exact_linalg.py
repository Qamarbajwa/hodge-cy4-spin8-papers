"""RTX A2000 (8 GB VRAM) Float-Free Exact int64 CUDA Linear Algebra & Cyclotomic Sieve.

Strictly float-free: all GPU tensors use `dtype=torch.int64` with explicit VRAM cap
(6.0 GB ceiling on the 8 GB RTX A2000) and safe CPU fallback when CUDA is unavailable
in the calling interpreter.
"""

from __future__ import annotations

import time
from typing import Any, Dict, List, Sequence, Tuple

try:
    import torch  # type: ignore

    HAS_TORCH = True
except Exception:
    torch = None  # type: ignore
    HAS_TORCH = False


MAX_VRAM_BYTES = int(6.0 * (1024 ** 3))
DEFAULT_3_PRIMES = (65521, 1000000007, 1000000009)


def get_compute_device() -> str:
    if HAS_TORCH and torch.cuda.is_available():
        return "cuda:0"
    return "cpu"


def device_summary() -> Dict[str, Any]:
    if HAS_TORCH and torch.cuda.is_available():
        return {
            "device": "cuda:0",
            "gpu_name": torch.cuda.get_device_name(0),
            "torch_version": torch.__version__,
            "vram_limit_gb": 6.0,
        }
    return {
        "device": "cpu",
        "gpu_name": "CPU_FALLBACK",
        "torch_version": torch.__version__ if HAS_TORCH else "none",
        "vram_limit_gb": 0.0,
    }


def _cpu_modp_rank(mat: Sequence[Sequence[int]], p: int) -> int:
    if not mat or not mat[0]:
        return 0
    rows = [[int(x) % p for x in r] for r in mat]
    nr = len(rows)
    nc = len(rows[0])
    rk = 0
    for col in range(nc):
        piv = -1
        for i in range(rk, nr):
            if rows[i][col] != 0:
                piv = i
                break
        if piv < 0:
            continue
        rows[rk], rows[piv] = rows[piv], rows[rk]
        inv = pow(rows[rk][col], p - 2, p)
        rows[rk] = [(x * inv) % p for x in rows[rk]]
        prow = rows[rk]
        for i in range(nr):
            if i != rk and rows[i][col] != 0:
                fac = rows[i][col]
                rows[i] = [(rows[i][j] - fac * prow[j]) % p for j in range(nc)]
        rk += 1
        if rk == nr:
            break
    return rk


def gpu_modp_rank_with_stats(
    mat: Sequence[Sequence[int]], p: int = 65521
) -> Tuple[int, Dict[str, Any]]:
    """Computes exact rank of integer matrix `mat` over F_p on cuda:0 in `torch.int64`."""
    t0 = time.perf_counter()
    if not mat or not mat[0]:
        info = device_summary()
        info.update({"elapsed_ms": 0.0, "peak_vram_mb": 0.0, "shape": [len(mat), 0]})
        return 0, info

    n_rows = len(mat)
    n_cols = len(mat[0])
    est_bytes = n_rows * n_cols * 8 * 2
    if est_bytes > MAX_VRAM_BYTES:
        raise MemoryError(
            f"Matrix ({n_rows}x{n_cols}) estimated {est_bytes} bytes exceeds 6.0 GB VRAM ceiling."
        )

    dev = get_compute_device()
    if not HAS_TORCH:
        rk = _cpu_modp_rank(mat, p)
        info = device_summary()
        info.update({
            "elapsed_ms": round((time.perf_counter() - t0) * 1000.0, 3),
            "peak_vram_mb": 0.0,
            "shape": [n_rows, n_cols],
        })
        return rk, info

    if dev == "cuda:0":
        _ = torch.empty(1, dtype=torch.int64, device="cuda:0")
        torch.cuda.reset_peak_memory_stats(0)

    M = torch.tensor(mat, dtype=torch.int64, device=dev) % p
    assert M.dtype == torch.int64

    rk = 0
    for col in range(n_cols):
        if rk >= n_rows:
            break
        sub = M[rk:, col]
        nz = torch.nonzero(sub, as_tuple=False)
        if nz.numel() == 0:
            continue
        piv_idx = rk + int(nz[0].item())
        if piv_idx != rk:
            tmp = M[rk].clone()
            M[rk] = M[piv_idx]
            M[piv_idx] = tmp
        piv_val = int(M[rk, col].item()) % p
        inv = pow(piv_val, p - 2, p)
        M[rk] = (M[rk] * inv) % p
        piv_row = M[rk]

        mask = M[:, col] != 0
        mask[rk] = False
        if bool(torch.any(mask).item()):
            factors = M[mask, col]
            M[mask] = (M[mask] - factors.unsqueeze(1) * piv_row.unsqueeze(0)) % p

        rk += 1

    if dev == "cuda:0":
        torch.cuda.synchronize(0)
        peak_mb = round(torch.cuda.max_memory_allocated(0) / (1024.0 * 1024.0), 3)
    else:
        peak_mb = 0.0

    elapsed_ms = round((time.perf_counter() - t0) * 1000.0, 3)
    info = device_summary()
    info.update({
        "elapsed_ms": elapsed_ms,
        "peak_vram_mb": peak_mb,
        "shape": [n_rows, n_cols],
        "dtype": str(M.dtype),
    })
    return rk, info


def gpu_modp_rank(mat: Sequence[Sequence[int]], p: int = 65521) -> int:
    rk, _ = gpu_modp_rank_with_stats(mat, p=p)
    return rk


def gpu_crt_3prime_rank(
    mat: Sequence[Sequence[int]],
    primes: Tuple[int, int, int] = DEFAULT_3_PRIMES,
) -> Dict[str, Any]:
    """Runs `gpu_modp_rank` across 3 primes (`<= 10^9 + 9`, safe in int64) on cuda:0."""
    t0 = time.perf_counter()
    prime_ranks: Dict[str, int] = {}
    max_peak = 0.0
    last_info: Dict[str, Any] = {}
    for p in primes:
        rk, info = gpu_modp_rank_with_stats(mat, p=p)
        prime_ranks[str(p)] = rk
        last_info = info
        if info["peak_vram_mb"] > max_peak:
            max_peak = info["peak_vram_mb"]
    vals = list(prime_ranks.values())
    total_ms = round((time.perf_counter() - t0) * 1000.0, 3)
    return {
        "rank": max(vals) if vals else 0,
        "prime_ranks": prime_ranks,
        "agreement": len(set(vals)) == 1,
        "device": last_info.get("device", get_compute_device()),
        "gpu_name": last_info.get("gpu_name", "CPU_FALLBACK"),
        "peak_vram_mb": max_peak,
        "elapsed_ms": total_ms,
    }


def gpu_filter_hodge22_batch(
    tuples_list: Sequence[Sequence[int]],
    units_list: Sequence[int],
    m: int,
    target_weight: int = 3,
) -> Tuple[List[Tuple[int, ...]], Dict[str, Any]]:
    """Evaluates Galois-invariant Hodge sum across all units in parallel in `int64` VRAM."""
    t0 = time.perf_counter()
    if not tuples_list:
        info = device_summary()
        info.update({"elapsed_ms": 0.0, "peak_vram_mb": 0.0, "input_count": 0, "matched_count": 0})
        return [], info

    dev = get_compute_device()
    if not HAS_TORCH:
        target = target_weight * m
        matched = [
            tuple(int(x) for x in r)
            for r in tuples_list
            if all(sum((u * x) % m for x in r) == target for u in units_list)
        ]
        info = device_summary()
        info.update({
            "elapsed_ms": round((time.perf_counter() - t0) * 1000.0, 3),
            "peak_vram_mb": 0.0,
            "input_count": len(tuples_list),
            "matched_count": len(matched),
        })
        return matched, info

    if dev == "cuda:0":
        _ = torch.empty(1, dtype=torch.int64, device="cuda:0")
        torch.cuda.reset_peak_memory_stats(0)

    t_gpu = torch.tensor(tuples_list, dtype=torch.int64, device=dev)
    u_gpu = torch.tensor(units_list, dtype=torch.int64, device=dev)
    assert t_gpu.dtype == torch.int64 and u_gpu.dtype == torch.int64

    target = target_weight * m
    # Evaluate ((t_gpu[B,1,K] * u_gpu[1,U,1]) % m).sum(dim=-1) == target across all U
    prod = (t_gpu.unsqueeze(1) * u_gpu.view(1, -1, 1)) % m
    ok_all = (prod.sum(dim=-1) == target).all(dim=-1)
    idx = torch.nonzero(ok_all, as_tuple=False).squeeze(-1).tolist()
    matched = [tuple(int(x) for x in tuples_list[i]) for i in idx]

    if dev == "cuda:0":
        torch.cuda.synchronize(0)
        peak_mb = round(torch.cuda.max_memory_allocated(0) / (1024.0 * 1024.0), 3)
    else:
        peak_mb = 0.0

    info = device_summary()
    info.update({
        "elapsed_ms": round((time.perf_counter() - t0) * 1000.0, 3),
        "peak_vram_mb": peak_mb,
        "input_count": len(tuples_list),
        "matched_count": len(matched),
    })
    return matched, info


def run_benchmark() -> Dict[str, Any]:
    """Quick self-test & benchmark on `cuda:0`."""
    # Benchmark rank of a 1200x1200 Band-diagonal + sparse perturbation matrix over 3 primes
    n = 1200
    rows = [[0] * n for _ in range(n)]
    for i in range(n):
        rows[i][i] = (i + 1) % 65521
        if i + 1 < n:
            rows[i][i + 1] = 7
        if i + 5 < n:
            rows[i][i + 5] = -3
    crt_res = gpu_crt_3prime_rank(rows)

    sample_tuples = [
        [1, 6, 11, 16, 20, 21],
        [2, 7, 12, 15, 17, 22],
        [1, 1, 1, 1, 1, 2],
        [3, 8, 10, 13, 18, 23],
    ]
    units_25 = [t for t in range(1, 25) if t % 5 != 0]
    matched, filt_info = gpu_filter_hodge22_batch(sample_tuples, units_25, 25, target_weight=3)
    return {
        "device_summary": device_summary(),
        "crt_3prime_1200x1200_benchmark": crt_res,
        "hodge22_batch_filter_test": {
            "matched": [list(x) for x in matched],
            "stats": filt_info,
        },
    }


if __name__ == "__main__":
    import json

    print(json.dumps(run_benchmark(), indent=2))
