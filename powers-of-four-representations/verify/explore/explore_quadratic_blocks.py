"""Finite checks, not a proof, for a density-(1-1/q) construction.

Omit [(qm)^2, (qm+1)^2-1], m >= 1. Exact mode uses integer polynomial
packing with a base exceeding every coefficient of the full cube.
FFT mode is a numerical screen and labels its results accordingly.
"""
import argparse
import json
from math import isqrt
from pathlib import Path
from time import perf_counter


def membership(limit, q):
    a = bytearray([1]) * (limit + 1)
    for k in range(q, isqrt(limit) + 1, q):
        start, stop = k * k, min((k + 1) ** 2, limit + 1)
        a[start:stop] = bytes(stop - start)
    return a


def exact_cube(a):
    # An ordered triple is fixed by its first two entries, so every
    # coefficient, including those past the truncation, is <= len(a)^2.
    # Consequently no base-B digit carries into the next coefficient.
    width = (len(a) ** 2).bit_length()
    width = (width + 7) // 8
    data = bytearray(len(a) * width)
    data[::width] = a
    polynomial = int.from_bytes(data, "little")
    cube = polynomial ** 3
    raw = cube.to_bytes((cube.bit_length() + 7) // 8, "little")
    coefficients = [int.from_bytes(raw[n * width:(n + 1) * width], "little")
                    for n in range(len(a))]
    return coefficients, {"coefficient_bytes": width,
                          "base": 1 << (8 * width),
                          "coefficient_upper_bound": len(a) ** 2}


def fft_cube(a):
    import numpy as np
    size = 1 << (3 * len(a) - 3).bit_length()
    v = np.fft.irfft(np.fft.rfft(np.asarray(a, dtype=float), size) ** 3,
                       size)[:len(a)]
    error = float(np.max(abs(v - np.rint(v))))
    return np.rint(v).astype(np.int64).tolist(), {
        "fft_size": size, "maximum_distance_to_integer": error,
        "warning": "Floating point rounding is not an exact certificate."}


def independent_small_check(a, r):
    limit = min(128, len(a) - 1)
    for n in range(limit + 1):
        count = sum(a[i] * a[j] * a[n - i - j]
                    for i in range(n + 1) for j in range(n - i + 1))
        assert r[n] == count, (n, r[n], count)


def report(limit, q, method, fill_prefix=0):
    start = perf_counter()
    a = membership(limit, q)
    a[:min(fill_prefix, len(a))] = bytes([1]) * min(fill_prefix, len(a))
    coefficients, details = (exact_cube(a) if method == "exact"
                             else fft_cube(a))
    independent_small_check(a, coefficients)
    differences = [coefficients[n + 1] - coefficients[n]
                   for n in range(limit)]
    failures = [(n, d) for n, d in enumerate(differences) if d <= 0]
    windows = []
    lo = 64
    while lo < limit:
        hi = min(2 * lo, limit)
        index = min(range(lo, hi), key=lambda n: differences[n] / (n + 1))
        windows.append({"first_n": lo, "last_n": hi - 1,
                        "minimum_ratio_index": index,
                        "difference": differences[index],
                        "ratio_to_n_plus_1": differences[index] / (index + 1)})
        lo = hi
    return {"q": q, "filled_prefix_length": fill_prefix,
            "natural_density_proved": f"{q-1}/{q}",
            "checked_differences_n": [0, limit - 1],
            "method": method, "method_details": details,
            "minimum_difference": min(differences),
            "nonpositive_difference_count": len(failures),
            "first_failures": failures[:10],
            "observed_prefix_density": sum(a) / len(a),
            "dyadic_windows": windows,
            "seconds": perf_counter() - start,
            "infinite_monotonicity_status": "UNPROVED"}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--limit", type=int, default=262144)
    parser.add_argument("--q", type=int, default=5)
    parser.add_argument("--method", choices=["exact", "fft"], default="exact")
    parser.add_argument("--fill-prefix", type=int, default=0)
    args = parser.parse_args()
    assert args.limit >= 2 and args.q >= 2 and args.fill_prefix >= 0
    result = report(args.limit, args.q, args.method, args.fill_prefix)
    suffix = f"-prefix{args.fill_prefix}" if args.fill_prefix else ""
    output = Path(__file__).with_name(
        f"quadratic-q{args.q}{suffix}-{args.method}-{args.limit}.json")
    output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
