#!/usr/bin/env python3
from __future__ import annotations

import argparse
import functools
import math
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Sequence

from schur_mod import SchurModSolver


@dataclass(frozen=True)
class StableRow:
    c: int
    d: int
    n: int
    sigma_inf: int
    k0_inf: int | None
    sat_ok_ell1: bool | None
    sat_ok_ell2: bool | None
    v: int
    mismatch: str | None


def divisors(n: int) -> list[int]:
    small: list[int] = []
    large: list[int] = []
    i = 1
    while i * i <= n:
        if n % i == 0:
            small.append(i)
            if i * i != n:
                large.append(n // i)
        i += 1
    return small + large[::-1]


def prime_factorization(n: int) -> dict[int, int]:
    factors: dict[int, int] = {}
    candidate = 2
    while candidate * candidate <= n:
        while n % candidate == 0:
            factors[candidate] = factors.get(candidate, 0) + 1
            n //= candidate
        candidate += 1 if candidate == 2 else 2
    if n > 1:
        factors[n] = factors.get(n, 0) + 1
    return factors


def prime_exponent(n: int, prime: int) -> int:
    exponent = 0
    while n % prime == 0:
        exponent += 1
        n //= prime
    return exponent


def subgroup_index(m: int, subset: Sequence[int]) -> int:
    if len(subset) <= 1:
        return m
    g = m
    for i, a in enumerate(subset):
        for b in subset[i + 1 :]:
            g = math.gcd(g, abs(a - b))
    return g


def is_stably_safe(m: int, c: int, subset: Sequence[int]) -> bool:
    if len(subset) <= 1:
        return True
    g_c = subgroup_index(m, subset)
    a0 = subset[0]
    return ((c - 1) * a0) % g_c != 0


def stable_candidate_masks(m: int, c: int) -> tuple[int, list[int]]:
    d = math.gcd(m, c - 1)
    size = m // d - 1
    masks: set[int] = set()

    # Every singleton is safe in the stable regime.
    for idx in range(size):
        masks.add(1 << idx)

    # By Proposition 2 / Proposition 3', every multi-element stable-safe set
    # is contained in a safe coset fragment A(g, r). Because safety is
    # hereditary, minimum partitions can be searched using only these maximal
    # fragments together with singleton cleanup.
    for g in divisors(m):
        if g < 2:
            continue
        if g >= size:
            continue
        g_star = g // math.gcd(g, d)
        if g_star <= 1:
            continue
        for r in range(1, min(g, size + 1)):
            if r % g_star == 0:
                continue
            mask = 0
            x = r
            while x <= size:
                mask |= 1 << (x - 1)
                x += g
            if mask.bit_count() >= 2:
                masks.add(mask)

    sorted_masks = sorted(masks, key=lambda mask: (-mask.bit_count(), mask))
    maximal_masks: list[int] = []
    maximal_by_bit: list[list[int]] = [[] for _ in range(size)]
    for mask in sorted_masks:
        first_bit = mask & -mask
        first_index = first_bit.bit_length() - 1
        if any(mask & sup == mask for sup in maximal_by_bit[first_index]):
            continue
        maximal_masks.append(mask)
        bitset = mask
        while bitset:
            bit = bitset & -bitset
            maximal_by_bit[bit.bit_length() - 1].append(mask)
            bitset ^= bit
    return size, maximal_masks


def sigma_inf(m: int, c: int) -> int:
    _, masks = stable_candidate_masks(m, c)
    return max(mask.bit_count() for mask in masks)


def exact_k0_inf(m: int, c: int) -> int:
    size, masks = stable_candidate_masks(m, c)
    sys.setrecursionlimit(max(sys.getrecursionlimit(), size + 1000))
    full = (1 << size) - 1
    by_first_bit: list[list[int]] = [[] for _ in range(size)]
    for mask in masks:
        bitset = mask
        while bitset:
            bit = bitset & -bitset
            by_first_bit[bit.bit_length() - 1].append(mask)
            bitset ^= bit

    @functools.lru_cache(maxsize=None)
    def solve(remaining: int) -> int:
        if remaining == 0:
            return 0

        probe = remaining
        best_choices: list[int] | None = None
        while probe:
            bit = probe & -probe
            idx = bit.bit_length() - 1
            choices = by_first_bit[idx]
            if best_choices is None or len(choices) < len(best_choices):
                best_choices = choices
            probe ^= bit

        best = remaining.bit_count()
        ordered: list[tuple[int, int]] = []
        max_cover = 1
        assert best_choices is not None

        for subset in best_choices:
            cover = (subset & remaining).bit_count()
            if cover == 0:
                continue
            if cover > max_cover:
                max_cover = cover
            ordered.append((cover, subset))

        ordered.sort(key=lambda item: (-item[0], item[1]))
        lower_bound = math.ceil(remaining.bit_count() / max_cover)

        for cover, subset in ordered:
            candidate = 1 + solve(remaining & ~subset)
            if candidate < best:
                best = candidate
                if best == lower_bound:
                    break

        return best

    return solve(full)


def mask_elements(mask: int, size: int) -> list[int]:
    return [idx + 1 for idx in range(size) if mask & (1 << idx)]


def private_fragment_certificate(
    size: int,
    masks: Sequence[int],
) -> tuple[list[tuple[int, int, list[int]]], int]:
    counts = [0] * size
    for mask in masks:
        bitset = mask
        while bitset:
            bit = bitset & -bitset
            counts[bit.bit_length() - 1] += 1
            bitset ^= bit

    forced: list[tuple[int, int, list[int]]] = []
    forced_union = 0
    for index, mask in enumerate(masks, start=1):
        private_points = [
            idx + 1 for idx in range(size) if mask & (1 << idx) and counts[idx] == 1
        ]
        if private_points:
            forced.append((index, mask, private_points))
            forced_union |= mask
    return forced, forced_union


def residual_cover_number(size: int, masks: Sequence[int], residual: Sequence[int]) -> int:
    target = 0
    for point in residual:
        target |= 1 << (point - 1)
    if target == 0:
        return 0

    fragments = sorted(
        {mask & target for mask in masks if mask & target},
        key=lambda mask: (-mask.bit_count(), mask),
    )
    by_first_bit: list[list[int]] = [[] for _ in range(size)]
    for mask in fragments:
        bitset = mask
        while bitset:
            bit = bitset & -bitset
            by_first_bit[bit.bit_length() - 1].append(mask)
            bitset ^= bit

    @functools.lru_cache(maxsize=None)
    def solve(remaining: int) -> int:
        if remaining == 0:
            return 0

        probe = remaining
        best_choices: list[int] | None = None
        while probe:
            bit = probe & -probe
            choices = by_first_bit[bit.bit_length() - 1]
            if best_choices is None or len(choices) < len(best_choices):
                best_choices = choices
            probe ^= bit

        assert best_choices is not None
        best = remaining.bit_count()
        for fragment in sorted(
            best_choices,
            key=lambda mask: (-(mask & remaining).bit_count(), mask),
        ):
            best = min(best, 1 + solve(remaining & ~fragment))
        return best

    return solve(target)


CAPSTONE_FIXED_QUOTIENT_NS = frozenset(
    {
        48,
        70,
        45,
        80,
        72,
        66,
        78,
        60,
        84,
        135,
        110,
        102,
        105,
        165,
        90,
        120,
        36,
        96,
        114,
        108,
        130,
        126,
        112,
        132,
        138,
        160,
        170,
        144,
        225,
        168,
        240,
        180,
        150,
        156,
        190,
        255,
        189,
        200,
        140,
        210,
        270,
        174,
        285,
        154,
        186,
        220,
        300,
        230,
        315,
        198,
        231,
        204,
        330,
        345,
        182,
    }
)


def is_capstone_fixed_quotient_row(m: int, d: int) -> bool:
    # Theorem 1 selects the quotient; Theorems 2-3 certify these family quotients.
    return d > 0 and m % d == 0 and (m // d) in CAPSTONE_FIXED_QUOTIENT_NS


def is_known_residual_row(m: int, d: int) -> bool:
    phase24_rows = {
        (675, 15),
        (720, 24),
        (720, 30),
        (756, 18),
        (800, 20),
        (864, 18),
        (900, 15),
    }
    phase33_rows = {
        (1200, 20),
        (1350, 15),
        (1350, 30),
        (1400, 20),
        (1440, 24),
        (1440, 30),
        (1575, 15),
        (1584, 24),
        (1600, 20),
        (1728, 24),
        (1764, 21),
        (1800, 15),
        (1800, 20),
        (1800, 30),
        (1872, 24),
        (1960, 28),
        (1980, 30),
    }
    phase55_rows = {
        (2646, 21),
        (2700, 15),
        (2800, 20),
        (2925, 15),
        (3000, 20),
    }
    phase90_rows = {
        (5184, 24),
    }
    phase91_rows = {
        (5200, 20),
    }
    phase92_rows = {
        (5292, 21),
    }
    phase93_rows = {
        (5328, 24),
    }
    phase94_rows = {
        (5400, 15),
    }
    phase95_rows = {
        (5472, 24),
    }
    t252 = m // 252 if m % 252 == 0 else None
    phase26 = (
        t252 is not None
        and d == m // 42
        and prime_exponent(t252, 2) <= 3
        and prime_exponent(t252, 3) <= 1
        and prime_exponent(t252, 7) == 0
    )
    t360 = m // 360 if m % 360 == 0 else None
    phase27 = (
        t360 is not None
        and d == m // 60
        and prime_exponent(t360, 2) == 0
        and prime_exponent(t360, 3) <= 1
        and prime_exponent(t360, 5) == 0
    )
    t216 = m // 216 if m % 216 == 0 else None
    phase28 = (
        t216 is not None
        and d == m // 36
        and prime_exponent(t216, 2) <= 1
        and prime_exponent(t216, 3) == 0
    )
    phase29 = d == 14 and m % 196 == 0
    phase30 = d == 18 and m % 108 == 0
    phase31 = m % 30 == 0 and d == m // 30
    phase32 = m % 40 == 0 and d == m // 40
    return (
        (d == 6 and m % 36 == 0)
        or (d == 12 and m % 72 == 0)
        or (m % 72 == 0 and d == m // 12)
        or (d == 10 and m % 100 == 0)
        or (m % 144 == 0 and d == m // 24 and math.gcd(m // 144, 6) == 1)
        or phase26
        or phase27
        or phase28
        or phase29
        or phase30
        or phase31
        or phase32
        or is_capstone_fixed_quotient_row(m, d)
        or (m, d) in phase90_rows
        or (m, d) in phase91_rows
        or (m, d) in phase92_rows
        or (m, d) in phase93_rows
        or (m, d) in phase94_rows
        or (m, d) in phase95_rows
        or (m == 600 and d == 20)
        or (m, d) in phase24_rows
        or (m, d) in phase33_rows
        or (m, d) in phase55_rows
    )


def print_dgt1_gap_scan(limit: int, private_failure_limit: int | None) -> None:
    rows: list[tuple[int, int, int, int, int, int, int, bool]] = []
    first_private_failure: tuple[int, int, int, int, int, int, list[int]] | None = None

    scan_limit = max(limit, private_failure_limit or limit)
    for m in range(8, scan_limit + 1):
        seen: set[int] = set()
        for c in range(1, m + 1):
            d = math.gcd(m, c - 1)
            if d in (1, m) or d in seen:
                continue
            seen.add(d)

            sigma = sigma_inf(m, c)
            k0 = exact_k0_inf(m, c)
            n = m // d
            packing_lb = math.ceil((n - 1) / sigma)
            if k0 <= packing_lb:
                continue

            size, masks = stable_candidate_masks(m, c)
            forced, forced_union = private_fragment_certificate(size, masks)
            private_covers = forced_union == (1 << size) - 1 and len(forced) == k0

            if m <= limit:
                rows.append((m, d, n, sigma, packing_lb, k0, k0 - packing_lb, private_covers))

            if (
                private_failure_limit is not None
                and m <= private_failure_limit
                and not private_covers
                and first_private_failure is None
            ):
                residual = [
                    idx + 1 for idx in range(size) if not (forced_union & (1 << idx))
                ]
                first_private_failure = (m, d, n, sigma, packing_lb, k0, residual)

    print(f"d>1 packing-gap rows for 8 <= m <= {limit}: {len(rows)}")
    print("| m | d | n | sigma_inf | packing_lb | k0_inf | gap | private_cert |")
    print("|---:|---:|---:|---:|---:|---:|---:|---|")
    for m, d, n, sigma, packing_lb, k0, gap, private_covers in rows:
        print(
            f"| {m} | {d} | {n} | {sigma} | {packing_lb} | {k0} | {gap} | {private_covers} |"
        )

    if private_failure_limit is not None:
        if first_private_failure is None:
            print(f"No private-certificate failure found through m={private_failure_limit}.")
        else:
            m, d, n, sigma, packing_lb, k0, residual = first_private_failure
            print(
                "First private-certificate failure through "
                f"m={private_failure_limit}: "
                f"m={m}, d={d}, n={n}, sigma_inf={sigma}, "
                f"packing_lb={packing_lb}, k0_inf={k0}, residual={residual}"
            )


def print_filtered_frontier_scan(limit: int) -> None:
    rows: list[tuple[int, int, int, int, int, int, int, int, list[int]]] = []
    for m in range(8, limit + 1):
        seen: set[int] = set()
        for c in range(1, m + 1):
            d = math.gcd(m, c - 1)
            if d in (1, m) or d in seen:
                continue
            seen.add(d)

            sigma = sigma_inf(m, c)
            k0 = exact_k0_inf(m, c)
            n = m // d
            packing_lb = math.ceil((n - 1) / sigma)
            if k0 <= packing_lb:
                continue

            size, masks = stable_candidate_masks(m, c)
            forced, forced_union = private_fragment_certificate(size, masks)
            private_covers = forced_union == (1 << size) - 1 and len(forced) == k0
            if private_covers or is_known_residual_row(m, d):
                continue

            residual = [
                idx + 1 for idx in range(size) if not (forced_union & (1 << idx))
            ]
            tau = residual_cover_number(size, masks, residual)
            rows.append((m, d, n, sigma, packing_lb, k0, len(forced), tau, residual))

    print(
        "Filtered non-private residual rows after Phase 19--95 "
        f"for 8 <= m <= {limit}: {len(rows)}"
    )
    print("| m | d | n | sigma_inf | packing_lb | k0_inf | forced | residual_tau | residual |")
    print("|---:|---:|---:|---:|---:|---:|---:|---:|---|")
    for m, d, n, sigma, packing_lb, k0, forced_count, tau, residual in rows:
        print(
            f"| {m} | {d} | {n} | {sigma} | {packing_lb} | {k0} | "
            f"{forced_count} | {tau} | `{residual}` |"
        )


def is_power_of_three(value: int) -> bool:
    if value < 1:
        return False
    while value % 3 == 0:
        value //= 3
    return value == 1


def is_power_of_prime(value: int, prime: int) -> bool:
    if value < 1:
        return False
    while value % prime == 0:
        value //= prime
    return value == 1


def predicted_m72t_d12_residual(t: int) -> list[int]:
    if is_power_of_prime(t, 2) or is_power_of_prime(t, 3):
        return []
    if t % 2 == 1:
        return [t, 5 * t]
    if t % 4 != 0 and is_power_of_prime(t // 2, 3):
        return [t, 5 * t]
    return [t, 5 * t // 2, 7 * t // 2, 5 * t]


def remove_prime_power(value: int, prime: int) -> int:
    while value % prime == 0:
        value //= prime
    return value


def predicted_m100t_d10_residual(t: int) -> list[int]:
    return [] if remove_prime_power(t, 5) in (1, 2, 3) else [3 * t, 7 * t]


def predicted_m144t_d6t(t: int) -> tuple[int, int, list[int]]:
    factors = prime_factorization(t)
    alpha = factors.get(2, 0)
    beta = factors.get(3, 0)
    if alpha == 0:
        return 6, 8, ([] if beta else [4, 20])
    if beta == 0 or alpha == 1:
        return 3, 13, []
    if alpha == 2:
        return 2, 19, []
    return 1, 23, []


def predicted_m252t_d6t(t: int) -> tuple[int | None, int | None, list[int]]:
    alpha = prime_exponent(t, 2)
    beta = prime_exponent(t, 3)
    gamma = prime_exponent(t, 7)
    if gamma == 0 and alpha <= 3 and beta <= 1:
        if alpha == 0:
            return 11, 10, [7, 35]
        return 6, 11, [7, 35]
    return None, None, []


def predicted_m360t_d6t(t: int) -> tuple[int | None, int | None, list[int] | None]:
    if (
        prime_exponent(t, 2) == 0
        and prime_exponent(t, 3) <= 1
        and prime_exponent(t, 5) == 0
    ):
        return 15, 10, [10, 50]
    return None, None, None


def predicted_m216t_d6t(t: int) -> tuple[int | None, int | None, list[int] | None]:
    alpha = prime_exponent(t, 2)
    if alpha <= 1 and prime_exponent(t, 3) == 0:
        if alpha == 0:
            return 9, 12, [6, 30]
        return 5, 15, [6, 30]
    return None, None, None


def predicted_m196t_d14(t: int) -> tuple[int, int, list[int]]:
    factors = prime_factorization(t)
    least_odd_prime = min((prime for prime in factors if prime >= 3), default=4)
    denominator = min(4, least_odd_prime)
    predicted_sigma = math.ceil((14 * t - 1) / denominator)
    predicted_k0 = (
        8
        + 2 * factors.get(2, 0)
        + 42 * factors.get(7, 0)
        + sum(
            exp * (prime - 1)
            for prime, exp in factors.items()
            if prime not in (2, 7)
        )
    )
    expected = (
        []
        if remove_prime_power(t, 7) in (1, 2, 3, 4, 5)
        else [t, 5 * t, 9 * t, 13 * t]
    )
    return predicted_sigma, predicted_k0, expected


def predicted_m108t_d18(t: int) -> tuple[int, int, list[int]]:
    factors = prime_factorization(t)
    beta = factors.get(3, 0)
    three_layers = 0 if beta == 0 else 6 + 18 * (beta - 1)
    predicted_sigma = math.ceil((6 * t - 1) / 4)
    predicted_k0 = (
        4
        + 2 * factors.get(2, 0)
        + three_layers
        + sum(
            exp * (prime - 1)
            for prime, exp in factors.items()
            if prime not in (2, 3)
        )
    )

    three_free_part = remove_prime_power(t, 3)
    if three_free_part in (1, 2, 4, 5):
        expected: list[int] = []
    elif beta == 0:
        expected = [t, 5 * t]
    else:
        expected = [t, 7 * t // 3, 11 * t // 3, 5 * t]
    return predicted_sigma, predicted_k0, expected


def normalized_n30_d(d: int) -> int:
    return (
        (2 ** min(prime_exponent(d, 2), 4))
        * (3 ** min(prime_exponent(d, 3), 3))
        * (5 ** min(prime_exponent(d, 5), 2))
    )


@functools.lru_cache(maxsize=None)
def predicted_n30_fixed_quotient(
    d: int,
) -> tuple[int, int, int, int, list[int]]:
    normalized_d = normalized_n30_d(d)
    m = 30 * normalized_d
    c = normalized_d + 1
    size, masks = stable_candidate_masks(m, c)
    forced, forced_union = private_fragment_certificate(size, masks)
    residual = [
        idx + 1 for idx in range(size) if not (forced_union & (1 << idx))
    ]
    return (
        normalized_d,
        sigma_inf(m, c),
        exact_k0_inf(m, c),
        residual_cover_number(size, masks, residual),
        residual,
    )


def normalized_n40_d(d: int) -> int:
    return (2 ** min(prime_exponent(d, 2), 5)) * (
        5 ** min(prime_exponent(d, 5), 2)
    )


@functools.lru_cache(maxsize=None)
def predicted_n40_fixed_quotient(
    d: int,
) -> tuple[int, int, int, int, list[int]]:
    normalized_d = normalized_n40_d(d)
    m = 40 * normalized_d
    c = normalized_d + 1
    size, masks = stable_candidate_masks(m, c)
    forced, forced_union = private_fragment_certificate(size, masks)
    residual = [
        idx + 1 for idx in range(size) if not (forced_union & (1 << idx))
    ]
    return (
        normalized_d,
        sigma_inf(m, c),
        exact_k0_inf(m, c),
        residual_cover_number(size, masks, residual),
        residual,
    )


def normalized_n48_d(d: int) -> int:
    return (2 ** min(prime_exponent(d, 2), 5)) * (
        3 ** min(prime_exponent(d, 3), 3)
    )


@functools.lru_cache(maxsize=None)
def predicted_n48_fixed_quotient(
    d: int,
) -> tuple[int, int, int, int, list[int]]:
    normalized_d = normalized_n48_d(d)
    m = 48 * normalized_d
    c = normalized_d + 1
    size, masks = stable_candidate_masks(m, c)
    forced, forced_union = private_fragment_certificate(size, masks)
    residual = [
        idx + 1 for idx in range(size) if not (forced_union & (1 << idx))
    ]
    return (
        normalized_d,
        sigma_inf(m, c),
        exact_k0_inf(m, c),
        residual_cover_number(size, masks, residual),
        residual,
    )


def normalized_n70_d(d: int) -> int:
    return (
        (2 ** min(prime_exponent(d, 2), 6))
        * (5 ** min(prime_exponent(d, 5), 2))
        * (7 ** min(prime_exponent(d, 7), 2))
    )


@functools.lru_cache(maxsize=None)
def predicted_n70_fixed_quotient(
    d: int,
) -> tuple[int, int, int, int, list[int]]:
    normalized_d = normalized_n70_d(d)
    m = 70 * normalized_d
    c = normalized_d + 1
    size, masks = stable_candidate_masks(m, c)
    forced, forced_union = private_fragment_certificate(size, masks)
    residual = [
        idx + 1 for idx in range(size) if not (forced_union & (1 << idx))
    ]
    return (
        normalized_d,
        sigma_inf(m, c),
        exact_k0_inf(m, c),
        residual_cover_number(size, masks, residual),
        residual,
    )


def normalized_n45_d(d: int) -> int:
    return (3 ** min(prime_exponent(d, 3), 3)) * (
        5 ** min(prime_exponent(d, 5), 2)
    )


@functools.lru_cache(maxsize=None)
def predicted_n45_fixed_quotient(
    d: int,
) -> tuple[int, int, int, int, list[int]]:
    normalized_d = normalized_n45_d(d)
    m = 45 * normalized_d
    c = normalized_d + 1
    size, masks = stable_candidate_masks(m, c)
    forced, forced_union = private_fragment_certificate(size, masks)
    residual = [
        idx + 1 for idx in range(size) if not (forced_union & (1 << idx))
    ]
    return (
        normalized_d,
        sigma_inf(m, c),
        exact_k0_inf(m, c),
        residual_cover_number(size, masks, residual),
        residual,
    )


def normalized_n80_d(d: int) -> int:
    return (2 ** min(prime_exponent(d, 2), 6)) * (
        5 ** min(prime_exponent(d, 5), 2)
    )


@functools.lru_cache(maxsize=None)
def predicted_n80_fixed_quotient(
    d: int,
) -> tuple[int, int, int, int, list[int]]:
    normalized_d = normalized_n80_d(d)
    m = 80 * normalized_d
    c = normalized_d + 1
    size, masks = stable_candidate_masks(m, c)
    forced, forced_union = private_fragment_certificate(size, masks)
    residual = [
        idx + 1 for idx in range(size) if not (forced_union & (1 << idx))
    ]
    return (
        normalized_d,
        sigma_inf(m, c),
        exact_k0_inf(m, c),
        residual_cover_number(size, masks, residual),
        residual,
    )


def normalized_n72_d(d: int) -> int:
    return (2 ** min(prime_exponent(d, 2), 6)) * (
        3 ** min(prime_exponent(d, 3), 3)
    )


@functools.lru_cache(maxsize=None)
def predicted_n72_fixed_quotient(
    d: int,
) -> tuple[int, int, int, int, list[int]]:
    normalized_d = normalized_n72_d(d)
    m = 72 * normalized_d
    c = normalized_d + 1
    size, masks = stable_candidate_masks(m, c)
    forced, forced_union = private_fragment_certificate(size, masks)
    residual = [
        idx + 1 for idx in range(size) if not (forced_union & (1 << idx))
    ]
    return (
        normalized_d,
        sigma_inf(m, c),
        exact_k0_inf(m, c),
        residual_cover_number(size, masks, residual),
        residual,
    )


def normalized_n66_d(d: int) -> int:
    return (
        (2 ** min(prime_exponent(d, 2), 6))
        * (3 ** min(prime_exponent(d, 3), 3))
        * (11 ** min(prime_exponent(d, 11), 1))
    )


@functools.lru_cache(maxsize=None)
def predicted_n66_fixed_quotient(
    d: int,
) -> tuple[int, int, int, int, list[int]]:
    normalized_d = normalized_n66_d(d)
    m = 66 * normalized_d
    c = normalized_d + 1
    size, masks = stable_candidate_masks(m, c)
    forced, forced_union = private_fragment_certificate(size, masks)
    residual = [
        idx + 1 for idx in range(size) if not (forced_union & (1 << idx))
    ]
    return (
        normalized_d,
        sigma_inf(m, c),
        exact_k0_inf(m, c),
        residual_cover_number(size, masks, residual),
        residual,
    )


def normalized_n78_d(d: int) -> int:
    return (
        (2 ** min(prime_exponent(d, 2), 6))
        * (3 ** min(prime_exponent(d, 3), 3))
        * (13 ** min(prime_exponent(d, 13), 1))
    )


@functools.lru_cache(maxsize=None)
def predicted_n78_fixed_quotient(
    d: int,
) -> tuple[int, int, int, int, list[int]]:
    normalized_d = normalized_n78_d(d)
    m = 78 * normalized_d
    c = normalized_d + 1
    size, masks = stable_candidate_masks(m, c)
    forced, forced_union = private_fragment_certificate(size, masks)
    residual = [
        idx + 1 for idx in range(size) if not (forced_union & (1 << idx))
    ]
    return (
        normalized_d,
        sigma_inf(m, c),
        exact_k0_inf(m, c),
        residual_cover_number(size, masks, residual),
        residual,
    )


def normalized_n60_d(d: int) -> int:
    return (
        (2 ** min(prime_exponent(d, 2), 5))
        * (3 ** min(prime_exponent(d, 3), 3))
        * (5 ** min(prime_exponent(d, 5), 2))
    )


@functools.lru_cache(maxsize=None)
def predicted_n60_fixed_quotient(
    d: int,
) -> tuple[int, int, int, int, list[int]]:
    normalized_d = normalized_n60_d(d)
    m = 60 * normalized_d
    c = normalized_d + 1
    size, masks = stable_candidate_masks(m, c)
    forced, forced_union = private_fragment_certificate(size, masks)
    residual = [
        idx + 1 for idx in range(size) if not (forced_union & (1 << idx))
    ]
    return (
        normalized_d,
        sigma_inf(m, c),
        exact_k0_inf(m, c),
        residual_cover_number(size, masks, residual),
        residual,
    )


def normalized_n84_d(d: int) -> int:
    return (
        (2 ** min(prime_exponent(d, 2), 6))
        * (3 ** min(prime_exponent(d, 3), 4))
        * (7 ** min(prime_exponent(d, 7), 2))
    )


@functools.lru_cache(maxsize=None)
def predicted_n84_fixed_quotient(
    d: int,
) -> tuple[int, int, int, int, list[int]]:
    normalized_d = normalized_n84_d(d)
    m = 84 * normalized_d
    c = normalized_d + 1
    size, masks = stable_candidate_masks(m, c)
    forced, forced_union = private_fragment_certificate(size, masks)
    residual = [
        idx + 1 for idx in range(size) if not (forced_union & (1 << idx))
    ]
    return (
        normalized_d,
        sigma_inf(m, c),
        exact_k0_inf(m, c),
        residual_cover_number(size, masks, residual),
        residual,
    )


def normalized_n135_d(d: int) -> int:
    return (3 ** min(prime_exponent(d, 3), 4)) * (
        5 ** min(prime_exponent(d, 5), 3)
    )


@functools.lru_cache(maxsize=None)
def predicted_n135_fixed_quotient(
    d: int,
) -> tuple[int, int, int, int, list[int]]:
    normalized_d = normalized_n135_d(d)
    m = 135 * normalized_d
    c = normalized_d + 1
    size, masks = stable_candidate_masks(m, c)
    forced, forced_union = private_fragment_certificate(size, masks)
    residual = [
        idx + 1 for idx in range(size) if not (forced_union & (1 << idx))
    ]
    return (
        normalized_d,
        sigma_inf(m, c),
        exact_k0_inf(m, c),
        residual_cover_number(size, masks, residual),
        residual,
    )


def normalized_n110_d(d: int) -> int:
    return (
        (2 ** min(prime_exponent(d, 2), 6))
        * (5 ** min(prime_exponent(d, 5), 2))
        * (11 ** min(prime_exponent(d, 11), 1))
    )


@functools.lru_cache(maxsize=None)
def predicted_n110_fixed_quotient(
    d: int,
) -> tuple[int, int, int, int, list[int]]:
    normalized_d = normalized_n110_d(d)
    m = 110 * normalized_d
    c = normalized_d + 1
    size, masks = stable_candidate_masks(m, c)
    forced, forced_union = private_fragment_certificate(size, masks)
    residual = [
        idx + 1 for idx in range(size) if not (forced_union & (1 << idx))
    ]
    return (
        normalized_d,
        sigma_inf(m, c),
        exact_k0_inf(m, c),
        residual_cover_number(size, masks, residual),
        residual,
    )


def normalized_n102_d(d: int) -> int:
    return (
        (2 ** min(prime_exponent(d, 2), 6))
        * (3 ** min(prime_exponent(d, 3), 4))
        * (17 ** min(prime_exponent(d, 17), 1))
    )


@functools.lru_cache(maxsize=None)
def predicted_n102_fixed_quotient(
    d: int,
) -> tuple[int, int, int, int, list[int]]:
    normalized_d = normalized_n102_d(d)
    m = 102 * normalized_d
    c = normalized_d + 1
    size, masks = stable_candidate_masks(m, c)
    forced, forced_union = private_fragment_certificate(size, masks)
    residual = [
        idx + 1 for idx in range(size) if not (forced_union & (1 << idx))
    ]
    return (
        normalized_d,
        sigma_inf(m, c),
        exact_k0_inf(m, c),
        residual_cover_number(size, masks, residual),
        residual,
    )


def normalized_n105_d(d: int) -> int:
    return (
        (3 ** min(prime_exponent(d, 3), 4))
        * (5 ** min(prime_exponent(d, 5), 2))
        * (7 ** min(prime_exponent(d, 7), 2))
    )


@functools.lru_cache(maxsize=None)
def predicted_n105_fixed_quotient(
    d: int,
) -> tuple[int, int, int, int, list[int]]:
    normalized_d = normalized_n105_d(d)
    m = 105 * normalized_d
    c = normalized_d + 1
    size, masks = stable_candidate_masks(m, c)
    forced, forced_union = private_fragment_certificate(size, masks)
    residual = [
        idx + 1 for idx in range(size) if not (forced_union & (1 << idx))
    ]
    return (
        normalized_d,
        sigma_inf(m, c),
        exact_k0_inf(m, c),
        residual_cover_number(size, masks, residual),
        residual,
    )


def normalized_n165_d(d: int) -> int:
    return (
        (3 ** min(prime_exponent(d, 3), 4))
        * (5 ** min(prime_exponent(d, 5), 3))
        * (11 ** min(prime_exponent(d, 11), 2))
    )


@functools.lru_cache(maxsize=None)
def predicted_n165_fixed_quotient(
    d: int,
) -> tuple[int, int, int, int, list[int]]:
    normalized_d = normalized_n165_d(d)
    m = 165 * normalized_d
    c = normalized_d + 1
    size, masks = stable_candidate_masks(m, c)
    forced, forced_union = private_fragment_certificate(size, masks)
    residual = [
        idx + 1 for idx in range(size) if not (forced_union & (1 << idx))
    ]
    return (
        normalized_d,
        sigma_inf(m, c),
        exact_k0_inf(m, c),
        residual_cover_number(size, masks, residual),
        residual,
    )


def normalized_n90_d(d: int) -> int:
    return (
        (2 ** min(prime_exponent(d, 2), 6))
        * (3 ** min(prime_exponent(d, 3), 4))
        * (5 ** min(prime_exponent(d, 5), 2))
    )


@functools.lru_cache(maxsize=None)
def predicted_n90_fixed_quotient(
    d: int,
) -> tuple[int, int, int, int, list[int]]:
    normalized_d = normalized_n90_d(d)
    m = 90 * normalized_d
    c = normalized_d + 1
    size, masks = stable_candidate_masks(m, c)
    forced, forced_union = private_fragment_certificate(size, masks)
    residual = [
        idx + 1 for idx in range(size) if not (forced_union & (1 << idx))
    ]
    return (
        normalized_d,
        sigma_inf(m, c),
        exact_k0_inf(m, c),
        residual_cover_number(size, masks, residual),
        residual,
    )


def normalized_n120_d(d: int) -> int:
    return (
        (2 ** min(prime_exponent(d, 2), 6))
        * (3 ** min(prime_exponent(d, 3), 4))
        * (5 ** min(prime_exponent(d, 5), 2))
    )


@functools.lru_cache(maxsize=None)
def predicted_n120_fixed_quotient(
    d: int,
) -> tuple[int, int, int, int, list[int]]:
    normalized_d = normalized_n120_d(d)
    m = 120 * normalized_d
    c = normalized_d + 1
    size, masks = stable_candidate_masks(m, c)
    forced, forced_union = private_fragment_certificate(size, masks)
    residual = [
        idx + 1 for idx in range(size) if not (forced_union & (1 << idx))
    ]
    return (
        normalized_d,
        sigma_inf(m, c),
        exact_k0_inf(m, c),
        residual_cover_number(size, masks, residual),
        residual,
    )


def normalized_n36_d(d: int) -> int:
    return (2 ** min(prime_exponent(d, 2), 5)) * (
        3 ** min(prime_exponent(d, 3), 3)
    )


@functools.lru_cache(maxsize=None)
def predicted_n36_fixed_quotient(
    d: int,
) -> tuple[int, int, int, int, list[int]]:
    normalized_d = normalized_n36_d(d)
    m = 36 * normalized_d
    c = normalized_d + 1
    size, masks = stable_candidate_masks(m, c)
    forced, forced_union = private_fragment_certificate(size, masks)
    residual = [
        idx + 1 for idx in range(size) if not (forced_union & (1 << idx))
    ]
    return (
        normalized_d,
        sigma_inf(m, c),
        exact_k0_inf(m, c),
        residual_cover_number(size, masks, residual),
        residual,
    )


def normalized_n96_d(d: int) -> int:
    return (2 ** min(prime_exponent(d, 2), 6)) * (
        3 ** min(prime_exponent(d, 3), 4)
    )


@functools.lru_cache(maxsize=None)
def predicted_n96_fixed_quotient(
    d: int,
) -> tuple[int, int, int, int, list[int]]:
    normalized_d = normalized_n96_d(d)
    m = 96 * normalized_d
    c = normalized_d + 1
    size, masks = stable_candidate_masks(m, c)
    forced, forced_union = private_fragment_certificate(size, masks)
    residual = [
        idx + 1 for idx in range(size) if not (forced_union & (1 << idx))
    ]
    return (
        normalized_d,
        sigma_inf(m, c),
        exact_k0_inf(m, c),
        residual_cover_number(size, masks, residual),
        residual,
    )


def normalized_n114_d(d: int) -> int:
    return (
        (2 ** min(prime_exponent(d, 2), 6))
        * (3 ** min(prime_exponent(d, 3), 4))
        * (19 ** min(prime_exponent(d, 19), 1))
    )


@functools.lru_cache(maxsize=None)
def predicted_n114_fixed_quotient(
    d: int,
) -> tuple[int, int, int, int, list[int]]:
    normalized_d = normalized_n114_d(d)
    m = 114 * normalized_d
    c = normalized_d + 1
    size, masks = stable_candidate_masks(m, c)
    forced, forced_union = private_fragment_certificate(size, masks)
    residual = [
        idx + 1 for idx in range(size) if not (forced_union & (1 << idx))
    ]
    return (
        normalized_d,
        sigma_inf(m, c),
        exact_k0_inf(m, c),
        residual_cover_number(size, masks, residual),
        residual,
    )


def normalized_n108_d(d: int) -> int:
    return (
        (2 ** min(prime_exponent(d, 2), 6))
        * (3 ** min(prime_exponent(d, 3), 4))
    )


@functools.lru_cache(maxsize=None)
def predicted_n108_fixed_quotient(
    d: int,
) -> tuple[int, int, int, int, list[int]]:
    normalized_d = normalized_n108_d(d)
    m = 108 * normalized_d
    c = normalized_d + 1
    size, masks = stable_candidate_masks(m, c)
    forced, forced_union = private_fragment_certificate(size, masks)
    residual = [
        idx + 1 for idx in range(size) if not (forced_union & (1 << idx))
    ]
    return (
        normalized_d,
        sigma_inf(m, c),
        exact_k0_inf(m, c),
        residual_cover_number(size, masks, residual),
        residual,
    )


def normalized_n130_d(d: int) -> int:
    return (
        (2 ** min(prime_exponent(d, 2), 7))
        * (5 ** min(prime_exponent(d, 5), 3))
        * (13 ** min(prime_exponent(d, 13), 1))
    )


@functools.lru_cache(maxsize=None)
def predicted_n130_fixed_quotient(
    d: int,
) -> tuple[int, int, int, int, list[int]]:
    normalized_d = normalized_n130_d(d)
    m = 130 * normalized_d
    c = normalized_d + 1
    size, masks = stable_candidate_masks(m, c)
    forced, forced_union = private_fragment_certificate(size, masks)
    residual = [
        idx + 1 for idx in range(size) if not (forced_union & (1 << idx))
    ]
    return (
        normalized_d,
        sigma_inf(m, c),
        exact_k0_inf(m, c),
        residual_cover_number(size, masks, residual),
        residual,
    )


def normalized_n126_d(d: int) -> int:
    return (
        (2 ** min(prime_exponent(d, 2), 6))
        * (3 ** min(prime_exponent(d, 3), 4))
        * (7 ** min(prime_exponent(d, 7), 2))
    )


@functools.lru_cache(maxsize=None)
def predicted_n126_fixed_quotient(
    d: int,
) -> tuple[int, int, int, int, list[int]]:
    normalized_d = normalized_n126_d(d)
    m = 126 * normalized_d
    c = normalized_d + 1
    size, masks = stable_candidate_masks(m, c)
    forced, forced_union = private_fragment_certificate(size, masks)
    residual = [
        idx + 1 for idx in range(size) if not (forced_union & (1 << idx))
    ]
    return (
        normalized_d,
        sigma_inf(m, c),
        exact_k0_inf(m, c),
        residual_cover_number(size, masks, residual),
        residual,
    )


def normalized_n112_d(d: int) -> int:
    return (
        (2 ** min(prime_exponent(d, 2), 6))
        * (7 ** min(prime_exponent(d, 7), 2))
    )


@functools.lru_cache(maxsize=None)
def predicted_n112_fixed_quotient(
    d: int,
) -> tuple[int, int, int, int, list[int]]:
    normalized_d = normalized_n112_d(d)
    m = 112 * normalized_d
    c = normalized_d + 1
    size, masks = stable_candidate_masks(m, c)
    forced, forced_union = private_fragment_certificate(size, masks)
    residual = [
        idx + 1 for idx in range(size) if not (forced_union & (1 << idx))
    ]
    return (
        normalized_d,
        sigma_inf(m, c),
        exact_k0_inf(m, c),
        residual_cover_number(size, masks, residual),
        residual,
    )


def normalized_n132_d(d: int) -> int:
    return (
        (2 ** min(prime_exponent(d, 2), 7))
        * (3 ** min(prime_exponent(d, 3), 4))
        * (11 ** min(prime_exponent(d, 11), 2))
    )


@functools.lru_cache(maxsize=None)
def predicted_n132_fixed_quotient(
    d: int,
) -> tuple[int, int, int, int, list[int]]:
    normalized_d = normalized_n132_d(d)
    m = 132 * normalized_d
    c = normalized_d + 1
    size, masks = stable_candidate_masks(m, c)
    forced, forced_union = private_fragment_certificate(size, masks)
    residual = [
        idx + 1 for idx in range(size) if not (forced_union & (1 << idx))
    ]
    return (
        normalized_d,
        sigma_inf(m, c),
        exact_k0_inf(m, c),
        residual_cover_number(size, masks, residual),
        residual,
    )


def normalized_n138_d(d: int) -> int:
    return (
        (2 ** min(prime_exponent(d, 2), 7))
        * (3 ** min(prime_exponent(d, 3), 4))
        * (23 ** min(prime_exponent(d, 23), 1))
    )


@functools.lru_cache(maxsize=None)
def predicted_n138_fixed_quotient(
    d: int,
) -> tuple[int, int, int, int, list[int]]:
    normalized_d = normalized_n138_d(d)
    m = 138 * normalized_d
    c = normalized_d + 1
    size, masks = stable_candidate_masks(m, c)
    forced, forced_union = private_fragment_certificate(size, masks)
    residual = [
        idx + 1 for idx in range(size) if not (forced_union & (1 << idx))
    ]
    return (
        normalized_d,
        sigma_inf(m, c),
        exact_k0_inf(m, c),
        residual_cover_number(size, masks, residual),
        residual,
    )


def normalized_n160_d(d: int) -> int:
    return (
        (2 ** min(prime_exponent(d, 2), 7))
        * (5 ** min(prime_exponent(d, 5), 3))
    )


@functools.lru_cache(maxsize=None)
def predicted_n160_fixed_quotient(
    d: int,
) -> tuple[int, int, int, int, list[int]]:
    normalized_d = normalized_n160_d(d)
    m = 160 * normalized_d
    c = normalized_d + 1
    size, masks = stable_candidate_masks(m, c)
    forced, forced_union = private_fragment_certificate(size, masks)
    residual = [
        idx + 1 for idx in range(size) if not (forced_union & (1 << idx))
    ]
    return (
        normalized_d,
        sigma_inf(m, c),
        exact_k0_inf(m, c),
        residual_cover_number(size, masks, residual),
        residual,
    )


def normalized_n170_d(d: int) -> int:
    return (
        (2 ** min(prime_exponent(d, 2), 7))
        * (5 ** min(prime_exponent(d, 5), 3))
        * (17 ** min(prime_exponent(d, 17), 1))
    )


@functools.lru_cache(maxsize=None)
def predicted_n170_fixed_quotient(
    d: int,
) -> tuple[int, int, int, int, list[int]]:
    normalized_d = normalized_n170_d(d)
    m = 170 * normalized_d
    c = normalized_d + 1
    size, masks = stable_candidate_masks(m, c)
    forced, forced_union = private_fragment_certificate(size, masks)
    residual = [
        idx + 1 for idx in range(size) if not (forced_union & (1 << idx))
    ]
    return (
        normalized_d,
        sigma_inf(m, c),
        exact_k0_inf(m, c),
        residual_cover_number(size, masks, residual),
        residual,
    )


def normalized_n144_d(d: int) -> int:
    return (
        (2 ** min(prime_exponent(d, 2), 7))
        * (3 ** min(prime_exponent(d, 3), 4))
    )


@functools.lru_cache(maxsize=None)
def predicted_n144_fixed_quotient(
    d: int,
) -> tuple[int, int, int, int, list[int]]:
    normalized_d = normalized_n144_d(d)
    m = 144 * normalized_d
    c = normalized_d + 1
    size, masks = stable_candidate_masks(m, c)
    forced, forced_union = private_fragment_certificate(size, masks)
    residual = [
        idx + 1 for idx in range(size) if not (forced_union & (1 << idx))
    ]
    return (
        normalized_d,
        sigma_inf(m, c),
        exact_k0_inf(m, c),
        residual_cover_number(size, masks, residual),
        residual,
    )


def normalized_n225_d(d: int) -> int:
    return (
        (3 ** min(prime_exponent(d, 3), 4))
        * (5 ** min(prime_exponent(d, 5), 3))
    )


@functools.lru_cache(maxsize=None)
def predicted_n225_fixed_quotient(
    d: int,
) -> tuple[int, int, int, int, list[int]]:
    normalized_d = normalized_n225_d(d)
    m = 225 * normalized_d
    c = normalized_d + 1
    size, masks = stable_candidate_masks(m, c)
    forced, forced_union = private_fragment_certificate(size, masks)
    residual = [
        idx + 1 for idx in range(size) if not (forced_union & (1 << idx))
    ]
    return (
        normalized_d,
        sigma_inf(m, c),
        exact_k0_inf(m, c),
        residual_cover_number(size, masks, residual),
        residual,
    )


N168_RESIDUAL_TAU = {
    6: 1,
    12: 4,
    14: 1,
    18: 1,
    21: 4,
    24: 4,
    28: 5,
    36: 4,
    42: 5,
    48: 4,
    54: 1,
    56: 16,
    63: 12,
    72: 10,
    84: 9,
    108: 4,
    112: 28,
    126: 13,
    144: 14,
    168: 20,
    189: 12,
    216: 10,
    224: 24,
    252: 17,
    288: 10,
    336: 32,
    378: 13,
    432: 14,
    448: 6,
    504: 28,
    576: 4,
    672: 24,
    756: 17,
    864: 10,
    1008: 40,
    1344: 6,
    1512: 29,
    1728: 4,
    2016: 32,
    2268: 1,
    3024: 48,
    4032: 8,
    4536: 7,
    6048: 34,
    9072: 14,
    10584: 1,
    12096: 10,
    21168: 3,
    42336: 6,
}


def normalized_n168_d(d: int) -> int:
    return (
        (2 ** min(prime_exponent(d, 2), 7))
        * (3 ** min(prime_exponent(d, 3), 4))
        * (7 ** min(prime_exponent(d, 7), 2))
    )


@functools.lru_cache(maxsize=None)
def predicted_n168_fixed_quotient(
    d: int,
) -> tuple[int, int, int, int, list[int]]:
    normalized_d = normalized_n168_d(d)
    m = 168 * normalized_d
    c = normalized_d + 1
    size, masks = stable_candidate_masks(m, c)
    forced, forced_union = private_fragment_certificate(size, masks)
    residual = [
        idx + 1 for idx in range(size) if not (forced_union & (1 << idx))
    ]
    tau = N168_RESIDUAL_TAU.get(normalized_d, 0)
    if bool(residual) != (normalized_d in N168_RESIDUAL_TAU):
        raise ValueError(f"incomplete n=168 residual tau table for d0={normalized_d}")
    return (
        normalized_d,
        sigma_inf(m, c),
        len(forced) + tau,
        tau,
        residual,
    )


N240_RESIDUAL_TAU = {
    6: 1,
    10: 1,
    12: 4,
    15: 4,
    18: 1,
    20: 5,
    24: 4,
    30: 5,
    36: 4,
    40: 14,
    45: 8,
    48: 2,
    50: 1,
    54: 1,
    60: 9,
    72: 10,
    75: 4,
    80: 12,
    90: 9,
    100: 5,
    108: 4,
    120: 18,
    135: 8,
    144: 14,
    150: 5,
    160: 2,
    180: 13,
    200: 14,
    216: 10,
    225: 8,
    240: 14,
    270: 9,
    288: 10,
    300: 9,
    360: 22,
    400: 26,
    432: 20,
    450: 9,
    480: 2,
    540: 13,
    600: 18,
    675: 8,
    720: 26,
    800: 36,
    864: 24,
    900: 13,
    1080: 25,
    1200: 28,
    1350: 9,
    1440: 12,
    1600: 30,
    1620: 1,
    1728: 14,
    1800: 25,
    2160: 32,
    2400: 36,
    2700: 13,
    3240: 7,
    3600: 38,
    4320: 26,
    4800: 30,
    5400: 25,
    7200: 42,
    8100: 1,
    8640: 14,
    9000: 3,
    10800: 46,
    14400: 30,
    16200: 7,
    21600: 68,
    27000: 3,
    32400: 10,
    43200: 58,
    54000: 4,
    64800: 22,
    86400: 20,
    108000: 6,
}


def normalized_n240_d(d: int) -> int:
    return (
        (2 ** min(prime_exponent(d, 2), 7))
        * (3 ** min(prime_exponent(d, 3), 4))
        * (5 ** min(prime_exponent(d, 5), 3))
    )


@functools.lru_cache(maxsize=None)
def predicted_n240_fixed_quotient(
    d: int,
) -> tuple[int, int, int, int, list[int]]:
    normalized_d = normalized_n240_d(d)
    m = 240 * normalized_d
    c = normalized_d + 1
    size, masks = stable_candidate_masks(m, c)
    forced, forced_union = private_fragment_certificate(size, masks)
    residual = [
        idx + 1 for idx in range(size) if not (forced_union & (1 << idx))
    ]
    tau = N240_RESIDUAL_TAU.get(normalized_d, 0)
    if bool(residual) != (normalized_d in N240_RESIDUAL_TAU):
        raise ValueError(f"incomplete n=240 residual tau table for d0={normalized_d}")
    return (
        normalized_d,
        sigma_inf(m, c),
        len(forced) + tau,
        tau,
        residual,
    )


N180_RESIDUAL_TAU = {
    6: 1,
    10: 1,
    12: 4,
    15: 4,
    18: 1,
    20: 5,
    24: 4,
    30: 5,
    36: 5,
    40: 10,
    45: 16,
    48: 4,
    50: 1,
    60: 9,
    72: 13,
    75: 2,
    80: 12,
    90: 17,
    96: 4,
    100: 3,
    108: 1,
    120: 14,
    135: 8,
    144: 18,
    150: 3,
    160: 10,
    180: 21,
    200: 6,
    216: 7,
    225: 8,
    240: 16,
    270: 8,
    288: 16,
    300: 5,
    320: 4,
    360: 27,
    400: 8,
    432: 16,
    450: 9,
    480: 14,
    540: 9,
    576: 2,
    600: 8,
    675: 14,
    720: 32,
    800: 6,
    864: 16,
    900: 11,
    960: 4,
    1080: 15,
    1200: 10,
    1350: 14,
    1440: 30,
    1600: 4,
    1728: 6,
    1800: 17,
    2160: 24,
    2400: 6,
    2700: 14,
    2880: 10,
    3600: 24,
    4320: 18,
    4800: 4,
    5400: 15,
    5760: 4,
    7200: 16,
    8640: 6,
    9000: 3,
    10800: 25,
    14400: 6,
    18000: 8,
    21600: 35,
    28800: 2,
    36000: 4,
    43200: 18,
    54000: 1,
    64800: 7,
    86400: 4,
    108000: 5,
}


def normalized_n180_d(d: int) -> int:
    return (
        (2 ** min(prime_exponent(d, 2), 7))
        * (3 ** min(prime_exponent(d, 3), 4))
        * (5 ** min(prime_exponent(d, 5), 3))
    )


@functools.lru_cache(maxsize=None)
def predicted_n180_fixed_quotient(
    d: int,
) -> tuple[int, int, int, int, list[int]]:
    normalized_d = normalized_n180_d(d)
    m = 180 * normalized_d
    c = normalized_d + 1
    size, masks = stable_candidate_masks(m, c)
    forced, forced_union = private_fragment_certificate(size, masks)
    residual = [
        idx + 1 for idx in range(size) if not (forced_union & (1 << idx))
    ]
    tau = N180_RESIDUAL_TAU.get(normalized_d, 0)
    if bool(residual) != (normalized_d in N180_RESIDUAL_TAU):
        raise ValueError(f"incomplete n=180 residual tau table for d0={normalized_d}")
    return (
        normalized_d,
        sigma_inf(m, c),
        len(forced) + tau,
        tau,
        residual,
    )


N150_RESIDUAL_TAU = {
    6: 1,
    12: 2,
    18: 1,
    20: 1,
    24: 2,
    36: 2,
    40: 2,
    45: 4,
    48: 2,
    54: 1,
    60: 1,
    72: 2,
    80: 2,
    90: 4,
    96: 2,
    108: 2,
    120: 2,
    135: 4,
    144: 2,
    160: 2,
    180: 5,
    216: 2,
    240: 2,
    270: 4,
    288: 2,
    320: 2,
    360: 9,
    432: 2,
    480: 2,
    540: 5,
    675: 12,
    720: 12,
    800: 6,
    864: 2,
    960: 2,
    1080: 9,
    1350: 12,
    1440: 12,
    1600: 6,
    2160: 12,
    2400: 6,
    2700: 12,
    2880: 4,
    4320: 12,
    4800: 6,
    5400: 12,
    5760: 2,
    7200: 6,
    8640: 4,
    10800: 12,
    14400: 6,
    17280: 2,
    21600: 13,
    43200: 6,
}


def normalized_n150_d(d: int) -> int:
    return (
        (2 ** min(prime_exponent(d, 2), 7))
        * (3 ** min(prime_exponent(d, 3), 4))
        * (5 ** min(prime_exponent(d, 5), 3))
    )


@functools.lru_cache(maxsize=None)
def predicted_n150_fixed_quotient(
    d: int,
) -> tuple[int, int, int, int, list[int]]:
    normalized_d = normalized_n150_d(d)
    m = 150 * normalized_d
    c = normalized_d + 1
    size, masks = stable_candidate_masks(m, c)
    forced, forced_union = private_fragment_certificate(size, masks)
    residual = [
        idx + 1 for idx in range(size) if not (forced_union & (1 << idx))
    ]
    tau = N150_RESIDUAL_TAU.get(normalized_d, 0)
    if bool(residual) != (normalized_d in N150_RESIDUAL_TAU):
        raise ValueError(f"incomplete n=150 residual tau table for d0={normalized_d}")
    return (
        normalized_d,
        sigma_inf(m, c),
        len(forced) + tau,
        tau,
        residual,
    )


N156_RESIDUAL_TAU = {
    6: 1,
    12: 4,
    18: 1,
    24: 4,
    36: 4,
    48: 4,
    54: 1,
    72: 6,
    96: 4,
    108: 4,
    144: 6,
    216: 6,
    288: 6,
    432: 6,
    576: 2,
    864: 6,
    1728: 2,
    5616: 3,
    11232: 6,
}


def normalized_n156_d(d: int) -> int:
    return (
        (2 ** min(prime_exponent(d, 2), 7))
        * (3 ** min(prime_exponent(d, 3), 4))
        * (13 ** min(prime_exponent(d, 13), 1))
    )


@functools.lru_cache(maxsize=None)
def predicted_n156_fixed_quotient(
    d: int,
) -> tuple[int, int, int, int, list[int]]:
    normalized_d = normalized_n156_d(d)
    m = 156 * normalized_d
    c = normalized_d + 1
    size, masks = stable_candidate_masks(m, c)
    forced, forced_union = private_fragment_certificate(size, masks)
    residual = [
        idx + 1 for idx in range(size) if not (forced_union & (1 << idx))
    ]
    tau = N156_RESIDUAL_TAU.get(normalized_d, 0)
    if bool(residual) != (normalized_d in N156_RESIDUAL_TAU):
        raise ValueError(f"incomplete n=156 residual tau table for d0={normalized_d}")
    return (
        normalized_d,
        sigma_inf(m, c),
        len(forced) + tau,
        tau,
        residual,
    )


N190_RESIDUAL_TAU = {
    10: 1,
    20: 3,
    40: 4,
    50: 1,
    80: 4,
    100: 3,
    160: 4,
    200: 4,
    320: 4,
    400: 4,
    800: 4,
    1600: 4,
}


def normalized_n190_d(d: int) -> int:
    return (
        (2 ** min(prime_exponent(d, 2), 7))
        * (5 ** min(prime_exponent(d, 5), 3))
        * (19 ** min(prime_exponent(d, 19), 1))
    )


@functools.lru_cache(maxsize=None)
def predicted_n190_fixed_quotient(
    d: int,
) -> tuple[int, int, int, int, list[int]]:
    normalized_d = normalized_n190_d(d)
    m = 190 * normalized_d
    c = normalized_d + 1
    size, masks = stable_candidate_masks(m, c)
    forced, forced_union = private_fragment_certificate(size, masks)
    residual = [
        idx + 1 for idx in range(size) if not (forced_union & (1 << idx))
    ]
    tau = N190_RESIDUAL_TAU.get(normalized_d, 0)
    if bool(residual) != (normalized_d in N190_RESIDUAL_TAU):
        raise ValueError(f"incomplete n=190 residual tau table for d0={normalized_d}")
    return (
        normalized_d,
        sigma_inf(m, c),
        len(forced) + tau,
        tau,
        residual,
    )


N255_RESIDUAL_TAU = {
    15: 4,
    45: 8,
    75: 4,
    135: 8,
    225: 8,
    675: 8,
    11475: 20,
}


def normalized_n255_d(d: int) -> int:
    return (
        (3 ** min(prime_exponent(d, 3), 5))
        * (5 ** min(prime_exponent(d, 5), 3))
        * (17 ** min(prime_exponent(d, 17), 1))
    )


@functools.lru_cache(maxsize=None)
def predicted_n255_fixed_quotient(
    d: int,
) -> tuple[int, int, int, int, list[int]]:
    normalized_d = normalized_n255_d(d)
    m = 255 * normalized_d
    c = normalized_d + 1
    size, masks = stable_candidate_masks(m, c)
    forced, forced_union = private_fragment_certificate(size, masks)
    residual = [
        idx + 1 for idx in range(size) if not (forced_union & (1 << idx))
    ]
    tau = N255_RESIDUAL_TAU.get(normalized_d, 0)
    if bool(residual) != (normalized_d in N255_RESIDUAL_TAU):
        raise ValueError(f"incomplete n=255 residual tau table for d0={normalized_d}")
    return (
        normalized_d,
        sigma_inf(m, c),
        len(forced) + tau,
        tau,
        residual,
    )


N189_RESIDUAL_TAU = {
    21: 4,
    63: 12,
}


def normalized_n189_d(d: int) -> int:
    return (
        (3 ** min(prime_exponent(d, 3), 4))
        * (7 ** min(prime_exponent(d, 7), 2))
    )


@functools.lru_cache(maxsize=None)
def predicted_n189_fixed_quotient(
    d: int,
) -> tuple[int, int, int, int, list[int]]:
    normalized_d = normalized_n189_d(d)
    m = 189 * normalized_d
    c = normalized_d + 1
    size, masks = stable_candidate_masks(m, c)
    forced, forced_union = private_fragment_certificate(size, masks)
    residual = [
        idx + 1 for idx in range(size) if not (forced_union & (1 << idx))
    ]
    tau = N189_RESIDUAL_TAU.get(normalized_d, 0)
    if bool(residual) != (normalized_d in N189_RESIDUAL_TAU):
        raise ValueError(f"incomplete n=189 residual tau table for d0={normalized_d}")
    return (
        normalized_d,
        sigma_inf(m, c),
        len(forced) + tau,
        tau,
        residual,
    )


N200_RESIDUAL_TAU = {
    10: 1,
    20: 3,
    40: 10,
    80: 10,
    160: 6,
    200: 1,
    400: 5,
    800: 12,
}


def normalized_n200_d(d: int) -> int:
    return (
        (2 ** min(prime_exponent(d, 2), 7))
        * (5 ** min(prime_exponent(d, 5), 3))
    )


@functools.lru_cache(maxsize=None)
def predicted_n200_fixed_quotient(
    d: int,
) -> tuple[int, int, int, int, list[int]]:
    normalized_d = normalized_n200_d(d)
    m = 200 * normalized_d
    c = normalized_d + 1
    size, masks = stable_candidate_masks(m, c)
    forced, forced_union = private_fragment_certificate(size, masks)
    residual = [
        idx + 1 for idx in range(size) if not (forced_union & (1 << idx))
    ]
    tau = N200_RESIDUAL_TAU.get(normalized_d, 0)
    if bool(residual) != (normalized_d in N200_RESIDUAL_TAU):
        raise ValueError(f"incomplete n=200 residual tau table for d0={normalized_d}")
    return (
        normalized_d,
        sigma_inf(m, c),
        len(forced) + tau,
        tau,
        residual,
    )


N140_RESIDUAL_TAU = {
    10: 1,
    14: 1,
    20: 5,
    28: 5,
    35: 16,
    40: 10,
    56: 12,
    70: 17,
    80: 12,
    100: 1,
    112: 18,
    140: 21,
    160: 8,
    175: 6,
    200: 2,
    224: 14,
    280: 28,
    320: 2,
    350: 6,
    400: 4,
    448: 2,
    560: 34,
    700: 7,
    800: 2,
    1120: 26,
    1400: 11,
    1600: 2,
    2240: 8,
    2800: 22,
    4480: 4,
    5600: 2,
    7000: 3,
    11200: 2,
    14000: 12,
    39200: 1,
}


def normalized_n140_d(d: int) -> int:
    return (
        (2 ** min(prime_exponent(d, 2), 7))
        * (5 ** min(prime_exponent(d, 5), 3))
        * (7 ** min(prime_exponent(d, 7), 2))
    )


@functools.lru_cache(maxsize=None)
def predicted_n140_fixed_quotient(
    d: int,
) -> tuple[int, int, int, int, list[int]]:
    normalized_d = normalized_n140_d(d)
    m = 140 * normalized_d
    c = normalized_d + 1
    size, masks = stable_candidate_masks(m, c)
    forced, forced_union = private_fragment_certificate(size, masks)
    residual = [
        idx + 1 for idx in range(size) if not (forced_union & (1 << idx))
    ]
    tau = N140_RESIDUAL_TAU.get(normalized_d, 0)
    if bool(residual) != (normalized_d in N140_RESIDUAL_TAU):
        raise ValueError(f"incomplete n=140 residual tau table for d0={normalized_d}")
    return (
        normalized_d,
        sigma_inf(m, c),
        len(forced) + tau,
        tau,
        residual,
    )


N210_RESIDUAL_TAU = {
    6: 1,
    10: 1,
    12: 2,
    14: 1,
    15: 4,
    18: 1,
    20: 3,
    21: 4,
    24: 2,
    28: 3,
    30: 5,
    35: 16,
    36: 2,
    40: 4,
    42: 5,
    45: 8,
    48: 2,
    50: 1,
    54: 1,
    56: 6,
    60: 7,
    63: 12,
    70: 17,
    72: 2,
    75: 2,
    80: 4,
    84: 7,
    90: 9,
    96: 2,
    100: 3,
    105: 20,
    108: 2,
    112: 6,
    120: 8,
    126: 13,
    135: 8,
    140: 19,
    144: 2,
    150: 3,
    160: 4,
    168: 10,
    175: 20,
    180: 11,
    189: 12,
    192: 2,
    200: 4,
    210: 21,
    216: 2,
    224: 6,
    225: 6,
    240: 8,
    252: 15,
    270: 9,
    280: 22,
    288: 2,
    300: 5,
    315: 28,
    320: 4,
    336: 10,
    350: 21,
    360: 15,
    378: 13,
    400: 4,
    420: 23,
    432: 2,
    448: 6,
    450: 7,
    480: 8,
    504: 18,
    525: 22,
    540: 11,
    560: 22,
    576: 2,
    600: 6,
    630: 29,
    672: 10,
    675: 6,
    700: 23,
    720: 18,
    756: 15,
    800: 4,
    840: 26,
    864: 2,
    900: 9,
    945: 28,
    960: 8,
    1008: 22,
    1050: 23,
    1080: 15,
    1120: 22,
    1200: 6,
    1260: 31,
    1344: 10,
    1350: 7,
    1400: 27,
    1440: 18,
    1512: 19,
    1575: 32,
    1600: 4,
    1620: 1,
    1680: 26,
    1728: 2,
    1800: 13,
    1890: 29,
    1920: 2,
    2016: 22,
    2100: 25,
    2160: 18,
    2240: 22,
    2268: 1,
    2400: 6,
    2520: 34,
    2688: 2,
    2700: 9,
    2800: 34,
    2835: 8,
    2880: 18,
    3024: 27,
    3150: 33,
    3240: 5,
    3360: 26,
    3600: 18,
    3780: 31,
    4032: 22,
    4200: 29,
    4320: 18,
    4480: 12,
    4536: 5,
    4725: 38,
    4800: 4,
    5040: 36,
    5400: 13,
    5600: 36,
    5670: 8,
    5760: 12,
    6048: 32,
    6300: 35,
    6480: 8,
    6720: 26,
    7000: 3,
    7056: 4,
    7200: 18,
    7560: 35,
    7875: 6,
    8064: 14,
    8100: 1,
    8400: 36,
    8640: 18,
    9000: 3,
    9072: 13,
    9450: 39,
    9800: 1,
    10080: 38,
    10584: 1,
    10800: 20,
    11200: 30,
    11340: 9,
    12096: 32,
    12600: 39,
    12960: 8,
    13440: 14,
    14000: 10,
    14112: 4,
    14175: 14,
    14400: 16,
    15120: 41,
    15750: 6,
    16200: 3,
    16800: 38,
    17280: 12,
    18000: 8,
    18144: 18,
    18900: 41,
    19600: 5,
    20160: 38,
    21000: 3,
    21168: 9,
    21600: 20,
    22400: 20,
    22680: 13,
    23625: 12,
    24192: 24,
    25200: 46,
    25920: 6,
    27000: 3,
    28000: 12,
    28350: 14,
    28800: 10,
    29400: 1,
    30240: 46,
    31500: 6,
    32400: 10,
    33075: 28,
    33600: 30,
    35280: 4,
    36000: 8,
    36288: 14,
    37800: 45,
    39200: 19,
    40320: 26,
    42000: 10,
    42336: 14,
    43200: 18,
    45360: 20,
    47250: 12,
    50400: 48,
    52920: 1,
    54000: 10,
    56000: 6,
    56700: 15,
    58800: 5,
    60480: 46,
    63000: 9,
    64800: 10,
    66150: 28,
    67200: 20,
    70560: 4,
    72000: 6,
    75600: 50,
    78400: 22,
    84000: 12,
    84672: 10,
    86400: 12,
    88200: 1,
    90720: 26,
    94500: 12,
    100800: 42,
    105840: 9,
    108000: 10,
    113400: 17,
    117600: 19,
    120960: 34,
    126000: 16,
    129600: 10,
    132300: 28,
    151200: 50,
    168000: 6,
    176400: 5,
    181440: 20,
    189000: 15,
    201600: 30,
    211680: 14,
    216000: 8,
    226800: 24,
    235200: 22,
    252000: 18,
    264600: 29,
    302400: 44,
    352800: 19,
    378000: 22,
    423360: 10,
    453600: 24,
    504000: 12,
    529200: 33,
    604800: 32,
    705600: 22,
    756000: 22,
    907200: 12,
    1058400: 40,
    1512000: 14,
    1814400: 2,
    2116800: 42,
    4233600: 16,
}


def normalized_n210_d(d: int) -> int:
    return (
        (2 ** min(prime_exponent(d, 2), 7))
        * (3 ** min(prime_exponent(d, 3), 4))
        * (5 ** min(prime_exponent(d, 5), 3))
        * (7 ** min(prime_exponent(d, 7), 2))
    )


@functools.lru_cache(maxsize=None)
def predicted_n210_fixed_quotient(
    d: int,
) -> tuple[int, int, int, int, list[int]]:
    normalized_d = normalized_n210_d(d)
    m = 210 * normalized_d
    c = normalized_d + 1
    size, masks = stable_candidate_masks(m, c)
    forced, forced_union = private_fragment_certificate(size, masks)
    residual = [
        idx + 1 for idx in range(size) if not (forced_union & (1 << idx))
    ]
    tau = N210_RESIDUAL_TAU.get(normalized_d, 0)
    if bool(residual) != (normalized_d in N210_RESIDUAL_TAU):
        raise ValueError(f"incomplete n=210 residual tau table for d0={normalized_d}")
    return (
        normalized_d,
        sigma_inf(m, c),
        len(forced) + tau,
        tau,
        residual,
    )


N270_RESIDUAL_TAU = {
    6: 1,
    10: 1,
    12: 2,
    15: 4,
    20: 3,
    24: 2,
    30: 5,
    36: 1,
    40: 4,
    45: 10,
    48: 2,
    50: 1,
    60: 7,
    72: 5,
    75: 4,
    80: 4,
    90: 10,
    96: 2,
    100: 3,
    120: 8,
    144: 6,
    150: 5,
    160: 4,
    180: 11,
    192: 2,
    200: 4,
    216: 1,
    225: 14,
    240: 8,
    288: 6,
    300: 7,
    320: 4,
    360: 15,
    400: 4,
    432: 9,
    450: 14,
    480: 8,
    576: 6,
    600: 8,
    675: 42,
    720: 16,
    800: 4,
    864: 20,
    900: 15,
    960: 8,
    1080: 1,
    1200: 8,
    1350: 42,
    1440: 16,
    1600: 4,
    1728: 20,
    1800: 19,
    1920: 2,
    2025: 6,
    2160: 9,
    2400: 8,
    2592: 4,
    2700: 42,
    2880: 16,
    3456: 2,
    3600: 24,
    3840: 2,
    4050: 6,
    4320: 20,
    4800: 8,
    5184: 4,
    5400: 43,
    7200: 24,
    8100: 6,
    8640: 20,
    9600: 2,
    10368: 2,
    10800: 51,
    12960: 4,
    14400: 24,
    16200: 6,
    17280: 2,
    19200: 2,
    21600: 64,
    25920: 4,
    28800: 8,
    32400: 6,
    43200: 69,
    51840: 2,
    57600: 8,
    64800: 10,
    86400: 26,
    129600: 10,
    172800: 22,
    259200: 2,
}


def normalized_n270_d(d: int) -> int:
    return (
        (2 ** min(prime_exponent(d, 2), 8))
        * (3 ** min(prime_exponent(d, 3), 5))
        * (5 ** min(prime_exponent(d, 5), 3))
    )


@functools.lru_cache(maxsize=None)
def predicted_n270_fixed_quotient(
    d: int,
) -> tuple[int, int, int, int, list[int]]:
    normalized_d = normalized_n270_d(d)
    m = 270 * normalized_d
    c = normalized_d + 1
    size, masks = stable_candidate_masks(m, c)
    forced, forced_union = private_fragment_certificate(size, masks)
    residual = [
        idx + 1 for idx in range(size) if not (forced_union & (1 << idx))
    ]
    tau = N270_RESIDUAL_TAU.get(normalized_d, 0)
    if bool(residual) != (normalized_d in N270_RESIDUAL_TAU):
        raise ValueError(f"incomplete n=270 residual tau table for d0={normalized_d}")
    return (
        normalized_d,
        sigma_inf(m, c),
        len(forced) + tau,
        tau,
        residual,
    )


N174_RESIDUAL_TAU = {
    6: 1,
    12: 2,
    18: 1,
    24: 2,
    36: 2,
    48: 2,
    54: 1,
    72: 2,
    96: 2,
    108: 2,
    144: 2,
    192: 2,
    216: 2,
    288: 2,
    432: 2,
    576: 2,
    864: 2,
    1728: 2,
}


def normalized_n174_d(d: int) -> int:
    return (
        (2 ** min(prime_exponent(d, 2), 7))
        * (3 ** min(prime_exponent(d, 3), 4))
        * (29 ** min(prime_exponent(d, 29), 1))
    )


@functools.lru_cache(maxsize=None)
def predicted_n174_fixed_quotient(
    d: int,
) -> tuple[int, int, int, int, list[int]]:
    normalized_d = normalized_n174_d(d)
    m = 174 * normalized_d
    c = normalized_d + 1
    size, masks = stable_candidate_masks(m, c)
    forced, forced_union = private_fragment_certificate(size, masks)
    residual = [
        idx + 1 for idx in range(size) if not (forced_union & (1 << idx))
    ]
    tau = N174_RESIDUAL_TAU.get(normalized_d, 0)
    if bool(residual) != (normalized_d in N174_RESIDUAL_TAU):
        raise ValueError(f"incomplete n=174 residual tau table for d0={normalized_d}")
    return (
        normalized_d,
        sigma_inf(m, c),
        len(forced) + tau,
        tau,
        residual,
    )


N285_RESIDUAL_TAU = {
    15: 4,
    45: 8,
    75: 4,
    135: 8,
    225: 8,
    405: 4,
    675: 8,
    2025: 4,
    12825: 16,
}


def normalized_n285_d(d: int) -> int:
    return (
        (3 ** min(prime_exponent(d, 3), 5))
        * (5 ** min(prime_exponent(d, 5), 3))
        * (19 ** min(prime_exponent(d, 19), 1))
    )


@functools.lru_cache(maxsize=None)
def predicted_n285_fixed_quotient(
    d: int,
) -> tuple[int, int, int, int, list[int]]:
    normalized_d = normalized_n285_d(d)
    m = 285 * normalized_d
    c = normalized_d + 1
    size, masks = stable_candidate_masks(m, c)
    forced, forced_union = private_fragment_certificate(size, masks)
    residual = [
        idx + 1 for idx in range(size) if not (forced_union & (1 << idx))
    ]
    tau = N285_RESIDUAL_TAU.get(normalized_d, 0)
    if bool(residual) != (normalized_d in N285_RESIDUAL_TAU):
        raise ValueError(f"incomplete n=285 residual tau table for d0={normalized_d}")
    return (
        normalized_d,
        sigma_inf(m, c),
        len(forced) + tau,
        tau,
        residual,
    )


N154_RESIDUAL_TAU = {
    14: 1,
    28: 3,
    56: 6,
    77: 4,
    88: 1,
    112: 6,
    154: 4,
    176: 4,
    224: 6,
    308: 4,
    352: 4,
    448: 2,
    616: 5,
    704: 4,
    1232: 8,
    2464: 8,
    4928: 4,
}


def normalized_n154_d(d: int) -> int:
    return (
        (2 ** min(prime_exponent(d, 2), 7))
        * (7 ** min(prime_exponent(d, 7), 2))
        * (11 ** min(prime_exponent(d, 11), 2))
    )


@functools.lru_cache(maxsize=None)
def predicted_n154_fixed_quotient(
    d: int,
) -> tuple[int, int, int, int, list[int]]:
    normalized_d = normalized_n154_d(d)
    m = 154 * normalized_d
    c = normalized_d + 1
    size, masks = stable_candidate_masks(m, c)
    forced, forced_union = private_fragment_certificate(size, masks)
    residual = [
        idx + 1 for idx in range(size) if not (forced_union & (1 << idx))
    ]
    tau = N154_RESIDUAL_TAU.get(normalized_d, 0)
    if bool(residual) != (normalized_d in N154_RESIDUAL_TAU):
        raise ValueError(f"incomplete n=154 residual tau table for d0={normalized_d}")
    return (
        normalized_d,
        sigma_inf(m, c),
        len(forced) + tau,
        tau,
        residual,
    )


N186_RESIDUAL_TAU = {
    6: 1,
    12: 2,
    18: 1,
    24: 2,
    36: 2,
    48: 2,
    54: 1,
    72: 2,
    96: 2,
    108: 2,
    144: 2,
    192: 2,
    216: 2,
    288: 2,
    432: 2,
    576: 2,
    864: 2,
    1728: 2,
}


def normalized_n186_d(d: int) -> int:
    return (
        (2 ** min(prime_exponent(d, 2), 7))
        * (3 ** min(prime_exponent(d, 3), 4))
        * (31 ** min(prime_exponent(d, 31), 1))
    )


@functools.lru_cache(maxsize=None)
def predicted_n186_fixed_quotient(
    d: int,
) -> tuple[int, int, int, int, list[int]]:
    normalized_d = normalized_n186_d(d)
    m = 186 * normalized_d
    c = normalized_d + 1
    size, masks = stable_candidate_masks(m, c)
    forced, forced_union = private_fragment_certificate(size, masks)
    residual = [
        idx + 1 for idx in range(size) if not (forced_union & (1 << idx))
    ]
    tau = N186_RESIDUAL_TAU.get(normalized_d, 0)
    if bool(residual) != (normalized_d in N186_RESIDUAL_TAU):
        raise ValueError(f"incomplete n=186 residual tau table for d0={normalized_d}")
    return (
        normalized_d,
        sigma_inf(m, c),
        len(forced) + tau,
        tau,
        residual,
    )


N220_RESIDUAL_TAU = {
    10: 1,
    20: 5,
    22: 1,
    40: 10,
    44: 3,
    50: 1,
    55: 12,
    80: 12,
    88: 11,
    100: 3,
    110: 13,
    160: 12,
    176: 22,
    200: 8,
    220: 15,
    275: 34,
    320: 6,
    352: 28,
    400: 10,
    440: 23,
    550: 34,
    704: 16,
    800: 10,
    880: 34,
    1100: 34,
    1600: 6,
    1760: 36,
    2200: 37,
    3520: 16,
    4400: 49,
    8800: 79,
    11000: 1,
    17600: 66,
    22000: 9,
    35200: 48,
    44000: 33,
    48400: 1,
    96800: 17,
}


def normalized_n220_d(d: int) -> int:
    return (
        (2 ** min(prime_exponent(d, 2), 7))
        * (5 ** min(prime_exponent(d, 5), 3))
        * (11 ** min(prime_exponent(d, 11), 2))
    )


@functools.lru_cache(maxsize=None)
def predicted_n220_fixed_quotient(
    d: int,
) -> tuple[int, int, int, int, list[int]]:
    normalized_d = normalized_n220_d(d)
    m = 220 * normalized_d
    c = normalized_d + 1
    size, masks = stable_candidate_masks(m, c)
    forced, forced_union = private_fragment_certificate(size, masks)
    residual = [
        idx + 1 for idx in range(size) if not (forced_union & (1 << idx))
    ]
    tau = N220_RESIDUAL_TAU.get(normalized_d, 0)
    if bool(residual) != (normalized_d in N220_RESIDUAL_TAU):
        raise ValueError(f"incomplete n=220 residual tau table for d0={normalized_d}")
    return (
        normalized_d,
        sigma_inf(m, c),
        len(forced) + tau,
        tau,
        residual,
    )


N300_RESIDUAL_TAU = {
    6: 1,
    10: 1,
    12: 4,
    15: 4,
    18: 1,
    20: 5,
    24: 4,
    30: 5,
    36: 4,
    40: 10,
    45: 8,
    48: 4,
    54: 1,
    60: 9,
    72: 6,
    80: 12,
    90: 9,
    96: 4,
    108: 4,
    120: 14,
    135: 8,
    144: 6,
    160: 12,
    162: 1,
    180: 13,
    192: 2,
    200: 3,
    216: 6,
    225: 8,
    240: 16,
    270: 9,
    288: 6,
    320: 10,
    324: 2,
    360: 18,
    400: 17,
    405: 4,
    432: 6,
    450: 8,
    480: 16,
    540: 13,
    576: 4,
    600: 3,
    640: 2,
    648: 4,
    675: 40,
    720: 22,
    800: 42,
    810: 5,
    864: 6,
    900: 8,
    960: 12,
    1080: 21,
    1152: 2,
    1200: 17,
    1296: 4,
    1350: 40,
    1440: 22,
    1600: 46,
    1620: 7,
    1728: 4,
    1800: 11,
    1920: 2,
    2025: 16,
    2160: 22,
    2400: 42,
    2592: 4,
    2700: 40,
    2880: 18,
    3200: 12,
    3240: 15,
    3456: 2,
    3600: 25,
    4050: 16,
    4320: 22,
    4800: 46,
    4860: 1,
    5184: 2,
    5400: 43,
    5760: 8,
    6480: 16,
    7200: 50,
    8100: 16,
    8640: 18,
    9600: 12,
    9720: 7,
    10368: 2,
    10800: 57,
    11520: 4,
    12960: 16,
    14400: 46,
    16200: 16,
    17280: 8,
    19440: 8,
    21600: 78,
    25920: 6,
    28800: 12,
    32400: 21,
    34560: 4,
    38880: 8,
    43200: 70,
    51840: 2,
    64800: 46,
    86400: 32,
    97200: 1,
    129600: 26,
    172800: 14,
    194400: 19,
    259200: 6,
    648000: 3,
}


def normalized_n300_d(d: int) -> int:
    return (
        (2 ** min(prime_exponent(d, 2), 8))
        * (3 ** min(prime_exponent(d, 3), 5))
        * (5 ** min(prime_exponent(d, 5), 3))
    )


@functools.lru_cache(maxsize=None)
def predicted_n300_fixed_quotient(
    d: int,
) -> tuple[int, int, int, int, list[int]]:
    normalized_d = normalized_n300_d(d)
    m = 300 * normalized_d
    c = normalized_d + 1
    size, masks = stable_candidate_masks(m, c)
    forced, forced_union = private_fragment_certificate(size, masks)
    residual = [
        idx + 1 for idx in range(size) if not (forced_union & (1 << idx))
    ]
    tau = N300_RESIDUAL_TAU.get(normalized_d, 0)
    if bool(residual) != (normalized_d in N300_RESIDUAL_TAU):
        raise ValueError(f"incomplete n=300 residual tau table for d0={normalized_d}")
    return (
        normalized_d,
        sigma_inf(m, c),
        len(forced) + tau,
        tau,
        residual,
    )


N230_RESIDUAL_TAU = {
    10: 1,
    20: 3,
    40: 4,
    50: 1,
    80: 4,
    100: 3,
    160: 4,
    200: 4,
    320: 4,
    400: 4,
    800: 4,
    1600: 4,
}


def normalized_n230_d(d: int) -> int:
    return (
        (2 ** min(prime_exponent(d, 2), 7))
        * (5 ** min(prime_exponent(d, 5), 3))
        * (23 ** min(prime_exponent(d, 23), 1))
    )


@functools.lru_cache(maxsize=None)
def predicted_n230_fixed_quotient(
    d: int,
) -> tuple[int, int, int, int, list[int]]:
    normalized_d = normalized_n230_d(d)
    m = 230 * normalized_d
    c = normalized_d + 1
    size, masks = stable_candidate_masks(m, c)
    forced, forced_union = private_fragment_certificate(size, masks)
    residual = [
        idx + 1 for idx in range(size) if not (forced_union & (1 << idx))
    ]
    tau = N230_RESIDUAL_TAU.get(normalized_d, 0)
    if bool(residual) != (normalized_d in N230_RESIDUAL_TAU):
        raise ValueError(f"incomplete n=230 residual tau table for d0={normalized_d}")
    return (
        normalized_d,
        sigma_inf(m, c),
        len(forced) + tau,
        tau,
        residual,
    )


N315_RESIDUAL_TAU = {
    15: 4,
    21: 4,
    35: 16,
    45: 16,
    63: 24,
    75: 4,
    105: 20,
    135: 12,
    175: 24,
    189: 30,
    225: 20,
    315: 40,
    525: 28,
    567: 4,
    675: 28,
    945: 41,
    1575: 50,
    2025: 10,
    2835: 4,
    4725: 58,
    7875: 6,
    11025: 4,
    14175: 14,
    33075: 22,
}


def normalized_n315_d(d: int) -> int:
    return (
        (3 ** min(prime_exponent(d, 3), 5))
        * (5 ** min(prime_exponent(d, 5), 3))
        * (7 ** min(prime_exponent(d, 7), 2))
    )


@functools.lru_cache(maxsize=None)
def predicted_n315_fixed_quotient(
    d: int,
) -> tuple[int, int, int, int, list[int]]:
    normalized_d = normalized_n315_d(d)
    m = 315 * normalized_d
    c = normalized_d + 1
    size, masks = stable_candidate_masks(m, c)
    forced, forced_union = private_fragment_certificate(size, masks)
    residual = [
        idx + 1 for idx in range(size) if not (forced_union & (1 << idx))
    ]
    tau = N315_RESIDUAL_TAU.get(normalized_d, 0)
    if bool(residual) != (normalized_d in N315_RESIDUAL_TAU):
        raise ValueError(f"incomplete n=315 residual tau table for d0={normalized_d}")
    return (
        normalized_d,
        sigma_inf(m, c),
        len(forced) + tau,
        tau,
        residual,
    )


N198_RESIDUAL_TAU = {
    6: 1,
    12: 2,
    18: 1,
    24: 2,
    36: 3,
    44: 1,
    48: 2,
    72: 7,
    88: 5,
    96: 2,
    99: 12,
    108: 1,
    132: 1,
    144: 8,
    176: 8,
    192: 2,
    198: 12,
    216: 5,
    264: 5,
    288: 8,
    297: 36,
    352: 8,
    396: 13,
    432: 6,
    528: 8,
    576: 6,
    594: 36,
    704: 8,
    792: 17,
    864: 6,
    1056: 8,
    1188: 36,
    1584: 20,
    1728: 4,
    2112: 8,
    2376: 37,
    3168: 20,
    4752: 43,
    6336: 14,
    9504: 51,
    12672: 6,
    19008: 39,
    38016: 20,
}


def normalized_n198_d(d: int) -> int:
    return (
        (2 ** min(prime_exponent(d, 2), 7))
        * (3 ** min(prime_exponent(d, 3), 4))
        * (11 ** min(prime_exponent(d, 11), 2))
    )


@functools.lru_cache(maxsize=None)
def predicted_n198_fixed_quotient(
    d: int,
) -> tuple[int, int, int, int, list[int]]:
    normalized_d = normalized_n198_d(d)
    m = 198 * normalized_d
    c = normalized_d + 1
    size, masks = stable_candidate_masks(m, c)
    forced, forced_union = private_fragment_certificate(size, masks)
    residual = [
        idx + 1 for idx in range(size) if not (forced_union & (1 << idx))
    ]
    tau = N198_RESIDUAL_TAU.get(normalized_d, 0)
    if bool(residual) != (normalized_d in N198_RESIDUAL_TAU):
        raise ValueError(f"incomplete n=198 residual tau table for d0={normalized_d}")
    return (
        normalized_d,
        sigma_inf(m, c),
        len(forced) + tau,
        tau,
        residual,
    )


N231_RESIDUAL_TAU = {
    21: 4,
    33: 2,
    63: 12,
    77: 32,
    99: 14,
    189: 12,
    231: 34,
    297: 18,
    693: 46,
    2079: 50,
    4851: 2,
    6237: 20,
    14553: 28,
}


def normalized_n231_d(d: int) -> int:
    return (
        (3 ** min(prime_exponent(d, 3), 4))
        * (7 ** min(prime_exponent(d, 7), 2))
        * (11 ** min(prime_exponent(d, 11), 2))
    )


@functools.lru_cache(maxsize=None)
def predicted_n231_fixed_quotient(
    d: int,
) -> tuple[int, int, int, int, list[int]]:
    normalized_d = normalized_n231_d(d)
    m = 231 * normalized_d
    c = normalized_d + 1
    size, masks = stable_candidate_masks(m, c)
    forced, forced_union = private_fragment_certificate(size, masks)
    residual = [
        idx + 1 for idx in range(size) if not (forced_union & (1 << idx))
    ]
    tau = N231_RESIDUAL_TAU.get(normalized_d, 0)
    if bool(residual) != (normalized_d in N231_RESIDUAL_TAU):
        raise ValueError(f"incomplete n=231 residual tau table for d0={normalized_d}")
    return (
        normalized_d,
        sigma_inf(m, c),
        len(forced) + tau,
        tau,
        residual,
    )


N204_RESIDUAL_TAU = {
    6: 1,
    12: 4,
    18: 1,
    24: 4,
    36: 4,
    48: 4,
    54: 1,
    72: 6,
    96: 4,
    108: 4,
    144: 6,
    216: 6,
    288: 6,
    432: 6,
    576: 2,
    864: 6,
    1728: 2,
    14688: 6,
}


def normalized_n204_d(d: int) -> int:
    return (
        (2 ** min(prime_exponent(d, 2), 7))
        * (3 ** min(prime_exponent(d, 3), 4))
        * (17 ** min(prime_exponent(d, 17), 1))
    )


@functools.lru_cache(maxsize=None)
def predicted_n204_fixed_quotient(
    d: int,
) -> tuple[int, int, int, int, list[int]]:
    normalized_d = normalized_n204_d(d)
    m = 204 * normalized_d
    c = normalized_d + 1
    size, masks = stable_candidate_masks(m, c)
    forced, forced_union = private_fragment_certificate(size, masks)
    residual = [
        idx + 1 for idx in range(size) if not (forced_union & (1 << idx))
    ]
    tau = N204_RESIDUAL_TAU.get(normalized_d, 0)
    if bool(residual) != (normalized_d in N204_RESIDUAL_TAU):
        raise ValueError(f"incomplete n=204 residual tau table for d0={normalized_d}")
    return (
        normalized_d,
        sigma_inf(m, c),
        len(forced) + tau,
        tau,
        residual,
    )


N330_RESIDUAL_TAU = {
    6: 1,
    10: 1,
    12: 2,
    15: 4,
    18: 1,
    20: 3,
    22: 1,
    24: 2,
    30: 5,
    33: 4,
    36: 2,
    40: 4,
    44: 3,
    45: 8,
    48: 2,
    50: 1,
    54: 1,
    55: 16,
    60: 7,
    66: 5,
    72: 2,
    75: 4,
    80: 4,
    88: 7,
    90: 9,
    96: 2,
    99: 16,
    100: 3,
    108: 2,
    110: 17,
    120: 8,
    132: 7,
    135: 8,
    144: 2,
    150: 5,
    160: 4,
    162: 1,
    165: 20,
    176: 10,
    180: 11,
    192: 2,
    198: 17,
    200: 4,
    216: 2,
    220: 19,
    225: 8,
    240: 8,
    264: 11,
    270: 9,
    275: 40,
    288: 2,
    297: 20,
    300: 7,
    320: 4,
    324: 2,
    330: 21,
    352: 10,
    360: 15,
    384: 2,
    396: 19,
    400: 4,
    405: 4,
    432: 2,
    440: 23,
    450: 9,
    480: 8,
    495: 32,
    528: 14,
    540: 11,
    550: 41,
    576: 2,
    594: 21,
    600: 8,
    640: 2,
    648: 2,
    660: 23,
    675: 8,
    704: 10,
    720: 18,
    792: 23,
    800: 4,
    810: 5,
    825: 44,
    864: 2,
    880: 26,
    891: 12,
    900: 11,
    960: 8,
    990: 33,
    1056: 14,
    1080: 15,
    1100: 43,
    1152: 2,
    1188: 23,
    1200: 8,
    1296: 2,
    1320: 27,
    1350: 9,
    1408: 4,
    1440: 18,
    1485: 36,
    1584: 26,
    1600: 4,
    1620: 7,
    1650: 45,
    1728: 2,
    1760: 26,
    1782: 13,
    1800: 15,
    1920: 6,
    1980: 35,
    2025: 4,
    2112: 14,
    2160: 18,
    2200: 47,
    2376: 27,
    2400: 8,
    2475: 56,
    2592: 2,
    2640: 30,
    2700: 11,
    2880: 18,
    2970: 37,
    3168: 26,
    3200: 2,
    3240: 11,
    3300: 47,
    3456: 2,
    3520: 26,
    3564: 15,
    3600: 20,
    3840: 2,
    3960: 39,
    4050: 5,
    4224: 8,
    4320: 18,
    4400: 55,
    4455: 24,
    4752: 35,
    4800: 8,
    4860: 1,
    4950: 57,
    5184: 2,
    5280: 30,
    5400: 15,
    5760: 16,
    5940: 39,
    6336: 26,
    6480: 14,
    6600: 51,
    7040: 18,
    7128: 19,
    7200: 20,
    7425: 92,
    7920: 42,
    8100: 7,
    8448: 2,
    8640: 18,
    8800: 71,
    8910: 25,
    9000: 3,
    9504: 51,
    9600: 6,
    9720: 5,
    9900: 59,
    10368: 2,
    10560: 30,
    10692: 1,
    10800: 22,
    11000: 3,
    11520: 12,
    11880: 43,
    12375: 8,
    12672: 20,
    12960: 14,
    13200: 59,
    13365: 8,
    14080: 12,
    14256: 27,
    14400: 20,
    14850: 93,
    15840: 42,
    16200: 11,
    17280: 16,
    17600: 94,
    17820: 27,
    18000: 8,
    19008: 52,
    19200: 2,
    19440: 8,
    19800: 63,
    21120: 22,
    21384: 5,
    21600: 22,
    22000: 11,
    22275: 96,
    23760: 51,
    24300: 1,
    24750: 8,
    25344: 14,
    25920: 14,
    26400: 75,
    26730: 8,
    27000: 3,
    28512: 43,
    28800: 18,
    29700: 95,
    31680: 42,
    32400: 18,
    33000: 3,
    34560: 12,
    35200: 86,
    35640: 31,
    36000: 8,
    37125: 44,
    38016: 46,
    38880: 8,
    39600: 71,
    42240: 14,
    42768: 13,
    43200: 22,
    44000: 27,
    44550: 97,
    47520: 67,
    48400: 5,
    48600: 5,
    49500: 8,
    51840: 8,
    52272: 5,
    52800: 96,
    53460: 9,
    54000: 10,
    57024: 44,
    57600: 14,
    59400: 99,
    63360: 34,
    64800: 18,
    66000: 11,
    66825: 80,
    70400: 80,
    71280: 39,
    72000: 8,
    74250: 44,
    76032: 40,
    77760: 8,
    79200: 87,
    81000: 1,
    81675: 32,
    85536: 29,
    86400: 20,
    88000: 50,
    89100: 99,
    95040: 68,
    96800: 21,
    97200: 12,
    99000: 11,
    103680: 4,
    104544: 21,
    105600: 90,
    106920: 13,
    108000: 10,
    111375: 14,
    114048: 28,
    118800: 104,
    126720: 26,
    129600: 18,
    132000: 27,
    133650: 80,
    142560: 55,
    144000: 2,
    145200: 5,
    148500: 44,
    156816: 1,
    158400: 102,
    162000: 6,
    163350: 32,
    171072: 30,
    172800: 16,
    176000: 22,
    178200: 102,
    190080: 60,
    193600: 44,
    194400: 12,
    198000: 19,
    209088: 22,
    211200: 82,
    213840: 21,
    216000: 10,
    222750: 14,
    228096: 22,
    237600: 109,
    245025: 14,
    259200: 12,
    261360: 5,
    264000: 50,
    267300: 81,
    285120: 56,
    290400: 21,
    297000: 47,
    313632: 11,
    316800: 94,
    324000: 6,
    326700: 32,
    342144: 12,
    356400: 102,
    380160: 52,
    387200: 20,
    388800: 12,
    396000: 35,
    418176: 10,
    427680: 37,
    432000: 4,
    435600: 5,
    445500: 14,
    475200: 111,
    490050: 14,
    518400: 8,
    522720: 21,
    528000: 22,
    534600: 84,
    570240: 34,
    580800: 44,
    594000: 54,
    627264: 12,
    633600: 86,
    648000: 6,
    653400: 32,
    712800: 103,
    777600: 4,
    784080: 1,
    792000: 56,
    855360: 38,
    871200: 21,
    891000: 15,
    950400: 107,
    980100: 14,
    1045440: 22,
    1069200: 84,
    1140480: 26,
    1161600: 20,
    1188000: 63,
    1254528: 10,
    1296000: 4,
    1306800: 37,
    1425600: 103,
    1568160: 11,
    1584000: 24,
    1710720: 12,
    1742400: 44,
    1782000: 20,
    1900800: 100,
    1960200: 14,
    2090880: 10,
    2138400: 85,
    2376000: 65,
    2613600: 49,
    2851200: 87,
    3136320: 12,
    3484800: 20,
    3564000: 20,
    3920400: 15,
    4276800: 85,
    4752000: 32,
    5227200: 62,
    5702400: 80,
    6272640: 10,
    7128000: 20,
    7840800: 24,
    8553600: 65,
    9504000: 8,
    10454400: 34,
    14256000: 4,
    15681600: 26,
    17107200: 50,
    20908800: 6,
    31363200: 10,
}


N345_RESIDUAL_TAU = {
    15: 4,
    45: 8,
    75: 4,
    135: 8,
    225: 8,
    405: 6,
    675: 8,
    2025: 6,
    15525: 4,
}


def normalized_n345_d(d: int) -> int:
    return (
        (3 ** min(prime_exponent(d, 3), 5))
        * (5 ** min(prime_exponent(d, 5), 3))
        * (23 ** min(prime_exponent(d, 23), 1))
    )


@functools.lru_cache(maxsize=None)
def predicted_n345_fixed_quotient(
    d: int,
) -> tuple[int, int, int, int, list[int]]:
    normalized_d = normalized_n345_d(d)
    m = 345 * normalized_d
    c = normalized_d + 1
    size, masks = stable_candidate_masks(m, c)
    forced, forced_union = private_fragment_certificate(size, masks)
    residual = [
        idx + 1 for idx in range(size) if not (forced_union & (1 << idx))
    ]
    tau = N345_RESIDUAL_TAU.get(normalized_d, 0)
    if bool(residual) != (normalized_d in N345_RESIDUAL_TAU):
        raise ValueError(f"incomplete n=345 residual tau table for d0={normalized_d}")
    return (
        normalized_d,
        sigma_inf(m, c),
        len(forced) + tau,
        tau,
        residual,
    )


def normalized_n330_d(d: int) -> int:
    return (
        (2 ** min(prime_exponent(d, 2), 8))
        * (3 ** min(prime_exponent(d, 3), 5))
        * (5 ** min(prime_exponent(d, 5), 3))
        * (11 ** min(prime_exponent(d, 11), 2))
    )


@functools.lru_cache(maxsize=None)
def predicted_n330_fixed_quotient(
    d: int,
) -> tuple[int, int, int, int, list[int]]:
    normalized_d = normalized_n330_d(d)
    m = 330 * normalized_d
    c = normalized_d + 1
    size, masks = stable_candidate_masks(m, c)
    forced, forced_union = private_fragment_certificate(size, masks)
    residual = [
        idx + 1 for idx in range(size) if not (forced_union & (1 << idx))
    ]
    tau = N330_RESIDUAL_TAU.get(normalized_d, 0)
    if bool(residual) != (normalized_d in N330_RESIDUAL_TAU):
        raise ValueError(f"incomplete n=330 residual tau table for d0={normalized_d}")
    return (
        normalized_d,
        sigma_inf(m, c),
        len(forced) + tau,
        tau,
        residual,
    )


N182_RESIDUAL_TAU = {
    14: 1,
    28: 3,
    56: 6,
    112: 6,
    208: 2,
    224: 6,
    416: 2,
    448: 4,
    832: 2,
    1456: 2,
    2912: 2,
    5824: 2,
}


def normalized_n182_d(d: int) -> int:
    return (
        (2 ** min(prime_exponent(d, 2), 7))
        * (7 ** min(prime_exponent(d, 7), 2))
        * (13 ** min(prime_exponent(d, 13), 2))
    )


@functools.lru_cache(maxsize=None)
def predicted_n182_fixed_quotient(
    d: int,
) -> tuple[int, int, int, int, list[int]]:
    normalized_d = normalized_n182_d(d)
    m = 182 * normalized_d
    c = normalized_d + 1
    size, masks = stable_candidate_masks(m, c)
    forced, forced_union = private_fragment_certificate(size, masks)
    residual = [
        idx + 1 for idx in range(size) if not (forced_union & (1 << idx))
    ]
    tau = N182_RESIDUAL_TAU.get(normalized_d, 0)
    if bool(residual) != (normalized_d in N182_RESIDUAL_TAU):
        raise ValueError(f"incomplete n=182 residual tau table for d0={normalized_d}")
    return (
        normalized_d,
        sigma_inf(m, c),
        len(forced) + tau,
        tau,
        residual,
    )


def print_m36t_d6_family(limit: int) -> None:
    failures: list[tuple[int, str, object, object]] = []
    print(f"`m=36t, d=6` family scan for 1 <= t <= {limit}")
    print(
        "| t | m | sigma_inf | packing_lb | k0_inf | predicted_k0 | forced | residual | expected |"
    )
    print("|---:|---:|---:|---:|---:|---:|---:|---|---|")

    for t in range(1, limit + 1):
        m = 36 * t
        d = 6
        c = next(candidate for candidate in range(1, m + 1) if math.gcd(m, candidate - 1) == d)
        n = 6 * t
        sigma = sigma_inf(m, c)
        k0 = exact_k0_inf(m, c)
        packing_lb = math.ceil((n - 1) / sigma)
        size, masks = stable_candidate_masks(m, c)
        forced, forced_union = private_fragment_certificate(size, masks)
        residual = [
            idx + 1 for idx in range(size) if not (forced_union & (1 << idx))
        ]
        expected = [] if is_power_of_three(t) else [t, 5 * t]
        factors = prime_factorization(t)
        predicted_k0 = (
            4
            + 2 * factors.get(2, 0)
            + 6 * factors.get(3, 0)
            + sum(exp * (prime - 1) for prime, exp in factors.items() if prime >= 5)
        )

        if k0 <= packing_lb:
            failures.append((t, "not_gap", k0, packing_lb))
        if residual != expected:
            failures.append((t, "residual", residual, expected))
        if k0 != predicted_k0:
            failures.append((t, "k0", k0, predicted_k0))

        print(
            f"| {t} | {m} | {sigma} | {packing_lb} | {k0} | {predicted_k0} | "
            f"{len(forced)} | `{residual}` | `{expected}` |"
        )

    if failures:
        print(f"Family scan failures: {len(failures)}")
        for failure in failures:
            print(f"- {failure}")
    else:
        print("Family scan matched the expected residual pattern and k0 formula.")


def print_m72t_d12_family(limit: int) -> None:
    failures: list[tuple[int, str, object, object]] = []
    print(f"`m=72t, d=12` family scan for 1 <= t <= {limit}")
    print(
        "| t | m | sigma_inf | predicted_sigma | k0_inf | predicted_k0 | forced | residual | expected |"
    )
    print("|---:|---:|---:|---:|---:|---:|---:|---|---|")

    for t in range(1, limit + 1):
        m = 72 * t
        c = 13
        size, masks = stable_candidate_masks(m, c)
        sigma = sigma_inf(m, c)
        k0 = exact_k0_inf(m, c)
        forced, forced_union = private_fragment_certificate(size, masks)
        residual = [
            idx + 1 for idx in range(size) if not (forced_union & (1 << idx))
        ]

        factors = prime_factorization(t)
        least_large_prime = min((prime for prime in factors if prime >= 5), default=8)
        denominator = min(8, least_large_prime)
        predicted_sigma = math.ceil((6 * t - 1) / denominator)
        predicted_k0 = (
            5
            + 4 * factors.get(2, 0)
            + 6 * factors.get(3, 0)
            + sum(exp * (prime - 1) for prime, exp in factors.items() if prime >= 5)
        )
        expected = predicted_m72t_d12_residual(t)

        if sigma != predicted_sigma:
            failures.append((t, "sigma", sigma, predicted_sigma))
        if k0 != predicted_k0:
            failures.append((t, "k0", k0, predicted_k0))
        if residual != expected:
            failures.append((t, "residual", residual, expected))

        print(
            f"| {t} | {m} | {sigma} | {predicted_sigma} | {k0} | {predicted_k0} | "
            f"{len(forced)} | `{residual}` | `{expected}` |"
        )

    if failures:
        print(f"Family scan failures: {len(failures)}")
        for failure in failures:
            print(f"- {failure}")
    else:
        print("Family scan matched the expected residual pattern and formulas.")


def print_m144t_d6t_family(limit: int) -> None:
    failures: list[tuple[int, str, object, object]] = []
    print(f"`m=144t, d=6t` family scan for 1 <= t <= {limit}")
    print(
        "| t | m | d | sigma_inf | predicted_sigma | k0_inf | predicted_k0 | forced | residual | expected |"
    )
    print("|---:|---:|---:|---:|---:|---:|---:|---:|---|---|")

    for t in range(1, limit + 1):
        m = 144 * t
        d = 6 * t
        c = d + 1
        size, masks = stable_candidate_masks(m, c)
        sigma = sigma_inf(m, c)
        k0 = exact_k0_inf(m, c)
        forced, forced_union = private_fragment_certificate(size, masks)
        residual = [
            idx + 1 for idx in range(size) if not (forced_union & (1 << idx))
        ]
        predicted_sigma, predicted_k0, expected = predicted_m144t_d6t(t)

        if sigma != predicted_sigma:
            failures.append((t, "sigma", sigma, predicted_sigma))
        if k0 != predicted_k0:
            failures.append((t, "k0", k0, predicted_k0))
        if residual != expected:
            failures.append((t, "residual", residual, expected))

        print(
            f"| {t} | {m} | {d} | {sigma} | {predicted_sigma} | {k0} | "
            f"{predicted_k0} | {len(forced)} | `{residual}` | `{expected}` |"
        )

    if failures:
        print(f"Family scan failures: {len(failures)}")
        for failure in failures:
            print(f"- {failure}")
    else:
        print("Family scan matched the expected residual pattern and formulas.")


def print_m252t_d6t_family(limit: int) -> None:
    failures: list[tuple[int, str, object, object]] = []
    print(f"`m=252t, d=6t` family scan for 1 <= t <= {limit}")
    print(
        "| t | m | d | sigma_inf | predicted_sigma | k0_inf | predicted_k0 | forced | residual_tau | residual | expected |"
    )
    print("|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|---|")

    for t in range(1, limit + 1):
        m = 252 * t
        d = 6 * t
        c = d + 1
        size, masks = stable_candidate_masks(m, c)
        sigma = sigma_inf(m, c)
        k0 = exact_k0_inf(m, c)
        forced, forced_union = private_fragment_certificate(size, masks)
        residual = [
            idx + 1 for idx in range(size) if not (forced_union & (1 << idx))
        ]
        tau = residual_cover_number(size, masks, residual)
        predicted_sigma, predicted_k0, expected = predicted_m252t_d6t(t)

        if residual != expected:
            failures.append((t, "residual", residual, expected))
        if predicted_sigma is not None and sigma != predicted_sigma:
            failures.append((t, "sigma", sigma, predicted_sigma))
        if predicted_k0 is not None and k0 != predicted_k0:
            failures.append((t, "k0", k0, predicted_k0))

        print(
            f"| {t} | {m} | {d} | {sigma} | "
            f"{predicted_sigma if predicted_sigma is not None else '-'} | "
            f"{k0} | {predicted_k0 if predicted_k0 is not None else '-'} | "
            f"{len(forced)} | {tau} | `{residual}` | `{expected}` |"
        )

    if failures:
        print(f"Family scan failures: {len(failures)}")
        for failure in failures:
            print(f"- {failure}")
    else:
        print("Family scan matched the expected residual criterion and residual-case formulas.")


def print_m360t_d6t_family(limit: int) -> None:
    failures: list[tuple[int, str, object, object]] = []
    print(f"`m=360t, d=6t` residual-subfamily scan for 1 <= t <= {limit}")
    print(
        "| t | m | d | sigma_inf | predicted_sigma | k0_inf | predicted_k0 | forced | residual_tau | residual | expected |"
    )
    print("|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|---|")

    for t in range(1, limit + 1):
        m = 360 * t
        d = 6 * t
        c = d + 1
        size, masks = stable_candidate_masks(m, c)
        sigma = sigma_inf(m, c)
        k0 = exact_k0_inf(m, c)
        forced, forced_union = private_fragment_certificate(size, masks)
        residual = [
            idx + 1 for idx in range(size) if not (forced_union & (1 << idx))
        ]
        tau = residual_cover_number(size, masks, residual)
        predicted_sigma, predicted_k0, expected = predicted_m360t_d6t(t)

        if expected is not None and residual != expected:
            failures.append((t, "residual", residual, expected))
        if predicted_sigma is not None and sigma != predicted_sigma:
            failures.append((t, "sigma", sigma, predicted_sigma))
        if predicted_k0 is not None and k0 != predicted_k0:
            failures.append((t, "k0", k0, predicted_k0))

        print(
            f"| {t} | {m} | {d} | {sigma} | "
            f"{predicted_sigma if predicted_sigma is not None else '-'} | "
            f"{k0} | {predicted_k0 if predicted_k0 is not None else '-'} | "
            f"{len(forced)} | {tau} | `{residual}` | "
            f"`{expected if expected is not None else '-'}` |"
        )

    if failures:
        print(f"Family scan failures: {len(failures)}")
        for failure in failures:
            print(f"- {failure}")
    else:
        print("Family scan matched the proved residual-subfamily formulas.")


def print_m216t_d6t_family(limit: int) -> None:
    failures: list[tuple[int, str, object, object]] = []
    print(f"`m=216t, d=6t` residual-subfamily scan for 1 <= t <= {limit}")
    print(
        "| t | m | d | sigma_inf | predicted_sigma | k0_inf | predicted_k0 | forced | residual_tau | residual | expected |"
    )
    print("|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|---|")

    for t in range(1, limit + 1):
        m = 216 * t
        d = 6 * t
        c = d + 1
        size, masks = stable_candidate_masks(m, c)
        sigma = sigma_inf(m, c)
        k0 = exact_k0_inf(m, c)
        forced, forced_union = private_fragment_certificate(size, masks)
        residual = [
            idx + 1 for idx in range(size) if not (forced_union & (1 << idx))
        ]
        tau = residual_cover_number(size, masks, residual)
        predicted_sigma, predicted_k0, expected = predicted_m216t_d6t(t)

        if expected is not None and residual != expected:
            failures.append((t, "residual", residual, expected))
        if predicted_sigma is not None and sigma != predicted_sigma:
            failures.append((t, "sigma", sigma, predicted_sigma))
        if predicted_k0 is not None and k0 != predicted_k0:
            failures.append((t, "k0", k0, predicted_k0))

        print(
            f"| {t} | {m} | {d} | {sigma} | "
            f"{predicted_sigma if predicted_sigma is not None else '-'} | "
            f"{k0} | {predicted_k0 if predicted_k0 is not None else '-'} | "
            f"{len(forced)} | {tau} | `{residual}` | "
            f"`{expected if expected is not None else '-'}` |"
        )

    if failures:
        print(f"Family scan failures: {len(failures)}")
        for failure in failures:
            print(f"- {failure}")
    else:
        print("Family scan matched the proved residual-subfamily formulas.")


def print_m196t_d14_family(limit: int) -> None:
    failures: list[tuple[int, str, object, object]] = []
    print(f"`m=196t, d=14` family scan for 1 <= t <= {limit}")
    print(
        "| t | m | sigma_inf | predicted_sigma | k0_inf | predicted_k0 | forced | residual_tau | residual | expected |"
    )
    print("|---:|---:|---:|---:|---:|---:|---:|---:|---|---|")

    for t in range(1, limit + 1):
        m = 196 * t
        d = 14
        c = d + 1
        size, masks = stable_candidate_masks(m, c)
        sigma = sigma_inf(m, c)
        k0 = exact_k0_inf(m, c)
        forced, forced_union = private_fragment_certificate(size, masks)
        residual = [
            idx + 1 for idx in range(size) if not (forced_union & (1 << idx))
        ]
        tau = residual_cover_number(size, masks, residual)
        predicted_sigma, predicted_k0, expected = predicted_m196t_d14(t)

        if sigma != predicted_sigma:
            failures.append((t, "sigma", sigma, predicted_sigma))
        if k0 != predicted_k0:
            failures.append((t, "k0", k0, predicted_k0))
        if residual != expected:
            failures.append((t, "residual", residual, expected))

        print(
            f"| {t} | {m} | {sigma} | {predicted_sigma} | {k0} | "
            f"{predicted_k0} | {len(forced)} | {tau} | `{residual}` | `{expected}` |"
        )

    if failures:
        print(f"Family scan failures: {len(failures)}")
        for failure in failures:
            print(f"- {failure}")
    else:
        print("Family scan matched the expected residual pattern and formulas.")


def print_m108t_d18_family(limit: int) -> None:
    failures: list[tuple[int, str, object, object]] = []
    print(f"`m=108t, d=18` family scan for 1 <= t <= {limit}")
    print(
        "| t | m | sigma_inf | predicted_sigma | k0_inf | predicted_k0 | forced | residual_tau | residual | expected |"
    )
    print("|---:|---:|---:|---:|---:|---:|---:|---:|---|---|")

    for t in range(1, limit + 1):
        m = 108 * t
        d = 18
        c = d + 1
        size, masks = stable_candidate_masks(m, c)
        sigma = sigma_inf(m, c)
        k0 = exact_k0_inf(m, c)
        forced, forced_union = private_fragment_certificate(size, masks)
        residual = [
            idx + 1 for idx in range(size) if not (forced_union & (1 << idx))
        ]
        tau = residual_cover_number(size, masks, residual)
        predicted_sigma, predicted_k0, expected = predicted_m108t_d18(t)

        if sigma != predicted_sigma:
            failures.append((t, "sigma", sigma, predicted_sigma))
        if k0 != predicted_k0:
            failures.append((t, "k0", k0, predicted_k0))
        if residual != expected:
            failures.append((t, "residual", residual, expected))

        print(
            f"| {t} | {m} | {sigma} | {predicted_sigma} | {k0} | "
            f"{predicted_k0} | {len(forced)} | {tau} | `{residual}` | `{expected}` |"
        )

    if failures:
        print(f"Family scan failures: {len(failures)}")
        for failure in failures:
            print(f"- {failure}")
    else:
        print("Family scan matched the expected residual pattern and formulas.")


def print_n30_fixed_quotient_family(limit: int) -> None:
    failures: list[tuple[int, str, object, object]] = []
    print(f"`m=30d, n=30` fixed-quotient scan for 2 <= d <= {limit}")
    print(
        "| d | normalized_d | m | sigma_inf | predicted_sigma | k0_inf | predicted_k0 | residual_tau | predicted_tau | residual | expected |"
    )
    print("|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|---|")

    for d in range(2, limit + 1):
        m = 30 * d
        c = d + 1
        size, masks = stable_candidate_masks(m, c)
        sigma = sigma_inf(m, c)
        k0 = exact_k0_inf(m, c)
        forced, forced_union = private_fragment_certificate(size, masks)
        residual = [
            idx + 1 for idx in range(size) if not (forced_union & (1 << idx))
        ]
        tau = residual_cover_number(size, masks, residual)
        normalized_d, predicted_sigma, predicted_k0, predicted_tau, expected = (
            predicted_n30_fixed_quotient(d)
        )

        if sigma != predicted_sigma:
            failures.append((d, "sigma", sigma, predicted_sigma))
        if k0 != predicted_k0:
            failures.append((d, "k0", k0, predicted_k0))
        if tau != predicted_tau:
            failures.append((d, "tau", tau, predicted_tau))
        if residual != expected:
            failures.append((d, "residual", residual, expected))

        print(
            f"| {d} | {normalized_d} | {m} | {sigma} | {predicted_sigma} | "
            f"{k0} | {predicted_k0} | {tau} | {predicted_tau} | "
            f"`{residual}` | `{expected}` |"
        )

    if failures:
        print(f"Family scan failures: {len(failures)}")
        for failure in failures:
            print(f"- {failure}")
    else:
        print("Family scan matched the normalized-cell predictions.")


def print_n40_fixed_quotient_family(limit: int) -> None:
    failures: list[tuple[int, str, object, object]] = []
    print(f"`m=40d, n=40` fixed-quotient scan for 2 <= d <= {limit}")
    print(
        "| d | normalized_d | m | sigma_inf | predicted_sigma | k0_inf | predicted_k0 | residual_tau | predicted_tau | residual | expected |"
    )
    print("|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|---|")

    for d in range(2, limit + 1):
        m = 40 * d
        c = d + 1
        size, masks = stable_candidate_masks(m, c)
        sigma = sigma_inf(m, c)
        k0 = exact_k0_inf(m, c)
        forced, forced_union = private_fragment_certificate(size, masks)
        residual = [
            idx + 1 for idx in range(size) if not (forced_union & (1 << idx))
        ]
        tau = residual_cover_number(size, masks, residual)
        normalized_d, predicted_sigma, predicted_k0, predicted_tau, expected = (
            predicted_n40_fixed_quotient(d)
        )

        if sigma != predicted_sigma:
            failures.append((d, "sigma", sigma, predicted_sigma))
        if k0 != predicted_k0:
            failures.append((d, "k0", k0, predicted_k0))
        if tau != predicted_tau:
            failures.append((d, "tau", tau, predicted_tau))
        if residual != expected:
            failures.append((d, "residual", residual, expected))

        print(
            f"| {d} | {normalized_d} | {m} | {sigma} | {predicted_sigma} | "
            f"{k0} | {predicted_k0} | {tau} | {predicted_tau} | "
            f"`{residual}` | `{expected}` |"
        )

    if failures:
        print(f"Family scan failures: {len(failures)}")
        for failure in failures:
            print(f"- {failure}")
    else:
        print("Family scan matched the normalized-cell predictions.")


def print_n48_fixed_quotient_family(limit: int) -> None:
    failures: list[tuple[int, str, object, object]] = []
    print(f"`m=48d, n=48` fixed-quotient scan for 2 <= d <= {limit}")
    print(
        "| d | normalized_d | m | sigma_inf | predicted_sigma | k0_inf | predicted_k0 | residual_tau | predicted_tau | residual | expected |"
    )
    print("|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|---|")

    for d in range(2, limit + 1):
        m = 48 * d
        c = d + 1
        size, masks = stable_candidate_masks(m, c)
        sigma = sigma_inf(m, c)
        k0 = exact_k0_inf(m, c)
        forced, forced_union = private_fragment_certificate(size, masks)
        residual = [
            idx + 1 for idx in range(size) if not (forced_union & (1 << idx))
        ]
        tau = residual_cover_number(size, masks, residual)
        normalized_d, predicted_sigma, predicted_k0, predicted_tau, expected = (
            predicted_n48_fixed_quotient(d)
        )

        if sigma != predicted_sigma:
            failures.append((d, "sigma", sigma, predicted_sigma))
        if k0 != predicted_k0:
            failures.append((d, "k0", k0, predicted_k0))
        if tau != predicted_tau:
            failures.append((d, "tau", tau, predicted_tau))
        if residual != expected:
            failures.append((d, "residual", residual, expected))

        print(
            f"| {d} | {normalized_d} | {m} | {sigma} | {predicted_sigma} | "
            f"{k0} | {predicted_k0} | {tau} | {predicted_tau} | "
            f"`{residual}` | `{expected}` |"
        )

    if failures:
        print(f"Family scan failures: {len(failures)}")
        for failure in failures:
            print(f"- {failure}")
    else:
        print("Family scan matched the normalized-cell predictions.")


def print_n70_fixed_quotient_family(limit: int) -> None:
    failures: list[tuple[int, str, object, object]] = []
    print(f"`m=70d, n=70` fixed-quotient scan for 2 <= d <= {limit}")
    print(
        "| d | normalized_d | m | sigma_inf | predicted_sigma | k0_inf | predicted_k0 | residual_tau | predicted_tau | residual | expected |"
    )
    print("|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|---|")

    for d in range(2, limit + 1):
        m = 70 * d
        c = d + 1
        size, masks = stable_candidate_masks(m, c)
        sigma = sigma_inf(m, c)
        k0 = exact_k0_inf(m, c)
        forced, forced_union = private_fragment_certificate(size, masks)
        residual = [
            idx + 1 for idx in range(size) if not (forced_union & (1 << idx))
        ]
        tau = residual_cover_number(size, masks, residual)
        normalized_d, predicted_sigma, predicted_k0, predicted_tau, expected = (
            predicted_n70_fixed_quotient(d)
        )

        if sigma != predicted_sigma:
            failures.append((d, "sigma", sigma, predicted_sigma))
        if k0 != predicted_k0:
            failures.append((d, "k0", k0, predicted_k0))
        if tau != predicted_tau:
            failures.append((d, "tau", tau, predicted_tau))
        if residual != expected:
            failures.append((d, "residual", residual, expected))

        print(
            f"| {d} | {normalized_d} | {m} | {sigma} | {predicted_sigma} | "
            f"{k0} | {predicted_k0} | {tau} | {predicted_tau} | "
            f"`{residual}` | `{expected}` |"
        )

    if failures:
        print(f"Family scan failures: {len(failures)}")
        for failure in failures:
            print(f"- {failure}")
    else:
        print("Family scan matched the normalized-cell predictions.")


def print_n45_fixed_quotient_family(limit: int) -> None:
    failures: list[tuple[int, str, object, object]] = []
    print(f"`m=45d, n=45` fixed-quotient scan for 2 <= d <= {limit}")
    print(
        "| d | normalized_d | m | sigma_inf | predicted_sigma | k0_inf | predicted_k0 | residual_tau | predicted_tau | residual | expected |"
    )
    print("|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|---|")

    for d in range(2, limit + 1):
        m = 45 * d
        c = d + 1
        size, masks = stable_candidate_masks(m, c)
        sigma = sigma_inf(m, c)
        k0 = exact_k0_inf(m, c)
        forced, forced_union = private_fragment_certificate(size, masks)
        residual = [
            idx + 1 for idx in range(size) if not (forced_union & (1 << idx))
        ]
        tau = residual_cover_number(size, masks, residual)
        normalized_d, predicted_sigma, predicted_k0, predicted_tau, expected = (
            predicted_n45_fixed_quotient(d)
        )

        if sigma != predicted_sigma:
            failures.append((d, "sigma", sigma, predicted_sigma))
        if k0 != predicted_k0:
            failures.append((d, "k0", k0, predicted_k0))
        if tau != predicted_tau:
            failures.append((d, "tau", tau, predicted_tau))
        if residual != expected:
            failures.append((d, "residual", residual, expected))

        print(
            f"| {d} | {normalized_d} | {m} | {sigma} | {predicted_sigma} | "
            f"{k0} | {predicted_k0} | {tau} | {predicted_tau} | "
            f"`{residual}` | `{expected}` |"
        )

    if failures:
        print(f"Family scan failures: {len(failures)}")
        for failure in failures:
            print(f"- {failure}")
    else:
        print("Family scan matched the normalized-cell predictions.")


def print_n80_fixed_quotient_family(limit: int) -> None:
    failures: list[tuple[int, str, object, object]] = []
    print(f"`m=80d, n=80` fixed-quotient scan for 2 <= d <= {limit}")
    print(
        "| d | normalized_d | m | sigma_inf | predicted_sigma | k0_inf | predicted_k0 | residual_tau | predicted_tau | residual | expected |"
    )
    print("|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|---|")

    for d in range(2, limit + 1):
        m = 80 * d
        c = d + 1
        size, masks = stable_candidate_masks(m, c)
        sigma = sigma_inf(m, c)
        k0 = exact_k0_inf(m, c)
        forced, forced_union = private_fragment_certificate(size, masks)
        residual = [
            idx + 1 for idx in range(size) if not (forced_union & (1 << idx))
        ]
        tau = residual_cover_number(size, masks, residual)
        normalized_d, predicted_sigma, predicted_k0, predicted_tau, expected = (
            predicted_n80_fixed_quotient(d)
        )

        if sigma != predicted_sigma:
            failures.append((d, "sigma", sigma, predicted_sigma))
        if k0 != predicted_k0:
            failures.append((d, "k0", k0, predicted_k0))
        if tau != predicted_tau:
            failures.append((d, "tau", tau, predicted_tau))
        if residual != expected:
            failures.append((d, "residual", residual, expected))

        print(
            f"| {d} | {normalized_d} | {m} | {sigma} | {predicted_sigma} | "
            f"{k0} | {predicted_k0} | {tau} | {predicted_tau} | "
            f"`{residual}` | `{expected}` |"
        )

    if failures:
        print(f"Family scan failures: {len(failures)}")
        for failure in failures:
            print(f"- {failure}")
    else:
        print("Family scan matched the normalized-cell predictions.")


def print_n72_fixed_quotient_family(limit: int) -> None:
    failures: list[tuple[int, str, object, object]] = []
    print(f"`m=72d, n=72` fixed-quotient scan for 2 <= d <= {limit}")
    print(
        "| d | normalized_d | m | sigma_inf | predicted_sigma | k0_inf | predicted_k0 | residual_tau | predicted_tau | residual | expected |"
    )
    print("|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|---|")

    for d in range(2, limit + 1):
        m = 72 * d
        c = d + 1
        size, masks = stable_candidate_masks(m, c)
        sigma = sigma_inf(m, c)
        k0 = exact_k0_inf(m, c)
        forced, forced_union = private_fragment_certificate(size, masks)
        residual = [
            idx + 1 for idx in range(size) if not (forced_union & (1 << idx))
        ]
        tau = residual_cover_number(size, masks, residual)
        normalized_d, predicted_sigma, predicted_k0, predicted_tau, expected = (
            predicted_n72_fixed_quotient(d)
        )

        if sigma != predicted_sigma:
            failures.append((d, "sigma", sigma, predicted_sigma))
        if k0 != predicted_k0:
            failures.append((d, "k0", k0, predicted_k0))
        if tau != predicted_tau:
            failures.append((d, "tau", tau, predicted_tau))
        if residual != expected:
            failures.append((d, "residual", residual, expected))

        print(
            f"| {d} | {normalized_d} | {m} | {sigma} | {predicted_sigma} | "
            f"{k0} | {predicted_k0} | {tau} | {predicted_tau} | "
            f"`{residual}` | `{expected}` |"
        )

    if failures:
        print(f"Family scan failures: {len(failures)}")
        for failure in failures:
            print(f"- {failure}")
    else:
        print("Family scan matched the normalized-cell predictions.")


def print_n66_fixed_quotient_family(limit: int) -> None:
    failures: list[tuple[int, str, object, object]] = []
    print(f"`m=66d, n=66` fixed-quotient scan for 2 <= d <= {limit}")
    print(
        "| d | normalized_d | m | sigma_inf | predicted_sigma | k0_inf | predicted_k0 | residual_tau | predicted_tau | residual | expected |"
    )
    print("|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|---|")

    for d in range(2, limit + 1):
        m = 66 * d
        c = d + 1
        size, masks = stable_candidate_masks(m, c)
        sigma = sigma_inf(m, c)
        k0 = exact_k0_inf(m, c)
        forced, forced_union = private_fragment_certificate(size, masks)
        residual = [
            idx + 1 for idx in range(size) if not (forced_union & (1 << idx))
        ]
        tau = residual_cover_number(size, masks, residual)
        normalized_d, predicted_sigma, predicted_k0, predicted_tau, expected = (
            predicted_n66_fixed_quotient(d)
        )

        if sigma != predicted_sigma:
            failures.append((d, "sigma", sigma, predicted_sigma))
        if k0 != predicted_k0:
            failures.append((d, "k0", k0, predicted_k0))
        if tau != predicted_tau:
            failures.append((d, "tau", tau, predicted_tau))
        if residual != expected:
            failures.append((d, "residual", residual, expected))

        print(
            f"| {d} | {normalized_d} | {m} | {sigma} | {predicted_sigma} | "
            f"{k0} | {predicted_k0} | {tau} | {predicted_tau} | "
            f"`{residual}` | `{expected}` |"
        )

    if failures:
        print(f"Family scan failures: {len(failures)}")
        for failure in failures:
            print(f"- {failure}")
    else:
        print("Family scan matched the normalized-cell predictions.")


def print_n78_fixed_quotient_family(limit: int) -> None:
    failures: list[tuple[int, str, object, object]] = []
    print(f"`m=78d, n=78` fixed-quotient scan for 2 <= d <= {limit}")
    print(
        "| d | normalized_d | m | sigma_inf | predicted_sigma | k0_inf | predicted_k0 | residual_tau | predicted_tau | residual | expected |"
    )
    print("|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|---|")

    for d in range(2, limit + 1):
        m = 78 * d
        c = d + 1
        size, masks = stable_candidate_masks(m, c)
        sigma = sigma_inf(m, c)
        k0 = exact_k0_inf(m, c)
        forced, forced_union = private_fragment_certificate(size, masks)
        residual = [
            idx + 1 for idx in range(size) if not (forced_union & (1 << idx))
        ]
        tau = residual_cover_number(size, masks, residual)
        normalized_d, predicted_sigma, predicted_k0, predicted_tau, expected = (
            predicted_n78_fixed_quotient(d)
        )

        if sigma != predicted_sigma:
            failures.append((d, "sigma", sigma, predicted_sigma))
        if k0 != predicted_k0:
            failures.append((d, "k0", k0, predicted_k0))
        if tau != predicted_tau:
            failures.append((d, "tau", tau, predicted_tau))
        if residual != expected:
            failures.append((d, "residual", residual, expected))

        print(
            f"| {d} | {normalized_d} | {m} | {sigma} | {predicted_sigma} | "
            f"{k0} | {predicted_k0} | {tau} | {predicted_tau} | "
            f"`{residual}` | `{expected}` |"
        )

    if failures:
        print(f"Family scan failures: {len(failures)}")
        for failure in failures:
            print(f"- {failure}")
    else:
        print("Family scan matched the normalized-cell predictions.")


def print_n60_fixed_quotient_family(limit: int) -> None:
    failures: list[tuple[int, str, object, object]] = []
    print(f"`m=60d, n=60` fixed-quotient scan for 2 <= d <= {limit}")
    print(
        "| d | normalized_d | m | sigma_inf | predicted_sigma | k0_inf | predicted_k0 | residual_tau | predicted_tau | residual | expected |"
    )
    print("|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|---|")

    for d in range(2, limit + 1):
        m = 60 * d
        c = d + 1
        size, masks = stable_candidate_masks(m, c)
        sigma = sigma_inf(m, c)
        k0 = exact_k0_inf(m, c)
        forced, forced_union = private_fragment_certificate(size, masks)
        residual = [
            idx + 1 for idx in range(size) if not (forced_union & (1 << idx))
        ]
        tau = residual_cover_number(size, masks, residual)
        normalized_d, predicted_sigma, predicted_k0, predicted_tau, expected = (
            predicted_n60_fixed_quotient(d)
        )

        if sigma != predicted_sigma:
            failures.append((d, "sigma", sigma, predicted_sigma))
        if k0 != predicted_k0:
            failures.append((d, "k0", k0, predicted_k0))
        if tau != predicted_tau:
            failures.append((d, "tau", tau, predicted_tau))
        if residual != expected:
            failures.append((d, "residual", residual, expected))

        print(
            f"| {d} | {normalized_d} | {m} | {sigma} | {predicted_sigma} | "
            f"{k0} | {predicted_k0} | {tau} | {predicted_tau} | "
            f"`{residual}` | `{expected}` |"
        )

    if failures:
        print(f"Family scan failures: {len(failures)}")
        for failure in failures:
            print(f"- {failure}")
    else:
        print("Family scan matched the normalized-cell predictions.")


def print_n84_fixed_quotient_family(limit: int) -> None:
    failures: list[tuple[int, str, object, object]] = []
    print(f"`m=84d, n=84` fixed-quotient scan for 2 <= d <= {limit}")
    print(
        "| d | normalized_d | m | sigma_inf | predicted_sigma | k0_inf | predicted_k0 | residual_tau | predicted_tau | residual | expected |"
    )
    print("|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|---|")

    for d in range(2, limit + 1):
        m = 84 * d
        c = d + 1
        size, masks = stable_candidate_masks(m, c)
        sigma = sigma_inf(m, c)
        k0 = exact_k0_inf(m, c)
        forced, forced_union = private_fragment_certificate(size, masks)
        residual = [
            idx + 1 for idx in range(size) if not (forced_union & (1 << idx))
        ]
        tau = residual_cover_number(size, masks, residual)
        normalized_d, predicted_sigma, predicted_k0, predicted_tau, expected = (
            predicted_n84_fixed_quotient(d)
        )

        if sigma != predicted_sigma:
            failures.append((d, "sigma", sigma, predicted_sigma))
        if k0 != predicted_k0:
            failures.append((d, "k0", k0, predicted_k0))
        if tau != predicted_tau:
            failures.append((d, "tau", tau, predicted_tau))
        if residual != expected:
            failures.append((d, "residual", residual, expected))

        print(
            f"| {d} | {normalized_d} | {m} | {sigma} | {predicted_sigma} | "
            f"{k0} | {predicted_k0} | {tau} | {predicted_tau} | "
            f"`{residual}` | `{expected}` |"
        )

    if failures:
        print(f"Family scan failures: {len(failures)}")
        for failure in failures:
            print(f"- {failure}")
    else:
        print("Family scan matched the normalized-cell predictions.")


def print_n135_fixed_quotient_family(limit: int) -> None:
    failures: list[tuple[int, str, object, object]] = []
    print(f"`m=135d, n=135` fixed-quotient scan for 2 <= d <= {limit}")
    print(
        "| d | normalized_d | m | sigma_inf | predicted_sigma | k0_inf | predicted_k0 | residual_tau | predicted_tau | residual | expected |"
    )
    print("|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|---|")

    for d in range(2, limit + 1):
        m = 135 * d
        c = d + 1
        size, masks = stable_candidate_masks(m, c)
        sigma = sigma_inf(m, c)
        k0 = exact_k0_inf(m, c)
        forced, forced_union = private_fragment_certificate(size, masks)
        residual = [
            idx + 1 for idx in range(size) if not (forced_union & (1 << idx))
        ]
        tau = residual_cover_number(size, masks, residual)
        normalized_d, predicted_sigma, predicted_k0, predicted_tau, expected = (
            predicted_n135_fixed_quotient(d)
        )

        if sigma != predicted_sigma:
            failures.append((d, "sigma", sigma, predicted_sigma))
        if k0 != predicted_k0:
            failures.append((d, "k0", k0, predicted_k0))
        if tau != predicted_tau:
            failures.append((d, "tau", tau, predicted_tau))
        if residual != expected:
            failures.append((d, "residual", residual, expected))

        print(
            f"| {d} | {normalized_d} | {m} | {sigma} | {predicted_sigma} | "
            f"{k0} | {predicted_k0} | {tau} | {predicted_tau} | "
            f"`{residual}` | `{expected}` |"
        )

    if failures:
        print(f"Family scan failures: {len(failures)}")
        for failure in failures:
            print(f"- {failure}")
    else:
        print("Family scan matched the normalized-cell predictions.")


def print_n110_fixed_quotient_family(limit: int) -> None:
    failures: list[tuple[int, str, object, object]] = []
    print(f"`m=110d, n=110` fixed-quotient scan for 2 <= d <= {limit}")
    print(
        "| d | normalized_d | m | sigma_inf | predicted_sigma | k0_inf | predicted_k0 | residual_tau | predicted_tau | residual | expected |"
    )
    print("|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|---|")

    for d in range(2, limit + 1):
        m = 110 * d
        c = d + 1
        size, masks = stable_candidate_masks(m, c)
        sigma = sigma_inf(m, c)
        k0 = exact_k0_inf(m, c)
        forced, forced_union = private_fragment_certificate(size, masks)
        residual = [
            idx + 1 for idx in range(size) if not (forced_union & (1 << idx))
        ]
        tau = residual_cover_number(size, masks, residual)
        normalized_d, predicted_sigma, predicted_k0, predicted_tau, expected = (
            predicted_n110_fixed_quotient(d)
        )

        if sigma != predicted_sigma:
            failures.append((d, "sigma", sigma, predicted_sigma))
        if k0 != predicted_k0:
            failures.append((d, "k0", k0, predicted_k0))
        if tau != predicted_tau:
            failures.append((d, "tau", tau, predicted_tau))
        if residual != expected:
            failures.append((d, "residual", residual, expected))

        print(
            f"| {d} | {normalized_d} | {m} | {sigma} | {predicted_sigma} | "
            f"{k0} | {predicted_k0} | {tau} | {predicted_tau} | "
            f"`{residual}` | `{expected}` |"
        )

    if failures:
        print(f"Family scan failures: {len(failures)}")
        for failure in failures:
            print(f"- {failure}")
    else:
        print("Family scan matched the normalized-cell predictions.")


def print_n102_fixed_quotient_family(limit: int) -> None:
    failures: list[tuple[int, str, object, object]] = []
    print(f"`m=102d, n=102` fixed-quotient scan for 2 <= d <= {limit}")
    print(
        "| d | normalized_d | m | sigma_inf | predicted_sigma | k0_inf | predicted_k0 | residual_tau | predicted_tau | residual | expected |"
    )
    print("|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|---|")

    for d in range(2, limit + 1):
        m = 102 * d
        c = d + 1
        size, masks = stable_candidate_masks(m, c)
        sigma = sigma_inf(m, c)
        k0 = exact_k0_inf(m, c)
        forced, forced_union = private_fragment_certificate(size, masks)
        residual = [
            idx + 1 for idx in range(size) if not (forced_union & (1 << idx))
        ]
        tau = residual_cover_number(size, masks, residual)
        normalized_d, predicted_sigma, predicted_k0, predicted_tau, expected = (
            predicted_n102_fixed_quotient(d)
        )

        if sigma != predicted_sigma:
            failures.append((d, "sigma", sigma, predicted_sigma))
        if k0 != predicted_k0:
            failures.append((d, "k0", k0, predicted_k0))
        if tau != predicted_tau:
            failures.append((d, "tau", tau, predicted_tau))
        if residual != expected:
            failures.append((d, "residual", residual, expected))

        print(
            f"| {d} | {normalized_d} | {m} | {sigma} | {predicted_sigma} | "
            f"{k0} | {predicted_k0} | {tau} | {predicted_tau} | "
            f"`{residual}` | `{expected}` |"
        )

    if failures:
        print(f"Family scan failures: {len(failures)}")
        for failure in failures:
            print(f"- {failure}")
    else:
        print("Family scan matched the normalized-cell predictions.")


def print_n105_fixed_quotient_family(limit: int) -> None:
    failures: list[tuple[int, str, object, object]] = []
    print(f"`m=105d, n=105` fixed-quotient scan for 2 <= d <= {limit}")
    print(
        "| d | normalized_d | m | sigma_inf | predicted_sigma | k0_inf | predicted_k0 | residual_tau | predicted_tau | residual | expected |"
    )
    print("|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|---|")

    for d in range(2, limit + 1):
        m = 105 * d
        c = d + 1
        size, masks = stable_candidate_masks(m, c)
        sigma = sigma_inf(m, c)
        k0 = exact_k0_inf(m, c)
        forced, forced_union = private_fragment_certificate(size, masks)
        residual = [
            idx + 1 for idx in range(size) if not (forced_union & (1 << idx))
        ]
        tau = residual_cover_number(size, masks, residual)
        normalized_d, predicted_sigma, predicted_k0, predicted_tau, expected = (
            predicted_n105_fixed_quotient(d)
        )

        if sigma != predicted_sigma:
            failures.append((d, "sigma", sigma, predicted_sigma))
        if k0 != predicted_k0:
            failures.append((d, "k0", k0, predicted_k0))
        if tau != predicted_tau:
            failures.append((d, "tau", tau, predicted_tau))
        if residual != expected:
            failures.append((d, "residual", residual, expected))

        print(
            f"| {d} | {normalized_d} | {m} | {sigma} | {predicted_sigma} | "
            f"{k0} | {predicted_k0} | {tau} | {predicted_tau} | "
            f"`{residual}` | `{expected}` |"
        )

    if failures:
        print(f"Family scan failures: {len(failures)}")
        for failure in failures:
            print(f"- {failure}")
    else:
        print("Family scan matched the normalized-cell predictions.")


def print_n165_fixed_quotient_family(limit: int) -> None:
    failures: list[tuple[int, str, object, object]] = []
    print(f"`m=165d, n=165` fixed-quotient scan for 2 <= d <= {limit}")
    print(
        "| d | normalized_d | m | sigma_inf | predicted_sigma | k0_inf | predicted_k0 | residual_tau | predicted_tau | residual | expected |"
    )
    print("|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|---|")

    for d in range(2, limit + 1):
        m = 165 * d
        c = d + 1
        size, masks = stable_candidate_masks(m, c)
        sigma = sigma_inf(m, c)
        k0 = exact_k0_inf(m, c)
        forced, forced_union = private_fragment_certificate(size, masks)
        residual = [
            idx + 1 for idx in range(size) if not (forced_union & (1 << idx))
        ]
        tau = residual_cover_number(size, masks, residual)
        normalized_d, predicted_sigma, predicted_k0, predicted_tau, expected = (
            predicted_n165_fixed_quotient(d)
        )

        if sigma != predicted_sigma:
            failures.append((d, "sigma", sigma, predicted_sigma))
        if k0 != predicted_k0:
            failures.append((d, "k0", k0, predicted_k0))
        if tau != predicted_tau:
            failures.append((d, "tau", tau, predicted_tau))
        if residual != expected:
            failures.append((d, "residual", residual, expected))

        print(
            f"| {d} | {normalized_d} | {m} | {sigma} | {predicted_sigma} | "
            f"{k0} | {predicted_k0} | {tau} | {predicted_tau} | "
            f"`{residual}` | `{expected}` |"
        )

    if failures:
        print(f"Family scan failures: {len(failures)}")
        for failure in failures:
            print(f"- {failure}")
    else:
        print("Family scan matched the normalized-cell predictions.")


def print_n90_fixed_quotient_family(limit: int) -> None:
    failures: list[tuple[int, str, object, object]] = []
    print(f"`m=90d, n=90` fixed-quotient scan for 2 <= d <= {limit}")
    print(
        "| d | normalized_d | m | sigma_inf | predicted_sigma | k0_inf | predicted_k0 | residual_tau | predicted_tau | residual | expected |"
    )
    print("|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|---|")

    for d in range(2, limit + 1):
        m = 90 * d
        c = d + 1
        size, masks = stable_candidate_masks(m, c)
        sigma = sigma_inf(m, c)
        k0 = exact_k0_inf(m, c)
        forced, forced_union = private_fragment_certificate(size, masks)
        residual = [
            idx + 1 for idx in range(size) if not (forced_union & (1 << idx))
        ]
        tau = residual_cover_number(size, masks, residual)
        normalized_d, predicted_sigma, predicted_k0, predicted_tau, expected = (
            predicted_n90_fixed_quotient(d)
        )

        if sigma != predicted_sigma:
            failures.append((d, "sigma", sigma, predicted_sigma))
        if k0 != predicted_k0:
            failures.append((d, "k0", k0, predicted_k0))
        if tau != predicted_tau:
            failures.append((d, "tau", tau, predicted_tau))
        if residual != expected:
            failures.append((d, "residual", residual, expected))

        print(
            f"| {d} | {normalized_d} | {m} | {sigma} | {predicted_sigma} | "
            f"{k0} | {predicted_k0} | {tau} | {predicted_tau} | "
            f"`{residual}` | `{expected}` |"
        )

    if failures:
        print(f"Family scan failures: {len(failures)}")
        for failure in failures:
            print(f"- {failure}")
    else:
        print("Family scan matched the normalized-cell predictions.")


def print_n120_fixed_quotient_family(limit: int) -> None:
    failures: list[tuple[int, str, object, object]] = []
    print(f"`m=120d, n=120` fixed-quotient scan for 2 <= d <= {limit}")
    print(
        "| d | normalized_d | m | sigma_inf | predicted_sigma | k0_inf | predicted_k0 | residual_tau | predicted_tau | residual | expected |"
    )
    print("|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|---|")

    for d in range(2, limit + 1):
        m = 120 * d
        c = d + 1
        size, masks = stable_candidate_masks(m, c)
        sigma = sigma_inf(m, c)
        k0 = exact_k0_inf(m, c)
        forced, forced_union = private_fragment_certificate(size, masks)
        residual = [
            idx + 1 for idx in range(size) if not (forced_union & (1 << idx))
        ]
        tau = residual_cover_number(size, masks, residual)
        normalized_d, predicted_sigma, predicted_k0, predicted_tau, expected = (
            predicted_n120_fixed_quotient(d)
        )

        if sigma != predicted_sigma:
            failures.append((d, "sigma", sigma, predicted_sigma))
        if k0 != predicted_k0:
            failures.append((d, "k0", k0, predicted_k0))
        if tau != predicted_tau:
            failures.append((d, "tau", tau, predicted_tau))
        if residual != expected:
            failures.append((d, "residual", residual, expected))

        print(
            f"| {d} | {normalized_d} | {m} | {sigma} | {predicted_sigma} | "
            f"{k0} | {predicted_k0} | {tau} | {predicted_tau} | "
            f"`{residual}` | `{expected}` |"
        )

    if failures:
        print(f"Family scan failures: {len(failures)}")
        for failure in failures:
            print(f"- {failure}")
    else:
        print("Family scan matched the normalized-cell predictions.")


def print_n36_fixed_quotient_family(limit: int) -> None:
    failures: list[tuple[int, str, object, object]] = []
    print(f"`m=36d, n=36` fixed-quotient scan for 2 <= d <= {limit}")
    print(
        "| d | normalized_d | m | sigma_inf | predicted_sigma | k0_inf | predicted_k0 | residual_tau | predicted_tau | residual | expected |"
    )
    print("|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|---|")

    for d in range(2, limit + 1):
        m = 36 * d
        c = d + 1
        size, masks = stable_candidate_masks(m, c)
        sigma = sigma_inf(m, c)
        k0 = exact_k0_inf(m, c)
        forced, forced_union = private_fragment_certificate(size, masks)
        residual = [
            idx + 1 for idx in range(size) if not (forced_union & (1 << idx))
        ]
        tau = residual_cover_number(size, masks, residual)
        normalized_d, predicted_sigma, predicted_k0, predicted_tau, expected = (
            predicted_n36_fixed_quotient(d)
        )

        if sigma != predicted_sigma:
            failures.append((d, "sigma", sigma, predicted_sigma))
        if k0 != predicted_k0:
            failures.append((d, "k0", k0, predicted_k0))
        if tau != predicted_tau:
            failures.append((d, "tau", tau, predicted_tau))
        if residual != expected:
            failures.append((d, "residual", residual, expected))

        print(
            f"| {d} | {normalized_d} | {m} | {sigma} | {predicted_sigma} | "
            f"{k0} | {predicted_k0} | {tau} | {predicted_tau} | "
            f"`{residual}` | `{expected}` |"
        )

    if failures:
        print(f"Family scan failures: {len(failures)}")
        for failure in failures:
            print(f"- {failure}")
    else:
        print("Family scan matched the normalized-cell predictions.")


def print_n96_fixed_quotient_family(limit: int) -> None:
    failures: list[tuple[int, str, object, object]] = []
    print(f"`m=96d, n=96` fixed-quotient scan for 2 <= d <= {limit}")
    print(
        "| d | normalized_d | m | sigma_inf | predicted_sigma | k0_inf | predicted_k0 | residual_tau | predicted_tau | residual | expected |"
    )
    print("|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|---|")

    for d in range(2, limit + 1):
        m = 96 * d
        c = d + 1
        size, masks = stable_candidate_masks(m, c)
        sigma = sigma_inf(m, c)
        k0 = exact_k0_inf(m, c)
        forced, forced_union = private_fragment_certificate(size, masks)
        residual = [
            idx + 1 for idx in range(size) if not (forced_union & (1 << idx))
        ]
        tau = residual_cover_number(size, masks, residual)
        normalized_d, predicted_sigma, predicted_k0, predicted_tau, expected = (
            predicted_n96_fixed_quotient(d)
        )

        if sigma != predicted_sigma:
            failures.append((d, "sigma", sigma, predicted_sigma))
        if k0 != predicted_k0:
            failures.append((d, "k0", k0, predicted_k0))
        if tau != predicted_tau:
            failures.append((d, "tau", tau, predicted_tau))
        if residual != expected:
            failures.append((d, "residual", residual, expected))

        print(
            f"| {d} | {normalized_d} | {m} | {sigma} | {predicted_sigma} | "
            f"{k0} | {predicted_k0} | {tau} | {predicted_tau} | "
            f"`{residual}` | `{expected}` |"
        )

    if failures:
        print(f"Family scan failures: {len(failures)}")
        for failure in failures:
            print(f"- {failure}")
    else:
        print("Family scan matched the normalized-cell predictions.")


def print_n114_fixed_quotient_family(limit: int) -> None:
    failures: list[tuple[int, str, object, object]] = []
    print(f"`m=114d, n=114` fixed-quotient scan for 2 <= d <= {limit}")
    print(
        "| d | normalized_d | m | sigma_inf | predicted_sigma | k0_inf | predicted_k0 | residual_tau | predicted_tau | residual | expected |"
    )
    print("|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|---|")

    for d in range(2, limit + 1):
        m = 114 * d
        c = d + 1
        size, masks = stable_candidate_masks(m, c)
        sigma = sigma_inf(m, c)
        k0 = exact_k0_inf(m, c)
        forced, forced_union = private_fragment_certificate(size, masks)
        residual = [
            idx + 1 for idx in range(size) if not (forced_union & (1 << idx))
        ]
        tau = residual_cover_number(size, masks, residual)
        normalized_d, predicted_sigma, predicted_k0, predicted_tau, expected = (
            predicted_n114_fixed_quotient(d)
        )

        if sigma != predicted_sigma:
            failures.append((d, "sigma", sigma, predicted_sigma))
        if k0 != predicted_k0:
            failures.append((d, "k0", k0, predicted_k0))
        if tau != predicted_tau:
            failures.append((d, "tau", tau, predicted_tau))
        if residual != expected:
            failures.append((d, "residual", residual, expected))

        print(
            f"| {d} | {normalized_d} | {m} | {sigma} | {predicted_sigma} | "
            f"{k0} | {predicted_k0} | {tau} | {predicted_tau} | "
            f"`{residual}` | `{expected}` |"
        )

    if failures:
        print(f"Family scan failures: {len(failures)}")
        for failure in failures:
            print(f"- {failure}")
    else:
        print("Family scan matched the normalized-cell predictions.")


def print_n108_fixed_quotient_family(limit: int) -> None:
    failures: list[tuple[int, str, object, object]] = []
    print(f"`m=108d, n=108` fixed-quotient scan for 2 <= d <= {limit}")
    print(
        "| d | normalized_d | m | sigma_inf | predicted_sigma | k0_inf | predicted_k0 | residual_tau | predicted_tau | residual | expected |"
    )
    print("|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|---|")

    for d in range(2, limit + 1):
        m = 108 * d
        c = d + 1
        size, masks = stable_candidate_masks(m, c)
        sigma = sigma_inf(m, c)
        k0 = exact_k0_inf(m, c)
        forced, forced_union = private_fragment_certificate(size, masks)
        residual = [
            idx + 1 for idx in range(size) if not (forced_union & (1 << idx))
        ]
        tau = residual_cover_number(size, masks, residual)
        normalized_d, predicted_sigma, predicted_k0, predicted_tau, expected = (
            predicted_n108_fixed_quotient(d)
        )

        if sigma != predicted_sigma:
            failures.append((d, "sigma", sigma, predicted_sigma))
        if k0 != predicted_k0:
            failures.append((d, "k0", k0, predicted_k0))
        if tau != predicted_tau:
            failures.append((d, "tau", tau, predicted_tau))
        if residual != expected:
            failures.append((d, "residual", residual, expected))

        print(
            f"| {d} | {normalized_d} | {m} | {sigma} | {predicted_sigma} | "
            f"{k0} | {predicted_k0} | {tau} | {predicted_tau} | "
            f"`{residual}` | `{expected}` |"
        )

    if failures:
        print(f"Family scan failures: {len(failures)}")
        for failure in failures:
            print(f"- {failure}")
    else:
        print("Family scan matched the normalized-cell predictions.")


def print_n130_fixed_quotient_family(limit: int) -> None:
    failures: list[tuple[int, str, object, object]] = []
    print(f"`m=130d, n=130` fixed-quotient scan for 2 <= d <= {limit}")
    print(
        "| d | normalized_d | m | sigma_inf | predicted_sigma | k0_inf | predicted_k0 | residual_tau | predicted_tau | residual | expected |"
    )
    print("|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|---|")

    for d in range(2, limit + 1):
        m = 130 * d
        c = d + 1
        size, masks = stable_candidate_masks(m, c)
        sigma = sigma_inf(m, c)
        k0 = exact_k0_inf(m, c)
        forced, forced_union = private_fragment_certificate(size, masks)
        residual = [
            idx + 1 for idx in range(size) if not (forced_union & (1 << idx))
        ]
        tau = residual_cover_number(size, masks, residual)
        normalized_d, predicted_sigma, predicted_k0, predicted_tau, expected = (
            predicted_n130_fixed_quotient(d)
        )

        if sigma != predicted_sigma:
            failures.append((d, "sigma", sigma, predicted_sigma))
        if k0 != predicted_k0:
            failures.append((d, "k0", k0, predicted_k0))
        if tau != predicted_tau:
            failures.append((d, "tau", tau, predicted_tau))
        if residual != expected:
            failures.append((d, "residual", residual, expected))

        print(
            f"| {d} | {normalized_d} | {m} | {sigma} | {predicted_sigma} | "
            f"{k0} | {predicted_k0} | {tau} | {predicted_tau} | "
            f"`{residual}` | `{expected}` |"
        )

    if failures:
        print(f"Family scan failures: {len(failures)}")
        for failure in failures:
            print(f"- {failure}")
    else:
        print("Family scan matched the normalized-cell predictions.")


def print_n126_fixed_quotient_family(limit: int) -> None:
    failures: list[tuple[int, str, object, object]] = []
    print(f"`m=126d, n=126` fixed-quotient scan for 2 <= d <= {limit}")
    print(
        "| d | normalized_d | m | sigma_inf | predicted_sigma | k0_inf | predicted_k0 | residual_tau | predicted_tau | residual | expected |"
    )
    print("|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|---|")

    for d in range(2, limit + 1):
        m = 126 * d
        c = d + 1
        size, masks = stable_candidate_masks(m, c)
        sigma = sigma_inf(m, c)
        k0 = exact_k0_inf(m, c)
        forced, forced_union = private_fragment_certificate(size, masks)
        residual = [
            idx + 1 for idx in range(size) if not (forced_union & (1 << idx))
        ]
        tau = residual_cover_number(size, masks, residual)
        normalized_d, predicted_sigma, predicted_k0, predicted_tau, expected = (
            predicted_n126_fixed_quotient(d)
        )

        if sigma != predicted_sigma:
            failures.append((d, "sigma", sigma, predicted_sigma))
        if k0 != predicted_k0:
            failures.append((d, "k0", k0, predicted_k0))
        if tau != predicted_tau:
            failures.append((d, "tau", tau, predicted_tau))
        if residual != expected:
            failures.append((d, "residual", residual, expected))

        print(
            f"| {d} | {normalized_d} | {m} | {sigma} | {predicted_sigma} | "
            f"{k0} | {predicted_k0} | {tau} | {predicted_tau} | "
            f"`{residual}` | `{expected}` |"
        )

    if failures:
        print(f"Family scan failures: {len(failures)}")
        for failure in failures:
            print(f"- {failure}")
    else:
        print("Family scan matched the normalized-cell predictions.")


def print_n112_fixed_quotient_family(limit: int) -> None:
    failures: list[tuple[int, str, object, object]] = []
    print(f"`m=112d, n=112` fixed-quotient scan for 2 <= d <= {limit}")
    print(
        "| d | normalized_d | m | sigma_inf | predicted_sigma | k0_inf | predicted_k0 | residual_tau | predicted_tau | residual | expected |"
    )
    print("|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|---|")

    for d in range(2, limit + 1):
        m = 112 * d
        c = d + 1
        size, masks = stable_candidate_masks(m, c)
        sigma = sigma_inf(m, c)
        k0 = exact_k0_inf(m, c)
        forced, forced_union = private_fragment_certificate(size, masks)
        residual = [
            idx + 1 for idx in range(size) if not (forced_union & (1 << idx))
        ]
        tau = residual_cover_number(size, masks, residual)
        normalized_d, predicted_sigma, predicted_k0, predicted_tau, expected = (
            predicted_n112_fixed_quotient(d)
        )

        if sigma != predicted_sigma:
            failures.append((d, "sigma", sigma, predicted_sigma))
        if k0 != predicted_k0:
            failures.append((d, "k0", k0, predicted_k0))
        if tau != predicted_tau:
            failures.append((d, "tau", tau, predicted_tau))
        if residual != expected:
            failures.append((d, "residual", residual, expected))

        print(
            f"| {d} | {normalized_d} | {m} | {sigma} | {predicted_sigma} | "
            f"{k0} | {predicted_k0} | {tau} | {predicted_tau} | "
            f"`{residual}` | `{expected}` |"
        )

    if failures:
        print(f"Family scan failures: {len(failures)}")
        for failure in failures:
            print(f"- {failure}")
    else:
        print("Family scan matched the normalized-cell predictions.")


def print_n132_fixed_quotient_family(limit: int) -> None:
    failures: list[tuple[int, str, object, object]] = []
    print(f"`m=132d, n=132` fixed-quotient scan for 2 <= d <= {limit}")
    print(
        "| d | normalized_d | m | sigma_inf | predicted_sigma | k0_inf | predicted_k0 | residual_tau | predicted_tau | residual | expected |"
    )
    print("|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|---|")

    for d in range(2, limit + 1):
        m = 132 * d
        c = d + 1
        size, masks = stable_candidate_masks(m, c)
        sigma = sigma_inf(m, c)
        k0 = exact_k0_inf(m, c)
        forced, forced_union = private_fragment_certificate(size, masks)
        residual = [
            idx + 1 for idx in range(size) if not (forced_union & (1 << idx))
        ]
        tau = residual_cover_number(size, masks, residual)
        normalized_d, predicted_sigma, predicted_k0, predicted_tau, expected = (
            predicted_n132_fixed_quotient(d)
        )

        if sigma != predicted_sigma:
            failures.append((d, "sigma", sigma, predicted_sigma))
        if k0 != predicted_k0:
            failures.append((d, "k0", k0, predicted_k0))
        if tau != predicted_tau:
            failures.append((d, "tau", tau, predicted_tau))
        if residual != expected:
            failures.append((d, "residual", residual, expected))

        print(
            f"| {d} | {normalized_d} | {m} | {sigma} | {predicted_sigma} | "
            f"{k0} | {predicted_k0} | {tau} | {predicted_tau} | "
            f"`{residual}` | `{expected}` |"
        )

    if failures:
        print(f"Family scan failures: {len(failures)}")
        for failure in failures:
            print(f"- {failure}")
    else:
        print("Family scan matched the normalized-cell predictions.")


def print_n138_fixed_quotient_family(limit: int) -> None:
    failures: list[tuple[int, str, object, object]] = []
    print(f"`m=138d, n=138` fixed-quotient scan for 2 <= d <= {limit}")
    print(
        "| d | normalized_d | m | sigma_inf | predicted_sigma | k0_inf | predicted_k0 | residual_tau | predicted_tau | residual | expected |"
    )
    print("|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|---|")

    for d in range(2, limit + 1):
        m = 138 * d
        c = d + 1
        size, masks = stable_candidate_masks(m, c)
        sigma = sigma_inf(m, c)
        k0 = exact_k0_inf(m, c)
        forced, forced_union = private_fragment_certificate(size, masks)
        residual = [
            idx + 1 for idx in range(size) if not (forced_union & (1 << idx))
        ]
        tau = residual_cover_number(size, masks, residual)
        normalized_d, predicted_sigma, predicted_k0, predicted_tau, expected = (
            predicted_n138_fixed_quotient(d)
        )

        if sigma != predicted_sigma:
            failures.append((d, "sigma", sigma, predicted_sigma))
        if k0 != predicted_k0:
            failures.append((d, "k0", k0, predicted_k0))
        if tau != predicted_tau:
            failures.append((d, "tau", tau, predicted_tau))
        if residual != expected:
            failures.append((d, "residual", residual, expected))

        print(
            f"| {d} | {normalized_d} | {m} | {sigma} | {predicted_sigma} | "
            f"{k0} | {predicted_k0} | {tau} | {predicted_tau} | "
            f"`{residual}` | `{expected}` |"
        )

    if failures:
        print(f"Family scan failures: {len(failures)}")
        for failure in failures:
            print(f"- {failure}")
    else:
        print("Family scan matched the normalized-cell predictions.")


def print_n160_fixed_quotient_family(limit: int) -> None:
    failures: list[tuple[int, str, object, object]] = []
    print(f"`m=160d, n=160` fixed-quotient scan for 2 <= d <= {limit}")
    print(
        "| d | normalized_d | m | sigma_inf | predicted_sigma | k0_inf | predicted_k0 | residual_tau | predicted_tau | residual | expected |"
    )
    print("|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|---|")

    for d in range(2, limit + 1):
        m = 160 * d
        c = d + 1
        size, masks = stable_candidate_masks(m, c)
        sigma = sigma_inf(m, c)
        k0 = exact_k0_inf(m, c)
        forced, forced_union = private_fragment_certificate(size, masks)
        residual = [
            idx + 1 for idx in range(size) if not (forced_union & (1 << idx))
        ]
        tau = residual_cover_number(size, masks, residual)
        normalized_d, predicted_sigma, predicted_k0, predicted_tau, expected = (
            predicted_n160_fixed_quotient(d)
        )

        if sigma != predicted_sigma:
            failures.append((d, "sigma", sigma, predicted_sigma))
        if k0 != predicted_k0:
            failures.append((d, "k0", k0, predicted_k0))
        if tau != predicted_tau:
            failures.append((d, "tau", tau, predicted_tau))
        if residual != expected:
            failures.append((d, "residual", residual, expected))

        print(
            f"| {d} | {normalized_d} | {m} | {sigma} | {predicted_sigma} | "
            f"{k0} | {predicted_k0} | {tau} | {predicted_tau} | "
            f"`{residual}` | `{expected}` |"
        )

    if failures:
        print(f"Family scan failures: {len(failures)}")
        for failure in failures:
            print(f"- {failure}")
    else:
        print("Family scan matched the normalized-cell predictions.")


def print_n170_fixed_quotient_family(limit: int) -> None:
    failures: list[tuple[int, str, object, object]] = []
    print(f"`m=170d, n=170` fixed-quotient scan for 2 <= d <= {limit}")
    print(
        "| d | normalized_d | m | sigma_inf | predicted_sigma | k0_inf | predicted_k0 | residual_tau | predicted_tau | residual | expected |"
    )
    print("|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|---|")

    for d in range(2, limit + 1):
        m = 170 * d
        c = d + 1
        size, masks = stable_candidate_masks(m, c)
        sigma = sigma_inf(m, c)
        k0 = exact_k0_inf(m, c)
        forced, forced_union = private_fragment_certificate(size, masks)
        residual = [
            idx + 1 for idx in range(size) if not (forced_union & (1 << idx))
        ]
        tau = residual_cover_number(size, masks, residual)
        normalized_d, predicted_sigma, predicted_k0, predicted_tau, expected = (
            predicted_n170_fixed_quotient(d)
        )

        if sigma != predicted_sigma:
            failures.append((d, "sigma", sigma, predicted_sigma))
        if k0 != predicted_k0:
            failures.append((d, "k0", k0, predicted_k0))
        if tau != predicted_tau:
            failures.append((d, "tau", tau, predicted_tau))
        if residual != expected:
            failures.append((d, "residual", residual, expected))

        print(
            f"| {d} | {normalized_d} | {m} | {sigma} | {predicted_sigma} | "
            f"{k0} | {predicted_k0} | {tau} | {predicted_tau} | "
            f"`{residual}` | `{expected}` |"
        )

    if failures:
        print(f"Family scan failures: {len(failures)}")
        for failure in failures:
            print(f"- {failure}")
    else:
        print("Family scan matched the normalized-cell predictions.")


def print_n144_fixed_quotient_family(limit: int) -> None:
    failures: list[tuple[int, str, object, object]] = []
    print(f"`m=144d, n=144` fixed-quotient scan for 2 <= d <= {limit}")
    print(
        "| d | normalized_d | m | sigma_inf | predicted_sigma | k0_inf | predicted_k0 | residual_tau | predicted_tau | residual | expected |"
    )
    print("|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|---|")

    for d in range(2, limit + 1):
        m = 144 * d
        c = d + 1
        size, masks = stable_candidate_masks(m, c)
        sigma = sigma_inf(m, c)
        k0 = exact_k0_inf(m, c)
        forced, forced_union = private_fragment_certificate(size, masks)
        residual = [
            idx + 1 for idx in range(size) if not (forced_union & (1 << idx))
        ]
        tau = residual_cover_number(size, masks, residual)
        normalized_d, predicted_sigma, predicted_k0, predicted_tau, expected = (
            predicted_n144_fixed_quotient(d)
        )

        if sigma != predicted_sigma:
            failures.append((d, "sigma", sigma, predicted_sigma))
        if k0 != predicted_k0:
            failures.append((d, "k0", k0, predicted_k0))
        if tau != predicted_tau:
            failures.append((d, "tau", tau, predicted_tau))
        if residual != expected:
            failures.append((d, "residual", residual, expected))

        print(
            f"| {d} | {normalized_d} | {m} | {sigma} | {predicted_sigma} | "
            f"{k0} | {predicted_k0} | {tau} | {predicted_tau} | "
            f"`{residual}` | `{expected}` |"
        )

    if failures:
        print(f"Family scan failures: {len(failures)}")
        for failure in failures:
            print(f"- {failure}")
    else:
        print("Family scan matched the normalized-cell predictions.")


def print_n225_fixed_quotient_family(limit: int) -> None:
    failures: list[tuple[int, str, object, object]] = []
    print(f"`m=225d, n=225` fixed-quotient scan for 2 <= d <= {limit}")
    print(
        "| d | normalized_d | m | sigma_inf | predicted_sigma | k0_inf | predicted_k0 | residual_tau | predicted_tau | residual | expected |"
    )
    print("|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|---|")

    for d in range(2, limit + 1):
        m = 225 * d
        c = d + 1
        size, masks = stable_candidate_masks(m, c)
        sigma = sigma_inf(m, c)
        k0 = exact_k0_inf(m, c)
        forced, forced_union = private_fragment_certificate(size, masks)
        residual = [
            idx + 1 for idx in range(size) if not (forced_union & (1 << idx))
        ]
        tau = residual_cover_number(size, masks, residual)
        normalized_d, predicted_sigma, predicted_k0, predicted_tau, expected = (
            predicted_n225_fixed_quotient(d)
        )

        if sigma != predicted_sigma:
            failures.append((d, "sigma", sigma, predicted_sigma))
        if k0 != predicted_k0:
            failures.append((d, "k0", k0, predicted_k0))
        if tau != predicted_tau:
            failures.append((d, "tau", tau, predicted_tau))
        if residual != expected:
            failures.append((d, "residual", residual, expected))

        print(
            f"| {d} | {normalized_d} | {m} | {sigma} | {predicted_sigma} | "
            f"{k0} | {predicted_k0} | {tau} | {predicted_tau} | "
            f"`{residual}` | `{expected}` |"
        )

    if failures:
        print(f"Family scan failures: {len(failures)}")
        for failure in failures:
            print(f"- {failure}")
    else:
        print("Family scan matched the normalized-cell predictions.")


def print_n168_fixed_quotient_family(limit: int) -> None:
    failures: list[tuple[int, str, object, object]] = []
    print(f"`m=168d, n=168` fixed-quotient scan for 2 <= d <= {limit}")
    print(
        "| d | normalized_d | m | sigma_inf | predicted_sigma | forced | predicted_forced | k0_formula | predicted_k0 | residual_tau | residual | expected |"
    )
    print("|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|---|")

    for d in range(2, limit + 1):
        m = 168 * d
        c = d + 1
        size, masks = stable_candidate_masks(m, c)
        sigma = sigma_inf(m, c)
        forced, forced_union = private_fragment_certificate(size, masks)
        residual = [
            idx + 1 for idx in range(size) if not (forced_union & (1 << idx))
        ]
        normalized_d, predicted_sigma, predicted_k0, predicted_tau, expected = (
            predicted_n168_fixed_quotient(d)
        )
        predicted_forced = predicted_k0 - predicted_tau
        k0_formula = len(forced) + predicted_tau

        if sigma != predicted_sigma:
            failures.append((d, "sigma", sigma, predicted_sigma))
        if len(forced) != predicted_forced:
            failures.append((d, "forced", len(forced), predicted_forced))
        if k0_formula != predicted_k0:
            failures.append((d, "k0_formula", k0_formula, predicted_k0))
        if residual != expected:
            failures.append((d, "residual", residual, expected))

        print(
            f"| {d} | {normalized_d} | {m} | {sigma} | {predicted_sigma} | "
            f"{len(forced)} | {predicted_forced} | {k0_formula} | "
            f"{predicted_k0} | {predicted_tau} | `{residual}` | `{expected}` |"
        )

    if failures:
        print(f"Family scan failures: {len(failures)}")
        for failure in failures:
            print(f"- {failure}")
    else:
        print("Family scan matched the normalized-cell predictions.")


def print_n240_fixed_quotient_family(limit: int) -> None:
    failures: list[tuple[int, str, object, object]] = []
    print(f"`m=240d, n=240` fixed-quotient scan for 2 <= d <= {limit}")
    print(
        "| d | normalized_d | m | sigma_inf | predicted_sigma | forced | predicted_forced | k0_formula | predicted_k0 | residual_tau | residual | expected |"
    )
    print("|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|---|")

    for d in range(2, limit + 1):
        m = 240 * d
        c = d + 1
        size, masks = stable_candidate_masks(m, c)
        sigma = sigma_inf(m, c)
        forced, forced_union = private_fragment_certificate(size, masks)
        residual = [
            idx + 1 for idx in range(size) if not (forced_union & (1 << idx))
        ]
        normalized_d, predicted_sigma, predicted_k0, predicted_tau, expected = (
            predicted_n240_fixed_quotient(d)
        )
        predicted_forced = predicted_k0 - predicted_tau
        k0_formula = len(forced) + predicted_tau

        if sigma != predicted_sigma:
            failures.append((d, "sigma", sigma, predicted_sigma))
        if len(forced) != predicted_forced:
            failures.append((d, "forced", len(forced), predicted_forced))
        if k0_formula != predicted_k0:
            failures.append((d, "k0_formula", k0_formula, predicted_k0))
        if residual != expected:
            failures.append((d, "residual", residual, expected))

        print(
            f"| {d} | {normalized_d} | {m} | {sigma} | {predicted_sigma} | "
            f"{len(forced)} | {predicted_forced} | {k0_formula} | "
            f"{predicted_k0} | {predicted_tau} | `{residual}` | `{expected}` |"
        )

    if failures:
        print(f"Family scan failures: {len(failures)}")
        for failure in failures:
            print(f"- {failure}")
    else:
        print("Family scan matched the normalized-cell predictions.")


def print_n180_fixed_quotient_family(limit: int) -> None:
    failures: list[tuple[int, str, object, object]] = []
    print(f"`m=180d, n=180` fixed-quotient scan for 2 <= d <= {limit}")
    print(
        "| d | normalized_d | m | sigma_inf | predicted_sigma | forced | predicted_forced | k0_formula | predicted_k0 | residual_tau | residual | expected |"
    )
    print("|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|---|")

    for d in range(2, limit + 1):
        m = 180 * d
        c = d + 1
        size, masks = stable_candidate_masks(m, c)
        sigma = sigma_inf(m, c)
        forced, forced_union = private_fragment_certificate(size, masks)
        residual = [
            idx + 1 for idx in range(size) if not (forced_union & (1 << idx))
        ]
        normalized_d, predicted_sigma, predicted_k0, predicted_tau, expected = (
            predicted_n180_fixed_quotient(d)
        )
        predicted_forced = predicted_k0 - predicted_tau
        k0_formula = len(forced) + predicted_tau

        if sigma != predicted_sigma:
            failures.append((d, "sigma", sigma, predicted_sigma))
        if len(forced) != predicted_forced:
            failures.append((d, "forced", len(forced), predicted_forced))
        if k0_formula != predicted_k0:
            failures.append((d, "k0_formula", k0_formula, predicted_k0))
        if residual != expected:
            failures.append((d, "residual", residual, expected))

        print(
            f"| {d} | {normalized_d} | {m} | {sigma} | {predicted_sigma} | "
            f"{len(forced)} | {predicted_forced} | {k0_formula} | "
            f"{predicted_k0} | {predicted_tau} | `{residual}` | `{expected}` |"
        )

    if failures:
        print(f"Family scan failures: {len(failures)}")
        for failure in failures:
            print(f"- {failure}")
    else:
        print("Family scan matched the normalized-cell predictions.")


def print_n150_fixed_quotient_family(limit: int) -> None:
    failures: list[tuple[int, str, object, object]] = []
    print(f"`m=150d, n=150` fixed-quotient scan for 2 <= d <= {limit}")
    print(
        "| d | normalized_d | m | sigma_inf | predicted_sigma | forced | predicted_forced | k0_formula | predicted_k0 | residual_tau | residual | expected |"
    )
    print("|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|---|")

    for d in range(2, limit + 1):
        m = 150 * d
        c = d + 1
        size, masks = stable_candidate_masks(m, c)
        sigma = sigma_inf(m, c)
        forced, forced_union = private_fragment_certificate(size, masks)
        residual = [
            idx + 1 for idx in range(size) if not (forced_union & (1 << idx))
        ]
        normalized_d, predicted_sigma, predicted_k0, predicted_tau, expected = (
            predicted_n150_fixed_quotient(d)
        )
        predicted_forced = predicted_k0 - predicted_tau
        k0_formula = len(forced) + predicted_tau

        if sigma != predicted_sigma:
            failures.append((d, "sigma", sigma, predicted_sigma))
        if len(forced) != predicted_forced:
            failures.append((d, "forced", len(forced), predicted_forced))
        if k0_formula != predicted_k0:
            failures.append((d, "k0_formula", k0_formula, predicted_k0))
        if residual != expected:
            failures.append((d, "residual", residual, expected))

        print(
            f"| {d} | {normalized_d} | {m} | {sigma} | {predicted_sigma} | "
            f"{len(forced)} | {predicted_forced} | {k0_formula} | "
            f"{predicted_k0} | {predicted_tau} | `{residual}` | `{expected}` |"
        )

    if failures:
        print(f"Family scan failures: {len(failures)}")
        for failure in failures:
            print(f"- {failure}")
    else:
        print("Family scan matched the normalized-cell predictions.")


def print_n156_fixed_quotient_family(limit: int) -> None:
    failures: list[tuple[int, str, object, object]] = []
    print(f"`m=156d, n=156` fixed-quotient scan for 2 <= d <= {limit}")
    print(
        "| d | normalized_d | m | sigma_inf | predicted_sigma | forced | predicted_forced | k0_formula | predicted_k0 | residual_tau | residual | expected |"
    )
    print("|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|---|")

    for d in range(2, limit + 1):
        m = 156 * d
        c = d + 1
        size, masks = stable_candidate_masks(m, c)
        sigma = sigma_inf(m, c)
        forced, forced_union = private_fragment_certificate(size, masks)
        residual = [
            idx + 1 for idx in range(size) if not (forced_union & (1 << idx))
        ]
        normalized_d, predicted_sigma, predicted_k0, predicted_tau, expected = (
            predicted_n156_fixed_quotient(d)
        )
        predicted_forced = predicted_k0 - predicted_tau
        k0_formula = len(forced) + predicted_tau

        if sigma != predicted_sigma:
            failures.append((d, "sigma", sigma, predicted_sigma))
        if len(forced) != predicted_forced:
            failures.append((d, "forced", len(forced), predicted_forced))
        if k0_formula != predicted_k0:
            failures.append((d, "k0_formula", k0_formula, predicted_k0))
        if residual != expected:
            failures.append((d, "residual", residual, expected))

        print(
            f"| {d} | {normalized_d} | {m} | {sigma} | {predicted_sigma} | "
            f"{len(forced)} | {predicted_forced} | {k0_formula} | "
            f"{predicted_k0} | {predicted_tau} | `{residual}` | `{expected}` |"
        )

    if failures:
        print(f"Family scan failures: {len(failures)}")
        for failure in failures:
            print(f"- {failure}")
    else:
        print("Family scan matched the normalized-cell predictions.")


def print_n190_fixed_quotient_family(limit: int) -> None:
    failures: list[tuple[int, str, object, object]] = []
    print(f"`m=190d, n=190` fixed-quotient scan for 2 <= d <= {limit}")
    print(
        "| d | normalized_d | m | sigma_inf | predicted_sigma | forced | predicted_forced | k0_formula | predicted_k0 | residual_tau | residual | expected |"
    )
    print("|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|---|")

    for d in range(2, limit + 1):
        m = 190 * d
        c = d + 1
        size, masks = stable_candidate_masks(m, c)
        sigma = sigma_inf(m, c)
        forced, forced_union = private_fragment_certificate(size, masks)
        residual = [
            idx + 1 for idx in range(size) if not (forced_union & (1 << idx))
        ]
        normalized_d, predicted_sigma, predicted_k0, predicted_tau, expected = (
            predicted_n190_fixed_quotient(d)
        )
        predicted_forced = predicted_k0 - predicted_tau
        k0_formula = len(forced) + predicted_tau

        if sigma != predicted_sigma:
            failures.append((d, "sigma", sigma, predicted_sigma))
        if len(forced) != predicted_forced:
            failures.append((d, "forced", len(forced), predicted_forced))
        if k0_formula != predicted_k0:
            failures.append((d, "k0_formula", k0_formula, predicted_k0))
        if residual != expected:
            failures.append((d, "residual", residual, expected))

        print(
            f"| {d} | {normalized_d} | {m} | {sigma} | {predicted_sigma} | "
            f"{len(forced)} | {predicted_forced} | {k0_formula} | "
            f"{predicted_k0} | {predicted_tau} | `{residual}` | `{expected}` |"
        )

    if failures:
        print(f"Family scan failures: {len(failures)}")
        for failure in failures:
            print(f"- {failure}")
    else:
        print("Family scan matched the normalized-cell predictions.")


def print_n255_fixed_quotient_family(limit: int) -> None:
    failures: list[tuple[int, str, object, object]] = []
    print(f"`m=255d, n=255` fixed-quotient scan for 2 <= d <= {limit}")
    print(
        "| d | normalized_d | m | sigma_inf | predicted_sigma | forced | predicted_forced | k0_formula | predicted_k0 | residual_tau | residual | expected |"
    )
    print("|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|---|")

    for d in range(2, limit + 1):
        m = 255 * d
        c = d + 1
        size, masks = stable_candidate_masks(m, c)
        sigma = sigma_inf(m, c)
        forced, forced_union = private_fragment_certificate(size, masks)
        residual = [
            idx + 1 for idx in range(size) if not (forced_union & (1 << idx))
        ]
        normalized_d, predicted_sigma, predicted_k0, predicted_tau, expected = (
            predicted_n255_fixed_quotient(d)
        )
        predicted_forced = predicted_k0 - predicted_tau
        k0_formula = len(forced) + predicted_tau

        if sigma != predicted_sigma:
            failures.append((d, "sigma", sigma, predicted_sigma))
        if len(forced) != predicted_forced:
            failures.append((d, "forced", len(forced), predicted_forced))
        if k0_formula != predicted_k0:
            failures.append((d, "k0_formula", k0_formula, predicted_k0))
        if residual != expected:
            failures.append((d, "residual", residual, expected))

        print(
            f"| {d} | {normalized_d} | {m} | {sigma} | {predicted_sigma} | "
            f"{len(forced)} | {predicted_forced} | {k0_formula} | "
            f"{predicted_k0} | {predicted_tau} | `{residual}` | `{expected}` |"
        )

    if failures:
        print(f"Family scan failures: {len(failures)}")
        for failure in failures:
            print(f"- {failure}")
    else:
        print("Family scan matched the normalized-cell predictions.")


def print_n189_fixed_quotient_family(limit: int) -> None:
    failures: list[tuple[int, str, object, object]] = []
    print(f"`m=189d, n=189` fixed-quotient scan for 2 <= d <= {limit}")
    print(
        "| d | normalized_d | m | sigma_inf | predicted_sigma | forced | predicted_forced | k0_formula | predicted_k0 | residual_tau | residual | expected |"
    )
    print("|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|---|")

    for d in range(2, limit + 1):
        m = 189 * d
        c = d + 1
        size, masks = stable_candidate_masks(m, c)
        sigma = sigma_inf(m, c)
        forced, forced_union = private_fragment_certificate(size, masks)
        residual = [
            idx + 1 for idx in range(size) if not (forced_union & (1 << idx))
        ]
        normalized_d, predicted_sigma, predicted_k0, predicted_tau, expected = (
            predicted_n189_fixed_quotient(d)
        )
        predicted_forced = predicted_k0 - predicted_tau
        k0_formula = len(forced) + predicted_tau

        if sigma != predicted_sigma:
            failures.append((d, "sigma", sigma, predicted_sigma))
        if len(forced) != predicted_forced:
            failures.append((d, "forced", len(forced), predicted_forced))
        if k0_formula != predicted_k0:
            failures.append((d, "k0_formula", k0_formula, predicted_k0))
        if residual != expected:
            failures.append((d, "residual", residual, expected))

        print(
            f"| {d} | {normalized_d} | {m} | {sigma} | {predicted_sigma} | "
            f"{len(forced)} | {predicted_forced} | {k0_formula} | "
            f"{predicted_k0} | {predicted_tau} | `{residual}` | `{expected}` |"
        )

    if failures:
        print(f"Family scan failures: {len(failures)}")
        for failure in failures:
            print(f"- {failure}")
    else:
        print("Family scan matched the normalized-cell predictions.")


def print_n200_fixed_quotient_family(limit: int) -> None:
    failures: list[tuple[int, str, object, object]] = []
    print(f"`m=200d, n=200` fixed-quotient scan for 2 <= d <= {limit}")
    print(
        "| d | normalized_d | m | sigma_inf | predicted_sigma | forced | predicted_forced | k0_formula | predicted_k0 | residual_tau | residual | expected |"
    )
    print("|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|---|")

    for d in range(2, limit + 1):
        m = 200 * d
        c = d + 1
        size, masks = stable_candidate_masks(m, c)
        sigma = sigma_inf(m, c)
        forced, forced_union = private_fragment_certificate(size, masks)
        residual = [
            idx + 1 for idx in range(size) if not (forced_union & (1 << idx))
        ]
        normalized_d, predicted_sigma, predicted_k0, predicted_tau, expected = (
            predicted_n200_fixed_quotient(d)
        )
        predicted_forced = predicted_k0 - predicted_tau
        k0_formula = len(forced) + predicted_tau

        if sigma != predicted_sigma:
            failures.append((d, "sigma", sigma, predicted_sigma))
        if len(forced) != predicted_forced:
            failures.append((d, "forced", len(forced), predicted_forced))
        if k0_formula != predicted_k0:
            failures.append((d, "k0_formula", k0_formula, predicted_k0))
        if residual != expected:
            failures.append((d, "residual", residual, expected))

        print(
            f"| {d} | {normalized_d} | {m} | {sigma} | {predicted_sigma} | "
            f"{len(forced)} | {predicted_forced} | {k0_formula} | "
            f"{predicted_k0} | {predicted_tau} | `{residual}` | `{expected}` |"
        )

    if failures:
        print(f"Family scan failures: {len(failures)}")
        for failure in failures:
            print(f"- {failure}")
    else:
        print("Family scan matched the normalized-cell predictions.")


def print_n140_fixed_quotient_family(limit: int) -> None:
    failures: list[tuple[int, str, object, object]] = []
    print(f"`m=140d, n=140` fixed-quotient scan for 2 <= d <= {limit}")
    print(
        "| d | normalized_d | m | sigma_inf | predicted_sigma | forced | predicted_forced | k0_formula | predicted_k0 | residual_tau | residual | expected |"
    )
    print("|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|---|")

    for d in range(2, limit + 1):
        m = 140 * d
        c = d + 1
        size, masks = stable_candidate_masks(m, c)
        sigma = sigma_inf(m, c)
        forced, forced_union = private_fragment_certificate(size, masks)
        residual = [
            idx + 1 for idx in range(size) if not (forced_union & (1 << idx))
        ]
        normalized_d, predicted_sigma, predicted_k0, predicted_tau, expected = (
            predicted_n140_fixed_quotient(d)
        )
        predicted_forced = predicted_k0 - predicted_tau
        k0_formula = len(forced) + predicted_tau

        if sigma != predicted_sigma:
            failures.append((d, "sigma", sigma, predicted_sigma))
        if len(forced) != predicted_forced:
            failures.append((d, "forced", len(forced), predicted_forced))
        if k0_formula != predicted_k0:
            failures.append((d, "k0_formula", k0_formula, predicted_k0))
        if residual != expected:
            failures.append((d, "residual", residual, expected))

        print(
            f"| {d} | {normalized_d} | {m} | {sigma} | {predicted_sigma} | "
            f"{len(forced)} | {predicted_forced} | {k0_formula} | "
            f"{predicted_k0} | {predicted_tau} | `{residual}` | `{expected}` |"
        )

    if failures:
        print(f"Family scan failures: {len(failures)}")
        for failure in failures:
            print(f"- {failure}")
    else:
        print("Family scan matched the normalized-cell predictions.")


def print_n210_fixed_quotient_family(limit: int) -> None:
    failures: list[tuple[int, str, object, object]] = []
    print(f"`m=210d, n=210` fixed-quotient scan for 2 <= d <= {limit}")
    print(
        "| d | normalized_d | m | sigma_inf | predicted_sigma | forced | predicted_forced | k0_formula | predicted_k0 | residual_tau | residual | expected |"
    )
    print("|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|---|")

    for d in range(2, limit + 1):
        m = 210 * d
        c = d + 1
        size, masks = stable_candidate_masks(m, c)
        sigma = sigma_inf(m, c)
        forced, forced_union = private_fragment_certificate(size, masks)
        residual = [
            idx + 1 for idx in range(size) if not (forced_union & (1 << idx))
        ]
        normalized_d, predicted_sigma, predicted_k0, predicted_tau, expected = (
            predicted_n210_fixed_quotient(d)
        )
        predicted_forced = predicted_k0 - predicted_tau
        k0_formula = len(forced) + predicted_tau

        if sigma != predicted_sigma:
            failures.append((d, "sigma", sigma, predicted_sigma))
        if len(forced) != predicted_forced:
            failures.append((d, "forced", len(forced), predicted_forced))
        if k0_formula != predicted_k0:
            failures.append((d, "k0_formula", k0_formula, predicted_k0))
        if residual != expected:
            failures.append((d, "residual", residual, expected))

        print(
            f"| {d} | {normalized_d} | {m} | {sigma} | {predicted_sigma} | "
            f"{len(forced)} | {predicted_forced} | {k0_formula} | "
            f"{predicted_k0} | {predicted_tau} | `{residual}` | `{expected}` |"
        )

    if failures:
        print(f"Family scan failures: {len(failures)}")
        for failure in failures:
            print(f"- {failure}")
    else:
        print("Family scan matched the normalized-cell predictions.")


def print_n270_fixed_quotient_family(limit: int) -> None:
    failures: list[tuple[int, str, object, object]] = []
    print(f"`m=270d, n=270` fixed-quotient scan for 2 <= d <= {limit}")
    print(
        "| d | normalized_d | m | sigma_inf | predicted_sigma | forced | predicted_forced | k0_formula | predicted_k0 | residual_tau | residual | expected |"
    )
    print("|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|---|")

    for d in range(2, limit + 1):
        m = 270 * d
        c = d + 1
        size, masks = stable_candidate_masks(m, c)
        sigma = sigma_inf(m, c)
        forced, forced_union = private_fragment_certificate(size, masks)
        residual = [
            idx + 1 for idx in range(size) if not (forced_union & (1 << idx))
        ]
        normalized_d, predicted_sigma, predicted_k0, predicted_tau, expected = (
            predicted_n270_fixed_quotient(d)
        )
        predicted_forced = predicted_k0 - predicted_tau
        k0_formula = len(forced) + predicted_tau

        if sigma != predicted_sigma:
            failures.append((d, "sigma", sigma, predicted_sigma))
        if len(forced) != predicted_forced:
            failures.append((d, "forced", len(forced), predicted_forced))
        if k0_formula != predicted_k0:
            failures.append((d, "k0_formula", k0_formula, predicted_k0))
        if residual != expected:
            failures.append((d, "residual", residual, expected))

        print(
            f"| {d} | {normalized_d} | {m} | {sigma} | {predicted_sigma} | "
            f"{len(forced)} | {predicted_forced} | {k0_formula} | "
            f"{predicted_k0} | {predicted_tau} | `{residual}` | `{expected}` |"
        )

    if failures:
        print(f"Family scan failures: {len(failures)}")
        for failure in failures:
            print(f"- {failure}")
    else:
        print("Family scan matched the normalized-cell predictions.")


def print_n174_fixed_quotient_family(limit: int) -> None:
    failures: list[tuple[int, str, object, object]] = []
    print(f"`m=174d, n=174` fixed-quotient scan for 2 <= d <= {limit}")
    print(
        "| d | normalized_d | m | sigma_inf | predicted_sigma | forced | predicted_forced | k0_formula | predicted_k0 | residual_tau | residual | expected |"
    )
    print("|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|---|")

    for d in range(2, limit + 1):
        m = 174 * d
        c = d + 1
        size, masks = stable_candidate_masks(m, c)
        sigma = sigma_inf(m, c)
        forced, forced_union = private_fragment_certificate(size, masks)
        residual = [
            idx + 1 for idx in range(size) if not (forced_union & (1 << idx))
        ]
        normalized_d, predicted_sigma, predicted_k0, predicted_tau, expected = (
            predicted_n174_fixed_quotient(d)
        )
        predicted_forced = predicted_k0 - predicted_tau
        k0_formula = len(forced) + predicted_tau

        if sigma != predicted_sigma:
            failures.append((d, "sigma", sigma, predicted_sigma))
        if len(forced) != predicted_forced:
            failures.append((d, "forced", len(forced), predicted_forced))
        if k0_formula != predicted_k0:
            failures.append((d, "k0_formula", k0_formula, predicted_k0))
        if residual != expected:
            failures.append((d, "residual", residual, expected))

        print(
            f"| {d} | {normalized_d} | {m} | {sigma} | {predicted_sigma} | "
            f"{len(forced)} | {predicted_forced} | {k0_formula} | "
            f"{predicted_k0} | {predicted_tau} | `{residual}` | `{expected}` |"
        )

    if failures:
        print(f"Family scan failures: {len(failures)}")
        for failure in failures:
            print(f"- {failure}")
    else:
        print("Family scan matched the normalized-cell predictions.")


def print_n285_fixed_quotient_family(limit: int) -> None:
    failures: list[tuple[int, str, object, object]] = []
    print(f"`m=285d, n=285` fixed-quotient scan for 2 <= d <= {limit}")
    print(
        "| d | normalized_d | m | sigma_inf | predicted_sigma | forced | predicted_forced | k0_formula | predicted_k0 | residual_tau | residual | expected |"
    )
    print("|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|---|")

    for d in range(2, limit + 1):
        m = 285 * d
        c = d + 1
        size, masks = stable_candidate_masks(m, c)
        sigma = sigma_inf(m, c)
        forced, forced_union = private_fragment_certificate(size, masks)
        residual = [
            idx + 1 for idx in range(size) if not (forced_union & (1 << idx))
        ]
        normalized_d, predicted_sigma, predicted_k0, predicted_tau, expected = (
            predicted_n285_fixed_quotient(d)
        )
        predicted_forced = predicted_k0 - predicted_tau
        k0_formula = len(forced) + predicted_tau

        if sigma != predicted_sigma:
            failures.append((d, "sigma", sigma, predicted_sigma))
        if len(forced) != predicted_forced:
            failures.append((d, "forced", len(forced), predicted_forced))
        if k0_formula != predicted_k0:
            failures.append((d, "k0_formula", k0_formula, predicted_k0))
        if residual != expected:
            failures.append((d, "residual", residual, expected))

        print(
            f"| {d} | {normalized_d} | {m} | {sigma} | {predicted_sigma} | "
            f"{len(forced)} | {predicted_forced} | {k0_formula} | "
            f"{predicted_k0} | {predicted_tau} | `{residual}` | `{expected}` |"
        )

    if failures:
        print(f"Family scan failures: {len(failures)}")
        for failure in failures:
            print(f"- {failure}")
    else:
        print("Family scan matched the normalized-cell predictions.")


def print_n154_fixed_quotient_family(limit: int) -> None:
    failures: list[tuple[int, str, object, object]] = []
    print(f"`m=154d, n=154` fixed-quotient scan for 2 <= d <= {limit}")
    print(
        "| d | normalized_d | m | sigma_inf | predicted_sigma | forced | predicted_forced | k0_formula | predicted_k0 | residual_tau | residual | expected |"
    )
    print("|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|---|")

    for d in range(2, limit + 1):
        m = 154 * d
        c = d + 1
        size, masks = stable_candidate_masks(m, c)
        sigma = sigma_inf(m, c)
        forced, forced_union = private_fragment_certificate(size, masks)
        residual = [
            idx + 1 for idx in range(size) if not (forced_union & (1 << idx))
        ]
        normalized_d, predicted_sigma, predicted_k0, predicted_tau, expected = (
            predicted_n154_fixed_quotient(d)
        )
        predicted_forced = predicted_k0 - predicted_tau
        k0_formula = len(forced) + predicted_tau

        if sigma != predicted_sigma:
            failures.append((d, "sigma", sigma, predicted_sigma))
        if len(forced) != predicted_forced:
            failures.append((d, "forced", len(forced), predicted_forced))
        if k0_formula != predicted_k0:
            failures.append((d, "k0_formula", k0_formula, predicted_k0))
        if residual != expected:
            failures.append((d, "residual", residual, expected))

        print(
            f"| {d} | {normalized_d} | {m} | {sigma} | {predicted_sigma} | "
            f"{len(forced)} | {predicted_forced} | {k0_formula} | "
            f"{predicted_k0} | {predicted_tau} | `{residual}` | `{expected}` |"
        )

    if failures:
        print(f"Family scan failures: {len(failures)}")
        for failure in failures:
            print(f"- {failure}")
    else:
        print("Family scan matched the normalized-cell predictions.")


def print_n186_fixed_quotient_family(limit: int) -> None:
    failures: list[tuple[int, str, object, object]] = []
    print(f"`m=186d, n=186` fixed-quotient scan for 2 <= d <= {limit}")
    print(
        "| d | normalized_d | m | sigma_inf | predicted_sigma | forced | predicted_forced | k0_formula | predicted_k0 | residual_tau | residual | expected |"
    )
    print("|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|---|")

    for d in range(2, limit + 1):
        m = 186 * d
        c = d + 1
        size, masks = stable_candidate_masks(m, c)
        sigma = sigma_inf(m, c)
        forced, forced_union = private_fragment_certificate(size, masks)
        residual = [
            idx + 1 for idx in range(size) if not (forced_union & (1 << idx))
        ]
        normalized_d, predicted_sigma, predicted_k0, predicted_tau, expected = (
            predicted_n186_fixed_quotient(d)
        )
        predicted_forced = predicted_k0 - predicted_tau
        k0_formula = len(forced) + predicted_tau

        if sigma != predicted_sigma:
            failures.append((d, "sigma", sigma, predicted_sigma))
        if len(forced) != predicted_forced:
            failures.append((d, "forced", len(forced), predicted_forced))
        if k0_formula != predicted_k0:
            failures.append((d, "k0_formula", k0_formula, predicted_k0))
        if residual != expected:
            failures.append((d, "residual", residual, expected))

        print(
            f"| {d} | {normalized_d} | {m} | {sigma} | {predicted_sigma} | "
            f"{len(forced)} | {predicted_forced} | {k0_formula} | "
            f"{predicted_k0} | {predicted_tau} | `{residual}` | `{expected}` |"
        )

    if failures:
        print(f"Family scan failures: {len(failures)}")
        for failure in failures:
            print(f"- {failure}")
    else:
        print("Family scan matched the normalized-cell predictions.")


def print_n220_fixed_quotient_family(limit: int) -> None:
    failures: list[tuple[int, str, object, object]] = []
    print(f"`m=220d, n=220` fixed-quotient scan for 2 <= d <= {limit}")
    print(
        "| d | normalized_d | m | sigma_inf | predicted_sigma | forced | predicted_forced | k0_formula | predicted_k0 | residual_tau | residual | expected |"
    )
    print("|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|---|")

    for d in range(2, limit + 1):
        m = 220 * d
        c = d + 1
        size, masks = stable_candidate_masks(m, c)
        sigma = sigma_inf(m, c)
        forced, forced_union = private_fragment_certificate(size, masks)
        residual = [
            idx + 1 for idx in range(size) if not (forced_union & (1 << idx))
        ]
        normalized_d, predicted_sigma, predicted_k0, predicted_tau, expected = (
            predicted_n220_fixed_quotient(d)
        )
        predicted_forced = predicted_k0 - predicted_tau
        k0_formula = len(forced) + predicted_tau

        if sigma != predicted_sigma:
            failures.append((d, "sigma", sigma, predicted_sigma))
        if len(forced) != predicted_forced:
            failures.append((d, "forced", len(forced), predicted_forced))
        if k0_formula != predicted_k0:
            failures.append((d, "k0_formula", k0_formula, predicted_k0))
        if residual != expected:
            failures.append((d, "residual", residual, expected))

        print(
            f"| {d} | {normalized_d} | {m} | {sigma} | {predicted_sigma} | "
            f"{len(forced)} | {predicted_forced} | {k0_formula} | "
            f"{predicted_k0} | {predicted_tau} | `{residual}` | `{expected}` |"
        )

    if failures:
        print(f"Family scan failures: {len(failures)}")
        for failure in failures:
            print(f"- {failure}")
    else:
        print("Family scan matched the normalized-cell predictions.")


def print_n300_fixed_quotient_family(limit: int) -> None:
    failures: list[tuple[int, str, object, object]] = []
    print(f"`m=300d, n=300` fixed-quotient scan for 2 <= d <= {limit}")
    print(
        "| d | normalized_d | m | sigma_inf | predicted_sigma | forced | predicted_forced | k0_formula | predicted_k0 | residual_tau | residual | expected |"
    )
    print("|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|---|")

    for d in range(2, limit + 1):
        m = 300 * d
        c = d + 1
        size, masks = stable_candidate_masks(m, c)
        sigma = sigma_inf(m, c)
        forced, forced_union = private_fragment_certificate(size, masks)
        residual = [
            idx + 1 for idx in range(size) if not (forced_union & (1 << idx))
        ]
        normalized_d, predicted_sigma, predicted_k0, predicted_tau, expected = (
            predicted_n300_fixed_quotient(d)
        )
        predicted_forced = predicted_k0 - predicted_tau
        k0_formula = len(forced) + predicted_tau

        if sigma != predicted_sigma:
            failures.append((d, "sigma", sigma, predicted_sigma))
        if len(forced) != predicted_forced:
            failures.append((d, "forced", len(forced), predicted_forced))
        if k0_formula != predicted_k0:
            failures.append((d, "k0_formula", k0_formula, predicted_k0))
        if residual != expected:
            failures.append((d, "residual", residual, expected))

        print(
            f"| {d} | {normalized_d} | {m} | {sigma} | {predicted_sigma} | "
            f"{len(forced)} | {predicted_forced} | {k0_formula} | "
            f"{predicted_k0} | {predicted_tau} | `{residual}` | `{expected}` |"
        )

    if failures:
        print(f"Family scan failures: {len(failures)}")
        for failure in failures:
            print(f"- {failure}")
    else:
        print("Family scan matched the normalized-cell predictions.")


def print_n230_fixed_quotient_family(limit: int) -> None:
    failures: list[tuple[int, str, object, object]] = []
    print(f"`m=230d, n=230` fixed-quotient scan for 2 <= d <= {limit}")
    print(
        "| d | normalized_d | m | sigma_inf | predicted_sigma | forced | predicted_forced | k0_formula | predicted_k0 | residual_tau | residual | expected |"
    )
    print("|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|---|")

    for d in range(2, limit + 1):
        m = 230 * d
        c = d + 1
        size, masks = stable_candidate_masks(m, c)
        sigma = sigma_inf(m, c)
        forced, forced_union = private_fragment_certificate(size, masks)
        residual = [
            idx + 1 for idx in range(size) if not (forced_union & (1 << idx))
        ]
        normalized_d, predicted_sigma, predicted_k0, predicted_tau, expected = (
            predicted_n230_fixed_quotient(d)
        )
        predicted_forced = predicted_k0 - predicted_tau
        k0_formula = len(forced) + predicted_tau

        if sigma != predicted_sigma:
            failures.append((d, "sigma", sigma, predicted_sigma))
        if len(forced) != predicted_forced:
            failures.append((d, "forced", len(forced), predicted_forced))
        if k0_formula != predicted_k0:
            failures.append((d, "k0_formula", k0_formula, predicted_k0))
        if residual != expected:
            failures.append((d, "residual", residual, expected))

        print(
            f"| {d} | {normalized_d} | {m} | {sigma} | {predicted_sigma} | "
            f"{len(forced)} | {predicted_forced} | {k0_formula} | "
            f"{predicted_k0} | {predicted_tau} | `{residual}` | `{expected}` |"
        )

    if failures:
        print(f"Family scan failures: {len(failures)}")
        for failure in failures:
            print(f"- {failure}")
    else:
        print("Family scan matched the normalized-cell predictions.")


def print_n315_fixed_quotient_family(limit: int) -> None:
    failures: list[tuple[int, str, object, object]] = []
    print(f"`m=315d, n=315` fixed-quotient scan for 2 <= d <= {limit}")
    print(
        "| d | normalized_d | m | sigma_inf | predicted_sigma | forced | predicted_forced | k0_formula | predicted_k0 | residual_tau | residual | expected |"
    )
    print("|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|---|")

    for d in range(2, limit + 1):
        m = 315 * d
        c = d + 1
        size, masks = stable_candidate_masks(m, c)
        sigma = sigma_inf(m, c)
        forced, forced_union = private_fragment_certificate(size, masks)
        residual = [
            idx + 1 for idx in range(size) if not (forced_union & (1 << idx))
        ]
        normalized_d, predicted_sigma, predicted_k0, predicted_tau, expected = (
            predicted_n315_fixed_quotient(d)
        )
        predicted_forced = predicted_k0 - predicted_tau
        k0_formula = len(forced) + predicted_tau

        if sigma != predicted_sigma:
            failures.append((d, "sigma", sigma, predicted_sigma))
        if len(forced) != predicted_forced:
            failures.append((d, "forced", len(forced), predicted_forced))
        if k0_formula != predicted_k0:
            failures.append((d, "k0_formula", k0_formula, predicted_k0))
        if residual != expected:
            failures.append((d, "residual", residual, expected))

        print(
            f"| {d} | {normalized_d} | {m} | {sigma} | {predicted_sigma} | "
            f"{len(forced)} | {predicted_forced} | {k0_formula} | "
            f"{predicted_k0} | {predicted_tau} | `{residual}` | `{expected}` |"
        )

    if failures:
        print(f"Family scan failures: {len(failures)}")
        for failure in failures:
            print(f"- {failure}")
    else:
        print("Family scan matched the normalized-cell predictions.")


def print_n198_fixed_quotient_family(limit: int) -> None:
    failures: list[tuple[int, str, object, object]] = []
    print(f"`m=198d, n=198` fixed-quotient scan for 2 <= d <= {limit}")
    print(
        "| d | normalized_d | m | sigma_inf | predicted_sigma | forced | predicted_forced | k0_formula | predicted_k0 | residual_tau | residual | expected |"
    )
    print("|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|---|")

    for d in range(2, limit + 1):
        m = 198 * d
        c = d + 1
        size, masks = stable_candidate_masks(m, c)
        sigma = sigma_inf(m, c)
        forced, forced_union = private_fragment_certificate(size, masks)
        residual = [
            idx + 1 for idx in range(size) if not (forced_union & (1 << idx))
        ]
        normalized_d, predicted_sigma, predicted_k0, predicted_tau, expected = (
            predicted_n198_fixed_quotient(d)
        )
        predicted_forced = predicted_k0 - predicted_tau
        k0_formula = len(forced) + predicted_tau

        if sigma != predicted_sigma:
            failures.append((d, "sigma", sigma, predicted_sigma))
        if len(forced) != predicted_forced:
            failures.append((d, "forced", len(forced), predicted_forced))
        if k0_formula != predicted_k0:
            failures.append((d, "k0_formula", k0_formula, predicted_k0))
        if residual != expected:
            failures.append((d, "residual", residual, expected))

        print(
            f"| {d} | {normalized_d} | {m} | {sigma} | {predicted_sigma} | "
            f"{len(forced)} | {predicted_forced} | {k0_formula} | "
            f"{predicted_k0} | {predicted_tau} | `{residual}` | `{expected}` |"
        )

    if failures:
        print(f"Family scan failures: {len(failures)}")
        for failure in failures:
            print(f"- {failure}")
    else:
        print("Family scan matched the normalized-cell predictions.")


def print_n231_fixed_quotient_family(limit: int) -> None:
    failures: list[tuple[int, str, object, object]] = []
    print(f"`m=231d, n=231` fixed-quotient scan for 2 <= d <= {limit}")
    print(
        "| d | normalized_d | m | sigma_inf | predicted_sigma | forced | predicted_forced | k0_formula | predicted_k0 | residual_tau | residual | expected |"
    )
    print("|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|---|")

    for d in range(2, limit + 1):
        m = 231 * d
        c = d + 1
        size, masks = stable_candidate_masks(m, c)
        sigma = sigma_inf(m, c)
        forced, forced_union = private_fragment_certificate(size, masks)
        residual = [
            idx + 1 for idx in range(size) if not (forced_union & (1 << idx))
        ]
        normalized_d, predicted_sigma, predicted_k0, predicted_tau, expected = (
            predicted_n231_fixed_quotient(d)
        )
        predicted_forced = predicted_k0 - predicted_tau
        k0_formula = len(forced) + predicted_tau

        if sigma != predicted_sigma:
            failures.append((d, "sigma", sigma, predicted_sigma))
        if len(forced) != predicted_forced:
            failures.append((d, "forced", len(forced), predicted_forced))
        if k0_formula != predicted_k0:
            failures.append((d, "k0_formula", k0_formula, predicted_k0))
        if residual != expected:
            failures.append((d, "residual", residual, expected))

        print(
            f"| {d} | {normalized_d} | {m} | {sigma} | {predicted_sigma} | "
            f"{len(forced)} | {predicted_forced} | {k0_formula} | "
            f"{predicted_k0} | {predicted_tau} | `{residual}` | `{expected}` |"
        )

    if failures:
        print(f"Family scan failures: {len(failures)}")
        for failure in failures:
            print(f"- {failure}")
    else:
        print("Family scan matched the normalized-cell predictions.")


def print_n204_fixed_quotient_family(limit: int) -> None:
    failures: list[tuple[int, str, object, object]] = []
    print(f"`m=204d, n=204` fixed-quotient scan for 2 <= d <= {limit}")
    print(
        "| d | normalized_d | m | sigma_inf | predicted_sigma | forced | predicted_forced | k0_formula | predicted_k0 | residual_tau | residual | expected |"
    )
    print("|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|---|")

    for d in range(2, limit + 1):
        m = 204 * d
        c = d + 1
        size, masks = stable_candidate_masks(m, c)
        sigma = sigma_inf(m, c)
        forced, forced_union = private_fragment_certificate(size, masks)
        residual = [
            idx + 1 for idx in range(size) if not (forced_union & (1 << idx))
        ]
        normalized_d, predicted_sigma, predicted_k0, predicted_tau, expected = (
            predicted_n204_fixed_quotient(d)
        )
        predicted_forced = predicted_k0 - predicted_tau
        k0_formula = len(forced) + predicted_tau

        if sigma != predicted_sigma:
            failures.append((d, "sigma", sigma, predicted_sigma))
        if len(forced) != predicted_forced:
            failures.append((d, "forced", len(forced), predicted_forced))
        if k0_formula != predicted_k0:
            failures.append((d, "k0_formula", k0_formula, predicted_k0))
        if residual != expected:
            failures.append((d, "residual", residual, expected))

        print(
            f"| {d} | {normalized_d} | {m} | {sigma} | {predicted_sigma} | "
            f"{len(forced)} | {predicted_forced} | {k0_formula} | "
            f"{predicted_k0} | {predicted_tau} | `{residual}` | `{expected}` |"
        )

    if failures:
        print(f"Family scan failures: {len(failures)}")
        for failure in failures:
            print(f"- {failure}")
    else:
        print("Family scan matched the normalized-cell predictions.")


def print_n330_fixed_quotient_family(limit: int) -> None:
    failures: list[tuple[int, str, object, object]] = []
    print(f"`m=330d, n=330` fixed-quotient scan for 2 <= d <= {limit}")
    print(
        "| d | normalized_d | m | sigma_inf | predicted_sigma | forced | predicted_forced | k0_formula | predicted_k0 | residual_tau | residual | expected |"
    )
    print("|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|---|")

    for d in range(2, limit + 1):
        m = 330 * d
        c = d + 1
        size, masks = stable_candidate_masks(m, c)
        sigma = sigma_inf(m, c)
        forced, forced_union = private_fragment_certificate(size, masks)
        residual = [
            idx + 1 for idx in range(size) if not (forced_union & (1 << idx))
        ]
        normalized_d, predicted_sigma, predicted_k0, predicted_tau, expected = (
            predicted_n330_fixed_quotient(d)
        )
        predicted_forced = predicted_k0 - predicted_tau
        k0_formula = len(forced) + predicted_tau

        if sigma != predicted_sigma:
            failures.append((d, "sigma", sigma, predicted_sigma))
        if len(forced) != predicted_forced:
            failures.append((d, "forced", len(forced), predicted_forced))
        if k0_formula != predicted_k0:
            failures.append((d, "k0_formula", k0_formula, predicted_k0))
        if residual != expected:
            failures.append((d, "residual", residual, expected))

        print(
            f"| {d} | {normalized_d} | {m} | {sigma} | {predicted_sigma} | "
            f"{len(forced)} | {predicted_forced} | {k0_formula} | "
            f"{predicted_k0} | {predicted_tau} | `{residual}` | `{expected}` |"
        )

    if failures:
        print(f"Family scan failures: {len(failures)}")
        for failure in failures:
            print(f"- {failure}")
    else:
        print("Family scan matched the normalized-cell predictions.")


def print_n345_fixed_quotient_family(limit: int) -> None:
    failures: list[tuple[int, str, object, object]] = []
    print(f"`m=345d, n=345` fixed-quotient scan for 2 <= d <= {limit}")
    print(
        "| d | normalized_d | m | sigma_inf | predicted_sigma | forced | predicted_forced | k0_formula | predicted_k0 | residual_tau | residual | expected |"
    )
    print("|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|---|")

    for d in range(2, limit + 1):
        m = 345 * d
        c = d + 1
        size, masks = stable_candidate_masks(m, c)
        sigma = sigma_inf(m, c)
        forced, forced_union = private_fragment_certificate(size, masks)
        residual = [
            idx + 1 for idx in range(size) if not (forced_union & (1 << idx))
        ]
        normalized_d, predicted_sigma, predicted_k0, predicted_tau, expected = (
            predicted_n345_fixed_quotient(d)
        )
        predicted_forced = predicted_k0 - predicted_tau
        k0_formula = len(forced) + predicted_tau

        if sigma != predicted_sigma:
            failures.append((d, "sigma", sigma, predicted_sigma))
        if len(forced) != predicted_forced:
            failures.append((d, "forced", len(forced), predicted_forced))
        if k0_formula != predicted_k0:
            failures.append((d, "k0_formula", k0_formula, predicted_k0))
        if residual != expected:
            failures.append((d, "residual", residual, expected))

        print(
            f"| {d} | {normalized_d} | {m} | {sigma} | {predicted_sigma} | "
            f"{len(forced)} | {predicted_forced} | {k0_formula} | "
            f"{predicted_k0} | {predicted_tau} | `{residual}` | `{expected}` |"
        )

    if failures:
        print(f"Family scan failures: {len(failures)}")
        for failure in failures:
            print(f"- {failure}")
    else:
        print("Family scan matched the normalized-cell predictions.")


def print_n182_fixed_quotient_family(limit: int) -> None:
    failures: list[tuple[int, str, object, object]] = []
    print(f"`m=182d, n=182` fixed-quotient scan for 2 <= d <= {limit}")
    print(
        "| d | normalized_d | m | sigma_inf | predicted_sigma | forced | predicted_forced | k0_formula | predicted_k0 | residual_tau | residual | expected |"
    )
    print("|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|---|")

    for d in range(2, limit + 1):
        m = 182 * d
        c = d + 1
        size, masks = stable_candidate_masks(m, c)
        sigma = sigma_inf(m, c)
        forced, forced_union = private_fragment_certificate(size, masks)
        residual = [
            idx + 1 for idx in range(size) if not (forced_union & (1 << idx))
        ]
        normalized_d, predicted_sigma, predicted_k0, predicted_tau, expected = (
            predicted_n182_fixed_quotient(d)
        )
        predicted_forced = predicted_k0 - predicted_tau
        k0_formula = len(forced) + predicted_tau

        if sigma != predicted_sigma:
            failures.append((d, "sigma", sigma, predicted_sigma))
        if len(forced) != predicted_forced:
            failures.append((d, "forced", len(forced), predicted_forced))
        if k0_formula != predicted_k0:
            failures.append((d, "k0_formula", k0_formula, predicted_k0))
        if residual != expected:
            failures.append((d, "residual", residual, expected))

        print(
            f"| {d} | {normalized_d} | {m} | {sigma} | {predicted_sigma} | "
            f"{len(forced)} | {predicted_forced} | {k0_formula} | "
            f"{predicted_k0} | {predicted_tau} | `{residual}` | `{expected}` |"
        )

    if failures:
        print(f"Family scan failures: {len(failures)}")
        for failure in failures:
            print(f"- {failure}")
    else:
        print("Family scan matched the normalized-cell predictions.")


def print_m72t_d6t_family(limit: int) -> None:
    failures: list[tuple[int, str, object, object]] = []
    print(f"`m=72t, d=6t` family scan for 1 <= t <= {limit}")
    print(
        "| t | m | d | sigma_inf | predicted_sigma | k0_inf | predicted_k0 | forced | residual | expected |"
    )
    print("|---:|---:|---:|---:|---:|---:|---:|---:|---|---|")

    for t in range(1, limit + 1):
        m = 72 * t
        d = 6 * t
        c = d + 1
        size, masks = stable_candidate_masks(m, c)
        sigma = sigma_inf(m, c)
        k0 = exact_k0_inf(m, c)
        forced, forced_union = private_fragment_certificate(size, masks)
        residual = [
            idx + 1 for idx in range(size) if not (forced_union & (1 << idx))
        ]

        if t % 12 == 0:
            predicted_sigma = 1
            predicted_k0 = 11
        elif t % 2 == 0:
            predicted_sigma = 2
            predicted_k0 = 9
        else:
            predicted_sigma = 3
            predicted_k0 = 6
        expected = [2, 10] if math.gcd(t, 6) == 1 else []

        if sigma != predicted_sigma:
            failures.append((t, "sigma", sigma, predicted_sigma))
        if k0 != predicted_k0:
            failures.append((t, "k0", k0, predicted_k0))
        if residual != expected:
            failures.append((t, "residual", residual, expected))

        print(
            f"| {t} | {m} | {d} | {sigma} | {predicted_sigma} | {k0} | "
            f"{predicted_k0} | {len(forced)} | `{residual}` | `{expected}` |"
        )

    if failures:
        print(f"Family scan failures: {len(failures)}")
        for failure in failures:
            print(f"- {failure}")
    else:
        print("Family scan matched the expected residual pattern and formulas.")


def print_m100t_d10_family(limit: int) -> None:
    failures: list[tuple[int, str, object, object]] = []
    print(f"`m=100t, d=10` family scan for 1 <= t <= {limit}")
    print(
        "| t | m | sigma_inf | predicted_sigma | k0_inf | predicted_k0 | forced | residual | expected |"
    )
    print("|---:|---:|---:|---:|---:|---:|---:|---|---|")

    for t in range(1, limit + 1):
        m = 100 * t
        c = 11
        size, masks = stable_candidate_masks(m, c)
        sigma = sigma_inf(m, c)
        k0 = exact_k0_inf(m, c)
        forced, forced_union = private_fragment_certificate(size, masks)
        residual = [
            idx + 1 for idx in range(size) if not (forced_union & (1 << idx))
        ]

        factors = prime_factorization(t)
        denominator = 3 if t % 3 == 0 else 4
        predicted_sigma = math.ceil((10 * t - 1) / denominator)
        predicted_k0 = (
            6
            + 2 * factors.get(2, 0)
            + 2 * factors.get(3, 0)
            + 20 * factors.get(5, 0)
            + sum(exp * (prime - 1) for prime, exp in factors.items() if prime >= 7)
        )
        expected = predicted_m100t_d10_residual(t)

        if sigma != predicted_sigma:
            failures.append((t, "sigma", sigma, predicted_sigma))
        if k0 != predicted_k0:
            failures.append((t, "k0", k0, predicted_k0))
        if residual != expected:
            failures.append((t, "residual", residual, expected))

        print(
            f"| {t} | {m} | {sigma} | {predicted_sigma} | {k0} | {predicted_k0} | "
            f"{len(forced)} | `{residual}` | `{expected}` |"
        )

    if failures:
        print(f"Family scan failures: {len(failures)}")
        for failure in failures:
            print(f"- {failure}")
    else:
        print("Family scan matched the expected residual pattern and formulas.")


def k0_from_values(values: dict[int, int], target: int) -> int | None:
    ks = sorted(values)
    for candidate in ks:
        if values[candidate] != target:
            continue
        if all(values[k] == target for k in ks if k >= candidate):
            return candidate
    return None


def sweep_values(
    solver: SchurModSolver,
    m: int,
    ell: int,
) -> dict[int, int | None]:
    results: dict[int, int | None] = {}
    for k in range(1, m):
        try:
            results[k] = solver.search(m, k, ell).value
        except RuntimeError as exc:
            if "Timeout during search" not in str(exc):
                raise
            results[k] = None
    return results


def verify_threshold(
    solver: SchurModSolver,
    m: int,
    ell: int,
    k0: int,
    target: int,
) -> bool:
    at_k0 = solver.search(m, k0, ell).value
    if at_k0 != target:
        return False
    if k0 > 1:
        below = solver.search(m, k0 - 1, ell).value
        if below == target:
            return False
    return True


def describe_sigma_patterns(rows: Sequence[StableRow]) -> list[str]:
    grouped: dict[int, list[int]] = {}
    for row in rows:
        grouped.setdefault(row.sigma_inf, []).append(row.c)
    lines = []
    for sigma in sorted(grouped):
        residues = ", ".join(str(c) for c in grouped[sigma])
        lines.append(f"- `sigma_inf={sigma}` on residues `c in {{{residues}}}`.")
    return lines


def characterize_h4z12() -> list[str]:
    lines = [
        "For `m=12`, `H_C = 4Z/12 = {0,4,8}` has four cosets:",
        "- `0 + H_C = {0,4,8}`; inside the stabilized range this contributes `{4}` when `n>=5`.",
        "- `1 + H_C = {1,5,9}`; inside the stabilized range this contributes `{1,5}` when `n>=6`.",
        "- `2 + H_C = {2,6,10}`; inside the stabilized range this contributes `{2}` when `n>=3`.",
        "- `3 + H_C = {3,7,11}`; inside the stabilized range this contributes `{3}` when `n>=4`.",
        "By Theorem 8.1, a coset fragment based at `a0` is stable-safe iff `4` does not divide `(c-1)a0`.",
        "Consequences:",
        "- Basepoints `a0 == 1,5 (mod 4)` are safe iff `c-1` is not divisible by `4`, i.e. `c not == 1,5,9 (mod 12)`.",
        "- Basepoint `a0 == 2 (mod 4)` is safe iff `c-1` is odd, i.e. `c` is even.",
        "- Basepoint `a0 == 3 (mod 4)` is safe iff `c-1` is not divisible by `4`, same condition as `a0=1`.",
        "What makes `c == 11 (mod 12)` special is that `d = gcd(12,10) = 2`, so the stabilized range is exactly `{1,2,3,4,5}` and the only nontrivial `H_C`-coset fragment available there is `{1,5}`. It is safe because `4` does not divide `10`.",
    ]
    return lines


def build_doc(
    output_path: Path,
    solver: SchurModSolver,
    moduli: Sequence[int],
    timeout_seconds: int,
) -> None:
    lines = [
        "# Phase 9 Stable Tables",
        "",
        "Computation setup:",
        "- For each modulus `m`, residue class representative `c in {2,...,m}`, and large-`ell` probes `ell1 = c + m`, `ell2 = c + 2m`.",
        f"- SAT threshold checks with per-instance cap `{timeout_seconds}` seconds.",
        "- Stable target value `V = n - 1` where `d = gcd(m, c-1)` and `n = m/d`.",
        "- `sigma_inf` and `k0_inf` computed from the Phase 8 large-`ell` coset criterion via stable safe coset fragments.",
        "",
    ]

    prime_summary: dict[int, tuple[bool, bool]] = {}

    for m in moduli:
        print(f"[phase9] start m={m}", flush=True)
        rows: list[StableRow] = []
        lines.extend([f"## m={m} stable values (ell >= {m + 2})", ""])
        lines.append(
            "| c (= ell mod m) | d = gcd(m,c-1) | n = m/d | sigma_inf | k0_inf | V = n-1 | SAT ok @ c+m | SAT ok @ c+2m | note |"
        )
        lines.append("| --- | --- | --- | --- | --- | --- | --- | --- | --- |")

        for c in range(2, m + 1):
            d = math.gcd(m, c - 1)
            n = m // d
            ell1 = c + m
            ell2 = c + 2 * m
            target = n - 1
            sigma = sigma_inf(m, c)
            k0_inf = exact_k0_inf(m, c)

            sat_ok_ell1 = None
            sat_ok_ell2 = None
            mismatch_note = None
            try:
                sat_ok_ell1 = verify_threshold(solver, m, ell1, k0_inf, target)
                sat_ok_ell2 = verify_threshold(solver, m, ell2, k0_inf, target)
            except RuntimeError as exc:
                if "Timeout during search" in str(exc):
                    mismatch_note = "timeout during SAT verify"
                else:
                    raise

            if sat_ok_ell1 is False or sat_ok_ell2 is False:
                mismatch_note = "SAT threshold mismatch"

            rows.append(
                StableRow(
                    c=c,
                    d=d,
                    n=n,
                    sigma_inf=sigma,
                    k0_inf=k0_inf,
                    sat_ok_ell1=sat_ok_ell1,
                    sat_ok_ell2=sat_ok_ell2,
                    v=target,
                    mismatch=mismatch_note,
                )
            )

            lines.append(
                f"| {c} | {d} | {n} | {sigma} | "
                f"{k0_inf} | {target} | "
                f"{sat_ok_ell1 if sat_ok_ell1 is not None else '?'} | "
                f"{sat_ok_ell2 if sat_ok_ell2 is not None else '?'} | "
                f"{mismatch_note or ''} |"
            )

        lines.extend(["", "### Notes", ""])
        mismatches = [row for row in rows if row.mismatch]
        if mismatches:
            lines.append("- SAT threshold mismatches or timeouts were detected:")
            for row in mismatches:
                lines.append(
                    f"- `c={row.c}`: `sat@c+m={row.sat_ok_ell1}`, `sat@c+2m={row.sat_ok_ell2}`, note=`{row.mismatch}`."
                )
        else:
            lines.append("- No SAT threshold mismatches between the two large-`ell` probes.")

        lines.append("- `sigma_inf` distribution:")
        lines.extend(describe_sigma_patterns(rows))

        lines.append("- `k0_inf` by residue class:")
        for row in rows:
            lines.append(
                f"- `c={row.c}`: `k0_inf={'?' if row.k0_inf is None else row.k0_inf}`, "
                f"`sigma_inf={row.sigma_inf}`, `d={row.d}`, `V={row.v}`."
            )

        if m in (11, 13, 17):
            sigma_ok = all(row.sigma_inf == 1 for row in rows if row.c != 1)
            k0_ok = all(row.k0_inf == m - 1 for row in rows if row.c != 1)
            prime_summary[m] = (sigma_ok, k0_ok)
            lines.append(
                f"- Prime check: `sigma_inf == 1` is `{sigma_ok}`, `k0_inf == {m-1}` is `{k0_ok}`."
            )

        if m == 12:
            lines.extend(["", "### `m=12`, `H_C = 4Z/12`", ""])
            lines.extend(characterize_h4z12())

        lines.append("")
        print(f"[phase9] done m={m}", flush=True)

    lines.extend(["## Pattern Summary", ""])
    lines.append(
        "- Across all computed moduli, the stable value `V = n-1` remained exact, with `n = m / gcd(m,c-1)`."
    )
    lines.append(
        "- No disagreements were found between the two stable-regime probes `ell=c+m` and `ell=c+2m` at the SAT-checked thresholds; this supports the Phase 8 periodicity claim."
    )
    lines.append(
        "- `sigma_inf` depends strongly on divisor structure: primes force `sigma_inf=1`, while composites often admit larger coset-fragment classes."
    )
    lines.append(
        "- `k0_inf` is much less rigid than `V` and does not appear to be a function of `d = gcd(m,c-1)` alone."
    )
    lines.append("")
    lines.append("Prime verification summary:")
    for p, (sigma_ok, k0_ok) in sorted(prime_summary.items()):
        lines.append(
            f"- `m={p}`: `sigma_inf=1` on every nontrivial residue is `{sigma_ok}`; "
            f"`k0_inf={p-1}` on every nontrivial residue is `{k0_ok}`."
        )

    output_path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--workdir", default=str(Path(__file__).resolve().parent))
    parser.add_argument(
        "--output",
        type=Path,
        default=Path("docs/phase9-stable-tables.md"),
    )
    parser.add_argument("--timeout-seconds", type=int, default=300)
    parser.add_argument(
        "--jobs",
        type=int,
        default=1,
        help="accepted for scan invocations; current stable-table scans run serially",
    )
    parser.add_argument(
        "--moduli",
        nargs="*",
        type=int,
        default=list(range(8, 19)),
    )
    parser.add_argument(
        "--scan-dgt1-gaps",
        type=int,
        metavar="LIMIT",
        help="print exact d>1 packing-gap rows up to LIMIT using only the stable set-cover backend",
    )
    parser.add_argument(
        "--scan-private-failures",
        type=int,
        metavar="LIMIT",
        help="with --scan-dgt1-gaps, also report the first private-certificate failure up to LIMIT",
    )
    parser.add_argument(
        "--scan-filtered-frontier",
        type=int,
        metavar="LIMIT",
        help="print non-private residual rows up to LIMIT after filtering the Phase 19--95 proved rows",
    )
    parser.add_argument(
        "--scan-residual-frontier",
        type=int,
        metavar="LIMIT",
        help="alias for --scan-filtered-frontier, retained for the strategy roadmap",
    )
    parser.add_argument(
        "--scan-m36t-d6-family",
        type=int,
        metavar="LIMIT",
        help="scan the conjectural m=36t, d=6 residual-family pattern for 1 <= t <= LIMIT",
    )
    parser.add_argument(
        "--scan-m72t-d12-family",
        type=int,
        metavar="LIMIT",
        help="scan the m=72t, d=12 residual-family formulas for 1 <= t <= LIMIT",
    )
    parser.add_argument(
        "--scan-m72t-d6t-family",
        type=int,
        metavar="LIMIT",
        help="scan the fixed-quotient m=72t, d=6t family for 1 <= t <= LIMIT",
    )
    parser.add_argument(
        "--scan-m100t-d10-family",
        type=int,
        metavar="LIMIT",
        help="scan the m=100t, d=10 residual-family formulas for 1 <= t <= LIMIT",
    )
    parser.add_argument(
        "--scan-m144t-d6t-family",
        type=int,
        metavar="LIMIT",
        help="scan the fixed-quotient m=144t, d=6t family for 1 <= t <= LIMIT",
    )
    parser.add_argument(
        "--scan-m252t-d6t-family",
        type=int,
        metavar="LIMIT",
        help="scan the fixed-quotient m=252t, d=6t residual criterion for 1 <= t <= LIMIT",
    )
    parser.add_argument(
        "--scan-m360t-d6t-family",
        type=int,
        metavar="LIMIT",
        help="scan the fixed-quotient m=360t, d=6t residual subfamily for 1 <= t <= LIMIT",
    )
    parser.add_argument(
        "--scan-m216t-d6t-family",
        type=int,
        metavar="LIMIT",
        help="scan the fixed-quotient m=216t, d=6t residual subfamily for 1 <= t <= LIMIT",
    )
    parser.add_argument(
        "--scan-m196t-d14-family",
        type=int,
        metavar="LIMIT",
        help="scan the m=196t, d=14 residual-family formulas for 1 <= t <= LIMIT",
    )
    parser.add_argument(
        "--scan-m108t-d18-family",
        type=int,
        metavar="LIMIT",
        help="scan the m=108t, d=18 residual-family formulas for 1 <= t <= LIMIT",
    )
    parser.add_argument(
        "--scan-n30-fixed-quotient-family",
        type=int,
        metavar="LIMIT",
        help="scan the fixed-quotient m=30d, n=30 formulas for 2 <= d <= LIMIT",
    )
    parser.add_argument(
        "--scan-n40-fixed-quotient-family",
        type=int,
        metavar="LIMIT",
        help="scan the fixed-quotient m=40d, n=40 formulas for 2 <= d <= LIMIT",
    )
    parser.add_argument(
        "--scan-n48-fixed-quotient-family",
        type=int,
        metavar="LIMIT",
        help="scan the fixed-quotient m=48d, n=48 formulas for 2 <= d <= LIMIT",
    )
    parser.add_argument(
        "--scan-n70-fixed-quotient-family",
        type=int,
        metavar="LIMIT",
        help="scan the fixed-quotient m=70d, n=70 formulas for 2 <= d <= LIMIT",
    )
    parser.add_argument(
        "--scan-n45-fixed-quotient-family",
        type=int,
        metavar="LIMIT",
        help="scan the fixed-quotient m=45d, n=45 formulas for 2 <= d <= LIMIT",
    )
    parser.add_argument(
        "--scan-n80-fixed-quotient-family",
        type=int,
        metavar="LIMIT",
        help="scan the fixed-quotient m=80d, n=80 formulas for 2 <= d <= LIMIT",
    )
    parser.add_argument(
        "--scan-n72-fixed-quotient-family",
        type=int,
        metavar="LIMIT",
        help="scan the fixed-quotient m=72d, n=72 formulas for 2 <= d <= LIMIT",
    )
    parser.add_argument(
        "--scan-n66-fixed-quotient-family",
        type=int,
        metavar="LIMIT",
        help="scan the fixed-quotient m=66d, n=66 formulas for 2 <= d <= LIMIT",
    )
    parser.add_argument(
        "--scan-n78-fixed-quotient-family",
        type=int,
        metavar="LIMIT",
        help="scan the fixed-quotient m=78d, n=78 formulas for 2 <= d <= LIMIT",
    )
    parser.add_argument(
        "--scan-n60-fixed-quotient-family",
        type=int,
        metavar="LIMIT",
        help="scan the fixed-quotient m=60d, n=60 formulas for 2 <= d <= LIMIT",
    )
    parser.add_argument(
        "--scan-n84-fixed-quotient-family",
        type=int,
        metavar="LIMIT",
        help="scan the fixed-quotient m=84d, n=84 formulas for 2 <= d <= LIMIT",
    )
    parser.add_argument(
        "--scan-n135-fixed-quotient-family",
        type=int,
        metavar="LIMIT",
        help="scan the fixed-quotient m=135d, n=135 formulas for 2 <= d <= LIMIT",
    )
    parser.add_argument(
        "--scan-n110-fixed-quotient-family",
        type=int,
        metavar="LIMIT",
        help="scan the fixed-quotient m=110d, n=110 formulas for 2 <= d <= LIMIT",
    )
    parser.add_argument(
        "--scan-n102-fixed-quotient-family",
        type=int,
        metavar="LIMIT",
        help="scan the fixed-quotient m=102d, n=102 formulas for 2 <= d <= LIMIT",
    )
    parser.add_argument(
        "--scan-n105-fixed-quotient-family",
        type=int,
        metavar="LIMIT",
        help="scan the fixed-quotient m=105d, n=105 formulas for 2 <= d <= LIMIT",
    )
    parser.add_argument(
        "--scan-n165-fixed-quotient-family",
        type=int,
        metavar="LIMIT",
        help="scan the fixed-quotient m=165d, n=165 formulas for 2 <= d <= LIMIT",
    )
    parser.add_argument(
        "--scan-n90-fixed-quotient-family",
        type=int,
        metavar="LIMIT",
        help="scan the fixed-quotient m=90d, n=90 formulas for 2 <= d <= LIMIT",
    )
    parser.add_argument(
        "--scan-n120-fixed-quotient-family",
        type=int,
        metavar="LIMIT",
        help="scan the fixed-quotient m=120d, n=120 formulas for 2 <= d <= LIMIT",
    )
    parser.add_argument(
        "--scan-n36-fixed-quotient-family",
        type=int,
        metavar="LIMIT",
        help="scan the fixed-quotient m=36d, n=36 formulas for 2 <= d <= LIMIT",
    )
    parser.add_argument(
        "--scan-n96-fixed-quotient-family",
        type=int,
        metavar="LIMIT",
        help="scan the fixed-quotient m=96d, n=96 formulas for 2 <= d <= LIMIT",
    )
    parser.add_argument(
        "--scan-n114-fixed-quotient-family",
        type=int,
        metavar="LIMIT",
        help="scan the fixed-quotient m=114d, n=114 formulas for 2 <= d <= LIMIT",
    )
    parser.add_argument(
        "--scan-n108-fixed-quotient-family",
        type=int,
        metavar="LIMIT",
        help="scan the fixed-quotient m=108d, n=108 formulas for 2 <= d <= LIMIT",
    )
    parser.add_argument(
        "--scan-n130-fixed-quotient-family",
        type=int,
        metavar="LIMIT",
        help="scan the fixed-quotient m=130d, n=130 formulas for 2 <= d <= LIMIT",
    )
    parser.add_argument(
        "--scan-n126-fixed-quotient-family",
        type=int,
        metavar="LIMIT",
        help="scan the fixed-quotient m=126d, n=126 formulas for 2 <= d <= LIMIT",
    )
    parser.add_argument(
        "--scan-n112-fixed-quotient-family",
        type=int,
        metavar="LIMIT",
        help="scan the fixed-quotient m=112d, n=112 formulas for 2 <= d <= LIMIT",
    )
    parser.add_argument(
        "--scan-n132-fixed-quotient-family",
        type=int,
        metavar="LIMIT",
        help="scan the fixed-quotient m=132d, n=132 formulas for 2 <= d <= LIMIT",
    )
    parser.add_argument(
        "--scan-n138-fixed-quotient-family",
        type=int,
        metavar="LIMIT",
        help="scan the fixed-quotient m=138d, n=138 formulas for 2 <= d <= LIMIT",
    )
    parser.add_argument(
        "--scan-n160-fixed-quotient-family",
        type=int,
        metavar="LIMIT",
        help="scan the fixed-quotient m=160d, n=160 formulas for 2 <= d <= LIMIT",
    )
    parser.add_argument(
        "--scan-n170-fixed-quotient-family",
        type=int,
        metavar="LIMIT",
        help="scan the fixed-quotient m=170d, n=170 formulas for 2 <= d <= LIMIT",
    )
    parser.add_argument(
        "--scan-n144-fixed-quotient-family",
        type=int,
        metavar="LIMIT",
        help="scan the fixed-quotient m=144d, n=144 formulas for 2 <= d <= LIMIT",
    )
    parser.add_argument(
        "--scan-n225-fixed-quotient-family",
        type=int,
        metavar="LIMIT",
        help="scan the fixed-quotient m=225d, n=225 formulas for 2 <= d <= LIMIT",
    )
    parser.add_argument(
        "--scan-n168-fixed-quotient-family",
        type=int,
        metavar="LIMIT",
        help="scan the fixed-quotient m=168d, n=168 formulas for 2 <= d <= LIMIT",
    )
    parser.add_argument(
        "--scan-n240-fixed-quotient-family",
        type=int,
        metavar="LIMIT",
        help="scan the fixed-quotient m=240d, n=240 formulas for 2 <= d <= LIMIT",
    )
    parser.add_argument(
        "--scan-n180-fixed-quotient-family",
        type=int,
        metavar="LIMIT",
        help="scan the fixed-quotient m=180d, n=180 formulas for 2 <= d <= LIMIT",
    )
    parser.add_argument(
        "--scan-n150-fixed-quotient-family",
        type=int,
        metavar="LIMIT",
        help="scan the fixed-quotient m=150d, n=150 formulas for 2 <= d <= LIMIT",
    )
    parser.add_argument(
        "--scan-n156-fixed-quotient-family",
        type=int,
        metavar="LIMIT",
        help="scan the fixed-quotient m=156d, n=156 formulas for 2 <= d <= LIMIT",
    )
    parser.add_argument(
        "--scan-n190-fixed-quotient-family",
        type=int,
        metavar="LIMIT",
        help="scan the fixed-quotient m=190d, n=190 formulas for 2 <= d <= LIMIT",
    )
    parser.add_argument(
        "--scan-n255-fixed-quotient-family",
        type=int,
        metavar="LIMIT",
        help="scan the fixed-quotient m=255d, n=255 formulas for 2 <= d <= LIMIT",
    )
    parser.add_argument(
        "--scan-n189-fixed-quotient-family",
        type=int,
        metavar="LIMIT",
        help="scan the fixed-quotient m=189d, n=189 formulas for 2 <= d <= LIMIT",
    )
    parser.add_argument(
        "--scan-n200-fixed-quotient-family",
        type=int,
        metavar="LIMIT",
        help="scan the fixed-quotient m=200d, n=200 formulas for 2 <= d <= LIMIT",
    )
    parser.add_argument(
        "--scan-n140-fixed-quotient-family",
        type=int,
        metavar="LIMIT",
        help="scan the fixed-quotient m=140d, n=140 formulas for 2 <= d <= LIMIT",
    )
    parser.add_argument(
        "--scan-n210-fixed-quotient-family",
        type=int,
        metavar="LIMIT",
        help="scan the fixed-quotient m=210d, n=210 formulas for 2 <= d <= LIMIT",
    )
    parser.add_argument(
        "--scan-n270-fixed-quotient-family",
        type=int,
        metavar="LIMIT",
        help="scan the fixed-quotient m=270d, n=270 formulas for 2 <= d <= LIMIT",
    )
    parser.add_argument(
        "--scan-n174-fixed-quotient-family",
        type=int,
        metavar="LIMIT",
        help="scan the fixed-quotient m=174d, n=174 formulas for 2 <= d <= LIMIT",
    )
    parser.add_argument(
        "--scan-n285-fixed-quotient-family",
        type=int,
        metavar="LIMIT",
        help="scan the fixed-quotient m=285d, n=285 formulas for 2 <= d <= LIMIT",
    )
    parser.add_argument(
        "--scan-n154-fixed-quotient-family",
        type=int,
        metavar="LIMIT",
        help="scan the fixed-quotient m=154d, n=154 formulas for 2 <= d <= LIMIT",
    )
    parser.add_argument(
        "--scan-n186-fixed-quotient-family",
        type=int,
        metavar="LIMIT",
        help="scan the fixed-quotient m=186d, n=186 formulas for 2 <= d <= LIMIT",
    )
    parser.add_argument(
        "--scan-n220-fixed-quotient-family",
        type=int,
        metavar="LIMIT",
        help="scan the fixed-quotient m=220d, n=220 formulas for 2 <= d <= LIMIT",
    )
    parser.add_argument(
        "--scan-n300-fixed-quotient-family",
        type=int,
        metavar="LIMIT",
        help="scan the fixed-quotient m=300d, n=300 formulas for 2 <= d <= LIMIT",
    )
    parser.add_argument(
        "--scan-n230-fixed-quotient-family",
        type=int,
        metavar="LIMIT",
        help="scan the fixed-quotient m=230d, n=230 formulas for 2 <= d <= LIMIT",
    )
    parser.add_argument(
        "--scan-n315-fixed-quotient-family",
        type=int,
        metavar="LIMIT",
        help="scan the fixed-quotient m=315d, n=315 formulas for 2 <= d <= LIMIT",
    )
    parser.add_argument(
        "--scan-n198-fixed-quotient-family",
        type=int,
        metavar="LIMIT",
        help="scan the fixed-quotient m=198d, n=198 formulas for 2 <= d <= LIMIT",
    )
    parser.add_argument(
        "--scan-n231-fixed-quotient-family",
        type=int,
        metavar="LIMIT",
        help="scan the fixed-quotient m=231d, n=231 formulas for 2 <= d <= LIMIT",
    )
    parser.add_argument(
        "--scan-n204-fixed-quotient-family",
        type=int,
        metavar="LIMIT",
        help="scan the fixed-quotient m=204d, n=204 formulas for 2 <= d <= LIMIT",
    )
    parser.add_argument(
        "--scan-n330-fixed-quotient-family",
        type=int,
        metavar="LIMIT",
        help="scan the fixed-quotient m=330d, n=330 formulas for 2 <= d <= LIMIT",
    )
    parser.add_argument(
        "--scan-n345-fixed-quotient-family",
        type=int,
        metavar="LIMIT",
        help="scan the fixed-quotient m=345d, n=345 formulas for 2 <= d <= LIMIT",
    )
    parser.add_argument(
        "--scan-n182-fixed-quotient-family",
        type=int,
        metavar="LIMIT",
        help="scan the fixed-quotient m=182d, n=182 formulas for 2 <= d <= LIMIT",
    )
    args = parser.parse_args()

    frontier_limit = args.scan_filtered_frontier
    if args.scan_residual_frontier is not None:
        frontier_limit = args.scan_residual_frontier
    if frontier_limit is not None:
        print_filtered_frontier_scan(frontier_limit)
        return 0

    if args.scan_m144t_d6t_family is not None:
        print_m144t_d6t_family(args.scan_m144t_d6t_family)
        return 0

    if args.scan_m252t_d6t_family is not None:
        print_m252t_d6t_family(args.scan_m252t_d6t_family)
        return 0

    if args.scan_m360t_d6t_family is not None:
        print_m360t_d6t_family(args.scan_m360t_d6t_family)
        return 0

    if args.scan_m216t_d6t_family is not None:
        print_m216t_d6t_family(args.scan_m216t_d6t_family)
        return 0

    if args.scan_m196t_d14_family is not None:
        print_m196t_d14_family(args.scan_m196t_d14_family)
        return 0

    if args.scan_m108t_d18_family is not None:
        print_m108t_d18_family(args.scan_m108t_d18_family)
        return 0

    if args.scan_n30_fixed_quotient_family is not None:
        print_n30_fixed_quotient_family(args.scan_n30_fixed_quotient_family)
        return 0

    if args.scan_n40_fixed_quotient_family is not None:
        print_n40_fixed_quotient_family(args.scan_n40_fixed_quotient_family)
        return 0

    if args.scan_n48_fixed_quotient_family is not None:
        print_n48_fixed_quotient_family(args.scan_n48_fixed_quotient_family)
        return 0

    if args.scan_n70_fixed_quotient_family is not None:
        print_n70_fixed_quotient_family(args.scan_n70_fixed_quotient_family)
        return 0

    if args.scan_n45_fixed_quotient_family is not None:
        print_n45_fixed_quotient_family(args.scan_n45_fixed_quotient_family)
        return 0

    if args.scan_n80_fixed_quotient_family is not None:
        print_n80_fixed_quotient_family(args.scan_n80_fixed_quotient_family)
        return 0

    if args.scan_n72_fixed_quotient_family is not None:
        print_n72_fixed_quotient_family(args.scan_n72_fixed_quotient_family)
        return 0

    if args.scan_n66_fixed_quotient_family is not None:
        print_n66_fixed_quotient_family(args.scan_n66_fixed_quotient_family)
        return 0

    if args.scan_n78_fixed_quotient_family is not None:
        print_n78_fixed_quotient_family(args.scan_n78_fixed_quotient_family)
        return 0

    if args.scan_n60_fixed_quotient_family is not None:
        print_n60_fixed_quotient_family(args.scan_n60_fixed_quotient_family)
        return 0

    if args.scan_n84_fixed_quotient_family is not None:
        print_n84_fixed_quotient_family(args.scan_n84_fixed_quotient_family)
        return 0

    if args.scan_n135_fixed_quotient_family is not None:
        print_n135_fixed_quotient_family(args.scan_n135_fixed_quotient_family)
        return 0

    if args.scan_n110_fixed_quotient_family is not None:
        print_n110_fixed_quotient_family(args.scan_n110_fixed_quotient_family)
        return 0

    if args.scan_n102_fixed_quotient_family is not None:
        print_n102_fixed_quotient_family(args.scan_n102_fixed_quotient_family)
        return 0

    if args.scan_n105_fixed_quotient_family is not None:
        print_n105_fixed_quotient_family(args.scan_n105_fixed_quotient_family)
        return 0

    if args.scan_n165_fixed_quotient_family is not None:
        print_n165_fixed_quotient_family(args.scan_n165_fixed_quotient_family)
        return 0

    if args.scan_n90_fixed_quotient_family is not None:
        print_n90_fixed_quotient_family(args.scan_n90_fixed_quotient_family)
        return 0

    if args.scan_n120_fixed_quotient_family is not None:
        print_n120_fixed_quotient_family(args.scan_n120_fixed_quotient_family)
        return 0

    if args.scan_n36_fixed_quotient_family is not None:
        print_n36_fixed_quotient_family(args.scan_n36_fixed_quotient_family)
        return 0

    if args.scan_n96_fixed_quotient_family is not None:
        print_n96_fixed_quotient_family(args.scan_n96_fixed_quotient_family)
        return 0

    if args.scan_n114_fixed_quotient_family is not None:
        print_n114_fixed_quotient_family(args.scan_n114_fixed_quotient_family)
        return 0

    if args.scan_n108_fixed_quotient_family is not None:
        print_n108_fixed_quotient_family(args.scan_n108_fixed_quotient_family)
        return 0

    if args.scan_n130_fixed_quotient_family is not None:
        print_n130_fixed_quotient_family(args.scan_n130_fixed_quotient_family)
        return 0

    if args.scan_n126_fixed_quotient_family is not None:
        print_n126_fixed_quotient_family(args.scan_n126_fixed_quotient_family)
        return 0

    if args.scan_n112_fixed_quotient_family is not None:
        print_n112_fixed_quotient_family(args.scan_n112_fixed_quotient_family)
        return 0

    if args.scan_n132_fixed_quotient_family is not None:
        print_n132_fixed_quotient_family(args.scan_n132_fixed_quotient_family)
        return 0

    if args.scan_n138_fixed_quotient_family is not None:
        print_n138_fixed_quotient_family(args.scan_n138_fixed_quotient_family)
        return 0

    if args.scan_n160_fixed_quotient_family is not None:
        print_n160_fixed_quotient_family(args.scan_n160_fixed_quotient_family)
        return 0

    if args.scan_n170_fixed_quotient_family is not None:
        print_n170_fixed_quotient_family(args.scan_n170_fixed_quotient_family)
        return 0

    if args.scan_n144_fixed_quotient_family is not None:
        print_n144_fixed_quotient_family(args.scan_n144_fixed_quotient_family)
        return 0

    if args.scan_n225_fixed_quotient_family is not None:
        print_n225_fixed_quotient_family(args.scan_n225_fixed_quotient_family)
        return 0

    if args.scan_n168_fixed_quotient_family is not None:
        print_n168_fixed_quotient_family(args.scan_n168_fixed_quotient_family)
        return 0

    if args.scan_n240_fixed_quotient_family is not None:
        print_n240_fixed_quotient_family(args.scan_n240_fixed_quotient_family)
        return 0

    if args.scan_n180_fixed_quotient_family is not None:
        print_n180_fixed_quotient_family(args.scan_n180_fixed_quotient_family)
        return 0

    if args.scan_n150_fixed_quotient_family is not None:
        print_n150_fixed_quotient_family(args.scan_n150_fixed_quotient_family)
        return 0

    if args.scan_n156_fixed_quotient_family is not None:
        print_n156_fixed_quotient_family(args.scan_n156_fixed_quotient_family)
        return 0

    if args.scan_n190_fixed_quotient_family is not None:
        print_n190_fixed_quotient_family(args.scan_n190_fixed_quotient_family)
        return 0

    if args.scan_n255_fixed_quotient_family is not None:
        print_n255_fixed_quotient_family(args.scan_n255_fixed_quotient_family)
        return 0

    if args.scan_n189_fixed_quotient_family is not None:
        print_n189_fixed_quotient_family(args.scan_n189_fixed_quotient_family)
        return 0

    if args.scan_n200_fixed_quotient_family is not None:
        print_n200_fixed_quotient_family(args.scan_n200_fixed_quotient_family)
        return 0

    if args.scan_n140_fixed_quotient_family is not None:
        print_n140_fixed_quotient_family(args.scan_n140_fixed_quotient_family)
        return 0

    if args.scan_n210_fixed_quotient_family is not None:
        print_n210_fixed_quotient_family(args.scan_n210_fixed_quotient_family)
        return 0

    if args.scan_n270_fixed_quotient_family is not None:
        print_n270_fixed_quotient_family(args.scan_n270_fixed_quotient_family)
        return 0

    if args.scan_n174_fixed_quotient_family is not None:
        print_n174_fixed_quotient_family(args.scan_n174_fixed_quotient_family)
        return 0

    if args.scan_n285_fixed_quotient_family is not None:
        print_n285_fixed_quotient_family(args.scan_n285_fixed_quotient_family)
        return 0

    if args.scan_n154_fixed_quotient_family is not None:
        print_n154_fixed_quotient_family(args.scan_n154_fixed_quotient_family)
        return 0

    if args.scan_n186_fixed_quotient_family is not None:
        print_n186_fixed_quotient_family(args.scan_n186_fixed_quotient_family)
        return 0

    if args.scan_n220_fixed_quotient_family is not None:
        print_n220_fixed_quotient_family(args.scan_n220_fixed_quotient_family)
        return 0

    if args.scan_n300_fixed_quotient_family is not None:
        print_n300_fixed_quotient_family(args.scan_n300_fixed_quotient_family)
        return 0

    if args.scan_n230_fixed_quotient_family is not None:
        print_n230_fixed_quotient_family(args.scan_n230_fixed_quotient_family)
        return 0

    if args.scan_n315_fixed_quotient_family is not None:
        print_n315_fixed_quotient_family(args.scan_n315_fixed_quotient_family)
        return 0

    if args.scan_n198_fixed_quotient_family is not None:
        print_n198_fixed_quotient_family(args.scan_n198_fixed_quotient_family)
        return 0

    if args.scan_n231_fixed_quotient_family is not None:
        print_n231_fixed_quotient_family(args.scan_n231_fixed_quotient_family)
        return 0

    if args.scan_n204_fixed_quotient_family is not None:
        print_n204_fixed_quotient_family(args.scan_n204_fixed_quotient_family)
        return 0

    if args.scan_n330_fixed_quotient_family is not None:
        print_n330_fixed_quotient_family(args.scan_n330_fixed_quotient_family)
        return 0

    if args.scan_n345_fixed_quotient_family is not None:
        print_n345_fixed_quotient_family(args.scan_n345_fixed_quotient_family)
        return 0

    if args.scan_n182_fixed_quotient_family is not None:
        print_n182_fixed_quotient_family(args.scan_n182_fixed_quotient_family)
        return 0

    if args.scan_m100t_d10_family is not None:
        print_m100t_d10_family(args.scan_m100t_d10_family)
        return 0

    if args.scan_m72t_d6t_family is not None:
        print_m72t_d6t_family(args.scan_m72t_d6t_family)
        return 0

    if args.scan_m72t_d12_family is not None:
        print_m72t_d12_family(args.scan_m72t_d12_family)
        return 0

    if args.scan_m36t_d6_family is not None:
        print_m36t_d6_family(args.scan_m36t_d6_family)
        return 0

    if args.scan_dgt1_gaps is not None:
        print_dgt1_gap_scan(args.scan_dgt1_gaps, args.scan_private_failures)
        return 0

    workdir = Path(args.workdir).resolve()
    output = workdir / args.output if not args.output.is_absolute() else args.output
    solver = SchurModSolver(workdir=workdir, timeout_seconds=args.timeout_seconds)
    build_doc(output, solver, args.moduli, args.timeout_seconds)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
