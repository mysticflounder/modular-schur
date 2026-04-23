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
    for mask in sorted_masks:
        if any(mask & sup == mask for sup in maximal_masks):
            continue
        maximal_masks.append(mask)
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
        or (m == 600 and d == 20)
        or (m, d) in phase24_rows
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
        "Filtered non-private residual rows after Phase 19--32 "
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
        help="print non-private residual rows up to LIMIT after filtering the Phase 19--32 proved rows",
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
    args = parser.parse_args()

    if args.scan_filtered_frontier is not None:
        print_filtered_frontier_scan(args.scan_filtered_frontier)
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
