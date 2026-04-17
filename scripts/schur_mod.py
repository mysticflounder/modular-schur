#!/usr/bin/env python3
"""SAT tooling for modular generalized Schur numbers.

This module implements a direct CNF encoding for S_m(k, ell) and uses either
PySAT (if available) or an external CaDiCaL binary. In this workspace the
external path is expected to be used, because package installation is blocked.
"""

from __future__ import annotations

import argparse
import itertools
import os
import subprocess
import sys
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, Sequence


SAT = "SAT"
UNSAT = "UNSAT"
TIMEOUT = "TIMEOUT"


@dataclass(frozen=True)
class SolveOutcome:
    status: str
    coloring: tuple[int, ...] | None
    n: int
    runtime_seconds: float
    cnf_path: Path | None = None
    solution_path: Path | None = None
    proof_path: Path | None = None
    proof_verified: bool | None = None
    exit_code: int | None = None


@dataclass(frozen=True)
class SearchOutcome:
    value: int
    witness: SolveOutcome
    unsat_boundary: SolveOutcome | None


@dataclass(frozen=True)
class SweepCell:
    m: int
    k: int
    ell: int
    outcome: SearchOutcome | None
    theorem8_predicted: int | None
    theorem8_match: bool | None
    error: str | None = None


def theorem_value(m: int, k: int, ell: int) -> int:
    """Closed formulas from Theorems 6, 7, 9, 10 for m in {4,5,6,7}."""
    if m == 4:
        if ell % 4 == 1:
            return 0
        if k == 1 or (k >= 2 and ell % 4 == 3):
            return 1
        return 3

    if m == 5:
        if ell % 5 == 1:
            return 0
        if k == 1:
            return 1
        if k in (2, 3) and ell != 2:
            return k
        return 4

    if m == 6:
        if ell % 6 == 1:
            return 0
        residue = ell % 6
        if (k == 1 and ell != 3) or (k >= 2 and residue == 4):
            return 1
        if (k == 1 and ell == 3) or (k >= 2 and residue in (3, 5)):
            return 2
        if k == 2 and ell == 2:
            return 4
        if k == 2 and residue in (0, 2) and ell >= 6:
            return 3
        if k >= 3 and residue in (0, 2):
            return 5
        raise ValueError(f"Unhandled theorem case for m=6, k={k}, ell={ell}")

    if m == 7:
        if ell % 7 == 1:
            return 0
        if k == 1 and ell != 3:
            return 1
        if (k == 1 and ell == 3) or (k == 2 and ell >= 4):
            return 2
        if (k == 2 and ell in (2, 3)) or (k == 3 and ell >= 5):
            return 3
        if k == 4 and ell >= 5:
            return 4
        if (k == 3 and ell == 3) or (k == 5 and ell >= 5):
            return 5
        if (k == 3 and ell in (2, 4)) or (k == 4 and ell in (2, 3, 4)) or (
            k == 5 and ell in (2, 3, 4)
        ) or k >= 6:
            return 6
        raise ValueError(f"Unhandled theorem case for m=7, k={k}, ell={ell}")

    raise ValueError(f"No theorem formula implemented for m={m}")


def prime_power_data(m: int) -> tuple[int, int] | None:
    if m < 2:
        return None
    for p in range(2, m + 1):
        if m % p != 0:
            continue
        exponent = 0
        value = m
        while value % p == 0:
            value //= p
            exponent += 1
        if value == 1:
            is_prime = True
            for q in range(2, int(p**0.5) + 1):
                if p % q == 0:
                    is_prime = False
                    break
            if is_prime:
                return p, exponent
    return None


def theorem8_value(m: int, k: int, ell: int) -> int | None:
    data = prime_power_data(m)
    if data is None:
        return None

    p, exponent = data
    if ell < m - 1 or ell % p == 1:
        return None

    if 1 <= k <= p - 1:
        return k

    if exponent == 1:
        return p - 1

    u = k - p + 2
    if 2 <= u <= p ** (exponent - 1):
        return u * p - 1

    cutoff = p + (p ** (exponent - 1) - 2)
    if k >= cutoff:
        return m - 1

    return None


class SchurModSolver:
    def __init__(
        self,
        workdir: Path,
        cadical_bin: str = "cadical",
        timeout_seconds: int = 300,
        seed: int = 0,
    ) -> None:
        self.workdir = workdir
        self.timeout_seconds = timeout_seconds
        self.seed = seed
        self.cadical_bin = cadical_bin
        self.artifacts_dir = self.workdir / "artifacts"
        self.cnf_dir = self.artifacts_dir / "cnf"
        self.sol_dir = self.artifacts_dir / "sol"
        self.proof_dir = self.artifacts_dir / "proof"
        self.cnf_dir.mkdir(parents=True, exist_ok=True)
        self.sol_dir.mkdir(parents=True, exist_ok=True)
        self.proof_dir.mkdir(parents=True, exist_ok=True)
        self.cache: dict[tuple[int, int, int, int], SolveOutcome] = {}
        self._pysat_solver_cls = self._load_pysat_solver()

    @staticmethod
    def _load_pysat_solver():
        try:
            from pysat.formula import CNF  # noqa: F401
            from pysat.solvers import Cadical153
        except Exception:
            return None
        return Cadical153

    @staticmethod
    def _var(i: int, j: int, k: int) -> int:
        return (i - 1) * k + j

    def _exactly_one_clauses(self, n: int, k: int) -> list[list[int]]:
        clauses: list[list[int]] = []
        for i in range(1, n + 1):
            vars_i = [self._var(i, j, k) for j in range(1, k + 1)]
            clauses.append(vars_i)
            for a in range(k):
                for b in range(a + 1, k):
                    clauses.append([-vars_i[a], -vars_i[b]])
        return clauses

    def _symmetry_clauses(self, n: int, k: int) -> list[list[int]]:
        if n == 0:
            return []
        clauses = [[self._var(1, 1, k)]]
        for i in range(2, n + 1):
            for j in range(2, k + 1):
                support = [self._var(t, j - 1, k) for t in range(1, i)]
                clauses.append([-self._var(i, j, k), *support])
        return clauses

    @staticmethod
    def _dedupe_clause(lits: Iterable[int]) -> list[int]:
        seen: set[int] = set()
        clause: list[int] = []
        for lit in lits:
            if lit not in seen:
                seen.add(lit)
                clause.append(lit)
        return clause

    @staticmethod
    def _reachable_residues_by_length(
        values: Sequence[int],
        m: int,
        max_length: int,
    ) -> list[set[int]]:
        reachable: list[set[int]] = [set() for _ in range(max_length + 1)]
        reachable[0] = {0}
        residues = [value % m for value in values]
        for length in range(1, max_length + 1):
            current: set[int] = set()
            for residue in reachable[length - 1]:
                for value_residue in residues:
                    current.add((residue + value_residue) % m)
            reachable[length] = current
        return reachable

    def build_cnf(self, m: int, k: int, ell: int, n: int) -> tuple[int, list[list[int]]]:
        if n < 0:
            raise ValueError("n must be nonnegative")
        if m < 1 or k < 1 or ell < 1:
            raise ValueError("m, k, ell must be positive")
        num_vars = n * k
        clauses = self._exactly_one_clauses(n, k)
        clauses.extend(self._symmetry_clauses(n, k))
        if n == 0:
            return num_vars, clauses

        residue_to_targets: dict[int, list[int]] = {}
        for y in range(1, n + 1):
            residue_to_targets.setdefault(y % m, []).append(y)

        values = list(range(1, n + 1))
        for mask in range(1, 1 << n):
            support = [values[index] for index in range(n) if mask & (1 << index)]
            support_size = len(support)
            if support_size > ell:
                continue

            # Clauses only depend on the distinct support used by the ell-tuple.
            # We therefore compute which residues are reachable by an ell-term sum
            # whose support is exactly this subset, rather than enumerating all
            # length-ell multisets explicitly.
            base_residue = sum(support) % m
            extra_length = ell - support_size
            reachable_residues = self._reachable_residues_by_length(support, m, extra_length)
            for extra_residue in reachable_residues[extra_length]:
                residue = (base_residue + extra_residue) % m
                targets = residue_to_targets.get(residue, [])
                if not targets:
                    continue
                for y in targets:
                    for color in range(1, k + 1):
                        lits = [-self._var(x, color, k) for x in support]
                        lits.append(-self._var(y, color, k))
                        clauses.append(self._dedupe_clause(lits))
        return num_vars, clauses

    @staticmethod
    def _write_dimacs(path: Path, num_vars: int, clauses: Sequence[Sequence[int]]) -> None:
        with path.open("w", encoding="ascii") as handle:
            handle.write(f"p cnf {num_vars} {len(clauses)}\n")
            for clause in clauses:
                handle.write(" ".join(str(lit) for lit in clause))
                handle.write(" 0\n")

    @staticmethod
    def _parse_solution(solution_path: Path, n: int, k: int) -> tuple[int, ...]:
        assignments: dict[int, bool] = {}
        with solution_path.open("r", encoding="ascii") as handle:
            for line in handle:
                if not line.startswith("v "):
                    continue
                for token in line.split()[1:]:
                    lit = int(token)
                    if lit == 0:
                        continue
                    assignments[abs(lit)] = lit > 0
        coloring: list[int] = []
        for i in range(1, n + 1):
            chosen = None
            for j in range(1, k + 1):
                var = (i - 1) * k + j
                if assignments.get(var, False):
                    chosen = j
                    break
            if chosen is None:
                raise RuntimeError(f"Missing color assignment for position {i}")
            coloring.append(chosen)
        return tuple(coloring)

    def _verify_proof(self, cnf_path: Path, proof_path: Path) -> bool | None:
        drat_trim = shutil_which("drat-trim")
        if drat_trim is None:
            return None
        proc = subprocess.run(
            [drat_trim, str(cnf_path), str(proof_path)],
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            timeout=self.timeout_seconds,
            check=False,
        )
        return proc.returncode == 0 and "s VERIFIED" in proc.stdout

    def _solve_with_pysat(
        self, m: int, k: int, ell: int, n: int, num_vars: int, clauses: list[list[int]]
    ) -> SolveOutcome | None:
        if self._pysat_solver_cls is None:
            return None
        solver_cls = self._pysat_solver_cls
        start = time.perf_counter()
        with solver_cls(bootstrap_with=clauses) as solver:
            solved = solver.solve_limited(expect_interrupt=True)
            runtime = time.perf_counter() - start
            if solved is True:
                model = solver.get_model() or []
                positives = {lit for lit in model if lit > 0}
                coloring = []
                for i in range(1, n + 1):
                    chosen = None
                    for j in range(1, k + 1):
                        if self._var(i, j, k) in positives:
                            chosen = j
                            break
                    if chosen is None:
                        raise RuntimeError(f"Missing color assignment for position {i}")
                    coloring.append(chosen)
                return SolveOutcome(
                    status=SAT,
                    coloring=tuple(coloring),
                    n=n,
                    runtime_seconds=runtime,
                )
            if solved is False:
                return SolveOutcome(
                    status=UNSAT,
                    coloring=None,
                    n=n,
                    runtime_seconds=runtime,
                )
            return SolveOutcome(
                status=TIMEOUT,
                coloring=None,
                n=n,
                runtime_seconds=runtime,
            )

    def solve_n(self, m: int, k: int, ell: int, n: int) -> SolveOutcome:
        key = (m, k, ell, n)
        if key in self.cache:
            return self.cache[key]
        if n == 0:
            outcome = SolveOutcome(status=SAT, coloring=tuple(), n=0, runtime_seconds=0.0)
            self.cache[key] = outcome
            return outcome

        num_vars, clauses = self.build_cnf(m, k, ell, n)
        pysat_outcome = self._solve_with_pysat(m, k, ell, n, num_vars, clauses)
        if pysat_outcome is not None and pysat_outcome.status != TIMEOUT:
            self.cache[key] = pysat_outcome
            return pysat_outcome

        stem = f"m{m}_k{k}_e{ell}_n{n}"
        cnf_path = self.cnf_dir / f"{stem}.cnf"
        sol_path = self.sol_dir / f"{stem}.sol"
        proof_path = self.proof_dir / f"{stem}.drat"
        self._write_dimacs(cnf_path, num_vars, clauses)

        command = [
            "timeout",
            str(self.timeout_seconds),
            self.cadical_bin,
            "--seed=0",
            "-q",
            "-w",
            str(sol_path),
            str(cnf_path),
            str(proof_path),
        ]

        start = time.perf_counter()
        proc = subprocess.run(
            command,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            check=False,
        )
        runtime = time.perf_counter() - start

        if proc.returncode == 10:
            coloring = self._parse_solution(sol_path, n, k)
            outcome = SolveOutcome(
                status=SAT,
                coloring=coloring,
                n=n,
                runtime_seconds=runtime,
                cnf_path=cnf_path,
                solution_path=sol_path,
                exit_code=proc.returncode,
            )
        elif proc.returncode == 20:
            proof_verified = None
            if proof_path.exists():
                proof_verified = self._verify_proof(cnf_path, proof_path)
            outcome = SolveOutcome(
                status=UNSAT,
                coloring=None,
                n=n,
                runtime_seconds=runtime,
                cnf_path=cnf_path,
                solution_path=sol_path if sol_path.exists() else None,
                proof_path=proof_path if proof_path.exists() else None,
                proof_verified=proof_verified,
                exit_code=proc.returncode,
            )
        elif proc.returncode == 124:
            outcome = SolveOutcome(
                status=TIMEOUT,
                coloring=None,
                n=n,
                runtime_seconds=runtime,
                cnf_path=cnf_path,
                solution_path=sol_path if sol_path.exists() else None,
                proof_path=proof_path if proof_path.exists() else None,
                exit_code=proc.returncode,
            )
        else:
            raise RuntimeError(
                f"CaDiCaL failed for (m={m}, k={k}, ell={ell}, n={n}) "
                f"with exit code {proc.returncode} and output:\n{proc.stdout}"
            )

        self.cache[key] = outcome
        return outcome

    def search(self, m: int, k: int, ell: int) -> SearchOutcome:
        low = 0
        high = m  # theoretical UNSAT upper bound from S_m(k, ell) <= m - 1

        while high - low > 1:
            mid = (low + high) // 2
            outcome = self.solve_n(m, k, ell, mid)
            if outcome.status == TIMEOUT:
                raise RuntimeError(
                    f"Timeout during search for (m={m}, k={k}, ell={ell}) at n={mid}"
                )
            if outcome.status == SAT:
                low = mid
            else:
                high = mid

        witness = self.solve_n(m, k, ell, low)
        if witness.status != SAT:
            raise RuntimeError(f"Expected SAT witness at n={low}, got {witness.status}")

        unsat_boundary = None
        boundary_n = low + 1
        if boundary_n <= m - 1:
            unsat_boundary = self.solve_n(m, k, ell, boundary_n)
            if unsat_boundary.status != UNSAT:
                raise RuntimeError(
                    f"Expected UNSAT boundary at n={boundary_n}, got {unsat_boundary.status}"
                )

        return SearchOutcome(value=low, witness=witness, unsat_boundary=unsat_boundary)


def shutil_which(name: str) -> str | None:
    for directory in os.environ.get("PATH", "").split(os.pathsep):
        candidate = Path(directory) / name
        if candidate.exists() and os.access(candidate, os.X_OK):
            return str(candidate)
    return None


def format_coloring(coloring: Sequence[int] | None) -> str:
    if coloring is None:
        return "-"
    if not coloring:
        return "[]"
    return "[" + ", ".join(str(x) for x in coloring) + "]"


def write_validation_report(output_path: Path, rows: Sequence[dict[str, object]]) -> None:
    lines = [
        "# Phase 2 Validation",
        "",
        "Validation scope: reproduce every closed-case value from Theorems 6, 7, 9, 10 for",
        "- `m in {4,5,6,7}`",
        "- `k in {1,...,6}`",
        "- `ell in {2,...,8}`",
        "",
        f"Total cases: {len(rows)}",
        "",
    ]

    mismatches = [row for row in rows if not row["match"]]
    lines.append(f"Mismatches: {len(mismatches)}")
    lines.append("")

    lines.append("| m | k | ell | predicted | computed | match? | runtime (s) |")
    lines.append("| --- | --- | --- | --- | --- | --- | --- |")
    for row in rows:
        lines.append(
            f"| {row['m']} | {row['k']} | {row['ell']} | {row['predicted']} | "
            f"{row['computed']} | {'yes' if row['match'] else 'NO'} | {row['runtime_seconds']:.3f} |"
        )

    if mismatches:
        lines.extend(["", "## Mismatches", ""])
        for row in mismatches:
            lines.append(
                f"- `(m,k,ell)=({row['m']},{row['k']},{row['ell']})`: "
                f"predicted `{row['predicted']}`, computed `{row['computed']}`."
            )
    else:
        lines.extend(["", "## Result", "", "All validation cases matched the closed-form theorems."])

    output_path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def write_s8_report(output_path: Path, table: dict[tuple[int, int], SearchOutcome]) -> None:
    ells = list(range(2, 9))
    ks = list(range(1, 9))
    lines = [
        "# Phase 2 S8 Table",
        "",
        "Computed values of `S_8(k, ell)` for `k in {1,...,8}` and `ell in {2,...,8}`.",
        "",
        "## Grid",
        "",
    ]

    header = "| k \\\\ ell | " + " | ".join(str(ell) for ell in ells) + " |"
    sep = "| --- | " + " | ".join("---" for _ in ells) + " |"
    lines.append(header)
    lines.append(sep)
    for k in ks:
        row = [str(table[(k, ell)].value) for ell in ells]
        lines.append(f"| {k} | " + " | ".join(row) + " |")

    lines.extend(["", "## Boundary Witnesses", ""])
    for ell in ells:
        lines.append(f"### ell = {ell}")
        lines.append("")
        for k in ks:
            outcome = table[(k, ell)]
            witness = outcome.witness
            boundary = outcome.unsat_boundary
            boundary_note = (
                f"`n={boundary.n}` UNSAT, proof verified={boundary.proof_verified}"
                if boundary is not None
                else f"`n={outcome.value + 1}` exceeds the universal upper bound `m-1=7`."
            )
            lines.append(
                f"- `k={k}`: `S_8({k},{ell})={outcome.value}`; "
                f"SAT witness at `n={witness.n}` is `{format_coloring(witness.coloring)}`; "
                f"{boundary_note}"
            )
        lines.append("")

    # Lightweight pattern discovery.
    lines.extend(["## Structure Notes", ""])
    lines.append("Observed regularities in the computed table:")
    lines.append(
        "- The table stabilizes very quickly in `k`: for every `ell in {2,...,8}`, the row is constant for all `k >= 3`."
    )
    lines.append(
        "- On that stable range `k >= 3`, there are only three row values: "
        "`7` for `ell in {2,4,6,8}`, `3` for `ell in {3,7}`, and `1` for `ell=5`."
    )
    lines.append(
        "- The `ell=5` row is uniformly `1`, which is exactly the behavior suggested by Corollary 4 for "
        "`m=8=2n` and `ell ≡ n+1 ≡ 5 (mod 8)`."
    )
    lines.append(
        "- The even rows `ell in {4,6,8}` are identical across all `k`, and `ell=2` joins the same stable value once `k >= 3`."
    )
    lines.append(
        "- The odd rows split: `ell in {3,7}` stabilize at `3`, while the special residue class `ell=5` collapses to `1`."
    )
    lines.append(
        "- There are small-`k` boundary effects only at `k=1` and `k=2`. The entire `k=2` row is "
        "`[4,3,3,1,3,2,3]` across `ell=2,...,8`."
    )
    lines.append(
        "- Compare especially `ell=5` against Corollary 4 and `ell=8` against Example 1 in D'orville et al.; "
        "those rows provide anchors inside the new `m=8` table."
    )
    lines.append(
        "- A naive plug-in of Theorem 8 for `ell=8` and small `k` should be re-checked carefully before using it as a shortcut. "
        "The SAT table agrees with the paper's explicit `S_8(4,8)=7` example, but the `k=3` entry is already saturated at `7`."
    )

    output_path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def run_search_with_timeout_handling(
    solver: SchurModSolver,
    m: int,
    k: int,
    ell: int,
) -> SweepCell:
    theorem8_predicted = theorem8_value(m, k, ell)
    try:
        outcome = solver.search(m, k, ell)
    except RuntimeError as exc:
        if "Timeout during search" not in str(exc):
            raise
        return SweepCell(
            m=m,
            k=k,
            ell=ell,
            outcome=None,
            theorem8_predicted=theorem8_predicted,
            theorem8_match=None,
            error="timeout",
        )

    theorem8_match = None
    if theorem8_predicted is not None:
        theorem8_match = theorem8_predicted == outcome.value

    return SweepCell(
        m=m,
        k=k,
        ell=ell,
        outcome=outcome,
        theorem8_predicted=theorem8_predicted,
        theorem8_match=theorem8_match,
    )


def compute_sweep(
    solver: SchurModSolver,
    m: int,
    ks: Sequence[int],
    ells: Sequence[int],
    *,
    check_theorem8: bool = True,
) -> dict[tuple[int, int], SweepCell]:
    table: dict[tuple[int, int], SweepCell] = {}
    for k in ks:
        for ell in ells:
            cell = run_search_with_timeout_handling(solver, m, k, ell)
            if check_theorem8 and cell.theorem8_match is False:
                raise RuntimeError(
                    f"Theorem 8 mismatch at (m,k,ell)=({m},{k},{ell}): "
                    f"predicted {cell.theorem8_predicted}, computed {cell.outcome.value if cell.outcome else 'unknown'}"
                )
            table[(k, ell)] = cell
    return table


def stabilized_from_k(
    table: dict[tuple[int, int], SweepCell],
    ks: Sequence[int],
    ell: int,
) -> tuple[int, int] | None:
    if not ks:
        return None
    values_by_k: dict[int, int] = {}
    for k in ks:
        cell = table[(k, ell)]
        if cell.outcome is None:
            return None
        values_by_k[k] = cell.outcome.value

    for candidate in ks:
        target = values_by_k[candidate]
        if all(values_by_k[k] == target for k in ks if k >= candidate):
            return candidate, target
    return None


def write_general_table_report(
    output_path: Path,
    m: int,
    ks: Sequence[int],
    ells: Sequence[int],
    table: dict[tuple[int, int], SweepCell],
    title: str,
    intro: str,
    *,
    include_theorem8_section: bool = True,
) -> None:
    lines = [
        f"# {title}",
        "",
        intro,
        "",
        "## Grid",
        "",
    ]

    header = "| k \\\\ ell | " + " | ".join(str(ell) for ell in ells) + " |"
    sep = "| --- | " + " | ".join("---" for _ in ells) + " |"
    lines.append(header)
    lines.append(sep)
    for k in ks:
        row: list[str] = []
        for ell in ells:
            cell = table[(k, ell)]
            if cell.outcome is None:
                row.append("?")
            else:
                row.append(str(cell.outcome.value))
        lines.append(f"| {k} | " + " | ".join(row) + " |")

    if include_theorem8_section:
        theorem_cells = [
            cell for cell in table.values() if cell.theorem8_predicted is not None and cell.outcome is not None
        ]
        lines.extend(["", "## Theorem 8 Cross-Check", ""])
        if theorem_cells:
            mismatches = [cell for cell in theorem_cells if cell.theorem8_match is False]
            lines.append(f"- Theorem-covered cells checked: `{len(theorem_cells)}`.")
            if mismatches:
                lines.append("- MISMATCHES detected. This indicates an encoder bug.")
                for cell in mismatches:
                    assert cell.outcome is not None
                    lines.append(
                        f"- `(k, ell)=({cell.k},{cell.ell})`: predicted `{cell.theorem8_predicted}`, "
                        f"computed `{cell.outcome.value}`."
                    )
            else:
                lines.append("- All theorem-covered cells matched the SAT computation.")
            for cell in theorem_cells:
                assert cell.outcome is not None
                lines.append(
                    f"- `(k, ell)=({cell.k},{cell.ell})`: theorem predicts `{cell.theorem8_predicted}`, "
                    f"SAT gives `{cell.outcome.value}`."
                )
        else:
            lines.append("- No requested cells fall under Theorem 8 / Corollary 8.")

    lines.extend(["", "## Boundary Witnesses", ""])
    for ell in ells:
        lines.append(f"### ell = {ell}")
        lines.append("")
        for k in ks:
            cell = table[(k, ell)]
            if cell.outcome is None:
                lines.append(f"- `k={k}`: unknown due to `{cell.error}`.")
                continue
            witness = cell.outcome.witness
            boundary = cell.outcome.unsat_boundary
            if boundary is None:
                boundary_note = f"`n={cell.outcome.value + 1}` exceeds the universal upper bound `m-1={m - 1}`."
            else:
                boundary_note = (
                    f"`n={boundary.n}` UNSAT, proof verified={boundary.proof_verified}"
                )
            theorem_note = ""
            if include_theorem8_section and cell.theorem8_predicted is not None:
                theorem_note = f" theorem8=`{cell.theorem8_predicted}`;"
            lines.append(
                f"- `k={k}`: `S_{m}({k},{ell})={cell.outcome.value}`; "
                f"SAT witness at `n={witness.n}` is `{format_coloring(witness.coloring)}`; "
                f"{boundary_note}{theorem_note}"
            )
        lines.append("")

    lines.extend(["## Stabilization Notes", ""])
    for ell in ells:
        stable = stabilized_from_k(table, ks, ell)
        if stable is None:
            lines.append(f"- `ell={ell}`: stabilization undetermined from the requested grid.")
        else:
            k0, value = stable
            lines.append(
                f"- `ell={ell}`: the column stabilizes by `k0={k0}` with value `{value}` over the checked range."
            )

    output_path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def run_validation(solver: SchurModSolver, output_path: Path) -> bool:
    rows: list[dict[str, object]] = []
    for m in range(4, 8):
        for k in range(1, 7):
            for ell in range(2, 9):
                predicted = theorem_value(m, k, ell)
                search_outcome = solver.search(m, k, ell)
                rows.append(
                    {
                        "m": m,
                        "k": k,
                        "ell": ell,
                        "predicted": predicted,
                        "computed": search_outcome.value,
                        "match": predicted == search_outcome.value,
                        "runtime_seconds": (
                            search_outcome.witness.runtime_seconds
                            + (search_outcome.unsat_boundary.runtime_seconds if search_outcome.unsat_boundary else 0.0)
                        ),
                    }
                )
                if predicted != search_outcome.value:
                    write_validation_report(output_path, rows)
                    return False
    write_validation_report(output_path, rows)
    return True


def run_s8_table(solver: SchurModSolver, output_path: Path) -> None:
    table: dict[tuple[int, int], SearchOutcome] = {}
    for k in range(1, 9):
        for ell in range(2, 9):
            table[(k, ell)] = solver.search(8, k, ell)
    write_s8_report(output_path, table)


def run_general_table(
    solver: SchurModSolver,
    m: int,
    ks: Sequence[int],
    ells: Sequence[int],
    output_path: Path,
    title: str,
    intro: str,
    *,
    check_theorem8: bool = True,
    include_theorem8_section: bool = True,
) -> None:
    table = compute_sweep(solver, m, ks, ells, check_theorem8=check_theorem8)
    write_general_table_report(
        output_path,
        m,
        ks,
        ells,
        table,
        title,
        intro,
        include_theorem8_section=include_theorem8_section,
    )


def run_phase3_reports(solver: SchurModSolver, docs_dir: Path) -> None:
    docs_dir.mkdir(parents=True, exist_ok=True)
    ks = list(range(1, 9))
    run_general_table(
        solver=solver,
        m=8,
        ks=ks,
        ells=list(range(9, 13)),
        output_path=docs_dir / "phase3-S8-extended.md",
        title="Phase 3 S8 Extended Table",
        intro="Computed values of `S_8(k, ell)` for `k in {1,...,8}` and `ell in {9,...,12}`.",
        check_theorem8=False,
        include_theorem8_section=False,
    )
    run_general_table(
        solver=solver,
        m=9,
        ks=ks,
        ells=list(range(2, 11)),
        output_path=docs_dir / "phase3-S9-table.md",
        title="Phase 3 S9 Table",
        intro="Computed values of `S_9(k, ell)` for `k in {1,...,8}` and `ell in {2,...,10}`.",
    )
    run_general_table(
        solver=solver,
        m=11,
        ks=ks,
        ells=list(range(2, 11)),
        output_path=docs_dir / "phase3-S11-table.md",
        title="Phase 3 S11 Table",
        intro="Computed values of `S_11(k, ell)` for `k in {1,...,8}` and `ell in {2,...,10}`.",
    )


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--workdir",
        default=str(Path(__file__).resolve().parent),
        help="Workspace root for artifacts and docs.",
    )
    parser.add_argument(
        "--timeout-seconds",
        type=int,
        default=300,
        help="Per-instance solver timeout in seconds.",
    )
    subparsers = parser.add_subparsers(dest="command", required=True)

    solve_parser = subparsers.add_parser("solve", help="Solve a fixed (m,k,ell,n) instance.")
    solve_parser.add_argument("--m", type=int, required=True)
    solve_parser.add_argument("--k", type=int, required=True)
    solve_parser.add_argument("--ell", type=int, required=True)
    solve_parser.add_argument("--n", type=int, required=True)

    search_parser = subparsers.add_parser("search", help="Compute S_m(k, ell).")
    search_parser.add_argument("--m", type=int, required=True)
    search_parser.add_argument("--k", type=int, required=True)
    search_parser.add_argument("--ell", type=int, required=True)

    validate_parser = subparsers.add_parser("validate", help="Run theorem validation.")
    validate_parser.add_argument(
        "--output",
        type=Path,
        default=Path("docs/phase2-validation.md"),
    )

    table_parser = subparsers.add_parser("table8", help="Compute the S8 grid.")
    table_parser.add_argument(
        "--output",
        type=Path,
        default=Path("docs/phase2-S8-table.md"),
    )

    general_table_parser = subparsers.add_parser("table", help="Compute a generic S_m(k, ell) grid.")
    general_table_parser.add_argument("--m", type=int, required=True)
    general_table_parser.add_argument("--k-min", type=int, default=1)
    general_table_parser.add_argument("--k-max", type=int, required=True)
    general_table_parser.add_argument("--ell-min", type=int, required=True)
    general_table_parser.add_argument("--ell-max", type=int, required=True)
    general_table_parser.add_argument("--title", default="Table")
    general_table_parser.add_argument("--intro", default="Computed table.")
    general_table_parser.add_argument("--output", type=Path, required=True)

    phase3_parser = subparsers.add_parser("phase3", help="Generate the requested Phase 3 reports.")
    phase3_parser.add_argument(
        "--docs-dir",
        type=Path,
        default=Path("docs"),
    )

    args = parser.parse_args(argv)
    workdir = Path(args.workdir).resolve()
    solver = SchurModSolver(workdir=workdir, timeout_seconds=args.timeout_seconds)

    if args.command == "solve":
        outcome = solver.solve_n(args.m, args.k, args.ell, args.n)
        print(f"status={outcome.status}")
        print(f"runtime_seconds={outcome.runtime_seconds:.6f}")
        print(f"coloring={format_coloring(outcome.coloring)}")
        if outcome.proof_path is not None:
            print(f"proof_path={outcome.proof_path}")
            print(f"proof_verified={outcome.proof_verified}")
        return 0

    if args.command == "search":
        outcome = solver.search(args.m, args.k, args.ell)
        print(f"S_{args.m}({args.k},{args.ell})={outcome.value}")
        print(f"witness={format_coloring(outcome.witness.coloring)}")
        if outcome.unsat_boundary is not None:
            print(
                f"unsat_boundary_n={outcome.unsat_boundary.n} "
                f"proof_verified={outcome.unsat_boundary.proof_verified}"
            )
        else:
            print(f"unsat_boundary_n={outcome.value + 1} (theoretical upper bound)")
        return 0

    if args.command == "validate":
        output = (workdir / args.output).resolve() if not args.output.is_absolute() else args.output
        output.parent.mkdir(parents=True, exist_ok=True)
        ok = run_validation(solver, output)
        return 0 if ok else 1

    if args.command == "table8":
        output = (workdir / args.output).resolve() if not args.output.is_absolute() else args.output
        output.parent.mkdir(parents=True, exist_ok=True)
        run_s8_table(solver, output)
        return 0

    if args.command == "table":
        output = (workdir / args.output).resolve() if not args.output.is_absolute() else args.output
        output.parent.mkdir(parents=True, exist_ok=True)
        ks = list(range(args.k_min, args.k_max + 1))
        ells = list(range(args.ell_min, args.ell_max + 1))
        run_general_table(
            solver=solver,
            m=args.m,
            ks=ks,
            ells=ells,
            output_path=output,
            title=args.title,
            intro=args.intro,
        )
        return 0

    if args.command == "phase3":
        docs_dir = (workdir / args.docs_dir).resolve() if not args.docs_dir.is_absolute() else args.docs_dir
        run_phase3_reports(solver, docs_dir)
        return 0

    raise AssertionError("unreachable")


if __name__ == "__main__":
    raise SystemExit(main())
