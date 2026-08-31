<!--
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Adam McKenna <adam@mysticflounder.ai>
-->

# Public repository release runbook

This is the authoritative procedure for publishing from the private
source-of-truth repository `flound1129/schur-numbers` to the curated public
repository `mysticflounder/modular-schur`.

The procedure is intentionally two-repository and two-commit. Source changes
are reviewed, validated, committed, and pushed first. A generated public diff
is then validated in the public checkout, committed there, and pushed. Never
edit a generated public file as the source of a lasting change.

## Repository roles

| Repository | Local checkout | Role |
| --- | --- | --- |
| Source of truth | `/Users/adam/projects/math-projects/schur-numbers` | Lean sources, public-content sources, release manifest, publisher, paper source, research docs |
| Public staging checkout | `/Users/adam/projects/math-projects/modular-schur-public-staging` | Exact candidate tree for `github.com/mysticflounder/modular-schur` |

The public repository is curated, not a mirror. Its included Lean module set is
defined by `scripts/public-lean-modules.txt`. Its generated root imports every
module in that file. `scripts/check-public-release.sh` rejects an unlisted
project import, an omitted dependency, or an extra formalization module.

Do not treat old audit reports as release instructions. They retain historical
value, but this file and the executable release checks govern current work.

## Release scopes

Always name the scope explicitly.

| Scope | Command | May change | Protected |
| --- | --- | --- | --- |
| Lean and status | `--scope lean` | curated Lean, comparator files, metadata, CI, reproduction scripts, public README, `LEAN_STATUS.md`, `RELEASING.md`, `docs/status.html` | `paper/`, `docs/index.html`, `docs/paper/`, `docs/assets/` |
| Full publication | `--scope full` | everything above plus the complete built site and paper snapshot | no paper guard; use only with explicit paper-release authority |

The publisher has no default scope. It exits unless the caller supplies
`--scope lean` or `--scope full`, so paper publication cannot result from an
omitted option.

The Lean scope renders the status page with `build-site.sh --status-only`. That
mode does not read, render, copy, or replace paper inputs. The publisher copies
only the resulting `status.html`; shared assets stay frozen because they also
control the live paper presentation.

## Publisher-owned public paths

The publisher may stage only these paths in Lean scope:

```text
.github/workflows/comparator.yml
LICENSE
README.md
LEAN_STATUS.md
RELEASING.md
formalization.yaml
lean/**
scripts/schur_mod.py
scripts/phase9_stable_tables.py
scripts/lake-build.sh          # deletion only; deprecated local wrapper
docs/status.html
```

Full scope additionally owns `docs/**` and `paper/**`. The script never uses
`git add -A`. It starts from a clean public checkout, stages the allowlist, and
fails if any staged path falls outside that scope.

Untracked source `scratch/` content is not a release input and must remain
untouched.

## Required tools and policy

- Read the inherited workspace `AGENTS.md` and repository `CLAUDE.md` before
  work.
- Use the global `lake-build` wrapper for maintainer Lake builds. Do not restore
  or use `scripts/lake-build.sh`.
- The source toolchain is pinned by `lean/lean-toolchain`; Mathlib is pinned by
  `lean/lakefile.toml` and `lean/lake-manifest.json`.
- `pandoc` is required for the status page. A full site build additionally
  needs Node, the TikZ toolchain, and the vendored page assets.
- The public checkout must be on `main`, point exactly at
  `mysticflounder/modular-schur`, and have no staged, unstaged, or untracked
  non-ignored file.
- Run Git commands from the repository they affect. Do not operate on the
  public checkout through a source-repository Git invocation.

## 1. Synchronize both repositories

From the source checkout:

```bash
git status --short
git pull --rebase --autostash
```

Only known pre-existing source scratch may remain untracked. Stop if a tracked
change is not part of the release.

From the public checkout:

```bash
git status --short
git pull --rebase --autostash
git branch --show-current
git remote get-url origin
```

Expected results are a clean `main` branch and the canonical public origin.
The publisher repeats the branch, remote, and cleanliness checks before any
destination mutation.

## 2. Record the paper guard

For a Lean-scope release, record hashes before source publication work:

```bash
shasum -a 256 \
  /Users/adam/projects/math-projects/modular-schur-public-staging/paper/modular-schur.md \
  /Users/adam/projects/math-projects/modular-schur-public-staging/paper/modular-schur.pdf \
  /Users/adam/projects/math-projects/modular-schur-public-staging/docs/index.html \
  /Users/adam/projects/math-projects/modular-schur-public-staging/docs/paper/modular-schur.pdf
```

The hashes must match after assembly and after the public commit. Also require
an empty Git status under `paper/`, `docs/index.html`, `docs/paper/`, and
`docs/assets/`. The publisher enforces the Git guard; the explicit hashes make
the release report independently checkable.

## 3. Update source-owned release material

Lean changes belong under `lean/ModularSchur/`. Public-facing descriptions
belong in:

- `site/public-README.md`, exported as public `README.md`;
- `site/public-lean-status.md`, exported as public `LEAN_STATUS.md`;
- `site/content/index.md`, rendered as public `docs/status.html`;
- this runbook, exported as public `RELEASING.md`;
- `formalization.yaml`, for formalization and registry metadata;
- `lean/comparator/README.md`, for comparator scope and planning-only stubs.

When a new hand-written module is ready for public distribution, add its flat
module name to `scripts/public-lean-modules.txt`. Every transitive
`ModularSchur.*` import must also be listed. Do not add generated modules,
generated-dependent bridges, or a module carrying an unapproved trust
boundary merely to close imports.

The twelve live comparator declarations are atomic. A future comparator
expansion must update `Challenge.lean`, `Solution.lean`, `config.json`,
`axiom-audit.lean`, and the documentation in one reviewed change. Planning
rows in `lean/comparator/README.md` make no comparator claim.

## 4. Validate the source Lean state

First check host load; do not overlap another top-level Lean build:

```bash
pgrep -x lean | wc -l
sysctl -n vm.loadavg
sysctl -n hw.ncpu
```

Use focused targets before the aggregate. From `lean/`:

```bash
lake-build ModularSchur.TauClosure
lake-build ModularSchur.CanonicalCriticalCore
lake-build ModularSchur.DeficitGrowthCertificateShape
lake-build ModularSchur.PublicAxiomAudit
lake-build Challenge Solution
```

This checkout's Lean 4.33 toolchain ships Lake 5, whose `build` command rejects
the older `--jobs` and `-j` flags. Control risk with focused targets, the global
wrapper's per-worker memory ceiling, and host-load preflight rather than copying
an obsolete jobs option into the command.

`PublicAxiomAudit` must print only the repository-approved standard foundations
for every named capstone: `propext`, `Classical.choice`, and `Quot.sound`. The
comparator package has its own audit:

```bash
lean/comparator/check-conformance.sh
```

Interpret the gates separately:

- a green build establishes elaboration of the selected import closure;
- the release source scan rejects placeholders and disallowed implementation
  boundaries in the curated project modules;
- `#print axioms` establishes the transitive trust closure of the named
  capstones;
- the comparator and `nanoda` CI jobs govern only the configured twelve
  `Headline` declarations;
- an independent review is required before a new theorem package is described
  as independently audited.

## 5. Validate the status page

From the source root:

```bash
scripts/build-site.sh --status-only
node scripts/check-site-math.mjs site/build/status.html
```

Confirm that `site/build/index.html`, the source paper, and the source PDF were
not used as release outputs. A full site build is not required for Lean scope.

## 6. Review, commit, and push the source change

Review only owned paths:

```bash
git diff --check
git diff --stat
git status --short
```

Stage explicit files, inspect the staged set, commit, and push. Do not stage
the source `scratch/` tree. The source commit must exist before the publisher
renders `status.html`, because the page footer records the source revision.

## 7. Dry-run the public assembly

From the source root, after the source commit:

```bash
scripts/publish-public.sh \
  --scope lean \
  --public /Users/adam/projects/math-projects/modular-schur-public-staging \
  --dry-run
```

The dry run:

1. checks the public branch, origin, and cleanliness;
2. renders only the status page;
3. assembles an export in a temporary directory;
4. validates the exact module set, project-import closure, comparator
   artifacts, maintainer docs, and source-level trust guards;
5. reports file-level differences;
6. leaves the public index and worktree unchanged.

Any failure is fail-closed. Fix the source or release tooling, commit that fix,
and repeat the dry run.

## 8. Assemble and stage the public candidate

```bash
scripts/publish-public.sh \
  --scope lean \
  --public /Users/adam/projects/math-projects/modular-schur-public-staging
```

This repeats temporary assembly and validation, updates only owned public
paths, rechecks the paper guard, validates the destination tree, and stages the
owned diff. It does not commit by default.

Inspect the public candidate from the public checkout:

```bash
git status --short
git diff --cached --name-status
git diff --cached --check
```

There must be no unstaged or untracked non-ignored file and no staged path
outside the scope table.

## 9. Build and audit the exact public candidate

From the public checkout's `lean/` directory:

```bash
lake-build
lake-build Challenge Solution
lake-build ModularSchur.PublicAxiomAudit
```

Then run the public comparator preflight from the public checkout root:

```bash
lean/comparator/check-conformance.sh
```

From the source checkout, rerun the static release checker against the public
candidate and validate the published status math:

```bash
scripts/check-public-release.sh \
  /Users/adam/projects/math-projects/modular-schur-public-staging
node scripts/check-site-math.mjs \
  /Users/adam/projects/math-projects/modular-schur-public-staging/docs/status.html
```

Recompute the four paper-guard hashes from step 2 and compare them byte for
byte. This is the final no-paper gate.

## 10. Commit and push the public repository

From the public checkout:

```bash
git commit -m "publish audited Lean theorem packages"
git push
```

`publish-public.sh --scope lean --push` is available for already-routine,
prevalidated releases. The staged-first path above is preferred for a theorem
inventory expansion because it permits builds and trust audits against the
exact public bytes before commit.

Record both commit hashes in the handoff:

- source commit that generated the release;
- immutable public commit that was pushed.

## 11. Post-push verification

Wait for the public comparator and kernel-replay jobs to reach a terminal
state. Check the public GitHub tree at the pushed SHA, not merely the local
checkout. Confirm:

- CI is green;
- the public module count and root imports match `lean/PUBLIC_MODULES.txt`;
- `LEAN_STATUS.md` and `README.md` state the comparator/project-only split;
- the status page shows the current content date and source revision;
- every paper-guard hash still matches the pre-release value.

If CI fails, keep the public SHA as a failed immutable attempt, repair the
source of truth, and publish a new commit. Do not rewrite public history.

## Full releases

Use full scope only when the paper and complete website are authorized release
targets:

```bash
pandoc --number-sections paper/modular-schur.md -o paper/modular-schur.pdf
scripts/build-site.sh
node scripts/check-site-math.mjs site/build/index.html
node scripts/check-site-math.mjs site/build/status.html
scripts/publish-public.sh --scope full --dry-run
scripts/publish-public.sh --scope full
```

A full release replaces public `docs/` and `paper/`. It therefore requires an
additional paper-source/PDF synchronization review, figure render checks, link
checks, and explicit inspection of all shared assets. None of that authority is
implied by a Lean-scope request.

## Recovery before commit

The publisher requires a clean public checkout at entry, so any candidate diff
belongs to that one release. If validation fails after staging, inspect the
failure first. To abandon the candidate, restore only the publisher-owned paths
listed above from public `HEAD`; never reset the repository or remove a broad
directory without first resolving the exact target.

If a paper guard fails, stop. Do not commit a partial release. Record which
protected path changed, restore that exact path from public `HEAD`, fix the
publisher, and repeat the dry run.

## Palomar Registry handoff

Public publication and registry submission are separate terminal states. After
a clean public release, re-read the current
[submission standard](https://github.com/PalomarRegistry/PalomarPolicy/blob/main/CONTRIBUTING.md),
[mechanical contract](https://github.com/PalomarRegistry/PalomarSubmission/blob/main/scripts/submission_contract.py),
and [v0.4 metadata schema](https://raw.githubusercontent.com/mathlib-initiative/formalization.yaml/main/schema/v0.4.schema.json).
The requirements are external and can change after this runbook is committed.

The current nonstandard-layout form values are:

- repository: `mysticflounder/modular-schur`;
- project path: `lean`;
- comparator configuration path: `lean/comparator/config.json`;
- formalization metadata path: `formalization.yaml`;
- authorization relationship: responsible author or maintainer;
- commit: the final full 40-character public SHA, selected last.

Before selecting that SHA:

1. audit the public checkout, not the private source tree, against the current
   requirements;
2. require one Lakefile under `lean/`, a supported toolchain, credential-free
   GitHub dependencies pinned to full lowercase SHAs, and one matching root
   licence;
3. validate the Challenge size/import boundary, comparator keys, statements,
   permitted axioms, and both kernel replays;
4. validate `formalization.yaml` against both the upstream schema and Palomar's
   stricter provenance/classification contract;
5. ensure the checked-out snapshot stays below Palomar's current size limit;
6. wait for public CI and verify that its commit or an unchanged-gated-path
   ancestor is the one being relied on;
7. select the final 40-character public commit SHA;
8. submit that immutable SHA only after explicit submission authority.

The upstream schema check can be reproduced with:

```bash
uv run --with check-jsonschema check-jsonschema \
  --schemafile https://raw.githubusercontent.com/mathlib-initiative/formalization.yaml/main/schema/formalization.schema.json \
  formalization.yaml
```

The registry intake remains authoritative for Palomar's additional checks. A
local schema pass alone does not establish submission readiness.

Do not place a prospective SHA in `formalization.yaml`: the release commit
cannot reliably name itself. Record the selected submission SHA in the
submission system and the release handoff after the commit exists.
