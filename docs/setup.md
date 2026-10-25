# Reproducible setup

## C++ numerics

GCC with C++17 and Python 3.10+ are sufficient; no downloaded library is needed at runtime.
The optional Dlog–Padé implementation uses the GCC `__float128` extension. Other methods
use standard C++17 `long double`. Use GCC/MinGW for the full test/table workflow.

```sh
make test
make tables
python3 scripts/check_pade.py
```

The last command independently verifies every accepted Padé system with Python exact
rational arithmetic and 80-digit decimal root refinement. It takes longer than the
ordinary synthetic and regression tests. Its recorded result is in
[`audit/pade-oracle.json`](../audit/pade-oracle.json).

## Lean: GitHub Actions only

All Lean compilation, dependency setup, and axiom audits run on the GitHub Actions
runner through [Verify Lean and C++](../.github/workflows/verify.yml). Push a commit
or use the workflow's **Run workflow** button in the repository's **Actions** tab.
Do not install or invoke Lean, Lake, or elan in the local assistant environment.
The local `make lean` target and `scripts/build_lean.py` reject execution outside
GitHub Actions before invoking Lean or changing audit receipts.

The workflow installs elan, selects Lean 4.33.0 from `lean-toolchain`, fetches the
Mathlib revision pinned in `lakefile.toml`, and retrieves precompiled Mathlib.
It then compiles the project and runs `#print axioms` for public project theorems.
Only `propext`, `Classical.choice`, and `Quot.sound` are allowed. The runner rejects
proof escapes and does not use `native_decide`. A source scan alone is not a proof.

Unchanged project modules are reused only from a successful GitHub Actions receipt
for this repository, with matching source, local dependency, toolchain, Mathlib
manifest, runner platform, and compiled-object fingerprints. `Audit.lean` always
reruns. Local receipts cannot authorize CI reuse. Compiler artifacts and the
Mathlib cache are excluded from Git and restored through the Actions cache.

The workflow uploads `proof-and-numerical-receipts`, including the audit log,
status, receipt, and numerical tables. A successful receipt records the repository,
commit, run ID, run URL, compiler, dependency revision, module hashes, and permitted
axioms. Only a completed successful CI run verifies the current repository in this
workflow; earlier local results are historical evidence, not a CI result.

## Windows

Install Python 3 and GCC/MinGW, with `g++` on PATH. No local Lean installation is
needed for the supported Windows entry point.

```cmd
call run.cmd
```

`run.cmd` compiles C++, tests it, and regenerates the front-page tables. It reports
`NUMERICS=PASS` and `LEAN=CI_ONLY`; it never starts a Lean build. The older runner
under `vendor/` is retained only as provenance and must not be invoked locally.

## GitHub automation

The workflow reproduces the C++ tables after its Lean audit. Failed and successful
jobs upload available diagnostics. The numerical executable needs no deployment
or external service at runtime.
