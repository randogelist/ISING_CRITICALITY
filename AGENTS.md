# Project instructions

- Compile and audit Lean only on the GitHub Actions CI runner. Do not invoke
  Lean, Lake, or elan in the local assistant environment, including version
  checks, dependency setup, or proof probes.
- Local source editing, static inspection, and C++/Python numerical work are
  permitted. `run.cmd` is a local numerics-only entry point.
- Run Lean through `.github/workflows/verify.yml`. Reuse compatible cached
  Mathlib and project objects only when the CI receipt and fingerprints match.
- Report CI verification only after inspecting the successful run and its
  audit receipt. Keep conditional physical-identification premises explicit.
- Do not treat an eight-decimal formula certificate as an eight-decimal
  physical critical-threshold certificate.
