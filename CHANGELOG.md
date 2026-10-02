# Changelog

## 0.1.0-rc5 — 2026-10-02

- Integrated constant-error `O(sqrt(N))` unitary implementation and the complete
  constant-coefficient ODE success and conditional mixed-output guarantee.
- Used the externally compiled correction-2 proof bodies for both extensions;
  omitted the later uncompiled unitary warning cleanup. Only release comments
  and audit placement changed in these files.
- Added both extensions to the default library imports and statement guides;
  collected their 12 strict axiom checks in the existing audit modules, giving
  588 audits in total.
- Retained rc4's `log(1/ε)` Hamiltonian corollaries, original proof modules and
  Lean/Mathlib dependency pins. Unfinished gate-efficient proofs are excluded.
- Packaging and source-equivalence checks are not compiler validation. The
  combined rc5 tree needs `lake build` with exit code zero before release.

## 0.1.0-rc4 — 2026-10-02

- Added Hamiltonian endpoint corollaries using `log(1/ε)` for `0 < ε ≤ 1/2`,
  including spectral-norm and entangled-reference versions.
- Preserved the existing circuit constructions, ODE proofs and dependency pins.
- Updated the statement guide, theorem map and axiom audits. The new corollaries
  require a Lean build before release; no local compilation is claimed.

## 0.1.0-rc3 — 2026-10-01

- Shortened the README and maintainer release instructions.
- Replaced development-history records with a current-release manifest for
  source hashes and audit coverage; simplified the packaging checker.
- Lean sources, checked axiom audits and dependency revisions are unchanged.
