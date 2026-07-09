# bala

A Lean 4 / Mathlib formalization checking the proof in *"A Proof of Bala's
Congruence Conjecture for A028342"* (see `main.tex` in the parent directory).

## Status

- **`Bala/Basic.lean`** — defines `a : ℕ → ℤ` via the paper's recurrence
  (footnote before Section 2); checked against the paper's stated values
  `1, 1, 3, 11, 59, 339, 2629, ...`.
- **`Bala/MainTheorem.lean`** — Sections 3 and 5 of the paper (the reduction
  lemma and the Chinese-remainder-theorem assembly of the three-case main
  theorem), fully proved from the two propositions below. Zero `sorry`.
- **`Bala/ProductCongruence.lean`** — Proposition 2.3 (`prop:product`,
  Section 2), the product congruence `a(n+k) ≡ a(n)·a(k) (mod k)`, proved in
  full via a group-action/orbit-stabilizer argument mirroring the paper.
  Zero `sorry`.
- **`Bala/Statements.lean`** — Proposition 4.2 (`prop:primepower`,
  Section 4, the prime-power residues), stated as `axiom`s. This part
  (block-cycle decomposition + exponential formula + lifting-the-exponent /
  Legendre's-formula valuation bounds) was **not** formalized; it was instead
  hand-verified against known number-theoretic identities and checked
  numerically (see `Bala/NumericCheck.lean`) with no counterexamples found.
- **`Bala/NumericCheck.lean`** — an independent numerical stress test of
  every claim in the paper (main theorem, product congruence, both
  prime-power cases) over a range wider than the paper's own footnote check.

Run `lake build` (after `lake exe cache get` to fetch Mathlib's prebuilt
oleans) to typecheck everything.
