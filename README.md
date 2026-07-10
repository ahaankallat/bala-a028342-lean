# Bala A028342 Lean

A complete Lean 4 / Mathlib formalization of *"A Proof of Bala's Congruence
Conjecture for A028342"* (see `main.tex` in the parent directory).

## Status: fully verified, zero `sorry`, zero paper-specific axioms

Every proposition, lemma, and the main theorem itself is proved. The final
top-level result:

```lean
theorem main_theorem (n k : ℕ) (hk : 1 ≤ k) :
    (Odd k → (k : ℤ) ∣ (a (n + k) + a n)) ∧
    ((k % 8 = 0 ∨ k % 8 = 2 ∨ k % 8 = 6) → (k : ℤ) ∣ (a (n + k) - a n)) ∧
    (k % 8 = 4 → (k : ℤ) ∣ 2 * (a (n + k) - a n))
```

`#print axioms main_theorem` reports only `[propext, Classical.choice,
Quot.sound]` — Lean/Mathlib's standard foundational axioms, nothing specific
to this paper.

## File-by-file breakdown

- **`Bala/Basic.lean`** — defines `a : ℕ → ℤ` via the paper's recurrence
  (footnote before Section 2); checked against the paper's stated values
  `1, 1, 3, 11, 59, 339, 2629, ...`.
- **`Bala/ProductCongruence.lean`** — Proposition 2.3 (`prop:product`,
  Section 2), `a(n+k) ≡ a(n)·a(k) (mod k)`, proved via a group-action /
  orbit-stabilizer argument on colored permutations mirroring the paper
  exactly, plus a from-scratch "exponential formula" bijection identifying
  the combinatorial definition with the recurrence. Zero `sorry`.
- **`Bala/PrimePower.lean`** — Proposition 4.2 (`prop:primepower`,
  Section 4), the prime-power residues (`a(p^r) ≡ -1 mod p^r` for odd `p`;
  `a(2)≡1 mod 2`, `a(4)≡3 mod 4`, `a(2^r)≡1 mod 2^r` for `r≥3`). This is the
  hardest part of the paper: a two-level group-action argument (blocks under
  a subgroup `H`, then block-cycles), an exponential-formula identity for
  the block-cycle weights, and p-adic valuation bounds (lifting-the-exponent,
  Legendre's formula). Fully proved, zero `sorry`.
- **`Bala/MainTheorem.lean`** — Sections 3 and 5 of the paper (the reduction
  lemma and the Chinese-remainder-theorem assembly of the three-case main
  theorem), derived from `Bala/Statements.lean`'s axioms. Zero `sorry`.
- **`Bala/Statements.lean`** — precise statements of Propositions 2.3 and
  4.2, declared as `axiom`s so Sections 3/5 could be formalized and checked
  independently of Sections 2/4. (Superseded by `Bala/Complete.lean` below.)
- **`Bala/Complete.lean`** — the final assembly: re-derives `main_theorem`
  using the *proved* theorems from `ProductCongruence.lean`/`PrimePower.lean`
  in place of the `Statements.lean` axioms, giving a single, fully
  self-contained, unconditional proof.
- **`Bala/NumericCheck.lean`** — an independent numerical stress test of
  every claim in the paper over a range wider than the paper's own footnote
  check (n ≤ 59, k ≤ 80 vs. the paper's n ≤ 30, k ≤ 40).
- **`Bala/AxiomCheck.lean`** — `#print axioms` audit of the key theorems.

Run `lake build` (after `lake exe cache get` to fetch Mathlib's prebuilt
oleans) to typecheck everything.
