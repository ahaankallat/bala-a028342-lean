import Bala.Basic

/-!
Precise Lean statements of the two combinatorial propositions from `main.tex`
(Proposition `prop:product` in Section 2, and Proposition `prop:primepower` in
Section 4), stated here as `axiom`s so that the purely number-theoretic
assembly of Sections 3 and 5 can be formalized and checked on its own.

`Bala/ProductCongruence.lean` and `Bala/PrimePower.lean` contain attempts to
actually *prove* these (discharging the axioms); see the final report for
which of these succeeded.
-/

/-- Proposition 2.3 (`prop:product`):
`a(n+k) ≡ a(n) a(k) (mod k)` for all `n ≥ 0`, `k ≥ 1`. -/
axiom product_congruence (n k : ℕ) (hk : 1 ≤ k) :
    (k : ℤ) ∣ (a (n + k) - a n * a k)

/-- Proposition 4.2 (`prop:primepower`), odd-prime case:
`a(p^r) ≡ -1 (mod p^r)` for odd prime `p`, `r ≥ 1`. -/
axiom primepower_odd (p r : ℕ) (hp : p.Prime) (hodd : Odd p) (hr : 1 ≤ r) :
    (p ^ r : ℤ) ∣ (a (p ^ r) + 1)

/-- Proposition 4.2, `p = 2`, `r = 1`: `a(2) ≡ 1 (mod 2)`. -/
axiom primepower_two_one : (2 : ℤ) ∣ (a 2 - 1)

/-- Proposition 4.2, `p = 2`, `r = 2`: `a(4) ≡ 3 (mod 4)`. -/
axiom primepower_two_two : (4 : ℤ) ∣ (a 4 - 3)

/-- Proposition 4.2, `p = 2`, `r ≥ 3`: `a(2^r) ≡ 1 (mod 2^r)`. -/
axiom primepower_two_large (r : ℕ) (hr : 3 ≤ r) :
    (2 ^ r : ℤ) ∣ (a (2 ^ r) - 1)
