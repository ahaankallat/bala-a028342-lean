import Mathlib

/-
Formal verification (in progress) of:
  "A Proof of Bala's Congruence Conjecture for A028342" (main.tex)

Step 0: define a(n) via the paper's recurrence (footnote before Section 2)
  a(n) = sum_{m=1}^n C(n-1,m-1) (m-1)! d(m) a(n-m),  a(0) = 1
and sanity-check it against the stated values 1, 1, 3, 11, 59, 339, 2629, ...
We take this as the *definition* of `a`, since it is elementary to encode and
is the formula the paper itself uses to generate data (footnote 1). The paper
also gives a combinatorial description (colored permutations, eq:combdef) and
an EGF (eq:egf); those are equivalent to this recurrence by the paper's own
argument (standard EGF-to-recurrence differentiation), which we do not
re-derive here.
-/

/-- number of positive divisors of `m` -/
def numDivisors (m : Nat) : Nat :=
  ((List.range m).map (· + 1)).countP (fun d => m % d == 0)

/-- `aList n = [a 0, a 1, ..., a n]`, built by structural recursion so no
    well-founded-recursion / termination proof is needed: each entry only
    ever reads earlier entries of the *already computed* list `prev`. -/
def aList : Nat → List Int
  | 0 => [1]
  | n + 1 =>
    let prev := aList n
    let n1 := n + 1
    let val : Int :=
      ((List.range n1).map (· + 1)).foldl
        (fun acc m =>
          acc + (Nat.choose n (m - 1) : Int) * (Nat.factorial (m - 1) : Int)
              * (numDivisors m : Int) * prev.getD (n1 - m) 0)
        0
    prev ++ [val]

/-- `a n` is the paper's sequence A028342. -/
def a (n : Nat) : Int := (aList n).getD n 0

#eval (List.range 8).map a
-- expect: [1, 1, 3, 11, 59, 339, 2629, ...] (paper, line "a(0),a(1),... = ...")
