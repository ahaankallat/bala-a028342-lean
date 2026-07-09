import Bala.Basic

/-!
Independent numerical stress test of every claim in the paper (Theorem
thm:main, Proposition prop:product, Proposition prop:primepower), run
directly against the `a` defined in Bala/Basic.lean (via its recurrence).
This is NOT a proof, but it is an independent re-implementation-and-check
(different code path than whatever the paper's author used) over a wider
range than the paper's own footnote check (k ≤ 40, n ≤ 30).
Each `#eval` below should print `[]` (no counterexamples found).

We precompute one shared table (`tbl`) once and read from it, instead of
calling `a` repeatedly (which is not memoized across separate calls and
would redo O(n) work from scratch each time).
-/

def M : Nat := 145
def tbl : List Int := aList M
def av (i : Nat) : Int := tbl.getD i 0

#eval (List.range 8).map av
-- expect: [1, 1, 3, 11, 59, 339, 2629, 20677]

def N : Nat := 60
def K : Nat := 80

/-- check k ∣ a(n+k)+a(n) [k odd], k ∣ a(n+k)-a(n) [k≡0,2,6 mod 8],
    2(a(n+k)-a(n)) ≡ 0 mod k [k≡4 mod 8] -/
def checkMain : List (Nat × Nat) :=
  ((List.range N).flatMap (fun n =>
    ((List.range K).map (· + 1)).filterMap (fun k =>
      let lhs :=
        if k % 2 = 1 then (av (n + k) + av n) % (k : Int)
        else if k % 8 = 0 ∨ k % 8 = 2 ∨ k % 8 = 6 then (av (n + k) - av n) % (k : Int)
        else 2 * (av (n + k) - av n) % (k : Int)
      if lhs = 0 then none else some (n, k))))

#eval checkMain

/-- check k ∣ a(n+k) - a(n)*a(k) -/
def checkProduct : List (Nat × Nat) :=
  ((List.range N).flatMap (fun n =>
    ((List.range K).map (· + 1)).filterMap (fun k =>
      if (av (n + k) - av n * av k) % (k : Int) = 0 then none else some (n, k))))

#eval checkProduct

/-- odd-prime-power case: a(p^r) ≡ -1 mod p^r, for small odd primes and r
    with p^r bounded (kept within table range) -/
def checkPrimePowerOdd : List (Nat × Nat) :=
  ([3, 5, 7, 11, 13].flatMap (fun p =>
    ([1, 2, 3].filterMap (fun r =>
      let Nn := p ^ r
      if Nn > M then none else
      if (av Nn + 1) % (Nn : Int) = 0 then none else some (p, r)))))

#eval checkPrimePowerOdd

-- p = 2 cases
#eval (av 2 - 1) % 2       -- expect 0
#eval (av 4 - 3) % 4       -- expect 0
#eval ((List.range 4).map (· + 3)).filterMap
  (fun r => let Nn := 2 ^ r
            if Nn > M then none else
            if (av Nn - 1) % (Nn : Int) = 0 then none else some r)
-- expect []
