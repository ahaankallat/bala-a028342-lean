import Bala.Statements

/-!
Target: formalize Section 3 (`sec:reduction`) and Section 5
(`sec:completing`) of `main.tex`, i.e. derive Theorem `thm:main` from the
axioms in `Bala/Statements.lean` (Propositions `prop:product` and
`prop:primepower`). This file should contain NO `sorry` and NO new `axiom`
once complete: it should build `reduction` and `main_theorem` purely by
number-theoretic reasoning (induction, Chinese remainder theorem) from the
three `Statements.lean` axioms.
-/

/-- Lemma 3.1 (`lem:reduction`): for `q ∣ k`, `q ≥ 1`, `k ≥ 1`,
`a(k) ≡ a(q)^(k/q) (mod q)`. -/
theorem reduction (q k : ℕ) (hq : 1 ≤ q) (hdvd : q ∣ k) (hk : 1 ≤ k) :
    (q : ℤ) ∣ (a k - a q ^ (k / q)) := by
  obtain ⟨s, hs⟩ := hdvd
  have hqpos : 0 < q := hq
  have hs1 : 1 ≤ s := by
    rcases Nat.eq_zero_or_pos s with h0 | h1
    · exfalso; rw [h0, Nat.mul_zero] at hs; omega
    · exact h1
  have hkq : k / q = s := by rw [hs, Nat.mul_div_cancel_left s hqpos]
  rw [hkq, hs]
  clear hkq hs hk hqpos
  induction s, hs1 using Nat.le_induction with
  | base => simp
  | succ s hs1 ih =>
    have hpc := product_congruence (q * s) q hq
    have heq : a (q * (s + 1)) - a q ^ (s + 1)
        = (a (q * s + q) - a (q * s) * a q) + a q * (a (q * s) - a q ^ s) := by
      have : q * (s + 1) = q * s + q := by ring
      rw [this]; ring
    rw [heq]
    exact dvd_add hpc (Dvd.dvd.mul_left ih (a q))

/-- Variant of `reduction` with the base case of the power replaced by an
arbitrary `y` congruent to `a q` modulo `q`: if `a q ≡ y (mod q)` then
`a k ≡ y^(k/q) (mod q)`. This is the form actually used in Section 5, since
there `a q` is replaced by its known residue (`-1`, `1`, or `3`). -/
theorem reduction_pow (q k : ℕ) (hq : 1 ≤ q) (hdvd : q ∣ k) (hk : 1 ≤ k) (y : ℤ)
    (hy : (q : ℤ) ∣ (a q - y)) :
    (q : ℤ) ∣ (a k - y ^ (k / q)) := by
  have h1 := reduction q k hq hdvd hk
  have h2 : (a q - y) ∣ (a q ^ (k / q) - y ^ (k / q)) := sub_dvd_pow_sub_pow (a q) y (k / q)
  have h3 : (q : ℤ) ∣ (a q ^ (k / q) - y ^ (k / q)) := hy.trans h2
  have heq : a k - y ^ (k / q) = (a k - a q ^ (k / q)) + (a q ^ (k / q) - y ^ (k / q)) := by ring
  rw [heq]
  exact dvd_add h1 h3

/-- Chinese-remainder-theorem combination lemma: if `x ≡ y` modulo `p^e` for
every maximal prime-power divisor `p^e` of `k`, then `x ≡ y` modulo `k`. This
packages the "Chinese remainder theorem" step used repeatedly in Section 5. -/
theorem combine_prime_powers (x y : ℤ) :
    ∀ k : ℕ, 1 ≤ k →
      (∀ p : ℕ, p.Prime → p ∣ k → (p ^ (k.factorization p) : ℤ) ∣ (x - y)) →
      (k : ℤ) ∣ (x - y) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk h
    rcases eq_or_lt_of_le hk with h1 | h1
    · rw [← h1]; norm_num
    · have hkne0 : k ≠ 0 := by omega
      have hkne1 : k ≠ 1 := by omega
      obtain ⟨p, pp, pdvd⟩ := Nat.exists_prime_and_dvd hkne1
      set e := k.factorization p with hedef
      have he1 : 1 ≤ e := Nat.Prime.factorization_pos_of_dvd pp hkne0 pdvd
      set k' := ordCompl[p] k with hk'def
      have hkey : p ^ e * k' = k := Nat.ordProj_mul_ordCompl_eq_self k p
      have hk'pos : 0 < k' := Nat.ordCompl_pos p hkne0
      have hpe2 : 2 ≤ p ^ e := by
        calc 2 ≤ p := pp.two_le
          _ ≤ p ^ e := Nat.le_self_pow (by omega) p
      have hk'lt : k' < k := by nlinarith [hkey, hpe2, hk'pos]
      have hcop : Nat.Coprime (p ^ e) k' := (Nat.coprime_ordCompl pp hkne0).pow_left e
      have hk'div : (k' : ℤ) ∣ (x - y) := by
        apply ih k' hk'lt hk'pos
        intro q qp qdvd
        have hqp : q ≠ p := by
          intro hcontra
          rw [hcontra] at qdvd
          exact (Nat.not_dvd_ordCompl pp hkne0) qdvd
        have hfeq : k'.factorization q = k.factorization q := by
          rw [hk'def, Nat.factorization_ordCompl]
          exact Finsupp.erase_ne hqp
        rw [hfeq]
        exact h q qp (qdvd.trans (Nat.ordCompl_dvd k p))
      have hpe : ((p : ℤ) ^ e) ∣ (x - y) := h p pp pdvd
      have hcopZ : IsCoprime ((p : ℤ) ^ e) (k' : ℤ) := by
        have hc := hcop.cast (R := ℤ)
        push_cast at hc
        exact hc
      have hkeyZ : (p : ℤ) ^ e * (k' : ℤ) = (k : ℤ) := by
        have := congrArg (fun n : ℕ => (n : ℤ)) hkey
        push_cast at this
        exact this
      have := hcopZ.mul_dvd hpe hk'div
      rwa [hkeyZ] at this

/-- Theorem `thm:main`, the paper's main result, stated exactly as in the
paper (three cases according to `k mod 8`, matching the `\begin{cases}` in
`main.tex`). -/
theorem main_theorem (n k : ℕ) (hk : 1 ≤ k) :
    (Odd k → (k : ℤ) ∣ (a (n + k) + a n)) ∧
    ((k % 8 = 0 ∨ k % 8 = 2 ∨ k % 8 = 6) → (k : ℤ) ∣ (a (n + k) - a n)) ∧
    (k % 8 = 4 → (k : ℤ) ∣ 2 * (a (n + k) - a n)) := by
  have hkne0 : k ≠ 0 := by omega
  refine ⟨?_, ?_, ?_⟩
  · -- Case 1: k odd.  Show a(k) ≡ -1 (mod k), then combine with the product
    -- congruence to get a(n+k) ≡ -a(n) (mod k).
    intro hodd
    have hak : (k : ℤ) ∣ (a k - (-1)) := by
      apply combine_prime_powers (a k) (-1) k hk
      intro p pp pdvd
      have he1 : 1 ≤ k.factorization p := Nat.Prime.factorization_pos_of_dvd pp hkne0 pdvd
      set e := k.factorization p with hedef
      set q := p ^ e with hqdef
      have hqZ : (p : ℤ) ^ e = (q : ℤ) := by rw [hqdef]; push_cast; ring
      rw [hqZ]
      have hqdvd : q ∣ k := Nat.ordProj_dvd k p
      have hqpos : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero e pp.pos.ne')
      -- p is odd, since p ∣ k and k is odd
      have hp2 : p ≠ 2 := by
        intro he
        rw [he] at pdvd
        obtain ⟨c, hc⟩ := hodd
        obtain ⟨d, hd⟩ := pdvd
        omega
      have hpodd : Odd p := pp.odd_of_ne_two hp2
      -- k / q is odd, since q ∣ k and k is odd
      have hqodd : Odd q := hqdef ▸ hpodd.pow
      have hmodd : Odd (k / q) := by
        by_contra hcontra
        rw [← Nat.not_even_iff_odd, not_not] at hcontra
        have : Even (q * (k / q)) := hcontra.mul_left q
        rw [Nat.mul_div_cancel' hqdvd] at this
        exact (Nat.not_even_iff_odd.mpr hodd) this
      have hpp : (q : ℤ) ∣ (a q + 1) := by
        have := primepower_odd p e pp hpodd he1
        rwa [← hqdef] at this
      have hstep := reduction_pow q k hqpos hqdvd hk (-1) (by simpa using hpp)
      rwa [Odd.neg_one_pow hmodd] at hstep
    have hpc := product_congruence n k hk
    have heq : a (n + k) + a n = (a (n + k) - a n * a k) + a n * (a k - (-1)) := by ring
    rw [heq]
    exact dvd_add hpc (Dvd.dvd.mul_left hak (a n))
  · -- Case 2: k ≡ 0, 2, 6 (mod 8).  Show a(k) ≡ 1 (mod k).
    intro h8
    have hkeven : k % 2 = 0 := by omega
    have hak : (k : ℤ) ∣ (a k - 1) := by
      apply combine_prime_powers (a k) 1 k hk
      intro p pp pdvd
      have he1 : 1 ≤ k.factorization p := Nat.Prime.factorization_pos_of_dvd pp hkne0 pdvd
      set e := k.factorization p with hedef
      set q := p ^ e with hqdef
      have hqZ : (p : ℤ) ^ e = (q : ℤ) := by rw [hqdef]; push_cast; ring
      rw [hqZ]
      have hqdvd : q ∣ k := Nat.ordProj_dvd k p
      have hqpos : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero e pp.pos.ne')
      by_cases hp2 : p = 2
      · -- the 2-part of k: either q = 2 (α = 1) or q = 2^α, α ≥ 3
        subst hp2
        have hcase : e = 1 ∨ 3 ≤ e := by
          rcases h8 with h0 | h2 | h6
          · right
            have h8dvd : (2 : ℕ) ^ 3 ∣ k := by
              refine ⟨k / 8, ?_⟩; omega
            exact (pp.pow_dvd_iff_le_factorization hkne0).mp h8dvd
          · left
            have hn4 : ¬ (2 : ℕ) ^ 2 ∣ k := by
              rintro ⟨c, hc⟩; omega
            have h2le : ¬ (2 ≤ e) := fun hh =>
              hn4 ((pp.pow_dvd_iff_le_factorization hkne0).mpr hh)
            omega
          · left
            have hn4 : ¬ (2 : ℕ) ^ 2 ∣ k := by
              rintro ⟨c, hc⟩; omega
            have h2le : ¬ (2 ≤ e) := fun hh =>
              hn4 ((pp.pow_dvd_iff_le_factorization hkne0).mpr hh)
            omega
        have hprim : (q : ℤ) ∣ (a q - 1) := by
          rcases hcase with he | he
          · rw [hqdef, he]
            simpa using primepower_two_one
          · have := primepower_two_large e he
            rwa [← hqdef] at this
        have hstep := reduction_pow q k hqpos hqdvd hk 1 hprim
        simpa using hstep
      · -- an odd prime-power factor of k
        have hpodd : Odd p := pp.odd_of_ne_two hp2
        have hqodd : Odd q := hqdef ▸ hpodd.pow
        have hmeven : Even (k / q) := by
          by_contra hcontra
          have hcontra' : Odd (k / q) := Nat.not_even_iff_odd.mp hcontra
          have : Odd (q * (k / q)) := hqodd.mul hcontra'
          rw [Nat.mul_div_cancel' hqdvd] at this
          rw [Nat.odd_iff] at this
          omega
        have hpp : (q : ℤ) ∣ (a q + 1) := by
          have := primepower_odd p e pp hpodd he1
          rwa [← hqdef] at this
        have hstep := reduction_pow q k hqpos hqdvd hk (-1) (by simpa using hpp)
        rwa [Even.neg_one_pow hmeven] at hstep
    have hpc := product_congruence n k hk
    have heq : a (n + k) - a n = (a (n + k) - a n * a k) + a n * (a k - 1) := by ring
    rw [heq]
    exact dvd_add hpc (Dvd.dvd.mul_left hak (a n))
  · -- Case 3: k ≡ 4 (mod 8).  Show a(k) ≡ 1 + k/2 (mod k).
    intro h4
    have hkeven : k % 2 = 0 := by omega
    set k2 := k / 2 with hk2def
    have hk2eq : 2 * k2 = k := by rw [hk2def]; omega
    have hak : (k : ℤ) ∣ (a k - (1 + (k2 : ℤ))) := by
      apply combine_prime_powers (a k) (1 + (k2 : ℤ)) k hk
      intro p pp pdvd
      have he1 : 1 ≤ k.factorization p := Nat.Prime.factorization_pos_of_dvd pp hkne0 pdvd
      set e := k.factorization p with hedef
      set q := p ^ e with hqdef
      have hqZ : (p : ℤ) ^ e = (q : ℤ) := by rw [hqdef]; push_cast; ring
      rw [hqZ]
      have hqdvd : q ∣ k := Nat.ordProj_dvd k p
      have hqpos : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero e pp.pos.ne')
      by_cases hp2 : p = 2
      · -- the 2-part of k is exactly 4, since k ≡ 4 (mod 8)
        subst hp2
        have he2 : e = 2 := by
          have h4dvd : (2 : ℕ) ^ 2 ∣ k := by refine ⟨k / 4, ?_⟩; omega
          have h8ndvd : ¬ (2 : ℕ) ^ 3 ∣ k := by rintro ⟨c, hc⟩; omega
          have hge : 2 ≤ e := (pp.pow_dvd_iff_le_factorization hkne0).mp h4dvd
          have hlt : ¬ (3 ≤ e) := fun hh =>
            h8ndvd ((pp.pow_dvd_iff_le_factorization hkne0).mpr hh)
          omega
        have hq4 : q = 4 := by rw [hqdef, he2]; norm_num
        rw [hq4]
        have hmodd : Odd (k / q) := by
          rw [hq4]
          rw [Nat.odd_iff]
          omega
        obtain ⟨mm, hmm⟩ := hmodd
        have hmm4 : k / 4 = 2 * mm + 1 := by rw [← hq4]; exact hmm
        have hkval : k = 4 * (2 * mm + 1) := by
          have := Nat.div_add_mod k 4
          omega
        have hk2val : k2 = 4 * mm + 2 := by omega
        -- a(k) ≡ a(4)^m ≡ 3^m ≡ 3 (mod 4), and 3 ≡ 1 + k2 (mod 4), where m = 2mm+1 = k/4
        have hprim34 : (4 : ℤ) ∣ (a 4 - 3) := primepower_two_two
        have hstep1 := reduction_pow q k hqpos hqdvd hk 3 (by rw [hq4]; simpa using hprim34)
        rw [hq4, hmm4] at hstep1
        -- hstep1 : (4 : ℤ) ∣ (a k - 3 ^ (2 * mm + 1))
        -- 3^m ≡ (-1)^m ≡ -1 (mod 4), since 3 - (-1) = 4 and m is odd
        have h3m : (4 : ℤ) ∣ (3 ^ (2 * mm + 1) - (-1) ^ (2 * mm + 1)) := by
          have h40 : (4 : ℤ) ∣ ((3 : ℤ) - (-1)) := by norm_num
          exact h40.trans (sub_dvd_pow_sub_pow 3 (-1) (2 * mm + 1))
        rw [Odd.neg_one_pow ⟨mm, rfl⟩] at h3m
        -- h3m : (4 : ℤ) ∣ (3 ^ (2 * mm + 1) - (-1))
        -- combine to get 4 ∣ (a k - (1 + k2)), using k2 = 4*mm + 2
        have heq : a k - (1 + (k2 : ℤ))
            = (a k - 3 ^ (2 * mm + 1)) + (3 ^ (2 * mm + 1) - (-1)) + (-4 * (mm : ℤ) - 4) := by
          have hk2Z : (k2 : ℤ) = 4 * (mm : ℤ) + 2 := by
            rw [hk2val]; push_cast; ring
          rw [hk2Z]; ring
        rw [heq]
        refine dvd_add (dvd_add hstep1 h3m) ?_
        exact ⟨-(mm : ℤ) - 1, by ring⟩
      · -- an odd prime-power factor of the odd part of k
        have hpodd : Odd p := pp.odd_of_ne_two hp2
        have hqodd : Odd q := hqdef ▸ hpodd.pow
        have hmeven : Even (k / q) := by
          by_contra hcontra
          have hcontra' : Odd (k / q) := Nat.not_even_iff_odd.mp hcontra
          have : Odd (q * (k / q)) := hqodd.mul hcontra'
          rw [Nat.mul_div_cancel' hqdvd] at this
          rw [Nat.odd_iff] at this
          omega
        have hpp : (q : ℤ) ∣ (a q + 1) := by
          have := primepower_odd p e pp hpodd he1
          rwa [← hqdef] at this
        have hstep := reduction_pow q k hqpos hqdvd hk (-1) (by simpa using hpp)
        rw [Even.neg_one_pow hmeven] at hstep
        -- hstep : q ∣ (a k - 1).  Also q ∣ k2, since q is odd and q ∣ k = 2 * k2.
        have hq2cop : Nat.Coprime q 2 := by
          rw [hqdef]
          exact (Nat.coprime_primes pp Nat.prime_two).mpr hp2 |>.pow_left e
        have hqk2 : q ∣ k2 := (Nat.Coprime.dvd_mul_left hq2cop).mp (hk2eq ▸ hqdvd)
        have hqk2Z : (q : ℤ) ∣ (k2 : ℤ) := Int.natCast_dvd_natCast.mpr hqk2
        have heq : a k - (1 + (k2 : ℤ)) = (a k - 1) - (k2 : ℤ) := by ring
        rw [heq]
        exact dvd_sub hstep hqk2Z
    have hpc := product_congruence n k hk
    have heq : 2 * (a (n + k) - a n)
        = 2 * (a (n + k) - a n * a k) + 2 * a n * (a k - (1 + (k2 : ℤ))) + (k : ℤ) * a n := by
      have hkZ : (k : ℤ) = 2 * (k2 : ℤ) := by rw [← hk2eq]; push_cast; ring
      rw [hkZ]; ring
    rw [heq]
    refine dvd_add (dvd_add ?_ ?_) ?_
    · exact Dvd.dvd.mul_left hpc 2
    · exact Dvd.dvd.mul_left hak (2 * a n)
    · exact Dvd.dvd.mul_right (dvd_refl (k : ℤ)) (a n)
