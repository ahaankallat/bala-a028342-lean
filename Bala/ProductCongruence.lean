import Bala.Statements

/-!
# Proposition 2.3 (`prop:product`): the product congruence `a(n+k) ≡ a(n) a(k) (mod k)`

This file formalizes the paper's own proof (Section 2 of `main.tex`): count "colored
permutations" (a permutation together with, for each cycle, a choice of a divisor of that
cycle's length), split them into "unmixed" (every cycle lies wholly in a distinguished
`n`-subset or wholly in the complementary `k`-subset) and "mixed" objects, and show the mixed
count is `≡ 0 (mod k)` via a free action of the cyclic group of order `k` (rotating the `k`-part)
combined with orbit-stabilizer. A second, independent piece of combinatorics (the "exponential
formula" / cycle-of-a-point decomposition of `permSum`) identifies this permutation-sum count
with the paper's sequence `a`.

The whole file is now complete: `product_congruence'` at the bottom is fully proved (no
`sorry`), depending only on the standard axioms `[propext, Classical.choice, Quot.sound]`
(checked via `#print axioms product_congruence'`).

See the bottom of the file for the overall status / a full account of what was proved.
-/

noncomputable section

open Equiv Equiv.Perm

/-- The "weight" of a permutation: for each cycle, the number of divisors of the cycle's
length, multiplied together. Summing this over all permutations of an `n`-element type counts
"colored permutations" (Definition `def:objects` of the paper) of that type. -/
def permWeight {α : Type*} [Fintype α] [DecidableEq α] (σ : Equiv.Perm α) : ℤ :=
  (σ.cycleType.map (fun c => (numDivisors c : ℤ))).prod

/-- The total count of colored permutations of `α` (a stand-in for `a (Fintype.card α)`,
proved equal to it below). -/
def permSum (α : Type*) [Fintype α] [DecidableEq α] : ℤ :=
  ∑ σ : Equiv.Perm α, permWeight σ

/-- `permWeight` is a conjugacy invariant, since `cycleType` is. -/
theorem permWeight_conj {α : Type*} [Fintype α] [DecidableEq α] (σ τ : Equiv.Perm α) :
    permWeight (τ * σ * τ⁻¹) = permWeight σ := by
  unfold permWeight
  rw [Equiv.Perm.cycleType_conj]

/-! ### Additivity of `cycleType` (hence multiplicativity of `permWeight`) over `sumCongr` -/

theorem cycleType_sumCongr_left {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] (σ : Equiv.Perm α) :
    (Equiv.Perm.sumCongr σ (1 : Equiv.Perm β)).cycleType = σ.cycleType := by
  classical
  let f : α ≃ Subtype (fun x : α ⊕ β => x ∈ Set.range (Sum.inl : α → α ⊕ β)) :=
    Equiv.ofInjective Sum.inl Sum.inl_injective
  have hf : ∀ a : α, (f a : α ⊕ β) = Sum.inl a := fun a => by simp [f]
  have hext : Equiv.Perm.sumCongr σ (1 : Equiv.Perm β) = σ.extendDomain f := by
    ext x
    cases x with
    | inl a =>
      have h2 := Equiv.Perm.extendDomain_apply_image σ f a
      rw [hf a] at h2
      rw [h2, Equiv.Perm.sumCongr_apply, Sum.map_inl, hf (σ a)]
    | inr b =>
      have hb : (Sum.inr b : α ⊕ β) ∉ Set.range (Sum.inl : α → α ⊕ β) := by simp
      rw [Equiv.Perm.extendDomain_apply_not_subtype σ f hb, Equiv.Perm.sumCongr_apply,
        Sum.map_inr, Equiv.Perm.one_apply]
  rw [hext, Equiv.Perm.cycleType_extendDomain]

theorem cycleType_sumCongr_right {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] (τ : Equiv.Perm β) :
    (Equiv.Perm.sumCongr (1 : Equiv.Perm α) τ).cycleType = τ.cycleType := by
  classical
  let f : β ≃ Subtype (fun x : α ⊕ β => x ∈ Set.range (Sum.inr : β → α ⊕ β)) :=
    Equiv.ofInjective Sum.inr Sum.inr_injective
  have hf : ∀ b : β, (f b : α ⊕ β) = Sum.inr b := fun b => by simp [f]
  have hext : Equiv.Perm.sumCongr (1 : Equiv.Perm α) τ = τ.extendDomain f := by
    ext x
    cases x with
    | inr b =>
      have h2 := Equiv.Perm.extendDomain_apply_image τ f b
      rw [hf b] at h2
      rw [h2, Equiv.Perm.sumCongr_apply, Sum.map_inr, hf (τ b)]
    | inl a =>
      have ha : (Sum.inl a : α ⊕ β) ∉ Set.range (Sum.inr : β → α ⊕ β) := by simp
      rw [Equiv.Perm.extendDomain_apply_not_subtype τ f ha, Equiv.Perm.sumCongr_apply,
        Sum.map_inl, Equiv.Perm.one_apply]
  rw [hext, Equiv.Perm.cycleType_extendDomain]

theorem Disjoint.sumCongr_left_right {α β : Type*} (σ : Equiv.Perm α) (τ : Equiv.Perm β) :
    Equiv.Perm.Disjoint (Equiv.Perm.sumCongr σ (1 : Equiv.Perm β))
      (Equiv.Perm.sumCongr (1 : Equiv.Perm α) τ) := by
  intro x
  cases x with
  | inl a => right; simp
  | inr b => left; simp

theorem cycleType_sumCongr {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (σ : Equiv.Perm α) (τ : Equiv.Perm β) :
    (Equiv.Perm.sumCongr σ τ).cycleType = σ.cycleType + τ.cycleType := by
  have hmul : Equiv.Perm.sumCongr σ τ =
      Equiv.Perm.sumCongr σ (1 : Equiv.Perm β) * Equiv.Perm.sumCongr (1 : Equiv.Perm α) τ := by
    rw [Equiv.Perm.sumCongr_mul, mul_one, one_mul]
  rw [hmul, (Disjoint.sumCongr_left_right σ τ).cycleType_mul, cycleType_sumCongr_left,
    cycleType_sumCongr_right]

theorem permWeight_sumCongr {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (σ : Equiv.Perm α) (τ : Equiv.Perm β) :
    permWeight (Equiv.Perm.sumCongr σ τ) = permWeight σ * permWeight τ := by
  unfold permWeight
  rw [cycleType_sumCongr, Multiset.map_add, Multiset.prod_add]

/-! ### The unmixed/mixed split -/

/-- `σ : Perm (α ⊕ β)` is *unmixed* if it maps the `α`-part into itself (equivalently, since it
is a bijection on a finite type, onto itself; and equivalently, by
`perm_mapsTo_inl_iff_mapsTo_inr`, iff it maps the `β`-part into itself). This matches the paper's
notion (Definition `def:objects`): every cycle lies wholly in `α` or wholly in `β`. -/
def Unmixed (α β : Type*) [Fintype α] [Fintype β] : Set (Equiv.Perm (α ⊕ β)) :=
  {σ | Set.MapsTo σ (Set.range (Sum.inl : α → α ⊕ β)) (Set.range (Sum.inl : α → α ⊕ β))}

open Classical in
/-- A more computation-friendly reformulation of `Unmixed`, avoiding `Set.MapsTo`'s
strict-implicit binder. -/
theorem mem_Unmixed_iff {α β : Type*} [Fintype α] [Fintype β] (σ : Equiv.Perm (α ⊕ β)) :
    σ ∈ Unmixed α β ↔ ∀ a : α, ∃ a', σ (Sum.inl a) = Sum.inl a' := by
  unfold Unmixed Set.MapsTo
  constructor
  · intro h a
    obtain ⟨a', ha'⟩ := h (Set.mem_range_self a)
    exact ⟨a', ha'.symm⟩
  · intro h x hx
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨a', ha'⟩ := h a
    exact ⟨a', ha'.symm⟩

open Classical in
theorem sum_unmixed (α β : Type*) [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] :
    ∑ σ ∈ Finset.univ.filter (fun σ => σ ∈ Unmixed α β), permWeight σ
      = permSum α * permSum β := by
  have hset : (Finset.univ.filter (fun σ : Equiv.Perm (α ⊕ β) => σ ∈ Unmixed α β))
      = Finset.image (Equiv.Perm.sumCongrHom α β) Finset.univ := by
    ext σ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hσ
      obtain ⟨p, hp⟩ := Equiv.Perm.mem_sumCongrHom_range_of_perm_mapsTo_inl hσ
      exact ⟨p, hp⟩
    · rintro ⟨⟨σ1, σ2⟩, -, rfl⟩
      intro x hx
      obtain ⟨a, rfl⟩ := hx
      rw [Equiv.Perm.sumCongrHom_apply, Equiv.Perm.sumCongr_apply, Sum.map_inl]
      exact Set.mem_range_self (σ1 a)
  rw [hset, Finset.sum_image (fun p _ q _ h => Equiv.Perm.sumCongrHom_injective h)]
  simp only [Equiv.Perm.sumCongrHom_apply, permWeight_sumCongr, Fintype.sum_prod_type]
  unfold permSum
  rw [Finset.sum_mul_sum]

/-! ### A generic "free action ⇒ divisibility of a weighted sum" lemma

This is the group-theoretic engine behind the mixed-object argument (the orbit-stabilizer part
of the paper's proof): if a finite additive group `G` acts on `X`, `w : X → ℤ` is invariant under
the action, `S` is a `G`-invariant finite set, and every point of `S` has trivial stabilizer,
then `|G|` divides `∑ x ∈ S, w x`.

We avoid Mathlib's `MulAction`/quotient machinery for this and instead give a direct proof by
strong induction on `S.card`, peeling off one free orbit (of size exactly `|G|`, all of whose
points have the same `w`-value) at a time. -/
theorem dvd_sum_of_free_action {G X : Type*} [AddCommGroup G] [Fintype G]
    [AddAction G X] (w : X → ℤ) (hw : ∀ (g : G) (x : X), w (g +ᵥ x) = w x) (S : Finset X)
    (hSinv : ∀ (g : G) (x : X), x ∈ S → g +ᵥ x ∈ S)
    (hfree : ∀ x ∈ S, ∀ g : G, g +ᵥ x = x → g = 0) :
    (Fintype.card G : ℤ) ∣ ∑ x ∈ S, w x := by
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    rcases S.eq_empty_or_nonempty with hS | ⟨x₀, hx₀⟩
    · simp [hS]
    · classical
      set O : Finset X := Finset.image (fun g : G => g +ᵥ x₀) Finset.univ with hOdef
      have hOself : ∀ (g : G) (y : X), y ∈ O → g +ᵥ y ∈ O := by
        intro g y hy
        simp only [hOdef, Finset.mem_image, Finset.mem_univ, true_and] at hy ⊢
        obtain ⟨g', rfl⟩ := hy
        exact ⟨g + g', add_vadd g g' x₀⟩
      have hOsub : O ⊆ S := by
        intro y hy
        simp only [hOdef, Finset.mem_image, Finset.mem_univ, true_and] at hy
        obtain ⟨g, rfl⟩ := hy
        exact hSinv g x₀ hx₀
      have hinj : Function.Injective (fun g : G => g +ᵥ x₀) := by
        intro g1 g2 h
        simp only at h
        have hz : (g1 - g2) +ᵥ x₀ = x₀ := by
          have e1 : (g1 - g2) +ᵥ x₀ = (-g2) +ᵥ (g1 +ᵥ x₀) := by
            rw [← add_vadd]; congr 1; abel
          rw [e1, h, ← add_vadd]
          simp
        have h0 := hfree x₀ hx₀ (g1 - g2) hz
        exact sub_eq_zero.mp h0
      have hOcard : O.card = Fintype.card G := Finset.card_image_of_injective _ hinj
      have hOsum : ∑ y ∈ O, w y = (Fintype.card G : ℤ) * w x₀ := by
        rw [hOdef, Finset.sum_image (fun g1 _ g2 _ h => hinj h)]
        simp only [hw]
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      set S' : Finset X := S \ O with hS'def
      have hS'inv : ∀ (g : G) (x : X), x ∈ S' → g +ᵥ x ∈ S' := by
        intro g x hx
        simp only [hS'def, Finset.mem_sdiff] at hx ⊢
        obtain ⟨hxS, hxO⟩ := hx
        refine ⟨hSinv g x hxS, fun hcontra => hxO ?_⟩
        have : (-g) +ᵥ (g +ᵥ x) ∈ O := hOself (-g) _ hcontra
        rwa [← add_vadd, neg_add_cancel, zero_vadd] at this
      have hS'free : ∀ x ∈ S', ∀ g : G, g +ᵥ x = x → g = 0 :=
        fun x hx => hfree x (Finset.mem_sdiff.mp hx).1
      have hSSub : S' ⊂ S := by
        have hOne : O.Nonempty :=
          ⟨x₀, by simp only [hOdef, Finset.mem_image, Finset.mem_univ, true_and]
                  exact ⟨0, zero_vadd G x₀⟩⟩
        exact Finset.sdiff_ssubset hOsub hOne
      have hdvdS' : (Fintype.card G : ℤ) ∣ ∑ x ∈ S', w x := ih S' hSSub hS'inv hS'free
      have hsplit : ∑ x ∈ S, w x = ∑ x ∈ O, w x + ∑ x ∈ S', w x := by
        rw [hS'def, add_comm]
        exact (Finset.sum_sdiff hOsub).symm
      rw [hsplit, hOsum]
      exact Dvd.dvd.add ⟨w x₀, rfl⟩ hdvdS'

/-! ### `permSum` only depends on the cardinality of the index type -/

open Classical in
theorem cycleType_permCongr {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (e : α ≃ β) (σ : Equiv.Perm α) : (e.permCongr σ).cycleType = σ.cycleType := by
  let f : α ≃ Subtype (fun _ : β => True) := e.trans (Equiv.Set.univ β).symm
  have hext : e.permCongr σ = σ.extendDomain f := by
    ext x
    have hp : (fun _ : β => True) x := trivial
    rw [Equiv.Perm.extendDomain_apply_subtype σ f hp, Equiv.permCongr_apply]
    congr 2
  rw [hext, Equiv.Perm.cycleType_extendDomain]

theorem permWeight_permCongr {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (e : α ≃ β) (σ : Equiv.Perm α) : permWeight (e.permCongr σ) = permWeight σ := by
  unfold permWeight
  rw [cycleType_permCongr]

theorem permSum_congr {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (e : α ≃ β) : permSum α = permSum β := by
  unfold permSum
  rw [Finset.sum_congr rfl (fun σ (_ : σ ∈ Finset.univ) => (permWeight_permCongr e σ).symm)]
  exact Equiv.sum_comp e.permCongr (fun τ => permWeight τ)

/-! ### The rotation action and the mixed-object argument -/

variable (n k : ℕ) [NeZero k]

/-- The rotation of `Fin n ⊕ ZMod k` by `g : ZMod k`: fixes the `Fin n` part and translates the
`ZMod k` part by `g`. -/
def rotPerm (g : ZMod k) : Equiv.Perm (Fin n ⊕ ZMod k) :=
  Equiv.Perm.sumCongr (Equiv.refl (Fin n)) (Equiv.addLeft g)

omit [NeZero k] in
@[simp] theorem rotPerm_inl (g : ZMod k) (a : Fin n) :
    rotPerm n k g (Sum.inl a) = Sum.inl a := by simp [rotPerm]

omit [NeZero k] in
@[simp] theorem rotPerm_inr (g : ZMod k) (b : ZMod k) :
    rotPerm n k g (Sum.inr b) = Sum.inr (g + b) := by simp [rotPerm]

theorem rotPerm_zero : rotPerm n k 0 = 1 := by
  ext x; cases x with
  | inl a => simp
  | inr b => simp

theorem rotPerm_add (g1 g2 : ZMod k) :
    rotPerm n k (g1 + g2) = rotPerm n k g1 * rotPerm n k g2 := by
  ext x; cases x with
  | inl a => simp
  | inr b => simp [add_assoc]

/-- `rotPerm` preserves membership in `Set.range Sum.inl`. -/
theorem rotPerm_mem_range_inl_iff (g : ZMod k) (y : Fin n ⊕ ZMod k) :
    rotPerm n k g y ∈ Set.range (Sum.inl : Fin n → Fin n ⊕ ZMod k) ↔
      y ∈ Set.range (Sum.inl : Fin n → Fin n ⊕ ZMod k) := by
  cases y with
  | inl a => simp
  | inr b => simp

/-- The conjugation action of `ZMod k` on `Equiv.Perm (Fin n ⊕ ZMod k)` given by rotating the
`ZMod k`-part of the labels (fixing the `Fin n`-part). This is the action described in the
paper's proof of Proposition 2.3. -/
instance rotAddAction : AddAction (ZMod k) (Equiv.Perm (Fin n ⊕ ZMod k)) where
  vadd g σ := rotPerm n k g * σ * (rotPerm n k g)⁻¹
  zero_vadd σ := by change rotPerm n k 0 * σ * (rotPerm n k 0)⁻¹ = σ; rw [rotPerm_zero]; simp
  add_vadd g1 g2 σ := by
    change rotPerm n k (g1 + g2) * σ * (rotPerm n k (g1 + g2))⁻¹ =
      rotPerm n k g1 * (rotPerm n k g2 * σ * (rotPerm n k g2)⁻¹) * (rotPerm n k g1)⁻¹
    rw [rotPerm_add, mul_inv_rev]
    group

theorem vadd_perm_def (g : ZMod k) (σ : Equiv.Perm (Fin n ⊕ ZMod k)) :
    g +ᵥ σ = rotPerm n k g * σ * (rotPerm n k g)⁻¹ := rfl

/-- `permWeight` is invariant under the rotation-conjugation action, since conjugation
preserves `cycleType`. -/
theorem permWeight_vadd (g : ZMod k) (σ : Equiv.Perm (Fin n ⊕ ZMod k)) :
    permWeight (g +ᵥ σ) = permWeight σ := by
  rw [vadd_perm_def]; exact permWeight_conj σ (rotPerm n k g)

theorem rotPerm_inv (g : ZMod k) : (rotPerm n k g)⁻¹ = rotPerm n k (-g) := by
  have h := rotPerm_add n k g (-g)
  rw [add_neg_cancel, rotPerm_zero] at h
  exact inv_eq_of_mul_eq_one_right h.symm

/-- `Unmixed` (hence its complement) is invariant under the rotation action, since `rotPerm`
preserves `Set.range Sum.inl` setwise. -/
theorem unmixed_vadd_iff (g : ZMod k) (σ : Equiv.Perm (Fin n ⊕ ZMod k)) :
    (g +ᵥ σ) ∈ Unmixed (Fin n) (ZMod k) ↔ σ ∈ Unmixed (Fin n) (ZMod k) := by
  rw [mem_Unmixed_iff, mem_Unmixed_iff, vadd_perm_def]
  have hpt : ∀ a : Fin n, (rotPerm n k g * σ * (rotPerm n k g)⁻¹) (Sum.inl a) =
      rotPerm n k g (σ (Sum.inl a)) := by
    intro a
    simp [Equiv.Perm.mul_apply, rotPerm_inv, rotPerm_inl]
  simp_rw [hpt]
  constructor
  · intro h a
    obtain ⟨a', ha'⟩ := h a
    rcases hc : σ (Sum.inl a) with a'' | b''
    · exact ⟨a'', rfl⟩
    · rw [hc, rotPerm_inr] at ha'
      exact absurd ha' (by simp)
  · intro h a
    obtain ⟨a', ha'⟩ := h a
    exact ⟨a', by rw [ha', rotPerm_inl]⟩

/-- The key combinatorial fact (mirroring the paper's proof exactly): every mixed permutation
has trivial stabilizer under the rotation action. If a nontrivial rotation fixed a mixed `σ`,
then (since `σ` sends some `A`-label to a `B`-label, directly from the definition of "mixed")
that `B`-label would be fixed by the nontrivial rotation, contradicting freeness of the rotation
action on `B`-labels. -/
theorem mixed_stabilizer_trivial (σ : Equiv.Perm (Fin n ⊕ ZMod k))
    (hσ : σ ∉ Unmixed (Fin n) (ZMod k)) (g : ZMod k) (hg : g +ᵥ σ = σ) : g = 0 := by
  by_contra hg0
  rw [mem_Unmixed_iff] at hσ
  simp only [not_forall, not_exists] at hσ
  obtain ⟨a, ha⟩ := hσ
  obtain ⟨b, hb⟩ : ∃ b, σ (Sum.inl a) = Sum.inr b := by
    rcases hc : σ (Sum.inl a) with a' | b'
    · exact absurd hc (ha a')
    · exact ⟨b', rfl⟩
  rw [vadd_perm_def] at hg
  have hcommute : rotPerm n k g * σ = σ * rotPerm n k g := by
    rwa [mul_inv_eq_iff_eq_mul] at hg
  have hLR : (rotPerm n k g * σ) (Sum.inl a) = (σ * rotPerm n k g) (Sum.inl a) := by
    rw [hcommute]
  simp only [Equiv.Perm.mul_apply, rotPerm_inl, hb, rotPerm_inr, Sum.inr.injEq] at hLR
  apply hg0
  have hz : g + b = 0 + b := by rwa [zero_add]
  exact add_right_cancel hz

/-- **Proposition 2.3 (`prop:product`), permutation-sum form.**
`permSum (Fin n ⊕ ZMod k) ≡ permSum (Fin n) * permSum (ZMod k) (mod k)`. -/
theorem permSum_sum_congr :
    (k : ℤ) ∣ permSum (Fin n ⊕ ZMod k) - permSum (Fin n) * permSum (ZMod k) := by
  classical
  set P : Equiv.Perm (Fin n ⊕ ZMod k) → Prop := fun σ => σ ∈ Unmixed (Fin n) (ZMod k) with hP
  have hsplit : permSum (Fin n ⊕ ZMod k) =
      (∑ σ ∈ Finset.univ.filter P, permWeight σ) +
      (∑ σ ∈ Finset.univ.filter (fun σ => ¬ P σ), permWeight σ) := by
    rw [Finset.sum_filter_add_sum_filter_not Finset.univ P]
    rfl
  have hunmixed := sum_unmixed (Fin n) (ZMod k)
  have hmixed_dvd : (k : ℤ) ∣ ∑ σ ∈ Finset.univ.filter (fun σ => ¬ P σ), permWeight σ := by
    have hcard : (Fintype.card (ZMod k) : ℤ) = (k : ℤ) := by exact_mod_cast ZMod.card k
    rw [← hcard]
    apply dvd_sum_of_free_action permWeight (permWeight_vadd n k) _
    · intro g σ hσ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
      simp only [hP]
      rwa [unmixed_vadd_iff]
    · intro σ hσ g hg
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
      exact mixed_stabilizer_trivial n k σ hσ g hg
  have hdvd : (k : ℤ) ∣
      (∑ σ ∈ Finset.univ.filter P, permWeight σ) +
        (∑ σ ∈ Finset.univ.filter (fun σ => ¬ P σ), permWeight σ)
        - permSum (Fin n) * permSum (ZMod k) := by
    rw [hunmixed, add_sub_cancel_left]
    exact hmixed_dvd
  rwa [← hsplit] at hdvd

/-! ### The bridge `permSum (Fin n) = a n`

This is Step 2 of Strategy A of the plan: `permSum (Fin n)` (the honest count of colored
permutations) satisfies the same recurrence that defines `a` (footnote 1 / `Bala/Basic.lean`),
hence equals it by strong induction. `permSum_zero` below is the base case. -/

theorem permSum_zero : permSum (Fin 0) = 1 := by
  have : (Finset.univ : Finset (Equiv.Perm (Fin 0))) = {1} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    exact ⟨Finset.mem_univ 1, fun x _ => Subsingleton.elim x 1⟩
  unfold permSum permWeight
  rw [this]
  simp

theorem aList_length : ∀ n, (aList n).length = n + 1
  | 0 => by simp [aList]
  | n + 1 => by simp [aList, aList_length n]

theorem aList_getD_eq_a : ∀ n i, i ≤ n → (aList n).getD i 0 = a i := by
  intro n
  induction n with
  | zero =>
    intro i hi
    interval_cases i
    rfl
  | succ n ih =>
    intro i hi
    rcases Nat.lt_or_ge i (n + 1) with hi' | hi'
    · change (aList n ++ [_]).getD i 0 = a i
      rw [List.getD_append (aList n) _ 0 i (by rw [aList_length]; omega)]
      exact ih i (by omega)
    · have heq : i = n + 1 := by omega
      subst heq
      rfl

theorem foldl_add_eq_sum_Icc (n : ℕ) (f : ℕ → ℤ) :
    ((List.range n).map (· + 1)).foldl (fun acc m => acc + f m) 0 = ∑ m ∈ Finset.Icc 1 n, f m := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.foldl_append, List.map_cons, List.map_nil,
      List.foldl_cons, List.foldl_nil, ih, Finset.sum_Icc_succ_top (by omega)]

/-- `a (n+1)` unwound from its defining recurrence (`Bala/Basic.lean`) into a clean `Finset.sum`
over `m ∈ [1, n+1]`. This is exactly the target that `permSum`'s cycle-of-a-point decomposition
(`permSum_succ_recurrence` below) needs to match. Fully proved: purely mechanical bookkeeping
about `aList`'s `List.foldl`/`getD` definition. -/
theorem a_succ_eq_sum (n : ℕ) :
    a (n + 1) = ∑ m ∈ Finset.Icc 1 (n + 1),
      (Nat.choose n (m - 1) : ℤ) * (Nat.factorial (m - 1) : ℤ) * (numDivisors m : ℤ)
        * a (n + 1 - m) := by
  have hval : a (n + 1) =
      ((List.range (n + 1)).map (· + 1)).foldl
        (fun acc m => acc + (Nat.choose n (m - 1) : ℤ) * (Nat.factorial (m - 1) : ℤ)
            * (numDivisors m : ℤ) * (aList n).getD (n + 1 - m) 0) 0 := by
    change (aList (n + 1)).getD (n + 1) 0 = _
    change (aList n ++ [_]).getD (n + 1) 0 = _
    rw [List.getD_append_right (aList n) _ 0 (n + 1) (aList_length n).le, aList_length]
    simp
  rw [hval, foldl_add_eq_sum_Icc]
  refine Finset.sum_congr rfl (fun m hm => ?_)
  rw [Finset.mem_Icc] at hm
  rw [aList_getD_eq_a n (n + 1 - m) (by omega)]

/-! ### Cycle-of-a-point decomposition (towards `permSum_succ_recurrence`)

Fix a distinguished point `x₀ : α`. Every `σ : Equiv.Perm α` factors uniquely as
`(cycle of x₀ under σ) * (a permutation of everything else)`; this section builds that
factorization and the counting facts needed to turn it into the sum identity
`permSum_succ_recurrence`. -/

section CycleDecomp

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The set of points in the same cycle as `x₀` under `σ` (always contains `x₀`, even when `x₀`
is a fixed point of `σ`, in which case this is just `{x₀}`). -/
def orbitAt (σ : Equiv.Perm α) (x0 : α) : Finset α := insert x0 (σ.cycleOf x0).support

theorem mem_orbitAt {σ : Equiv.Perm α} {x0 y : α} :
    y ∈ orbitAt σ x0 ↔ σ.SameCycle x0 y := by
  unfold orbitAt
  rw [Finset.mem_insert, Equiv.Perm.mem_support_cycleOf_iff]
  constructor
  · rintro (h | ⟨h, -⟩)
    · rw [h]
    · exact h
  · intro h
    by_cases hx0 : x0 ∈ σ.support
    · exact Or.inr ⟨h, hx0⟩
    · rw [Equiv.Perm.notMem_support] at hx0
      exact Or.inl (h.eq_of_left hx0).symm

theorem x0_mem_orbitAt (σ : Equiv.Perm α) (x0 : α) : x0 ∈ orbitAt σ x0 :=
  Finset.mem_insert_self _ _

theorem orbitAt_invariant (σ : Equiv.Perm α) (x0 y : α) :
    σ y ∈ orbitAt σ x0 ↔ y ∈ orbitAt σ x0 := by
  rw [mem_orbitAt, mem_orbitAt, Equiv.Perm.sameCycle_apply_right]

/-- `cycleOf σ x0` is "idempotent": taking the cycle-of-`x0` again does nothing. -/
theorem cycleOf_cycleOf_self (σ : Equiv.Perm α) (x0 : α) :
    (σ.cycleOf x0).cycleOf x0 = σ.cycleOf x0 := by
  by_cases hx0 : σ x0 = x0
  · rw [(Equiv.Perm.cycleOf_eq_one_iff σ).mpr hx0, Equiv.Perm.cycleOf_one]
  · have hc : (σ.cycleOf x0) x0 ≠ x0 := by
      rw [Equiv.Perm.cycleOf_apply_self]; exact hx0
    exact (Equiv.Perm.isCycle_cycleOf σ hx0).cycleOf_eq hc

theorem orbitAt_cycleOf_self (σ : Equiv.Perm α) (x0 : α) :
    orbitAt (σ.cycleOf x0) x0 = orbitAt σ x0 := by
  unfold orbitAt
  rw [cycleOf_cycleOf_self]

/-- A permutation that equals its own `cycleOf x0` is either the identity (if `x0` is its fixed
point) or an honest cycle through `x0`. -/
theorem eq_one_or_isCycle_of_cycleOf_self_eq {c : Equiv.Perm α} {x0 : α}
    (hc : c.cycleOf x0 = c) : c = 1 ∨ (c.IsCycle ∧ x0 ∈ c.support) := by
  by_cases hx0 : c x0 = x0
  · left
    rw [← hc, Equiv.Perm.cycleOf_eq_one_iff]; exact hx0
  · right
    refine ⟨?_, Equiv.Perm.mem_support.mpr hx0⟩
    have := Equiv.Perm.isCycle_cycleOf c hx0
    rwa [hc] at this

/-- The set `Sᶜ` (complement of the orbit-of-`x0`) is `σ`-invariant, given `orbitAt σ x0 = S`. -/
theorem compl_invariant_of_orbitAt_eq {σ : Equiv.Perm α} {x0 : α} {S : Finset α}
    (hS : orbitAt σ x0 = S) (y : α) : σ y ∈ Sᶜ ↔ y ∈ Sᶜ := by
  simp only [Finset.mem_compl, ← hS]
  exact not_iff_not.mpr (orbitAt_invariant σ x0 y)

/-- The permutation of the complement `↥Sᶜ` induced by `σ`, given `orbitAt σ x0 = S`. -/
def ρPerm {σ : Equiv.Perm α} {x0 : α} {S : Finset α} (hS : orbitAt σ x0 = S) :
    Equiv.Perm (↥(Sᶜ : Finset α)) :=
  σ.subtypePerm (compl_invariant_of_orbitAt_eq hS)

/-- **The key factorization**: `σ` is the product of its cycle through `x0` and the extension
of `ρPerm` (the induced permutation on the complement). -/
theorem cycleOf_mul_ofSubtype_ρPerm {σ : Equiv.Perm α} {x0 : α} {S : Finset α}
    (hS : orbitAt σ x0 = S) :
    σ.cycleOf x0 * Equiv.Perm.ofSubtype (ρPerm hS) = σ := by
  ext y
  rw [Equiv.Perm.mul_apply]
  by_cases hy : y ∈ S
  · have hyc : y ∉ (Sᶜ : Finset α) := by simp [hy]
    rw [Equiv.Perm.ofSubtype_apply_of_not_mem (ρPerm hS) hyc]
    have hySame : σ.SameCycle x0 y := mem_orbitAt.mp (hS ▸ hy)
    exact hySame.cycleOf_apply
  · have hyc : y ∈ (Sᶜ : Finset α) := Finset.mem_compl.mpr hy
    rw [Equiv.Perm.ofSubtype_apply_of_mem (ρPerm hS) hyc]
    change (σ.cycleOf x0) (σ.subtypePerm (compl_invariant_of_orbitAt_eq hS) ⟨y, hyc⟩ : α) = σ y
    rw [Equiv.Perm.subtypePerm_apply]
    have hyNotSame : ¬ σ.SameCycle x0 y := fun h => hy (hS ▸ mem_orbitAt.mpr h)
    have hyNotSame' : ¬ σ.SameCycle x0 (σ y) := by
      rw [← hS, ← orbitAt_invariant] at hy
      rwa [mem_orbitAt] at hy
    exact Equiv.Perm.cycleOf_apply_of_not_sameCycle hyNotSame'

/-- `cycleOf σ x0` and the extension of `ρPerm` are disjoint permutations. -/
theorem disjoint_cycleOf_ofSubtype_ρPerm {σ : Equiv.Perm α} {x0 : α} {S : Finset α}
    (hS : orbitAt σ x0 = S) :
    (σ.cycleOf x0).Disjoint (Equiv.Perm.ofSubtype (ρPerm hS)) := by
  intro y
  by_cases hy : y ∈ S
  · have hyc : y ∉ (Sᶜ : Finset α) := by simp [hy]
    right
    exact Equiv.Perm.ofSubtype_apply_of_not_mem (ρPerm hS) hyc
  · have hyNotSame : ¬ σ.SameCycle x0 y := fun h => hy (hS ▸ mem_orbitAt.mpr h)
    left
    exact Equiv.Perm.cycleOf_apply_of_not_sameCycle hyNotSame

/-- `permWeight` factorizes across the cycle-of-`x0` decomposition. -/
theorem permWeight_eq_mul {σ : Equiv.Perm α} {x0 : α} {S : Finset α}
    (hS : orbitAt σ x0 = S) :
    permWeight σ = permWeight (σ.cycleOf x0) * permWeight (ρPerm hS) := by
  have hcycle : σ.cycleType = (σ.cycleOf x0).cycleType + (ρPerm hS).cycleType := by
    conv_lhs => rw [← cycleOf_mul_ofSubtype_ρPerm hS]
    rw [(disjoint_cycleOf_ofSubtype_ρPerm hS).cycleType_mul, Equiv.Perm.cycleType_ofSubtype]
  unfold permWeight
  rw [hcycle, Multiset.map_add, Multiset.prod_add]

end CycleDecomp

/-! ### The `CycleFinset`: the set of possible values of `σ.cycleOf x0` for a fixed orbit `S` -/

section CycleFinsetSection

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The set of permutations `c` that arise as `σ.cycleOf x0` for some `σ` with `orbitAt σ x0 = S`:
either the identity (if `S = {x0}`) or an honest cycle with support exactly `S`. -/
def CycleFinset (x0 : α) (S : Finset α) : Finset (Equiv.Perm α) :=
  Finset.univ.filter (fun c => c.cycleOf x0 = c ∧ orbitAt c x0 = S)

theorem cycleOf_mem_CycleFinset {σ : Equiv.Perm α} {x0 : α} {S : Finset α}
    (hS : orbitAt σ x0 = S) : σ.cycleOf x0 ∈ CycleFinset x0 S := by
  unfold CycleFinset
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_univ _, cycleOf_cycleOf_self σ x0, ?_⟩
  rw [orbitAt_cycleOf_self]; exact hS

theorem CycleFinset_card_one {x0 : α} {S : Finset α} (hx0 : x0 ∈ S) (hS1 : S.card = 1) :
    CycleFinset x0 S = {1} := by
  have hSeq : S = {x0} := by
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hS1
    rw [ha] at hx0 ⊢
    rw [Finset.mem_singleton] at hx0
    rw [hx0]
  ext c
  simp only [CycleFinset, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · rintro ⟨hc, hS'⟩
    rcases eq_one_or_isCycle_of_cycleOf_self_eq hc with h1 | ⟨hcyc, hx0mem⟩
    · exact h1
    · exfalso
      have hsupp : orbitAt c x0 = c.support := by
        unfold orbitAt; rw [hc]; exact Finset.insert_eq_self.mpr hx0mem
      rw [hsupp] at hS'
      have h2 : 2 ≤ c.support.card := hcyc.two_le_card_support
      rw [hS'] at h2
      omega
  · rintro rfl
    refine ⟨Equiv.Perm.cycleOf_one x0, ?_⟩
    show orbitAt (1 : Equiv.Perm α) x0 = S
    unfold orbitAt
    rw [Equiv.Perm.cycleOf_one, Equiv.Perm.support_one]
    simp [hSeq]

theorem mem_CycleFinset_of_two_le {x0 : α} {S : Finset α} (hx0 : x0 ∈ S) (hS2 : 2 ≤ S.card)
    (c : Equiv.Perm α) : c ∈ CycleFinset x0 S ↔ c.IsCycle ∧ c.support = S := by
  unfold CycleFinset
  rw [Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hc, hS'⟩
    rcases eq_one_or_isCycle_of_cycleOf_self_eq hc with h1 | ⟨hcyc, hx0mem⟩
    · exfalso
      rw [h1] at hS'
      unfold orbitAt at hS'
      rw [Equiv.Perm.cycleOf_one, Equiv.Perm.support_one] at hS'
      have hcard : S.card = 1 := by rw [← hS']; simp
      omega
    · refine ⟨hcyc, ?_⟩
      have hsupp : orbitAt c x0 = c.support := by
        unfold orbitAt; rw [hc]; exact Finset.insert_eq_self.mpr hx0mem
      rwa [hsupp] at hS'
  · rintro ⟨hcyc, hsupp⟩
    have hx0mem : x0 ∈ c.support := hsupp ▸ hx0
    have hc : c.cycleOf x0 = c := hcyc.cycleOf_eq (Equiv.Perm.mem_support.mp hx0mem)
    refine ⟨hc, ?_⟩
    unfold orbitAt
    rw [hc, hsupp]
    exact Finset.insert_eq_self.mpr hx0

open Classical in
theorem CycleFinset_eq_of_two_le {x0 : α} {S : Finset α} (hx0 : x0 ∈ S) (hS2 : 2 ≤ S.card) :
    CycleFinset x0 S = Finset.univ.filter (fun c : Equiv.Perm α => c.IsCycle ∧ c.support = S) := by
  ext c
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact mem_CycleFinset_of_two_le hx0 hS2 c

open Classical in
/-- The number of honest cycles with a fixed support `S` (of size `≥ 2`) is `(|S| - 1)!`: the
number of cyclic orderings of an `|S|`-element set. Proved by transporting
`Equiv.Perm.card_of_cycleType_singleton` from `Equiv.Perm ↥S` (where it says the count of full
single-cycles is `(|S|-1)! * choose |S| |S| = (|S|-1)!`) along `Equiv.Perm.ofSubtype`. -/
theorem card_isCycle_support_eq {S : Finset α} (hS2 : 2 ≤ S.card) :
    (Finset.univ.filter (fun c : Equiv.Perm α => c.IsCycle ∧ c.support = S)).card
      = Nat.factorial (S.card - 1) := by
  classical
  have him : Finset.univ.filter (fun c : Equiv.Perm α => c.IsCycle ∧ c.support = S)
      = Finset.image (Equiv.Perm.ofSubtype : Equiv.Perm (↥(S : Finset α)) → Equiv.Perm α)
          (Finset.univ.filter
            (fun g : Equiv.Perm (↥(S : Finset α)) => g.cycleType = {S.card})) := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · rintro ⟨hcyc, hsupp⟩
      have hmem : ∀ x, x ∈ S ↔ c x ∈ S := by
        intro x; rw [← hsupp, Equiv.Perm.apply_mem_support]
      have hfix : ∀ x, c x ≠ x → x ∈ S := fun x hx => hsupp ▸ Equiv.Perm.mem_support.mpr hx
      refine ⟨c.subtypePerm (fun x => (hmem x).symm), ?_, ?_⟩
      · have heq : Equiv.Perm.ofSubtype (c.subtypePerm (fun x => (hmem x).symm)) = c :=
          Equiv.Perm.ofSubtype_subtypePerm _ hfix
        have hcte : (c.subtypePerm (fun x => (hmem x).symm)).cycleType = c.cycleType := by
          conv_rhs => rw [← heq]
          rw [Equiv.Perm.cycleType_ofSubtype]
        rw [hcte, hcyc.cycleType, hsupp]
      · exact Equiv.Perm.ofSubtype_subtypePerm _ hfix
    · rintro ⟨g, hg, rfl⟩
      have hone : Multiset.card g.cycleType = 1 := by rw [hg]; exact Multiset.card_singleton _
      have hgc : g.IsCycle := Equiv.Perm.card_cycleType_eq_one.mp hone
      have hgsupp_card : g.support.card = S.card := by
        have h1 := hgc.cycleType
        rw [hg] at h1
        exact Multiset.singleton_inj.mp h1.symm
      have hgsupp : g.support = Finset.univ := by
        apply Finset.eq_univ_of_card
        rw [hgsupp_card, Fintype.card_coe]
      have hc : Equiv.Perm.ofSubtype g = g.extendDomain (Equiv.refl (↥(S : Finset α))) := rfl
      refine ⟨?_, ?_⟩
      · rw [hc]; exact hgc.extendDomain _
      · ext x
        rw [Equiv.Perm.mem_support]
        by_cases hx : x ∈ S
        · rw [Equiv.Perm.ofSubtype_apply_of_mem g hx]
          have hgx : g ⟨x, hx⟩ ≠ ⟨x, hx⟩ := by
            have hmemuniv : (⟨x, hx⟩ : ↥(S : Finset α)) ∈ g.support :=
              Finset.eq_univ_iff_forall.mp hgsupp ⟨x, hx⟩
            rwa [Equiv.Perm.mem_support] at hmemuniv
          simp only [hx, iff_true]
          intro hEq
          exact hgx (Subtype.ext hEq)
        · rw [Equiv.Perm.ofSubtype_apply_of_not_mem g hx]
          simp [hx]
  rw [him, Finset.card_image_of_injective _ Equiv.Perm.ofSubtype_injective]
  have hcardS : Fintype.card (↥(S : Finset α)) = S.card := Fintype.card_coe S
  have hkey := Equiv.Perm.card_of_cycleType_singleton (α := ↥(S : Finset α))
    (n := S.card) hS2 (by rw [hcardS])
  rw [hkey, hcardS, Nat.choose_self, mul_one]

open Classical in
theorem CycleFinset_sum_permWeight (x0 : α) {S : Finset α} (hx0 : x0 ∈ S) :
    ∑ c ∈ CycleFinset x0 S, permWeight c
      = (Nat.factorial (S.card - 1) : ℤ) * (numDivisors S.card : ℤ) := by
  rcases Nat.lt_or_ge S.card 2 with hS1 | hS2
  · have hS1' : S.card = 1 := by
      have hpos : 1 ≤ S.card := Finset.card_pos.mpr ⟨x0, hx0⟩
      omega
    rw [CycleFinset_card_one hx0 hS1', Finset.sum_singleton]
    have hw1 : permWeight (1 : Equiv.Perm α) = 1 := by
      unfold permWeight; rw [Equiv.Perm.cycleType_one]; rfl
    rw [hw1, hS1']
    norm_num [numDivisors]
  · have heq : ∀ c ∈ Finset.univ.filter (fun c : Equiv.Perm α => c.IsCycle ∧ c.support = S),
        permWeight c = (numDivisors S.card : ℤ) := by
      intro c hc
      rw [Finset.mem_filter] at hc
      obtain ⟨-, hcyc, hsupp⟩ := hc
      unfold permWeight
      rw [hcyc.cycleType, hsupp]
      simp
    rw [CycleFinset_eq_of_two_le hx0 hS2, Finset.sum_congr rfl heq, Finset.sum_const,
      card_isCycle_support_eq hS2, nsmul_eq_mul]

/-! ### The per-`S` bijection: `{σ | orbitAt σ x0 = S} ≃ CycleFinset x0 S × Perm ↥Sᶜ` -/

theorem orbitAt_mul_ofSubtype {x0 : α} {S : Finset α} {c : Equiv.Perm α}
    (hc : c ∈ CycleFinset x0 S) (τ : Equiv.Perm (↥(Sᶜ : Finset α))) :
    orbitAt (c * Equiv.Perm.ofSubtype τ) x0 = S := by
  unfold CycleFinset at hc
  rw [Finset.mem_filter] at hc
  obtain ⟨-, hcc, hcS⟩ := hc
  have horbit_eq : orbitAt c x0 = insert x0 c.support := by unfold orbitAt; rw [hcc]
  have hsupp_sub : c.support ⊆ S := by
    rw [← hcS, horbit_eq]; exact Finset.subset_insert _ _
  have hdfix : ∀ y, y ∈ S → (Equiv.Perm.ofSubtype τ) y = y := fun y hy =>
    Equiv.Perm.ofSubtype_apply_of_not_mem τ (by simp [hy])
  have hcfix : ∀ y, y ∈ (Sᶜ : Finset α) → c y = y := fun y hy => by
    by_contra hcy
    exact (Finset.mem_compl.mp hy) (hsupp_sub (Equiv.Perm.mem_support.mpr hcy))
  have hdisj : c.Disjoint (Equiv.Perm.ofSubtype τ) := fun y => by
    by_cases hy : y ∈ S
    · exact Or.inr (hdfix y hy)
    · exact Or.inl (hcfix y (Finset.mem_compl.mpr hy))
  have hstep : (c * Equiv.Perm.ofSubtype τ).cycleOf x0 = c.cycleOf x0 :=
    Equiv.Perm.cycleOf_mul_of_apply_right_eq_self hdisj.commute x0
      (hdfix x0 (hcS ▸ x0_mem_orbitAt c x0))
  change orbitAt (c * Equiv.Perm.ofSubtype τ) x0 = S
  unfold orbitAt
  rw [hstep, hcc, ← horbit_eq]
  exact hcS

theorem cycleOf_mul_ofSubtype_eq {x0 : α} {S : Finset α} {c : Equiv.Perm α}
    (hc : c ∈ CycleFinset x0 S) (τ : Equiv.Perm (↥(Sᶜ : Finset α))) :
    (c * Equiv.Perm.ofSubtype τ).cycleOf x0 = c := by
  unfold CycleFinset at hc
  rw [Finset.mem_filter] at hc
  obtain ⟨-, hcc, hcS⟩ := hc
  have horbit_eq : orbitAt c x0 = insert x0 c.support := by unfold orbitAt; rw [hcc]
  have hsupp_sub : c.support ⊆ S := by
    rw [← hcS, horbit_eq]; exact Finset.subset_insert _ _
  have hdfix : ∀ y, y ∈ S → (Equiv.Perm.ofSubtype τ) y = y := fun y hy =>
    Equiv.Perm.ofSubtype_apply_of_not_mem τ (by simp [hy])
  have hcfix : ∀ y, y ∈ (Sᶜ : Finset α) → c y = y := fun y hy => by
    by_contra hcy
    exact (Finset.mem_compl.mp hy) (hsupp_sub (Equiv.Perm.mem_support.mpr hcy))
  have hdisj : c.Disjoint (Equiv.Perm.ofSubtype τ) := fun y => by
    by_cases hy : y ∈ S
    · exact Or.inr (hdfix y hy)
    · exact Or.inl (hcfix y (Finset.mem_compl.mpr hy))
  rw [Equiv.Perm.cycleOf_mul_of_apply_right_eq_self hdisj.commute x0
    (hdfix x0 (hcS ▸ x0_mem_orbitAt c x0)), hcc]

theorem ρPerm_mul_ofSubtype {x0 : α} {S : Finset α} {c : Equiv.Perm α}
    (hc : c ∈ CycleFinset x0 S) (τ : Equiv.Perm (↥(Sᶜ : Finset α)))
    (hS : orbitAt (c * Equiv.Perm.ofSubtype τ) x0 = S) :
    ρPerm hS = τ := by
  unfold CycleFinset at hc
  rw [Finset.mem_filter] at hc
  obtain ⟨-, hcc, hcS⟩ := hc
  have horbit_eq : orbitAt c x0 = insert x0 c.support := by unfold orbitAt; rw [hcc]
  have hsupp_sub : c.support ⊆ S := by
    rw [← hcS, horbit_eq]; exact Finset.subset_insert _ _
  have hcfix : ∀ y, y ∈ (Sᶜ : Finset α) → c y = y := fun y hy => by
    by_contra hcy
    exact (Finset.mem_compl.mp hy) (hsupp_sub (Equiv.Perm.mem_support.mpr hcy))
  apply Equiv.ext
  rintro ⟨y, hy⟩
  apply Subtype.ext
  simp only [ρPerm, Equiv.Perm.subtypePerm_apply]
  rw [Equiv.Perm.mul_apply, Equiv.Perm.ofSubtype_apply_of_mem τ hy]
  exact hcfix _ (τ ⟨y, hy⟩).2

/-- **The per-`S` bijection.** Every colored permutation with `orbitAt σ x0 = S` decomposes
uniquely into a choice of cycle `c ∈ CycleFinset x0 S` (the cycle through `x0`) and a colored
permutation `τ` of the complement `↥Sᶜ`, with `permWeight σ = permWeight c * permWeight τ`. -/
theorem sum_orbitAt_eq (x0 : α) (S : Finset α) :
    ∑ σ ∈ Finset.univ.filter (fun σ : Equiv.Perm α => orbitAt σ x0 = S), permWeight σ
      = (∑ c ∈ CycleFinset x0 S, permWeight c) * permSum (↥(Sᶜ : Finset α)) := by
  classical
  have hprod : (∑ c ∈ CycleFinset x0 S, permWeight c) * permSum (↥(Sᶜ : Finset α))
      = ∑ p ∈ CycleFinset x0 S ×ˢ (Finset.univ : Finset (Equiv.Perm (↥(Sᶜ : Finset α)))),
          permWeight p.1 * permWeight p.2 := by
    rw [Finset.sum_product]
    unfold permSum
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl (fun c _ => Finset.mul_sum _ _ _)
  rw [hprod]
  apply Finset.sum_bij'
    (i := fun (σ : Equiv.Perm α)
        (hσ : σ ∈ Finset.univ.filter (fun σ : Equiv.Perm α => orbitAt σ x0 = S)) =>
      (σ.cycleOf x0, ρPerm (Finset.mem_filter.mp hσ).2))
    (j := fun (p : Equiv.Perm α × Equiv.Perm (↥(Sᶜ : Finset α)))
        (_ : p ∈ CycleFinset x0 S ×ˢ (Finset.univ : Finset (Equiv.Perm (↥(Sᶜ : Finset α))))) =>
      p.1 * Equiv.Perm.ofSubtype p.2)
    ?_ ?_ ?_ ?_ ?_
  · intro σ hσ
    rw [Finset.mem_product]
    exact ⟨cycleOf_mem_CycleFinset (Finset.mem_filter.mp hσ).2, Finset.mem_univ _⟩
  · intro p hp
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    exact orbitAt_mul_ofSubtype (Finset.mem_product.mp hp).1 p.2
  · intro σ hσ
    exact cycleOf_mul_ofSubtype_ρPerm (Finset.mem_filter.mp hσ).2
  · intro p hp
    have hp1 : p.1 ∈ CycleFinset x0 S := (Finset.mem_product.mp hp).1
    refine Prod.ext (cycleOf_mul_ofSubtype_eq hp1 p.2) ?_
    exact ρPerm_mul_ofSubtype hp1 p.2 (orbitAt_mul_ofSubtype hp1 p.2)
  · intro σ hσ
    exact permWeight_eq_mul (Finset.mem_filter.mp hσ).2

end CycleFinsetSection

/-! ### Assembling `permSum_succ_recurrence` from the `CycleDecomp`/`CycleFinsetSection` pieces -/

/-- The number of `S : Finset (Fin (n+1))` with `0 ∈ S` and `S.card = m` (for `1 ≤ m`) is
`n.choose (m-1)`: choosing the `m-1` other elements of `S` from the `n` non-`0` elements. -/
theorem card_filter_zero_mem_card_eq (n m : ℕ) (hm : 1 ≤ m) :
    (Finset.univ.filter (fun S : Finset (Fin (n + 1)) => (0 : Fin (n + 1)) ∈ S ∧ S.card = m)).card
      = n.choose (m - 1) := by
  classical
  have himg : Finset.univ.filter
      (fun S : Finset (Fin (n + 1)) => (0 : Fin (n + 1)) ∈ S ∧ S.card = m)
      = Finset.image (fun A : Finset (Fin (n + 1)) => insert (0 : Fin (n + 1)) A)
          (Finset.powersetCard (m - 1) (Finset.univ.erase (0 : Fin (n + 1)))) := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
      Finset.mem_powersetCard]
    constructor
    · rintro ⟨h0, hcard⟩
      refine ⟨S.erase 0, ⟨Finset.erase_subset_erase _ (Finset.subset_univ _), ?_⟩,
        Finset.insert_erase h0⟩
      rw [Finset.card_erase_of_mem h0, hcard]
    · rintro ⟨A, ⟨hAsub, hAcard⟩, rfl⟩
      have h0A : (0 : Fin (n + 1)) ∉ A := fun h => (Finset.mem_erase.mp (hAsub h)).1 rfl
      refine ⟨Finset.mem_insert_self _ _, ?_⟩
      rw [Finset.card_insert_of_notMem h0A, hAcard]
      omega
  have hinj : Set.InjOn (fun A : Finset (Fin (n + 1)) => insert (0 : Fin (n + 1)) A)
      (Finset.powersetCard (m - 1) (Finset.univ.erase (0 : Fin (n + 1))) :
        Set (Finset (Fin (n + 1)))) := by
    intro A hA B hB hAB
    rw [Finset.mem_coe, Finset.mem_powersetCard] at hA hB
    have h0A : (0 : Fin (n + 1)) ∉ A := fun h => (Finset.mem_erase.mp (hA.1 h)).1 rfl
    have h0B : (0 : Fin (n + 1)) ∉ B := fun h => (Finset.mem_erase.mp (hB.1 h)).1 rfl
    have herase := congrArg (fun T : Finset (Fin (n + 1)) => T.erase (0 : Fin (n + 1))) hAB
    simpa only [Finset.erase_insert h0A, Finset.erase_insert h0B] using herase
  rw [himg, Finset.card_image_of_injOn hinj, Finset.card_powersetCard,
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  simp

/-- **The recurrence for `permSum`** (the genuinely hard part of Strategy A — see the file-level
summary at the bottom of this file for a full account).

Conditioning on the cycle of a distinguished point `x₀ = 0 : Fin (n+1)`, a colored permutation
of `Fin (n+1)` decomposes uniquely into: a choice of the `m - 1` other elements of `x₀`'s
cycle (`n.choose (m-1)` ways), an arrangement of these `m` elements (including `x₀`) into a
single cycle (`(m-1)!` ways, since the number of cyclic orderings of an `m`-element set is
`(m-1)!`), a divisor-color for that cycle (`numDivisors m` ways), and an arbitrary colored
permutation of the remaining `n + 1 - m` elements (`permSum (Fin (n+1-m))` many). This is the
standard "exponential formula" / "assemblies of cycles" argument, proved via the `orbitAt`/
`CycleFinset`/`sum_orbitAt_eq` machinery above: `orbitAt σ 0` is the set of points in the same
cycle as `0`, and grouping `∑ σ, permWeight σ` first by `S := orbitAt σ 0` and then by `S.card`
reproduces exactly this sum. -/
theorem permSum_succ_recurrence (n : ℕ) :
    permSum (Fin (n + 1)) = ∑ m ∈ Finset.Icc 1 (n + 1),
      (Nat.choose n (m - 1) : ℤ) * (Nat.factorial (m - 1) : ℤ) * (numDivisors m : ℤ)
        * permSum (Fin (n + 1 - m)) := by
  classical
  -- Step 1: group `permSum (Fin (n+1)) = ∑ σ, permWeight σ` by `S := orbitAt σ 0`.
  have hstep1 : permSum (Fin (n + 1)) =
      ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin (n + 1)) => (0 : Fin (n + 1)) ∈ S),
        ∑ σ ∈ Finset.univ.filter
          (fun σ : Equiv.Perm (Fin (n + 1)) => orbitAt σ (0 : Fin (n + 1)) = S), permWeight σ := by
    unfold permSum
    exact (Finset.sum_fiberwise_of_maps_to
      (t := Finset.univ.filter (fun S : Finset (Fin (n + 1)) => (0 : Fin (n + 1)) ∈ S))
      (fun σ (_ : σ ∈ (Finset.univ : Finset (Equiv.Perm (Fin (n + 1))))) =>
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, x0_mem_orbitAt σ (0 : Fin (n + 1))⟩)
      permWeight).symm
  -- Step 2: evaluate the inner sum via `sum_orbitAt_eq` and `CycleFinset_sum_permWeight`,
  -- then rewrite the complement's `permSum` as `permSum (Fin (n+1-S.card))`.
  have hstep2 : ∀ S ∈ Finset.univ.filter (fun S : Finset (Fin (n + 1)) => (0 : Fin (n + 1)) ∈ S),
      ∑ σ ∈ Finset.univ.filter
        (fun σ : Equiv.Perm (Fin (n + 1)) => orbitAt σ (0 : Fin (n + 1)) = S), permWeight σ
        = (Nat.factorial (S.card - 1) : ℤ) * (numDivisors S.card : ℤ)
            * permSum (Fin ((n + 1) - S.card)) := by
    intro S hS
    rw [Finset.mem_filter] at hS
    have hcardeq : Fintype.card (↥(Sᶜ : Finset (Fin (n + 1)))) = (n + 1) - S.card := by
      rw [Fintype.card_coe, Finset.card_compl, Fintype.card_fin]
    rw [sum_orbitAt_eq (0 : Fin (n + 1)) S, CycleFinset_sum_permWeight (0 : Fin (n + 1)) hS.2,
      permSum_congr (Fintype.equivFinOfCardEq hcardeq)]
  rw [hstep1, Finset.sum_congr rfl hstep2]
  -- Step 3: group the outer sum (over `S` with `0 ∈ S`) by `S.card`, matching `Icc 1 (n+1)`.
  have hstep3 : ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin (n + 1)) => (0 : Fin (n + 1)) ∈ S),
      ((Nat.factorial (S.card - 1) : ℤ) * (numDivisors S.card : ℤ)
        * permSum (Fin ((n + 1) - S.card)))
      = ∑ m ∈ Finset.Icc 1 (n + 1),
          ∑ S ∈ (Finset.univ.filter
              (fun S : Finset (Fin (n + 1)) => (0 : Fin (n + 1)) ∈ S)) with S.card = m,
            ((Nat.factorial (S.card - 1) : ℤ) * (numDivisors S.card : ℤ)
              * permSum (Fin ((n + 1) - S.card))) := by
    exact (Finset.sum_fiberwise_of_maps_to
      (t := Finset.Icc 1 (n + 1))
      (fun S (hS : S ∈ Finset.univ.filter
          (fun S : Finset (Fin (n + 1)) => (0 : Fin (n + 1)) ∈ S)) => by
        rw [Finset.mem_filter] at hS
        rw [Finset.mem_Icc]
        refine ⟨Finset.card_pos.mpr ⟨(0 : Fin (n + 1)), hS.2⟩, ?_⟩
        calc S.card ≤ Fintype.card (Fin (n + 1)) := Finset.card_le_univ S
          _ = n + 1 := Fintype.card_fin _)
      (fun S => (Nat.factorial (S.card - 1) : ℤ) * (numDivisors S.card : ℤ)
        * permSum (Fin ((n + 1) - S.card)))).symm
  rw [hstep3]
  refine Finset.sum_congr rfl (fun m hm => ?_)
  rw [Finset.mem_Icc] at hm
  have hconst : ∀ S ∈ Finset.filter (fun S : Finset (Fin (n + 1)) => S.card = m)
      (Finset.univ.filter (fun S : Finset (Fin (n + 1)) => (0 : Fin (n + 1)) ∈ S)),
      ((Nat.factorial (S.card - 1) : ℤ) * (numDivisors S.card : ℤ)
        * permSum (Fin ((n + 1) - S.card)))
      = (Nat.factorial (m - 1) : ℤ) * (numDivisors m : ℤ) * permSum (Fin ((n + 1) - m)) := by
    intro S hS
    rw [Finset.mem_filter] at hS
    rw [hS.2]
  rw [Finset.sum_congr rfl hconst, Finset.sum_const]
  have hcardS : (Finset.filter (fun S : Finset (Fin (n + 1)) => S.card = m)
      (Finset.univ.filter (fun S : Finset (Fin (n + 1)) => (0 : Fin (n + 1)) ∈ S))).card
      = n.choose (m - 1) := by
    have heq : Finset.filter (fun S : Finset (Fin (n + 1)) => S.card = m)
        (Finset.univ.filter (fun S : Finset (Fin (n + 1)) => (0 : Fin (n + 1)) ∈ S))
        = Finset.univ.filter
            (fun S : Finset (Fin (n + 1)) => (0 : Fin (n + 1)) ∈ S ∧ S.card = m) := by
      ext S
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [heq]
    exact card_filter_zero_mem_card_eq n m (by omega)
  rw [hcardS, nsmul_eq_mul]
  ring

/-- **`permSum (Fin n) = a n`**: the count of colored permutations of an `n`-element type equals
the paper's sequence `a n`. Follows from `permSum_succ_recurrence` and `permSum_zero` by strong
induction, exactly mirroring how `a` itself is built from its recurrence. Depends on the
unproved `permSum_succ_recurrence`. -/
theorem permSum_eq_a (n : ℕ) : permSum (Fin n) = a n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => exact permSum_zero
    | n + 1 =>
      rw [permSum_succ_recurrence, a_succ_eq_sum]
      refine Finset.sum_congr rfl (fun m hm => ?_)
      rw [Finset.mem_Icc] at hm
      rw [ih (n + 1 - m) (by omega)]

/-! ### Final assembly -/

/-- **Proposition 2.3 (`prop:product`)**: `a(n+k) ≡ a(n) a(k) (mod k)` for `n ≥ 0`, `k ≥ 1`.

This is exactly the target statement (matching `Bala.Statements.product_congruence`, which is
declared as an `axiom` there and re-proved here under a primed name to avoid a name clash with
that axiom). It follows formally from `permSum_sum_congr` (the group-action / orbit-stabilizer
argument, fully proved) and `permSum_eq_a` (the identification of `permSum` with `a`, which in
turn rests on the single `sorry` in `permSum_succ_recurrence` above). -/
theorem product_congruence' (n k : ℕ) (hk : 1 ≤ k) :
    (k : ℤ) ∣ (a (n + k) - a n * a k) := by
  haveI : NeZero k := ⟨by omega⟩
  have heq : Fin n ⊕ ZMod k ≃ Fin (n + k) :=
    (Equiv.sumCongr (Equiv.refl (Fin n)) (ZMod.finEquiv k).toEquiv.symm).trans finSumFinEquiv
  have h1 : permSum (Fin n ⊕ ZMod k) = a (n + k) := by
    rw [permSum_congr heq, permSum_eq_a]
  have h3 : permSum (Fin n) = a n := permSum_eq_a n
  have h4 : permSum (ZMod k) = a k := by
    rw [permSum_congr (ZMod.finEquiv k).toEquiv.symm, permSum_eq_a]
  have hcong := permSum_sum_congr n k
  rwa [h1, h3, h4] at hcong

/-!
## Status summary

Fully proved, zero `sorry` (verified via `#print axioms`, which reports only the standard
`propext, Classical.choice, Quot.sound`):
* `permWeight`, `permSum`: the colored-permutation-count definitions.
* `cycleType_sumCongr`, `permWeight_sumCongr`, `sum_unmixed`: the "unmixed objects = a n * a k"
  half of the paper's argument (Definition `def:objects` + the first paragraph of the proof of
  Proposition 2.3), done exactly as in the paper via `Equiv.Perm.sumCongr` and
  `Mathlib`'s `mem_sumCongrHom_range_of_perm_mapsTo_inl`.
* `dvd_sum_of_free_action`: a from-scratch, self-contained proof (strong induction peeling off
  one free orbit at a time) of "a finite group acting freely on an invariant weighted set
  divides the weighted sum" -- i.e. orbit-stabilizer plus the class-formula conclusion the paper
  actually uses, avoiding Mathlib's heavier `MulAction` quotient machinery.
* `rotPerm`, `rotAddAction`, `mixed_stabilizer_trivial`, `permSum_sum_congr`: the mixed-object
  half of the proof, i.e. the actual novel combinatorial idea of Section 2 -- rotating the
  `B`-labels, showing every mixed object has trivial stabilizer (via a two-line computation,
  *not* the cycle-traversal argument the paper uses -- see the "informal proof" remarks below),
  and concluding `k ∣ (mixed count)`.
* `permSum_zero`, `aList_length`, `aList_getD_eq_a`, `foldl_add_eq_sum_Icc`, `a_succ_eq_sum`:
  fully mechanical bookkeeping unwinding `a`'s `List.foldl`/`aList` definition
  (`Bala/Basic.lean`) into a clean `Finset.sum` recurrence, so that it can be compared term by
  term against `permSum`'s own recurrence.

**`permSum_succ_recurrence` is now also fully proved (no `sorry`).** It is the classical
"exponential formula" fact that `permSum (Fin (n+1))` satisfies the *same* recurrence that
defines `a`, obtained by conditioning on the cycle of a distinguished point `x₀ = 0`. This was
the genuinely hard part of Strategy A (Step 2 in the original task brief), and required building
substantial cycle-decomposition machinery from scratch, since Mathlib has the *pieces*
(`Equiv.Perm.cycleOf`, `Equiv.Perm.subtypePerm`, `Equiv.Perm.ofSubtype`,
`Equiv.Perm.card_of_cycleType_singleton`) but no assembled "peel off the cycle through a point,
with cardinality bookkeeping" equivalence. The proof is organized as follows (see the
`### Cycle-of-a-point decomposition` and `### The CycleFinset` section headers above):
  * `orbitAt σ x0 := insert x0 (σ.cycleOf x0).support` is the set of points in `x0`'s cycle
    (always contains `x0`, even if `x0` is a fixed point of `σ`, in which case this is `{x0}`).
    `orbitAt_invariant` shows it is `σ`-invariant; this lets `ρPerm` extract the induced
    permutation of the complement `↥(orbitAt σ x0)ᶜ` via `Equiv.Perm.subtypePerm`.
  * `cycleOf_mul_ofSubtype_ρPerm`, `disjoint_cycleOf_ofSubtype_ρPerm`, `permWeight_eq_mul` give
    the key factorization `σ = σ.cycleOf x0 * ofSubtype (ρPerm _)` (a disjoint product), hence
    `permWeight σ = permWeight (σ.cycleOf x0) * permWeight (ρPerm _)`.
  * `CycleFinset x0 S` (the permutations `c` with `c.cycleOf x0 = c` and `orbitAt c x0 = S`, i.e.
    the possible values of `σ.cycleOf x0` for `σ` with `orbitAt σ x0 = S`) is shown to have
    `permWeight`-sum `(S.card - 1)! * numDivisors S.card` in `CycleFinset_sum_permWeight`: either
    `S = {x0}` and `CycleFinset x0 S = {1}` (`CycleFinset_card_one`), or `S.card ≥ 2` and
    `CycleFinset x0 S` is exactly the honest cycles with support `S`
    (`mem_CycleFinset_of_two_le`), whose count is `(S.card - 1)!` via `card_isCycle_support_eq`
    -- transporting `Equiv.Perm.card_of_cycleType_singleton` from `Equiv.Perm ↥S` (where a full
    single-cycle count is `(|S|-1)! * choose |S| |S| = (|S|-1)!`) along `Equiv.Perm.ofSubtype`.
  * `sum_orbitAt_eq` is the per-`S` bijection `{σ | orbitAt σ x0 = S} ≃ CycleFinset x0 S × Perm
    ↥Sᶜ` (built explicitly via `Finset.sum_bij'`, with round-trip facts
    `orbitAt_mul_ofSubtype`/`cycleOf_mul_ofSubtype_eq`/`ρPerm_mul_ofSubtype`), giving
    `∑_{σ : orbitAt σ x0 = S} permWeight σ = (∑_{CycleFinset x0 S} permWeight) * permSum ↥Sᶜ`.
  * `permSum_succ_recurrence` itself assembles these: group `∑ σ, permWeight σ` first by
    `S := orbitAt σ 0` (`Finset.sum_fiberwise_of_maps_to`), evaluate each fiber via the above,
    then regroup by `S.card = m` and count `{S | 0 ∈ S, S.card = m}` as `n.choose (m-1)` via
    `card_filter_zero_mem_card_eq` (a bijection `S ↦ S.erase 0` with `m-1`-subsets of the `n`
    non-`0` elements).
Everything downstream of it (`permSum_eq_a`, `product_congruence'`) was already a complete,
formal proof conditional on this; the whole file is now `sorry`-free end to end.

**On the correctness of the paper's informal proof (Section 2):** no gap was found. The
"unmixed" and orbit-stabilizer halves are exactly as the paper states and were formalized
faithfully. One clarification surfaced during formalization: the paper's stabilizer-triviality
argument phrases the key step as "traverse the mixed cycle to find an `A`→`B` transition
`u, σ(u)`"; formalizing `Unmixed`/`Mixed` directly as "does `σ` map `A` into `A`" (equivalent to
the paper's "some cycle crosses `A` and `B`", but not needing cycle language at all) shows that
this transition pair is available *immediately* by pigeonhole from the definition of "mixed",
with no need to actually walk around the cycle. That is a simplification of the exposition, not
a correction -- the paper's argument is correct as written, just slightly more roundabout than
necessary.
-/
