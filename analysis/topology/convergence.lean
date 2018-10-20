import analysis.topology.continuity

open filter set

universe u

structure convergence (α : Type u) : Type (u+1) :=
(r : Π (n : Type u) (ω : ultrafilter n), (n → α) → α → Prop)
(H : ∀ (n : Type u) (f : n → α) (ω : ultrafilter n) (a : α),
     r α (ω.map f) id a → r n ω f a)
(I : ∀ (a : α), r α (pure a) id a)
(J : ∀ (n m : Type u) (ω : ultrafilter n) (ξ : n → ultrafilter m)
       (f : n → α) (g : m → α) (a : α),
     (∀ (i : n), r m (ξ i) g (f i)) ∧ r n ω f a → r m (ω.bind ξ) g a)

def convergence_of_topology {α : Type u} (t : topological_space α) : convergence α :=
{ r := λ n ω f x, ∀ u ∈ (nhds x).sets, {i | f i ∈ u} ∈ ω.val.sets,
  H := assume n f ω a h, h,
  I := assume a, pure_le_nhds a,
  J := assume n m ω ξ f g a ⟨h₁, h₂⟩ u hu,
    let ⟨v, vu, vo, av⟩ := mem_nhds_sets_iff.mp hu in
    ω.val.sets_of_superset (h₂ v (mem_nhds_sets vo av))
      (λ i hi, h₁ _ _ (mem_nhds_sets_iff.mpr ⟨v, vu, vo, hi⟩)) }

section closure_operator

variables {α : Type u} [partial_order α]

structure is_closure_operator (cl : α → α) : Prop :=
(monotone : ∀ {x y}, x ≤ y → cl x ≤ cl y)
(unit : ∀ x, x ≤ cl x)
(join : ∀ x, cl (cl x) ≤ cl x)

lemma is_closure_operator.idempotent {cl : α → α} (h : is_closure_operator cl) (x) :
  cl (cl x) = cl x :=
le_antisymm (h.join x) (h.unit (cl x))

end closure_operator

section kuratowski

open lattice

variables {α : Type u} [semilattice_sup_bot α]

structure is_kuratowski (cl : α → α) extends is_closure_operator cl : Prop :=
(le_bot : cl ⊥ ≤ ⊥)
(le_sup : ∀ x y, cl (x ⊔ y) ≤ cl x ⊔ cl y)

lemma is_kuratowski.bot {cl : α → α} (h : is_kuratowski cl) : cl ⊥ = ⊥ :=
bot_unique h.le_bot

lemma is_kuratowski.sup {cl : α → α} (h : is_kuratowski cl) (x y) :
  cl (x ⊔ y) = cl x ⊔ cl y :=
le_antisymm (h.le_sup x y) (sup_le (h.monotone le_sup_left) (h.monotone le_sup_right))

variables (α)
def kuratowski_closure_operator := subtype (is_kuratowski : set (α → α))

end kuratowski

section kuratowski_and_topology

/- A topology can equivalently be described by its closure
  operator. The closed sets of the topology are the sets `s` with `cl
  s = s`. -/

variables {α : Type u}

def kuratowski_of_topology (t : topological_space α) : kuratowski_closure_operator (set α) :=
⟨λ s, closure s,
 { monotone := assume s t, closure_mono,
   unit := assume s, subset_closure,
   join := assume s, le_of_eq closure_closure,
   le_bot := le_of_eq closure_empty,
   le_sup := assume s t, le_of_eq closure_union }⟩

-- TODO: Define a topological space in terms of its closed sets
-- (rather than open ones), in general?

def topology_of_kuratowski_closure {cl : set α → set α} (h : is_kuratowski cl) :
  topological_space α :=
{ is_open := λ s, cl (-s) = -s,
  is_open_univ := by convert h.bot; simp; refl,
  is_open_inter := assume s t hs ht,
    by convert (h.sup (-s) (-t)); simp [hs, ht, compl_inter]; refl,
  is_open_sUnion := assume s hs, begin
    refine le_antisymm _ (h.unit _),
    rw [compl_sUnion],
    apply subset_sInter,
    rintros _ ⟨t', ht', rfl⟩,
    change _ ⊆ -_,
    rw ←hs t' ht',
    apply h.monotone,
    exact sInter_subset_of_mem ⟨t', ht', rfl⟩
  end }

def topology_of_kuratowski (k : kuratowski_closure_operator (set α)) : topological_space α :=
topology_of_kuratowski_closure k.property

def topology_equiv_kuratowski : topological_space α ≃ kuratowski_closure_operator (set α) :=
{ to_fun := kuratowski_of_topology,
  inv_fun := topology_of_kuratowski,
  left_inv := assume t, begin
    resetI,
    ext s,
    change closure (-s) = -s ↔ is_open s,
    rw [closure_eq_iff_is_closed, is_closed_compl_iff]
  end,
  right_inv := assume k, begin
    letI := topology_of_kuratowski k,
    cases k with cl h,
    apply subtype.eq, ext1 s,
    change closure s = cl s,
    apply subset.antisymm,
    { apply closure_minimal (h.unit s),
      change cl (- -cl s) = - -cl s,
      rw compl_compl,
      exact h.to_is_closure_operator.idempotent s },
    { apply subset_sInter, rintros t ⟨tc, st⟩,
      have : - -t = cl (- -t), from tc.symm, rw compl_compl at this,
      rw this, exact h.monotone st }
  end }

end kuratowski_and_topology

section topology_of_convergence

variables {α : Type u}

def closure_of_convergence (δ : convergence α) : set α → set α :=
λ A, {x | ∃ (u : ultrafilter α), δ.r α u id x ∧ A ∈ u.val.sets}

-- (F). Needed?
lemma mem_closure_of_convergence {δ : convergence α} {A : set α} {x : α} :
  x ∈ closure_of_convergence δ A ↔
  ∃ n (ω : ultrafilter n) (f : n → α), δ.r n ω f x ∧ {i | f i ∈ A} ∈ ω.val.sets :=
sorry

-- Needed?
lemma convergence.lemma_2_2 (δ : convergence α) (a : α) {n : Type u} (ω : ultrafilter n) :
  δ.r n ω (λ _, a) a :=
δ.H n (λ _, a) ω a (by convert δ.I a; admit)

open classical
local attribute [instance] prop_decidable

lemma closure_of_convergence_is_kuratowski (δ : convergence α) :
  is_kuratowski (closure_of_convergence δ) :=
{ monotone := assume A B AB x ⟨u, ux, Au⟩, ⟨u, ux, u.val.sets_of_superset Au AB⟩,
  unit := assume A x xA, ⟨pure x, δ.I x, mem_pure xA⟩,
  join := assume A x ⟨u, ux, hu⟩,
    let u' : α → ultrafilter α :=
          λ y, if h : y ∈ closure_of_convergence δ A then some h else pure y,
        w : ultrafilter α := u.bind u' in
    have t₁ : ∀ y, δ.r α (u' y) id y, begin
      intro y, dsimp [u'], split_ifs,
      { exact (some_spec h).1 },
      { apply δ.I }
    end,
    have t₂ : ∀ y, y ∈ closure_of_convergence δ A → A ∈ (u' y).val.sets,
      by intros y h; dsimp [u']; simpa [dif_pos h] using (some_spec h).2,
    ⟨w, δ.J α α u u' id id x ⟨t₁, ux⟩, u.val.sets_of_superset hu t₂⟩,
  le_bot := assume x ⟨u, _, hu⟩, u.property.1 (empty_in_sets_eq_bot.mp hu),
  le_sup := assume A B x ⟨u, ux, ABu⟩,
    (mem_or_mem_of_ultrafilter u.property ABu).imp
      (assume h, ⟨u, ux, h⟩) (assume h, ⟨u, ux, h⟩) }

-- TODO: Move to ultrafilter
lemma exists_ultrafilter_iff (f : filter α) : (∃ (u : ultrafilter α), u.val ≤ f) ↔ f ≠ ⊥ :=
⟨assume ⟨u, uf⟩, lattice.neq_bot_of_le_neq_bot u.property.1 uf,
 assume h, let ⟨u, uf, hu⟩ := exists_ultrafilter h in ⟨⟨u, hu⟩, uf⟩⟩

lemma closure_of_convergence_of_topology (t : topological_space α) (s : set α) :
  closure_of_convergence (convergence_of_topology t) s = closure s :=
begin
  ext a,
  change (∃ (u : ultrafilter α), u.val ≤ nhds a ∧ s ∈ u.val.sets) ↔ a ∈ closure s,
  have : ∀ {f : filter α}, f ≤ nhds a ∧ s ∈ f.sets ↔ f ≤ nhds a ⊓ principal s, by simp,
  simp only [this],
  rw [exists_ultrafilter_iff, closure_eq_nhds], refl
end

-- Next: The convergence of the topology associated to the closure
-- operator associated to a convergence is the original convergence.
lemma convergence_of_closure_of_convergence (δ : convergence α) :
  convergence_of_topology (topology_of_kuratowski_closure (closure_of_convergence_is_kuratowski δ)) = δ :=
sorry

end topology_of_convergence
