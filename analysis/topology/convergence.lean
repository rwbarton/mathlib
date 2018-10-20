import analysis.topology.continuity

open filter

universe u

structure convergence (α : Type u) : Type (u+1) :=
(r : Π (n : Type u) (ω : ultrafilter n), (n → α) → α → Prop)
(H : ∀ (n : Type u) (f : n → α) (ω : ultrafilter n) (a : α),
     r α (ω.map f) id a → r n ω f a)
(I : ∀ (a : α), r α (pure a) id a)
(J : ∀ (n m : Type u) (ω : ultrafilter n) (ξ : n → ultrafilter m)
       (f : n → α) (g : m → α) (a : α),
     (∀ (i : n), r m (ξ i) g (f i)) ∧ r n ω f a → r m (ω.bind ξ) g a)

variables {α : Type u}

def convergence_of_topology (t : topological_space α) : convergence α :=
{ r := λ n ω f x, ∀ u ∈ (nhds x).sets, {i | f i ∈ u} ∈ ω.val.sets,
  H := assume n f ω a h, h,
  I := assume a, pure_le_nhds a,
  J := assume n m ω ξ f g a ⟨h₁, h₂⟩ u hu,
    let ⟨v, vu, vo, av⟩ := mem_nhds_sets_iff.mp hu in
    ω.val.sets_of_superset (h₂ v (mem_nhds_sets vo av))
      (λ i hi, h₁ _ _ (mem_nhds_sets_iff.mpr ⟨v, vu, vo, hi⟩)) }
