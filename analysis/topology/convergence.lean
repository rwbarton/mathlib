import analysis.topology.continuity

open filter

universe u

lemma not_mem_iff_compl_mem_of_ultrafilter {α : Type u} {f : filter α} (hf : ultrafilter f)
  {s : set α} : s ∉ f.sets ↔ -s ∈ f.sets :=
begin
  split,
  { intro h, exact (mem_or_compl_mem_of_ultrafilter hf s).resolve_left h },
  { intros h₁ h₂, apply mt empty_in_sets_eq_bot.mp hf.1,
    convert f.inter_sets h₁ h₂, simp }
end

-- bundled ultrafilter
def ultra (n : Type u) := {ω : filter n // ultrafilter ω}

def ultra.image {n m : Type u} (ω : ultra n) (f : n → m) : ultra m :=
⟨ω.val.map f, ultrafilter_map ω.property⟩

def ultra.pure {n : Type u} (x : n) : ultra n :=
⟨pure x, ultrafilter_pure⟩

def ultra.bind {n m : Type u} (ω : ultra n) (ξ : n → ultra m) : ultra m :=
⟨ω.val.bind (subtype.val ∘ ξ), begin
   apply ultrafilter_of_split,
-- TODO: Can we combine these two properties using the correct def of ultrafilter?
   { change ¬_, rw ←empty_in_sets_eq_bot,
     dsimp [filter.bind, filter.join, filter.map],
     convert mt empty_in_sets_eq_bot.mp ω.property.1,
     ext i,
     have : ∅ ∉ (ξ i).val.sets, from mt empty_in_sets_eq_bot.mp (ξ i).property.1,
     simpa using this },
   { intro s,
     dsimp [filter.bind, filter.join, filter.map],
     suffices : {i : n | -s ∈ (ξ i).val.sets} = -{i : n | s ∈ (ξ i).val.sets},
     { rw this, apply mem_or_compl_mem_of_ultrafilter ω.property },
     ext i,
     exact (not_mem_iff_compl_mem_of_ultrafilter (ξ i).property).symm }
 end⟩

-- Do we need preconvergences?

structure convergence (α : Type u) : Type (u+1) :=
(r : Π (n : Type u) (ω : ultra n), (n → α) → α → Prop)
(H : ∀ (n : Type u) (f : n → α) (ω : ultra n) (a : α), r α (ω.image f) id a → r n ω f a)
(I : ∀ (a : α), r α (ultra.pure a) id a)
(J : ∀ (n m : Type u) (ω : ultra n) (ξ : n → ultra m) (f : n → α) (g : m → α) (a : α),
     (∀ (i : n), r m (ξ i) g (f i)) ∧ r n ω f a → r m (ω.bind ξ) g a)
