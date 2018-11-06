import category_theory.functor_category
import category_theory.yoneda

universes u u' v

open category_theory

namespace category_theory.functor

variables (J : Type v) [small_category J]
variables (C : Type u) [𝒞 : category.{u v} C]
include 𝒞

def const : C ⥤ (J ⥤ C) :=
{ obj := λ X,
  { obj := λ j, X,
    map' := λ j j' f, 𝟙 X },
  map' := λ X Y f, { app := λ j, f } }

namespace const
@[simp] lemma obj_obj (X : C) (j : J) : ((const J C) X) j = X := rfl
@[simp] lemma obj_map (X : C) {j j' : J} (f : j ⟶ j') : (const J C X).map f = 𝟙 X := rfl
@[simp] lemma map_app {X Y : C} (f : X ⟶ Y) (j : J) : ((const J C).map f) j = f := rfl
end const

variables {J}

section
variables {D : Type u'} [𝒟 : category.{u' v} D]
include 𝒟

@[simp] def const_compose (X : C) (F : C ⥤ D) : const J D (F X) ≅ const J C X ⋙ F :=
{ hom := { app := λ _, 𝟙 _ },
  inv := { app := λ _, 𝟙 _ } }

end

variables {C}

/--
`F.cones` is the functor assigning to an object `X` the type of
natural transformations from the constant functor with value `X` to `F`.

`cone F` is equivalent, in the obvious way, to `Σ X, F.cones X`.
-/
def cones (F : J ⥤ C) : (Cᵒᵖ) ⥤ (Type v) :=
  (const (Jᵒᵖ) (Cᵒᵖ)) ⋙ (op_inv J C) ⋙ ((yoneda (J ⥤ C)).obj F)

end category_theory.functor