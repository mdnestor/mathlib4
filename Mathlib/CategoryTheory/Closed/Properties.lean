/-
Copyright (c) 2024 Michael Nestor. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Nestor
-/
import Mathlib.CategoryTheory.Closed.Cartesian

/-!
# Properties of Cartesian closed categories

Defines point-surjectivity and weak point-surjective morphisms.

Proves Lawvere's fixed point theorem for Cartesian closed categories.

## References
https://ncatlab.org/nlab/show/Lawvere%27s+fixed+point+theorem

-/

def point_surjective {C : Type u} [Category.{v} C] [HasTerminal C] {X Y: C} (f: X ⟶ Y): Prop :=
  ∀ y: ⊤_ C ⟶ Y, ∃ x: ⊤_ C ⟶ X, x ≫ f = y

def weak_point_surjective {C : Type u} [Category.{v} C] [HasFiniteProducts C] [CartesianClosed C] {A X Y: C} (g: X ⟶ A ⟹ Y): Prop :=
  ∀ f: A ⟶ Y, ∃ x: ⊤_ C ⟶ X, ∀ a: ⊤_ C  ⟶ A, a ≫ (prod.rightUnitor A).inv ≫ uncurry (x ≫ g) = a ≫ f

theorem weak_point_surjective_of_point_surjective {C : Type u} [Category.{v} C] [HasFiniteProducts C] [CartesianClosed C] {A X Y: C} {g: X ⟶ A ⟹ Y} (h: point_surjective g): weak_point_surjective g := by
  intro f
  obtain ⟨x, hx⟩ := h (curry ((prod.rightUnitor A).hom ≫ f))
  exists x
  simp [hx]

def has_fixed_point {C: Type u} [Category.{v} C] [HasTerminal C] {Y: C} (t: Y ⟶ Y): Prop :=
  ∃ y: ⊤_ C ⟶ Y, y ≫ t = y

def fixed_point_property {C: Type u} [Category.{v} C] [HasTerminal C] (Y: C): Prop :=
  ∀ t: Y ⟶ Y, has_fixed_point t

-- Lawvere's fixed point theorem
theorem lawvere_fixed_point {C: Type u} [Category.{v} C] [HasFiniteProducts C] [CartesianClosed C] {A Y: C} {g: A ⟶ A ⟹ Y} (h: weak_point_surjective g): fixed_point_property Y := by
  intro t
  have h1 := h (diag A ≫ uncurry g ≫ t)
  obtain ⟨x, hx⟩ := h1
  exists x ≫ diag A ≫ uncurry g
  have h2 := hx x
  have h3: x ≫ (prod.rightUnitor A).inv ≫ uncurry (x ≫ g) = x ≫ diag A ≫ uncurry g := by
    rw [uncurry_natural_left x g]
    simp
    repeat rw [←Category.assoc]
    apply eq_whisker
    apply prod.hom_ext
    simp
    simp
    rw [←Category.assoc]
    calc
      (x ≫ terminal.from A) ≫ x = 𝟙 (⊤_ C) ≫ x := by rw [CategoryTheory.Limits.terminal.hom_ext (x ≫ terminal.from A) (𝟙 (⊤_ C))]
                              _ = x            := Category.id_comp x
  rw [h3] at h2
  simp [Eq.comm]
  exact h2
