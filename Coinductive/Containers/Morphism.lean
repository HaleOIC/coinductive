/- SPDX-License-Identifier: Apache-2.0 -/
module

public import Coinductive.Containers.Basic

/-!
# Container morphisms

A morphism `C ⇒ D` maps shapes forwards and positions backwards. Each morphism
acts on extensions as a natural transformation `⟦ C ⟧ ⟹ ⟦ D ⟧`, and every
natural transformation arises from exactly one morphism (`ofNat_toNat`,
`toNat_ofNat`): `⟦_⟧` is full and faithful.
-/

@[expose] public section

universe u

namespace Cont

/--
  A container morphism `C ⇒ D`:
  (1) `f`: a map on shapes, going forwards.
  (2) `r`: for each shape, a map on positions, going backwards.
-/
structure Hom (C D : Cont.{u}) : Type u where
  f : C.S → D.S
  r : (s : C.S) → D.P (f s) → C.P s

@[inherit_doc] infixr:10 " ⇒ " => Hom

namespace Hom

variable {C D E : Cont.{u}} {α β : Type u}

/-- A container morphism `m : C ⇒ D` turns a `C`-container into a `D`-container. -/
def app (m : C ⇒ D) : C.Ext α → D.Ext α :=
  fun ⟨s, g⟩ => ⟨m.f s, g ∘ m.r s⟩

/-- `app` is natural: mapping before or after it gives the same result. -/
theorem app_map (m : C ⇒ D) (h : α → β) (x : C.Ext α) :
    m.app (Ext.map h x) = Ext.map h (m.app x) := by
  rfl

/-- Shapes go forwards through `m` then `n`; positions go backwards. -/
def comp (n : D ⇒ E) (m : C ⇒ D) : C ⇒ E :=
  ⟨n.f ∘ m.f, fun s => m.r s ∘ n.r (m.f s)⟩

/-! ## Morphisms are natural transformations -/

section NatTrans

/-- Forwards: a morphism acts as a natural transformation via `app`. -/
def toNat (m : C ⇒ D) : C.toFunc ⟹ D.toFunc where
  app := m.app
  naturality h x := m.app_map h x

/-- Backwards: apply `η` to the generic element of shape `s`. -/
def ofNat (η : C.toFunc ⟹ D.toFunc) : C ⇒ D where
  f s := (η.app ⟨s, id⟩).1
  r s := (η.app ⟨s, id⟩).2

theorem ofNat_toNat (m : C ⇒ D) : ofNat m.toNat = m := rfl

theorem toNat_ofNat (η : C.toFunc ⟹ D.toFunc) : (ofNat η).toNat = η := by
  ext α ⟨s, p⟩
  exact (η.naturality p ⟨s, id⟩).symm

end NatTrans

end Hom

end Cont
