/- SPDX-License-Identifier: Apache-2.0 -/
module

/-!
# Containers and their functors

Endofunctors on `Type u`, natural transformations between them, and unary
containers `S ◁ P` with their extension functors `⟦ S ◁ P ⟧`.
-/

@[expose] public section

universe u

/-! ## Functors -/

/-- An endofunctor on `Type u`. -/
structure Func : Type (u + 1) where
  obj : Type u → Type u
  mor {α β} : (α → β) → obj α → obj β

namespace Func

/-- A natural transformation `F ⟹ G`. -/
@[ext] structure NatTrans (F G : Func.{u}) : Type (u + 1) where
  app {α : Type u} : F.obj α → G.obj α
  naturality {α β : Type u} (h : α → β) (x : F.obj α) :
    app (F.mor h x) = G.mor h (app x)

@[inherit_doc] infixr:10 " ⟹ " => NatTrans

end Func

/-! ## Containers -/

/--
  A unary container `S ◁ P` is composed of `S`: a collection of shapes and
  `P`: for each shape, the positions where data can be stored.
-/
structure Cont : Type (u + 1) where
  S : Type u
  P : S → Type u

namespace Cont

/-- The extension `⟦ S ◁ P ⟧ α = Σ s : S, (P s → α)`. -/
def Ext (C : Cont.{u}) : Type u → Type u :=
  fun α => (s : C.S) × (C.P s → α)

section Ext

variable {C : Cont.{u}} {α β : Type u}

/-- Keep the shape, post-compose on the positions. -/
def Ext.map (g : α → β) : C.Ext α → C.Ext β :=
  fun ⟨s, f⟩ => ⟨s, g ∘ f⟩

end Ext

/-- `S ◁ P` gives rise to the functor `⟦ S ◁ P ⟧`. -/
def toFunc (C : Cont.{u}) : Func.{u} :=
  ⟨C.Ext, Ext.map⟩

end Cont
