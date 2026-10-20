/- SPDX-License-Identifier: Apache-2.0 -/
module

@[expose] public section

universe u

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

/-! ## The category of families over `I` (`Fam I`) -/

variable {I : Type u}

/-- `I`-indexed families of types are the objects of `Fam I`. -/
abbrev Fam (I : Type u) : Type (u + 1) := I → Type u

/-- A morphism of `Fam I` is one function `α i → β i` for each index `i`. -/
abbrev IHom {I} (α β : Fam I) : Type u := (i : I) → α i → β i

@[inherit_doc] infixr:25 " →ᴵ " => IHom

namespace IHom

variable {α β γ θ : Fam I}

protected def id : α →ᴵ α :=
  fun _ α => α

/-- Composition of morphisms in `Fam I`, index by index. -/
protected def comp (g : β →ᴵ γ) (f : α →ᴵ β) : α →ᴵ γ :=
  fun i => g i ∘ f i

theorem id_comp (f : α →ᴵ β) : IHom.comp IHom.id f = f := rfl
theorem comp_id (f : α →ᴵ β) : IHom.comp f IHom.id = f := rfl
theorem comp_assoc (f : α →ᴵ β) (g : β →ᴵ γ) (h : γ →ᴵ θ) :
    IHom.comp (IHom.comp h g) f = IHom.comp h (IHom.comp g f) :=
  rfl

end IHom

@[inherit_doc] infixr:90 " ∘ᴵ " => IHom.comp

/-- An `I`-indexed functor from `Fam I` to `Type u`. -/
structure IFunc (I : Type u) : Type (u + 1) where
  obj : Fam I → Type u
  mor {α β : Fam I} : (α →ᴵ β) → obj α → obj β

namespace IFunc

/-- A natural transformation over `Fam I`. -/
@[ext] structure NatTrans (F G : IFunc.{u} I) : Type (u + 1) where
  app {α} : F.obj α → G.obj α
  naturality {α β} (h : α →ᴵ β) (x : F.obj α) :
    app (F.mor h x) = G.mor h (app x)

@[inherit_doc] infixr:10 " ⟹ᴵ " => NatTrans

section monad

def η (i : I) : IFunc I where
  obj α := α i
  mor f := f i

def bind {J} (F : IFunc I) (H : I → IFunc J) : IFunc J where
  obj α := F.obj (fun i => (H i).obj α)
  mor f := F.mor (fun i => (H i).mor f)

/-- Lean's monad hold for universal property (`Type u → Type v`) frees us from introducing relative monad. -/
instance : Monad IFunc.{u} where
  pure := η
  bind := bind

/-- Law (1): substituting into the variable `η i` gives `H i`. -/
theorem η_bind {J : Type u} (i : I) (H : I → IFunc J) :
    (η i) >>= H = H i :=
  rfl

/-- Law (2): substituting each variable by itself changes nothing. -/
theorem bind_η (F : IFunc I) : F >>= η = F := rfl

/-- Law (3): substituting in two steps is substituting the composite. -/
theorem bind_assoc {J K} (F: IFunc I) (G : I → IFunc J) (H : J → IFunc K) :
    (F >>= G) >>= H = F >>= (fun i => (G i) >>= H) := by
  rfl

instance : LawfulMonad IFunc.{u} := LawfulMonad.mk'
  (id_map := fun _ => rfl)
  (pure_bind := η_bind)
  (bind_assoc := bind_assoc)

end monad

end IFunc

abbrev IFunc' (I J : Type u) : Type (u + 1) := J → IFunc I

namespace IFunc'

variable {I J K : Type u}

/-- As a functor `Fam I → Fam J`: output index `j` gets `(F j).obj α`. -/
def obj (F : IFunc' I J) : Fam I → Fam J := fun α => fun j => (F j).obj α

def mor {α β} (F : IFunc' I J) (h : α →ᴵ β) : F.obj α →ᴵ F.obj β :=
  fun j => (F j).mor h

/--
  A natural transformation between doubly indexed functors: for every
  family `α`, a morphism `F.obj α →ᴵ G.obj α` in `Fam J`, natural in `α`.
-/
@[ext] structure NatTrans (F G : IFunc' I J) : Type (u + 1) where
  app {α : Fam I} : F.obj α →ᴵ G.obj α
  naturality {α β : Fam I} (h : α →ᴵ β) (j : J) (x : F.obj α j) :
    app j (F.mor h j x) = G.mor h j (app j x)

@[inherit_doc] infixr:25 " ⟹ᴵ' " => NatTrans

/-- The identity functor `Fam I → Fam I` is `η`. -/
def id (I : Type u) : IFunc' I I := IFunc.η

/-- Composition `Fam I → Fam J → Fam K`, via `bind`. -/
def comp {I J K : Type u} (G : IFunc' J K) (F : IFunc' I J) : IFunc' I K :=
  fun k => IFunc.bind (G k) F

/-- Re-indexing operation. -/
def reIndex (h : J → K) : IFunc' I K → IFunc' I J :=
  fun F => F ∘ h

end IFunc'


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
