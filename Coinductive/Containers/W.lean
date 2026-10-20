/- SPDX-License-Identifier: Apache-2.0 -/
module

public import Coinductive.Containers.Basic

/-!
# W-types

The W-type of a container `C` is the type of well-founded trees whose nodes are
labelled by shapes `s : C.S`, with one subtree for each position `p : C.P s`.
It is the initial algebra of the functor `⟦ C ⟧`.

* `sup : ⟦ C ⟧ (W C) → W C` is the algebra structure, with inverse `dest`;
* `fold alg` is the unique algebra morphism from `W C` into any algebra `alg`
  (`fold_sup`, `fold_unique`).

Note that `fold` here is the paper's fold out of `W C` (a catamorphism). It is not
the constructor `CoInd.fold` of `Coinductive.CoInd`, which corresponds to `sup`.
-/

@[expose] public section

universe u

namespace Cont

/--
  The W-type of `C`: a node has a shape `s` and one subtree for each position
  of `s`. The constructor is curried; `W.sup` is the uncurried version.
-/
inductive W (C : Cont.{u}) : Type u where
  | mk (s : C.S) (f : C.P s → W C) : W C

namespace W

variable {C : Cont.{u}} {α : Type u}

/-! ## The algebra structure -/

section Sup

/-- The paper's `sup : ⟦ C ⟧ (W C) → W C`. -/
def sup : C.Ext (W C) → W C :=
  fun ⟨s, f⟩ => mk s f

/-- The inverse of `sup`: read off the root shape and the subtrees. -/
def dest : W C → C.Ext (W C)
  | mk s f => ⟨s, f⟩

theorem dest_sup (x : C.Ext (W C)) : dest (sup x) = x := rfl

theorem sup_dest (w : W C) : sup (dest w) = w := by
  cases w
  rfl

end Sup

/-! ## Initiality -/

section Fold

/-- Fold a tree with an algebra `alg : ⟦ C ⟧ α → α`, bottom-up. -/
def fold (alg : C.Ext α → α) : W C → α
  | mk s f => alg ⟨s, fun p => fold alg (f p)⟩

/-- `fold alg` is an algebra morphism from `sup` to `alg`. -/
theorem fold_sup (alg : C.Ext α → α) (x : C.Ext (W C)) :
    fold alg (sup x) = alg (Ext.map (fold alg) x) := by
  rcases x with ⟨s, f⟩
  rfl

/-- `fold alg` is the only algebra morphism from `sup` to `alg`. -/
theorem fold_unique (alg : C.Ext α → α) (h : W C → α)
    (hh : ∀ x, h (sup x) = alg (Ext.map h x)) : h = fold alg := by
  funext w
  induction w with
  | mk s f ih =>
    rw [fold]
    exact (hh ⟨s, f⟩).trans (congrArg (fun k => alg ⟨s, k⟩) (funext ih))

end Fold

end W

end Cont
