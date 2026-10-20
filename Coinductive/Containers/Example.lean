/- SPDX-License-Identifier: Apache-2.0 -/
module

public import Coinductive.Containers.Basic

@[expose] public section

-- Indexed Containers motivating examples

/-- Index means the upperbound. -/
inductive MyFin : Nat → Type where
  | zero : MyFin (n + 1)
  | succ (x : MyFin n) : MyFin (n + 1)

/-- Index means the length of vector. -/
inductive MyVec (α : Type) : Nat → Type where
  | nil : MyVec α 0
  | cons (x : α) (xs : MyVec α n) : MyVec α (n + 1)

inductive ScLam : Nat → Type where
  | var (i : MyFin n) : ScLam n
  | app (f a : ScLam n) : ScLam n
  | lam (t : ScLam (n + 1)) : ScLam n

mutual
  inductive NeLam : Nat → Type where
    | var (i : Fin n) : NeLam n
    | app (f : NeLam n) (a : NfLam n) : NeLam n
  with
  inductive NfLam : Nat → Type where
    | lam (t : NfLam (n + 1)) : NfLam n
    | ne (t : NeLam n) : NfLam n
end
