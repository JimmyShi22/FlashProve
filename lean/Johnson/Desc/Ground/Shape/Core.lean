-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Ground/Shape/Core.lean: THE SHAPE OF WHAT THE GROUND's PLAIN FUNCTIONS WRITE: what is
left of a statement, a book of trees and a count of roots (`Core`, Johnson/Desc/CoreKeeps.lean)
when every field element is left out: numbers, flags and lists of these. Types, readers and small
laws on the readers. It stands over the library's ground alone: no kind, no chain, no frame for an
honest side.

What for. A verifier's step accepts where its guards on the structure pass and its tests on values
pass. The first half is to be written as a function of a shape that holds no field element, so that
it can be run without a proof.

The types. Each is a structure whose fields are listed here; none holds a field element.
  `OrcSh`   an oracle message: shape : OracleShape · sampled : Bool · rows : Nat (the NUMBER of its
      sample rows) · pad : List (Part × Nat) · groups : List Nat · ledger : Option Ledger · spent :
      Bool.
  `GrpSh`   a group: code, maskCode : Nat · members : List Nat · kept : List Bool · kinds : List
      RowKind (its open rows BY KIND, in their order) · inRun : Bool.
  `StSh`   a statement: codes : Codes · oracles : List OrcSh · groups : List GrpSh.
  `SrcSh`   where a tree's root is taken from: own n | given (without the two values).
  `TreeSh`   a tree: shape : TreeShape · number : Nat · src : SrcSh · parts : List Nat · oneList :
      Bool · lists : Nat.
  `BookSh`   trees : List TreeSh · place : List (Nat × Nat).
  `CoreSh`   st : StSh · book : BookSh · roots : Nat.
  Taken as they lie (OnBytes/Iop/Ground.lean): `Code`, `OracleShape`, `Ledger`, `TreeShape`: made
  of Nat, Bool and arrays of Nat; `Codes`: arrays of `Code`; `Part`, `RowKind`: enumerations.

WHAT IS NOT IN THE SHAPE. A row's summands (terms, single entries, runs, whole coefficient vectors)
and its target. Not even their number: the number of a row's terms can hang on a value
(`tensorBelow`, OnBytes/Iop/Tensor.lean, has two short cuts that ask whether an element is 0). NO
Bool THAT IS MADE FROM THE ROWS IS A FIELD EITHER: what guards ask of all summands of all rows
stands in two readers of their own, beside the shape (Johnson/Desc/Ground/Shape/Marks.lean).

Main names. `orcSh`, `grpSh`, `stSh`, `srcSh`, `treeSh`, `bookSh`, `coreSh`: the readers.
`orc_get`, `grp_get`, `tree_get`, `place_get`, the sizes: a reader at one member. `modAt`,
`map_modify`, `modAt_get`, `modAt_modAt`: a change of one member of an array, seen through a
reader.

Limits. That a shape is blind to what is sent and sampled is so by type for field elements alone: a
number can still be made of a value. `modAt` and `map_modify` have their like in a file on the
first chain's shape, which imports files on that chain; they are laid here so that this file
imports none. Nothing is evaluated here. Nothing on completeness, on soundness or on what is
hidden.


-/
import Johnson.Desc.CoreKeeps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Ground.Sh
open OnBytes

/-! ## 1 The types -/

/-- An oracle message without its sample rows' summands. -/
structure OrcSh where
  shape : OracleShape
  sampled : Bool
  rows : Nat
  pad : List (Part × Nat)
  groups : List Nat
  ledger : Option Ledger
  spent : Bool
  deriving DecidableEq, Repr

/-- A group with its open rows by kind. -/
structure GrpSh where
  code : Nat
  maskCode : Nat
  members : List Nat
  kept : List Bool
  kinds : List RowKind
  inRun : Bool
  deriving DecidableEq, Repr

/-- A statement. -/
structure StSh where
  codes : Codes
  oracles : List OrcSh
  groups : List GrpSh
  deriving DecidableEq, Repr

/-- Where a tree's root is taken from, without the two values. -/
inductive SrcSh where
  | own (n : Nat)
  | given
  deriving DecidableEq, Repr

structure TreeSh where
  shape : TreeShape
  number : Nat
  src : SrcSh
  parts : List Nat
  oneList : Bool
  lists : Nat
  deriving DecidableEq, Repr

structure BookSh where
  trees : List TreeSh
  place : List (Nat × Nat)
  deriving DecidableEq, Repr

/-- **The shape of statement, book and count of roots.** -/
structure CoreSh where
  st : StSh
  book : BookSh
  roots : Nat
  deriving DecidableEq, Repr

/-! ## 2 The readers -/

def orcSh (x : Oracle) : OrcSh :=
  ⟨x.shape, x.sampled, x.sampleRows.size, x.pad, x.groups, x.ledger, x.spentAsMask⟩

def grpSh (G : Group) : GrpSh :=
  ⟨G.code, G.maskCode, G.members.toList, G.kept.toList, G.rows.toList.map (·.kind), G.inRun⟩

def stSh (S : Statement) : StSh :=
  ⟨S.codes, S.oracles.toList.map orcSh, S.groups.toList.map grpSh⟩

def srcSh : Fmt.Src → SrcSh
  | .own n => .own n
  | .given _ _ => .given

def treeSh (T : Tree) : TreeSh :=
  ⟨T.shape, T.number, srcSh T.src, T.parts.toList, T.oneList, T.lists⟩

def bookSh (B : TreeBook) : BookSh := ⟨B.trees.toList.map treeSh, B.place.toList⟩

/-- **The reader.** -/
def coreSh (T : Core) : CoreSh := ⟨stSh T.st, bookSh T.book, T.roots⟩

/-! ## 3 A reader at one member -/

theorem map_get {α β : Type} (a : Array α) (f : α → β) (i : Nat) :
    (a.toList.map f)[i]? = (a[i]?).map f := by
  rw [List.getElem?_map, Array.getElem?_toList]

theorem orc_get (S : Statement) (o : Nat) : (stSh S).oracles[o]? = (S.oracles[o]?).map orcSh :=
  map_get _ _ _

theorem grp_get (S : Statement) (g : Nat) : (stSh S).groups[g]? = (S.groups[g]?).map grpSh :=
  map_get _ _ _

theorem tree_get (B : TreeBook) (t : Nat) : (bookSh B).trees[t]? = (B.trees[t]?).map treeSh :=
  map_get _ _ _

theorem place_get (B : TreeBook) (o : Nat) : (bookSh B).place[o]? = B.place[o]? :=
  Array.getElem?_toList

theorem orc_size (S : Statement) : (stSh S).oracles.length = S.oracles.size := by
  show (S.oracles.toList.map orcSh).length = _
  rw [List.length_map, Array.length_toList]

theorem grp_size (S : Statement) : (stSh S).groups.length = S.groups.size := by
  show (S.groups.toList.map grpSh).length = _
  rw [List.length_map, Array.length_toList]

theorem tree_size (B : TreeBook) : (bookSh B).trees.length = B.trees.size := by
  show (B.trees.toList.map treeSh).length = _
  rw [List.length_map, Array.length_toList]

theorem place_size (B : TreeBook) : (bookSh B).place.length = B.place.size := Array.length_toList

/-! ## 4 A change of one member of a list -/

/-- The list with f laid on member number i; a number outside the list changes nothing. -/
def modAt {α : Type} (l : List α) (i : Nat) (f : α → α) : List α :=
  l.zipIdx.map fun x => if x.2 = i then f x.1 else x.1

/-- A change of one member of an array, seen through a reader. -/
theorem map_modify {α β : Type} (a : Array α) (i : Nat) (f : α → α) (sh : α → β) (g : β → β)
    (h : ∀ x, sh (f x) = g (sh x)) :
    (a.modify i f).toList.map sh = modAt (a.toList.map sh) i g := by
  refine List.ext_getElem (by simp [modAt]) fun j j1 j2 => ?_
  simp only [modAt, List.getElem_map, List.getElem_zipIdx, Array.getElem_toList,
    Array.getElem_modify, Nat.zero_add]
  by_cases e : i = j
  · rw [if_pos e, if_pos e.symm, h]
  · rw [if_neg e, if_neg fun a => e a.symm]

theorem modAt_get {α : Type} (l : List α) (i : Nat) (f : α → α) :
    (modAt l i f)[i]? = (l[i]?).map f := by
  unfold modAt
  rw [List.getElem?_map, List.getElem?_zipIdx]
  cases l[i]? with
  | none => rfl
  | some x => simp

theorem modAt_modAt {α : Type} (l : List α) (i : Nat) (f g : α → α) :
    modAt (modAt l i f) i g = modAt l i fun x => g (f x) := by
  refine List.ext_getElem (by simp [modAt]) fun j j1 j2 => ?_
  simp only [modAt, List.getElem_map, List.getElem_zipIdx, Nat.zero_add]
  by_cases e : j = i
  · rw [if_pos e, if_pos e, if_pos e]
  · rw [if_neg e, if_neg e, if_neg e]

end VerifiableInference.Desc.Ground.Sh

#print axioms VerifiableInference.Desc.Ground.Sh.map_get
#print axioms VerifiableInference.Desc.Ground.Sh.orc_get
#print axioms VerifiableInference.Desc.Ground.Sh.grp_get
#print axioms VerifiableInference.Desc.Ground.Sh.tree_get
#print axioms VerifiableInference.Desc.Ground.Sh.place_get
#print axioms VerifiableInference.Desc.Ground.Sh.orc_size
#print axioms VerifiableInference.Desc.Ground.Sh.grp_size
#print axioms VerifiableInference.Desc.Ground.Sh.tree_size
#print axioms VerifiableInference.Desc.Ground.Sh.place_size
#print axioms VerifiableInference.Desc.Ground.Sh.map_modify
#print axioms VerifiableInference.Desc.Ground.Sh.modAt_get
#print axioms VerifiableInference.Desc.Ground.Sh.modAt_modAt
