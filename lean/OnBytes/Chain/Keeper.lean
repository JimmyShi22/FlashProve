-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Chain/Keeper.lean: what a way to keep the record of vertices must do.

The strict reader (`Fmt.readChainX`, the reader of one chain's bytes) keeps, for each root's 32
bytes, the tree vertices that it has met under that root (format page, R7.14). By that rule the
root's own value is not entered, and only what an accepted opening shows is entered. Both are the
caller's matter (`storedK` and `opensK` in OnBytes/Chain/Engine.lean), not a keeper's.
Fmt/ keeps the vertices in a list (`Fmt.Seen`) and enters an opening's vertices
with `Fmt.addSeen`, which compares each new vertex with each old one. A program wants a faster
way. A `Keeper` is any way to keep the record that can be read back as the list and that enters
vertices as `Fmt.addSeen` does.
C++ counterpart: TreeValues in blocks/tree/tree.h.
The format page is docs/format/FORMAT.md. A number such as R7.14 is a rule of that page.

Main definitions: `Met`, `Keeper`, `Keeper.list`.
-/
import Fmt.Rules8X

namespace OnBytes

/-- A vertex as it was met: its depth, its place within that depth, its value. -/
abbrev Met : Type := Nat × Nat × ByteArray

/-- A way to keep the record of vertices in a value of type R. -/
structure Keeper (R : Type) where
  /-- the record as the list of Fmt/ -/
  toSeen : R → Fmt.Seen
  /-- the record that holds a given list -/
  ofSeen : Fmt.Seen → R
  /-- enters the vertices of one accepted opening under a root; nothing if a new vertex differs in
  value from an old one at the same depth and place under that root. By `toSeen_add` the new
  vertices are not compared with each other -/
  add : ByteArray → List Met → R → Option R
  /-- reading back gives the list that was put in -/
  toSeen_ofSeen : ∀ (s : Fmt.Seen), toSeen (ofSeen s) = s
  /-- entering is `Fmt.addSeen` -/
  toSeen_add : ∀ (root : ByteArray) (new : List Met) (r : R),
    (add root new r).map toSeen = Fmt.addSeen root new (toSeen r)

/-- The list of Fmt/ itself. -/
def Keeper.list : Keeper Fmt.Seen where
  toSeen := fun s => s
  ofSeen := fun s => s
  add := Fmt.addSeen
  toSeen_ofSeen := fun _ => rfl
  toSeen_add := fun root new r => by
    cases Fmt.addSeen root new r with
    | none => rfl
    | some _ => rfl

end OnBytes
