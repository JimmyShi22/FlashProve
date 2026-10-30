-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/RoundsAtTags.lean: the second chain's description at the roots and run values that
were read, and at made-up names (`Three.tagChain`, OnBytes/Three/Data.lean), are the same rounds but
for the names of the trees taken over.

A second chain's block begins with the first chain's trees and takes over one tree of the shared
chain (OnBytes/Proof/Tail.lean). Its dry run notes these trees' names in the openings. A protocol's
description is fixed before any root is, so it is made at made-up names. This file calls the law
on dry runs (`second_rounds_alike`, OnBytes/TypedOracleCompiler/Laws/LawDry.lean) at these two readings.

  `srcAlike_any`, `bookAlike_any`   a source, and a book of trees, is alike to itself
  `alike_map`, `alike_stored`, `alike_entries`, `alike_kinds`, `alike_items`, `alike_items₂`,
  `alike_shapes`, `alike_length`   what two lists of rounds that are alike have in common, each as
        an equation of lists: the stored tables (`StoredAlike`, OnBytes/Maker/ReadSpecs.lean), the
        entries, the kinds, the items (also member by member), and each round's openings' shapes
        (so: as many openings a round)
  `secondRounds_tags_some`   where the description at what was read is there, the one at made-up
        names is there too, with these six equations
  `secondRounds_at_tags`   both lists of rounds are missing, or they are alike round by round
        (`RoundAlike`, OnBytes/TypedOracleCompiler/Laws/LawRun.lean): the same entry, kind and items; as many
        openings, of the same shapes, an own tree with the same own tree and a tree taken over with
        a tree taken over; the same stored tables

Not claimed. Which made-up name stands for which root. Nothing on a run on a view, on reading, or on
soundness.


-/
import OnBytes.Maker.Decide3Laws
import OnBytes.Maker.ReadSpecs

set_option autoImplicit false

namespace OnBytes.Maker

open OnBytes.Proof OnBytes.TwoLaws

/-- A source is alike to itself. -/
theorem srcAlike_any (s : Fmt.Src) : SrcAlike AnyGiven s s := by
  cases s with
  | own n => exact .own n
  | given r t => exact .given trivial

/-- A book of trees is alike to itself. -/
theorem bookAlike_any (B : TreeBook) : BookAlike AnyGiven B B :=
  ⟨fun i => by
    cases B.trees[i]? with
    | none => exact .none
    | some t => exact .some ⟨rfl, rfl, srcAlike_any _, rfl, rfl, rfl⟩, rfl⟩

/-- **The second chain's rounds at what was read, and at made-up names.** dry, end2: what the dry
runs of the first and of the shared chain's block have returned. -/
theorem secondRounds_at_tags (p : TailPublic) (dry : FirstEnd) (end2 : SharedEnd)
    (first shared : ChainRead) (n₂ : Nat) :
    OptAlike (LAlike (RoundAlike AnyGiven))
      ((secondBlock p.lin dry.lin (end2.goesOn shared)).rounds (secondStart p dry first))
      ((secondBlock p.lin dry.lin (end2.goesOn (Three.tagChain 2 n₂))).rounds
        (secondStart p dry (Three.tagChain 1 first.roots.length))) :=
  second_rounds_alike p ⟨rfl, bookAlike_any _, ⟨rfl, rfl, rfl, rfl⟩⟩ ⟨rfl, bookAlike_any _, rfl⟩
    first _ shared _ (fun n => treesOf_any _ _ n) (fun n => treesOf_any _ _ n)
    (tagChain_roots 1 _).symm

/-! ## What two lists of rounds that are alike have in common -/

section
variable {G : ByteArray → ByteArray → ByteArray → ByteArray → Prop}

/-- A function that does not tell two members that are alike apart gives one list. -/
theorem alike_map {α β : Type} {P : α → α → Prop} {l l' : List α} (h : LAlike P l l') (f : α → β)
    (hf : ∀ a b, P a b → f a = f b) : l.map f = l'.map f := by
  induction h with
  | nil => rfl
  | cons a _ ih => rw [List.map_cons, List.map_cons, hf _ _ a, ih]

variable {l l' : Params.Rounds} (h : LAlike (RoundAlike G) l l')
include h

/-- Round by round the same stored tables. -/
theorem alike_stored : StoredAlike l l' := alike_map h (·.2) fun _ _ k => k.stored

theorem alike_entries : l.map (·.1.entry) = l'.map (·.1.entry) :=
  alike_map h (·.1.entry) fun _ _ k => k.entry

theorem alike_kinds : l.map (·.1.kind) = l'.map (·.1.kind) :=
  alike_map h (·.1.kind) fun _ _ k => k.kind

theorem alike_items : l.map (·.1.items) = l'.map (·.1.items) :=
  alike_map h (·.1.items) fun _ _ k => k.items

/-- Round by round as many openings, of the same shapes. -/
theorem alike_shapes :
    l.map (fun x => x.1.opens.map (·.1)) = l'.map (fun x => x.1.opens.map (·.1)) :=
  alike_map h (fun x => x.1.opens.map (·.1)) fun _ _ k => alike_map k.opens (·.1) fun _ _ o => o.1

/-- The same as a relation between the two lists of rounds, member by member. -/
theorem alike_items₂ :
    List.Forall₂ (fun r r' : Fmt.Round => r.items = r'.items) (l.map (·.1)) (l'.map (·.1)) := by
  induction h with
  | nil => exact .nil
  | cons a _ ih => exact .cons a.items ih

theorem alike_length : l.length = l'.length := by
  have e := congrArg List.length (alike_entries h)
  rwa [List.length_map, List.length_map] at e

end

/-- **Where the second chain's description at what was read is there, the one at made-up names is
there too**, and the two have the same stored tables, entries, kinds, items and openings' shapes,
round by round. -/
theorem secondRounds_tags_some (p : TailPublic) (dry : FirstEnd) (end2 : SharedEnd)
    (first shared : ChainRead) (n₂ : Nat) (rounds3 : Params.Rounds)
    (h : (secondBlock p.lin dry.lin (end2.goesOn shared)).rounds (secondStart p dry first) =
      some rounds3) :
    ∃ R₃, (secondBlock p.lin dry.lin (end2.goesOn (Three.tagChain 2 n₂))).rounds
        (secondStart p dry (Three.tagChain 1 first.roots.length)) = some R₃ ∧
      StoredAlike rounds3 R₃ ∧ rounds3.map (·.1.entry) = R₃.map (·.1.entry) ∧
      rounds3.map (·.1.kind) = R₃.map (·.1.kind) ∧ rounds3.map (·.1.items) = R₃.map (·.1.items) ∧
      rounds3.map (fun x => x.1.opens.map (·.1)) = R₃.map (fun x => x.1.opens.map (·.1)) ∧
      rounds3.length = R₃.length := by
  have k := secondRounds_at_tags p dry end2 first shared n₂
  rw [h] at k
  generalize (secondBlock p.lin dry.lin (end2.goesOn (Three.tagChain 2 n₂))).rounds
    (secondStart p dry (Three.tagChain 1 first.roots.length)) = y at k
  cases k with
  | some q =>
    exact ⟨_, rfl, alike_stored q, alike_entries q, alike_kinds q, alike_items q, alike_shapes q,
      alike_length q⟩

end OnBytes.Maker
