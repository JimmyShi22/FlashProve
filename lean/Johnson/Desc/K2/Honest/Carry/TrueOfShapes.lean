-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K2/Honest/Carry/TrueOfShapes.lean: UNDER THE LIBRARY's `ShapesAre`
(Johnson/Desc/First/Close/Law/LayoutOfShapes.lean) THE CLOSED GROUP's MEMBERS AT THEIR TRUE SHAPES
(`membersTrue`, Carry/OfRows.lean) ARE A WRITTEN LIST's MEMBERS WITH ITS FLAGS. Two statements with
their proofs; no definition.

  `shapesAre_grown` `ShapesAre T G lo kb no` stays where the statement grows (`Grows T T'`,
                    Johnson/Desc/Grows.lean), at the same group G: its first two clauses read G
                    alone; a message's shape stays
  `membersTrue_of_shapes` `ShapesAre T G lo kb no` · the carried rows' layout names G's members and
                    G's flags ⊢ `membersTrue T old` is `(membersOf lo).map fun i => ⟨(lo.get i).1,
                    kb i⟩`: the numbering `no` drops out

NEAR, NOT CALLED: `shapesAre_move` (Johnson/Desc/First/Close/Law/ShapesFiveOfSix.lean): the sentence
moved between two LISTS at one statement · `shapesAre_begun`
(Johnson/Desc/First/Close/Law/ShapesBegun.lean): the sentence at `begun T g G` and `begunGroup G`:
one step of a statement's growing, with the group's record turned with it.

Limits. `ShapesAre` is a premise: shown of no state here. G need not stand in the grown statement.
Nothing on rows' entries. Nothing on any property.
-/
import Johnson.Desc.K2.Honest.Carry.OfRows
import Johnson.Desc.First.Close.Law.LayoutOfShapes
import Johnson.Desc.Grows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest
open OnBytes
open VerifiableInference.Desc (Grows)
open VerifiableInference.Desc.First.Close (ShapesAre membersOf)

/-- `ShapesAre` stays where the statement grows. -/
theorem shapesAre_grown {T T' : Statement} (hg : Grows T T') {G : Group}
    {lo : List (OracleShape × ℕ)} {kb : Fin lo.length → Bool} {no : Fin lo.length → ℕ}
    (H : ShapesAre T G lo kb no) : ShapesAre T' G lo kb no := by
  refine ⟨H.members, H.kept, fun i hi => ?_⟩
  have h := H.shape i hi
  cases hx : T.oracles[no i]? with
  | none =>
    rw [hx] at h
    cases h
  | some x =>
    rw [hx] at h
    obtain ⟨x', hx', e, -⟩ := hg.2.2 _ x hx
    rw [hx']
    show some x'.shape = _
    rw [e]
    exact h

/-- **The members at their true shapes are the written list's**, where the carried rows' layout
names the group's members and flags. -/
theorem membersTrue_of_shapes {T : Statement} {G : Group} {lo : List (OracleShape × ℕ)}
    {kb : Fin lo.length → Bool} {no : Fin lo.length → ℕ} (H : ShapesAre T G lo kb no)
    (old : SingleRows) (hm : old.layout.members = G.members) (hk : old.layout.kept = G.kept) :
    membersTrue T old = (membersOf lo).map fun i => ⟨(lo.get i).1, kb i⟩ := by
  unfold membersTrue
  rw [hm, hk, Array.toList_zip, H.members, H.kept, List.zip_map', List.map_map]
  refine List.map_congr_left fun i hi => ?_
  have h := H.shape i hi
  show (⟨(T.oracles.getD (no i) default).shape, kb i⟩ : GroupMember) = _
  rw [Array.getD_eq_getD_getElem?]
  cases hx : T.oracles[no i]? with
  | none =>
    rw [hx] at h
    cases h
  | some x =>
    rw [hx] at h
    have e : x.shape = (lo.get i).1 := Option.some.inj h
    show (⟨x.shape, kb i⟩ : GroupMember) = _
    rw [e]

end VerifiableInference.Desc.K2.Honest

#print axioms VerifiableInference.Desc.K2.Honest.shapesAre_grown
#print axioms VerifiableInference.Desc.K2.Honest.membersTrue_of_shapes
