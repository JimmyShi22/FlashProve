-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/PlacesAtChain.lean: THE SHARED CHAIN's FLAT LIST HAS JUST THE TABLE's PLACES,
IN THE TABLE's ORDER (placesFitS, sharedPlaces: Johnson/Desc/Shared/BordersShared.lean), WHERE THE
CHAIN's OWN BLOCKS PASS THEIR TESTS ON THE PLAN. The table's letter "split" is NOT free: it is laid
here as the shape's own flag, Q.S.sharedSplitNeeded, and under that premise the flag is true.

  own_places         the eight blocks' places, by the page's text: 1 … 8; K14 but for the two
                     sendings (K1).
  places_at_chainOf  **the field's fact at chainOf**: from hpl (every block of the flat list passes
                     its test on the plan), h9 (the two proximity tests' places) and h11 (the last
                     block's place).
  places_retype      a chain without links, carried to another type of claims, keeps its places.
  places_at_retype   the fact at the chain carried, as a description's fold lays it.
WHY hpl. blocksOr has a stand-by arm where the kind's blocks cannot be said: there the flat list is
another, and the fact is false. That arm's one block fails its test on the plan: blocks_said
(Johnson/Desc/K14/Law/SplitGiven.lean) bars it; split_at_the_chain gives the flag.
What is not claimed. h9 and h11 are the proximity test's files' facts. That a file's description
has this chain, carried, as its shared chain. That some plan passes. No soundness of a verifier.

-/
import Johnson.Desc.K14.Law.SplitGiven
import Johnson.Desc.K14.Law.FlatAt
import Johnson.Desc.Shared.BordersShared

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params Desc.Plain
open VerifiableInference.Desc (Block Place Chain)
open VerifiableInference.Desc.Shared (placesFitS sharedPlaces)

/-- The eight blocks' places. -/
theorem own_places (P : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8]) :
    [b1, b2, b3, b4, b5, b6, b7, b8].map (·.place) =
      [⟨2, none, 1, .K14⟩, ⟨2, none, 2, .K1⟩, ⟨2, none, 3, .K14⟩, ⟨2, none, 4, .K14⟩,
        ⟨2, none, 5, .K1⟩, ⟨2, none, 6, .K14⟩, ⟨2, none, 7, .K14⟩, ⟨2, none, 8, .K14⟩] := by
  unfold blocks at hb
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq,
    List.cons.injEq, and_true] at hb
  obtain ⟨_, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hb
  rfl

/-- **The shared chain's places are the table's.** -/
theorem places_at_chainOf (c : Model.Verify.Chains) (Q : P14) (tests : List (Block St Unit))
    (last : List (Block St Unit) → Block St Unit)
    (hpl : ∀ b ∈ (chainOf c Q tests last).blocksInOrder, b.planOk = true)
    (h9 : tests.map (·.place) = [⟨2, none, 9, .K12⟩, ⟨2, none, 10, .K12⟩])
    (h11 : (last (blocksOr Q ++ tests)).place = ⟨2, none, 11, .frame⟩) :
    Q.S.sharedSplitNeeded = true ∧
      placesFitS (chainOf c Q tests last) (sharedPlaces Q.S.sharedSplitNeeded) = true := by
  obtain ⟨l, hb⟩ := blocks_said c Q tests last hpl
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, rfl⟩ := eight Q l hb
  have hS := split_at_the_chain c Q tests last hpl
  refine ⟨hS, ?_⟩
  have hor : blocksOr Q = [b1, b2, b3, b4, b5, b6, b7, b8] := by simp [blocksOr, hb]
  rw [hor] at h11
  have hbare : ∀ l : List (Block St Unit), (l.map bareOf).map (·.place) = l.map (·.place) :=
    fun l => by
      rw [List.map_map]
      rfl
  have hp : (chainOf c Q tests last).blocksInOrder.map (·.place) = sharedPlaces true := by
    rw [flat_at c Q b1 b2 b3 b4 b5 b6 b7 b8 tests last hb, List.map_cons, List.map_append,
      own_places Q b1 b2 b3 b4 b5 b6 b7 b8 hb, hbare, List.map_append, h9, List.map_cons, h11]
    rfl
  rw [hS]
  unfold placesFitS
  rw [hp]
  exact beq_self_eq_true _

/-- A chain without links, carried to another type of claims, keeps its places. -/
theorem places_retype {S Cl Cl' : Type} (c : Chain S Cl) (h : c.links = []) :
    (c.retype (Cl' := Cl')).blocksInOrder.map (·.place) = c.blocksInOrder.map (·.place) := by
  simp [Chain.retype, Chain.blocksInOrder, h, Block.retype, Function.comp_def]

/-- **The fact at the chain carried to a description's type of claims.** -/
theorem places_at_retype {Cl' : Type} (c : Model.Verify.Chains) (Q : P14)
    (tests : List (Block St Unit)) (last : List (Block St Unit) → Block St Unit)
    (hpl : ∀ b ∈ (chainOf c Q tests last).blocksInOrder, b.planOk = true)
    (h9 : tests.map (·.place) = [⟨2, none, 9, .K12⟩, ⟨2, none, 10, .K12⟩])
    (h11 : (last (blocksOr Q ++ tests)).place = ⟨2, none, 11, .frame⟩) :
    placesFitS ((chainOf c Q tests last).retype (Cl' := Cl'))
      (sharedPlaces Q.S.sharedSplitNeeded) = true := by
  have h := (places_at_chainOf c Q tests last hpl h9 h11).2
  unfold placesFitS at h ⊢
  rw [places_retype _ rfl]
  exact h

end Desc.K14.Law
