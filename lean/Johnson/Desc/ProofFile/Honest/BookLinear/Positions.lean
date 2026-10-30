-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/BookLinear/Positions.lean: WHERE AN ORDER OF PLACES HAS NO PLACE
TWICE, AND A FUNCTION g NAMES THE POSITIONS OF TWO ADDRESSES' PLACES IN IT (placedAt: a test),
Addr.before (Honest/Frame.lean) AT THAT ORDER IS A COMPARISON OF g's NUMBERS, AND OF THE TWO PARTS'
NUMBERS WHERE g's AGREE (beforeG). GENERAL IN g: nothing is asked of it: where g is wrong at a
place, placedAt refuses there. Two definitions with code; two statements with their proofs; two
closed facts on small orders. Written by the authors of the honest side of the linear claim's shared
rounds (K14), in the frame's folder, not by the frame's authors; Addr and Addr.before are the
frame's (Honest/Frame.lean); Place is the library's (Johnson/Desc/Block.lean).

  placedAt g all p   the test: at the position g p of the order all stands p
  beforeG g a b   Addr.before's text with g's numbers for the two walks along the order, and for the
    comparison of the two places
  findIdx_of_placed   **where all has no place twice and placedAt g all p accepts: the first
                  position at which p stands is g p, and all holds p** (the second half wants no "no
                  place twice"; nothing here spends it: it is meant for the fifth test, which asks
                  "contains")
  before_of_placed   **where all has no place twice and placedAt accepts at both places: a.before
                  all b = beforeG g a b**: the two walks by findIdx_of_placed; the two places are
                  equal just where g's numbers are (if the places are equal, so are the numbers: g
                  is a function; if the numbers are equal, both places stand at that one position)

What it is for. Addr.before walks the order twice at each call and compares places at each step; the
fifth test of ProverCoinCounts.clauses calls it at every entry, the eighth at every pair of a spending entry and
another entry that shares a coin with it. By these laws a test can go by numbers, and walk to each
place's position once, without a comparison on the way. No such test stands here.

That the order of a description has no place twice: the frame's orderOf_nodup
(Honest/Law/Rule/Tests.lean), under its test placesOk. It is not called here: "no place twice" is a
premise.

Kin. THE NEAREST, OF findIdx_of_placed: the frame's findIdx_at (Honest/Law/Rule/Tests.lean): "Behind
a stretch that does not hold x, x's first index is the stretch's length": the first position of a
member, as a number, at an order that is split at the member; with it findIdx_lt (the same file) and
findIdx_ge (Honest/Law/Rule/Lent.lean). It is not called: it wants the order split at the place,
where here a test "at position g p stands p" is at hand: Mathlib's List.Nodup.idxOf_getElem takes
the position. LAWS WITH A CLAUSE ON Addr.before: the frame's Addr.before_irrefl (no premise),
Addr.before_asymm, Addr.before_of_split, Addr.before_same (under i < j on the parts' numbers),
ProverCoinCounts.behind (the fifth test drawn out of a book's return) (all Honest/Law/Rule/Tests.lean);
Addr.not_before (Honest/Law/Rule/Lent.lean); before_places (Honest/Law/Rule/Order.lean: under "no
place twice", at an order split in two: a place of the first stretch stands before a place of the
second); RowOk.before_front, RowOk.before_back (Honest/Law/Rule/Items.lean). Of the linear claim's
kind: addr_not_before (Honest/K14/BookMakers.lean), fold_not_before and maskCarriers_all
(Honest/K14/BookAtU.lean), fold_in_front (Honest/K14/BookAtUHead.lean), spent_not_known
(Honest/K14/OwnerWhole.lean), carriers_u_written (Honest/K14/SharedAheadOwners.lean). IN EACH THE
CLAUSE ON Addr.before IS "… = true" OR "… = false"; NONE HAS A NUMBER FOR A PLACE.

Limits. THE PREMISE "NO PLACE TWICE" IS NEEDED: twice_needed: at an order that holds a place twice,
a g that names the second of the two positions passes placedAt, and Addr.before and beforeG differ.
What g is to be at a description's order is not said. Nothing on what an evaluation costs. Nothing
on any book; nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.Frame

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Place)

/-- g names the place's position in the order. -/
def placedAt (g : Place → Nat) (all : List Place) (p : Place) : Bool := all[g p]? == some p

/-- `Addr.before`, by positions. -/
def beforeG (g : Place → Nat) (a b : Addr) : Bool :=
  decide (g a.place < g b.place) || (g a.place == g b.place && decide (a.part < b.part))

/-- **Where the order has no place twice and g is right at p**: the first position at which p stands
is g p; and the order holds p. -/
theorem findIdx_of_placed {g : Place → Nat} {all : List Place} (hn : all.Nodup) {p : Place}
    (h : placedAt g all p = true) : all.findIdx (· == p) = g p ∧ all.contains p = true := by
  have h' : all[g p]? = some p := beq_iff_eq.1 h
  obtain ⟨i, e⟩ := List.getElem?_eq_some_iff.1 h'
  refine ⟨?_, List.contains_iff_mem.2 (e ▸ List.getElem_mem i)⟩
  have := hn.idxOf_getElem (g p) i
  rw [e] at this
  exact this

/-- **Where the order has no place twice and g is right at both places: Addr.before is beforeG.** -/
theorem before_of_placed {g : Place → Nat} {all : List Place} (hn : all.Nodup) {a b : Addr}
    (ha : placedAt g all a.place = true) (hb : placedAt g all b.place = true) :
    a.before all b = beforeG g a b := by
  unfold Addr.before beforeG
  rw [(findIdx_of_placed hn ha).1, (findIdx_of_placed hn hb).1]
  have e : (a.place == b.place) = (g a.place == g b.place) := by
    by_cases c : a.place = b.place
    · rw [c, beq_self_eq_true, beq_self_eq_true]
    · have c' : g a.place ≠ g b.place := by
        intro q
        have h1 : all[g a.place]? = some a.place := beq_iff_eq.1 ha
        have h2 : all[g b.place]? = some b.place := beq_iff_eq.1 hb
        rw [q, h2] at h1
        exact c (Option.some.inj h1).symm
      rw [beq_eq_false_iff_ne.2 c, beq_eq_false_iff_ne.2 c']
  rw [e]

/-! ## A small order: what placedAt must accept and refuse; that "no place twice" is needed -/

/-- placedAt: a right g: yes; a g that is one off: no; a place that the order does not hold: no. -/
theorem placedAt_small :
    placedAt (fun p => p.piece) [⟨1, none, 0, .K1⟩, ⟨1, none, 1, .K2⟩] ⟨1, none, 1, .K2⟩ = true ∧
    placedAt (fun p => p.piece + 1) [⟨1, none, 0, .K1⟩, ⟨1, none, 1, .K2⟩] ⟨1, none, 0, .K1⟩ = false
      ∧
    placedAt (fun p => p.piece) [⟨1, none, 0, .K1⟩, ⟨1, none, 1, .K2⟩] ⟨1, none, 1, .K3⟩ = false :=
      by
  decide +kernel

/-- **"No place twice" is needed**: the order holds its first place again at position 2; g names
that position; placedAt accepts at both places; Addr.before says yes and beforeG no. -/
theorem twice_needed :
    placedAt (fun p => 2 - p.piece) [⟨1, none, 0, .K1⟩, ⟨1, none, 1, .K2⟩, ⟨1, none, 0, .K1⟩]
      ⟨1, none, 0, .K1⟩ = true ∧
    placedAt (fun p => 2 - p.piece) [⟨1, none, 0, .K1⟩, ⟨1, none, 1, .K2⟩, ⟨1, none, 0, .K1⟩]
      ⟨1, none, 1, .K2⟩ = true ∧
    Addr.before [⟨1, none, 0, .K1⟩, ⟨1, none, 1, .K2⟩, ⟨1, none, 0, .K1⟩] ⟨⟨1, none, 0, .K1⟩, 0⟩
      ⟨⟨1, none, 1, .K2⟩, 0⟩ = true ∧
    beforeG (fun p => 2 - p.piece) ⟨⟨1, none, 0, .K1⟩, 0⟩ ⟨⟨1, none, 1, .K2⟩, 0⟩ = false := by
  decide +kernel

end ProofFile.Honest

#print axioms ProofFile.Honest.findIdx_of_placed
#print axioms ProofFile.Honest.before_of_placed
#print axioms ProofFile.Honest.placedAt_small
#print axioms ProofFile.Honest.twice_needed
