-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Desc/Lots/H1Row.lean.
WHAT IT DOES NOT SHOW. No soundness. NO EXAMPLE OF THE HEAD IS SHOWN IN THIS FILE; two, at storedPublicFiles and
at zGap alone, are AtFullSide.Top.headMember_zFull and headMember_zGap, whose own Limits say what
they are worth. This is one lot's row
toward one. ALL THAT IS "AT THE RELEASE's FILES" IS STILL OWED: by h1_row_iff the row at the written
values says just that G has 25 built segments and a vocabulary of at least two entries: neither is
shown here of any public files. Nothing on the other lot of p4Pure (K6's). That the places' names
(the spots') give "H:1" at this place is another's.
WHAT A SKELETON IS BLIND TO, BY ITS MAKE: the block's decision; the round's entry ("REPLY", 24
bytes); THE GUARD (skel_guarded erases it: without "guarded sameReply" the row would be proved the
same); the argument of the step that enters the head's segment (G.W.H.tl). WHERE A WRONG LOT WOULD
BITE: a round more, another name, place or piece, a claim, a second block, letters, still, a
batching supplied: h1_lotSk would not compile.
WHAT THE CLOSED FACTS COUNT FOR: LITTLE. NOBODY SPENDS h1_written: back_of_skel spends the lots'
skeletons, Steady and four closed facts of its own. ROW 338 OF THE WRITTEN TABLE IS NOT THIS LOT's
BLOCK's ROW: the flat list's block there is the base's block (its name from the spot) joined to the
frame found behind it; the six columns agree because that frame is quiet. AND THE WRITTEN TABLE IS
NO INDEPENDENT WITNESS: by its own head it was printed by a program off ProofFile.onlineDescription at the goals'
stored full-size public files (VerifierAndGoals.storedPublicFiles), by Lean's evaluator, so off this very lot: were the
lot's text wrong, print and lot would be wrong alike; and NO THEOREM SAYS THAT THESE ARE THAT
VALUE's ROWS. They show that the written skeleton and the written table agree in six columns at one
row, and that this comparison can fail.
WORDS. "Skeleton": a block less its functions (Johnson/Desc/ProofFile/Law/Skel/Skel.lean).
"Lot": a named table of blocks from one module (ProofFile/LotCore.lean). "The written
table": cutFirstFull (Johnson/Desc/Ok/PlanWritten/CutLit.lean): 358 rows.
LETTERS. No "there is". G is general throughout. No scope, no opening, no pin is asked or spent.
OBJECT. The second of the two lots of ProofFile.p4Pure (ProofFile/Lots/PureLots.lean): the lot with the
one block at "H:1", the next token's place (K7): the guarded step that enters the head's segment,
joined to the kind's block (ProofFile/Lots/H1.lean: h1Own).
USER. The premises hk (one row a lot: the lots' skeletons are the written ones) and hS (Steady at
every lot) of ProofFile.Sk.back_of_skel (Law/Skel/SkelEnd.lean).
WHAT IT IS. h1Lot: that lot by name; p4Pure_two: p4Pure is K6's lot and this one, in a row. h1Skel l
ok, h1LotSk l ok: the written skeletons, at the head's segment's number l and the plan's test's
answer ok. skel_k7Core, skel_h1Front: the two halves' skeletons. h1_blocks: THE LOT HAS JUST ONE
BLOCK AT EVERY G, with the skeleton h1Skel (G.built.size - 1) (2 ≤ G.W.hS.V): OF G THE SKELETON
READS THESE TWO NUMBERS ALONE (the block itself reads G.W.H.tl too). h1_lotSk: so the lot's
skeleton, at every G: no hypothesis. h1_row_iff: THE ROW AT THE WRITTEN VALUES HOLDS JUST IF
G.built.size = 25 AND 2 ≤ G.W.hS.V: so it can fail, and its two hypotheses by field are no less than
the row. h1_row_at: the one direction, for a caller. h1_small: at a vocabulary below two the lot's
own block fails its test on the plan. h1_steady.
CLOSED FACTS, BY LEAN's KERNEL. h1_written: row number 338 of the written table is the written
skeleton's row. h1_once: just one row of the written table is of the kind K7. THE COMPARISON CAN
FAIL, AT EACH SORT OF COLUMN: h1_not_at23 (the place: 24 built segments); h1_not_beside (rows 337
and 339: the name); h1_not_two (two rounds); h1_not_named (the kind's own name "the next token" in
the place of the join's).

-/
import Johnson.Desc.ProofFile.Law.Skel.SkelEnd
import Johnson.Desc.ProofFile.Lots.PureLots
import Johnson.Desc.Ok.PlanWritten.CutLit
import Johnson.Desc.Ok.PlanWritten.CutTest

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Lots
open ProofFile ProofFile.Sk
open VerifiableInference.Desc (Block roundlessBlock)
open VerifiableInference.Desc.First (S)
open VerifiableInference.PlanWritten (cutFirstFull sameRow)

/-- **The lot with the one block at "H:1"**, as `ProofFile.p4Pure` writes it. -/
def h1Lot : Lot :=
  { name := "the next token (K7), with the step that enters the head's link"
    letters := false
    own := h1Own }

/-- `p4Pure` is K6's lot and this one, in a row. -/
theorem p4Pure_two (Z : Pub) : p4Pure Z = [P4.k6Lot Z, h1Lot] := rfl

/-- The block's written skeleton. l: the head's segment's number. ok: the plan's test's answer. -/
def h1Skel (l : Nat) (ok : Bool) : Skel :=
  { name := "H:1", place := ⟨1, some l, 1, .K7⟩, nRounds := 1, nOracles := 1, told := []
    before := [], planOk := ok, claims := [], after := [] }

/-- The lot's written skeleton. -/
def h1LotSk (l : Nat) (ok : Bool) : LotSk :=
  { name := "the next token (K7), with the step that enters the head's link"
    letters := false, still := [], blocks := [h1Skel l ok], batch := fun _ => none
    each := fun _ => false, tests := fun _ => false }

/-- The kind's own block's skeleton. -/
theorem skel_k7Core (G : Ground) : skel (P4.k7Core G) =
    { name := "the next token", place := ⟨1, some (G.built.size - 1), 1, .K7⟩, nRounds := 1
      nOracles := 1, told := [], before := [], planOk := decide (2 ≤ G.W.hS.V), claims := []
      after := [] } := rfl

/-- The skeleton of the step that enters the head's segment, under the kind's place. -/
theorem skel_h1Front (G : Ground) (f : S → Except String S) :
    skel ({ (roundlessBlock "H:1" 1 (some (G.built.size - 1)) 1 f : Block S Unit) with
      place := (P4.k7Core G).place }) =
    { Skel.quiet "H:1" 1 (some (G.built.size - 1)) 1 with
      place := ⟨1, some (G.built.size - 1), 1, .K7⟩ } := rfl

/-- **The lot has just one block at every G; of G that block's skeleton reads two numbers
alone.** -/
theorem h1_blocks (G : Ground) :
    (h1Lot.blocks G).map skel = [h1Skel (G.built.size - 1) (decide (2 ≤ G.W.hS.V))] := by
  have e : h1Lot.blocks G =
      [((({ (roundlessBlock "H:1" 1 (some (G.built.size - 1)) 1
          (VerifiableInference.Desc.First.K2.headFrontQ G.W.H.tl) : Block S Unit) with
          place := (P4.k7Core G).place } : Block S Unit).guarded sameReply
        fun _ => false).andThen "H:1" (P4.k7Core G)).retype] := rfl
  rw [e, List.map_cons, List.map_nil, skel_retype, skel_andThen, skel_guarded, skel_h1Front,
    skel_k7Core]
  simp [Skel.andThen, Skel.retype, Skel.quiet, h1Skel]

/-- **The lot's skeleton, at every G.** -/
theorem h1_lotSk (G : Ground) :
    lotSk G h1Lot = h1LotSk (G.built.size - 1) (decide (2 ≤ G.W.hS.V)) := by
  unfold lotSk h1LotSk
  rw [h1_blocks]
  rfl

/-- **THE ROW AT THE WRITTEN VALUES HOLDS JUST IF G HAS 25 BUILT SEGMENTS AND A VOCABULARY OF AT
LEAST TWO ENTRIES.** -/
theorem h1_row_iff (G : Ground) :
    lotSk G h1Lot = h1LotSk 24 true ↔ (G.built.size = 25 ∧ 2 ≤ G.W.hS.V) := by
  rw [h1_lotSk]
  constructor
  · intro h
    have h1 : h1Skel (G.built.size - 1) (decide (2 ≤ G.W.hS.V)) = h1Skel 24 true :=
      (List.cons.inj (congrArg LotSk.blocks h)).1
    have e : G.built.size - 1 = 24 :=
      Option.some.inj (congrArg (fun k : Skel => k.place.link) h1)
    exact ⟨by omega, of_decide_eq_true (congrArg (fun k : Skel => k.planOk) h1)⟩
  · rintro ⟨hb, hV⟩
    have e : G.built.size - 1 = 24 := by omega
    rw [e, decide_eq_true hV]

/-- The one direction, for a caller: the row at two hypotheses by field. -/
theorem h1_row_at (G : Ground) (hb : G.built.size = 25) (hV : 2 ≤ G.W.hS.V) :
    lotSk G h1Lot = h1LotSk 24 true := (h1_row_iff G).2 ⟨hb, hV⟩

/-- **At a vocabulary below two the lot's own block fails its test on the plan.** -/
theorem h1_small (G : Ground) (h : G.W.hS.V < 2) :
    (lotSk G h1Lot).blocks.all (·.planOk) = false := by
  rw [h1_lotSk, decide_eq_false (by omega)]
  rfl

/-- The lot supplies no batching: it is steady. -/
theorem h1_steady (G : Ground) : Steady G h1Lot := steady_none G h1Lot fun _ => rfl

/-! ## Closed facts, by evaluation in Lean's kernel -/

/-- Row number n of the written table is the row of the skeleton k. -/
def rowIsB (n : Nat) (k : Skel) : Bool := (cutFirstFull[n]?).any fun r => sameRow r k.row

set_option maxRecDepth 1000000 in
/-- **Row number 338 of the written table is the written skeleton's row.** -/
theorem h1_written : rowIsB 338 (h1Skel 24 true) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- Just one row of the written table is of the kind K7. -/
theorem h1_once : (cutFirstFull.filter fun r => decide (r.2.1.kind = .K7)).length = 1 := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The comparison can fail, at the place: with 24 built segments the row is another. -/
theorem h1_not_at23 : rowIsB 338 (h1Skel 23 true) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The comparison can fail, at the name: the rows beside are other rows. -/
theorem h1_not_beside :
    (rowIsB 337 (h1Skel 24 true) || rowIsB 339 (h1Skel 24 true)) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The comparison can fail, at a count: with two rounds. -/
theorem h1_not_two : rowIsB 338 { h1Skel 24 true with nRounds := 2 } = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The comparison can fail, at the name alone: under the kind's own name. -/
theorem h1_not_named : rowIsB 338 { h1Skel 24 true with name := "the next token" } = false := by
  decide +kernel

end Johnson.AtFull.Lots

#print axioms Johnson.AtFull.Lots.p4Pure_two
#print axioms Johnson.AtFull.Lots.skel_k7Core
#print axioms Johnson.AtFull.Lots.skel_h1Front
#print axioms Johnson.AtFull.Lots.h1_blocks
#print axioms Johnson.AtFull.Lots.h1_lotSk
#print axioms Johnson.AtFull.Lots.h1_row_iff
#print axioms Johnson.AtFull.Lots.h1_row_at
#print axioms Johnson.AtFull.Lots.h1_small
#print axioms Johnson.AtFull.Lots.h1_steady
#print axioms Johnson.AtFull.Lots.h1_written
#print axioms Johnson.AtFull.Lots.h1_once
#print axioms Johnson.AtFull.Lots.h1_not_at23
#print axioms Johnson.AtFull.Lots.h1_not_beside
#print axioms Johnson.AtFull.Lots.h1_not_two
#print axioms Johnson.AtFull.Lots.h1_not_named
