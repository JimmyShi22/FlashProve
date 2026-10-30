-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Look/K3LiveIs.lean: the kind "lookup" (K3): A FILLING OF THE TABLE OF JOINTS'
DOOR: THE PUBLIC ITEM «frame.liveIs» OF A SEGMENT: the live request's shape and its rows' layout are
the plan's. Its name, its rows (who makes, asks, drops it), its sentence, the sentence's Bool, and
what the lookups owe of it: that their blocks keep it. Definitions, statements and proofs. NO
SOUNDNESS IS CLAIMED.

Why. The lookups' condition in front asks that the state's own five are the caller's data's (OwnIs,
K3CallerOwn.lean). Two of the five, the live request's shape and its rows' layout, are read through
S.live, which inside a link is the link's own copy: a part of «here»: so they cannot be clauses of
Meaning.inOrder, which does not read that part (not shown here). They come through
the door.

Main names.
  liveName m := (some m, "frame.liveIs"); liveItem m: the item.
  liveMore: the door's filling: MADE at piece 1 + o of the segment (the block whose second half
    opens the link and copies the chain's check into it: not shown here), ASKED at
    the pieces of liveAskers o := [2 + o, 7 + o, 10 + 2 o, 13 + 2 o] (the two lookups; the closing's
    first block, the one equation; the frame's block «cleared»), DROPPED BY THE LAST OF THEM; o :=
    shift of the segment's sort. A later asker lengthens that one list.
  liveNameC, liveItemC, liveMoreChain: THE OTHER FORM, NOT TAKEN: one item
    (none, "frame.liveIs") for the whole chain: OPEN AT THE START, asked at the same pieces of every
    segment, made and dropped by no block, kept by all. THE TABLE TAKES THE FORM BY
    SEGMENT; this one is kept as a second test of the door.
  LiveIs D s: THE SENTENCE: s.live.frame.shape = D.shape ∧ s.live.rows.layout = D.layout.
  liveIsB D s: ITS Bool: the two types have a decidable equality (OnBytes/Params/Items.lean: both
    structures derive it): so the item can be said by Meaning.pub, as a Bool that a walk evaluates.
  liveIsB_iff.
  sameBut_live, liveIs_sameBut: whatever leaves what SameBut names (K3CallsTurns.lean) leaves
    S.live: so both lookups' yes keeps the item.
  liveFit_small, liveFit_full: the table's test pubFit says true at this filling at the two written
    lists of segments; liveFit_control: with the maker's row struck it says false.
    liveFitChain_small, _full, _control: the like for the other form (the control: nothing open at
    the start).
OBJECT. No block's text: the table's door (More, Johnson/Desc/First/Borders.lean) and the verifier's
state's reader S.live (State.lean).
USER. The lookups' two rows (fLive in K3DigitsRow.lean and its like at the calls); the one
equation's block's law. Of the maker's lemma at piece 1 + o: the files of the
block that opens the link.
LETTERS. D : Sent (the plan's data), m, s.
IS IT EMPTY? liveIsB ran true at 79 of 79 borders of an honest walk over the small stored set
(at another list of askers: open at 46, true at 46), with two controls
true at none.
(Where this and lean/THEOREM.md differ, the page holds.)
Limits. WHO MAKES IT TRUE (the block at piece 1 + o) AND WHO KEEPS IT BESIDE THE LOOKUPS is not
shown here.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Borders
import Johnson.Desc.First.Look.K3CallerOwn
import Johnson.Desc.First.Look.K3CallsTurns

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Look
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (ModelPart Pub More MoreRow MoreName moreItem shift pubFit
  flatPlacesOf)

/-- The item's name at segment m. -/
def liveName (m : Nat) : MoreName := (some m, "frame.liveIs")

/-- The item. -/
def liveItem (m : Nat) : Pub := moreItem (liveName m)

/-- **The pieces of a segment at which the item is asked, in their order; THE LAST ONE DROPS IT**:
the lookup on the calls, the lookup on the digits, the closing's first block (the one equation), the
frame's block "cleared" (it writes the link's live copy back into the chain's own check: so what
"in order" says of that check behind it is earned from this item in front). A LATER ASKER LENGTHENS
THIS LIST AND NOTHING ELSE. -/
def liveAskers (o : Nat) : List Nat := [2 + o, 7 + o, 10 + 2 * o, 13 + 2 * o]

/-- **The door's filling.** -/
def liveMore : More where
  rows links p :=
    match p.link with
    | some m =>
      match links[m]? with
      | none => {}
      | some sub =>
        let o := shift sub
        if p.piece == 1 + o then { makes := [liveName m] }
        else if (liveAskers o).getLast? == some p.piece then
          { asks := [liveName m], drops := [liveName m] }
        else if (liveAskers o).contains p.piece then { asks := [liveName m] }
        else {}
    | none => {}

/-- THE OTHER FORM THAT WAS PROPOSED, AND NOT TAKEN: ONE ITEM FOR THE WHOLE CHAIN. -/
def liveNameC : MoreName := (none, "frame.liveIs")

/-- That item. -/
def liveItemC : Pub := moreItem liveNameC

/-- **The door's filling in that form**: open at the chain's start; asked at the two lookups' places
of every segment; made and dropped by no block. -/
def liveMoreChain : More where
  rows links p :=
    match p.link with
    | some m =>
      match links[m]? with
      | none => {}
      | some sub =>
        let o := shift sub
        if (liveAskers o).contains p.piece then { asks := [liveNameC] } else {}
    | none => {}
  start := [liveNameC]

/-- **The sentence.** -/
def LiveIs (D : Sent) (s : First.S) : Prop :=
  s.live.frame.shape = D.shape ∧ s.live.rows.layout = D.layout

/-- **Its Bool.** -/
def liveIsB (D : Sent) (s : First.S) : Bool :=
  decide (s.live.frame.shape = D.shape) && decide (s.live.rows.layout = D.layout)

theorem liveIsB_iff (D : Sent) (s : First.S) : liveIsB D s = true ↔ LiveIs D s := by
  unfold liveIsB LiveIs
  simp only [Bool.and_eq_true, decide_eq_true_eq]

/-- What leaves what SameBut names leaves the live copy. -/
theorem sameBut_live {s s' : First.S} (h : VerifiableInference.OnPublicFiles.SameBut s s') :
    s'.live = s.live := by
  unfold First.S.live
  rw [h.link, h.check]

/-- **So it keeps the item.** -/
theorem liveIs_sameBut {D : Sent} {s s' : First.S}
    (h : VerifiableInference.OnPublicFiles.SameBut s s') (hL : LiveIs D s) : LiveIs D s' := by
  unfold LiveIs at hL ⊢
  rw [sameBut_live h]
  exact hL

/-- The two written lists of segments. -/
def liveSmall : List ModelPart := [.layers, .attention, .layers, .attention, .head]
def liveFull : List ModelPart :=
  (List.range 12).flatMap (fun _ => [ModelPart.layers, ModelPart.attention]) ++ [.head]

set_option maxRecDepth 100000 in
theorem liveFit_small : pubFit liveMore liveSmall (flatPlacesOf liveSmall true) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem liveFit_full : pubFit liveMore liveFull (flatPlacesOf liveFull true) = true := by
  decide +kernel

/-- The filling with the maker's row struck. -/
def liveMoreNoMaker : More where
  rows links p := { liveMore.rows links p with makes := [] }

set_option maxRecDepth 100000 in
/-- **A control**: without a maker the test rings. -/
theorem liveFit_control :
    pubFit liveMoreNoMaker liveSmall (flatPlacesOf liveSmall true) = false := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem liveFitChain_small :
    pubFit liveMoreChain liveSmall (flatPlacesOf liveSmall true) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem liveFitChain_full : pubFit liveMoreChain liveFull (flatPlacesOf liveFull true) = true := by
  decide +kernel

/-- That filling with nothing open at the start. -/
def liveMoreChainNoStart : More where
  rows := liveMoreChain.rows

set_option maxRecDepth 100000 in
/-- **A control**: where the item is not open at the start the test rings. -/
theorem liveFitChain_control :
    pubFit liveMoreChainNoStart liveSmall (flatPlacesOf liveSmall true) = false := by
  decide +kernel

end VerifiableInference.Desc.First.Look

#print axioms VerifiableInference.Desc.First.Look.liveFitChain_small
#print axioms VerifiableInference.Desc.First.Look.liveFitChain_full
#print axioms VerifiableInference.Desc.First.Look.liveFitChain_control
#print axioms VerifiableInference.Desc.First.Look.liveIsB_iff
#print axioms VerifiableInference.Desc.First.Look.liveIs_sameBut
#print axioms VerifiableInference.Desc.First.Look.liveFit_small
#print axioms VerifiableInference.Desc.First.Look.liveFit_full
#print axioms VerifiableInference.Desc.First.Look.liveFit_control
