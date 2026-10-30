-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Rounds/K7.lean.
WHAT IT DOES NOT SHOW. No soundness. NO EXAMPLE OF THE HEAD IS SHOWN IN THIS FILE; two, at storedPublicFiles and
at zGap alone, are AtFullSide.Top.headMember_zFull and headMember_zGap, whose own Limits say what
they are worth. This is one lot's second row toward one. THE SPOT's NAME IS NOT PAID HERE: that the
list of places names K7's place "H:1" is a premise (hn of h1_lists and h1_lists_scope; hN of
h1_lists_at): it hangs on the table of stretches, of which nothing is read here; IT IS SHOWN HERE AT
NO WRITTEN LIST OF PLACES AND AT NO FILES (h1Named_yes is at a made-up list of two spots: it shows
only that the test is not always "no"); and by h1_lists_can_fail the row IS FALSE where that place
bears the name beside. THAT ps HAS A SPOT AT THE PLACE IS NOT ASKED: at the empty list, and at every
list without that place, hn and h1NamedB are met and h1_lists and h1_lists_scope hold for nothing.
hS, hR, hZ, hG are spent for one number alone (25 built segments, so the place's segment is
24) and are paid here at no files. THE WRITTEN TABLE IS NO INDEPENDENT WITNESS: by the head of
Johnson/Unfolds/DeclRecsLit.lean its values were printed off ProofFile.onlineDescription at the goals' stored
full-size public files by Lean's evaluator, so off this very block: were the kind's round wrong,
print and block would be wrong alike. What h1_listAt shows is that the written list at the name
"H:1" and the kind's own text agree, and that this comparison can fail.
WORDS. "Lot": a named table of blocks from one module (Johnson/Desc/ProofFile/LotCore.lean). "Spot":
a place with its name and its rows of the table of stretches (Johnson/Desc/ProofFile/Places.lean).
"The written table": listAt (Johnson/AtFull/Rounds/ListAt.lean): a block's name to its declared
rounds. Lst T n r: r is empty or r is T n (Johnson/Desc/ProofFile/Law/Skel/SkelLists.lean).
LETTERS. No "there is". G is general but in h1_lists_scope and h1_lists_at.
ps: ANY list of spots: nothing ties it
to a file. lay is a free letter, as in H1RowScope.lean. At the second hash function OnBytes.secondHashFunction
alone. NO OPENING OF THE PROOF FILE, NO PIN, NO RETURN OF THE CHAIN IS ASKED OR SPENT.
OBJECT. The lot h1Lot (Johnson/AtFull/Desc/Lots/H1Row.lean): the one block at "H:1", the next
token's place (K7).
USER. The premise hL of ProofFile.Sk.back_good (Law/Skel/SkelRoundsParts.lean) at Q := Lst listAt, at this
lot, outright or through a law of that folder from rows by the place (h1_lists_at's form); its
premise hK at this lot holds for nothing (h1_no_batch).
WHAT IT IS. THE LAW. h1_block: AT EVERY G each block of the lot has the kind's own one declared
round (Reply.rounds: "REPLY", 24 bytes, nothing drawn) and K7's place in the last built segment: OF
G THE ROUNDS READ NOTHING; the place reads G.built.size alone. h1_one: the lot has just one block.
THE CLOSED FACT, BY LEAN's KERNEL. h1_listAt_yes, h1_listAt: the written list at "H:1" is that
round. THE ROW. h1_list: b.rounds = listAt "H:1", at
every G, under no premise. h1_lists: the same in hL's letters, under hn. h1NamedB: hn at segment 24
as a closed test on a list of spots; h1_lists_scope: the row from the scope, the reading, the two
returns and that test. h1_lists_at: the same by the place, at any table N of names by places with
N ‹K7's place in segment 24› = "H:1": the form "Lst listAt (N b.place) b.rounds".
THE COMPARISON (isListB: yes and no's on one function) CAN FAIL, AT EACH SORT: h1_listAt_not25,
h1_listAt_notCount (words of the entry); h1_listAt_notStored (beyond the entry: a stored tree);
h1_listAt_notRng (the entry's name); h1_listAt_notTwo (two rounds); h1_listAt_notBeside (the name
beside, "H:2"); h1_listAt_notKnown (a name that the table has not);
h1_listAt_notNone (no round: so the name stands in the table, and the row is not paid by the empty
arm). h1NamedB CAN FAIL: h1Named_no; at a made-up list it says yes: h1Named_yes.

-/
import Johnson.AtFull.Desc.Lots.H1RowScope
import Johnson.AtFull.Rounds.ListAt
import Johnson.Desc.ProofFile.Law.Skel.SkelLists

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Rounds
open ProofFile ProofFile.Sk
open VerifiableInference.Desc (Block Place roundlessBlock)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Kinds (Reply.rounds)
open Johnson.AtFull.Lots (h1Lot)

/-- **THE LAW. At every G each block of the lot has the kind's own one declared round, and K7's
place in the last built segment.** -/
theorem h1_block (G : Ground) : ∀ b ∈ h1Lot.blocks G,
    b.rounds = Reply.rounds ∧ b.place = ⟨1, some (G.built.size - 1), 1, .K7⟩ := by
  intro b hb
  have e : h1Lot.blocks G =
      [((({ (roundlessBlock "H:1" 1 (some (G.built.size - 1)) 1
          (VerifiableInference.Desc.First.K2.headFrontQ G.W.H.tl) : Block S Unit) with
          place := (P4.k7Core G).place } : Block S Unit).guarded sameReply
        fun _ => false).andThen "H:1" (P4.k7Core G)).retype] := rfl
  rw [e] at hb
  obtain rfl := List.mem_singleton.1 hb
  exact ⟨rfl, rfl⟩

/-- The lot has just one block, at every G. -/
theorem h1_one (G : Ground) : (h1Lot.blocks G).length = 1 := rfl

/-- The lot supplies no batching. -/
theorem h1_no_batch (G : Ground) (a : Place) : h1Lot.batch G a = none := rfl

/-! ## The closed fact, by evaluation in Lean's kernel -/

/-- The written list at the name n is r. -/
def isListB (n : String) (r : List Fmt.DeclaredRound) : Bool := decide (listAt n = r)

set_option maxRecDepth 1000000 in
/-- **The written list at "H:1" is the kind's own one declared round**: the test says yes. -/
theorem h1_listAt_yes : isListB "H:1" Reply.rounds = true := by
  decide +kernel

/-- The same as an equation. -/
theorem h1_listAt : listAt "H:1" = Reply.rounds :=
  of_decide_eq_true (p := listAt "H:1" = Reply.rounds) h1_listAt_yes

set_option maxRecDepth 1000000 in
/-- The comparison can fail, at a word of the entry: 25 bytes. -/
theorem h1_listAt_not25 : isListB "H:1" [{ entry := { name := "REPLY", msg := 25 } }] = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The comparison can fail, at another word of the entry: the count. -/
theorem h1_listAt_notCount :
    isListB "H:1" [{ entry := { name := "REPLY", count := 2, msg := 24 } }] = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The comparison can fail, beyond the entry: a stored tree is opened. -/
theorem h1_listAt_notStored : isListB "H:1"
    [{ entry := { name := "REPLY", msg := 24 }, stored := [⟨⟨32, 2048, true, 0⟩, 40, 0, 0, 64⟩] }] =
      false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The comparison can fail, at the entry's name. -/
theorem h1_listAt_notRng : isListB "H:1" [{ entry := { name := "RNG", msg := 24 } }] = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The comparison can fail, at the number of rounds. -/
theorem h1_listAt_notTwo : isListB "H:1" (Reply.rounds ++ Reply.rounds) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The comparison can fail, at the block's name: the name beside bears another list. -/
theorem h1_listAt_notBeside : isListB "H:2" Reply.rounds = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The comparison can fail, at a name that the table has not: it bears no round. -/
theorem h1_listAt_notKnown : isListB "H:0" Reply.rounds = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The written list at "H:1" is not empty. -/
theorem h1_listAt_notNone : isListB "H:1" [] = false := by
  decide +kernel

/-! ## The row -/

/-- **THE ROW, AT THE NAME: at every G, under no premise.** -/
theorem h1_list (G : Ground) : ∀ b ∈ h1Lot.blocks G, b.rounds = listAt "H:1" := fun b hb =>
  (h1_block G b hb).1.trans h1_listAt.symm

/-- **THE ROW, IN hL's LETTERS**, at any list of spots that names K7's place "H:1". -/
theorem h1_lists (G : Ground) (ps : List Spot)
    (hn : ∀ p ∈ ps, p.place = ⟨1, some (G.built.size - 1), 1, .K7⟩ → p.name = "H:1") :
    ∀ b ∈ h1Lot.blocks G, ∀ p ∈ ps, p.place = b.place → Lst listAt p.name b.rounds := by
  intro b hb p hp e
  rw [hn p hp (e.trans (h1_block G b hb).2)]
  exact Or.inr (h1_list G b hb)

/-- **Without hn the row is false**: at a spot that names the place "H:2": of the lot's one block
(h1_one). -/
theorem h1_lists_can_fail (G : Ground) : ∀ b ∈ h1Lot.blocks G, ¬ Lst listAt "H:2" b.rounds := by
  intro b hb h
  rw [(h1_block G b hb).1] at h
  rcases (h : Reply.rounds = [] ∨ Reply.rounds = listAt "H:2") with h | h
  · exact absurd (congrArg List.length h) (by decide)
  · exact of_decide_eq_false (p := listAt "H:2" = Reply.rounds) h1_listAt_notBeside h.symm

/-- hn at segment 24, as a closed test on a list of spots. -/
def h1NamedB (ps : List Spot) : Bool :=
  ps.all fun p => !decide (p.place = ⟨1, some 24, 1, .K7⟩) || p.name == "H:1"

/-- The test can be met. -/
theorem h1Named_yes :
    h1NamedB [⟨"H:1", ⟨1, some 24, 1, .K7⟩, []⟩, ⟨"H:2", ⟨1, some 24, 2, .K2⟩, []⟩] = true := by
  decide +kernel

/-- The test can fail: K7's place under the name beside. -/
theorem h1Named_no : h1NamedB [⟨"H:2", ⟨1, some 24, 1, .K7⟩, []⟩] = false := by
  decide +kernel

/-- **THE ROW, FROM THE SCOPE, THE READING, THE TWO RETURNS AND THE TEST ON THE SPOTS' NAMES.** -/
theorem h1_lists_scope {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {Z : ProofFile.Pub}
    {G : ProofFile.Ground} (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (hZ : ProofFile.pubPlain OnBytes.secondHashFunction P.pol lay P.KL = .ok Z)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Z = some G) (ps : List Spot) (hn : h1NamedB ps = true) :
    ∀ b ∈ h1Lot.blocks G, ∀ p ∈ ps, p.place = b.place → Lst listAt p.name b.rounds := by
  have hb : G.built.size = 25 := (IM.ground_gets hS hR hZ hG).1
  refine h1_lists G ps fun p hp e => ?_
  have e24 : G.built.size - 1 = 24 := by omega
  have e' : p.place = ⟨1, some 24, 1, .K7⟩ := by rw [e, e24]
  have h : (!decide (p.place = (⟨1, some 24, 1, .K7⟩ : Place)) || p.name == "H:1") = true :=
    List.all_eq_true.1 hn p hp
  rw [decide_eq_true e'] at h
  exact eq_of_beq h

/-- **THE ROW, BY THE PLACE**: at any table N of names by places that gives "H:1" at K7's place in
segment 24. No spot, no list of spots. -/
theorem h1_lists_at {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {Z : ProofFile.Pub}
    {G : ProofFile.Ground} (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (hZ : ProofFile.pubPlain OnBytes.secondHashFunction P.pol lay P.KL = .ok Z)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Z = some G) (N : Place → String)
    (hN : N ⟨1, some 24, 1, .K7⟩ = "H:1") :
    ∀ b ∈ h1Lot.blocks G, Lst listAt (N b.place) b.rounds := by
  intro b hb
  have hs : G.built.size = 25 := (IM.ground_gets hS hR hZ hG).1
  have e24 : G.built.size - 1 = 24 := by omega
  rw [(h1_block G b hb).2, e24, hN]
  exact Or.inr (h1_list G b hb)

end Johnson.AtFull.Rounds

#print axioms Johnson.AtFull.Rounds.h1_block
#print axioms Johnson.AtFull.Rounds.h1_one
#print axioms Johnson.AtFull.Rounds.h1_no_batch
#print axioms Johnson.AtFull.Rounds.h1_listAt_yes
#print axioms Johnson.AtFull.Rounds.h1_listAt
#print axioms Johnson.AtFull.Rounds.h1_listAt_not25
#print axioms Johnson.AtFull.Rounds.h1_listAt_notCount
#print axioms Johnson.AtFull.Rounds.h1_listAt_notStored
#print axioms Johnson.AtFull.Rounds.h1_listAt_notRng
#print axioms Johnson.AtFull.Rounds.h1_listAt_notTwo
#print axioms Johnson.AtFull.Rounds.h1_listAt_notBeside
#print axioms Johnson.AtFull.Rounds.h1_listAt_notKnown
#print axioms Johnson.AtFull.Rounds.h1_listAt_notNone
#print axioms Johnson.AtFull.Rounds.h1_list
#print axioms Johnson.AtFull.Rounds.h1_lists
#print axioms Johnson.AtFull.Rounds.h1_lists_can_fail
#print axioms Johnson.AtFull.Rounds.h1Named_yes
#print axioms Johnson.AtFull.Rounds.h1Named_no
#print axioms Johnson.AtFull.Rounds.h1_lists_scope
#print axioms Johnson.AtFull.Rounds.h1_lists_at
