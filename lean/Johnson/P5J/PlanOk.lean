-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/PlanOk.lean: THE NAMED TESTS ON THE PLAN THAT STAND IN FRONT OF THE COMPOSED MEANING's CONSTANT: ONE STRUCTURE. Two definitions, one structure, four theorems. hN stands at the label's form of the seats: it needs no scope. "fit" and "groups" ARE OVER THE PLAN's SEATS ALONE: seatsFitP | groupsP (Johnson/P5T/MembersPlain.lean): THEY READ NO ROW OF THE SENDINGS AND NOT lay; the members are by the make. 𝔇Ok stands in Johnson/P5J/LettersRec.lean: this file hangs on no text of the composed meaning. "groups" STANDS AT nG := the number of the request's groups, a term off the public part, NOT AT 24 (the head's segment's number): the last group's number is 25 (the last proximity test's own) and it has a tenant; "beyond" is no field: a theorem. A joint build of several kinds' files.

Why. The counted statements end in the form: InScope Z → "the verifier's own value is laid" (LaidAt) → ‹these tests say yes› → … at mgAll (𝔇At …) Mg₀. THE LIST OF TESTS IS CLOSED AND MUST SHRINK: each is either to become a theorem in scope or a row that the verifier's door asks.
PlanOk o Zp Np cF lay: SEVEN FIELDS, EACH A Bool WITH CODE = true: FIVE PAY THE FOUR PREMISES IN THE TYPE OF 𝔇At (Johnson/P5J/LettersRec.lean); THE LAST TWO FENCE A DEFAULT EACH (spent by no theorem here):
  shape    fullShapeB at the plan's shape of the shared chain: the one decoder's typed data (decT)
  laid     laidThere: every matrix of every segment has its array in the layout: it fences the seats' silent (0, 0, 0) (H)
  named    seatsNamedC: once a matrix: the number that a seat names has just one tenant in the reader's own group (H: SeatsNamed)
  fit      seatsFitP: no entry of the plan's seats with a sample has a fault at its (tree, tenant) (H: GroupsSeated)
  groups   groupsP AT nG: every seat of every group 0 … nG, the index masks' and W's is an entry's with a sample (H: GroupsSeated)
  radii    radIsB: at every entry with a sample the rows of the sendings HAVE a radius, and it is rad's: it fences rad's silent 0 (ms). THE ONE FIELD THAT READS THE ROWS AND lay.
  poss     possThereB: for every group from 1 to the number of segments a code switch stands among the first chain's sub-protocols: it fences the silent 0 of "the positions that the switch into group m draws" (N's rowsAt)
THEOREMS, NO FIELDS: beyond (above nG the numbers' groups are empty: by the make of the plan's seats: group_beyond).
CAN IT BE MET? NOT SHOWN BY LEAN. By a run of these very terms: see the page beside this file's rest: NOTHING IS SAID HERE.
WHAT COMES OUT: PlanOk.hN (SeatsNamed at the seats as a function of the label: no scope) · PlanOk.hG (GroupsSeated). (𝔇Ok, 𝔇At with its four premises paid from PlanOk, in scope: Johnson/P5J/LettersRec.lean.)
NOT IN IT, BECAUSE THEY ARE THEOREMS: the numbers' groupAt 0 = 0 (rfl) · sizesFit | SeatsOne (in scope). NOT IN IT, BECAUSE 𝔇At's TYPE DOES NOT TAKE THEM (they stand in front of single laws; the page beside this file lists them): padsFreeC · the blocks' places are the written list · headLink X = 24 · the proximity test's door's list is there · the batching round of a segment is there · the
shared chain's three tenants bear three numbers.

Limits. A bundling. It shows no test to be true. The full size alone. NO MEMBER. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.P5J.LettersAt
import Johnson.P5J.WordsOfTests
import Johnson.Desc.Sound.GroupsSeatedB
import Johnson.P5T.PlanFacts
import Johnson.Desc.First.PossThere

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P5J.At
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.Sound (SeatsNamed GroupsSeated msOf groupsSeated_of_B)

variable (o : ProofFile.SecondHashFunctionArgument) (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain TS ProofFile.Cl) (lay : ByteArray)

/-- The members' lists: shapes and seats by the make off the plan's seats; the radii off the rows of the sendings. -/
def members : VerifiableInference.Desc.MemberLists :=
  P5T.memberListsR Zp.made.proof.1.sends.length (rad Zp lay) (pseats Zp)

theorem ms_is : ms Zp lay = msOf (members Zp lay) := rfl

/-- The number of the request's groups: one for each link, then the group of the last test. -/
def nG : ℕ := (OnBytes.reqGroups Zp.first.shape).toList.length

/-- **Above nG the numbers' groups are empty**: by the make of the plan's seats. -/
theorem beyond (k : ℕ) (hk : nG Zp < k) : (N Zp cF).group k = [] :=
  P5T.group_beyond Zp Zp.D.1 k hk

/-- **THE NAMED TESTS ON THE PLAN.** -/
structure PlanOk : Prop where
  shape : Desc.K14.Law.fullShapeB (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par.S = true
  laid : Meaning.laidThere (X Zp) (Meaning.sizesOf (X Zp)) (layout Zp) = true
  named : seatsNamedC (X Zp) (Meaning.sizesOf (X Zp)) (layout Zp) (num Zp) (arr Zp) (N Zp cF) = true
  fit : P5T.seatsFitP (F0T o Zp Np cF) (cs Zp) (pseats Zp) = true
  groups : P5T.groupsP (N Zp cF) (nG Zp) (pseats Zp) = true
  radii : P5T.radIsB ((P5T.rowsAt? Zp.pol lay Zp.KL).getD []) Zp.made.proof.1.sends.length (rad Zp lay) (pseats Zp) = true
  poss : VerifiableInference.Desc.First.possThereB cF.blocksInOrder links.length = true

variable {o Zp Np cF lay}

/-- GroupsSeated, from two tests. -/
theorem PlanOk.hG (ok : PlanOk o Zp Np cF lay) : GroupsSeated (ms Zp lay) (N Zp cF) :=
  groupsSeated_of_B (F0T o Zp Np cF) (cs Zp) (members Zp lay)
    ((P5T.seatsFitB_R _ _ _ _ _ (fun p hp _ => P5T.planSeats_send_lt Zp Zp.D.1 p hp)).trans ok.fit) (N Zp cF) (nG Zp)
    ((P5T.groups_R _ _ _ _ _ (fun p hp _ => P5T.planSeats_send_lt Zp Zp.D.1 p hp)).trans ok.groups) (beyond Zp cF)

/-- SeatsNamed at the seats as a function of the label, from two tests: NO SCOPE. -/
theorem PlanOk.hN (ok : PlanOk o Zp Np cF lay) :
    SeatsNamed (arr Zp) (N Zp cF) (Meaning.sizesOf (X Zp))
      (Meaning.seatBy (Meaning.fLay (layout Zp) (num Zp)) (X Zp) (Meaning.sizesOf (X Zp))) :=
  seatsNamed_at_plan ok.laid ok.named

end P5J.At

#print axioms P5J.At.ms_is
#print axioms P5J.At.beyond
#print axioms P5J.At.PlanOk.hG
#print axioms P5J.At.PlanOk.hN
