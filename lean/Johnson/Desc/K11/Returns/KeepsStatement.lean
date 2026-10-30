-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K11/Returns/KeepsStatement.lean: WHAT THE STEP OF THE MERGE OF THE CLAIMS ON THE
WEIGHTS LEAVES OF THE VERIFIER's STATE, AND HOW WHAT IT TURNS HAS TURNED: two definitions, and
STATEMENTS ALONE: two, each a definition of a proposition. NOTHING IS PROVED IN THIS FILE, and
neither is one of the library's goals: they are lemmas' statements. The text is the verifier's; no
prover is named.

  `K11Writes P s s'`   FIVE FACTS ON THE STATE IN FRONT, which a yes of the decision gives for
                       nothing: the head's link is open; the end value's slot is there; the array of
                       marks has its size; THE MARK AT THAT SLOT WAS FREE; the slots come out at the
                       plan's number. AND ONE EQUATION: s' is s with: nothing owed by the round in
                       front; and, in the head's own part: what the merge left laid; the ledger in
                       front kept aside, whole; the next free slot noted; and the ledger turned in
                       five fields:
                       2 lk + 3 slots more are taken; the plan's number of claims is written; at ONE
                       slot, the end value's, the mark is set and a shown value and a factor are
                       laid. EVERY OTHER FIELD OF THE STATE, OF THE HEAD's OWN PART AND OF THE
                       LEDGER STANDS, and so does every other entry of the ledger's three arrays
  `K11Keeps P s s'`    that, and: the state behind bears no mark of failure
  `HeadMergeWrites`    wherever the decision (`headMergeDecide`,
                       Johnson/Desc/First/Fork/MergeKind.lean) returns, with no other premise:
                       `K11Writes`
  `HeadMergeKeeps`     wherever the decision of the kind's block AS IT STANDS ALONE AT A SEAT
                       (`IM.seatedAs`, Johnson/IMR/SeatForm.lean) returns: `K11Keeps`

Limits. Three letters stand under "there is": what the merge left: it is read off s'; the shown
value and the factor: they are read off s' WHERE THE END VALUE's SLOT LIES INSIDE THE TWO ARRAYS OF
VALUES; beyond an array's end nothing is laid, and the letter is free and idle. With the equation,
`K11Keeps` gives that the state IN FRONT bears no mark either: the mark is among the fields that
stand. Of what the merge left nothing is said here (`MergeBehind`, Statement.lean of this folder;
`HeadMergeRecs`, SeatStatement.lean). Nothing on the run of claims "the merge", which is called
inside the batching. Nothing on any property.
-/
import Johnson.Desc.K11.Returns.SeatStatement

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Desc.First.ForkMerge.Returns
open OnBytes (E)
open OnBytes.Model (WsForkOut)
open OnBytes.PscRun (Filled)
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.First (S HeadOwn)

/-- Five facts on the state in front, and the state behind the merge's decision, written out of the
state in front. a: the head's own part in front. wo: what the merge left. v, β: the shown value and
the factor at the end value's slot. -/
def K11Writes (P : HeadMergeP) (s s' : S) : Prop :=
  ∃ (a : HeadOwn) (wo : WsForkOut) (v β : E), s.here = .head a ∧ a.opened = true ∧
    mergeEndSlot P.lay.lk a.F < a.F.ns ∧ a.F.gotF.size = a.F.ns ∧
    ¬ Filled a.F (mergeEndSlot P.lay.lk a.F) ∧ a.F.next + 2 * P.lay.lk + 3 = P.nMsg ∧
    s' = { s with
      rowsOwed := none
      here := .head { a with
        wo := some wo
        F := { a.F with
          next := a.F.next + 2 * P.lay.lk + 3
          planClaimsF := P.nLin
          gotF := a.F.gotF.set! (mergeEndSlot P.lay.lk a.F) true
          vp := a.F.vp.set! (mergeEndSlot P.lay.lk a.F) v
          mf := a.F.mf.set! (mergeEndSlot P.lay.lk a.F) β }
        Fm := a.F
        slot := some (a.F.next + 2 * P.lay.lk + 3) } }

/-- What the member's step leaves and turns: that, and no mark of failure behind. -/
def K11Keeps (P : HeadMergeP) (s s' : S) : Prop := K11Writes P s s' ∧ s'.failed = none

/-- The statement at the decision. Not proved here; a lemma's statement, none of the library's
goals. -/
def HeadMergeWrites : Prop :=
  ∀ (P : HeadMergeP) (s s' : S) (rs : List Fmt.RoundView), headMergeDecide P s rs = .ok s' →
    K11Writes P s s'

/-- The statement at the seated block's decision. name, pl: the seat's name and place. Not proved
here; a lemma's statement, none of the library's goals. -/
def HeadMergeKeeps : Prop :=
  ∀ (P : HeadMergeP) (name : String) (pl : Place) (s s' : S) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))),
    (IM.seatedAs ProofFile.sameReply (headClaimMergeKind P) name pl).decide s rs gs = .ok s' →
    K11Keeps P s s'

end Johnson.Desc.First.ForkMerge.Returns
