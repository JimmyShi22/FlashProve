-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/FirstNo.lean: THE SHARED "SENDING" (the kind K1): THE NUMBER THAT A
PLACE's FIRST NEW ORACLE MESSAGE GETS, MADE OFF A DESCRIPTION's OWN LIST OF BLOCKS: how many oracle
messages the blocks in front of the place tell. Public data alone: no coin, no witness, no index is
read. Three definitions with code; no theorem. Written from the verifier's text
(Johnson/Desc/Block.lean, Johnson/Desc/Oracle.lean) alone.

Why. A sending's job states the number of its first new message (SendJob.first,
Honest/K1/Part.lean); the halves at K1's places take it as a letter no : Place → Nat
(Honest/K1/PlaceJob.lean). Whoever seats them MAKES that number off the description's own list, and
never types it: as roundsInFront (Honest/ForKinds.lean) does for the rounds.

Main names (namespace ProofFile.Honest.K1).
  firstNoOf bs a   the text of roundsInFront with, for b.rounds.length, the number of tenants in the
      block's own field "oracles": the oracle messages that the block tells. The first block at the
      place counts. WHERE NO BLOCK STANDS AT THE PLACE: none.
  firstNoFits bs places   A PUBLIC TEST: at each of the places a block stands.
  firstNoAt bs a   the total form, for the letter no. WHERE NO BLOCK STANDS AT THE PLACE IT IS 0,
      WHICH MEANS NOTHING: so firstNoFits stands in the seat's public test, and every law that
      spends firstNoAt names firstNoFits.

Laws: Honest/K1/FirstNoLaw.lean. Tests at synthetic small parameters: Honest/K1/FirstNoPlay.lean.

Limits. Nothing ties the number to a state here. THE NUMBER ENTERS NOTHING THAT IS SENT: the part
and the half of a job are one value at every number laid into "first" (Honest/K1/FirstFree.lean): so
firstNoFits guards a number on which no sent value hangs. Where two blocks stand at one place the
first counts: that they are meant as one is not asked. Nothing on the shared and the last chain.
Nothing on any property.

Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.Block

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open VerifiableInference.Desc (Block Place)

variable {S Cl : Type}

/-- **How many oracle messages the blocks in front of the place tell**: public data, to be laid into
a job's "first". none if no block stands at the place. -/
def firstNoOf : List (Block S Cl) → Place → Option Nat
  | [], _ => none
  | b :: bs, a =>
    if b.place == a then some 0
    else (firstNoOf bs a).map (· + (b.oracles.flatten.map fun o => o.tenants.length).sum)

/-- **A public test**: at each of the places a block of the list stands. -/
def firstNoFits (bs : List (Block S Cl)) (places : List Place) : Bool :=
  places.all fun a => (firstNoOf bs a).isSome

/-- The total form. WHERE NO BLOCK STANDS AT THE PLACE IT IS 0, WHICH MEANS NOTHING: firstNoFits is
the named public test beside it. -/
def firstNoAt (bs : List (Block S Cl)) (a : Place) : Nat := (firstNoOf bs a).getD 0

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.firstNoOf
#print axioms ProofFile.Honest.K1.firstNoFits
#print axioms ProofFile.Honest.K1.firstNoAt
