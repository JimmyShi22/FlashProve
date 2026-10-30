-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K10/StAt.lean: the closing of a segment (K10): a filler for the lot's third parameter:
the verifier's statement in front of "BAT", made by the description's own step. This file defines a filler that is
laid in no lot: it is no part of the honest prover (why: «stAtFirst AND HIDING» below). Three definitions with code;
no theorem.

Why. The closing's part sends values that are made of the rows' coefficients in the verifier's statement in front of
"BAT". It could reckon them by a text of its own: a second text of what the verifier reckons. This file calls the
verifier's own text: the library's fold over a chain's members (`foldBlocks`, Johnson/Desc/Block.lean), over the members
in front of the closing's place, from the chain's own start at the public instance.

  `frontState`   the state in front of the member at a place: `foldBlocks` over the members in front of it; a refusal,
                 with words, where no member stands at the place, and wherever `foldBlocks` refuses: it names the member
                 and the test
  `stAtBy`       of a reading of the state: the filler's form, general in the state's type
  `stAtFirst`    the filler: at the first chain's state: the statement, and the number of the live frame's group:
                 the two that `K9.recOf` (Johnson/Desc/First/Batch/Place.lean) hands the kind's block as `st` and
                 `frame.group`

The letters that whoever would lay it fills (no lot lays it: see below). bs: the first chain's members in a row (the
description's `first.blocksInOrder`). start: the chain's first state, of the public instance (the description's `start₁` after
`pub`). The first chain's number of its first tree is 0 (`runCore`, Johnson/Desc/Block.lean: "the first chain" at 0):
laid here.

stAtFirst AND HIDING. WITH
stAtFirst THE ROW's FORM SENDS bareAsk AT ALL CLOSINGS BUT THE FIRST: such a prover sends the run's image and nothing of
the tables: it hides for free, as fixed messages do. NEVER: a law on hiding counted at a lot that holds stAtFirst · «the
honest prover's closing» said of it. It stands in no lot, and it may stand in no lot of a filling at
which anything on hiding is said or counted.
`Seen` has the field `opened`, and `stAtFirst` reads none of it (by `stAtBy`'s
text): so the bar stands: it lifts for a filler that folds at the handed columns, not for the field. On
hiding this file says nothing of its own.

Limits. Of a `Seen` (Honest/Frame.lean) this filler reads the rounds alone and no opened column, by `stAtBy`'s text, not
by a type: the fold is run at no columns. So at every closing but the chain's first it refuses: by the plan's names
every later link has a round "LOC" near its head, as its second round, or its third at the head's link
(Johnson/Desc/First/Driver/Cut.lean), and there the fold refuses under that member's name, "the columns" (by reading:
that a round "LOC" is owed a column is no theorem; a chain of the head's link alone has "LOC" at its first link too). At
the first it can return: that no member in front of it reads a column is a count, by reading, at the two written lists
of the dry runs' rounds (Johnson/G/DryProofLit.lean): so at these two examples alone, and no theorem; and the fold hands
on every other refusal of a member in front. The part that the lot lays makes nothing of a refusal of this parameter and
sends its default (Honest/K10/Job.lean, `closeAsk`; Sim.lean, `foldShellT`): `closeAtHand` (Job.lean) is the test with
code. It yields the state in front of a member, not inside one: "BAT" is the closing's first round. The list of
challenges is not read: a round as shown holds its own. More rounds than the members in front take do no harm: the rest
is not read. Every call folds all members in front anew. That the state is the one that a player holds at that member is
stated nowhere. Nothing ties bs or start to a description. `stAtFirst` is run by no line: it wants the public data of a
real description. No property of the protocol is claimed: beside the bar above nothing is said on its soundness,
completeness, binding or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K10.Half
import Johnson.Desc.First.Batch.Place

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open OnBytes (Statement)
open VerifiableInference.Desc (Block Place OpenedColumn foldBlocks)
open VerifiableInference.Desc.First.Close (Par)

/-- **The state in front of the member at the place a**, along a chain's rounds and columns from the chain's start on.
A refusal where no member stands at a; and `foldBlocks`' own. -/
def frontState {σ Cl : Type} (firstTree : Nat) (bs : List (Block σ Cl)) (s₀ : σ) (a : Place)
    (rs : List Fmt.RoundView) (cols : List OpenedColumn) : Except String σ :=
  if !bs.any (·.place == a) then .error "K10: no member of the chain stands at the place"
  else (foldBlocks firstTree (bs.takeWhile (·.place != a)) s₀ rs cols).map (·.1)

/-- **The filler's form** (its type is `StAtOf Xi`, Honest/K10/Seat.lean, written out). read: what is read off the
state. At no columns (this file's Limits). The list of challenges is not read. -/
def stAtBy {σ Cl Xi : Type} (read : σ → Statement × Nat) (bs : List (Block σ Cl)) (start : Xi → σ) :
    Xi → Par → Seen → List Fmt.Drawn → Except String (Statement × Nat) :=
  fun x P seen _ => (frontState 0 bs (start x) (closePlace P) seen.rounds []).map read

/-- **The filler**, at the first chain's state. Laid in no lot: see this file's head. -/
def stAtFirst {Cl Xi : Type} (bs : List (Block VerifiableInference.Desc.First.S Cl))
    (start : Xi → VerifiableInference.Desc.First.S) :
    Xi → Par → Seen → List Fmt.Drawn → Except String (Statement × Nat) :=
  stAtBy (fun s => (s.st, s.live.frame.group)) bs start

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.frontState
#print axioms ProofFile.Honest.K10.stAtBy
#print axioms ProofFile.Honest.K10.stAtFirst
