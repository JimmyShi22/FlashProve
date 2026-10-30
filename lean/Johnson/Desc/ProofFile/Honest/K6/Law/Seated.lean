-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K6/Law/Seated.lean: what it means that the honest side of the
sub-protocol "the output head's own rounds" (`headRow`, Honest/K6/Part.lean) stands at a member of
a chain's `Thread` (Honest/Thread/Thr.lean). One definition of a proposition: the form of a premise,
for laws on that row. These laws stand in other files, none of which this file imports. No theorem.

What it is not. A premise's form: nothing here shows that it is met at a description of the
protocol. Nothing is asked of the member's name, its decision or its runs of claims: what the
verifier's yes wants of the member stands in a structure of its own. Nothing is claimed on
soundness, completeness or hiding.

  `K6Seated T b wit p at_ blk`   blk is the member number b of T's flat list; it stands at the place
      at_; its rounds are those that the verifier's text lays for the public numbers p, and no round
      has an oracle message; the half that T's list of halves holds for that place is the row at
      wit, p and that place

General in T's fields, and in its letters Bk, S, Cl, X and Pb. Its letters V and W are not free:
both are `Local W₀ Rc Inst Tr`, general in W₀, Rc and Tr alone.

Who is meant to show each clause. `member`, `place`, `rounds`, `oracles`: whoever ties T's flat list
to the description: the member is the kind's block, wrapped; wrapping leaves rounds and oracle
messages, and lays the place (Honest/K6/Cut.lean: `headLot_seated` has
place and rounds for every block that the lot seats). `half`: whoever lays T's list of halves
(there: `headLot_halves`).
The form follows the like structure on the attention segment's own rounds
(Honest/K5/Law/Seated.lean: `K5Seated`).
-/
import Johnson.Desc.ProofFile.Honest.Thread.Pays
import Johnson.Desc.ProofFile.Honest.K6.Part

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K6
open VerifiableInference.Desc (Block Place)
open VerifiableInference.Desc.Kinds (Head.Par)

variable {Bk : ProverCoinCounts} {S Cl W₀ Rc Tr X Pb : Type}

/-- **The sub-protocol's half stands at the member number b.** A definition: a premise's form.
Nothing is claimed of it. -/
structure K6Seated (T : Thread Bk S Cl (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X Pb) (b : Nat)
    (wit : Local W₀ Rc Inst Tr → HeadAsk) (p : Head.Par) (at_ : Place) (blk : Block S Cl) :
    Prop where
  /-- blk is the member -/
  member : T.bs[b]? = some blk
  /-- it stands at the place -/
  place : blk.place = at_
  /-- its rounds are the verifier's, at the public numbers p -/
  rounds : blk.rounds = p.rounds
  /-- no round has an oracle message -/
  oracles : blk.oracles = p.rounds.map fun _ => []
  /-- the half that the fold finds for the member's place -/
  half : T.hs.find? (fun h => h.place == blk.place) = some ⟨at_, headRow wit p at_⟩

end ProofFile.Honest.K6
