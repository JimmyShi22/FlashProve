-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/Names/ArrNamesK2.lean: «THE OPEN LEDGER's ARRAYS HAVE THE PLAN's NAMES»: THE
KIND K2's SHARE. MADE BY PROGRAM FROM THE LIBRARY's Johnson/Desc/First/Link/Law/LooksK2.lean, WITH
AN ARRAY's NAME (`treeName`, Johnson/Desc/K8/Honest/Names/TreeName.lean) IN THE PLACE OF ITS LOOK:
every declaration of that file that the instance `seatKeeps_arrNames` (Names/ArrNamesSeat.lean)
wants and that names the looks, or leans on one that does, under a new name; the others are called
where they lie: that file is imported. NO NEW ARGUMENT: the library's proofs, token for token, but
for the turns that are named here. None of the library's goals.
Why. The smallness test's second computation asks that the digits' array bears the name "ZZ"
(`piecesTile`, OnBytes/Model/Tail.lean). The library carries each array's look (kind, rows, columns,
number of virtual rows) from the planned ledger to every reached state; a look holds no name. Spent
in Johnson/Desc/K8/Honest/NamesAtBatch.lean.
KEPT AND RENAMED (2): k2_keeps → k2_keepsN · k2_steps → k2_stepsN.
CALLED WHERE THEY LIE (1): k2_link_kept.
NOT WANTED BY THE INSTANCE, AND SO NOT MADE (1): placeH2_makes.
THE GENERAL TURNS: look → treeName · Look → String · …looks… → …arrNames… · …Looks… → …ArrNames… ·
shOfBuilt → anOfBuilt · shOf_at → anOf_at · Stays → StaysN · the tactic stays → staysN · every other
kept name gets an N behind; the letter shOf stays, at the type ℕ → List String; in comments "look" →
"name". Lines over 100 signs are broken.
TURNED BY HAND: nothing.
Limits. ITS SOURCE's LIMITS ARE ITS OWN: one direction, from a yes or from a return; nothing says
that any state is reached. It is no second text of its source: it speaks of another field of an
array, and no law ties the two. The comments on the declarations are the source's, turned by the
same program: they were not written for this file. It stands in the source's own namespace, so that
every name resolves as there. No prover stands in it.
Nothing is claimed on completeness, soundness or hiding.

-/
import Johnson.Desc.First.Link.Law.LooksK2
import Johnson.Desc.K8.Honest.Names.TreeName
import Johnson.Desc.K8.Honest.Names.ArrNamesWalk

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2

theorem k2_keepsN (shOf : ℕ → List String) {snd : _root_.Tw.K2.SendFn} {p : P2} {s : S}
    {rs : List Fmt.RoundView} {gs : List (List (ℕ × List UInt64))} {s' : S}
    (h : decideWith snd p s rs gs = .ok s') : KeepsArrNames shOf s s' :=
  keeps_sameN shOf (fork_kept h) (by rw [k2_link_kept h])

/-- **K2: the code switch.** -/
theorem k2_stepsN (shOf : ℕ → List String) (p : P2) :
    (codeSwitchKind p : Block S Unit).Steps (KeepsArrNames shOf) := by
  intro s rs gs s' h
  exact k2_keepsN shOf (show decideWith _ p s rs gs = .ok s' from h)

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.k2_keepsN
#print axioms VerifiableInference.Desc.LinkJoin.k2_stepsN
