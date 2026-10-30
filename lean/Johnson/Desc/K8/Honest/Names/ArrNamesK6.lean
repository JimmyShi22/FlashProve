-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/Names/ArrNamesK6.lean: «THE OPEN LEDGER's ARRAYS HAVE THE PLAN's NAMES»: THE
KIND K6's SHARE. MADE BY PROGRAM FROM THE LIBRARY's Johnson/Desc/First/Link/Law/LooksK6.lean, WITH
AN ARRAY's NAME (`treeName`, Johnson/Desc/K8/Honest/Names/TreeName.lean) IN THE PLACE OF ITS LOOK:
every declaration of that file that the instance `seatKeeps_arrNames` (Names/ArrNamesSeat.lean)
wants and that names the looks, or leans on one that does, under a new name; the others are called
where they lie: that file is imported. NO NEW ARGUMENT: the library's proofs, token for token, but
for the turns that are named here. None of the library's goals.
Why. The smallness test's second computation asks that the digits' array bears the name "ZZ"
(`piecesTile`, OnBytes/Model/Tail.lean). The library carries each array's look (kind, rows, columns,
number of virtual rows) from the planned ledger to every reached state; a look holds no name. Spent
in Johnson/Desc/K8/Honest/NamesAtBatch.lean.
KEPT AND RENAMED (2): k6_steps → k6_stepsN · k6_steps_seated → k6_steps_seatedN.
CALLED WHERE THEY LIE (2): setHeard_ctx · k6_reads.
NOT WANTED BY THE INSTANCE, AND SO NOT MADE (1): k6_steps_of.
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
import Johnson.Desc.First.Link.Law.LooksK6
import Johnson.Desc.K8.Honest.Names.TreeName
import Johnson.Desc.K8.Honest.Names.ArrNamesWalk

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Kinds.Head VerifiableInference.Desc.Kinds.Head.Law

/-- **K6: the output head's own rounds.** -/
theorem k6_stepsN (shOf : ℕ → List String) (h : OnBytes.Model.Head.Shape) (iU3 work l : ℕ) :
    (blockAt h iU3 work l).Steps (KeepsArrNames shOf) := by
  intro s rs gs s' hd
  obtain ⟨F0, F', L, a1, a2, a3, a4⟩ := k6_reads h iU3 work l s s' rs gs hd
  have ht : (s'.fork?.getD {}).trees = (s.fork?.getD {}).trees :=
    blockAt_trees h iU3 work l s s' rs gs hd
  rw [a1, a3] at ht
  refine keeps_of_casesN shOf fun G' L' hG hL' => Or.inr ⟨F0, L, a1, a2, ?_, ?_⟩
  · rw [Option.some.inj (a4.symm.trans hL')]
  · rw [← Option.some.inj (a3.symm.trans hG)]
    exact congrArg (·.map treeName) ht

/-- **So of the sub-protocol as a lot seats it.** -/
theorem k6_steps_seatedN (shOf : ℕ → List String) {W : OnBytes.Model.Verify.Public} {l : ℕ}
    {ms : List (ℕ × ℕ)} {b : Block S Claim} (h : seatedClaims W l ms = some b) :
    b.Steps (KeepsArrNames shOf) := by
  obtain ⟨b0, h0, rfl⟩ := seatedClaims_some h
  unfold blockClaims at h0
  obtain ⟨i, _, rfl⟩ := Option.map_eq_some_iff.mp h0
  intro s rs gs s' hd
  exact k6_stepsN shOf W.hS i _ l s rs gs s' ((tested_decide _ _ _ _ _ _ _ _).1 hd).1

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.k6_stepsN
#print axioms VerifiableInference.Desc.LinkJoin.k6_steps_seatedN
