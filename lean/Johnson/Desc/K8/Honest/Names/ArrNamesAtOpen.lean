-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/Names/ArrNamesAtOpen.lean: «THE OPEN LEDGER's ARRAYS HAVE THE PLAN's NAMES»:
THE TERM OFF THE PLAN AT A BUILT SEGMENT OF THE BLANK GROUND. MADE BY PROGRAM FROM THE LIBRARY's
Johnson/Desc/First/Link/Law/AtBatchOpen.lean, WITH AN ARRAY's NAME (`treeName`,
Johnson/Desc/K8/Honest/Names/TreeName.lean) IN THE PLACE OF ITS LOOK: every declaration of that file
that the instance `seatKeeps_arrNames` (Names/ArrNamesSeat.lean) wants and that names the looks, or
leans on one that does, under a new name; the others are called where they lie: that file is
imported. NO NEW ARGUMENT: the library's proofs, token for token, but for the turns that are named
here. None of the library's goals.
Why. The smallness test's second computation asks that the digits' array bears the name "ZZ"
(`piecesTile`, OnBytes/Model/Tail.lean). The library carries each array's look (kind, rows, columns,
number of virtual rows) from the planned ledger to every reached state; a look holds no name. Spent
in Johnson/Desc/K8/Honest/NamesAtBatch.lean.
KEPT AND RENAMED (1): shOf_at → anOf_at.
CALLED WHERE THEY LIE (1): link_at_batch.
NOT WANTED BY THE INSTANCE, AND SO NOT MADE (2): looks_at_open · part_at_batch.
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
import Johnson.Desc.First.Link.Law.AtBatchOpen
import Johnson.Desc.K8.Honest.Names.ArrNamesSeated
import Johnson.Desc.K8.Honest.Names.TreeName

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.LinkJoin
open Inst.Model
open OnBytes OnBytes.Model
open OnBytes.Model.Stages (LinkH)
open VerifiableInference.Desc.K9 (atS)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.First (S)
open Meaning.K2 (frontOf blank_built)
open Johnson.Desc.First.Walk.Tied (RchAt rchAt_fold)
open ProofFile (Cl)

variable {P : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

/-- The plan's names of link l are the built link's planned arrays'. -/
theorem anOf_at {mk : ProofFile.LinksBy} {G : ProofFile.Ground} (h : ProofFile.blankBy mk Z = some G) {l : ℕ}
    {Xl : LinkH} (e3 : G.built[l]? = some Xl) :
    anOfBuilt Z.p.built.links l = Xl.Fp.trees.toList.map treeName := by
  obtain ⟨links, e⟩ := blank_built h
  rw [e] at e3
  obtain ⟨hl, e'⟩ := Array.getElem?_eq_some_iff.1 e3
  have hl1 : l < Z.p.built.links.size := by
    rw [Array.size_zipWith] at hl
    omega
  rw [Array.getElem_zipWith] at e'
  rw [← e']
  exact anOfBuilt_at (X := Z.p.built.links[l]'hl1) (Array.getElem?_eq_getElem hl1)

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.anOf_at
