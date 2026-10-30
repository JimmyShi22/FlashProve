-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/Names/ArrNamesAre.lean: «THE OPEN LEDGER's ARRAYS HAVE THE PLAN's NAMES»: THE
PROPERTY OF A LEDGER, «THE ARRAYS HAVE, IN ORDER, JUST THESE NAMES», WHERE IT IS MADE AND WHAT KEEPS
IT: AMONG THESE THE FIVE CLOSURE RULES `ForkRests`. MADE BY PROGRAM FROM THE LIBRARY's
Johnson/Desc/First/Link/Law/LooksAre.lean, WITH AN ARRAY's NAME (`treeName`,
Johnson/Desc/K8/Honest/Names/TreeName.lean) IN THE PLACE OF ITS LOOK: every declaration of that file
that the instance `seatKeeps_arrNames` (Names/ArrNamesSeat.lean) wants and that names the looks, or
leans on one that does, under a new name; the others are called where they lie: that file is
imported. NO NEW ARGUMENT: the library's proofs, token for token, but for the turns that are named
here. None of the library's goals.
Why. The smallness test's second computation asks that the digits' array bears the name "ZZ"
(`piecesTile`, OnBytes/Model/Tail.lean). The library carries each array's look (kind, rows, columns,
number of virtual rows) from the planned ledger to every reached state; a look holds no name. Spent
in Johnson/Desc/K8/Honest/NamesAtBatch.lean.
KEPT AND RENAMED (7): LooksAre → ArrNamesAre · looks_trees → arrNames_trees · looks_map →
arrNames_map · looks_laid → arrNames_laid · looks_rests → arrNames_rests · looks_fill →
arrNames_fill · looks_draw → arrNames_draw.
CALLED WHERE THEY LIE (4): rests_and · reads_mem · ledgerIn_of_four · totalIn_of_four.
NOT WANTED BY THE INSTANCE, AND SO NOT MADE (22): shapeAt_look · looks_frame · looks_start ·
looks_runs · looks_puts · looks_add · SizedLooks · sizedLooks_rests · looks_batch · looks_behind ·
looks_shut · looks_size · looks_get · unitLook · shape_at · shape_of_looks · shape_letter ·
totalIn_of_looks · looks_toy · looks_toy_no · unit_toy · unit_toy_no.
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
import Johnson.Desc.First.Link.Law.LooksAre
import Johnson.Desc.K8.Honest.Names.TreeName
import Johnson.Desc.K8.Honest.Names.ArrNamesFill

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open OnBytes.PscRun (Later Sized)
open OnBytes.Model.Road (SameSlots)
open OnBytes.Desc.First.K4 (Core hideRun_core paid_core)
open OnBytes.Tie.Pv.Tail.Port (readsList segsOf uOf hasRow)
open VerifiableInference.Desc.First.TailClaims.Law (eq_side coefBody_inv)
open VerifiableInference.Desc.First.TailClaims (equations coefBody)
open VerifiableInference.Desc.K9 (atS Where shut drawn drawnClean ledgerIn totalIn maskSeat arrayIn)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.JoinAtBlocks
open VerifiableInference.Desc.PhiAll
open Johnson.Desc.First.Walk (LinkPub startFork emptySlots weightsAtZero)

/-- **The ledger's arrays have, in order, just these names.** -/
def ArrNamesAre (sh : List String) (F : Fork) : Prop := F.trees.toList.map treeName = sh

section
variable {sh : List String}

theorem arrNames_trees {F G : Fork} (h : G.trees = F.trees) (hF : ArrNamesAre sh F) :
    ArrNamesAre sh G := by
  unfold ArrNamesAre at hF ⊢
  rw [h]
  exact hF

theorem arrNames_map {F G : Fork} (h : G.trees.map treeName = F.trees.map treeName)
    (hF : ArrNamesAre sh F) :
    ArrNamesAre sh G := by
  unfold ArrNamesAre at hF ⊢
  rw [← Array.toList_map, h, Array.toList_map]
  exact hF

end

/-- The ledger that is laid off a list of arrays has their names. -/
theorem arrNames_laid (F : Fork) (ns : ℕ) :
    ArrNamesAre (F.trees.toList.map treeName) (emptySlots (weightsAtZero F) ns) := by
  unfold ArrNamesAre emptySlots weightsAtZero
  simp only [Array.toList_map, List.map_map]
  exact List.map_congr_left fun T _ => arrName_rows_map T _

/-- **The five closure rules.** -/
theorem arrNames_rests (sh : List String) : ForkRests (ArrNamesAre sh) where
  later _ _ hc _ := arrNames_trees hc.trees
  hide _ _ _ _ _ h := arrNames_trees (hideRun_core h).trees
  paid F i := arrNames_trees (paid_core F i).trees
  eq _ _ _ _ _ _ _ he := arrNames_trees (eq_side he).trees
  coef tl g F h := coefBody_inv (ArrNamesAre sh)
    (fun r t' r' f hr => arrNames_map (by
      unfold HTailF2.onRow
      exact map_modify_same treeName (fun X => { X with rows := X.rows.modify r' f })
        (fun X => arrName_rows_modify X r' f) r.trees t') hr) tl g F h

/-- The filling of the weights that are not yet there. -/
theorem arrNames_fill {sh : List String} (F : Fork) (T : Tail2) (h : ArrNamesAre sh F) :
    ArrNamesAre sh (t2FillL F T) := arrNames_map (fold_arrNames _ _) h

/-- **The batching's draw.** -/
theorem arrNames_draw {sh : List String} (rows : ℕ) (chi : E) (owed : Option ℕ) (used : ℕ)
    (L : LinkCtx) (F : Fork) (o : K9.Drawn) (h : drawnClean rows chi owed used L F = .ok o)
    (hF : ArrNamesAre sh F) : ArrNamesAre sh o.F := by
  unfold drawnClean at h
  obtain ⟨o', ho, h⟩ := ok_bind h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain rfl : o' = o := Except.ok.inj h
  unfold drawn at ho
  obtain ⟨_, _, ho⟩ := ok_bind ho
  obtain ⟨_, _, ho⟩ := ok_bind ho
  obtain ⟨_, _, ho⟩ := ok_bind ho
  obtain ⟨_, _, ho⟩ := ok_bind ho
  obtain ⟨_, _, ho⟩ := ok_bind ho
  rw [← Except.ok.inj ho]
  exact arrNames_trees (F := t2FillL F L.list) rfl (arrNames_fill F L.list hF)

section
variable {sh : List String}

end

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.arrNames_trees
#print axioms VerifiableInference.Desc.LinkJoin.arrNames_map
#print axioms VerifiableInference.Desc.LinkJoin.arrNames_laid
#print axioms VerifiableInference.Desc.LinkJoin.arrNames_rests
#print axioms VerifiableInference.Desc.LinkJoin.arrNames_fill
#print axioms VerifiableInference.Desc.LinkJoin.arrNames_draw
