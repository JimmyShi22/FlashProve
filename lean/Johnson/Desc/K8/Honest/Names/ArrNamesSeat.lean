-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/Names/ArrNamesSeat.lean: «THE OPEN LEDGER's ARRAYS HAVE THE PLAN's NAMES»:
EVERY MAKER OF THE PROOF FILE's SEAT HANDS THE SENTENCE ON: THE INSTANCE OF THE LIBRARY's GENERIC
WALK `Meaning.K2.SeatKeeps`. MADE BY PROGRAM FROM THE LIBRARY's Johnson/LPFK9R/LooksSeat.lean, WITH
AN ARRAY's NAME (`treeName`, Johnson/Desc/K8/Honest/Names/TreeName.lean) IN THE PLACE OF ITS LOOK:
every declaration of that file that the instance `seatKeeps_arrNames` (Names/ArrNamesSeat.lean)
wants and that names the looks, or leans on one that does, under a new name; the others are called
where they lie: that file is imported. NO NEW ARGUMENT: the library's proofs, token for token, but
for the turns that are named here. None of the library's goals.
Why. The smallness test's second computation asks that the digits' array bears the name "ZZ"
(`piecesTile`, OnBytes/Model/Tail.lean). The library carries each array's look (kind, rows, columns,
number of virtual rows) from the planned ledger to every reached state; a look holds no name. Spent
in Johnson/Desc/K8/Honest/NamesAtBatch.lean.
KEPT AND RENAMED (3): okHead → okHeadN · seatKeeps_looks → seatKeeps_arrNames · okHead_at →
okHead_atN.
CALLED WHERE THEY LIE (1): start_none.
NOT WANTED BY THE INSTANCE, AND SO NOT MADE (3): descPure_looks · looks_reach_front ·
looks_at_reached.
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
import Johnson.LPFK9R.LooksSeat
import Johnson.Desc.K8.Honest.Names.ArrNamesSeated
import Johnson.Desc.K8.Honest.Names.TreeName
import Johnson.Desc.K8.Honest.Names.ArrNamesWalk
import Johnson.Desc.K8.Honest.Names.ArrNamesEnds
import Johnson.Desc.K8.Honest.Names.ArrNamesRuns
import Johnson.Desc.K8.Honest.Names.ArrNamesVia
import Johnson.Desc.K8.Honest.Names.ArrNamesClose

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Keeps (Whole Decides Fn FnCl)
open Meaning.K2 (SeatKeeps descPure_keepsP frontOf backOf flat_eq blank_built pub_start)
open Johnson.Desc.First.Walk.Tied (Reach RchAt)

/-- The premise on the head's link's letters. -/
def okHeadN (B₀ : Array Stages.LinkH) (P : First.K2.HeadPar) : Prop :=
  anOfBuilt B₀ P.l = P.X.Fp.trees.toList.map treeName

/-- **EVERY MAKER OF THE SEAT.** -/
theorem seatKeeps_arrNames (B₀ : Array Stages.LinkH) :
    SeatKeeps (KeepsArrNames (anOfBuilt B₀)) (fun built => built = B₀) (okHeadN B₀) where
  refl := keeps_reflN _
  trans := keeps_transN _
  frames := fun hB h => by
    subst hB
    exact frames_keepN h
  k1First := fun q gp _ => k1First_wholeN _ q gp
  k1Later := fun q gp l p m a _ => k1Later_wholeN _ q gp l p m a
  reads := fun h => readsQuietAt_wholeN _ h
  k3 := fun c r X cs sh a _ h => theStated_wholeN _ c r X cs sh a h
  k4 := k4C_wholeN _
  k5 := fun W l g bf _ h => k5N_wholeN _ W l g bf h
  k6 := fun h => k6S_wholeN _ h
  k7 := k7Of_wholeN _
  k8 := k8W_wholeN _
  k11 := k11_wholeN _
  closeOf := closeOf_wholeN _
  batch := fun p _ hf => batch_wholeN _ p hf
  k2 := fun p _ => k2_wholeN _ p
  front := headFront_keepsN _
  openQ := fun P hP => headOpen_makesN _ P hP
  finFront := finFront_keepsN _
  finBehind := finBehind_keepsN _

/-- **The head's link's letters, off the blank letters, bear the built link's planned arrays**
(letters_arr, Johnson/IMR/OwnSeat.lean, at another field). -/
theorem okHead_atN {mk : ProofFile.LinksBy} {Z : ProofFile.Pub} {G : ProofFile.Ground}
    (h : ProofFile.blankBy mk Z = some G) {l : ℕ} {P : First.K2.HeadPar}
    (hP : P1K2.pureLetters G l = some P) : okHeadN Z.p.built.links P := by
  obtain ⟨links, e⟩ := blank_built h
  unfold P1K2.pureLetters at hP
  obtain ⟨X', hX', rfl⟩ := Option.map_eq_some_iff.1 hP
  show anOfBuilt Z.p.built.links l = X'.Fp.trees.toList.map treeName
  rw [e] at hX'
  obtain ⟨hl, e'⟩ := Array.getElem?_eq_some_iff.1 hX'
  have hl1 : l < Z.p.built.links.size := by
    rw [Array.size_zipWith] at hl
    omega
  rw [Array.getElem_zipWith] at e'
  rw [← e']
  exact anOfBuilt_at (X := Z.p.built.links[l]'hl1) (Array.getElem?_eq_getElem hl1)

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.seatKeeps_arrNames
#print axioms VerifiableInference.Desc.LinkJoin.okHead_atN
