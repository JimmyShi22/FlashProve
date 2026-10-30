-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/Riders/DoorFuns.lean: THE ONE NAME THAT THE WIDER DOOR LETS K4's ROW MAKE:
"K8.funsThird" ("the tables as the claims take them are there, and every one lies on the third
vector of reads"): ITS TEST ACCEPTS AT THE VERIFIER's STATE AFTER K4's SUB-PROTOCOL ACCEPTS; so the
named premise hDoor of `k4Row_of_means` (K4RowOfMeans.lean) is paid where the door makes that name
alone at K4's place. Statements and proofs: one call of a law on the hearing
(Johnson/Road/K4/FunsTree.lean).

  `funsThirdB_made`: `KeptAtS p s s'` ⟹ funsThirdB s' = true.
  **`door_funs`**: the equation of the side structure `K4PileNames` at that name · "the door makes
  [that name] at K4's place" ⟹ hDoor.

Limits. AT THE WIDER DOOR ALONE (a bridge's side). At the composed meaning's small door K4's row
makes no name and hDoor is idle (`door_none`). ON THE BRIDGE THIS MAKE IS DROPPED, AND THE SAME TEST
IS OWED AGAIN at the reached state behind K4's sub-protocol: `funsThirdB_made` is the step's lemma
for that debt; `door_funs` is not. That the door makes that name alone there is a test on the door
(Riders/PlanFull.lean asks it). K04_law, the law of K4's sub-protocol itself, IS NOT PROVED. Nothing
on soundness.
-/
import Johnson.Road.K4.Riders.KeptNames
import Johnson.Road.K4.KeptOfYes
import Johnson.Road.K4.FunsTree

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.Riders

open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4 (Par seatS)
open _root_.Run (ckP)
open VerifiableInference.Desc (Place Wit)
open VerifiableInference.Desc.First (S ModelPart Meaning Numbers moreItem)
open VerifiableInference.Desc.First.K8.Ready (funsThirdB)
open VerifiableInference.Desc.Sound (Frame Piece onQ MsgT)

/-- After K4's sub-protocol accepts, the test of "K8.funsThird" accepts. -/
theorem funsThirdB_made {p : Par} {s s' : S} (K : KeptAtS p s s') : funsThirdB s' = true := by
  obtain ⟨a, fo, o, G, _, _, _, _, _, hf, _, _, _, _, _, t, u, hh⟩ := K
  have h : (o.funs.toList.all fun Fn => Fn.tree == 2) = true :=
    List.all_eq_true.2 fun Fn hFn => by
      simpa using funs_tree_of_hear hh Fn (Array.mem_toList_iff.1 hFn)
  unfold funsThirdB
  rw [hf, Option.map_some, h]
  rfl

variable {Xi P Tok Cl : Type} {rows cols : ℕ} {Fr : Frame}
  {Mg : Meaning P (Wit (CellsK rows cols) Tok MsgT)} {N : Numbers} {Z : P} {links : List ModelPart}
  {ps : List Place} {k m : ℕ} {pl : Place} {par : Par}
  {q : Piece (ckP .two) Fr S Cl (Wit (CellsK rows cols) Tok MsgT)}

/-- **The premise hDoor, where the door makes "K8.funsThird" alone at K4's place.** -/
theorem door_funs {tlP : ℕ → Option HTailF2} (Ep : K4PileNames Mg tlP)
    (h : (Mg.more.rows links pl).makes = [(some m, "K8.funsThird")]) :
    ∀ a τ fo o G', onQ N Mg links ps (fun s => (Z, s)) k a → a.1.failed = none →
      Yes seatS par q a τ fo o G' → ∀ nm ∈ (Mg.more.rows links pl).makes,
      Mg.pub (moreItem nm) (Z, (behindOf seatS q a τ o G').1) = true := by
  intro a τ fo o G' _ _ y nm hnm
  rw [h, List.mem_singleton] at hnm
  subst hnm
  show Mg.pub (.more (some m) "K8.funsThird") _ = true
  rw [Ep.funsThird]
  exact funsThirdB_made (kept_of_yes y)

end OnBytes.Road.K4.Riders

#print axioms OnBytes.Road.K4.Riders.funsThirdB_made
#print axioms OnBytes.Road.K4.Riders.door_funs
