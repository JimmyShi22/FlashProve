-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/ClassAtLater.lean: five of the eight
names of the class `cA13` (K13/Law/BridgeK13.lean) are kept over an accept of a later sending's
sub-protocol `blkL Z G l d X arrs`, at every meaning `plus13 D dk M`. Arms of
hrest_plus13. Statements with their proofs; they call, and retype none.
  `laterFits_blkL`  the sub-protocol at (l, d) is a member of `LaterFits`;
                    that it is one of `Later` is `later_blkL` of Johnson/Desc/K1/Law/APileOf.lean
  `masks_later`     "K13.pileMasks": `later_pileMasks` (K1/Law/RowsFactAtLater.lean)
  `within_later`    "K13.pileWithin": `later_pileWithin`
  `oneRow_later`    "K13.oneRow": `later_oneRow`: it holds behind the accept, whatever stood before
  `weights_later`   "K13.weightsOk": `later_rows` (K1/Law/PileAtLater.lean) and `weightsB_same`
  `fits_later`      "K12.bookFits": `LaterFits`. PREMISE hfB: the test `Sound.bookFitsB` says
                    `Book.BookFits` (the field `fitsSays` of `LaidK1` at fB := that test)
NOT HERE: "K12.bookInOrder", "K12.seatsCarried", "K12.msgShapes": these three grow with the sending,
and want equations on the list of rounds.
What is not claimed. Nothing on which items are open. Nothing on soundness.

-/
import Johnson.Desc.K1.Law.APileOf
import Johnson.Desc.K1.Law.BookHoldsAt
import Johnson.Desc.K1.Law.RowsFactAtLater
import Johnson.Desc.K1.Law.PileAtLater
import Johnson.Desc.K13.Law.BridgeK13

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model
open VerifiableInference.Desc.First (S Pub Meaning weightsB weightsB_same)
open VerifiableInference.Desc.Book (BookFits)
open VerifiableInference.Desc.K13.Law (plus13 DataK13)
open VerifiableInference.Desc.K12.Door (K12Data)
open OnBytes.Model.Stages (LinkH)

section
variable (Z : ProofFile.Pub) (G : ProofFile.Ground) (l : ℕ) (d : Bool) (X : LinkH) (arrs : Option (List ℕ))

theorem laterFits_blkL : LaterFits (blkL Z G l d X arrs) := by
  cases d with
  | true => exact laterFits_laterAt _ _ _ _ _ _
  | false => exact laterFits_k1Reads _ _ _ _ _ _

end

section
variable {Pp W : Type} {nR : ℕ} (D : DataK13 Pp W nR) (dk : K12Data) (M : Meaning Pp W)
  {Z : ProofFile.Pub} {G : ProofFile.Ground} {l : ℕ} {d : Bool} {X : LinkH} {arrs : Option (List ℕ)}
  {x x' : Pp × S}

theorem masks_later (hy : YesOf (blkL Z G l d X arrs) x x')
    (h0 : (plus13 D dk M).pub (.more none "K13.pileMasks") x = true) :
    (plus13 D dk M).pub (.more none "K13.pileMasks") x' = true := by
  obtain ⟨_, rs, gs, _, hd⟩ := hy
  obtain ⟨own, hB⟩ := later_blkL Z G l d X arrs
  exact later_pileMasks hB hd h0

theorem within_later (hy : YesOf (blkL Z G l d X arrs) x x')
    (h0 : (plus13 D dk M).pub (.more none "K13.pileWithin") x = true) :
    (plus13 D dk M).pub (.more none "K13.pileWithin") x' = true := by
  obtain ⟨_, rs, gs, _, hd⟩ := hy
  obtain ⟨own, hB⟩ := later_blkL Z G l d X arrs
  exact later_pileWithin hB hd h0

theorem oneRow_later (hy : YesOf (blkL Z G l d X arrs) x x') :
    (plus13 D dk M).pub (.more none "K13.oneRow") x' = true := by
  obtain ⟨_, rs, gs, _, hd⟩ := hy
  obtain ⟨own, hB⟩ := later_blkL Z G l d X arrs
  exact later_oneRow hB hd

theorem weights_later (hy : YesOf (blkL Z G l d X arrs) x x')
    (h0 : (plus13 D dk M).pub (.more none "K13.weightsOk") x = true) :
    (plus13 D dk M).pub (.more none "K13.weightsOk") x' = true := by
  obtain ⟨_, rs, gs, _, hd⟩ := hy
  obtain ⟨own, hB⟩ := later_blkL Z G l d X arrs
  show weightsB x'.2 = true
  rw [weightsB_same (later_rows hB _ _ _ _ hd)]
  exact h0

theorem fits_later (hfB : ∀ B, Sound.bookFitsB B = true ↔ BookFits B)
    (hy : YesOf (blkL Z G l d X arrs) x x')
    (h0 : (plus13 D dk M).pub (.more none "K12.bookFits") x = true) :
    (plus13 D dk M).pub (.more none "K12.bookFits") x' = true := by
  obtain ⟨_, rs, gs, _, hd⟩ := hy
  show Sound.bookFitsB x'.2.book = true
  exact (hfB _).2 (laterFits_blkL Z G l d X arrs _ _ _ _ hd ((hfB _).1 h0))

end

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.masks_later
#print axioms VerifiableInference.Desc.K1.within_later
#print axioms VerifiableInference.Desc.K1.oneRow_later
#print axioms VerifiableInference.Desc.K1.weights_later
#print axioms VerifiableInference.Desc.K1.fits_later
