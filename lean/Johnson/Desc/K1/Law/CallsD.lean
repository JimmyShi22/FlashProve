-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K1/Law/CallsD.lean: K01_law: THE CALL hSmp_of: THE TOP's BINDER hSmp (SmpLeft: the block's own yes, from inside the promise in front, leaves the out-of-domain (OOD) sample that the letter smp reads for each member at a tenant whose pin is
open in front), TO ITS LETTER, AT smp := smpNamed cs seats (Johnson/Desc/Sound/SmpNamed.lean), AT BOTH SORTS OF LATER BLOCK: by smpLeft_named (Johnson/Desc/K1/Law/SmpNamedEarlierMessages.lean).

  keepsOld_blkL   the lot's own block at (l, d) leaves the older messages (keepsOld_commitAtS · keepsOld_andThen · keepsOld_of_leaves at leaves_k1Quiet)
  hSmp_of         **hSmp at (l, d, X, arrs)**: ONE TEST ON THE PLAN IS LEFT: hn : every tenant whose pin is open in front has its number in seats below the plan's count of messages in front of the place
Nothing on soundness.
-/
import Johnson.Desc.K1.Law.LaterOne
import Johnson.Desc.K1.Law.MgK1
import Johnson.Desc.K1.Law.SmpNamedEarlierMessages

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open OnBytes.Maker
open VerifiableInference.Desc.First (S ModelPart Item Pub Meaning Numbers flatPlacesOf)
open VerifiableInference.Desc.Sound (Mem linksFull smpNamed)
open VerifiableInference.Desc.K13.Law (openAt)
open OnBytes.Model.Stages (LinkH)
open IM (k1Ix k1Reads k1Quiet)

variable {Pp W : Type}

theorem keepsOld_blkL (Z : ProofFile.Pub) (G : ProofFile.Ground) (l : ℕ) (d : Bool) (X : LinkH)
    (arrs : Option (List ℕ)) : KeepsOld (fun s : S => s.st) (blkL Z G l d X arrs) := by
  cases d with
  | true => exact keepsOld_commitAtS _ _ _ _
  | false =>
    exact keepsOld_andThen _ _ _ _ (keepsOld_commitAtS _ _ _ _)
      (keepsOld_of_leaves _ _ (leaves_k1Quiet (leavesAtt _) l X))

/-- **hSmp, to the binder's letter, at smpNamed.** -/
theorem hSmp_of (cs : Codes) (seats : List (ℕ × ℕ)) (N : Numbers) (Mg : Meaning Pp W)
    (ms : List Mem) (Z : ProofFile.Pub) (G : ProofFile.Ground) (l : ℕ) (d : Bool) (X : LinkH)
    (arrs : Option (List ℕ))
    (hn : ∀ u ∈ First.sampledIn N (openAt linksFull (flatPlacesOf linksFull true) (noL l d)),
      seats.idxOf u < N.msgsAt (flatPlacesOf linksFull true)[noL l d]?) :
    SmpLeft cs (blkL Z G l d X arrs)
      (InAt N Mg linksFull (flatPlacesOf linksFull true) (noL l d)) (smpNamed cs seats) ms
      (First.sampledIn N (openAt linksFull (flatPlacesOf linksFull true) (noL l d))) :=
  fun x x' y hy hIn => by
    obtain ⟨_, rs, gs, _, h⟩ := hy
    exact smpLeft_named cs seats N Mg linksFull _ _ _ _ (keepsOld_blkL Z G l d X arrs) ms _ hn x x'
      y _ gs h hIn.1 hIn.2

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.keepsOld_blkL
#print axioms VerifiableInference.Desc.K1.hSmp_of
