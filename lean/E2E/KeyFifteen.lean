-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
E2E/KeyFifteen.lean: the sixteen fields of the key file's prover that neither withStoredColumnsAndPlan nor the
four proximity tests fill, laid into KeyParts. With these two beside it, no field of the parts stays
idle (E2E/KeyArgumentsAt.lean):

  withTests (withStoredColumnsAndPlan Xs Pl (withSendingsAndLookups K' Xs N f inR d) f g) Xs N Pl pU pO (matrixEntryOf f)
    (multiplicitiesGroups Xs) 0

Of K' only what these overwrite is read: nothing of it reaches the prover. fixedKeyParts serves as K'.

  withSendingsAndLookups   the fields

What the parts pass on is Unit. That costs nothing: every half of keyProver is typed at any X, X₀, so
none of them can hold anything there; they hand things on by the challenges and the rounds shown.

Limits. inR and d are letters: the test on the index and a member of the range. They must be ProofFile's
mxIn.inRange and mxIn.dummy, at FullSizeMatrix; a constant true would be wrong there, since at FullSizeMatrix the range is
not in the type. f must be keyOf's f and g's index: nothing here ties them. Nothing says that any
verifier accepts this prover. Nothing on any property.
-/
import E2E.KeyLookups

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace AtPublicFiles.KeyValues
open ProofFile.Honest (Weights)
open VerifiableInference.Desc.Key (Source)
open AtPublicFiles.KeyFile (KeyParts)

variable {W₀ Rc : Type}

/-- **The sixteen fields.** -/
def withSendingsAndLookups (K' : KeyParts W₀ Rc Unit Unit WitK) (Xs : Source) (N : H2U.PlaceNums)
    (f : W₀ → Weights) (inR : W₀ → Bool) (d : W₀) : KeyParts W₀ Rc Unit Unit WitK :=
  { K' with
    inRange := inR
    dummy := d
    own₀ := ()
    ownShared₀ := ()
    meet := fun a _ => a
    idx := indexMaskSending Xs
    msg := multiplicitiesSending f Xs
    w := batchedRowsSending f Xs N
    reads := keyReads
    jobs0 := keyJobs0 Xs
    jobs1 := keyJobs1 Xs
    wit := keyWit f Xs
    look0 := lookOf Xs N 0
    look1 := lookOf Xs N 1
    pile := constraintRowsAtClaimPoints Xs N
    batt := keyBatt Xs }

end AtPublicFiles.KeyValues
