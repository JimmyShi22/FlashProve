-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
E2E/KeyPartsHalves.lean: the letters onU and onOmega of the key file's prover (KeyParts,
E2E/KeyProver.lean), filled with the pairs of E2E/KeyHalves.lean at the parts' own letters. What is
named here: the stored columns, the eight blocks, the public data, the two readers. What stays a
letter: the places' numbers pU and pO, and every other field of KeyParts.

  stOf, bsOf, wtOf, rdOf   the parts' own letters as the pairs take them: the stored columns as
                 words; the eight at K.send; the reader of the index; the committer's values,
                 as keyProver hands them to the sendings
  onUOf, onOmegaOf   the two pairs
  withTestsOnUAndOmega     the parts with these two in place
  stOf_eq, shared_withHalves, weights_withHalves, send_withHalves, stored_withHalves   what that
      turns and what not
  recU_of_parts, recO_of_parts   the pairs' states on entry, at the prover's own stored columns

So of the pairs' letters these are one with the sendings' by text: A, weights, rand; st is the
prover's own (stOf_eq). No test on the shape stands around the pairs (see `proverSideOfGuardedSending`'s docstring,
E2E/KeyProverSideOfOwnTest.lean); that K.send is the key file's, that pU, pO are the chain's, and that K.lin
stands at K.send's shape and "LIN point" (keyProver lays both, and no field of KeyParts ties them)
are not shown here.

Limits.
- bsOf takes [] where the eight are not made, silently: the doors then fold over no block, or over
  the test on G_u alone, a state that is nobody's; that blocks returns at the key's written sizes is
  blocksK_made (KeyHalves.lean), and K.send.P is a letter here.
- No KeyParts value is given; every field but these two stays as K has it.
- The limits and the words of KeyHalves.lean stand.
- Nothing on completeness, soundness or hiding.
-/
import E2E.KeyProver
import E2E.KeyHalves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtPublicFiles.KeyLay
open OnBytes (TableKey)
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.K12 (P12 T12)
open Desc.K14 (St blocks)
open AtPublicFiles.KeyFile (KeyParts keyProver randK14 In2 sharedChainProverSidesInOrder)
open ProofFile.Honest (Common Placed Weights TableRand Front)
open ProofFile.Honest.K12.Light (doorUF doorOmegaF colsLoc colsOpened sentOf)

variable {W₀ Rc X₀ X Wk : Type}

/-- The stored columns as words. -/
def stOf (K : KeyParts W₀ Rc X₀ X Wk) : W₀ → Rc → ℕ → ℕ → Option (List UInt64) :=
  fun w rc i x => (K.stored w rc i x).map (·.map OnBytes.Slice.ofF)

/-- The eight at the sendings' public data. -/
def bsOf (K : KeyParts W₀ Rc X₀ X Wk) : List (Block St Unit) := (blocks K.send.P).getD []

/-- The reader of the index, of the pair's input. -/
def wtOf (K : KeyParts W₀ Rc X₀ X Wk) : Common W₀ Rc TableKey → Weights := fun w => K.weights w.w₀

/-- The committer's values, as keyProver hands them to the sendings. -/
def rdOf (K : KeyParts W₀ Rc X₀ X Wk) : Common W₀ Rc TableKey → TableRand :=
  fun w => randK14 (K.rand w.rc)

/-- **The pair at the test on G_u**, at the parts' own letters; `withTestsOnUAndOmega` lays it. -/
def onUOf (K : KeyParts W₀ Rc X₀ X Wk) (pU : P12) : Placed Empty (In2 W₀ Rc) X₀ :=
  proverSideOfTestOnU K.send pU (bsOf K) (stOf K) (wtOf K) (rdOf K)

/-- **The pair at the test on G_omega, behind the guard**, at the parts' own letters; `withTestsOnUAndOmega`
lays it. -/
def onOmegaOf (K : KeyParts W₀ Rc X₀ X Wk) (pU pO : P12) : Placed Empty (In2 W₀ Rc) X₀ :=
  proverSideOfTestOnOmega K.send pU pO (bsOf K) (wtOf K) (rdOf K)

/-- **The parts with these two in place.** -/
def withTestsOnUAndOmega (K : KeyParts W₀ Rc X₀ X Wk) (pU pO : P12) : KeyParts W₀ Rc X₀ X Wk :=
  { K with onU := onUOf K pU, onOmega := onOmegaOf K pU pO }

/-- The stored columns are the prover's own. -/
theorem stOf_eq (K : KeyParts W₀ Rc X₀ X Wk) : stOf K = (keyProver K).storedWords := rfl

/-- The shared chain's halves at the new parts: the two pairs stand last. -/
theorem shared_withHalves (K : KeyParts W₀ Rc X₀ X Wk) (pU pO : P12) :
    (keyProver (withTestsOnUAndOmega K pU pO)).shared =
      sharedChainProverSidesInOrder (ProofFile.Honest.K14.proverSidesOfSharedRounds K.lin K.weights)
          (ProofFile.Honest.K14.proverSidesOfSharedSendings K.send K.weights fun c => randK14 (K.rand c)) ++
        [onUOf K pU, onOmegaOf K pU pO] := rfl

/-- No other reader turns. -/
theorem weights_withHalves (K : KeyParts W₀ Rc X₀ X Wk) (pU pO : P12) :
    (withTestsOnUAndOmega K pU pO).weights = K.weights ∧ (withTestsOnUAndOmega K pU pO).rand = K.rand := ⟨rfl, rfl⟩

/-- No public data turns. -/
theorem send_withHalves (K : KeyParts W₀ Rc X₀ X Wk) (pU pO : P12) :
    (withTestsOnUAndOmega K pU pO).send = K.send := rfl

/-- The prover with the pairs has K's stored columns. -/
theorem stored_withHalves (K : KeyParts W₀ Rc X₀ X Wk) (pU pO : P12) :
    (keyProver (withTestsOnUAndOmega K pU pO)).storedWords = (keyProver K).storedWords := rfl

/-- The state on entry at the test on G_u reads the prover's own stored columns. -/
theorem recU_of_parts (K : KeyParts W₀ Rc X₀ X Wk) (pU : P12) :
    (jobKU (X := X₀) K.send pU (bsOf K) (stOf K) (wtOf K) (rdOf K)).rec₀ =
      doorUF K.send.P (sentOf K.send.P.S) (bsOf K) (fun w : Common W₀ Rc TableKey => w.key)
        (fun w fr => colsLoc K.send.P ((keyProver K).storedWords w.w₀ w.rc) fr.seen.rounds) := rfl

/-- The state on entry at the test on G_omega. -/
theorem recO_of_parts (K : KeyParts W₀ Rc X₀ X Wk) (pU pO : P12) :
    (jobKO (X := X₀) K.send pU pO (bsOf K) (wtOf K) (rdOf K)).rec₀ =
      doorOmegaF K.send.P (sentOf K.send.P.S) (bsOf K) pU
        (fun w : Common W₀ Rc TableKey => w.key) colsOpened := rfl

end AtPublicFiles.KeyLay

#print axioms AtPublicFiles.KeyLay.stOf
#print axioms AtPublicFiles.KeyLay.bsOf
#print axioms AtPublicFiles.KeyLay.wtOf
#print axioms AtPublicFiles.KeyLay.rdOf
#print axioms AtPublicFiles.KeyLay.onUOf
#print axioms AtPublicFiles.KeyLay.onOmegaOf
#print axioms AtPublicFiles.KeyLay.withTestsOnUAndOmega
#print axioms AtPublicFiles.KeyLay.stOf_eq
#print axioms AtPublicFiles.KeyLay.shared_withHalves
#print axioms AtPublicFiles.KeyLay.weights_withHalves
#print axioms AtPublicFiles.KeyLay.send_withHalves
#print axioms AtPublicFiles.KeyLay.stored_withHalves
#print axioms AtPublicFiles.KeyLay.recU_of_parts
#print axioms AtPublicFiles.KeyLay.recO_of_parts
