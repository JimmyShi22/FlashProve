-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K10/FiveHonest.lean: THE CLOSING OF A SEGMENT (K10): ITS FIVE STATEMENTS AT EVERY MEMBER OF THE KIND, at the first chain's thread of the online part
(`firstThread`, Johnson/Desc/ProofFile/Honest/Thread/TheFirstThread.lean) with the script of the base prover (`firstScriptAt`, AtFullSide/K1/FirstScript.lean), at the
base filling. `kindTen_five_at_script` (AtFullSide/K10/FiveAtScript.lean) with its two named premises paid:
  hC      the public test on the code switch's closings: `closes_at_base` (AtFullSide/K10/ScriptRowsPaid.lean)
  hCopy   the message of a kept copy is, in the script's witness, the switch's own text: `copies_at_thread` (AtFullSide/K10/ScriptCopiesAt.lean)

  **`kindTen_five_at_every_member_honest`**   `FiveAtBorder` (it plays · behind · exchange · rides past · the step accepts) at every number b at which the first chain's
      list has a member of the kind K10, at every Said that gives `SaidOk` and every table of falls

What is left as premises: the head at the return · the maker's return at the base filling · Said gives `SaidOk`.

Limits. All five speak at every stand at which the thread's invariant and Said hold; that they hold together at any run is not proved here: where they hold at
none, the five hold for nothing. The full size and the hash function `secondHashFunction` alone. This is the base prover, whose table randomness has the type `IndexCommitterCoins`, not
`onlineFilling` (E2E/TheHonestProver.lean), which is the same filling read through a map of the randomness. This file proves no property of a prover or a protocol.
-/
import AtFullSide.K10.FiveAtScript
import AtFullSide.K10.ScriptRowsPaid
import AtFullSide.K10.ScriptCopiesAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K10
open VerifiableInference.Desc
open OnBytes.HonestTrace (Sz)
open P5J (TS)
open ProofFile.Honest ProofFile.Honest.FirstThread
open ProofFile.Honest.Term (matrixInput)
open AtPublicFiles.AtFiles (FullSizeMatrix)
open ProofFile.Honest.K1 (firstScriptAt)

/-- **The five statements at every member of the kind K10, at the base prover's script.** -/
theorem kindTen_five_at_every_member_honest {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}
    (head : HeadAtReturn files A)
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL
      (onlineProverPartsInUse matrixInput OnBytes.secondHashFunction Sz.ref openHonest) = .ok A)
    (numbers : FallNumbers) (input : Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells)
    (Said : Nat → Coins A.B → Mid (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) Unit → Prop)
    (hSaid : ∀ b k m, Said b k m → SaidOk b k m) (fall : Nat → TS → List Fmt.Drawn → Option String) {b : Nat}
    {member : Block TS ProofFile.Cl} (atNumber : head.firstChain.blocksInOrder[b]? = some member)
    (ofTheKind : member.place.kind = .K10) :
    FiveAtBorder
      (firstThread head ⟨firstScriptAt matrixInput Sz.ref openHonest A head.firstChain, numbers⟩ input) Said fall b :=
  kindTen_five_at_script head made numbers input Said hSaid fall atNumber ofTheKind (closes_at_base head.head made)
    (copies_at_thread head made numbers input)

end AtFullSide.K10

#print axioms AtFullSide.K10.kindTen_five_at_every_member_honest
