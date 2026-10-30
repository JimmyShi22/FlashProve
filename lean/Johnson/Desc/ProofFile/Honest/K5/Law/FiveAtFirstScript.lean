-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K5/Law/FiveAtFirstScript.lean: conditional: the five statements that the
attention sub-protocol (kind K5) owes at its border, at the first thread of the base prover at
matrixInput, at the reference sizes, with the first chain's script laid at its value, firstScriptAt
(AtFullSide/K1/FirstScript.lean). Three theorems, no definition.

  kindFive_five_at_first_script   FiveAtBorder at the border of group g, at every Said and every fall
  kindFive_five_at_honest_opening the same at baseMaker's filling, where the key reader is the kind's
                                  by the text of openHonest
  kindFive_five_at_every_member_honest   the same at every member of the first chain of the kind K5

The premises of the first theorem, all of them: head, the library's head at the return; keyReader, the filling's reader of
the key points is the kind's; made, the maker returns at this filling; that g is below 12. numbers, the
stated numbers of the falls, and input, the run's input, are letters.

How. kindFive_five_at_first_thread (FiveAtBase.lean in this folder), with its three premises on the
script paid: treesFixed_first, k5ScriptQ_at_firstScript at traceIsFull_at_base, validCellsHold_at_first.

Limits.
  * Conditional on the head at the return, on the maker's return and, in the first theorem, on
    keyReader, which are not proved here.
  * Each statement is an implication from the thread's invariant with Said in front of the member.
    Nobody has a state that meets it at one of these twelve borders; where none does they say nothing.
    ReadyInput is empty where the prover has no trace.
  * This is the base prover at IndexCommitterCoins, not onlineFilling (E2E/TheHonestProver.lean), which is the same
    filling read through a map of the randomness.
  * This is not the kind's acceptance. That also asks the kind's sides to be lent their coins, and
    states that reach these borders.
  * NOT IN FRONT OF A LAW OVER COINS. The full size alone, at the earlier hash
    OnBytes.secondHashFunction.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.FiveAtBase
import Johnson.Desc.ProofFile.Honest.K5.Law.ScriptAtFirst
import AtFullSide.K5.ValidCellsAtFirst
import E2E.BaseMaker
import Johnson.Desc.ProofFile.Honest.K5.Law.TraceAtMatrix
import AtFullSide.K1.FirstScriptFixed

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open ProofFile.Honest.FirstThread (HeadAtReturn FirstThreadParts FallNumbers firstThread)
open AtPublicFiles.AtFiles (FullSizeMatrix)
open ProofFile.Honest.Term (matrixInput baseMaker)
open OnBytes.HonestTrace (Sz)
open P5J (TS)

variable {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}

/-- **THE FIVE STATEMENTS AT THE FIRST THREAD, AT THE SCRIPT's VALUE.** Conditional: every premise
stands, by name, in the file's head. Each statement is an implication from the thread's invariant with
Said in front of the member. -/
theorem kindFive_five_at_first_script (head : HeadAtReturn files A) (opening : OnlineProverArguments)
    (keyReader : opening.keyOf = keyOfK3)
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL
      (onlineProverPartsInUse matrixInput OnBytes.secondHashFunction Sz.ref opening) = .ok A)
    (numbers : FallNumbers) (input : Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) {g : Nat} (groupInRange : g < 12)
    (Said : Nat → Coins A.B → Mid (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) Unit → Prop)
    (fall : Nat → TS → List Fmt.Drawn → Option String) :
    FiveAtBorder
      (firstThread head
        ⟨ProofFile.Honest.K1.firstScriptAt matrixInput Sz.ref opening A head.firstChain, numbers⟩ input)
      Said fall (borderOf g) :=
  kindFive_five_at_first_thread head matrixInput Sz.ref opening keyReader made _ input groupInRange
    (ProofFile.Honest.K1.treesFixed_first head.head made)
    (k5ScriptQ_at_firstScript head matrixInput opening made
      (traceIsFull_at_base head Sz.ref opening made) groupInRange)
    (validCellsHold_at_first made head.firstChain input) Said fall

/-- **The same at the opening of the online filling.** Conditional: the head and the maker's return. -/
theorem kindFive_five_at_honest_opening (head : HeadAtReturn files A)
    (made : baseMaker files = .ok A)
    (numbers : FallNumbers) (input : Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) {g : Nat} (groupInRange : g < 12)
    (Said : Nat → Coins A.B → Mid (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) Unit → Prop)
    (fall : Nat → TS → List Fmt.Drawn → Option String) :
    FiveAtBorder
      (firstThread head
        ⟨ProofFile.Honest.K1.firstScriptAt matrixInput Sz.ref openHonest A head.firstChain, numbers⟩ input)
      Said fall (borderOf g) :=
  kindFive_five_at_first_script head openHonest rfl made numbers input groupInRange Said fall

/-- **AT EACH MEMBER OF THE FIRST CHAIN OF THE KIND K5**, at the opening of the online filling. The other
two chains have no member of the kind: kindFive_not_in_shared, kindFive_not_in_second
(KindFivePlaces.lean in this folder). Conditional: the head and the maker's return. -/
theorem kindFive_five_at_every_member_honest (head : HeadAtReturn files A)
    (made : baseMaker files = .ok A)
    (numbers : FallNumbers) (input : Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells)
    (Said : Nat → Coins A.B → Mid (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) Unit → Prop)
    (fall : Nat → TS → List Fmt.Drawn → Option String) {b : Nat}
    {member : VerifiableInference.Desc.Block TS ProofFile.Cl}
    (atNumber : head.firstChain.blocksInOrder[b]? = some member) (ofTheKind : member.place.kind = .K5) :
    FiveAtBorder
      (firstThread head
        ⟨ProofFile.Honest.K1.firstScriptAt matrixInput Sz.ref openHonest A head.firstChain, numbers⟩ input)
      Said fall b := by
  obtain ⟨g, groupInRange, rfl⟩ := kindFive_only_at_borders head.head atNumber ofTheKind
  exact kindFive_five_at_honest_opening head made numbers input groupInRange Said fall

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.kindFive_five_at_first_script
#print axioms ProofFile.Honest.K5.kindFive_five_at_honest_opening
#print axioms ProofFile.Honest.K5.kindFive_five_at_every_member_honest
