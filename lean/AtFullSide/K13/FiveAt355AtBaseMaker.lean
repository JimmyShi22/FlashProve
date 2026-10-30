-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K13/FiveAt355AtBaseMaker.lean: kind K13, the members' batching: THE FIVE STATEMENTS AT
NUMBER 355 OF THE PROOF FILE's FIRST CHAIN (`k13_five_at_firstScript`, FiveAt355AtFirstScript.lean
of this folder) AT THE NAMED MAKER `baseMaker` (E2E/BaseMaker.lean): the maker at the filling that
the honest prover's text reads through: at the matrices, the reference sizes and the honest prover's
own opening. One statement with its proof: a call; no definition.

`k13_five_at_baseMaker`: ALL ITS PREMISES: hA: `baseMaker files` returns A · hd: the head at A
(`HeadAtReturn`, Johnson/Desc/ProofFile/Honest/Thread/TheFirstThread.lean). That the opening's
filler of the pile is the written one holds by its text.

Limits and what is not claimed: those of FiveAt355AtFirstScript.lean, all of them. Above all: the
five are premises' forms, and neither this file nor any file that it imports shows that the thread
stands at 355 at any run; that the
maker returns, and that a head stands at its return, are premises. Nothing on soundness,
completeness or hiding.
-/
import AtFullSide.K13.FiveAt355AtFirstScript
import E2E.BaseMaker

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K13
open OnBytes
open ProofFile.Honest ProofFile.Honest.K1 ProofFile.Honest.Term
open AtPublicFiles.AtFiles
open P5J (TS)
open ProofFile.Honest.FirstThread

/-- **THE FIVE STATEMENTS AT 355, OVER THE PROVER THAT THE NAMED MAKER RETURNS**, at the first
thread with the written Script, at every Said, fall, numbers and input. -/
theorem k13_five_at_baseMaker {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}
    (hA : baseMaker files = .ok A) (hd : HeadAtReturn files A) (numbers : FallNumbers)
    (w : LocB FullSizeMatrix) (Said : Nat → Coins A.B → Mid (LocB FullSizeMatrix) Unit → Prop)
    (fall : Nat → TS → List Fmt.Drawn → Option String) :
    FiveAtBorder
      (firstThread hd
        ⟨firstScriptAt matrixInput OnBytes.HonestTrace.Sz.ref openHonest A hd.firstChain, numbers⟩
        w) Said fall 355 :=
  k13_five_at_firstScript hA hd numbers w rfl Said fall

end AtFullSide.K13

#print axioms AtFullSide.K13.k13_five_at_baseMaker
