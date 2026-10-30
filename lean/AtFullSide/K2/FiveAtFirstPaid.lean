-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K2/FiveAtFirstPaid.lean: the five debts of the code switch at each of its 25 members, at the
first thread as it is written, over the prover that the maker returns at the base filling, with the
written Script of the first chain in the script's place.

  k2_five_first   FiveAtBorder at each member of the kind

The premises are the maker's return, the head at that return, hp (the thread's script is the written
Script), hOk (what the laws read of Said) and hw: the input's public part is that of a typed instance.
The first test on the instance is no premise: the thread's input is a ready one.

  k2_five_at_every_member   the same in the form of the other kinds' tops: the Script written in the
                            thread's parts, the member named by its number in the chain's own list

Limits. Where the maker does not return, or no head stands at the return, the theorem holds of nothing.
-/
import AtFullSide.K2.FiveAtFirstThread
import AtFullSide.K2.AsksPaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K2.Base
open VerifiableInference.Desc (Chain Block Place KindName)
open P5J (TS F0T)
open AtPublicFiles.AtFiles
open ProofFile.Honest
open ProofFile.Honest.K1
open ProofFile.Honest.Term
open ProofFile.Honest.FirstThread

/-- The input's public part is that of a typed instance. -/
def TypedAtRun (w : LocB FullSizeMatrix) : Prop :=
  ∃ z : LPFD.Full.XF × OnBytes.Flat.RecFull, w.x.pub = (LPFD.Full.instanceAsPlainRecord z).pub

/-- **The five debts at each member of the kind, at the first thread with the written Script.** -/
theorem k2_five_first {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}
    (hA : baseMaker files = .ok A) (hd : HeadAtReturn files A) (parts : FirstThreadParts A)
    (hp : parts.script =
      firstScriptAt matrixInput OnBytes.HonestTrace.Sz.ref openHonest A hd.firstChain)
    (w : LocB FullSizeMatrix) (Said : Nat → Coins A.B → Mid (LocB FullSizeMatrix) Unit → Prop)
    (fall : Nat → TS → List Fmt.Drawn → Option String)
    (hOk : ∀ b k m, Said b k m → SaidOk b k m) (hw : TypedAtRun w)
    {b : Nat} {q : Place} (hb : P5J.At.ps[b]? = some q) (hq : q.kind = KindName.K2) :
    FiveAtBorder (firstThread hd parts w) Said fall b :=
  k2_five_first_of hA hd parts hp w Said fall hOk
    (fun Bs base O S => k2AsksPaid matrixInput openHonest files _ _ _ _ _ _ A Bs base hA hd.head O S
      _ 0 _ _ 339 _ _ _ w Said hOk (fun hv => hv.1) (fun _ => hw)) hb hq

/-- **At each member of the first chain of the kind K2**, in the form of the other kinds' tops. The
other two chains have no member of the kind. Conditional: the head, the maker's return, hOk and hw. -/
theorem k2_five_at_every_member {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}
    (head : HeadAtReturn files A) (made : baseMaker files = .ok A) (numbers : FallNumbers)
    (input : LocB FullSizeMatrix) (Said : Nat → Coins A.B → Mid (LocB FullSizeMatrix) Unit → Prop)
    (fall : Nat → TS → List Fmt.Drawn → Option String)
    (hOk : ∀ b k m, Said b k m → SaidOk b k m) (hw : TypedAtRun input) {b : Nat}
    {member : Block TS ProofFile.Cl} (atNumber : head.firstChain.blocksInOrder[b]? = some member)
    (ofTheKind : member.place.kind = KindName.K2) :
    FiveAtBorder
      (firstThread head
        ⟨firstScriptAt matrixInput OnBytes.HonestTrace.Sz.ref openHonest A head.firstChain, numbers⟩
        input)
      Said fall b := by
  have hps : P5J.At.ps[b]? = some member.place := by
    rw [← P5J.At.places_paid head.head.toAtMg.scope head.head.toAtMg.reads head.head.toAtMg.laid]
    simp [VerifiableInference.Desc.First.blockPlaces, atNumber]
  exact k2_five_first made head ⟨_, numbers⟩ rfl input Said fall hOk hw hps ofTheKind

end AtFullSide.K2.Base

#print axioms AtFullSide.K2.Base.k2_five_first
#print axioms AtFullSide.K2.Base.k2_five_at_every_member
