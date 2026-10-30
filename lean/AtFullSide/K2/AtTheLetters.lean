-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K2/AtTheLetters.lean: the five debts of the code switch at the first chain's letters.

  k2_five_at_letters   FiveAtBorder at thread₁ and said₁, at each member of the kind, at every fall

The premises are the maker's return, the head at that return, the run, and hw: the run's input is of a
typed instance. What the laws read of Said is the walk's own first clause.

Limits. Where the maker does not return, or no head stands at the return, the theorem holds of nothing.
-/
import AtFullSide.K2.FiveAtFirstPaid
import AtFullSide.Honest.TheLettersFirst
import Johnson.Desc.ProofFile.Honest.Thread.SaidOkOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtFullSide.K2.Base
open VerifiableInference.Desc (Place KindName)
open P5J (TS)
open AtPublicFiles.AtFiles
open ProofFile.Honest
open ProofFile.Honest.Term
open ProofFile.Honest.FirstThread
open AtFullSide.Honest.TheLetters

variable [Inhabited P5J.TS] [Inhabited Desc.K14.St]

/-- **The five debts at each member of the kind, at the first chain's letters.** -/
theorem k2_five_at_letters {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}
    (hA : baseMaker files = .ok A) (h : HeadAtReturn files A)
    (R : Ready FullSizeMatrix IndexCommitterCoins ProofFile.Inst OnBytes.TableKey Cells Unit Unit)
    (fall : Nat → TS → List Fmt.Drawn → Option String) (hw : TypedAtRun R.own)
    {b : Nat} {q : Place} (hb : P5J.At.ps[b]? = some q) (hq : q.kind = KindName.K2) :
    FiveAtBorder (thread₁ h R) (said₁ h R) fall b :=
  k2_five_first hA h (first h) rfl R.own (said₁ h R) fall
    (fun _ _ _ hs => hs.1.1) hw hb hq

end AtFullSide.K2.Base

#print axioms AtFullSide.K2.Base.k2_five_at_letters
