-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K10/FiveAtLetters.lean: the closing of a segment (K10): its five statements AT THE FIRST CHAIN's NAMED LETTERS
(AtFullSide/Honest/TheLettersFirst.lean): the thread `thread₁`, what is said `said₁`, the numbers `numbers`, and the family on shapes
`J₁`. Instances of AtFullSide/K10/FiveByNumber.lean and AtFullSide/K10/FiveHonest.lean, which are general in these letters.

  **`kindTen_five_at_letters`**     `FiveAtBorder (thread₁ h R) (said₁ h R) fall` at the closing of segment l, l < 25, at every table of falls
  `kindTen_five_of_kind_at_letters`  the same at every number at which the first chain's list has a member of the kind K10
  **`kindTen_fiveJ_at_letters`**    `FiveAtBorderJ` at `J₁ h F`, under one premise: the yes of the run on shapes

"Said gives `SaidOk`" is no premise here: at `said₁` it holds by `saidOk_of_walk` (Johnson/Desc/ProofFile/Honest/Thread/SaidOkOf.lean).

Limits. Premises: the head at the return and the maker's return at the base filling. This is the base prover, whose table
randomness has the type `IndexCommitterCoins`. All statements speak at the stands at which the thread's invariant and `said₁` hold; that a run
stands there is not proved here. The yes of the run on shapes is shown by no theorem here.
-/
import AtFullSide.K10.FiveByNumber
import AtFullSide.Honest.TheLettersFirst
import Johnson.Desc.ProofFile.Honest.Thread.SaidOkOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K10
open VerifiableInference.Desc
open OnBytes.HonestTrace (Sz)
open OnBytes (TableKey)
open P5J (TS)
open ProofFile.Honest ProofFile.Honest.FirstThread
open ProofFile.Honest.Term (matrixInput)
open AtPublicFiles.AtFiles (FullSizeMatrix)
open AtFullSide.Honest.TheLetters

variable [Inhabited P5J.TS] [Inhabited Desc.K14.St]
variable {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit} (h : HeadAtReturn files A)
  (made : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL
    (onlineProverPartsInUse matrixInput OnBytes.secondHashFunction Sz.ref openHonest) = .ok A)
  (R : Ready FullSizeMatrix IndexCommitterCoins ProofFile.Inst TableKey Cells Unit Unit)

include made in
/-- **The five statements at the closing of segment l, at the first chain's named letters.** -/
theorem kindTen_five_at_letters (fall : Nat → TS → List Fmt.Drawn → Option String) {l : Nat} (hl : l < 25) :
    FiveAtBorder (thread₁ h R) (said₁ h R) fall (14 * l + IM.nAt l + 5) :=
  kindTen_five_at_number h made (numbers h) R.own (said₁ h R) (fun b k m hs => saidOk_of_walk _ b k m hs) fall hl

include made in
/-- The same at every member of the kind. -/
theorem kindTen_five_of_kind_at_letters (fall : Nat → TS → List Fmt.Drawn → Option String) {b : Nat}
    {member : Block TS ProofFile.Cl} (atNumber : h.firstChain.blocksInOrder[b]? = some member)
    (ofTheKind : member.place.kind = .K10) : FiveAtBorder (thread₁ h R) (said₁ h R) fall b :=
  kindTen_five_at_every_member_honest h made (numbers h) R.own (said₁ h R)
    (fun b k m hs => saidOk_of_walk _ b k m hs) fall atNumber ofTheKind

include made in
/-- **The five statements with the family on shapes in hand, at the named letters.** -/
theorem kindTen_fiveJ_at_letters (F : OpenFiles A) (fall : Nat → TS → List Fmt.Drawn → Option String)
    (hyes : (Johnson.AtFull.Shape.firstZA (Johnson.AtFull.Shape.Tab.g A.Z F.base.G₀)
      (Johnson.AtFull.Shape.Tab.vals A.Z F.base.G₀)).yes Johnson.AtFull.Shape.startShA 358 = true) {l : Nat}
    (hl : l < 25) : FiveAtBorderJ (thread₁ h R) (said₁ h R) (J₁ h F) fall (14 * l + IM.nAt l + 5) :=
  kindTen_fiveJ_at_number h made (numbers h) R.own (said₁ h R) (fun b k m hs => saidOk_of_walk _ b k m hs) F.seat fall
    Johnson.AtFull.Shape.startShA hyes hl

end AtFullSide.K10

#print axioms AtFullSide.K10.kindTen_five_at_letters
#print axioms AtFullSide.K10.kindTen_five_of_kind_at_letters
#print axioms AtFullSide.K10.kindTen_fiveJ_at_letters
