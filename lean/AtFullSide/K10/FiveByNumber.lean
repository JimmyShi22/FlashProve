-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K10/FiveByNumber.lean: the closing of a segment (K10): the five statements of AtFullSide/K10/FiveHonest.lean BY NUMBER: at
each of the 25 numbers 14 l + `IM.nAt l` + 5, l < 25, of the first chain, in the forms in which the first thread's gatherer asks
them (`owesS_firstThread`, Johnson/Desc/ProofFile/Honest/Thread/FirstThreadOwes.lean), and with the family on shapes in hand.

  **`kindTen_five_at_number`**    `FiveAtBorder` at the closing of segment l
  `kindTen_plays_at_number`      its first field, at the gatherer's spelling of the thread: its premise on the closings' plays
  `kindTen_exchange_at_number`   its third field item by item: the gatherer's premise on what the closings' rows owe, with no use
                               made of the guard that the gatherer offers
  **`kindTen_fiveJ_at_number`**   `FiveAtBorderJ` at the family on shapes, under two premises more: the base's return, and the yes of the
                               run on shapes

This is the base prover: the filling `onlineProverPartsInUse matrixInput secondHashFunction Sz.ref openHonest` at the randomness `IndexCommitterCoins`. It is not the
online filling of E2E/TheHonestProver.lean, which is the same filling read through a map of the randomness.

Limits. As AtFullSide/K10/FiveHonest.lean's: premises: the head at the return, the maker's return at the base filling, Said gives
`SaidOk`. All statements speak at the stands at which the thread's invariant and Said hold; that they hold together at any run is
not proved here. The yes of the run on shapes is shown by no theorem here. The full size and the hash function `secondHashFunction` alone.
-/
import AtFullSide.K10.FiveHonest
import Johnson.Desc.ProofFile.Honest.K10.Pay.KindTenPlaces
import Johnson.Desc.ProofFile.Honest.K10.Pay.FiveJ
import Johnson.Desc.ProofFile.Honest.Thread.SharesS

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K10
open VerifiableInference.Desc
open Johnson.AtFull.Shape
open VerifiableInference.Desc.First.Shape
open OnBytes.HonestTrace (Sz)
open P5J (TS)
open ProofFile.Honest ProofFile.Honest.FirstThread
open ProofFile.Honest.Term (matrixInput)
open AtPublicFiles.AtFiles (FullSizeMatrix)
open ProofFile.Honest.K1 (firstScriptAt)

variable {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit} (head : HeadAtReturn files A)
  (made : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL
    (onlineProverPartsInUse matrixInput OnBytes.secondHashFunction Sz.ref openHonest) = .ok A)
  (numbers : FallNumbers) (input : Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells)
  (Said : Nat → Coins A.B → Mid (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) Unit → Prop)
  (hSaid : ∀ b k m, Said b k m → SaidOk b k m)

include made hSaid in
/-- **The five statements at the closing of segment l.** -/
theorem kindTen_five_at_number (fall : Nat → TS → List Fmt.Drawn → Option String) {l : Nat} (hl : l < 25) :
    FiveAtBorder
      (firstThread head ⟨firstScriptAt matrixInput Sz.ref openHonest A head.firstChain, numbers⟩ input) Said fall
      (14 * l + IM.nAt l + 5) := by
  obtain ⟨blk, hb, hk⟩ := ProofFile.Honest.K10.kindTen_at_each_border head.head hl
  exact kindTen_five_at_every_member_honest head made numbers input Said hSaid fall hb hk

include made hSaid in
/-- The closings' senders play: the gatherer's premise, at its spelling of the thread. -/
theorem kindTen_plays_at_number : ∀ l, l < 25 →
    PlaysS (firstLetters head ⟨firstScriptAt matrixInput Sz.ref openHonest A head.firstChain, numbers⟩ input).thread Said
      (14 * l + IM.nAt l + 5) :=
  fun _ hl => (kindTen_five_at_number head made numbers input Said hSaid (fun _ _ _ => none) hl).plays

include made hSaid in
/-- What the closings' rows owe, item by item: the gatherer's premise at the closings. -/
theorem kindTen_exchange_at_number : ∀ l, l < 25 → ∀ j : VerifiableInference.Desc.First.Item,
    j ∈ ((firstLetters head ⟨firstScriptAt matrixInput Sz.ref openHonest A head.firstChain, numbers⟩ input).thread.row
      (14 * l + IM.nAt l + 5)).owes →
    ExchangeAtS (firstLetters head ⟨firstScriptAt matrixInput Sz.ref openHonest A head.firstChain, numbers⟩ input).thread
      Said (14 * l + IM.nAt l + 5) j :=
  fun _ hl j hj =>
    (exchangeS_iff _ _).1 (kindTen_five_at_number head made numbers input Said hSaid (fun _ _ _ => none) hl).exchange j hj

include made hSaid in
/-- **The five statements with the family on shapes in hand, at the closing of segment l.** -/
theorem kindTen_fiveJ_at_number {Bs : ProofFile.PureBase}
    (hB : ProofFile.baseOf A.Z (ProofFile.pureSeat OnBytes.secondHashFunction A.Z) = .ok Bs)
    (fall : Nat → TS → List Fmt.Drawn → Option String) (a₀ : ShA)
    (hyes : (firstZA (Tab.g A.Z Bs.G₀) (Tab.vals A.Z Bs.G₀)).yes a₀ 358 = true) {l : Nat} (hl : l < 25) :
    FiveAtBorderJ
      (firstThread head ⟨firstScriptAt matrixInput Sz.ref openHonest A head.firstChain, numbers⟩ input) Said
      (shapeJ (firstZA (Tab.g A.Z Bs.G₀) (Tab.vals A.Z Bs.G₀)) a₀) fall (14 * l + IM.nAt l + 5) :=
  fiveJ_of_five (kindTen_five_at_number head made numbers input Said hSaid fall hl)
    (ProofFile.Honest.K10.k10_next_first head _ input hB l hl hSaid fall a₀ hyes)

end AtFullSide.K10

#print axioms AtFullSide.K10.kindTen_five_at_number
#print axioms AtFullSide.K10.kindTen_plays_at_number
#print axioms AtFullSide.K10.kindTen_exchange_at_number
#print axioms AtFullSide.K10.kindTen_fiveJ_at_number
