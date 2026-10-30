-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/K2/HandedAtTheBook.lean: the kind "the code switch" (K2): AT WHATEVER BOOK bookWhole
RETURNS AT F0T, UNDER THE LIBRARY's HEAD AND THE OPENING, ON CHAIN 0, THE FRAME HANDS EACH SWITCH OF
THE PLAN ITS STRETCHES, AT EVERY RUN's COINS: `handed 0 p k` (Honest/K2/ScriptLots.lean) IS "some".
One lemma with its proof: a join of five calls; no definition; nothing is evaluated here; none of
the library's goals. It lies in the side library because it imports files of it.

By: `switch_lends_at_written` (AtFullSide/K14/SwitchesLend.lean, another group of authors'): at the
book that bookWhole returns at the written description the public test `lendsPart` says yes at each
member of placesW, at the switch's own part and address · `rawBook_same`
(AtFullSide/K14/RawAtTheBookAtHead.lean, theirs): under the head the book at F0T is that book ·
`places_at_head` (Honest/K2/Law/PlacesWritten.lean) · `lendPart_ok_iff`, `look_dueIs`
(Honest/Small/LendsRow.lean, a third group's): `lendPart` returns just where the test says yes.

WHAT IT IS NOT. WHETHER, NOT WHAT, NOR WHOSE: nothing on the coins that are handed: the test beneath
asks the runs' names and counts and that the owners' cuts fit: it would say yes as well at a book
that lent another owner's coins of that count. So this lemma does not say whose coins reach the
switch, nor from which coin on. Chain 0 alone. That a thread's book is what bookWhole returns at F0T
is not said. The merges are mergesByName's, which the frame's own text calls a guess.

NEAR, another group of authors': `switch_handed_at_maker_closed`
(AtFullSide/K5/SwitchesLendAtMakerClosed.lean; this library may not hold it): the same end, over the
same law, at the book and the ground of what `onlineProverFromPublicFiles` returns, under the head and that return. Here:
at whatever bookWhole returns at F0T, at the base's ground, under the head and the opening. That the
two books are one is not said here.

Limits. Closed facts by Lean's kernel lie beneath, eight of them in SwitchesLend.lean. The full
size; the format's second hash function. All limits of SwitchesLend.lean stand. Nothing on any property.
-/
import AtFullSide.K14.SwitchesLend
import AtFullSide.K14.RawAtTheBookAtHead
import Johnson.Desc.ProofFile.Honest.K2.ScriptLots

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K2
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.First (S)
open Johnson.G (proofSendsFull)
open P5J (AtMgA F0T TS)
open _root_.Desc.K14.Law (secondAt seatZ)
open ProofFile.Honest
open ProofFile.Honest.K2 (SwitchPlace switchPlaces handed)
open ProofFile.Honest.K2.Law (placesW places_at_head)
open AtFullSide.K14 (switch_lends_at_written rawBook_same bookWhole_returns_raw
  bookRaw_returns_written)

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {B : ProverCoinCounts}

/-- THE HEAD, THE OPENING AND THE BOOK ARE PREMISES. **AT THAT BOOK, ON CHAIN 0, EACH SWITCH OF THE
PLAN IS HANDED ITS STRETCHES, AT EVERY RUN's COINS.** -/
theorem handed_at_book (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    (hB : bookWhole (F0T OnBytes.secondHashFunction Zp Np cF) proofSendsFull.1 proofSendsFull.2.1
      proofSendsFull.2.2 (mergesByName (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder) = .ok B)
    {p : SwitchPlace} (hp : p ∈ switchPlaces Zp Bs.G₀) (k : Coins B) :
    (handed 0 p k).isSome = true := by
  obtain ⟨W, hW⟩ := bookRaw_returns_written
  have hWP := bookWhole_returns_raw W hW
  obtain rfl : B = W := rawBook_same h.scope h.laid hWP hB
  have hp' : p ∈ placesW := by
    rw [← places_at_head h.toAtMg O]
    exact hp
  have t := switch_lends_at_written hWP hp'
  have e : (fun o => (k.look 0 o).1) = lookDue B 0 := funext (look_dueIs k 0)
  obtain ⟨y, hy⟩ := (lendPart_ok_iff B (B.rowsOf 0) (k.look 0) ⟨p.place, 0⟩ _).2 (by
    rw [e]
    exact t)
  unfold handed
  rw [hy]
  rfl

end AtFullSide.K2

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms AtFullSide.K2.handed_at_book
