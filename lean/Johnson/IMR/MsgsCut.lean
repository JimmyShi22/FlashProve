-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/MsgsCut.lean: THE
NUMBER OF ORACLE MESSAGES THAT THE VERIFIER's STATE HAS RECEIVED, AT EVERY CUT OF THE FIRST CHAIN's
FLAT LIST IN FRONT OF THE BLOCKS BEHIND THE LAST LINK, at an opening of onlineDescription: from the fold's
return alone. UNDER Johnson/IMR/MsgsSeat.lean's THREE NAMED PREMISES (one of them paid elsewhere,
one owed).

  msgs_at_cut: **O : Open … · H : SeatKeeps (InvR A) okB okP · K1Told · K2Adds A ok2 · OksAt (oksOf
      okB okP ok2) Z Bs.G₀ · k ≤ (frontOf c).length · every block of c.blocksInOrder.take k passes its test
      on the plan · A s · foldBlocks ft (c.blocksInOrder.take k) s rs cols = .ok r ⇒ r.1.st.oracles.size =
      s.st.oracles.size + ((c.blocksInOrder.take k).map toldMsgs).sum ∧ A r.1.** AT EVERY o, ANY ft. No
      "there is" stands in it.
  msgs_at_cut_but: **THE SAME WITH THE CODE SWITCHES SET APART: O · K1Told · k ≤ (frontOf c).length
      · the tests on the plan · hM · the fold's return ⇒ r.1.st.oracles.size = s.st.oracles.size +
      ((c.blocksInOrder.take k).map toldMsgs).sum.** hM: of each block c.blocksInOrder[j], j < k, that declares a
          round which draws positions (drawsPos):
          at the fold's own returns r₀ (cut j) and r₁ (cut j + 1):
      r₁.1.st.oracles.size = r₀.1.st.oracles.size + toldMsgs b. ANY FIRST STATE s; NO INVARIANT. WHO
      CAN PAY hM, PLACE BY PLACE: at a link: the switch's block's seat (K2Seat.lean) · this folder's
      "the walk's frame's link is l at the cut in front" and RecAll at that cut · K2's yes_size,
      notices_sent, told_tenants.
WHO CAN PAY. The three: see MsgsSeat.lean's head. OksAt: the seat's own numbers (SeatKeeps.lean's
pub_firstTree and pureSpots_firstTree for "firstTree = 0"; okB, okP, ok2 as A's chooser needs them).
The tests on the plan: F.planOk. A at the first state: A's chooser.
OBJECT · USER · LETTERS. Object: c := F.first, F := ProofFile.onlineDescription o's value; not verify(). User: the
third conjunct of bookAt (Johnson/Desc/First/Borders.lean). Letters: A, okB, okP, ok2.
Compiled with the whole library.
Limits. msgs_at_cut SAYS NOTHING UNTIL K2Adds IS PAID AT SOME A THAT EVERY MAKER KEEPS;
msgs_at_cut_but says, as it stands, that between two code switches the number grows by what the
blocks tell. Book-keeping. Nothing
on soundness.
-/
import Johnson.IMR.MsgsSeat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.Carry

open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.First (S)
open Meaning.K2 (frontOf)

variable {A : S → Prop} {okB : Array Stages.LinkH → Prop}
  {okP : VerifiableInference.Desc.First.K2.HeadPar → Prop}
  {ok2 : VerifiableInference.Desc.First.K2.P2 → Prop}
  {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl} {A' : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

/-- **THE NUMBER OF ORACLE MESSAGES AT EVERY CUT OF THE FIRST CHAIN's FLAT LIST IN FRONT OF THE
BLOCKS BEHIND THE LAST LINK**: from the fold's return alone, from any first state at which the
invariant holds. -/
theorem msgs_at_cut (O : IM.Open o pol lay KL F Z Bs base c A' B)
    (H : Meaning.K2.SeatKeeps (InvR A) okB okP) (h1 : K1Told) (h2 : K2Adds A ok2)
    (hok : OksAt (oksOf okB okP ok2) Z Bs.G₀) (k : Nat) (hk : k ≤ (frontOf c).length)
    (hp : ∀ b ∈ c.blocksInOrder.take k, b.planOk = true) (ft : Nat) (s : S) (ha : A s) (rs : List Fmt.RoundView)
    (cols : List OpenedColumn) (r : S × List Fmt.RoundView × List OpenedColumn)
    (h : foldBlocks ft (c.blocksInOrder.take k) s rs cols = .ok r) :
    r.1.st.oracles.size = s.st.oracles.size + ((c.blocksInOrder.take k).map toldMsgs).sum ∧ A r.1 := by
  obtain ⟨e, hf⟩ := seat_frontP carriedAll_told (seatCarry_msgs H h1 h2) O hok
  have e2 : c.blocksInOrder.take k = (frontOf c).take k := by
    rw [e, List.take_append_of_le_length hk]
  exact foldBlocks_told A msgsOf ft (c.blocksInOrder.take k)
    (fun b hb => hf b (List.mem_of_mem_take (e2 ▸ hb))) hp s rs cols r ha h

/-- **THE SAME WITH THE CODE SWITCHES SET APART: NO INVARIANT**: of each block among the first k
that declares a round which draws positions it is asked, AT THE FOLD's OWN TWO STATES, that the
step adds what the block tells; of every other block it is shown. -/
theorem msgs_at_cut_but (O : IM.Open o pol lay KL F Z Bs base c A' B) (h1 : K1Told) (k : Nat)
    (hk : k ≤ (frontOf c).length) (hp : ∀ b ∈ c.blocksInOrder.take k, b.planOk = true) (ft : Nat) (s : S)
    (rs : List Fmt.RoundView) (cols : List OpenedColumn)
    (hM : ∀ (j : Nat) (b : Block S ProofFile.Cl), j < k → c.blocksInOrder[j]? = some b → Marked drawsPos b →
      ∀ r₀ r₁ : S × List Fmt.RoundView × List OpenedColumn, foldBlocks ft (c.blocksInOrder.take j) s rs cols = .ok r₀ →
        foldBlocks ft (c.blocksInOrder.take (j + 1)) s rs cols = .ok r₁ →
        r₁.1.st.oracles.size = r₀.1.st.oracles.size + toldMsgs b)
    (r : S × List Fmt.RoundView × List OpenedColumn) (h : foldBlocks ft (c.blocksInOrder.take k) s rs cols = .ok r) :
    r.1.st.oracles.size = s.st.oracles.size + ((c.blocksInOrder.take k).map toldMsgs).sum := by
  have hok : OksAt oksOr Z Bs.G₀ :=
    ⟨trivial, Meaning.K2.pub_firstTree O.pub, fun _ _ _ => trivial, fun _ _ => trivial⟩
  obtain ⟨e, hf⟩ := seat_frontP carriedAll_or (seatCarry_or h1) O hok
  have et : ∀ j, j ≤ (frontOf c).length → c.blocksInOrder.take j = (frontOf c).take j := fun j hj => by
    rw [e, List.take_append_of_le_length hj]
  have eg : ∀ j, j < (frontOf c).length → c.blocksInOrder[j]? = (frontOf c)[j]? := fun j hj => by
    rw [e, List.getElem?_append_left hj]
  rw [et k hk] at hp h ⊢
  refine told_at_take drawsPos msgsOf ft (frontOf c) hf s rs cols k hp
    (fun j b hj hb hm r₀ r₁ f₀ f₁ => ?_) r h
  exact hM j b hj (by rw [eg j (by omega)]; exact hb) hm r₀ r₁ (by rw [et j (by omega)]; exact f₀)
    (by rw [et (j + 1) (by omega)]; exact f₁)

#print axioms msgs_at_cut
#print axioms msgs_at_cut_but

end Meaning.Carry
