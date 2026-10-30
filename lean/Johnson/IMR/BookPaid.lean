-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/BookPaid.lean: AS MANY ROOTS AS TREES, AND THE TREE AT PLACE z BEARS THE NUMBER z:
BookSeat.lean's descPure_ordered WITH ITS TWO PREMISES PAID BY OTHER FILES' LAWS, CALLED: NO
PREMISE IS LEFT BUT onlineDescription's RETURN AND THE YES:

  ordered_iff: orderedP B r (Johnson/IMR/BookSeat.lean) is Sound.BookStep 0 B r
    (Johnson/Desc/Sound/BookInOrder.lean), by unfolding.
  recv_ordered: the plain ground's receiving at 0 hands it on: K1.recvP_received
    (Johnson/Desc/Sound/FenceSendGround.lean) and Sound.bookStep_received (BookInOrder.lean).
  p12_firstTree: at the numbers that the maker lays at the first chain's last test the first tree's
    number is 0: H2K.Made.places_firstTree (Johnson/Desc/K12/Law/FirstTreeOfMade.lean); where the
    maker lays nothing the place's own text has 0.
  k12_ordered: kind K12's block there, where it passes its own test on the plan: K12.Coin's
    atFinish_bookStep (Johnson/Desc/K12/Law/BookAtFinish.lean), with early_of_planOk and
    answers_of_planOk (Johnson/Desc/K12/Law/Top.lean).
  descPure_bookOrd: the law stated above. descPure_bookStepAt: BookStep 0 at every record that the
    first chain's fold passes through.
OBJECT: ProofFile.onlineDescription's value, at every o. USER: whoever spends the law.
Not claimed: that the count of roots is what the plan's declared rounds hold. No soundness.
-/
import Johnson.IMR.BookSeat
import Johnson.Desc.Sound.FenceSendGround
import Johnson.Desc.Sound.BookInOrder
import Johnson.Desc.K12.Law.BookAtFinish
import Johnson.Desc.K12.Law.FirstTreeOfMade
import Johnson.Desc.K12.Law.Top

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.K2

open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.Sound (BookStep bookStep_received)
open ProofFile (Pub)

theorem ordered_iff (B : TreeBook) (r : Nat) : orderedP B r ↔ BookStep 0 B r := Iff.rfl

theorem recv_ordered {L : Type} (d d' : _root_.Desc.Plain.DState L) (sent : Array OracleNotice)
    (ids : Array Nat) (h : Ground.recvP 0 d sent = some (ids, d'))
    (k : orderedP d.book d.roots) : orderedP d'.book d'.roots := by
  obtain ⟨lay, hr⟩ := K1.recvP_received 0 d d' sent ids h
  exact bookStep_received 0 sent lay _ _ _ _ _ _ hr k

theorem p12_firstTree (m : Johnson.G.OfPlan.Made) : (H2U.p12OfMade m).nums.firstTree = 0 := by
  unfold H2U.p12OfMade
  dsimp only
  split
  · rename_i X hX
    unfold H2U.proximityTestParametersAt
    split
    · rfl
    · split
      · exact (H2K.Made.places_firstTree m X hX).1
      · rfl
  · rfl

theorem k12_ordered (m : Johnson.G.OfPlan.Made) (s s' : S) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64)))
    (hp : (K12.atFinish (H2U.p12OfMade m)).planOk = true)
    (h : (K12.atFinish (H2U.p12OfMade m)).decide s rs gs = .ok s')
    (k : orderedP s.book s.roots) : orderedP s'.book s'.roots := by
  have hp' := atFinish_planOk hp
  have hf := p12_firstTree m
  have := K12.Coin.atFinish_bookStep (H2U.p12OfMade m) (H2K.JointK.early_of_planOk _ hp')
    (H2K.JointK.answers_of_planOk _ hp') s s' rs gs h (by rw [hf]; exact k)
  rw [hf] at this
  exact this

/-- **THE ROW's FIRST LAW: A YES OF THE FILE's DECISION: THE FIRST CHAIN's LAST RECORD COUNTS AS
MANY ROOTS AS ITS BOOK HAS TREES, AND THE TREE AT PLACE z BEARS THE NUMBER z.** -/
theorem descPure_bookOrd {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst}
    (h : ProofFile.onlineDescription o pol lay KL = .ok F) {x : ProofFile.Inst} {v₁ v₂ v₃ : Fmt.View}
    (hr : F.run x v₁ v₂ v₃ = true) :
    ∃ (Z : Pub) (A : ProofFile.SharedSeat) (B : ProofFile.SecondSeat) (c : Chain S ProofFile.Cl) (e₁ : S),
      ProofFile.pureRoad.pub o pol lay KL = .ok Z ∧
      F = ProofFile.fileDescBy o ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c ∧
      chainAt "the first chain" 0 c.blocksInOrder (ProofFile.startS Z x.pub) (withEmptySealRound v₁) = .ok e₁ ∧
      e₁.roots = e₁.book.trees.size ∧
      ∀ (z : Nat) (T : Tree), e₁.book.trees[z]? = some T → T.number = z :=
  descPure_ordered recv_ordered k12_ordered h hr

/-- **AND AT EVERY RECORD THAT THE FIRST CHAIN's FOLD PASSES THROUGH**, in the form of
Sound.BookStep. -/
theorem descPure_bookStepAt {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst}
    (h : ProofFile.onlineDescription o pol lay KL = .ok F) {x : ProofFile.Inst} {v₁ v₂ v₃ : Fmt.View}
    (hr : F.run x v₁ v₂ v₃ = true) :
    ∃ (Z : Pub) (A : ProofFile.SharedSeat) (B : ProofFile.SecondSeat) (c : Chain S ProofFile.Cl),
      ProofFile.pureRoad.pub o pol lay KL = .ok Z ∧
      F = ProofFile.fileDescBy o ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c ∧
      ∀ (l₁ l₂ : List (Block S ProofFile.Cl)) (t : S) (rs : List Fmt.RoundView)
        (cols : List VerifiableInference.Desc.OpenedColumn), c.blocksInOrder = l₁ ++ l₂ →
        foldBlocks 0 l₁ (ProofFile.startS Z x.pub) (withEmptySealRound v₁).rounds (withEmptySealRound v₁).opened =
          .ok (t, rs, cols) → BookStep 0 t.book t.roots :=
  descPure_sentenceAt (P := orderedP)
    ⟨recv_ordered, fun A B r hs k => K2.ordered_same 0 A B r hs k, k12_ordered⟩ empty_ordered h hr

#print axioms recv_ordered
#print axioms p12_firstTree
#print axioms k12_ordered
#print axioms descPure_bookOrd
#print axioms descPure_bookStepAt

end Meaning.K2
