-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/GrownBK.lean: THE TERMS AND THE RULES THAT NAME NO SEAT (openAt · BK · XK · Yes · Hands
· S1 · s1_of_hands · xk_parts · Yes.under · Hands.under · Keeps4 · hands_quiet · hands_same) STAND
IN THE LIGHT FILE Johnson/IMR/HandsDef.lean, WHICH IMPORTS NOTHING OF Johnson/IMR/; HERE STAY
hands_joined AND front_hands. THE REST OF THIS HEAD MAY DIFFER FROM THE TEXT: THE TEXT HOLDS.

ft, THE FIRST TREE, IS A LETTER OF Yes · Hands · S1 (at a
sender or a switch the trees' numbers hang on ft, and a field could be unpayable at a wrong one) · E
: ℕ → S → Bool BEARS THE BORDER (XK k s := BK k s && E k s; the field «more» asks E (k + 1) s'): for
the door's names that are open only between maker and last asker. WHEN N IS CLOSED AT THE TERM {
numbersOf … }.withTold ps told, S1 IS MEANT UNDER ITS NAMED TESTS ON THE PLAN (bookFit · fenceFit ·
numbersFit · rowsAtFit …): as long as N is a letter each payer brings what it needs (hT | hM).
Keeps4 (Johnson/IMR/HandsDef.lean) IS Rq (Johnson/Desc/First/Link/Law/RbDef.lean): field by field
the same.
THE TABLE OF JOINTS' PROMISE AT THE PROOF FILE, THE RECORD's HALF: «EACH BLOCK's YES HANDS THE
GROWTH ON»: THE SKELETON: A FORM WITH ITS DEBTS COUNTED, NOT A PAYMENT.
THE STATEMENT: X k s := BK k s && ‹more Bools on the record› s, BK k s := shapeAt links ps[k]? s &&
rowsHeld N (O k) s && membersHeld N (O k) s && bookAt N ps[k]? s, O k the table's open set at border
k
(Johnson/Desc/First/Borders.lean § 7); (S1): a block's yes from s to s' keeps a mark, and, with no
mark in front and behind, hands X k s on to X (k + 1) s'. It is the middle clause of EachGrown
(Johnson/Desc/K12/Coin/GrownPromise.lean), at the blocks' steps.
STILL LETTERS: E · N (the term { numbersOf … }.withTold ps told is to be laid in) · ft.
OBJECT. The blocks of c.blocksInOrder, c onlineDescription's first chain; ps := c.blocksInOrder.map (·.place).
LETTERS. N : Numbers · links : List ModelPart · E : ℕ → S → Bool (further Bools on the record, border by
border: LETTERS HERE) · ft: the first tree · k: the block's number in the flat list.

  openAt · BK · XK   the statement's terms.
  Yes ft b s s'        b's step says yes from s to s', at the first tree ft, at some rounds and columns.
  Hands N links ps E ft k b   WHAT ONE BLOCK OWES: six fields: mark · shape · rows · members · book · more.
  S1 · s1_of_hands  (S1) at a chain, from Hands at every block of its flat list.
  Hands.under       the debt of a SEATED block is its lot's block's: b.UnderR b'
                    (Johnson/IMR/SeatForm.lean: alone_underR) carries Hands from b' to b.
  hands_joined      at a link's first place (Johnson/IMR/SameSpot.lean: Joined): two stages: the
                    lot's block's step, then the row's «opened»: what the two owe together.
  Keeps4 · hands_quiet   AT A QUIET ROW (it closes and opens no class of rows and no pin): rows · members · book follow from ONE relation on the two records (the statement's groups, the book's places, the numbers of trees and of oracle messages are as they were) and «the plan's two
                    numbers are the same at the two places»; shape · mark · more stay the block's own.
  hands_same        a block whose yes hands the record back owes only what the TABLE says of its two borders.
  front_hands       THE FIRST MEMBER: c.blocksInOrder[0] (Johnson/IMR/FrontSeat.lean: front_of): under «X 0 s
                    → X 1 s», a sentence on the table alone.

What is not claimed. NO BLOCK BUT THE FRONT IS PAID HERE, AND THAT ONE UNDER A SENTENCE ON THE TABLE. (S0). That X is inductive at a sender or a switch. The promise's other half (inOrder · pubHeld · samplesHeld · shown · no collision · pubP · decodes) and the ties (t1) · (t3) · (t4) · (t5). From a piece's «out a τ = some b» to the block's step. No soundness.
-/
import Johnson.IMR.HandsDef
import Johnson.IMR.FrontSeat
import Johnson.IMR.FirstSeats

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace IM

open VerifiableInference.Desc (Block Chain FileDescription Place KindName)
open VerifiableInference.Desc.First (S ModelPart Numbers)
open ProofFile (Cl)

/-- **At a link's first place: two stages**: the lot's block's step from s to m, then the row's «opened» from m to s'. What the two owe together is Hands of the seated block. -/
theorem hands_joined {N : Numbers} {links : List ModelPart} {ps : List Place} {E : ℕ → S → Bool} {ft k : ℕ}
    {Z : ProofFile.Pub} {l : ℕ} {b b' : Block S Cl} {a : Place} (hj : Joined Z l b b' a)
    (H : ∀ fs f, Johnson.Desc.First.Walk.Seat.framesOf Z.p.built.links Z.first Z.p.X = .ok fs →
      fs[l]? = some f → ∀ s m s', Yes ft b' s m → m.failed = none → f.opened m = .ok s' →
        s'.failed = none →
        (s.failed = none) ∧ (XK N links ps E k s = true → XK N links ps E (k + 1) s' = true)) :
    Hands N links ps E ft k b := by
  have key : ∀ s s', Yes ft b s s' → s'.failed = none ∧ s.failed = none ∧
      (XK N links ps E k s = true → XK N links ps E (k + 1) s' = true) := by
    intro s s' hy
    obtain ⟨rs, cols, n, e⟩ := hy
    obtain ⟨fs, f, m, hfs, hf, h1, h2, h3, h4, -⟩ := hj.step e
    obtain ⟨g1, g2⟩ := H fs f hfs hf s m s' ⟨rs, cols, n, h1⟩ h2 h3 h4
    exact ⟨h4, g1, g2⟩
  refine ⟨fun s s' hy h => absurd (key s s' hy).2.1 h, fun s s' hy _ _ hx => ?_,
    fun s s' hy _ _ hx => ?_, fun s s' hy _ _ hx => ?_, fun s s' hy _ _ hx => ?_,
    fun s s' hy _ _ hx => ?_⟩
  · exact (xk_parts ((key s s' hy).2.2 hx)).1
  · exact (xk_parts ((key s s' hy).2.2 hx)).2.1
  · exact (xk_parts ((key s s' hy).2.2 hx)).2.2.1
  · exact (xk_parts ((key s s' hy).2.2 hx)).2.2.2.1
  · exact (xk_parts ((key s s' hy).2.2 hx)).2.2.2.2

/-- **THE FIRST MEMBER: THE FRONT**, at every o: under a sentence on the table alone. -/
theorem front_hands {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst}
    {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
    {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} (O : Open o pol lay KL F Z Bs base c A B)
    {N : Numbers} {links : List ModelPart} {E : ℕ → S → Bool} {ft : ℕ}
    (hT : ∀ s, s.failed = none → XK N links (c.blocksInOrder.map (·.place)) E 0 s = true →
      XK N links (c.blocksInOrder.map (·.place)) E 1 s = true) :
    ∀ b, c.blocksInOrder[0]? = some b → Hands N links (c.blocksInOrder.map (·.place)) E ft 0 b := by
  intro b hb
  obtain ⟨b0, e0, -, -, -, -, hd⟩ := front_of O
  obtain rfl : b0 = b := Option.some.inj (e0.symm.trans hb)
  refine hands_same (fun s s' hy => ?_) hT
  obtain ⟨rs, cols, n, e⟩ := hy
  exact (hd s _ _ s').1 ((VerifiableInference.Desc.Sound.step_ok_iff ft b0 s s' rs cols n).1 e).2.2.2

end IM

#print axioms IM.hands_joined
#print axioms IM.front_hands
