-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/WordsAtFour.lean: THE SHARED "SENDING" (the kind K1): UNDER THE
RECORD OF PREMISES K1Seated (Honest/K1/Seated.lean): THE WORDS THAT THE SCRIPT's WITNESS GIVES
THROUGH A STATEMENT AND A BOOK ARE, AT A MESSAGE OF THE JOB's, THE HELD WORDS OF THE ROWS THAT THE
PART LAYS: AT ANY STATEMENT AND ANY BOOK AT WHICH FOUR PUBLIC FACTS HOLD. One theorem; no
definition.

Why. words_behind (ExchangeAtPins.lean) says this at the state behind the member's own step; its
proof parts in two: the four facts, off the member's own yes; and the tie with the unfolding. The
second half is handed out here, so that it can be called at a later border, where the job's messages
still stand in the statement.

  - words_at: UNDER R · hc : lentCut k 0 ⟨J.P.place, 0⟩ (dueR J.P J.ride) = some c (one run's coins,
    with the cut's equation) · hw : L.valid w · hN : the list of challenges is no shorter than the
    rounds in front of the member · hn : n < J.P.sent.size · AND FOUR PUBLIC FACTS ON st, book, o:
    hcodes : st.codes = J.P.codes · hx : st.oracles[o]? = some x · hxs : x.shape = shapeAt J.P n ·
    hseat : the book seats message o at the job's message's seat: Sound.wordsFirst arr st book
    (L.Q.wit k w hd) o part i = held w₀ first J.P (rowsLaid J own₀ c (wit w) (hd.take
    (L.thread.front + roundsTo L.bs b))) (first + n) part i, at any w₀ and any first.

An equation at one run's coins, every k; the cut never under a bare "there is"; no coin fixed; no
measure. Fields of R spent: msgs, pads. The rows on the right are laid at the job's data AT NOTHING
SEEN and at own₀; that the part's data at what it had seen are the same is heardOnly, which is not
spent here. However long the list of challenges, the right side reads its front alone: the rounds in
front of the member. THE w₀ BENEATH THE HELD WORDS IS NO COIN: never read at the job's own messages
(held_new).

Limits. THE TIE (msgs, pads) IS A PREMISE. Who pays the four facts at a later border is not said
here. Nothing on soundness or on any other property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.Law.ExchangeAtPins

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open OnBytes OnBytes.Slice OnBytes.Means Cb Cb.Ood Johnson.Pack VerifiableInference.Desc
open VerifiableInference.Desc.First (S Numbers rowSays wordsAtFirst)
open VerifiableInference.Desc.Sound (MsgT Mem SitsAt smpNamed smpNamed_at numAt msgsOf)
open ProofFile.Honest.FirstThread (Letters OwnMsgs OwnPads)
open Johnson.Prover.Send (answers shapeAt)

variable {Bk : ProverCoinCounts} {Cl W₀ Rc Xi Tr X P Cells Tok : Type}
variable {L : Letters Bk Cl W₀ Rc Xi Tr X P Cells Tok MsgT} {b : Nat} {blk : Block S Cl}
  {wit : Local W₀ Rc Xi Tr → PlaceIn Xi} {J : SendJob (PlaceIn Xi) X} {own₀ : X}
  {sort : K1Sort} {arr : ℕ → ℕ → ℕ} {seats₀ : List (ℕ × ℕ)} {ms : List Mem}
  {rad : ℕ → ℕ}

/-- **THE WORDS, AT ANY STATEMENT AND BOOK WITH THE FOUR FACTS.** The rows are rowsLaid's: the job's
data AT NOTHING SEEN; that the part's data at what it had seen are the same: heardOnly, not spent
here. NOT UNDER "Stepped": the caller spends hasCoins by name for the cut. -/
theorem words_at (R : K1Seated L b blk wit J own₀ sort arr seats₀ ms rad) (k : Coins Bk)
    (c : Cs (dueR J.P J.ride)) (hc : lentCut k 0 ⟨J.P.place, 0⟩ (dueR J.P J.ride) = some c)
    (w : Local W₀ Rc Xi Tr) (hw : L.valid w) (hd : List Fmt.Drawn)
    (hN : L.thread.front + roundsTo L.bs b ≤ hd.length) (st : Statement) (book : TreeBook)
    (o n : ℕ) (hn : n < J.P.sent.size) (hcodes : st.codes = J.P.codes) (x : _)
    (hx : st.oracles[o]? = some x) (hxs : x.shape = shapeAt J.P n)
    (hseat : Sound.seatBy Sound.noFirst book o = some (seatAtMember L.bs b J.P n))
    (w₀ : Words GE) (first : ℕ) (part : OnBytes.Part) (i : ℕ) :
    Sound.wordsFirst arr st book (L.Q.wit k w hd) o part i =
      Johnson.Prover.Send.held w₀ first J.P
        (rowsLaid J own₀ c (wit w) (hd.take (L.thread.front + roundsTo L.bs b))) (first + n) part
        i := by
  have hT := tab_rows L.Q L.valid _ 0 wit J own₀ _ n _ _ _ (R.msgs n hn) (R.pads n hn) k c hc w hw
    hd hN
  rw [Johnson.Prover.Send.held_new _ _ _ _ n hn]
  show wordsOn st (Sound.tabAt st.codes arr (Sound.seatBy Sound.noFirst book) st _) o part i = _
  unfold wordsOn Sound.tabAt Statement.rowBits realRows
  rw [hseat, hx, hcodes]
  simp only [hxs, hT]
  cases part <;> rfl

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.words_at
