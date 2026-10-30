-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/WordsBehind.lean: the kind "the code switch" (K2): THE WORDS
BEHIND THE MEMBER's STEP, under the record at a switch (`K2SeatedL`, Honest/K2/SeatedL.lean): at
every continuation of the challenges heard, the words that the witness gives through the verifier's
statement and book are, at each message of the switch's own sending, the held words of the rows that
the part lays. One statement with its proof: calls; no definition.

  `words_behind` c: what the frame hands the part (`handed`) · V: the switch's messages in full at
                    c, at the input and at what was heard in front (`switchRowsLaid`; both:
                    Honest/K2/ScriptLots.lean) ⊢ `wordsFirst` (Johnson/Desc/Sound/WordsAt.lean) at
                    the statement and book behind the step, at the Script's witness, at the
                    statement's message number (messages in front) + n, is `held`
                    (Johnson/Prover/Send/Core.lean) of V there: at every part and place of the
                    message, at every w₀ beneath

After the form of the statement of this name at the shared sending's member
(Honest/K1/Law/ExchangeAtPins.lean, of other authors; namespace ProofFile.Honest.K1), line by line but for
four things: the switch's yes holds the sending's decision at a CUT second round, so `msg_at_block`
(Honest/K1/Law/SendAtBlock.lean) is called at a helper block (`fit_trimmed`, `block_at_cut`,
Honest/K2/Law/AnsAtCut.lean) · the Script's message is tied OFF THE PAD's PLACES alone
(`tab_rows_off`, Honest/K2/Law/TabRowsOff.lean) · the sending's public letter holds the sending's
messages by a law, not by unfolding (`sendingPar_sent`, `sendingPar_shape`,
Honest/K2/Law/Counts.lean) · c and V are letters with their equations, not terms. Besides:
`step_at_switch` (Honest/K2/Law/StepAtSwitch.lean) · `seatBy_behind`
(Honest/K2/Law/SeatsBehind.lean) · the library's `held_new` (Johnson/Prover/Send/Held.lean). Spends
of the record, beside what these spend: sends · books · seedsNo · nonZeroNo · answersNo · msgs ·
pads · noWord. A NAMESAKE, in a namespace of its own: `ProofFile.Honest.K1.words_behind` (the model).

Limits. hFits, hNum: TWO PREMISES on the verifier's book alone, asked at every reached state (here:
at the state behind the step): shown of no book here. SPEAKS OF WHOLE MESSAGES, THE PADS' PLACES
INCLUDED: an equation at one run's coins, at every k: it says nothing on how a coin is made. Under
`Stepped`: it holds of nothing at a book of coins that lends the part nothing. The record is a
record of premises: shown at no letters; `msgs` at a kept copy wants a law that is not typed. What
`Wit.tab` returns at a message's number and seat is `tab_rows_off`'s end, AND THAT LAW HAS NEITHER
hA NOR hS AMONG ITS PREMISES: whoever needs that equation by itself calls `tab_rows_off`, not this.
Here hA hands it that the input is valid and how much was heard; hS, through `step_at_switch`, gives
the messages' shapes and the codes in the state behind, their seats, that the input stays and how
what is heard grows. THE RECORD's TWO TIES `msgs`, `pads` ARE BOTH USED, WHICHEVER INDEX i IS ASKED.
Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.SeatsBehind
import Johnson.Desc.ProofFile.Honest.K2.Law.AnsAtCut
import Johnson.Desc.ProofFile.Honest.K2.Law.TabRowsOff

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open OnBytes OnBytes.Slice OnBytes.Means Cb Cb.Ood Johnson.Pack VerifiableInference.Desc
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2 (P2)
open VerifiableInference.Desc.Sound (MsgT Mem)
open ProofFile.Honest.FirstThread (Letters)

variable {Bk : ProofFile.Honest.ProverCoinCounts} {Cl W₀ Rc Xi Tr X P Cells Tok : Type}
variable {L : Letters Bk Cl W₀ Rc Xi Tr X P Cells Tok MsgT} {b : Nat} {blk : Block S Cl}
  {D : RowDataOf Xi} {readers : Local W₀ Rc Xi Tr → Readers} {lay : OnBytes.Params.ReqLayout}
  {segs : List SegmentPub} {p : SwitchPlace} {q : P2} {before : S → Except String S}
  {after : S → S → Except String S} {seg first : Nat} {Zp : ProofFile.Pub} {arr : ℕ → ℕ → ℕ}
  {seats₀ : List (ℕ × ℕ)} {ms : List Mem} {rad : ℕ → ℕ}

/-- **THE WORDS**: behind the member's step, at every continuation of the challenges heard, the
words that the witness gives through the verifier's statement and book are, at each of the sending's
messages, the held words of the rows that the part lays. hFits, hNum: TWO PREMISES on the verifier's
book alone, asked at every reached state (here: at the state behind the step). hA: the thread's
invariant in front of the member (`ThrS`). hS: `Thread.Stepped`: the half has moved, and the
member's own step returns s' at what was played. NOT IN FRONT OF A LAW OVER COINS.
-/
theorem words_behind
    (R : K2SeatedL L b blk D readers lay segs p q before after seg first Zp arr seats₀ ms rad)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop) {k : Coins Bk} {s s' : S}
    {m : Mid (Local W₀ Rc Xi Tr) X} {E : Env} {ds : List Fmt.Drawn}
    {y : List Played × Mid (Local W₀ Rc Xi Tr) X} {cols : List OpenedColumn}
    (hA : ThrS L.thread Said b k s m E) (hd : drawsFit blk.rounds ds = true)
    (hS : L.thread.Stepped blk k s m E ds y cols s')
    (hFits : VerifiableInference.Desc.Book.BookFits s'.book)
    (hNum : ∀ (z : ℕ) (T : OnBytes.Tree), s'.book.trees[z]? = some T → T.number = z)
    (c : SwitchCoins p.sizes p.others p.foldVars p.carries) (hc : handed 0 p k = some c)
    (V : ℕ → Johnson.Prover.Send.Rows)
    (hV : switchRowsLaid D readers (lotClosingAt lay segs) p c m.st.input m.st.heard = .ok V)
    (n : ℕ) (hn : n < (switchPar p).sent.size) (w₀ : Words GE) (ds' : List Fmt.Drawn)
    (part : OnBytes.Part) (i : ℕ) :
    Sound.wordsFirst arr s'.st s'.book (L.Q.wit k y.2.st.input (y.2.st.heard ++ ds'))
        (s.st.oracles.size + n) part i =
      Johnson.Prover.Send.held w₀ s.st.oracles.size (switchPar p) V (s.st.oracles.size + n)
        part i := by
  obtain ⟨-, -, r₁, r₂, gs, -, -, hdec, hfit, -, -, hin, hheard⟩ :=
    step_at_switch R Said hA hd hS
  have hB := R.books _ _ _ _ _ _ _ _ hA.1 hdec
  obtain ⟨-, hl⟩ := fit_trimmed (switchPar p) q R.seedsNo R.nonZeroNo R.answersNo hfit
  obtain ⟨b', hS', hd'⟩ := block_at_cut (switchPar p)
    (fun _ _ _ _ h => R.sends _ _ _ _ _ _ _ _ hA.1 h) hdec hl
  obtain ⟨hcodes, x, hx, hxs, -⟩ := ProofFile.Honest.K1.msg_at_block (switchPar p) hS' hd' hB n hn
  have hcodes' : s'.st.codes = p.sizes.codes := hcodes
  have hsh := ProofFile.Honest.K2.sendingPar_shape p.sizes.codes (switchSent p.sizes p.others) n
  rw [hsh] at hxs
  have hn' : n < (switchSent p.sizes p.others).size := by
    rw [← ProofFile.Honest.K2.sendingPar_sent p.sizes.codes (switchSent p.sizes p.others)]
    exact hn
  have hlen : m.st.heard.length = L.thread.front + roundsTo L.bs b := by
    have e := drawsFit_length _ _ hA.1.2.1
    rw [e, List.length_append]
    rfl
  have htk : (m.st.heard ++ ds ++ ds').take (L.thread.front + roundsTo L.bs b) = m.st.heard := by
    rw [List.append_assoc, ← hlen, List.take_left]
  have hT := tab_rows_off L.Q L.valid _ 0 D readers (lotClosingAt lay segs) p _ n _ _ _
    (R.msgs n hn) (R.pads n hn) R.noWord hn' k hc m.st.input hA.1.2.2.2.2.2.2
    (m.st.heard ++ ds ++ ds')
    (by rw [List.length_append, List.length_append, hlen]; omega) (by rw [htk]; exact hV)
  have hseat := seatBy_behind R Said hA hd hS hFits hNum n hn
  rw [hin, hheard, Johnson.Prover.Send.held_new _ _ _ _ n hn, hsh]
  show wordsOn s'.st (Sound.tabAt s'.st.codes arr (Sound.seatBy Sound.noFirst s'.book) s'.st _)
    (s.st.oracles.size + n) part i = _
  unfold wordsOn Sound.tabAt Statement.rowBits realRows
  rw [hseat, hx, hcodes']
  simp only [hxs, hT]
  cases part <;> rfl

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.words_behind
