-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/WordsOffPad.lean: the kind "the code switch" (K2): BEHIND THE
MEMBER's STEP THE WORDS THAT THE SCRIPT's WITNESS GIVES AT THE SENDING's MESSAGES ARE THE HELD WORDS
OF THE ROWS THAT THE PART LAYS, AT EVERY INDEX AT WHICH `padB` (Johnson/Desc/SeatAt.lean) SAYS NO:
UNDER THE RECORD's TIE `msgs`; ITS TIE `pads` IS NOT SPENT. Under the record at a switch
(`K2SeatedL`, Honest/K2/SeatedL.lean) and two premises on the verifier's book alone, asked at every
reached state. One statement with its proof; no definition.

  `words_off_pad` `words_behind`'s end (Honest/K2/Law/WordsBehind.lean), to the sign, at one part
                    and index, under one premise more: hb: at that index's row and place, read by
                    the shape that the part's sending gives the message, `padB` says no

WHY. `words_behind` gives the words at every index and spends `msgs` and `pads` together. The rows
that a switch makes have no coefficient at a new pad's place (`padsUnread`,
Johnson/Desc/K2/Honest/Inner/PadsProof.lean): a law on these rows needs the words off the pad alone.

How. `words_behind`'s own proof, to the line, but for this (four hunks of a plain difference): hb is
rewritten along with the message's shape · `tab_off_pad` (Honest/K2/Law/TabOffPad.lean, our second
author's) at the one entry stands where `tab_rows_off` gave the whole table: the fields `pads` and
`noWord` leave the call, and with them a helper fact on the sending's size · the closing step
rewrites by that one entry.

Spends of the record: what `words_behind` spends, less `pads` and `noWord`. Limits. R IS BOUND
WHOLE: whoever calls this law still hands over a record with its field `pads` filled: `pads` HAS
LEFT THE PROOF, NOT THE PREMISES. A record without that field, and the laws beneath over it: not
typed. hFits, hNum: shown of no book. `msgs`: a tie to a Script that is not laid; at a kept copy it
wants a law of its own. hb speaks of `padB`, by row and place: that an index which is no place of
the list `padPlaces` is such an index is not said here. SPEAKS OF ONE ENTRY OF A MESSAGE AT ONE
RUN's COINS. Under `Stepped`: it holds of nothing at a book of coins that lends the part nothing.
Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.SeatsBehind
import Johnson.Desc.ProofFile.Honest.K2.Law.AnsAtCut
import Johnson.Desc.ProofFile.Honest.K2.Law.TabOffPad

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open OnBytes OnBytes.Slice OnBytes.Means Cb Cb.Ood Johnson.Pack VerifiableInference.Desc
open Johnson.Prover.Send (shapeAt)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2 (P2)
open VerifiableInference.Desc.Sound (MsgT Mem)
open ProofFile.Honest.FirstThread (Letters)
open ProofFile.Honest.K1 (seatAtMember)

variable {Bk : ProofFile.Honest.ProverCoinCounts} {Cl W₀ Rc Xi Tr X P Cells Tok : Type}
variable {L : Letters Bk Cl W₀ Rc Xi Tr X P Cells Tok MsgT} {b : Nat} {blk : Block S Cl}
  {D : RowDataOf Xi} {readers : Local W₀ Rc Xi Tr → Readers} {lay : OnBytes.Params.ReqLayout}
  {segs : List SegmentPub} {p : SwitchPlace} {q : P2} {before : S → Except String S}
  {after : S → S → Except String S} {seg first : Nat} {Zp : ProofFile.Pub} {arr : ℕ → ℕ → ℕ}
  {seats₀ : List (ℕ × ℕ)} {ms : List Mem} {rad : ℕ → ℕ}

/-- **WHERE `padB` SAYS NO, THE TIE `msgs` SUFFICES**: behind the member's step, at every
continuation of the challenges heard, the witness's word at one index of one of the sending's
messages is the held word of the rows that the part lays. hFits, hNum: TWO PREMISES on the
verifier's book alone, asked at every reached state (here: at the state behind the step). hb: `padB`
says no at the index's row and place. hA: the thread's invariant in front of the member (`ThrS`).
hS: `Thread.Stepped`: the half has moved, and the member's own step returns s' at what was played.
NOT IN FRONT OF A LAW OVER COINS. -/
theorem words_off_pad
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
    (part : OnBytes.Part) (i : ℕ)
    (hb : VerifiableInference.Desc.padB p.sizes.codes (shapeAt (switchPar p) n) (part == .mask)
      (i % 2 ^ ceilLog2 ((shapeAt (switchPar p) n).rows part))
      (i / 2 ^ ceilLog2 ((shapeAt (switchPar p) n).rows part)) = false) :
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
  rw [hsh] at hxs hb
  have hlen : m.st.heard.length = L.thread.front + roundsTo L.bs b := by
    have e := drawsFit_length _ _ hA.1.2.1
    rw [e, List.length_append]
    rfl
  have htk : (m.st.heard ++ ds ++ ds').take (L.thread.front + roundsTo L.bs b) = m.st.heard := by
    rw [List.append_assoc, ← hlen, List.take_left]
  have hT := tab_off_pad L.Q L.valid _ 0 D readers (lotClosingAt lay segs) p _ n _
    (seatAtMember L.bs b (switchPar p) n).1 (seatAtMember L.bs b (switchPar p) n).2
    (R.msgs n hn) k hc m.st.input hA.1.2.2.2.2.2.2
    (m.st.heard ++ ds ++ ds')
    (by rw [List.length_append, List.length_append, hlen]; omega) (by rw [htk]; exact hV)
    _ _ _ hb
  have hseat := seatBy_behind R Said hA hd hS hFits hNum n hn
  rw [hin, hheard, Johnson.Prover.Send.held_new _ _ _ _ n hn, hsh]
  show wordsOn s'.st (Sound.tabAt s'.st.codes arr (Sound.seatBy Sound.noFirst s'.book) s'.st _)
    (s.st.oracles.size + n) part i = _
  unfold wordsOn Sound.tabAt Statement.rowBits realRows
  rw [hseat, hx, hcodes']
  simp only [hxs]
  rw [hT]
  cases part <;> rfl

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.words_off_pad
