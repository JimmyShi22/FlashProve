-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/WordIsData.lean: THE SHARED "SENDING" (the kind K1): UNDER THE
RECORD OF PREMISES K1Seated (Honest/K1/Seated.lean): BEHIND THE MEMBER's STEP, THE WORD THAT THE
SCRIPT's WITNESS GIVES THROUGH THE VERIFIER's STATEMENT AND BOOK, IN THE MAIN TABLE OF A MESSAGE OF
THE JOB's, INSIDE THE MESSAGE's RANGES AND OFF ITS SAMPLE's PAD, OVER THE EXTENSION FIELD, IS WHAT
THE JOB's DATA SAY THERE. Two theorems; no definition. A JOIN OF THREE LAWS THAT LIE; NO NEW
ARGUMENT.

  - word_is_data_behind: UNDER R (the record: A PREMISE, WHOLE: its fields msgs and pads, THE TIE,
    are spent) · hA (the pair ThrS at the member) · hd · hS (the member's accepted step) · hFits,
    hNum (two public premises on the verifier's book behind the step) · n < J.P.sent.size · hr, hj,
    ha, hp, h3 (main_data_e's five: the row and the place lie inside the message's ranges; the
    message is sampled; (r, j) is none of padInMain's places; the main rows are over the extension
    field): Sound.wordsFirst arr s'.st s'.book (L.Q.wit k y.2.st.input (y.2.st.heard ++ ds'))
    (s.st.oracles.size + n) .main (r + 2 ^ k1 (shapeAt J.P n) * j) IS the job's data at (n, r, j),
    at the input in front and what was heard in front: an element of the extension field itself, an
    element of the base field by the fields' map, 0 where the data are silent.
  - rowBits_is_k1: PUBLIC: the number of row bits of the library's layout of a vector in a message
    of the shape s (vectorLay, OnBytes/Iop/Foldeq.lean) is k1 s (Johnson/Pack/PortZ.lean): both are
    ceilLog2 s.mainRows: by unfolding.

For whom. The hash build's WitnessHasW (Honest/K13/ExchangeM4.lean), the premise of its share at the
item wrow at W's sending, speaks of this left side at n := 0: of the eleven links that its page
counts for it, this law is links 1, 2 and 3 in one, GIVEN THE RECORD THERE; rowBits_is_k1 is the
step between its row and place of an index and ours. GENERAL IN THE MEMBER AND THE SORT: W is not
named here.

The road. step_at_block hands out the part's own cut; words_behind (both ExchangeAtPins.lean);
held_at_main (SendAtBlock.lean); the texts of rowsMsg and rowsLaid (Honest/K1/ScriptAt.lean) and of
the sealed Rows.main; main_data_e (Honest/K1/DataLaw.lean). Kin: held_is_data (CellIsData.lean) and
cell_behind (CellBehind.lean): the like through the cells' accessor; words_at (WordsAtFour.lean):
words_behind's like at a later border.

In word_is_data_behind's proof words_behind is called at w₀ := fun _ _ _ => 0. w₀ : Words GE is that
law's own "for all" letter: the words held in front of the part. It stands in that law's end only as
held's first argument, and held (Johnson/Prover/Send/Core.lean) reads it only at messages that are
not the part's; the end stands at the part's own message number n (n < J.P.sent.size): so no value
of w₀ is read (held_new, Johnson/Prover/Send/Held.lean; held_at_main, SendAtBlock.lean, is general
in it): any other words would serve.

An equation at one run's coins, every k: THE RIGHT SIDE NAMES NO COIN: off the pad a main entry
holds data alone. THE 0 WHERE THE DATA ARE SILENT IS A DEFAULT AT A DATUM, as in rowsR: whoever
spends this law says where the data answer. The data on the right are read at own₀.

ALOUD. "none => 0" IS A DEFAULT AT A DATUM: NEVER AT A PLACE AT WHICH THE MESSAGE's SHAPE SAYS
"COIN": the law speaks in the main table alone, inside the message's ranges, at a sampled message,
and off padInMain's places (hr, hj, ha, hp): that these leave no coin is main_data_e itself. THAT R
CAN BE MET AT W's SENDING IS NOT SAID.
NOT IN FRONT OF A LAW OVER COINS.

Limits. THE TIE (msgs, pads) IS A PREMISE HERE. UNDER "Stepped": it holds of nothing at a book that
does not cover the part's count. THAT THE RECORD CAN BE MET AT W's SENDING IS NOT SAID: member,
half, hasCoins, msgs and pads are handed on there. Who pays hFits and hNum behind a given member is
not said here. What the data are is the caller's. Nothing on soundness, on completeness or on any
other property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.Law.ExchangeAtPins
import Johnson.Desc.ProofFile.Honest.K1.DataLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open OnBytes OnBytes.Slice OnBytes.Means Cb Cb.Ood Johnson.Pack VerifiableInference.Desc
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (MsgT Mem)
open ProofFile.Honest.FirstThread (Letters)
open Johnson.Prover.Send (Rows shapeAt)

variable {Bk : ProverCoinCounts} {Cl W₀ Rc Xi Tr X P Cells Tok : Type}
variable {L : Letters Bk Cl W₀ Rc Xi Tr X P Cells Tok MsgT} {b : Nat} {blk : Block S Cl}
  {wit : Local W₀ Rc Xi Tr → PlaceIn Xi} {J : SendJob (PlaceIn Xi) X} {own₀ : X}
  {sort : K1Sort} {arr : ℕ → ℕ → ℕ} {seats₀ : List (ℕ × ℕ)} {ms : List Mem}
  {rad : ℕ → ℕ}

/-- **THE WITNESS's WORD AT A MAIN ENTRY IS THE JOB's DATUM**: behind the member's step, at every
continuation of the challenges heard. THE TIE (R.msgs, R.pads) IS SPENT. UNDER "Stepped": IT HOLDS
OF NOTHING AT A BOOK THAT DOES NOT COVER THE PART's COUNT. The 0 where the data are silent is a
default at a datum. The data: at the text's own record, where nothing seen and no column is handed
(.bare []); at what a move is handed in a run:
where the job's data reads neither (heardOnly). -/
theorem word_is_data_behind (R : K1Seated L b blk wit J own₀ sort arr seats₀ ms rad)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop) {k : Coins Bk} {s s' : S}
    {m : Mid (Local W₀ Rc Xi Tr) X} {E : Env} {ds : List Fmt.Drawn}
    {y : List Played × Mid (Local W₀ Rc Xi Tr) X} {cols : List OpenedColumn}
    (hA : ThrS L.thread Said b k s m E) (hd : drawsFit blk.rounds ds = true)
    (hS : L.thread.Stepped blk k s m E ds y cols s')
    (hFits : Book.BookFits s'.book)
    (hNum : ∀ (z : ℕ) (T : OnBytes.Tree), s'.book.trees[z]? = some T → T.number = z)
    (n : ℕ) (hn : n < J.P.sent.size) (ds' : List Fmt.Drawn) (r j : ℕ)
    (hr : r < (shapeAt J.P n).mainRows)
    (hj : j < (J.P.codes.base.getD (shapeAt J.P n).code default).ell)
    (ha : (shapeAt J.P n).answers ≠ 0)
    (hp : (r, j) ∉ padInMain (J.P.codes.base.getD (shapeAt J.P n).code default).ell
      (shapeAt J.P n))
    (h3 : ((shapeAt J.P n).mainDeg == 3) = true) :
    Sound.wordsFirst arr s'.st s'.book (L.Q.wit k y.2.st.input (y.2.st.heard ++ ds'))
        (s.st.oracles.size + n) .main (r + 2 ^ k1 (shapeAt J.P n) * j) =
      match J.data (wit m.st.input)
          { heard := m.st.heard, own := own₀, seen := .bare [] } n r j with
      | some (.inr x) => x
      | some (.inl x) => algebraMap GF GE x
      | none => 0 := by
  obtain ⟨c, -, -, -, hc, -⟩ := step_at_block R Said hA hd hS
  rw [words_behind R Said hA hd hS hFits hNum c hc n hn (fun _ _ _ => 0) ds' .main _,
    held_at_main J.P _ _ _ n hn r j hr]
  show Rows.main (rowsLaid J own₀ c (wit m.st.input) m.st.heard n)
    ((shapeAt J.P n).mainDeg == 3) r j = _
  unfold Rows.main rowsLaid
  rw [if_pos h3]
  exact main_data_e J.P J.ride _ c n r j h3 hr hj ha hp

/-- The layout's row bits are k1: both are ceilLog2 of the shape's main rows. -/
theorem rowBits_is_k1 (codes : Codes) (s : OracleShape) (rowsHigh : Bool) :
    (vectorLay codes s rowsHigh).rowBits = k1 s := rfl

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.word_is_data_behind
#print axioms ProofFile.Honest.K1.rowBits_is_k1
