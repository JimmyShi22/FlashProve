-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/SeatsBehind.lean: the kind "the code switch" (K2): WHERE THE
SWITCH's MESSAGES SIT BEHIND THE MEMBER's STEP, under the record at a switch (`K2SeatedL`,
Honest/K2/SeatedL.lean): the verifier's book behind the step has each message of the switch's own
sending at its seat, and the library's reader of the witness's words seats it there. Two statements
with their proofs: calls; no definition.

  `place_behind` behind the step the book's place of the statement's message number (messages in
                    front) + n is `seatAtMember L.bs b (switchPar p) n` (Honest/K1/Seated.lean)
  `seatBy_behind` so `seatBy noFirst` (Johnson/Desc/Sound/TabAt.lean), which seats a message by its
                    tree's own number, gives that seat: UNDER TWO PREMISES on the verifier's book
                    alone, asked at every reached state, ON THE BOOK BEHIND THE STEP: hFits:
                    `BookFits` (Johnson/Desc/Book/BookFits.lean) · hNum: each tree's number is its
                    place in the book

After the form of the two statements of these names at the shared sending's member
(Honest/K1/Law/ExchangeAtPins.lean, of other authors; namespace ProofFile.Honest.K1), line by line. By:
`step_at_switch` (Honest/K2/Law/StepAtSwitch.lean) · `place_at_block`
(Honest/K1/Law/SendAtBlock.lean) · `book_at_border`, `trees_at_border`
(Honest/K1/Law/BookAtBorder.lean): these three are general in the plan and the member. Spends of the
record, beside what the step spends: books · treesNo · placeAt. NAMESAKES, each in a namespace of
its own: `ProofFile.Honest.K1.place_behind`, `ProofFile.Honest.K1.seatBy_behind` (the models) ·
`ProofFile.Honest.place_behind` (Honest/Law/FallPlaces.lean), on other matter.

Limits. hFits and hNum are premises: shown of no book here. Under `Stepped`: it holds of nothing at
a book of coins that lends the part nothing. The record is a record of premises: shown at no
letters. Nothing on what a message holds. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.StepAtSwitch
import Johnson.Desc.ProofFile.Honest.K1.Law.BookAtBorder

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc (Block OpenedColumn)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2 (P2)
open VerifiableInference.Desc.Sound (MsgT Mem)
open ProofFile.Honest.FirstThread (Letters)
open ProofFile.Honest.K1 (seatAtMember place_at_block book_at_border trees_at_border)

variable {Bk : ProverCoinCounts} {Cl W₀ Rc Xi Tr X P Cells Tok : Type}
variable {L : Letters Bk Cl W₀ Rc Xi Tr X P Cells Tok MsgT} {b : Nat} {blk : Block S Cl}
  {D : RowDataOf Xi} {readers : Local W₀ Rc Xi Tr → Readers} {lay : OnBytes.Params.ReqLayout}
  {segs : List SegmentPub} {p : SwitchPlace} {q : P2} {before : S → Except String S}
  {after : S → S → Except String S} {seg first : Nat} {Zp : ProofFile.Pub} {arr : ℕ → ℕ → ℕ}
  {seats₀ : List (ℕ × ℕ)} {ms : List Mem} {rad : ℕ → ℕ}

/-- Behind the member's step the verifier's book has the sending's message number n at its seat. hA:
the thread's invariant in front of the member (`ThrS`). hS: `Thread.Stepped`: the half has moved,
and the member's own step returns s' at what was played.
NOT IN FRONT OF A LAW OVER COINS. -/
theorem place_behind
    (R : K2SeatedL L b blk D readers lay segs p q before after seg first Zp arr seats₀ ms rad)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop) {k : Coins Bk} {s s' : S}
    {m : Mid (Local W₀ Rc Xi Tr) X} {E : Env} {ds : List Fmt.Drawn}
    {y : List Played × Mid (Local W₀ Rc Xi Tr) X} {cols : List OpenedColumn}
    (hA : ThrS L.thread Said b k s m E) (hd : drawsFit blk.rounds ds = true)
    (hS : L.thread.Stepped blk k s m E ds y cols s')
    (n : ℕ) (hn : n < (switchPar p).sent.size) :
    s'.book.place[s.st.oracles.size + n]? = some (seatAtMember L.bs b (switchPar p) n) := by
  obtain ⟨-, -, r₁, r₂, gs, -, -, hdec, -, -, -, -, -⟩ := step_at_switch R Said hA hd hS
  have hpl := place_at_block (switchPar p) (R.books _ _ _ _ _ _ _ _ hA.1 hdec)
    (book_at_border L Said hA).2.1 hn
  have htr : s.book.trees.size = treesTo L.bs b := by
    rw [R.treesNo]
    exact trees_at_border L Said hA R.placeAt rfl
  rw [htr] at hpl
  exact hpl

/-- And the library's reader of the witness's words, which seats a message by its tree's own number,
seats it there: under the two premises on the book. hA, hS: as above.
NOT IN FRONT OF A LAW OVER COINS. -/
theorem seatBy_behind
    (R : K2SeatedL L b blk D readers lay segs p q before after seg first Zp arr seats₀ ms rad)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop) {k : Coins Bk} {s s' : S}
    {m : Mid (Local W₀ Rc Xi Tr) X} {E : Env} {ds : List Fmt.Drawn}
    {y : List Played × Mid (Local W₀ Rc Xi Tr) X} {cols : List OpenedColumn}
    (hA : ThrS L.thread Said b k s m E) (hd : drawsFit blk.rounds ds = true)
    (hS : L.thread.Stepped blk k s m E ds y cols s')
    (hFits : VerifiableInference.Desc.Book.BookFits s'.book)
    (hNum : ∀ (z : ℕ) (T : OnBytes.Tree), s'.book.trees[z]? = some T → T.number = z)
    (n : ℕ) (hn : n < (switchPar p).sent.size) :
    VerifiableInference.Desc.Sound.seatBy VerifiableInference.Desc.Sound.noFirst s'.book
        (s.st.oracles.size + n) = some (seatAtMember L.bs b (switchPar p) n) := by
  have hpl := place_behind R Said hA hd hS n hn
  obtain ⟨T, hTr, -⟩ := hFits _ _ hpl
  unfold VerifiableInference.Desc.Sound.seatBy
  rw [hpl, Option.bind_some, hTr, Option.map_some]
  show some (T.number, _) = _
  rw [hNum _ _ hTr]

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.place_behind
#print axioms ProofFile.Honest.K2.Law.seatBy_behind
