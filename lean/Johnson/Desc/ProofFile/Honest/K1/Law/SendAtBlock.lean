-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/SendAtBlock.lean: THE SHARED "SENDING" (the kind K1): BEHIND A
YES OF A BLOCK THAT IS A SENDING: WHAT THE VERIFIER's RECORD HOLDS OF THE NEW MESSAGES, AND WHAT THE
NEW SAMPLE ROWS SAY OF THE HELD WORDS WHERE THE SECOND ROUND's VALUES ARE THE SENDER's OWN ANSWERS.
Seventeen theorems; no definition. (This file names no record of premises and no thread: it is the
lower layer of a piece whose end, ExchangeAtPins.lean, stands over the record K1Seated: that the
record holds at a member of a real chain is not proved there.)

The letters. P: a plan. b: a block over the first chain's state with hS : IsSend P (·.st) b
(Johnson/Desc/K1/Law/GoodSend3.lean). hd: its decision's yes at two rounds, from s to s'. hB :
Booked (Johnson/Desc/K1/Law/BookAtRecord.lean). f := s.st.oracles.size. V : ℕ → Rows: the sender's
rows: A BOUND VARIABLE: no coin, no run and no input is named here. H := held w f P V
(Johnson/Prover/Send/Core.lean).

  - shape_sameMsgs, says_sameMsgs, padded_sameMsgs: two statements with the same messages (SameMsgs,
    Johnson/Desc/K1/Law/SeedIs.lean): the same shapes; a row that names one message says the same of
    the same words; padded words stay padded.
  - send_unpack: the yes, unpacked: a yes of the kind's own decision at a record that has as many
    messages as s; what it leaves has s'.st's messages.
  - names_new, msg_at_block: a new message stands at f + k, with the plan's shape; its sample rows
    name it alone; the statement's codes are the plan's.
  - seedIs_at_block: UNDER condPort P rad (Johnson/Desc/K1/Law/Port6.lean), roundsFit, and hok (the
    first round's drawn elements are spelt by words below the prime): at each sampled message the
    record holds the kind's one sample row at a seed (SeedIs).
  - says_at_block: UNDER hans (the second round's values are "answers" at the held words of V):
    every sample row of a new message says its claim of H, at every w.
  - padded_at_block. ans_at_block, ans_at_entry: UNDER ALL OF THESE: at the seed that the library's
    reader of samples chooses (smpAt, Johnson/Desc/K1/Law/GoodSendForms.lean) the message that H
    holds has the sample's answers; at every radius; ans_at_entry: with the sample, at an entry
    whose shape is the message's.
  - shapeAt_fin: the two readings of a message's shape are one. held_at_main, held_at_mask: H at a
    message's entry, INSIDE THE ROWS OF THAT KIND (hr), is the row's entry (rowsMsg,
    Honest/K1/ScriptAt.lean). answers_canon: each answer is spelt as the field's writer spells it.
    answers_any: THE 0 BENEATH THE HELD WORDS IN hans IS NO COIN: A CONSTANT; NEVER READ AT THE
    PLACE's OWN MESSAGES: the answers are the same at any words beneath.
  - place_at_block: WHERE THE BOOK IN FRONT HAS A PLACE FOR EVERY MESSAGE (hfull : s.book.place.size
    = s.st.oracles.size) the book behind seats a new message at K1.seatOfMsg
    (Johnson/Desc/K1/Law/WordsAtPlace.lean).

By calls: send_says, send_padded, behind_at, wr_shape, wr_sampled, rowsOf_mem_at, held_new,
split_index (Johnson/Prover/Send/) · seedIs_behind, reads_exists, cond_tie, smpAt_of,
decideSend_iff, size_behind, Booked.newer (Johnson/Desc/K1/Law/) · LPFD.factor_ok
(Johnson/Top/Fire/Code/KeyFillFactor.lean) · LinkJoin.namesOne_sampleRow
(Johnson/Desc/First/Link/Law/SampleAtK10.lean) · part_answers, value_named, size_same, onTable_same
(Honest/K1/AnswersChain.lean) · ans_iff_says (SaysMeets.lean).

Kin in the library. seedIs_of_held (Johnson/RunOne/KeySeedIsHeld.lean): seedIs_at_block's end at a
block as the maker holds it, where the holding's own test gives hok; here hok is a premise on the
challenge. held_behind_send (Honest/K1/Law/HeldAtW.lean): the test with code smpHeld at the same
seat, under BookFits and PlanOwn.

SPEAKS OF ANSWERS, WHICH HANG ON THE PADS (THROUGH THE SEED's FACTOR: NOT AT A FACTOR 0, NOR AT A
LIST OF SEEDS SHORTER THAN THE ANSWERS): says_at_block, ans_at_block, ans_at_entry: each an
implication from an equation on the second round's values, at every V.

Limits. It holds under premises: among them
the tie (the fields msgs and pads of the record K1Seated, Honest/K1/Seated.lean) at
real letters and that record at the 52 plans. hans is met by nothing here: that a part's
second move says these answers is ExchangeAtPins.lean's step_at_block. condPort is run at no plan
here. Nothing says that the seed by choice is the seed that was drawn. One answer a message
(Tie.one, out of condPort). Nothing on how V is made. Nothing on soundness, on completeness or on
any other property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.Law.SaysMeets
import Johnson.Top.Fire.Code.KeyFillFactor
import Johnson.Desc.K1.Law.Sound
import Johnson.Desc.K1.Law.SeedIs
import Johnson.Desc.K1.Law.GoodSend3
import Johnson.Desc.K1.Law.BookAtRecord
import Johnson.Desc.K1.Law.WordsAtPlace
import Johnson.Prover.Send.Says
import Johnson.Desc.ProofFile.Honest.K1.ScriptAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open OnBytes OnBytes.Slice OnBytes.Means Cb Cb.Ood Johnson.Pack VerifiableInference.Desc
open _root_.Desc.Plain (DState)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Close (NamesOne)
open VerifiableInference.Desc.K1 (IsSend Booked SameMsgs SeedIs condPort sampledAt shapesOf
  decideSend decideSend_iff size_behind seedIs_behind reads_exists cond_tie smpAt)
open Johnson.Prover.Send (Rows answers send_says send_padded behind_at wr_sampled
  wr_unsampled rowsOf_mem_at)

variable {Cl : Type}

/-! ## 1 Two statements with the same messages -/

/-- Two statements with the same messages have the same shapes. -/
theorem shape_sameMsgs {A B : Statement} (h : SameMsgs A B) (o : ℕ) :
    (B.oracles[o]?).map (·.shape) = (A.oracles[o]?).map (·.shape) := by
  have e := congrArg (Option.map Prod.fst) (h.2 o)
  simpa [Option.map_map, Function.comp_def] using e

/-- A row that names one message says of the same words the same at both. -/
theorem says_sameMsgs {A B : Statement} (h : SameMsgs A B) (r : OnBytes.Row) (o : ℕ)
    (hN : NamesOne r o) (Wd : Words GE) : Says rdE B r Wd ↔ Says rdE A r Wd := by
  unfold Says
  rw [value_named B r o hN Wd, value_named A r o hN Wd,
    onTable_same A B r Wd Wd o .main (size_same A B o h.1 (shape_sameMsgs h o) .main)
      (fun _ => rfl),
    onTable_same A B r Wd Wd o .mask (size_same A B o h.1 (shape_sameMsgs h o) .mask)
      (fun _ => rfl)]

/-- Words that are 0 on the rows beyond the real ones at the one are so at the other. -/
theorem padded_sameMsgs {A B : Statement} (h : SameMsgs A B) (Wd : Words GE)
    (hP : Padded A Wd) : Padded B Wd := by
  intro o part i hi
  refine hP o part i ?_
  have hx := shape_sameMsgs h o
  have hb : B.rowBits o part = A.rowBits o part ∧ realRows B o part = realRows A o part := by
    unfold Statement.rowBits realRows
    cases hA : A.oracles[o]? with
    | none =>
      rw [hA, Option.map_none, Option.map_eq_none_iff] at hx
      rw [hx]
      exact ⟨rfl, rfl⟩
    | some x =>
      rw [hA, Option.map_some] at hx
      obtain ⟨x', h', e⟩ := Option.map_eq_some_iff.1 hx
      rw [h']
      dsimp only
      rw [e]
      exact ⟨rfl, rfl⟩
  rw [← hb.1, ← hb.2]
  exact hi

/-! ## 2 A yes of a sending's block, unpacked -/

/-- **The yes, unpacked.** -/
theorem send_unpack (P : K1.Par) {b : Block S Cl} (hS : IsSend P (fun s : S => s.st) b)
    {s s' : S} {r₁ r₂ : Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (hd : b.decide s [r₁, r₂] gs = .ok s')
    (hB : Booked P s.book s.st.oracles.size s'.book s'.st.oracles.size) :
    ∃ (L : Type) (d d' : DState L) (owed : Option Nat) (ids : Array Nat),
      decideSend P owed d [r₁, r₂] = .ok (ids, d') ∧ d.st.oracles.size = s.st.oracles.size ∧
        SameMsgs d'.st s'.st := by
  obtain ⟨L, d, d', owed, ids, hyes, hsame, hsz⟩ := hS _ _ _ _ _ hd
  refine ⟨L, d, d', owed, ids, hyes, ?_, hsame⟩
  have a := size_behind P owed d d' r₁ r₂ ids hyes
  have a' := hB.msgs
  have c : s'.st.oracles.size = d'.st.oracles.size := hsz
  have hl : (shapesOf P).length = P.sent.size := by simp [shapesOf]
  omega

/-- The sample rows of a new message name that message alone. -/
theorem names_new {L : Type} (P : K1.Par) (d : DState L) (seeds : List (List E × E))
    (ys : List E) (k : ℕ) (hk : k < P.sent.size) (x : OnBytes.Oracle)
    (hx : (K1.behind P d seeds ys).st.oracles[d.st.oracles.size + k]? = some x) :
    ∀ r ∈ x.sampleRows.toList, NamesOne r (d.st.oracles.size + k) := by
  intro r hr
  rw [behind_at P d _ _ k hk] at hx
  obtain rfl := Option.some.inj hx
  by_cases h0 : (Johnson.Prover.Send.shapeAt P k).answers = 0
  · rw [wr_unsampled _ _ _ _ _ h0] at hr
    simp at hr
  · rw [(wr_sampled _ _ _ _ _ h0).2.2.1] at hr
    obtain ⟨i, sd, y, _, _, _, rfl⟩ := rowsOf_mem_at _ _ _ _ _ r hr
    exact LinkJoin.namesOne_sampleRow _ _ _ _ _ _

/-- **A new message behind the yes**: it stands at its number, with the plan's shape; its sample
rows name it alone; the statement's codes are the plan's. -/
theorem msg_at_block (P : K1.Par) {b : Block S Cl} (hS : IsSend P (fun s : S => s.st) b)
    {s s' : S} {r₁ r₂ : Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (hd : b.decide s [r₁, r₂] gs = .ok s')
    (hB : Booked P s.book s.st.oracles.size s'.book s'.st.oracles.size) (k : ℕ)
    (hk : k < P.sent.size) :
    s'.st.codes = P.codes ∧ ∃ x, s'.st.oracles[s.st.oracles.size + k]? = some x ∧
      x.shape = Johnson.Prover.Send.shapeAt P k ∧
      ∀ r ∈ x.sampleRows.toList, NamesOne r (s.st.oracles.size + k) := by
  obtain ⟨L, d, d', owed, ids, hyes, hn, hsame⟩ := send_unpack P hS hd hB
  obtain ⟨hasks, _, rfl⟩ := (decideSend_iff P owed d d' r₁ r₂ ids).1 hyes
  have hx := behind_at P d (K1.seedsOf P r₁) (K1.answersIn r₂) k hk
  have e := hsame.2 (d.st.oracles.size + k)
  rw [hx, Option.map_some] at e
  obtain ⟨x, hx', e'⟩ := Option.map_eq_some_iff.1 e
  rw [← hn]
  refine ⟨hsame.1.trans hasks.2.1, x, hx', (Prod.mk.inj e').1.trans
    (Johnson.Prover.Send.wr_shape _ _ _ _ _), fun r hr => ?_⟩
  have hrows := (Prod.mk.inj (Prod.mk.inj e').2).2
  exact names_new P d _ _ k hk _ hx r (by rw [← hrows]; exact hr)

/-! ## 3 The record holds the kind's own sample row -/

/-- **At each sampled message the record behind holds the kind's one sample row at a seed.** Under
condPort P rad and roundsFit. hok: a premise on the challenge. -/
theorem seedIs_at_block (P : K1.Par) (rad : ℕ → ℕ) (hC : condPort P rad = true) {b : Block S Cl}
    (hS : IsSend P (fun s : S => s.st) b) {s s' : S} {r₁ r₂ : Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (hd : b.decide s [r₁, r₂] gs = .ok s')
    (hB : Booked P s.book s.st.oracles.size s'.book s'.st.oracles.size)
    (hfit : roundsFit (K1.rounds P) [r₁, r₂] = true)
    (hok : (r₁.drawn.elems.all fun x =>
      x.1 < fieldPrimeWord && x.2.1 < fieldPrimeWord && x.2.2 < fieldPrimeWord) = true)
    (k : Fin (shapesOf P).length) (hk : sampledAt P k) :
    ∃ ρ y, SeedIs P.codes (K1.shapeAt P k) s'.st (s.st.oracles.size + k.val) ρ y := by
  obtain ⟨L, d, d', owed, ids, hyes, hn, hsame⟩ := send_unpack P hS hd hB
  obtain ⟨ρ, hρ⟩ := reads_exists P r₁ (LPFD.factor_ok P _ hok)
    ((decideSend_iff P owed d d' _ _ ids).1 hyes).1.2.2.1
  obtain ⟨y, hy⟩ := seedIs_behind P rad owed d d' _ _ ids hC hfit hyes ρ hρ k hk
  rw [← hn]
  exact ⟨_, y, hy.travels hsame⟩

/-! ## 4 Every new sample row says its claim of the held words -/

/-- **EVERY SAMPLE ROW OF A NEW MESSAGE SAYS ITS CLAIM OF THE HELD WORDS**, where the second round's
values are the answers at these words. SPEAKS OF ANSWERS, WHICH HANG ON THE PADS. -/
theorem says_at_block (P : K1.Par) {b : Block S Cl} (hS : IsSend P (fun s : S => s.st) b)
    {s s' : S} {r₁ r₂ : Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (hd : b.decide s [r₁, r₂] gs = .ok s')
    (hB : Booked P s.book s.st.oracles.size s'.book s'.st.oracles.size) (V : ℕ → Rows)
    (hans : r₂.vals = (answers P (stAt P s.st.oracles.size) s.st.oracles.size
      (Johnson.Prover.Send.held (fun _ _ _ => 0) s.st.oracles.size P V)
      (K1.seedsOf P r₁)).map .answer)
    (w : Words GE) (k : ℕ) (hk : k < P.sent.size) (x : OnBytes.Oracle)
    (hx : s'.st.oracles[s.st.oracles.size + k]? = some x) :
    AllSay rdE s'.st x.sampleRows.toList (Johnson.Prover.Send.held w s.st.oracles.size P V) := by
  obtain ⟨L, d, d', owed, ids, hyes, hn, hsame⟩ := send_unpack P hS hd hB
  obtain ⟨hasks, _, rfl⟩ := (decideSend_iff P owed d d' r₁ r₂ ids).1 hyes
  have hans' : r₂.vals = (answers P (stSent d.st P.sent) d.st.oracles.size
      (Johnson.Prover.Send.held w d.st.oracles.size P V) (K1.seedsOf P r₁)).map .answer := by
    rw [← part_answers P d hasks.2.1 w V _, hn]
    exact hans
  have e := hsame.2 (s.st.oracles.size + k)
  rw [hx, Option.map_some] at e
  obtain ⟨x', hx', e'⟩ := Option.map_eq_some_iff.1 e.symm
  have hrows : x'.sampleRows = x.sampleRows := (Prod.mk.inj (Prod.mk.inj e').2).2
  rw [← hn] at hx'
  intro r hr
  have hr' : r ∈ x'.sampleRows.toList := by rw [hrows]; exact hr
  have h1 := send_says P d r₁ r₂ w V hans' k x' hk hx' r hr'
  rw [← hn]
  exact (says_sameMsgs hsame r _ (names_new P d _ _ k hk x' hx' r hr') _).2 h1

/-- The held words over 0 are 0 on the rows beyond the real ones, at the statement behind. -/
theorem padded_at_block (P : K1.Par) {b : Block S Cl} (hS : IsSend P (fun s : S => s.st) b)
    {s s' : S} {r₁ r₂ : Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (hd : b.decide s [r₁, r₂] gs = .ok s')
    (hB : Booked P s.book s.st.oracles.size s'.book s'.st.oracles.size) (V : ℕ → Rows) :
    Padded s'.st (Johnson.Prover.Send.held (fun _ _ _ => 0) s.st.oracles.size P V) := by
  obtain ⟨L, d, d', owed, ids, hyes, hn, hsame⟩ := send_unpack P hS hd hB
  obtain ⟨_, _, rfl⟩ := (decideSend_iff P owed d d' r₁ r₂ ids).1 hyes
  rw [← hn]
  exact padded_sameMsgs hsame _ (send_padded P d _ _ _ V fun _ _ _ _ => rfl)

/-! ## 5 The held words' message has the sample's answers at the reader's seed -/

/-- **AT THE READER's SEED THE HELD WORDS' MESSAGE HAS THE SAMPLE's ANSWERS**, at a sampled message,
under condPort P rad, roundsFit, hok and hans, where the reader returns a sample (hz). SPEAKS OF
ANSWERS, WHICH HANG ON THE PADS. -/
theorem ans_at_block (P : K1.Par) (rad : ℕ → ℕ) (hC : condPort P rad = true) {b : Block S Cl}
    (hS : IsSend P (fun s : S => s.st) b) {s s' : S} {r₁ r₂ : Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (hd : b.decide s [r₁, r₂] gs = .ok s')
    (hB : Booked P s.book s.st.oracles.size s'.book s'.st.oracles.size)
    (hfit : roundsFit (K1.rounds P) [r₁, r₂] = true)
    (hok : (r₁.drawn.elems.all fun x =>
      x.1 < fieldPrimeWord && x.2.1 < fieldPrimeWord && x.2.2 < fieldPrimeWord) = true) (V : ℕ → Rows)
    (hans : r₂.vals = (answers P (stAt P s.st.oracles.size) s.st.oracles.size
      (Johnson.Prover.Send.held (fun _ _ _ => 0) s.st.oracles.size P V)
      (K1.seedsOf P r₁)).map .answer)
    (k : Fin (shapesOf P).length) (hk : sampledAt P k) (e : ℕ)
    (z : (portOmZ P.codes (K1.shapeAt P k) e).Smp)
    (hz : smpAt P.codes (K1.shapeAt P k) e s'.st (s.st.oracles.size + k.val) = some z) :
    (portOmZ P.codes (K1.shapeAt P k) e).Z.val z.1
        (fun j => Johnson.Prover.Send.held (fun _ _ _ => 0) s.st.oracles.size P V
          (s.st.oracles.size + k.val) (partZ P.codes (K1.shapeAt P k) j)
          (locZ P.codes (K1.shapeAt P k) j)) = z.2 := by
  obtain ⟨ρ, y, hcodes, x, zz, β, t, hx, hshape, _, hrows, _, _⟩ :=
    seedIs_at_block P rad hC hS hd hB hfit hok k hk
  have hT := cond_tie P rad hC k hk
  have hl : (shapesOf P).length = P.sent.size := by simp [shapesOf]
  have hkk : k.val < P.sent.size := hl ▸ k.isLt
  have hr : x.sampleRows[0]? = some (K1.sampleRow (K1.Msg.of P.codes (K1.shapeAt P k))
      (s.st.oracles.size + k.val) zz β 0 t) := by
    rw [hrows]
    rfl
  have hsay := says_at_block P hS hd hB V hans (fun _ _ _ => 0) k.val hkk x hx _
    (by rw [hrows]; exact List.mem_singleton.2 rfl)
  have hP := padded_at_block P hS hd hB V
  revert z
  rw [← hcodes, ← hshape] at hT ⊢
  intro z hz
  exact (ans_iff_says s'.st _ x hx _ hr (LinkJoin.namesOne_sampleRow _ _ _ _ _ _)
    (fun h0 => hT.lenMain h0) (fun h0 => hT.lenMask h0) _ hP e z hz).2 hsay

/-- The same at an entry (shape and radius) whose shape is the message's: with the sample. -/
theorem ans_at_entry (P : K1.Par) (rad : ℕ → ℕ) (hC : condPort P rad = true) {b : Block S Cl}
    (hS : IsSend P (fun s : S => s.st) b) {s s' : S} {r₁ r₂ : Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (hd : b.decide s [r₁, r₂] gs = .ok s')
    (hB : Booked P s.book s.st.oracles.size s'.book s'.st.oracles.size)
    (hfit : roundsFit (K1.rounds P) [r₁, r₂] = true)
    (hok : (r₁.drawn.elems.all fun x =>
      x.1 < fieldPrimeWord && x.2.1 < fieldPrimeWord && x.2.2 < fieldPrimeWord) = true) (V : ℕ → Rows)
    (hans : r₂.vals = (answers P (stAt P s.st.oracles.size) s.st.oracles.size
      (Johnson.Prover.Send.held (fun _ _ _ => 0) s.st.oracles.size P V)
      (K1.seedsOf P r₁)).map .answer)
    (k : Fin (shapesOf P).length) (hk : sampledAt P k) (p : OracleShape × ℕ)
    (hp : p.1 = K1.shapeAt P k) :
    ∃ z : (portOmZ P.codes p.1 p.2).Smp,
      smpAt P.codes p.1 p.2 s'.st (s.st.oracles.size + k.val) = some z ∧
        (portOmZ P.codes p.1 p.2).Z.val z.1
          (fun j => Johnson.Prover.Send.held (fun _ _ _ => 0) s.st.oracles.size P V
            (s.st.oracles.size + k.val) (partZ P.codes p.1 j) (locZ P.codes p.1 j)) = z.2 := by
  obtain ⟨sh, e⟩ := p
  obtain rfl : sh = K1.shapeAt P k := hp
  obtain ⟨ρ, y, hs⟩ := seedIs_at_block P rad hC hS hd hB hfit hok k hk
  obtain ⟨z, hz, _, _⟩ := K1.smpAt_of P.codes _ e s'.st _ ρ y (cond_tie P rad hC k hk) hs
  exact ⟨z, hz, ans_at_block P rad hC hS hd hB hfit hok V hans k hk e z hz⟩

/-! ## 6 The held words at a message's entries; the two readings of a message's shape -/

/-- The kind's reading of a message's shape (by a number below the list's length) and the sender's
(by a number) are one. -/
theorem shapeAt_fin (P : K1.Par) (k : Fin (shapesOf P).length) :
    K1.shapeAt P k = Johnson.Prover.Send.shapeAt P k.val := by
  have hk : k.val < P.sent.size := by
    have h := k.isLt
    simpa [shapesOf] using h
  simp [K1.shapeAt, shapesOf, Johnson.Prover.Send.shapeAt, hk]

/-- The held words at a main entry's index, inside the main rows, are the row's entry. -/
theorem held_at_main (P : K1.Par) (w : Words GE) (f : ℕ) (V : ℕ → Rows) (n : ℕ)
    (hn : n < P.sent.size) (r j : ℕ) (hr : r < (Johnson.Prover.Send.shapeAt P n).mainRows) :
    Johnson.Prover.Send.held w f P V (f + n) .main
        (r + 2 ^ k1 (Johnson.Prover.Send.shapeAt P n) * j) =
      rowsMsg (Johnson.Prover.Send.shapeAt P n) (V n) false r j := by
  rw [Johnson.Prover.Send.held_new w f P V n hn, Nat.mul_comm]
  have e : (r + j * 2 ^ k1 (Johnson.Prover.Send.shapeAt P n)) %
        2 ^ K1.clog (Johnson.Prover.Send.shapeAt P n).mainRows = r ∧
      (r + j * 2 ^ k1 (Johnson.Prover.Send.shapeAt P n)) /
        2 ^ K1.clog (Johnson.Prover.Send.shapeAt P n).mainRows = j :=
    Johnson.Prover.Send.split_index r j _ hr
  show (if _ % 2 ^ K1.clog _ < _ then _ else _) = _
  rw [e.1, e.2, if_pos hr]
  rfl

/-- And at a mask entry's, inside the mask rows. -/
theorem held_at_mask (P : K1.Par) (w : Words GE) (f : ℕ) (V : ℕ → Rows) (n : ℕ)
    (hn : n < P.sent.size) (r j : ℕ) (hr : r < (Johnson.Prover.Send.shapeAt P n).maskRows) :
    Johnson.Prover.Send.held w f P V (f + n) .mask
        (r + 2 ^ k2 (Johnson.Prover.Send.shapeAt P n) * j) =
      rowsMsg (Johnson.Prover.Send.shapeAt P n) (V n) true r j := by
  rw [Johnson.Prover.Send.held_new w f P V n hn, Nat.mul_comm]
  have e : (r + j * 2 ^ k2 (Johnson.Prover.Send.shapeAt P n)) %
        2 ^ K1.clog (Johnson.Prover.Send.shapeAt P n).maskRows = r ∧
      (r + j * 2 ^ k2 (Johnson.Prover.Send.shapeAt P n)) /
        2 ^ K1.clog (Johnson.Prover.Send.shapeAt P n).maskRows = j :=
    Johnson.Prover.Send.split_index r j _ hr
  show (if _ % 2 ^ K1.clog _ < _ then _ else _) = _
  rw [e.1, e.2, if_pos hr]
  rfl

/-- Each answer is spelt as the field's writer spells it. -/
theorem answers_canon (P : K1.Par) (S' : Statement) (f : ℕ) (w : Words GE)
    (seeds : List (List E × E)) : ∀ a ∈ answers P S' f w seeds, ofE (toE a) = a := by
  intro a h
  unfold answers at h
  obtain ⟨k, _, h⟩ := List.mem_flatMap.1 h
  obtain ⟨i, _, rfl⟩ := List.mem_map.1 h
  rw [toE_ofE]

/-- **THE 0 BENEATH THE HELD WORDS IS NO COIN: A CONSTANT; NEVER READ AT THE PLACE's OWN MESSAGES**:
the answers at the part's own statement are the same at any words w₀ beneath. -/
theorem answers_any (P : K1.Par) (f : ℕ) (V : ℕ → Rows) (seeds : List (List E × E))
    (w₀ : Words GE) :
    answers P (stAt P f) f (Johnson.Prover.Send.held w₀ f P V) seeds =
      answers P (stAt P f) f (Johnson.Prover.Send.held (fun _ _ _ => 0) f P V) seeds :=
  answers_at_chain P _ _ f _ _ seeds rfl (fun _ _ => rfl) fun k hk part i => by
    rw [Johnson.Prover.Send.held_new _ _ _ _ k hk, Johnson.Prover.Send.held_new _ _ _ _ k hk]

/-! ## 7 The book seats a new message -/

/-- Where the book in front has a place for every message, the book behind seats the new message
number i at the place's seat behind the trees in front. -/
theorem place_at_block (P : K1.Par) {s s' : S}
    (hB : Booked P s.book s.st.oracles.size s'.book s'.st.oracles.size)
    (hfull : s.book.place.size = s.st.oracles.size) {i : ℕ} (hi : i < P.sent.size) :
    s'.book.place[s.st.oracles.size + i]? = some (K1.seatOfMsg P s.book.trees.size i) :=
  hB.newer hfull hi

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.shape_sameMsgs
#print axioms ProofFile.Honest.K1.says_sameMsgs
#print axioms ProofFile.Honest.K1.padded_sameMsgs
#print axioms ProofFile.Honest.K1.send_unpack
#print axioms ProofFile.Honest.K1.names_new
#print axioms ProofFile.Honest.K1.msg_at_block
#print axioms ProofFile.Honest.K1.seedIs_at_block
#print axioms ProofFile.Honest.K1.says_at_block
#print axioms ProofFile.Honest.K1.padded_at_block
#print axioms ProofFile.Honest.K1.ans_at_block
#print axioms ProofFile.Honest.K1.ans_at_entry
#print axioms ProofFile.Honest.K1.shapeAt_fin
#print axioms ProofFile.Honest.K1.held_at_main
#print axioms ProofFile.Honest.K1.held_at_mask
#print axioms ProofFile.Honest.K1.answers_canon
#print axioms ProofFile.Honest.K1.answers_any
#print axioms ProofFile.Honest.K1.place_at_block
