-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/ExchangeAtPins.lean: THE SHARED "SENDING" (the kind K1) AT THE
FIRST CHAIN's THREAD: THE KIND's SHARE (ExchangeAtS, Honest/Thread/SharesS.lean) OF ExchangeS
(Honest/Thread/PaysS.lean) AT THE ITEMS pin m t, pinI, pinV AND row m (sample t), UNDER THE RECORD
OF PREMISES K1Seated (Honest/K1/Seated.lean). Sixteen theorems; no definition. That the record holds
at a member of a real chain is not proved here.

The letters. R : K1Seated L b blk wit J own₀ sort arr seats₀ ms rad. Said: any sentence on a run: a
bound letter. The run: hA : ThrS L.thread Said b k s m E (the thread and what is said, in front of
the member) · hd : drawsFit blk.rounds ds · hS : L.thread.Stepped blk k s m E ds y cols s' (the
member's step: the prover's play and the yes of the verifier's own step). v := L.Q.wit k
y.2.st.input (y.2.st.heard ++ ds'), AT EVERY CONTINUATION ds' of the challenges heard. c: THE PART's
OWN CUT OF THE RUN's COINS: ONE NAME: lentCut k 0 ⟨J.P.place, 0⟩ (dueR J.P J.ride) = some c: what
the frame lends the part is that value (cut_of_lendPlace, Honest/K1/ScriptLendRow.lean).

  - draws_words, played_vals, rounds_played: tools: the challenge's elements are spelt by words
    below the prime (a clause of the frame's drawFit) · the second round's values as played are
    "answers" at the rows that the part lays at what was heard in front (rowsLaid,
    Honest/K1/ScriptAt.lean), through R's heardOnly · the two rounds as the verifier's step is
    handed them.
  - step_at_block: THE MEMBER's STEP, UNPACKED: there are c, two rounds and groups with: lentCut's
    value is c · blk's decision says yes from s to s' · roundsFit · the first round's words below
    the prime · the second round's values are the answers at the held words of the rows laid AT c ·
    the input stays; what is heard grows by ds. THE 0 BENEATH THESE HELD WORDS IS NO COIN: A
    CONSTANT; never read at the job's own messages: step_at_block_any: the same at any words
    beneath. Spends member's neighbours shape · half · fits · heardOnly · placeAt · firstNo.
  - pin_entry, pins_behind: THE PINS: at every seat x that the table pins at the member's sort, at
    every p and all strings: L.ans x.1 x.2 (p, s') yy v. Spends also seats (from left to right
    alone) · sits · numbered · ans · port · isSend · books · msgs · pads. NO PREMISE ON THE
    VERIFIER's BOOK. hasCoins AND oneAns ARE SPENT BY NO PROOF HERE: c is what the frame lends at
    the step (k1_moved_term): at a book that does not cover the part's count lentCut answers nothing
    (lentCut_isSome, Honest/K1/ScriptAtLaw.lean), so no step is met, and these sentences hold of
    nothing there. UNDER R THE BOOK DOES COVER: K1Seated.covers, K1Seated.cut
    (Honest/K1/SeatedLaw.lean): at every run's coins the cut is there: so it is not for want of a
    cut that these could be empty; one answer at each sampled message comes out of port (Tie.one,
    Johnson/Desc/K1/Law/Port2.lean).
  - classOf_sub: what a member's class of sample rows is sent at lies among its sort's pins.
  - place_behind: the book behind the step has each of the job's messages at its seat (no premise on
    the book). seatBy_behind: so does the library's reader of the witness's words, under the two
    premises below. words_behind: THE WORDS: at each of the job's messages the words that v gives
    through s'.st and s'.book are the held words of the rows laid at c: at both tables, at every
    index. rows_behind: THE SAMPLE ROWS: every sample row of the member's own class says its claim
    of v's words. BOTH UNDER TWO PUBLIC PREMISES ON THE VERIFIER's BOOK BEHIND THE STEP: hFits :
    BookFits s'.book (Johnson/Desc/Book/BookFits.lean) · hNum : a tree's number is its place in the
    book. place_behind spends step_at_block's six, books and treesNo; words_behind these and isSend
    · msgs · pads; rows_behind these and seats: TWELVE; NOT port · ans · numbered · sits.
  - exchange_pin (under classOf sort = some (m, t)), exchange_pinI (at the opening), exchange_pinV
    (at W's member): ExchangeAtS L.thread Said b at these items: no premise beyond R; they spend
    member too. exchange_rows: at row m (sample t), under classOf sort = some (m, t) and the two
    premises on the book at every step under the pair; it spends member and rowM too. At W's member
    classOf answers nothing: of a class of sample rows nothing is said there.

The two premises on the book. The library's reader of the witness's words seats a message by ITS
TREE's OWN NUMBER (seatBy noFirst, Johnson/Desc/Sound/TabAt.lean); the table, the tie and the book's
places count a tree by its PLACE: hNum makes the two one (the premise h₂ of seatFirst_atPlan,
Johnson/Desc/Sound/WordsAtPlan.lean). hFits gives that the message's tree stands in the book, and
that no two messages have one place (places_inj): the library's PlacesApart
(Johnson/Desc/First/Close/Law/FillRow.lean). Both speak of the verifier's record alone. AT A
VARIABLE L NO FILE MEETS THEM. At the letters lettersHead (Honest/Thread/FirstHead.lean) the file
Honest/Thread/BookFacts.lean has "places apart" and "number = place" behind a member's step, from
the thread, the step and "no mark behind": BookFits itself, which hFits asks, is no statement of
that file.

The fences. msgs and pads speak at the thread's valid inputs, at lists of challenges no shorter than
the rounds in front of the member: the pair pays both: its clause on the input, and its clause that
what was heard fits the rounds in front (drawsFit_length, Honest/Law/Along.lean).

By calls: k1_moved_term (Honest/K1/Plays.lean) · cut_of_lendPlace · tab_rows
(Honest/K1/ScriptTie.lean) · rowsLaid_part (Honest/K1/ScriptAtLaw.lean) · book_at_border,
first_at_border, trees_at_border (BookAtBorder.lean) · SendAtBlock.lean · K1.step_ok
(Johnson/Desc/K1/Law/AtRecord.lean) · smpNamed_at (Johnson/Desc/Sound/SmpNamed.lean) · places_inj.

SPEAKS OF ANSWERS, WHICH HANG ON THE PADS (THROUGH THE SEED's FACTOR: NOT AT A FACTOR 0, NOR AT A
LIST OF SEEDS SHORTER THAN THE ANSWERS): step_at_block, pins_behind, rows_behind and the four
shares. EACH IS AN EQUATION OR AN IMPLICATION AT ONE RUN's COINS, AT EVERY k: none says how a coin
is made. At W's member the data are another file's letter; nothing here says what W's entries are.
Of the index masks' message nothing here says what its entries are, nor which kind spends which.
FOUR DEFAULTS IN THE LIBRARY's DEFINITIONS ARE READ THROUGH, each barred by what stands in brackets
behind it (argued by the texts: no statement here says so): tabAt's zero table (the book's place;
hFits) · seeds.getD in "answers" (the challenge fits the rounds) · ce, cf beyond the count
(Honest/K1/CoinsIn.lean) · layOf's getD (the member's yes).

Limits. It holds under premises: among them
the tie (msgs, pads) at real letters and the record at the 52 plans. K1Seated
is a record of premises: met at the first Script (`k1Seated_first`), under the head and a returned
prover: a closed term: that a run has this Script is not said here.
THE TIE (msgs, pads) IS A PREMISE. That each message has at most one answer at the 52 plans
(oneAns) is not said here; of the sampled messages at the 52 places of the kind K1 in the first
chain the library has one answer each (PlanOwn.one: planOwn_first, planOwn_later, planOwn_w,
Johnson/Desc/K1/Law/PlanOwn.lean, under LikeFull q and gp = gpFull). These shares are not "the
exchange": the items owed again, the forms at "reads", "tie m" and W's row are other files'. It is
no completeness. Nothing on soundness or on any other property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.Law.SendAtBlock
import Johnson.Desc.ProofFile.Honest.K1.Law.BookAtBorder
import Johnson.Desc.ProofFile.Honest.K1.SeatedLaw
import Johnson.Desc.ProofFile.Honest.K1.ScriptTie
import Johnson.Desc.ProofFile.Honest.K1.ScriptLendRow
import Johnson.Desc.ProofFile.Honest.K1.Plays
import Johnson.Desc.ProofFile.Honest.Thread.SharesS
import Johnson.Desc.ProofFile.Honest.Law.Along
import Johnson.Desc.K1.Law.AtRecord
import Johnson.Desc.Sound.SmpNamed
import Johnson.Desc.Sound.WordsAt
import Johnson.Desc.Book.BookFits

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open OnBytes OnBytes.Slice OnBytes.Means Cb Cb.Ood Johnson.Pack VerifiableInference.Desc
open VerifiableInference.Desc.First (S Numbers rowSays wordsAtFirst)
open VerifiableInference.Desc.Sound (MsgT Mem SitsAt smpNamed smpNamed_at numAt msgsOf)
open VerifiableInference.Desc.K1 (condPort sampledAt shapesOf smpAt)
open ProofFile.Honest.FirstThread (Letters OwnMsgs OwnPads)
open Johnson.Prover.Send (answers shapeAt)

variable {Bk : ProverCoinCounts} {Cl W₀ Rc Xi Tr X P Cells Tok : Type}
variable {L : Letters Bk Cl W₀ Rc Xi Tr X P Cells Tok MsgT} {b : Nat} {blk : Block S Cl}
  {wit : Local W₀ Rc Xi Tr → PlaceIn Xi} {J : SendJob (PlaceIn Xi) X} {own₀ : X}
  {sort : K1Sort} {arr : ℕ → ℕ → ℕ} {seats₀ : List (ℕ × ℕ)} {ms : List Mem}
  {rad : ℕ → ℕ}

/-! ## 1 From the member's step to the sending's block -/

/-- The first challenge's elements are spelt by words below the prime: a clause of the frame's
drawFit. -/
theorem draws_words {a : Fmt.DeclaredRound} {as : List Fmt.DeclaredRound} {d : Fmt.Drawn}
    {ds : List Fmt.Drawn} (h : drawsFit (a :: as) (d :: ds) = true) :
    (d.elems.all fun x => x.1 < fieldPrimeWord && x.2.1 < fieldPrimeWord && x.2.2 < fieldPrimeWord) = true := by
  unfold drawsFit drawFit at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.2

/-- The second round's values as played are the answers at the rows that the part lays at what was
heard in front, spelt as a view spells them: under hh (of what stands in front the job's data read
what was heard alone). -/
theorem played_vals {W : Type} (wit : W → PlaceIn Xi) (J : SendJob (PlaceIn Xi) X) (own₀ : X)
    (hh : ∀ w fr fr', fr.heard = fr'.heard → J.data w fr = J.data w fr')
    (c : Cs (dueR J.P J.ride)) (t : State W X) (sn : Seen) (d₀ : Fmt.Drawn) :
    ((answers J.P (stAt J.P J.first) J.first
        (Johnson.Prover.Send.held (fun _ _ _ => 0) J.first J.P
          (J.rows c sn ((t.hears d₀).narrow wit id) 1))
        (seedsAt J.P [d₀])).map fun a => ProofFile.Honest.Said.got (.answer (toE a))) =
      (answers J.P (stAt J.P J.first) J.first
        (Johnson.Prover.Send.held (fun _ _ _ => 0) J.first J.P
          (rowsLaid J own₀ c (wit t.input) t.heard)) (seedsAt J.P [d₀])).map .answer := by
  have e1 : J.rows c sn ((t.hears d₀).narrow wit id) 1 =
      rowsLaid J own₀ c (wit t.input) t.heard := by
    rw [← rowsLaid_part J own₀ hh c sn ((t.hears d₀).narrow wit id) 1]
    show rowsLaid J own₀ c (wit t.input)
      ((t.heard ++ [d₀]).take ((t.heard ++ [d₀]).length - 1)) = _
    rw [List.length_append, List.length_singleton, Nat.add_sub_cancel, List.take_left]
  rw [e1]
  refine List.map_congr_left fun a ha => ?_
  show Fmt.ItemValue.answer (ofE (toE a)) = _
  rw [answers_canon _ _ _ _ _ a ha]

/-- The member's two rounds as the verifier's step is handed them: without the sealed digest. -/
theorem rounds_played {W : Type} (name : String) (wit : W → PlaceIn Xi)
    (J : SendJob (PlaceIn Xi) X) (c : Cs (dueR J.P J.ride)) (t : State W X) (seen : Seen)
    (d₀ d₁ : Fmt.Drawn) :
    (roundsOf (playedK1 name wit J c t seen d₀ d₁)).map noDigest =
      [noDigest ⟨[], d₀⟩,
        noDigest ⟨(answers J.P (stAt J.P J.first) J.first
          (Johnson.Prover.Send.held (fun _ _ _ => 0) J.first J.P
            (J.rows c (seen.plus [⟨[], d₀⟩]) ((t.hears d₀).narrow wit id) 1))
          (seedsAt J.P [d₀])).map fun a => ProofFile.Honest.Said.got (.answer (toE a)), d₁⟩] := rfl

/-- **THE MEMBER's STEP, UNPACKED.** c: the part's own cut of the run's coins: what the frame lends
the part IS lentCut's value (cut_of_lendPlace). The rows: those that the part lays at what was heard
in front. THE 0 BENEATH THE HELD WORDS: NO COIN: A CONSTANT; never read at the job's own messages
(step_at_block_any). -/
theorem step_at_block (R : K1Seated L b blk wit J own₀ sort arr seats₀ ms rad)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop) {k : Coins Bk} {s s' : S}
    {m : Mid (Local W₀ Rc Xi Tr) X} {E : Env} {ds : List Fmt.Drawn}
    {y : List Played × Mid (Local W₀ Rc Xi Tr) X} {cols : List OpenedColumn}
    (hA : ThrS L.thread Said b k s m E) (hd : drawsFit blk.rounds ds = true)
    (hS : L.thread.Stepped blk k s m E ds y cols s') :
    ∃ (c : Cs (dueR J.P J.ride)) (r₁ r₂ : Fmt.RoundView) (gs : List (List (Nat × List UInt64))),
      lentCut k 0 ⟨J.P.place, 0⟩ (dueR J.P J.ride) = some c ∧
      blk.decide s [r₁, r₂] gs = .ok s' ∧
      roundsFit (K1.rounds J.P) [r₁, r₂] = true ∧
      (r₁.drawn.elems.all fun x => x.1 < fieldPrimeWord && x.2.1 < fieldPrimeWord && x.2.2 < fieldPrimeWord) = true ∧
      r₂.vals = (answers J.P (stAt J.P s.st.oracles.size) s.st.oracles.size
        (Johnson.Prover.Send.held (fun _ _ _ => 0) s.st.oracles.size J.P
          (rowsLaid J own₀ c (wit m.st.input) m.st.heard)) (K1.seedsOf J.P r₁)).map .answer ∧
      y.2.st.input = m.st.input ∧ y.2.st.heard = m.st.heard ++ ds := by
  obtain ⟨c', d₀, d₁, hlend, hds, -, hy1, hin, hheard⟩ :=
    k1_moved_term L.thread blk wit J R.shape R.half R.fits k m E ds y cols hd hS.1
  have hc : lentCut k 0 ⟨J.P.place, 0⟩ (dueR J.P J.ride) = some c'.1.1 :=
    cut_of_lendPlace _ k 0 wit J c' hlend
  obtain ⟨hfit, gs, hdec⟩ := K1.step_ok _ blk s s' _ _ _ hS.2
  have hf : s.st.oracles.size = J.first := first_at_border L Said hA R.placeAt R.firstNo
  rw [hy1, rounds_played] at hdec
  rw [hy1, R.shape.2.1] at hfit
  rw [hds, R.shape.2.1] at hd
  have hw : (d₀.elems.all fun x => x.1 < fieldPrimeWord && x.2.1 < fieldPrimeWord && x.2.2 < fieldPrimeWord) = true :=
    draws_words (by unfold K1.rounds at hd; exact hd)
  refine ⟨c'.1.1, _, _, gs, hc, hdec, hfit, hw, ?_, hin, hheard⟩
  rw [hf]
  exact played_vals wit J own₀ R.heardOnly c'.1.1 m.st _ d₀

/-- **THE SAME AT ANY WORDS BENEATH**: the 0 in step_at_block's fifth clause is NO COIN: A CONSTANT;
never read at the job's own messages (answers_any). -/
theorem step_at_block_any (R : K1Seated L b blk wit J own₀ sort arr seats₀ ms rad)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop) {k : Coins Bk} {s s' : S}
    {m : Mid (Local W₀ Rc Xi Tr) X} {E : Env} {ds : List Fmt.Drawn}
    {y : List Played × Mid (Local W₀ Rc Xi Tr) X} {cols : List OpenedColumn}
    (hA : ThrS L.thread Said b k s m E) (hd : drawsFit blk.rounds ds = true)
    (hS : L.thread.Stepped blk k s m E ds y cols s') :
    ∃ (c : Cs (dueR J.P J.ride)) (r₁ r₂ : Fmt.RoundView) (gs : List (List (Nat × List UInt64))),
      lentCut k 0 ⟨J.P.place, 0⟩ (dueR J.P J.ride) = some c ∧
      blk.decide s [r₁, r₂] gs = .ok s' ∧
      ∀ w₀ : Words GE, r₂.vals = (answers J.P (stAt J.P s.st.oracles.size) s.st.oracles.size
        (Johnson.Prover.Send.held w₀ s.st.oracles.size J.P
          (rowsLaid J own₀ c (wit m.st.input) m.st.heard)) (K1.seedsOf J.P r₁)).map .answer := by
  obtain ⟨c, r₁, r₂, gs, hc, hdec, -, -, hans, -, -⟩ := step_at_block R Said hA hd hS
  exact ⟨c, r₁, r₂, gs, hc, hdec, fun w₀ => by rw [answers_any]; exact hans⟩

/-! ## 2 The pins -/

/-- **ONE PINNED SEAT**, at an entry (shape and radius) whose shape is the message's: under a yes of
the member's decision (hdec), roundsFit, hok and hans, at a sampled message n of the job, the reader
of samples returns a sample, and T has its answers at its seed. V: any rows at which hans holds. T:
any message that is V n read as a message (rowsMsg). -/
theorem pin_entry (R : K1Seated L b blk wit J own₀ sort arr seats₀ ms rad) {s s' : S}
    {r₁ r₂ : Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (hdec : blk.decide s [r₁, r₂] gs = .ok s')
    (hfit : roundsFit (K1.rounds J.P) [r₁, r₂] = true)
    (hok : (r₁.drawn.elems.all fun x =>
      x.1 < fieldPrimeWord && x.2.1 < fieldPrimeWord && x.2.2 < fieldPrimeWord) = true) (V : ℕ → Johnson.Prover.Send.Rows)
    (hans : r₂.vals = (answers J.P (stAt J.P s.st.oracles.size) s.st.oracles.size
      (Johnson.Prover.Send.held (fun _ _ _ => 0) s.st.oracles.size J.P V)
      (K1.seedsOf J.P r₁)).map .answer)
    (n : ℕ) (hn : n < J.P.sent.size) (ha : (shapeAt J.P n).answers ≠ 0)
    (T : MsgT) (hT : T = rowsMsg (shapeAt J.P n) (V n)) (p : OracleShape × ℕ)
    (hp : p.1 = shapeAt J.P n) :
    ∃ z : (portOmZ J.P.codes p.1 p.2).Smp,
      smpAt J.P.codes p.1 p.2 s'.st (s.st.oracles.size + n) = some z ∧
        (portOmZ J.P.codes p.1 p.2).Z.val z.1
          (fun j => match (j : (Fin p.1.mainRows × Fin (pMain J.P.codes p.1).ell) ⊕
              (Fin p.1.maskRows × Fin (pMask J.P.codes p.1).ell)) with
            | .inl q => T false q.1.val q.2.val
            | .inr q => T true q.1.val q.2.val) = z.2 := by
  have hl : (shapesOf J.P).length = J.P.sent.size := by simp [shapesOf]
  have hsh := shapeAt_fin J.P ⟨n, hl ▸ hn⟩
  have hk : sampledAt J.P ⟨n, hl ▸ hn⟩ := by
    show (K1.shapeAt J.P ⟨n, hl ▸ hn⟩).answers ≠ 0
    rw [hsh]
    exact ha
  obtain ⟨z, hz, hv⟩ := ans_at_entry J.P rad R.port R.isSend hdec (R.books _ _ _ _ _ hdec) hfit hok
    V hans ⟨n, hl ▸ hn⟩ hk p (hp.trans hsh.symm)
  refine ⟨z, hz, ?_⟩
  rw [← hv]
  congr 1
  funext j
  obtain ⟨sh, e⟩ := p
  obtain rfl : sh = shapeAt J.P n := hp
  subst hT
  rcases j with q | q
  · exact (held_at_main J.P _ _ V n hn q.1.val q.2.val q.1.isLt).symm
  · exact (held_at_mask J.P _ _ V n hn q.1.val q.2.val q.1.isLt).symm

/-- **THE PINS**: behind the member's step, at every continuation of the challenges heard, each seat
that the table pins at the member's sort answers. SPEAKS OF ANSWERS, WHICH HANG ON THE PADS (THROUGH
THE SEED's FACTOR: NOT AT A FACTOR 0, NOR AT A LIST OF SEEDS SHORTER THAN THE ANSWERS). UNDER
"Stepped": THE CUT IS THE FRAME's: IT HOLDS OF NOTHING AT A BOOK THAT DOES NOT COVER THE PART's
COUNT. -/
theorem pins_behind (R : K1Seated L b blk wit J own₀ sort arr seats₀ ms rad)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop) {k : Coins Bk} {s s' : S}
    {m : Mid (Local W₀ Rc Xi Tr) X} {E : Env} {ds : List Fmt.Drawn}
    {y : List Played × Mid (Local W₀ Rc Xi Tr) X} {cols : List OpenedColumn}
    (hA : ThrS L.thread Said b k s m E) (hd : drawsFit blk.rounds ds = true)
    (hS : L.thread.Stepped blk k s m E ds y cols s') (x : ℕ × ℕ)
    (hx : x ∈ pinsAtSort L.N sort) (p : P) (yy : Strs) (ds' : List Fmt.Drawn) :
    L.ans x.1 x.2 (p, s') yy (L.Q.wit k y.2.st.input (y.2.st.heard ++ ds')) := by
  obtain ⟨n, hn, ha, rfl⟩ := (R.seats x).1 hx
  obtain ⟨c, r₁, r₂, gs, hc, hdec, hfit, hok, hans, hin, hheard⟩ := step_at_block R Said hA hd hS
  have hf : s.st.oracles.size = J.first := first_at_border L Said hA R.placeAt R.firstNo
  have hlen : m.st.heard.length = L.thread.front + roundsTo L.bs b := by
    have e := drawsFit_length _ _ hA.1.2.1
    rw [e, List.length_append]
    rfl
  have hT := tab_rows L.Q L.valid _ 0 wit J own₀ _ n _ _ _ (R.msgs n hn) (R.pads n hn) k c hc
    m.st.input hA.1.2.2.2.2.2.2 (m.st.heard ++ ds ++ ds')
    (by rw [List.length_append, List.length_append, hlen]; omega)
  have htk : (m.st.heard ++ ds ++ ds').take (L.thread.front + roundsTo L.bs b) = m.st.heard := by
    rw [List.append_assoc, ← hlen, List.take_left]
  rw [htk] at hT
  rw [R.ans]
  refine ⟨(R.sits n hn ha).1, fun μ hμ hs => ?_⟩
  have hsh : (μ.1.l.get μ.2).1 = shapeAt J.P n := (R.sits n hn ha).2 μ hμ hs
  obtain ⟨z, hz, hv⟩ := pin_entry R hdec hfit hok _ hans n hn ha _ hT (μ.1.l.get μ.2) hsh
  have hseat : μ.1.seat μ.2 = seatAtMember L.bs b J.P n := hs
  have hq : μ.1.seat μ.2 ∈ seats₀ := by rw [hseat]; exact (R.numbered n hn ha).1
  have hnum : numAt seats₀ μ = s.st.oracles.size + n := by
    show seats₀.idxOf (μ.1.seat μ.2) = _
    rw [hseat, (R.numbered n hn ha).2, hf]
  refine ⟨z, ?_, ?_⟩
  · show smpNamed J.P.codes seats₀ _ μ.1 μ.2 = some z
    rw [smpNamed_at J.P.codes seats₀ _ μ.1 μ.2 hq]
    show smpAt J.P.codes _ _ s'.st (numAt seats₀ μ) = some z
    rw [hnum]
    exact hz
  · rw [← hv, hin, hheard]
    congr 1
    funext j
    show msgsOf J.P.codes μ.1.l μ.1.seat arr _ μ.2 j = _
    unfold msgsOf
    rw [hseat]
    rcases j with q | q
    · exact congrArg (fun sh => (L.Q.wit k m.st.input (m.st.heard ++ ds ++ ds')).tab J.P.codes sh
        _ _ _ false q.1.val q.2.val) hsh
    · exact congrArg (fun sh => (L.Q.wit k m.st.input (m.st.heard ++ ds ++ ds')).tab J.P.codes sh
        _ _ _ true q.1.val q.2.val) hsh

/-! ## 3 The witness's words at the job's messages -/

/-- What a member's class of sample rows is sent at lies among the seats that its sort pins. -/
theorem classOf_sub (N : Numbers) (sort : K1Sort) (m t : ℕ) (h : classOf sort = some (m, t)) :
    ∀ x ∈ N.sent m t, x ∈ pinsAtSort N sort := by
  intro x hx
  cases sort with
  | opening =>
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    exact List.mem_append_left _ hx
  | reads m' =>
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    exact hx
  | digits m' =>
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    exact hx
  | w => cases h

/-- Behind the member's step the verifier's book has the job's message number n at its seat. -/
theorem place_behind (R : K1Seated L b blk wit J own₀ sort arr seats₀ ms rad)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop) {k : Coins Bk} {s s' : S}
    {m : Mid (Local W₀ Rc Xi Tr) X} {E : Env} {ds : List Fmt.Drawn}
    {y : List Played × Mid (Local W₀ Rc Xi Tr) X} {cols : List OpenedColumn}
    (hA : ThrS L.thread Said b k s m E) (hd : drawsFit blk.rounds ds = true)
    (hS : L.thread.Stepped blk k s m E ds y cols s')
    (n : ℕ) (hn : n < J.P.sent.size) :
    s'.book.place[s.st.oracles.size + n]? = some (seatAtMember L.bs b J.P n) := by
  obtain ⟨-, r₁, r₂, gs, -, hdec, -, -, -, -, -⟩ := step_at_block R Said hA hd hS
  have hpl := place_at_block J.P (R.books _ _ _ _ _ hdec) (book_at_border L Said hA).2.1 hn
  have htr : s.book.trees.size = treesTo L.bs b := by
    rw [R.treesNo]
    exact trees_at_border L Said hA R.placeAt rfl
  rw [htr] at hpl
  exact hpl

/-- And the library's reader of the witness's words, which seats a message by its tree's own number,
seats it there: under the two premises on the book. -/
theorem seatBy_behind (R : K1Seated L b blk wit J own₀ sort arr seats₀ ms rad)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop) {k : Coins Bk} {s s' : S}
    {m : Mid (Local W₀ Rc Xi Tr) X} {E : Env} {ds : List Fmt.Drawn}
    {y : List Played × Mid (Local W₀ Rc Xi Tr) X} {cols : List OpenedColumn}
    (hA : ThrS L.thread Said b k s m E) (hd : drawsFit blk.rounds ds = true)
    (hS : L.thread.Stepped blk k s m E ds y cols s')
    (hFits : Book.BookFits s'.book)
    (hNum : ∀ (z : ℕ) (T : OnBytes.Tree), s'.book.trees[z]? = some T → T.number = z)
    (n : ℕ) (hn : n < J.P.sent.size) :
    Sound.seatBy Sound.noFirst s'.book (s.st.oracles.size + n) =
      some (seatAtMember L.bs b J.P n) := by
  have hpl := place_behind R Said hA hd hS n hn
  obtain ⟨T, hTr, -⟩ := hFits _ _ hpl
  unfold Sound.seatBy
  rw [hpl, Option.bind_some, hTr, Option.map_some]
  show some (T.number, _) = _
  rw [hNum _ _ hTr]

/-- **THE WORDS**: behind the member's step, at every continuation of the challenges heard, the
words that the witness gives through the verifier's statement and book are, at each of the job's
messages, the held words of the rows that the part lays. hFits, hNum: TWO PUBLIC PREMISES ON THE
VERIFIER's BOOK BEHIND THE STEP. UNDER "Stepped": THE CUT IS THE FRAME's: IT HOLDS OF NOTHING AT A
BOOK THAT DOES NOT COVER THE PART's COUNT. -/
theorem words_behind (R : K1Seated L b blk wit J own₀ sort arr seats₀ ms rad)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop) {k : Coins Bk} {s s' : S}
    {m : Mid (Local W₀ Rc Xi Tr) X} {E : Env} {ds : List Fmt.Drawn}
    {y : List Played × Mid (Local W₀ Rc Xi Tr) X} {cols : List OpenedColumn}
    (hA : ThrS L.thread Said b k s m E) (hd : drawsFit blk.rounds ds = true)
    (hS : L.thread.Stepped blk k s m E ds y cols s')
    (hFits : Book.BookFits s'.book)
    (hNum : ∀ (z : ℕ) (T : OnBytes.Tree), s'.book.trees[z]? = some T → T.number = z)
    (c : Cs (dueR J.P J.ride)) (hc : lentCut k 0 ⟨J.P.place, 0⟩ (dueR J.P J.ride) = some c)
    (n : ℕ) (hn : n < J.P.sent.size) (w₀ : Words GE) (ds' : List Fmt.Drawn)
    (part : OnBytes.Part) (i : ℕ) :
    Sound.wordsFirst arr s'.st s'.book (L.Q.wit k y.2.st.input (y.2.st.heard ++ ds'))
        (s.st.oracles.size + n) part i =
      Johnson.Prover.Send.held w₀ s.st.oracles.size J.P
        (rowsLaid J own₀ c (wit m.st.input) m.st.heard) (s.st.oracles.size + n) part i := by
  obtain ⟨c₁, r₁, r₂, gs, hc₁, hdec, -, -, -, hin, hheard⟩ := step_at_block R Said hA hd hS
  have hB := R.books _ _ _ _ _ hdec
  obtain ⟨hcodes, x, hx, hxs, -⟩ := msg_at_block J.P R.isSend hdec hB n hn
  have hlen : m.st.heard.length = L.thread.front + roundsTo L.bs b := by
    have e := drawsFit_length _ _ hA.1.2.1
    rw [e, List.length_append]
    rfl
  have hT := tab_rows L.Q L.valid _ 0 wit J own₀ _ n _ _ _ (R.msgs n hn) (R.pads n hn) k c hc
    m.st.input hA.1.2.2.2.2.2.2 (m.st.heard ++ ds ++ ds')
    (by rw [List.length_append, List.length_append, hlen]; omega)
  have htk : (m.st.heard ++ ds ++ ds').take (L.thread.front + roundsTo L.bs b) = m.st.heard := by
    rw [List.append_assoc, ← hlen, List.take_left]
  rw [htk] at hT
  have hseat := seatBy_behind R Said hA hd hS hFits hNum n hn
  rw [hin, hheard, Johnson.Prover.Send.held_new _ _ _ _ n hn]
  show wordsOn s'.st (Sound.tabAt s'.st.codes arr (Sound.seatBy Sound.noFirst s'.book) s'.st _)
    (s.st.oracles.size + n) part i = _
  unfold wordsOn Sound.tabAt Statement.rowBits realRows
  rw [hseat, hx, hcodes]
  simp only [hxs, hT]
  cases part <;> rfl

/-! ## 4 The sample rows -/

/-- **THE SAMPLE ROWS**: behind the member's step, at every continuation of the challenges heard,
every sample row of the member's own class says its claim of the witness's words, UNDER hFits AND
hNum, THE TWO PUBLIC PREMISES ON THE VERIFIER's BOOK BEHIND THE STEP. At W's member classOf answers
nothing: this says nothing there. SPEAKS OF ANSWERS, WHICH HANG ON THE PADS (THROUGH THE SEED's
FACTOR: NOT AT A FACTOR 0, NOR AT A LIST OF SEEDS SHORTER THAN THE ANSWERS). UNDER "Stepped": THE
CUT IS THE FRAME's: IT HOLDS OF NOTHING AT A BOOK THAT DOES NOT COVER THE PART's COUNT. -/
theorem rows_behind (R : K1Seated L b blk wit J own₀ sort arr seats₀ ms rad)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop) {k : Coins Bk} {s s' : S}
    {m : Mid (Local W₀ Rc Xi Tr) X} {E : Env} {ds : List Fmt.Drawn}
    {y : List Played × Mid (Local W₀ Rc Xi Tr) X} {cols : List OpenedColumn}
    (hA : ThrS L.thread Said b k s m E) (hd : drawsFit blk.rounds ds = true)
    (hS : L.thread.Stepped blk k s m E ds y cols s')
    (hFits : Book.BookFits s'.book)
    (hNum : ∀ (z : ℕ) (T : OnBytes.Tree), s'.book.trees[z]? = some T → T.number = z)
    (m₀ t₀ : ℕ) (hcl : classOf sort = some (m₀, t₀)) (p : P) (yy : Strs)
    (ds' : List Fmt.Drawn) :
    rowSays L.N (wordsAtFirst arr) m₀ (.sample t₀) (p, s') yy
      (L.Q.wit k y.2.st.input (y.2.st.heard ++ ds')) := by
  obtain ⟨c, r₁, r₂, gs, hc, hdec, -, -, hans, -, -⟩ := step_at_block R Said hA hd hS
  have hB := R.books _ _ _ _ _ hdec
  intro r hr
  obtain ⟨o, -, hr⟩ := List.mem_flatMap.1 hr
  split at hr
  · rename_i hany
    obtain ⟨q, hq, hmem⟩ : ∃ q, s'.book.place[o]? = some q ∧ q ∈ L.N.sent m₀ t₀ := by
      cases hq : s'.book.place[o]? with
      | none =>
        rw [hq] at hany
        cases hany
      | some q =>
        rw [hq] at hany
        exact ⟨q, rfl, by simpa using hany⟩
    obtain ⟨n, hn, -, rfl⟩ := (R.seats q).1 (classOf_sub L.N sort m₀ t₀ hcl q hmem)
    obtain rfl : o = s.st.oracles.size + n :=
      Book.places_inj hFits hq (place_behind R Said hA hd hS n hn)
    obtain ⟨-, x, hx, -, hN⟩ := msg_at_block J.P R.isSend hdec hB n hn
    rw [hx] at hr
    have hr' : r ∈ x.sampleRows.toList := hr
    have h1 := says_at_block J.P R.isSend hdec hB _ hans (fun _ _ _ => 0) n hn x hx r hr'
    have h2 : Says rdE s'.st r (Sound.wordsFirst arr s'.st s'.book
        (L.Q.wit k y.2.st.input (y.2.st.heard ++ ds'))) := by
      unfold Says at h1 ⊢
      rw [← h1, value_named _ r _ (hN r hr'), value_named _ r _ (hN r hr'),
        onTable_same s'.st s'.st r _ _ _ .main rfl
          (fun i => words_behind R Said hA hd hS hFits hNum c hc n hn _ ds' .main i),
        onTable_same s'.st s'.st r _ _ _ .mask rfl
          (fun i => words_behind R Said hA hd hS hFits hNum c hc n hn _ ds' .mask i)]
    exact h2
  · cases hr

/-! ## 5 The kind's share of ExchangeS -/

/-- **THE KIND's SHARE AT "pin m t"** of the member's own class. SPEAKS OF ANSWERS, WHICH HANG ON
THE PADS. -/
theorem exchange_pin (R : K1Seated L b blk wit J own₀ sort arr seats₀ ms rad)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop) (m₀ t₀ : ℕ)
    (hcl : classOf sort = some (m₀, t₀)) : ExchangeAtS L.thread Said b (.pin m₀ t₀) := by
  intro blk' hblk k s m E ds y cols s' hA hd hS ds' i hi
  obtain rfl := List.mem_singleton.1 hi
  obtain rfl : blk' = blk := Option.some.inj (hblk.symm.trans R.member)
  intro x hx
  exact pins_behind R Said hA hd hS x (classOf_sub L.N sort m₀ t₀ hcl x hx) _ _ ds'

/-- **AT "pinI"**: at the opening. Of that message nothing here says what its entries are, nor which
kind spends which. -/
theorem exchange_pinI (R : K1Seated L b blk wit J own₀ .opening arr seats₀ ms rad)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop) :
    ExchangeAtS L.thread Said b .pinI := by
  intro blk' hblk k s m E ds y cols s' hA hd hS ds' i hi
  obtain rfl := List.mem_singleton.1 hi
  obtain rfl : blk' = blk := Option.some.inj (hblk.symm.trans R.member)
  exact pins_behind R Said hA hd hS L.N.index
    (List.mem_append_right _ (List.mem_singleton.2 rfl)) _ _ ds'

/-- **AT "pinV"**: at W's member. The data there are another file's letter: nothing here says what
W's entries are. -/
theorem exchange_pinV (R : K1Seated L b blk wit J own₀ .w arr seats₀ ms rad)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop) :
    ExchangeAtS L.thread Said b .pinV := by
  intro blk' hblk k s m E ds y cols s' hA hd hS ds' i hi
  obtain rfl := List.mem_singleton.1 hi
  obtain rfl : blk' = blk := Option.some.inj (hblk.symm.trans R.member)
  exact pins_behind R Said hA hd hS L.N.w (List.mem_singleton.2 rfl) _ _ ds'

/-- **AT "row m (sample t)"** of the member's own class, UNDER THE TWO PUBLIC PREMISES ON THE BOOK,
at every step under the pair. -/
theorem exchange_rows (R : K1Seated L b blk wit J own₀ sort arr seats₀ ms rad)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop) (m₀ t₀ : ℕ)
    (hcl : classOf sort = some (m₀, t₀))
    (hFits : ∀ k s m E ds y cols s', ThrS L.thread Said b k s m E →
      drawsFit blk.rounds ds = true → L.thread.Stepped blk k s m E ds y cols s' →
      Book.BookFits s'.book)
    (hNum : ∀ k s m E ds y cols s', ThrS L.thread Said b k s m E →
      drawsFit blk.rounds ds = true → L.thread.Stepped blk k s m E ds y cols s' →
      ∀ (z : ℕ) (T : OnBytes.Tree), s'.book.trees[z]? = some T → T.number = z) :
    ExchangeAtS L.thread Said b (.row m₀ (.sample t₀)) := by
  intro blk' hblk k s m E ds y cols s' hA hd hS ds' i hi
  obtain rfl := List.mem_singleton.1 hi
  obtain rfl : blk' = blk := Option.some.inj (hblk.symm.trans R.member)
  show (L.Mg y.2.st.input).row m₀ (.sample t₀) _ _ _
  rw [R.rowM]
  exact rows_behind R Said hA hd hS (hFits _ _ _ _ _ _ _ _ hA hd hS)
    (hNum _ _ _ _ _ _ _ _ hA hd hS) m₀ t₀ hcl _ _ ds'

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.draws_words
#print axioms ProofFile.Honest.K1.played_vals
#print axioms ProofFile.Honest.K1.rounds_played
#print axioms ProofFile.Honest.K1.step_at_block
#print axioms ProofFile.Honest.K1.step_at_block_any
#print axioms ProofFile.Honest.K1.pin_entry
#print axioms ProofFile.Honest.K1.pins_behind
#print axioms ProofFile.Honest.K1.classOf_sub
#print axioms ProofFile.Honest.K1.place_behind
#print axioms ProofFile.Honest.K1.seatBy_behind
#print axioms ProofFile.Honest.K1.words_behind
#print axioms ProofFile.Honest.K1.rows_behind
#print axioms ProofFile.Honest.K1.exchange_pin
#print axioms ProofFile.Honest.K1.exchange_pinI
#print axioms ProofFile.Honest.K1.exchange_pinV
#print axioms ProofFile.Honest.K1.exchange_rows
