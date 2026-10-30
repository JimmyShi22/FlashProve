-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/StepAtSwitch.lean: the kind "the code switch" (K2): THE
MEMBER's STEP, UNPACKED, under the record at a switch (`K2SeatedL`, Honest/K2/SeatedL.lean): from
the thread's invariant in front of the member, challenges that its rounds can draw, and the member's
step (`Thread.Stepped`, Honest/Thread/Pays.lean): what the frame hands the part, the rows that the
part lays, the yes of the member's own decision, the test on the rounds' form, and what the second
round's values are. One statement with its proof: calls; no definition.

  `step_at_switch` there are c, rows V, two rounds and groups of columns with: the frame hands the
                    part c (`handed`, Honest/K2/ScriptLots.lean) · V are the switch's messages in
                    full at c, at the input and at what was heard in front (`switchRowsLaid`) · the
                    member's decision says yes from s to s' at the two rounds · these fit the kind's
                    own rounds at the place's numbers (`roundsFit`) · the first round's elements are
                    spelt by words below the prime · THE SECOND ROUND's VALUES ARE THE ANSWERS AT
                    THE HELD WORDS OF V, at the seeds of the first round, at the number of messages
                    that the statement in front has · the input stays; what is heard grows by the
                    challenges

After the form of `step_at_block` (Honest/K1/Law/ExchangeAtPins.lean, of other authors), at the
shared sending's member. By: `steps_one_half` (Honest/Law/Thread.lean) · `draws_two`
(Honest/K2/Law/ExactProof.lean) · `play_heard` (Honest/Thread/PaysLaw.lean) · `half_played_rows`
(Honest/K2/Law/PlayedOfRows.lean) · `lent_part`, `rounds_items` (Honest/K2/Law/PlaysSeated.lean),
along the lines of that file's `switch_plays`, run from a given step · `returnsLaw`
(Honest/K2/Law/SegmentAlike.lean) · the library's `step_ok` (Johnson/Desc/K1/Law/AtRecord.lean),
which is general in the block, and its `roundsFit_noDigest` (Johnson/Desc/K15/SendOwnLaw.lean) ·
`draws_words` (ExchangeAtPins.lean) and `answers_canon` (Honest/K1/Law/SendAtBlock.lean), which are
general in the plan. Spends of the record: shape · half · serves · roomy · placeOk · closes ·
publicAt · trees · answersNo.

Limits. THE TWO ROUNDS ARE AS THE MEMBER's DECISION IS SHOWN THEM: without the sealed digest. THE 0
BENEATH THE HELD WORDS IS A CONSTANT, NO COIN. SPEAKS OF ANSWERS, WHICH HANG ON THE PADS. An
equation at one run's coins, at every k: it says nothing on how a coin is made. Under `Stepped`: it
holds of nothing at a book that lends the part nothing. The record is a record of premises: shown at
no letters. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.SeatedL
import Johnson.Desc.ProofFile.Honest.K2.Law.PlayedOfRows
import Johnson.Desc.ProofFile.Honest.K1.Law.ExchangeAtPins
import Johnson.Desc.ProofFile.Honest.Thread.Said
import Johnson.Desc.K1.Law.AtRecord
import Johnson.Desc.K15.SendOwnLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc (Block roundsFit noDigest OpenedColumn fieldPrimeWord)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2 (P2 rounds)
open VerifiableInference.Desc.Sound (MsgT Mem)
open ProofFile.Honest.FirstThread (Letters)
open Johnson.Prover.Send (answers)

variable {Bk : ProverCoinCounts} {Cl W₀ Rc Xi Tr X P Cells Tok : Type}
variable {L : Letters Bk Cl W₀ Rc Xi Tr X P Cells Tok MsgT} {b : Nat} {blk : Block S Cl}
  {D : RowDataOf Xi} {readers : Local W₀ Rc Xi Tr → Readers} {lay : OnBytes.Params.ReqLayout}
  {segs : List SegmentPub} {p : SwitchPlace} {q : P2} {before : S → Except String S}
  {after : S → S → Except String S} {seg first : Nat} {Zp : ProofFile.Pub} {arr : ℕ → ℕ → ℕ}
  {seats₀ : List (ℕ × ℕ)} {ms : List Mem} {rad : ℕ → ℕ}

/-- **THE MEMBER's STEP, UNPACKED.** c: what the frame hands the part off the run's coins. V: the
switch's messages in full, by number in the order of sending. THE 0 BENEATH THE HELD WORDS: NO COIN:
A CONSTANT. hA: the thread's invariant in front of the member (`ThrS`). hS: `Thread.Stepped`: the
half has moved, and the member's own step returns s' at what was played.
NOT IN FRONT OF A LAW OVER COINS. -/
theorem step_at_switch
    (R : K2SeatedL L b blk D readers lay segs p q before after seg first Zp arr seats₀ ms rad)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop) {k : Coins Bk} {s s' : S}
    {m : Mid (Local W₀ Rc Xi Tr) X} {E : Env} {ds : List Fmt.Drawn}
    {y : List Played × Mid (Local W₀ Rc Xi Tr) X} {cols : List OpenedColumn}
    (hA : ThrS L.thread Said b k s m E) (hd : drawsFit blk.rounds ds = true)
    (hS : L.thread.Stepped blk k s m E ds y cols s') :
    ∃ (c : SwitchCoins p.sizes p.others p.foldVars p.carries)
      (V : Nat → Johnson.Prover.Send.Rows) (r₁ r₂ : Fmt.RoundView)
      (gs : List (List (Nat × List UInt64))),
      handed 0 p k = some c ∧
      switchRowsLaid D readers (lotClosingAt lay segs) p c m.st.input m.st.heard = .ok V ∧
      blk.decide s [r₁, r₂] gs = .ok s' ∧
      roundsFit (rounds q) [r₁, r₂] = true ∧
      (r₁.drawn.elems.all fun x => x.1 < fieldPrimeWord && x.2.1 < fieldPrimeWord && x.2.2 < fieldPrimeWord) = true ∧
      r₂.vals = (answers (switchPar p) (K1.stAt (switchPar p) s.st.oracles.size) s.st.oracles.size
        (Johnson.Prover.Send.held (fun _ _ _ => 0) s.st.oracles.size (switchPar p) V)
        (VerifiableInference.Desc.K1.seedsOf (switchPar p) r₁)).map .answer ∧
      y.2.st.input = m.st.input ∧ y.2.st.heard = m.st.heard ++ ds := by
  obtain ⟨⟨⟨l, hl, hy⟩, -⟩, hstep⟩ := hS
  obtain ⟨⟨-, -, -, -, -, -, hval⟩, -⟩ := hA
  have hf' : (L.hs.find? fun g => g.place == blk.place) =
      some (switchHalf (coreSender freshTable) D readers (lotClosingAt lay segs) p) := by
    rw [R.shape.1]
    exact R.half
  obtain ⟨c, hlend, el⟩ := steps_one_half hf' hl
  obtain ⟨d₁, d₂, hq⟩ : ∃ d₁ d₂, rounds q = [d₁, d₂] := ⟨_, _, rfl⟩
  rw [R.shape.2.1, hq] at hd
  obtain ⟨x₁, x₂, rfl, -⟩ := draws_two d₁ d₂ ds hd
  obtain ⟨V, m', hV, hy', hi⟩ := half_played_rows D readers (lotClosingAt lay segs) p blk d₁ d₂
    q.sent [] (by rw [R.shape.2.1, R.shape.2.2, hq]; rfl) (L.thread.φ.sees m.st.input) c x₁ x₂ m
    R.serves R.roomy R.placeOk (rounds_items q d₁ d₂ hq).1 R.trees
    (by rw [R.answersNo]; exact (rounds_items q d₁ d₂ hq).2) rfl
    ((returnsLaw D readers lay segs p R.closes m.st.input m.st.heard c.1.2.2).trans
      (R.publicAt _ hval)) s.st.oracles.size
  rw [← el] at hy'
  obtain rfl : y = (_, m') := Except.ok.inj (hy.symm.trans hy')
  obtain ⟨hfit, gs, hdec⟩ := VerifiableInference.Desc.K1.step_ok _ blk s s' _ _ _ hstep
  have hw : (x₁.elems.all fun x => x.1 < fieldPrimeWord && x.2.1 < fieldPrimeWord && x.2.2 < fieldPrimeWord) = true :=
    ProofFile.Honest.K1.draws_words hd
  refine ⟨c.1, V, noDigest ⟨[], x₁⟩, noDigest ⟨_, x₂⟩, gs, ?_, hV, hdec, ?_, hw, ?_, hi,
    play_heard _ _ _ _ _ hy'⟩
  · have h := lent_part Bk (Bk.rowsOf 0) (k.look 0) blk.place (coreSender freshTable) D readers
      (lotClosingAt lay segs) p c hlend
    unfold handed
    rw [← R.shape.1, h]
    rfl
  · rw [R.shape.2.1] at hfit
    exact (VerifiableInference.Desc.roundsFit_noDigest _ _).trans hfit
  · show (((answers (switchPar p) (K1.stAt (switchPar p) s.st.oracles.size) s.st.oracles.size
      (Johnson.Prover.Send.held (fun _ _ _ => 0) s.st.oracles.size (switchPar p) V)
      (K1.seedsAt (switchPar p) [x₁])).map OnBytes.Slice.toE).map
        ProofFile.Honest.Said.answer).map ProofFile.Honest.Said.got = _
    rw [List.map_map, List.map_map]
    refine List.map_congr_left fun a ha => ?_
    show Fmt.ItemValue.answer (OnBytes.Slice.ofE (OnBytes.Slice.toE a)) = _
    rw [ProofFile.Honest.K1.answers_canon _ _ _ _ _ a ha]

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.step_at_switch
