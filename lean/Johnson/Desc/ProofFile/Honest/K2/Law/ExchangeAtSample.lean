-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/ExchangeAtSample.lean: the kind "the code switch" (K2): THE
KIND's SHARE OF "THE EXCHANGE" (`ExchangeAtS`, Honest/Thread/SharesS.lean) AT THE ITEM "row seg
(sample 0)", under the record at a switch (`K2SeatedL`, Honest/K2/SeatedL.lean): behind the member's
step every sample row of the switch's own sending says its claim of the witness's words. Two
statements with their proofs: calls; no definition.

  `rows_behind` behind the step, at every continuation of the challenges heard: `rowSays`
                    (Johnson/Desc/First/Close/Law/FillRow.lean) at the class "sample 0" of the
                    segment seg, at the Script's witness: UNDER hFits AND hNum, TWO PREMISES on the
                    verifier's book alone, asked at every reached state (here: at the state behind
                    the step)
  `exchange_sample_switch` ⊢ `ExchangeAtS L.thread Said b (.row seg (.sample 0))`: under the record
                    and the two premises at every step under the pair

After the form of `rows_behind` and `exchange_rows` at the shared sending's member
(Honest/K1/Law/ExchangeAtPins.lean, of other authors; namespace ProofFile.Honest.K1), line by line but for
two things: `msg_at_block` and `says_at_block` (Honest/K1/Law/SendAtBlock.lean) are called at a
helper block (`fit_trimmed`, `block_at_cut`, Honest/K2/Law/AnsAtCut.lean), since the switch's yes
holds the sending's decision at a cut second round · the record's field `seats` speaks of the
class's seats outright, so no step from a sort to its class is wanted. Besides: `step_at_switch`
(Honest/K2/Law/StepAtSwitch.lean) · `place_behind` (Honest/K2/Law/SeatsBehind.lean) · `words_behind`
(Honest/K2/Law/WordsBehind.lean) · `value_named`, `onTable_same` (Honest/K1/AnswersChain.lean) · the
library's `places_inj` (Johnson/Desc/Book/BookFits.lean). Spends of the record, beside what these
spend: member · sends · books · seedsNo · nonZeroNo · answersNo · seats · rowM. NAMESAKES OF
`rows_behind`, each in a namespace of its own: `ProofFile.Honest.K1.rows_behind` (the model) ·
`VerifiableInference.Desc.First.K2Caller.rows_behind` (Johnson/Top/H0/Tw/K2C/TieThreeRows.lean) ·
`VerifiableInference.Desc.LinkJoin.rows_behind` (Johnson/Desc/First/Link/Law/RowsSameAt.lean) ·
`H2K5.Door.rows_behind`: on other matter.

Limits. SPEAKS OF ANSWERS, WHICH HANG ON THE PADS (through the seed's factor: not at a factor 0, nor
at a list of seeds shorter than the answers). hFits, hNum: premises: shown of no book here. Under
`Stepped`: it holds of nothing at a book of coins that lends the part nothing. On the switch's own
sending's sample rows alone: nothing on the carried claim, the kept members' earlier samples or the
positions' rows. The record is a record of premises: shown at no letters; `msgs` at a kept copy
wants a law that is not typed. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.WordsBehind

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open OnBytes OnBytes.Slice OnBytes.Means Cb Cb.Ood Johnson.Pack VerifiableInference.Desc
open VerifiableInference.Desc.First (S rowSays wordsAtFirst)
open VerifiableInference.Desc.First.K2 (P2)
open VerifiableInference.Desc.Sound (MsgT Mem)
open ProofFile.Honest.FirstThread (Letters)
open ProofFile.Honest.K1 (msg_at_block says_at_block value_named onTable_same)

variable {Bk : ProofFile.Honest.ProverCoinCounts} {Cl W₀ Rc Xi Tr X P Cells Tok : Type}
variable {L : Letters Bk Cl W₀ Rc Xi Tr X P Cells Tok MsgT} {b : Nat} {blk : Block S Cl}
  {D : RowDataOf Xi} {readers : Local W₀ Rc Xi Tr → Readers} {lay : OnBytes.Params.ReqLayout}
  {segs : List SegmentPub} {p : SwitchPlace} {q : P2} {before : S → Except String S}
  {after : S → S → Except String S} {seg first : Nat} {Zp : ProofFile.Pub} {arr : ℕ → ℕ → ℕ}
  {seats₀ : List (ℕ × ℕ)} {ms : List Mem} {rad : ℕ → ℕ}

/-- **THE SAMPLE ROWS**: behind the member's step, at every continuation of the challenges heard,
every sample row of the switch's own sending says its claim of the witness's words, UNDER hFits AND
hNum, THE TWO PREMISES on the verifier's book alone, asked at every reached state (here: at the
state behind the step). SPEAKS OF ANSWERS, WHICH HANG ON THE PADS. hA: the thread's invariant in
front of the member (`ThrS`). hS: `Thread.Stepped`: the half has moved, and the member's own step
returns s' at what was played. NOT IN FRONT OF A LAW OVER COINS. -/
theorem rows_behind
    (R : K2SeatedL L b blk D readers lay segs p q before after seg first Zp arr seats₀ ms rad)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop) {k : Coins Bk} {s s' : S}
    {m : Mid (Local W₀ Rc Xi Tr) X} {E : Env} {ds : List Fmt.Drawn}
    {y : List Played × Mid (Local W₀ Rc Xi Tr) X} {cols : List OpenedColumn}
    (hA : ThrS L.thread Said b k s m E) (hd : drawsFit blk.rounds ds = true)
    (hS : L.thread.Stepped blk k s m E ds y cols s')
    (hFits : VerifiableInference.Desc.Book.BookFits s'.book)
    (hNum : ∀ (z : ℕ) (T : OnBytes.Tree), s'.book.trees[z]? = some T → T.number = z)
    (pp : P) (yy : Strs) (ds' : List Fmt.Drawn) :
    rowSays L.N (wordsAtFirst arr) seg (.sample 0) (pp, s') yy
      (L.Q.wit k y.2.st.input (y.2.st.heard ++ ds')) := by
  obtain ⟨c, V, r₁, r₂, gs, hc, hV, hdec, hfit, -, hans, -, -⟩ :=
    step_at_switch R Said hA hd hS
  have hB := R.books _ _ _ _ _ _ _ _ hA.1 hdec
  obtain ⟨-, hl⟩ := fit_trimmed (switchPar p) q R.seedsNo R.nonZeroNo R.answersNo hfit
  obtain ⟨b', hS', hd'⟩ := block_at_cut (switchPar p)
    (fun _ _ _ _ h => R.sends _ _ _ _ _ _ _ _ hA.1 h) hdec hl
  intro r hr
  obtain ⟨o, -, hr⟩ := List.mem_flatMap.1 hr
  split at hr
  · rename_i hany
    obtain ⟨z, hz, hmem⟩ : ∃ z, s'.book.place[o]? = some z ∧ z ∈ L.N.sent seg 0 := by
      cases hz : s'.book.place[o]? with
      | none =>
        rw [hz] at hany
        cases hany
      | some z =>
        rw [hz] at hany
        exact ⟨z, rfl, by simpa using hany⟩
    obtain ⟨n, hn, -, rfl⟩ := (R.seats z).1 hmem
    obtain rfl : o = s.st.oracles.size + n :=
      Book.places_inj hFits hz (place_behind R Said hA hd hS n hn)
    obtain ⟨-, x, hx, -, hN⟩ := msg_at_block (switchPar p) hS' hd' hB n hn
    rw [hx] at hr
    have hr' : r ∈ x.sampleRows.toList := hr
    have h1 := says_at_block (switchPar p) hS' hd' hB V hans (fun _ _ _ => 0) n hn x hx r hr'
    have h2 : Says rdE s'.st r (Sound.wordsFirst arr s'.st s'.book
        (L.Q.wit k y.2.st.input (y.2.st.heard ++ ds'))) := by
      unfold Says at h1 ⊢
      rw [← h1, value_named _ r _ (hN r hr'), value_named _ r _ (hN r hr'),
        onTable_same s'.st s'.st r _ _ _ .main rfl
          (fun i => words_behind R Said hA hd hS hFits hNum c hc V hV n hn _ ds' .main i),
        onTable_same s'.st s'.st r _ _ _ .mask rfl
          (fun i => words_behind R Said hA hd hS hFits hNum c hc V hV n hn _ ds' .mask i)]
    exact h2
  · cases hr

/-- **AT "row seg (sample 0)"**, UNDER THE TWO PREMISES on the verifier's book alone, asked at every
reached state: at every step under the pair. Under `Stepped`: where the book of coins lends the part
nothing the ends hold of nothing. FREE LETTERS OF THE RECORD: D · readers · rad · before · after;
and, inside its field `sends`, the type Lt and the states d, d'. `readers` takes the whole input.
hFits, hNum: asked at every run's coins, state and step under `ThrS` and `Stepped`.
NOT IN FRONT OF A LAW OVER COINS.
-/
theorem exchange_sample_switch
    (R : K2SeatedL L b blk D readers lay segs p q before after seg first Zp arr seats₀ ms rad)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop)
    (hFits : ∀ k s m E ds y cols s', ThrS L.thread Said b k s m E →
      drawsFit blk.rounds ds = true → L.thread.Stepped blk k s m E ds y cols s' →
      VerifiableInference.Desc.Book.BookFits s'.book)
    (hNum : ∀ k s m E ds y cols s', ThrS L.thread Said b k s m E →
      drawsFit blk.rounds ds = true → L.thread.Stepped blk k s m E ds y cols s' →
      ∀ (z : ℕ) (T : OnBytes.Tree), s'.book.trees[z]? = some T → T.number = z) :
    ExchangeAtS L.thread Said b (.row seg (.sample 0)) := by
  intro blk' hblk k s m E ds y cols s' hA hd hS ds' i hi
  obtain rfl := List.mem_singleton.1 hi
  obtain rfl : blk' = blk := Option.some.inj (hblk.symm.trans R.member)
  show (L.Mg y.2.st.input).row seg (.sample 0) _ _ _
  rw [R.rowM]
  exact rows_behind R Said hA hd hS (hFits _ _ _ _ _ _ _ _ hA hd hS)
    (hNum _ _ _ _ _ _ _ _ hA hd hS) _ _ ds'

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.rows_behind
#print axioms ProofFile.Honest.K2.Law.exchange_sample_switch
