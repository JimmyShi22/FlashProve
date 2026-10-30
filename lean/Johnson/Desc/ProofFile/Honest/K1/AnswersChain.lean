-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/AnswersChain.lean: THE SHARED "SENDING" (the kind K1): THE ANSWERS
THAT THE HONEST PART RECKONS AT A STATEMENT OF ITS OWN MAKING ARE THE ANSWERS AT THE CHAIN's
STATEMENT, UNDER TWO PREMISES: the job's "first" is the number of messages in the chain's statement;
that statement has the place's codes. Theorems; no definition. No coin is read.

Why. The second move of sendPart (Honest/K1/Part.lean) reckons answers J.P (stAt J.P J.first)
J.first (held 0 …): at a statement that holds "first" messages without a row and then the place's
own, and at words that are 0 off the place. The law on the new sample rows (send_says,
Johnson/Prover/Send/Says.lean) asks for the answers at the chain's statement behind the sending and
at the chain's held words. The two agree because answers (Johnson/Prover/Send/Core.lean) reads the
statement and the words inside Means.value alone, at K1's sample row; that row has no coefficient
off its own message; and the sizes of a message's two tables hang on its shape and on the
statement's codes alone.

Main names (namespace ProofFile.Honest.K1).
  value_named   a row that has no coefficient off the message o (NamesOne) is worth what it gives on
      that message's two tables; no premise that o lies below the statement's end.
  size_same, onTable_same   one codes and one shape at o (or no message in either statement): tables
      of one size; a row on one table, at two statements and two families of words that agree there.
  answers_at_chain   two statements with one codes in which the place's messages have one shape
      each, two families of words that agree on these messages: one list of answers.
  part_answers   UNDER d.st.codes = P.codes: the part's term at "first" := the number of messages in
      d.st is the term of send_says.
  job_answers   the same in a job's letters, UNDER J.first = d.st.oracles.size AND d.st.codes =
      J.P.codes.
  seeds_at   the part's cut of the seeds off a list of challenges that begins with a round's is the
      verifier's side's cut off that round.

By calls to lemmas of the library that lie outside the honest side's folders; nothing else of these
folders is called: LinkJoin.namesOne_sampleRow (Johnson/Desc/First/Link/Law/SampleAtK10.lean), with
the definition NamesOne (Johnson/Desc/First/Close/Law/SampleTie.lean) · Third.Law.tableSize_same
(Johnson/Desc/Third/Law/Renamed.lean) · Slice.stSent_new (OnBytes/Slice/BlkStLaws.lean). They speak
of a public row's coefficients and of the sizes of a statement's tables: public data, though not the
layout. Of the sender's core: held_new (Johnson/Prover/Send/Held.lean). A FILE OF LAWS ALONE. OF THE
FOLDER Johnson/Goal/ IT CALLS NOTHING AND IMPORTS NOTHING DIRECTLY.

Kin. value_named: Third.Law.value_one (Renamed.lean) asks that the row's lists name o alone and that
o lies below the end; of K1's sample row the library shows NamesOne, on coefficients. size_same: its
case of two messages calls tableSize_same. K3.KeyLaw.value_same
(Johnson/Desc/First/Look/KeyLaw/SameTables.lean) asks one number of messages and one size at every
message, and Desc.K14.Law.value_same (Johnson/Desc/K14/Law/Shapes.lean) that one statement grows out
of the other: the part's statement and the chain's differ in front of "first", and neither grows out
of the other.

Limits. The two premises are shown of no chain here. The premise on "first" is shed in
Honest/K1/FirstFree.lean: job_answers_free has the same equation under the premise on the codes
alone; job_answers keeps both. Not treated: that what the frame sends (.answer (toE a)) becomes the
round's values · that the challenges which the part reads (t.lately 1) begin with that round's · the
other premises of send_yes_of (Johnson/Prover/Send/Form.lean).
answers_at_chain, part_answers and job_answers SPEAK OF ANSWERS, WHICH HANG ON THE PADS (THROUGH THE
SEED's FACTOR: NOT AT A FACTOR 0, NOR AT A LIST OF SEEDS SHORTER THAN THE ANSWERS): each is an
equation of two lists: at one family of rows, or at two families of words that agree on the place's
messages. Nothing on any property.

Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.Part
import Johnson.Prover.Send.Held
import Johnson.Desc.First.Link.Law.SampleAtK10
import Johnson.Desc.Third.Law.Renamed
import OnBytes.Slice.BlkStLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open OnBytes OnBytes.Slice OnBytes.Means VerifiableInference.Desc
open Johnson.Prover.Send (Rows shapeAt answers held_new)
open _root_.Desc.Plain (DState)
open VerifiableInference.Desc.First.Close (NamesOne)

/-- A row that has no coefficient off the message o is worth what it gives on that message's two
tables. Beyond the statement's last message both tables have size 0, and both sides are 0. -/
theorem value_named (S : Statement) (r : OnBytes.Row) (o : ℕ) (h : NamesOne r o) (w : Words GE) :
    value rdE S r w = onTable rdE S r w o .main + onTable rdE S r w o .mask := by
  have off : ∀ b, b ≠ o → onTable rdE S r w b .main + onTable rdE S r w b .mask = 0 := by
    intro b hb
    unfold onTable
    rw [Finset.sum_eq_zero, Finset.sum_eq_zero, add_zero]
    · intro i _
      show readE (r.coefficient b .mask i) * _ = 0
      rw [h b hb, zero_mul]
    · intro i _
      show readE (r.coefficient b .main i) * _ = 0
      rw [h b hb, zero_mul]
  unfold value
  by_cases ho : o < S.oracles.size
  · rw [Finset.sum_eq_single o]
    · intro b _ hb
      exact off b hb
    · intro hn
      exact absurd (Finset.mem_range.2 ho) hn
  · rw [Finset.sum_eq_zero fun b hb => off b fun e => ho (e ▸ Finset.mem_range.1 hb)]
    have z : ∀ part, tableSize S o part = 0 := by
      intro part
      simp [tableSize, Statement.has, Array.getElem?_eq_none (Nat.le_of_not_lt ho)]
    unfold onTable
    rw [z, z]
    simp

/-- Two statements with one codes, in which the message number o has one shape or is in neither:
its tables have one size. -/
theorem size_same (S S' : Statement) (o : ℕ) (hc : S'.codes = S.codes)
    (hx : (S'.oracles[o]?).map (·.shape) = (S.oracles[o]?).map (·.shape))
    (part : OnBytes.Part) :
    tableSize S' o part = tableSize S o part := by
  cases h : S.oracles[o]? with
  | none =>
    have h' : S'.oracles[o]? = none := by
      rw [h] at hx
      simpa using hx
    simp [tableSize, Statement.has, h, h']
  | some x =>
    have hx2 : (S'.oracles[o]?).map (·.shape) = some x.shape := by
      rw [hx, h]
      rfl
    obtain ⟨x', h', e⟩ := Option.map_eq_some_iff.1 hx2
    exact Third.Law.tableSize_same S S' o o x x' h h' e hc part

/-- A row on one table, at two statements and two families of words that agree there. -/
theorem onTable_same (S S' : Statement) (r : OnBytes.Row) (w w' : Words GE) (o : ℕ)
    (part : OnBytes.Part)
    (hs : tableSize S' o part = tableSize S o part) (hw : ∀ i, w' o part i = w o part i) :
    onTable rdE S' r w' o part = onTable rdE S r w o part := by
  unfold onTable
  rw [hs]
  exact Finset.sum_congr rfl fun i _ => by rw [hw i]

/-- **THE ANSWERS HANG ON THE PLACE's OWN MESSAGES ALONE.** Two statements with one codes, in which
the place's messages have one shape each; two families of words that agree on these messages: the
two lists of answers are one.
SPEAKS OF ANSWERS, WHICH HANG ON THE PADS (THROUGH THE SEED's FACTOR: NOT AT A FACTOR 0, NOR AT A
LIST OF SEEDS SHORTER THAN THE ANSWERS): an equation of two lists, at two families of words that
agree on the place's messages. -/
theorem answers_at_chain (P : K1.Par) (S S' : Statement) (first : ℕ) (w w' : Words GE)
    (seeds : List (List E × E)) (hc : S'.codes = S.codes)
    (hx : ∀ k, k < P.sent.size →
      (S'.oracles[first + k]?).map (·.shape) = (S.oracles[first + k]?).map (·.shape))
    (hw : ∀ k, k < P.sent.size → ∀ part i, w' (first + k) part i = w (first + k) part i) :
    answers P S' first w' seeds = answers P S first w seeds := by
  unfold answers
  apply List.flatMap_congr
  intro k hk
  have hk' : k < P.sent.size := List.mem_range.1 (List.mem_filter.1 hk).1
  apply List.map_congr_left
  intro i _
  rw [value_named S' _ _ (LinkJoin.namesOne_sampleRow _ _ _ _ _ _),
    value_named S _ _ (LinkJoin.namesOne_sampleRow _ _ _ _ _ _),
    onTable_same S S' _ w w' _ .main (size_same S S' _ hc (hx k hk') .main) (hw k hk' .main),
    onTable_same S S' _ w w' _ .mask (size_same S S' _ hc (hx k hk') .mask) (hw k hk' .mask)]

/-- **UNDER ONE PREMISE, THAT THE CHAIN's STATEMENT HAS THE PLACE's CODES, THE PART's ANSWERS ARE
THE CHAIN's**: the answers at the part's own statement (stAt) and at words that are 0 off the place
are the answers at the chain's statement behind the sending and at the chain's held words.
SPEAKS OF ANSWERS, WHICH HANG ON THE PADS (THROUGH THE SEED's FACTOR: NOT AT A FACTOR 0, NOR AT A
LIST OF SEEDS SHORTER THAN THE ANSWERS): an equation of two lists at one family of rows V. -/
theorem part_answers {L : Type} (P : K1.Par) (d : DState L) (hc : d.st.codes = P.codes)
    (w : Words GE) (V : ℕ → Rows) (seeds : List (List E × E)) :
    answers P (stAt P d.st.oracles.size) d.st.oracles.size
        (Johnson.Prover.Send.held (fun _ _ _ => 0) d.st.oracles.size P V) seeds =
      answers P (stSent d.st P.sent) d.st.oracles.size
        (Johnson.Prover.Send.held w d.st.oracles.size P V) seeds := by
  apply answers_at_chain
  · exact hc.symm
  · intro k _
    have e := stSent_new { codes := P.codes, groups := #[]
                           oracles := Array.replicate d.st.oracles.size
                             { shape := { mainRows := 0, maskRows := 0, answers := 0 } } } P.sent k
    rw [Array.size_replicate] at e
    rw [stSent_new]
    exact congrArg _ e
  · intro k hk part i
    rw [held_new _ _ _ _ k hk, held_new _ _ _ _ k hk]

/-- The same in a job's letters: the term that sendPart's second move reckons is the term that the
core's law on the sample rows asks (Johnson/Prover/Send/Says.lean, send_says).
NOT UNDER THE SEAT's TEST: it reads neither the job's ride nor its data: the rows V are a letter,
and the two premises speak of the chain's statement.
SPEAKS OF ANSWERS, WHICH HANG ON THE PADS (THROUGH THE SEED's FACTOR: NOT AT A FACTOR 0, NOR AT A
LIST OF SEEDS SHORTER THAN THE ANSWERS): an equation of two lists at one family of rows V. -/
theorem job_answers {W X L : Type} (J : SendJob W X) (d : DState L)
    (hf : J.first = d.st.oracles.size) (hc : d.st.codes = J.P.codes) (w : Words GE)
    (V : ℕ → Rows) (seeds : List (List E × E)) :
    answers J.P (stAt J.P J.first) J.first
        (Johnson.Prover.Send.held (fun _ _ _ => 0) J.first J.P V) seeds =
      answers J.P (stSent d.st J.P.sent) d.st.oracles.size
        (Johnson.Prover.Send.held w d.st.oracles.size J.P V) seeds := by
  rw [hf]
  exact part_answers J.P d hc w V seeds

/-- The part's seeds off a list of challenges whose first is a round's are the seeds that the
verifier's side cuts off that round. -/
theorem seeds_at (P : K1.Par) (r₁ : Fmt.RoundView) (ds : List Fmt.Drawn) :
    seedsAt P (r₁.drawn :: ds) = K1.seedsOf P r₁ := rfl

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.value_named
#print axioms ProofFile.Honest.K1.size_same
#print axioms ProofFile.Honest.K1.onTable_same
#print axioms ProofFile.Honest.K1.answers_at_chain
#print axioms ProofFile.Honest.K1.part_answers
#print axioms ProofFile.Honest.K1.job_answers
#print axioms ProofFile.Honest.K1.seeds_at
