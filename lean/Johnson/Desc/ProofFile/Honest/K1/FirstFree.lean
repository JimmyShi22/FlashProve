-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/FirstFree.lean: THE SHARED "SENDING" (the kind K1): WHAT THE PART
SENDS DOES NOT HANG ON THE NUMBER THAT ITS JOB STATES FOR ITS FIRST NEW ORACLE MESSAGE
(SendJob.first, Honest/K1/Part.lean). Eight theorems; no definition. A file of laws alone.

Why. The part's second move reckons its answers at a statement of its own (stAt) in which "first"
blank messages stand in front, at words that are 0 off the place, on rows that name the message
number first + k. The number stands thrice in that one term and nowhere else in the part. Here: the
term is the same at every number.

Main names (namespace ProofFile.Honest.K1).
  sample_coef_own, stAt_new, stAt_size_shift   public: the kind's sample row reads at its own
      message's number the same whatever that number is; which message stands at first + k in stAt;
      its tables' sizes.
  sample_value_shift   one sample row's value at the part's statement and words, at any number and
      at 0.
  answers_any_first   the part's list of answers at any number is the list at 0.
  job_answers_free   job_answers (Honest/K1/AnswersChain.lean) WITHOUT its premise on "first": under
      the one premise that the chain's statement has the place's codes, the term that sendPart's
      second move reckons is the term that the core's law on the sample rows asks.
  sendPart_any_first, sendHalf_any_first   the part, and the half, of a job with another number laid
      into "first" ARE the job's own.

By calls to lemmas of the library that lie outside the honest side's folders: K1.coefAt_sampleRow
(Johnson/Desc/K1/Law/Means.lean) · Third.Law.tableSize_same (Johnson/Desc/Third/Law/Renamed.lean) ·
LinkJoin.namesOne_sampleRow (Johnson/Desc/First/Link/Law/SampleAtK10.lean) · stSent_new
(OnBytes/Slice/BlkStLaws.lean) · held_new (Johnson/Prover/Send/Held.lean). OF THE FOLDER
Johnson/Goal/ IT CALLS NOTHING AND IMPORTS NOTHING.

Limits. sample_value_shift, answers_any_first and job_answers_free SPEAK OF ANSWERS, WHICH HANG ON
THE PADS (THROUGH THE SEED's FACTOR: NOT AT A FACTOR 0, NOR AT A LIST OF SEEDS SHORTER THAN THE
ANSWERS): each is an equation at one family of rows V. The two laws on the part and the half say
that two values are one: of what a part sends they say no more than that. WHAT THESE LAWS GIVE: THE
PART AND THE HALF ARE ONE VALUE AT EVERY NUMBER LAID INTO "first", AND THE TIE TO THE CORE's LAW
(job_answers_free) ASKS NOTHING OF IT. The part's text still names the field; job_answers keeps its
premise; the laws of Honest/K1/FirstNoLaw.lean speak of the number itself. Whether another text than
sendPart and proverSideOfSending reads the field is not followed here. Nothing on any property.

Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.AnswersChain

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open OnBytes OnBytes.Slice OnBytes.Means VerifiableInference.Desc
open Johnson.Prover.Send (Rows shapeAt answers held_new)
open _root_.Desc.Plain (DState)

/-- The kind's sample row reads at its own message's number the same, whatever that number is. -/
theorem sample_coef_own (m : K1.Msg) (o n : ℕ) (z : List E) (β : E) (i : ℕ) (y : E)
    (part : OnBytes.Part) (j : ℕ) :
    readE ((K1.sampleRow m o z β i y).coefficient o part j) =
      readE ((K1.sampleRow m n z β i y).coefficient n part j) := by
  have a := K1.coefAt_sampleRow m o z β i y o part j
  have b := K1.coefAt_sampleRow m n z β i y n part j
  simp only [beq_self_eq_true, Bool.true_and] at a b
  exact a.trans b.symm

/-- In the part's own statement the place's message number k stands at first + k. -/
theorem stAt_new (P : K1.Par) (f k : ℕ) :
    (stAt P f).oracles[f + k]? = (P.sent[k]?).map fun n => { shape := n.shape } := by
  have e := stSent_new { codes := P.codes, groups := #[]
                         oracles := Array.replicate f
                           { shape := { mainRows := 0, maskRows := 0, answers := 0 } } } P.sent k
  rw [Array.size_replicate] at e
  exact e

/-- Its tables have the same sizes at every number. -/
theorem stAt_size_shift (P : K1.Par) (f k : ℕ) (hk : k < P.sent.size) (part : OnBytes.Part) :
    tableSize (stAt P f) (f + k) part = tableSize (stAt P 0) (0 + k) part := by
  have h : P.sent[k]? = some P.sent[k] := Array.getElem?_eq_getElem hk
  exact Third.Law.tableSize_same (stAt P 0) (stAt P f) (0 + k) (f + k)
    { shape := P.sent[k].shape } { shape := P.sent[k].shape } (by rw [stAt_new, h]; rfl)
    (by rw [stAt_new, h]; rfl) rfl rfl part

/-- **One sample row's value, at any number and at 0.** SPEAKS OF ANSWERS, WHICH HANG ON THE PADS
(THROUGH THE SEED's FACTOR: NOT AT A FACTOR 0, NOR AT A LIST OF SEEDS SHORTER THAN THE ANSWERS): an
equation at one family of rows V. -/
theorem sample_value_shift (P : K1.Par) (f k : ℕ) (hk : k < P.sent.size) (V : ℕ → Rows)
    (m : K1.Msg) (z : List E) (β : E) (i : ℕ) (y : E) :
    value rdE (stAt P f) (K1.sampleRow m (f + k) z β i y)
        (Johnson.Prover.Send.held (fun _ _ _ => 0) f P V) =
      value rdE (stAt P 0) (K1.sampleRow m (0 + k) z β i y)
        (Johnson.Prover.Send.held (fun _ _ _ => 0) 0 P V) := by
  have t : ∀ part : OnBytes.Part,
      onTable rdE (stAt P f) (K1.sampleRow m (f + k) z β i y)
          (Johnson.Prover.Send.held (fun _ _ _ => 0) f P V) (f + k) part =
        onTable rdE (stAt P 0) (K1.sampleRow m (0 + k) z β i y)
          (Johnson.Prover.Send.held (fun _ _ _ => 0) 0 P V) (0 + k) part := by
    intro part
    unfold onTable
    rw [stAt_size_shift P f k hk part]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [held_new _ _ _ _ k hk, held_new _ _ _ _ k hk]
    exact congrArg (· * _) (sample_coef_own m (f + k) (0 + k) z β i y part j)
  rw [value_named _ _ _ (LinkJoin.namesOne_sampleRow _ _ _ _ _ _),
    value_named _ _ _ (LinkJoin.namesOne_sampleRow _ _ _ _ _ _), t .main, t .mask]

/-- **THE PART's ANSWERS ARE THE SAME AT EVERY NUMBER.** SPEAKS OF ANSWERS, WHICH HANG ON THE PADS
(THROUGH THE SEED's FACTOR: NOT AT A FACTOR 0, NOR AT A LIST OF SEEDS SHORTER THAN THE ANSWERS): an
equation of two lists at one family of rows V. -/
theorem answers_any_first (P : K1.Par) (f : ℕ) (V : ℕ → Rows) (seeds : List (List E × E)) :
    answers P (stAt P f) f (Johnson.Prover.Send.held (fun _ _ _ => 0) f P V) seeds =
      answers P (stAt P 0) 0 (Johnson.Prover.Send.held (fun _ _ _ => 0) 0 P V) seeds := by
  unfold answers
  apply List.flatMap_congr
  intro k hk
  have hk' : k < P.sent.size := List.mem_range.1 (List.mem_filter.1 hk).1
  apply List.map_congr_left
  intro i _
  rw [sample_value_shift P f k hk' V]

/-- **job_answers WITHOUT ITS PREMISE ON "first".** NOT UNDER THE SEAT's TEST, as job_answers is
not. SPEAKS OF ANSWERS, WHICH HANG ON THE PADS (THROUGH THE SEED's FACTOR: NOT AT A FACTOR 0, NOR AT
A LIST OF SEEDS SHORTER THAN THE ANSWERS): an equation of two lists at one family of rows V. -/
theorem job_answers_free {W X L : Type} (J : SendJob W X) (d : DState L)
    (hc : d.st.codes = J.P.codes) (w : Words GE) (V : ℕ → Rows) (seeds : List (List E × E)) :
    answers J.P (stAt J.P J.first) J.first
        (Johnson.Prover.Send.held (fun _ _ _ => 0) J.first J.P V) seeds =
      answers J.P (stSent d.st J.P.sent) d.st.oracles.size
        (Johnson.Prover.Send.held w d.st.oracles.size J.P V) seeds :=
  (answers_any_first J.P J.first V seeds).trans
    ((answers_any_first J.P d.st.oracles.size V seeds).symm.trans
      (part_answers J.P d hc w V seeds))

/-- **THE PART OF A JOB WITH ANOTHER NUMBER LAID INTO "first" IS THE JOB's OWN PART.** -/
theorem sendPart_any_first {V W X : Type} (J : SendJob W X) (f : ℕ) :
    sendPart (V := V) { J with first := f } = sendPart J := by
  unfold sendPart SendJob.rows
  simp only [answers_any_first J.P f, answers_any_first J.P J.first]

/-- The same of the half. -/
theorem sendHalf_any_first {V W X : Type} (J : SendJob W X) (f : ℕ) :
    proverSideOfSending (V := V) { J with first := f } = proverSideOfSending J := by
  unfold proverSideOfSending
  rw [sendPart_any_first]

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.sample_coef_own
#print axioms ProofFile.Honest.K1.stAt_new
#print axioms ProofFile.Honest.K1.stAt_size_shift
#print axioms ProofFile.Honest.K1.sample_value_shift
#print axioms ProofFile.Honest.K1.answers_any_first
#print axioms ProofFile.Honest.K1.job_answers_free
#print axioms ProofFile.Honest.K1.sendPart_any_first
#print axioms ProofFile.Honest.K1.sendHalf_any_first
