-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/SendingsViaAnswers.lean: the out-of-domain (OOD) answers of a
sending (answers, Johnson/Prover/Send/Core.lean) hang on the codes, the seeds and the SAMPLED
messages' own two tables alone: not on the statement in front, on the number that the first new
message gets, on the words in front, or on a message that is not sampled.

  answer_sum      one answer's value: a sum over the message's own two tables, below their sizes
  answers_same    **two statements in front with the sending's codes, two families of rows that
                  agree on the sampled messages' tables below the sizes: the same answers**
  stFront, stAt_front   the statement at which the shared part computes its answers (stAt,
                  Honest/K1/Part.lean) is a statement in front, with the sending's messages received
  answers_round   an answer, laid into the field and back, is itself
  via_shown       **the term viaShownAt** (Honest/K14/SendingsViaPaid.lean: what a call of the
                  shared part shows in its second round, where the call passes sendFits and the
                  challenge holds the seeds: via_moved) **is answersAt**
                  (Johnson/Desc/K14/Honest/SendMoves.lean) at any statement in front with the codes,
                  any words in front, and any rows that agree with the call's rows on the sampled
                  messages' tables

What is assumed. Only what is named above.
What is not claimed. That the call's rows agree with any honest tables: for this kind's two calls it
is stated by `viaU_same` and `viaOmega_same` (Honest/K14/SendingsViaShows.lean), of this kind's own
text, under their premises on the plan, the shapes and `sendFits`, `viaU_same` at a sampled message
alone. Nothing on a verifier's decision, on soundness or on hiding.
-/
import Johnson.Desc.ProofFile.Honest.K14.SendingsViaPaid
import Johnson.Desc.ProofFile.Honest.K14.SendingsAnswers

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open OnBytes (E zeroE Statement Codes OracleNotice)
open OnBytes.Means (Words)
open OnBytes.Slice (GE rdE ofE toE stSent)
open VerifiableInference.Desc (K1.Par K1.Msg K1.Msg.of K1.sampleRow K1.cutSeeds)
open VerifiableInference.Desc.K1 (tableSize_eq)
open Johnson.Prover.Send (Rows shapeAt answers)
open ProofFile.Honest.K1 (sendPart sendFits dueR stAt seedsAt)

/-- One answer's value: a sum over the message's own two tables, below their sizes. -/
theorem answer_sum (Q : K1.Par) (T : Statement) (hT : T.codes = Q.codes) (V : Nat → Rows)
    (w : Words GE) (k : Nat) (hk : k < Q.sent.size) (z : List E) (β : E) (i : Nat) :
    OnBytes.Means.value rdE (stSent T Q.sent)
        (K1.sampleRow (K1.Msg.of Q.codes (shapeAt Q k)) (T.oracles.size + k) z β i zeroE)
        (Johnson.Prover.Send.held w T.oracles.size Q V) =
      (∑ j ∈ Finset.range ((K1.Msg.of Q.codes (shapeAt Q k)).size .main),
        sampleK (K1.Msg.of Q.codes (shapeAt Q k)) z β i .main j *
          (V k).word (shapeAt Q k) .main j) +
      ∑ j ∈ Finset.range ((K1.Msg.of Q.codes (shapeAt Q k)).size .mask),
        sampleK (K1.Msg.of Q.codes (shapeAt Q k)) z β i .mask j *
          (V k).word (shapeAt Q k) .mask j := by
  have h2 := stSent_at Q T k hk
  have l2 : T.oracles.size + k < (stSent T Q.sent).oracles.size := by
    by_contra h
    rw [Array.getElem?_eq_none (Nat.le_of_not_lt h)] at h2
    cases h2
  have s2 : ∀ part, OnBytes.Means.tableSize (stSent T Q.sent) (T.oracles.size + k) part =
      (K1.Msg.of Q.codes (shapeAt Q k)).size part := fun part => by
    rw [tableSize_eq (stSent T Q.sent) (T.oracles.size + k) _ h2 part]
    show (K1.Msg.of T.codes (shapeAt Q k)).size part = _
    rw [hT]
  rw [sampleValue_single _ _ (T.oracles.size + k) l2, s2, s2]
  congr 1 <;>
    exact Finset.sum_congr rfl fun j _ => by
      rw [Johnson.Prover.Send.held_new w T.oracles.size Q V k hk]

/-- **The same answers.** -/
theorem answers_same (Q : K1.Par) (T T' : Statement) (hT : T.codes = Q.codes)
    (hT' : T'.codes = Q.codes) (V V' : Nat → Rows) (w w' : Words GE) (seeds : List (List E × E))
    (hW : ∀ k, k < Q.sent.size → (shapeAt Q k).answers ≠ 0 → ∀ part j,
      j < (K1.Msg.of Q.codes (shapeAt Q k)).size part →
      (V k).word (shapeAt Q k) part j = (V' k).word (shapeAt Q k) part j) :
    answers Q (stSent T Q.sent) T.oracles.size (Johnson.Prover.Send.held w T.oracles.size Q V)
        seeds =
      answers Q (stSent T' Q.sent) T'.oracles.size
        (Johnson.Prover.Send.held w' T'.oracles.size Q V') seeds := by
  unfold answers
  refine List.flatMap_congr fun k hk => ?_
  obtain ⟨hk1, hk2⟩ := List.mem_filter.1 hk
  have hk' : k < Q.sent.size := List.mem_range.1 hk1
  have ha : (shapeAt Q k).answers ≠ 0 := by simpa using hk2
  refine List.map_congr_left fun i _ => ?_
  rw [answer_sum Q T hT V w k hk', answer_sum Q T' hT' V' w' k hk']
  congr 2 <;>
    exact Finset.sum_congr rfl fun j hj => by rw [hW k hk' ha _ j (Finset.mem_range.1 hj)]

/-- The statement in front, at which the shared part computes: as many messages without a row as the
number first says. -/
def stFront (P : K1.Par) (first : Nat) : Statement :=
  { codes := P.codes, groups := #[]
    oracles := Array.replicate first { shape := { mainRows := 0, maskRows := 0, answers := 0 } } }

/-- stAt is that statement with the sending's messages received; it has first messages. -/
theorem stAt_front (P : K1.Par) (first : Nat) :
    stAt P first = stSent (stFront P first) P.sent ∧ (stFront P first).oracles.size = first :=
  ⟨rfl, Array.size_replicate ..⟩

/-- An answer is the words of a field's element: laid into the field and back, it is itself. -/
theorem answers_round (P : K1.Par) (S : Statement) (first : Nat) (w : Words GE)
    (seeds : List (List E × E)) :
    (answers P S first w seeds).map (fun y => ofE (toE y)) = answers P S first w seeds := by
  unfold answers
  rw [List.map_flatMap]
  refine List.flatMap_congr fun k _ => ?_
  rw [List.map_map]
  refine List.map_congr_left fun i _ => ?_
  show ofE (toE (ofE _)) = _
  rw [OnBytes.Slice.toE_ofE]

/-- **The term viaShownAt is answersAt.** -/
theorem via_shown (J : ProofFile.Honest.K1.SendJob Ask Unit) (own : Cs (dueR J.P J.ride)) (a : Ask)
    (h : List Fmt.Drawn) (x₀ : Fmt.Drawn) (sn : Seen) (vals : List Fmt.ItemValue) (T : Statement)
    (hT : T.codes = J.P.codes) (V : Nat → Rows) (w₀ : Words GE)
    (hW : ∀ k, k < J.P.sent.size → (shapeAt J.P k).answers ≠ 0 → ∀ part j,
      j < (K1.Msg.of J.P.codes (shapeAt J.P k)).size part →
      (J.rows own sn { input := a, heard := h ++ [x₀], own := () } 1 k).word
          (shapeAt J.P k) part j = (V k).word (shapeAt J.P k) part j) :
    viaShownAt J own a (h ++ [x₀]) sn =
      Desc.K14.Honest.answersAt J.P T { vals := vals, drawn := x₀ } w₀ V := by
  obtain ⟨e1, e2⟩ := stAt_front J.P J.first
  have key := answers_same J.P (stFront J.P J.first) T rfl hT
    (J.rows own sn { input := a, heard := h ++ [x₀], own := () } 1) V
    (fun _ _ _ => 0) w₀
    (K1.cutSeeds J.P.coordinates J.P.seeds (x₀.elems.map E.ofTriple)) hW
  rw [e2, ← e1] at key
  unfold viaShownAt viaSaidAt Desc.K14.Honest.answersAt
  rw [lately_one, List.map_map]
  show (answers J.P (stAt J.P J.first) J.first _
    (K1.cutSeeds J.P.coordinates J.P.seeds (x₀.elems.map E.ofTriple))).map
      (fun y => Fmt.ItemValue.answer (ofE (toE y))) = _
  rw [← key, ← answers_round J.P (stAt J.P J.first), List.map_map, List.map_map]
  refine List.map_congr_left fun y _ => ?_
  show Fmt.ItemValue.answer (ofE (toE (ofE (toE y)))) = Fmt.ItemValue.answer (ofE (toE y))
  rw [OnBytes.Slice.toE_ofE]

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.answer_sum
#print axioms ProofFile.Honest.K14.answers_same
#print axioms ProofFile.Honest.K14.stAt_front
#print axioms ProofFile.Honest.K14.answers_round
#print axioms ProofFile.Honest.K14.via_shown
#print axioms ProofFile.Honest.K14.stFront
