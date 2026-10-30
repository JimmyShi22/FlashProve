-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/SendingsAnswers.lean: the out-of-domain (OOD) answers that a
sending's part makes with code (answersOf, Honest/K14/Sendings.lean) READ as the shared sending's
answers (Johnson/Prover/Send/Core.lean) at rows that hold what the coded tables read as.

  sampleK, coef_self, coef_ne   a sample row's coefficient on an entry of its own message, which
                  does not hang on the message's number; on any other message it is 0
  sampleValue_single   so a sample row's left side is a sum over its own message's two tables
  local_at        the part's own small statement has message number k's shape at the number k
  answer_read     **one answer**: the coded value, read, is the left side of the same sample row at
                  the statement that has received the messages, at the shared sending's held words
  answersOf_read  all answers, in order
  shown_read      what the part shows in its second round is answersAt
                  (Johnson/Desc/K14/Honest/SendMoves.lean)

What is assumed. hW: at each message of the sending, at each index below the table's size, the coded
table reads as the rows' table. The statement in front has the sending's codes.
What is not claimed. That hW holds (Honest/K14/SendingsTables.lean has the tables). Nothing on a
verifier's decision, on soundness or on hiding.
-/
import Johnson.Desc.ProofFile.Honest.K14.SendingsPlay
import Johnson.Desc.K14.Honest.SendMoves
import Johnson.Desc.K1.Law.SaysTie
import Johnson.Prover.Send.Held

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open OnBytes (E zeroE Statement Codes OracleNotice)
open OnBytes.Means (Words)
open OnBytes.Slice (GE rdE readE ofE toE stSent rdE_val)
open VerifiableInference.Desc (K1.Par K1.Msg K1.Msg.of K1.sampleRow K1.cutSeeds)
open VerifiableInference.Desc.K1 (coefAt_sampleRow tableSize_eq padW)
open OnBytes.Slice (coefAt)
open Johnson.Prover.Send (Rows shapeAt answers)

/-- A sample row's coefficient on the entry j of a table of its own message. -/
noncomputable def sampleK (m : K1.Msg) (z : List E) (β : E) (i : Nat) (part : OnBytes.Part)
    (j : Nat) : GE :=
  (if m.has part then readE ((m.ten z part).entry j) else 0) +
    (m.pads.map fun x => if m.padPart == part && x.2.1 == j then
      padW β i x - readE ((m.ten z m.padPart).entry x.2.1) else 0).sum

theorem coef_self (m : K1.Msg) (o : Nat) (z : List E) (β : E) (i : Nat) (y : E)
    (part : OnBytes.Part) (j : Nat) :
    coefAt (K1.sampleRow m o z β i y) o part j = sampleK m z β i part j := by
  rw [coefAt_sampleRow]
  simp [sampleK]

theorem coef_ne (m : K1.Msg) (o o' : Nat) (z : List E) (β : E) (i : Nat) (y : E)
    (part : OnBytes.Part) (j : Nat) (h : o ≠ o') :
    coefAt (K1.sampleRow m o z β i y) o' part j = 0 := by
  rw [coefAt_sampleRow]
  have e : (o == o') = false := beq_eq_false_iff_ne.2 h
  simp [e]

/-- A sample row's left side is a sum over its own message's two tables. -/
theorem sampleValue_single (S : Statement) (m : K1.Msg) (o : Nat) (ho : o < S.oracles.size)
    (z : List E) (β : E) (i : Nat) (y : E) (w : Words GE) :
    OnBytes.Means.value rdE S (K1.sampleRow m o z β i y) w =
      (∑ j ∈ Finset.range (OnBytes.Means.tableSize S o .main),
        sampleK m z β i .main j * w o .main j) +
      ∑ j ∈ Finset.range (OnBytes.Means.tableSize S o .mask),
        sampleK m z β i .mask j * w o .mask j := by
  have hT : ∀ part, OnBytes.Means.onTable rdE S (K1.sampleRow m o z β i y) w o part =
      ∑ j ∈ Finset.range (OnBytes.Means.tableSize S o part),
        sampleK m z β i part j * w o part j := fun part => by
    unfold OnBytes.Means.onTable
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← coef_self m o z β i y part j]
    rfl
  unfold OnBytes.Means.value
  rw [Finset.sum_eq_single o, hT, hT]
  · intro o' _ hne
    have hz0 : ∀ part, OnBytes.Means.onTable rdE S (K1.sampleRow m o z β i y) w o' part = 0 :=
      fun part => by
        unfold OnBytes.Means.onTable
        refine Finset.sum_eq_zero fun j _ => ?_
        have := coef_ne m o o' z β i y part j (Ne.symm hne)
        unfold coefAt at this
        rw [rdE_val, this, zero_mul]
    rw [hz0, hz0, add_zero]
  · intro h
    exact absurd (Finset.mem_range.2 ho) h

/-- The part's own small statement has message number k's shape at the number k. -/
theorem local_at (codes : Codes) (sent : Array OracleNotice) (k : Nat) (hk : k < sent.size) :
    (localOf codes sent).oracles[k]? = some { shape := (sent.getD k default).shape } := by
  show (sent.map fun n => ({ shape := n.shape } : OnBytes.Oracle))[k]? = _
  rw [Array.getElem?_map, Array.getElem?_eq_getElem hk, Array.getD_eq_getD_getElem?,
    Array.getElem?_eq_getElem hk]
  rfl

/-- The statement that has received a sending's messages has message number k's shape at its
number. -/
theorem stSent_at (Q : K1.Par) (T : Statement) (k : Nat) (hk : k < Q.sent.size) :
    (stSent T Q.sent).oracles[T.oracles.size + k]? = some { shape := shapeAt Q k } := by
  rw [OnBytes.Slice.stSent_new, Array.getElem?_eq_getElem hk]
  unfold shapeAt
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hk]
  rfl

/-- **One answer, read.** -/
theorem answer_read (Q : K1.Par) (T : Statement) (hT : T.codes = Q.codes) (L : Nat → Laid)
    (V : Nat → Rows) (w₀ : Words GE) (k : Nat) (hk : k < Q.sent.size) (z : List E) (β : E)
    (i : Nat)
    (hW : ∀ part j, j < (K1.Msg.of Q.codes (shapeAt Q k)).size part →
      rdE.val (wordsOf Q.sent L k part j) = (V k).word (shapeAt Q k) part j) :
    rdE.val (Desc.K14.Law.valueE (localOf Q.codes Q.sent)
        (K1.sampleRow (K1.Msg.of Q.codes (Q.sent.getD k default).shape) k z β i zeroE)
        (wordsOf Q.sent L)) =
      OnBytes.Means.value rdE (stSent T Q.sent)
        (K1.sampleRow (K1.Msg.of Q.codes (shapeAt Q k)) (T.oracles.size + k) z β i zeroE)
        (Johnson.Prover.Send.held w₀ T.oracles.size Q V) := by
  have h1 := local_at Q.codes Q.sent k hk
  have h2 := stSent_at Q T k hk
  have l1 : k < (localOf Q.codes Q.sent).oracles.size := by
    by_contra h
    rw [Array.getElem?_eq_none (Nat.le_of_not_lt h)] at h1
    cases h1
  have l2 : T.oracles.size + k < (stSent T Q.sent).oracles.size := by
    by_contra h
    rw [Array.getElem?_eq_none (Nat.le_of_not_lt h)] at h2
    cases h2
  have s1 : ∀ part, OnBytes.Means.tableSize (localOf Q.codes Q.sent) k part =
      (K1.Msg.of Q.codes (shapeAt Q k)).size part := fun part =>
    tableSize_eq (localOf Q.codes Q.sent) k _ h1 part
  have s2 : ∀ part, OnBytes.Means.tableSize (stSent T Q.sent) (T.oracles.size + k) part =
      (K1.Msg.of Q.codes (shapeAt Q k)).size part := fun part => by
    rw [tableSize_eq (stSent T Q.sent) (T.oracles.size + k) _ h2 part]
    show (K1.Msg.of T.codes (shapeAt Q k)).size part = _
    rw [hT]
  rw [Desc.K14.Law.val_valueE, sampleValue_single _ _ k l1,
    sampleValue_single _ _ (T.oracles.size + k) l2, s1, s1, s2, s2]
  have hw : ∀ part j, j < (K1.Msg.of Q.codes (shapeAt Q k)).size part →
      Desc.K14.Law.wordsOf rdE (wordsOf Q.sent L) k part j =
        Johnson.Prover.Send.held w₀ T.oracles.size Q V (T.oracles.size + k) part j :=
      fun part j hj => by
    rw [Johnson.Prover.Send.held_new w₀ T.oracles.size Q V k hk]
    exact hW part j hj
  congr 1 <;>
    exact Finset.sum_congr rfl fun j hj => by rw [hw _ j (Finset.mem_range.1 hj)]; rfl

/-- **All answers, read**, in order. -/
theorem answersOf_read (Q : K1.Par) (T : Statement) (hT : T.codes = Q.codes) (L : Nat → Laid)
    (V : Nat → Rows) (w₀ : Words GE) (seeds : List (List E × E))
    (hW : ∀ k, k < Q.sent.size → ∀ part j, j < (K1.Msg.of Q.codes (shapeAt Q k)).size part →
      rdE.val (wordsOf Q.sent L k part j) = (V k).word (shapeAt Q k) part j) :
    (answersOf Q L seeds).map (fun y => ofE (rdE.val y)) =
      answers Q (stSent T Q.sent) T.oracles.size
        (Johnson.Prover.Send.held w₀ T.oracles.size Q V) seeds := by
  unfold answersOf answers
  rw [List.map_flatMap]
  refine List.flatMap_congr fun k hk => ?_
  have hk' : k < Q.sent.size := List.mem_range.1 (List.mem_filter.1 hk).1
  rw [List.map_map]
  refine List.map_congr_left fun i _ => ?_
  show ofE (rdE.val _) = _
  rw [answer_read Q T hT L V w₀ k hk' _ _ i (hW k hk')]

/-- **What the part shows in its second round is answersAt.** vals: whatever the first round showed.
-/
theorem shown_read (J : SendJob) (own : Cs (sendingPart J).takes) (a : Ask) (h : List Fmt.Drawn)
    (x₀ : Fmt.Drawn) (vals : List Fmt.ItemValue) (T : Statement) (hT : T.codes = J.Q.codes)
    (V : Nat → Rows) (w₀ : Words GE)
    (hW : ∀ k, k < J.Q.sent.size → ∀ part j,
      j < (K1.Msg.of J.Q.codes (shapeAt J.Q k)).size part →
      rdE.val (wordsOf J.Q.sent
          (J.rows { input := a, heard := h ++ [x₀], own := () } (coinsE own).toArray) k part j) =
        (V k).word (shapeAt J.Q k) part j) :
    sendShownAt J own a (h ++ [x₀]) =
      Desc.K14.Honest.answersAt J.Q T { vals := vals, drawn := x₀ } w₀ V := by
  unfold sendShownAt Desc.K14.Honest.answersAt
  have hl : ((⟨a, h ++ [x₀], ()⟩ : State Ask Unit).lately 1) = [x₀] := by
    unfold State.lately
    show (h ++ [x₀]).drop ((h ++ [x₀]).length - 1) = [x₀]
    rw [List.length_append, List.length_singleton, Nat.add_sub_cancel, List.drop_left]
  have he : elems [x₀] = x₀.elems.map E.ofTriple := by
    show x₀.elems.map E.ofTriple ++ [] = _
    rw [List.append_nil]
  rw [hl, he, ← answersOf_read J.Q T hT _ V w₀ _ hW, List.map_map, List.map_map]
  rfl

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.coef_self
#print axioms ProofFile.Honest.K14.coef_ne
#print axioms ProofFile.Honest.K14.sampleValue_single
#print axioms ProofFile.Honest.K14.local_at
#print axioms ProofFile.Honest.K14.stSent_at
#print axioms ProofFile.Honest.K14.answer_read
#print axioms ProofFile.Honest.K14.answersOf_read
#print axioms ProofFile.Honest.K14.shown_read
