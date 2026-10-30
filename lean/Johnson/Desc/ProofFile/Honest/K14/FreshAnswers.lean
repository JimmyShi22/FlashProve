-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/FreshAnswers.lean: kind K14: THE OUT-OF-DOMAIN (OOD) ANSWERS OF
"send o_omega" (answersOf, Honest/K14/Sendings.lean, at jobOmega), AND THE LIBRARY's STATEMENT ON
o_sp's COINS (fresh_words, Johnson/Desc/K14/Honest/FreshAt.lean) CALLED AT THE PART's OWN SMALL
STATEMENT (localOf).

  size_main_zero, size_mask_one, local_sp, sp_word   o_sp in the small statement: no main table; a
                  mask table of as many entries as the row; entry j of the table is entry j of the
                  row
  sp_answer_read  **o_sp's answer, as the part computes it, read**: at any family of rows whose
                  message number 1 has a mask row that reads as (k, p) below n + 1: the left side of
                  o_sp's sample row at the words that hold that row in every table
  sp_law          **fresh_words, called**: over uniform (tail, pad, entries): (the row's symbols at
                  a set of at most r positions, that left side, the n entries) IS A UNIFORM TRIPLE
  omega_words_congr, omega_answer_congr   o_omega's tables, and so each of its answers, are made of
                  its main rows alone
  answers_congr   **all answers that the part sends are the same for two families of rows** whose
                  o_omega's main rows agree and whose o_sp's answers read the same
  omega_seeds     the place has a seed, and its number of coordinates is at least what o_sp's sample
                  row reads

What is assumed. The shape splits; o_omega has no mask row; SpShape; in sp_law: at most r positions,
a factor that does not read as 0, a point of enough coordinates.
What is not claimed. That an honest prover samples its coins uniformly. Nothing on any other value
that is shown. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K14.FreshRows
import Johnson.Desc.ProofFile.Honest.K14.SendingsAnswers
import Johnson.Desc.K14.Honest.FreshAt
import OnBytes.Flat.WireBlocks

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open OnBytes (E zeroE)
open OnBytes.Slice (GE rdE readE rdE_val toE)
open VerifiableInference.Desc (K1.Msg K1.Msg.of K1.sampleRow)
open VerifiableInference.Desc.K1 (tableSize_eq)
open Johnson.Prover.Link (symG)
open Desc.K14.Honest (SpShape maskRowOf maskTailOf spSymCode fresh_words)
open Prob

/-- A message without a main row has no main table. -/
theorem size_main_zero (m : K1.Msg) (hK : m.K = 0) : m.size .main = 0 := by
  simp [K1.Msg.size, K1.Msg.has, hK]

/-- The mask table of a message with one mask row. -/
theorem size_mask_one (m : K1.Msg) (hZ : m.Kzk = 1) : m.size .mask = 2 ^ m.logEllZk := by
  simp [K1.Msg.size, K1.Msg.has, K1.Msg.bits, K1.Msg.maskBits, hZ,
    VerifiableInference.Desc.K1.clog]

variable (A : SendPub)

/-- o_sp's entry in the part's own small statement. -/
theorem local_sp (hs : A.P.S.sharedSplitNeeded = true) :
    (localOf (jobOmega A).Q.codes (jobOmega A).Q.sent).oracles[1]? =
      some { shape := A.P.S.sharedSplit } := by
  have h := local_at (jobOmega A).Q.codes (jobOmega A).Q.sent 1 (by
    rw [omega_sent A hs]
    exact Nat.one_lt_two)
  rw [omega_shape1 A hs] at h
  exact h

/-- Entry j of o_sp's mask table is entry j of its row. -/
theorem sp_word {n : Nat} (hs : A.P.S.sharedSplitNeeded = true) (H : SpShape A.P.codes A.P.S n)
    (L : Nat → Laid) (j : Nat) : wordsOf (jobOmega A).Q.sent L 1 .mask j = (L 1).mask 0 j := by
  show (if j % 2 ^ OnBytes.ceilLog2 ((jobOmega A).Q.sent.getD 1 default).shape.maskRows <
      ((jobOmega A).Q.sent.getD 1 default).shape.maskRows then
    (L 1).mask (j % 2 ^ OnBytes.ceilLog2 ((jobOmega A).Q.sent.getD 1 default).shape.maskRows)
      (j / 2 ^ OnBytes.ceilLog2 ((jobOmega A).Q.sent.getD 1 default).shape.maskRows)
    else zeroE) = _
  have e : OnBytes.ceilLog2 1 = 0 := rfl
  rw [omega_shape1 A hs, H.oneRow, e, Nat.pow_zero, Nat.mod_one, Nat.div_one, if_pos Nat.one_pos]

/-- **o_sp's answer, as the part computes it, read.** -/
theorem sp_answer_read {n : Nat} (hs : A.P.S.sharedSplitNeeded = true)
    (H : SpShape A.P.codes A.P.S n) (L : Nat → Laid) (z : List E) (β : E) (p : GE)
    (k : Fin n → GE) (hrow : ∀ j, j < n + 1 → readE ((L 1).mask 0 j) = maskRowOf n p k j) :
    readE (Desc.K14.Law.valueE (localOf (jobOmega A).Q.codes (jobOmega A).Q.sent)
        (K1.sampleRow (K1.Msg.of (jobOmega A).Q.codes ((jobOmega A).Q.sent.getD 1 default).shape) 1
          z β 0 zeroE) (wordsOf (jobOmega A).Q.sent L)) =
      OnBytes.Means.value rdE (localOf (jobOmega A).Q.codes (jobOmega A).Q.sent)
        (K1.sampleRow (K1.Msg.of (jobOmega A).Q.codes A.P.S.sharedSplit) 1 z β 0 zeroE)
        fun _ _ j => maskRowOf n p k j := by
  have hX := local_sp A hs
  have l1 : 1 < (localOf (jobOmega A).Q.codes (jobOmega A).Q.sent).oracles.size :=
    (Array.getElem?_eq_some_iff.1 hX).1
  have s0 : OnBytes.Means.tableSize (localOf (jobOmega A).Q.codes (jobOmega A).Q.sent) 1 .main =
      0 := by
    rw [tableSize_eq _ 1 _ hX .main]
    exact size_main_zero _ H.noMain
  have s1 : OnBytes.Means.tableSize (localOf (jobOmega A).Q.codes (jobOmega A).Q.sent) 1 .mask =
      n + 1 := by
    rw [tableSize_eq _ 1 _ hX .mask]
    exact (size_mask_one _ H.oneRow).trans (H.power.trans H.length)
  rw [omega_shape1 A hs, ← rdE_val, Desc.K14.Law.val_valueE, sampleValue_single _ _ 1 l1,
    sampleValue_single _ _ 1 l1, s0, s1, Finset.range_zero, Finset.sum_empty, Finset.sum_empty]
  refine congrArg _ (Finset.sum_congr rfl fun j hj => ?_)
  show _ * rdE.val (wordsOf (jobOmega A).Q.sent L 1 .mask j) = _
  rw [sp_word A hs H, rdE_val, hrow j (Finset.mem_range.1 hj)]

/-- **fresh_words, called at the part's own small statement**: a uniform triple. -/
theorem sp_law {n : Nat} (hs : A.P.S.sharedSplitNeeded = true) (H : SpShape A.P.codes A.P.S n)
    (S : Finset (Fin (2 ^ (spSymCode A.P.codes A.P.S).a)))
    (hS : S.card ≤ (spSymCode A.P.codes A.P.S).r) (z : List E) (β : E)
    (hz : (K1.Msg.of A.P.codes A.P.S.sharedSplit).v ≤ z.length) (hβ : readE β ≠ 0) :
    (unif ((Fin (spSymCode A.P.codes A.P.S).r → GE) × GE × (Fin n → GE))).map (fun x =>
        ((fun j : S => symG (spSymCode A.P.codes A.P.S) j.1.val (maskRowOf n x.2.1 x.2.2)
            (maskTailOf (spSymCode A.P.codes A.P.S).r x.1)),
          OnBytes.Means.value rdE (localOf (jobOmega A).Q.codes (jobOmega A).Q.sent)
            (K1.sampleRow (K1.Msg.of (jobOmega A).Q.codes A.P.S.sharedSplit) 1 z β 0 zeroE)
            (fun _ _ j => maskRowOf n x.2.1 x.2.2 j), x.2.2)) =
      unif ((S → GE) × GE × (Fin n → GE)) := by
  have h := fresh_words (spSymCode A.P.codes A.P.S) n H.length H.positions S hS
    (localOf (jobOmega A).Q.codes (jobOmega A).Q.sent) 1 { shape := A.P.S.sharedSplit }
    (local_sp A hs) H.noMain H.oneRow H.oneAnswer (H.power.trans H.length) z β zeroE hz hβ
    (fun _ => 0) (fun x _ _ j => maskRowOf n x.2.1 x.2.2 j) (fun _ _ _ => rfl) id
  simp only [zero_add, id_eq] at h
  rw [PMF.map_id] at h
  exact h

/-- o_omega's tables are made of its main rows alone. -/
theorem omega_words_congr (hs : A.P.S.sharedSplitNeeded = true) (hz : A.P.S.omega.maskRows = 0)
    (L L' : Nat → Laid) (hm : ∀ r j, (L 0).main r j = (L' 0).main r j) (part : OnBytes.Part)
    (i : Nat) :
    wordsOf (jobOmega A).Q.sent L 0 part i = wordsOf (jobOmega A).Q.sent L' 0 part i := by
  cases part with
  | main =>
    show (if _ then (L 0).main _ _ else zeroE) = (if _ then (L' 0).main _ _ else zeroE)
    rw [hm]
  | mask =>
    show (if i % 2 ^ OnBytes.ceilLog2 ((jobOmega A).Q.sent.getD 0 default).shape.maskRows <
        ((jobOmega A).Q.sent.getD 0 default).shape.maskRows then _ else zeroE) =
      (if i % 2 ^ OnBytes.ceilLog2 ((jobOmega A).Q.sent.getD 0 default).shape.maskRows <
        ((jobOmega A).Q.sent.getD 0 default).shape.maskRows then _ else zeroE)
    rw [omega_shape0 A hs, hz, if_neg (Nat.not_lt_zero _), if_neg (Nat.not_lt_zero _)]

/-- Each of o_omega's answers, at every sample row of message number 0, is made of its main rows
alone. -/
theorem omega_answer_congr (hs : A.P.S.sharedSplitNeeded = true)
    (hz : A.P.S.omega.maskRows = 0) (L L' : Nat → Laid)
    (hm : ∀ r j, (L 0).main r j = (L' 0).main r j) (m : K1.Msg) (z : List E) (β : E) (i : Nat) :
    readE (Desc.K14.Law.valueE (localOf (jobOmega A).Q.codes (jobOmega A).Q.sent)
        (K1.sampleRow m 0 z β i zeroE) (wordsOf (jobOmega A).Q.sent L)) =
      readE (Desc.K14.Law.valueE (localOf (jobOmega A).Q.codes (jobOmega A).Q.sent)
        (K1.sampleRow m 0 z β i zeroE) (wordsOf (jobOmega A).Q.sent L')) := by
  have l0 : 0 < (localOf (jobOmega A).Q.codes (jobOmega A).Q.sent).oracles.size :=
    Nat.lt_trans Nat.zero_lt_one (Array.getElem?_eq_some_iff.1 (local_sp A hs)).1
  rw [← rdE_val, ← rdE_val, Desc.K14.Law.val_valueE, Desc.K14.Law.val_valueE,
    sampleValue_single _ _ 0 l0, sampleValue_single _ _ 0 l0]
  refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun j _ => ?_)
    (Finset.sum_congr rfl fun j _ => ?_)
  · show _ * rdE.val (wordsOf (jobOmega A).Q.sent L 0 .main j) =
      _ * rdE.val (wordsOf (jobOmega A).Q.sent L' 0 .main j)
    rw [omega_words_congr A hs hz L L' hm]
  · show _ * rdE.val (wordsOf (jobOmega A).Q.sent L 0 .mask j) =
      _ * rdE.val (wordsOf (jobOmega A).Q.sent L' 0 .mask j)
    rw [omega_words_congr A hs hz L L' hm]

/-- **All answers that the part sends, of two families of rows.** -/
theorem answers_congr {n : Nat} (hs : A.P.S.sharedSplitNeeded = true)
    (hz : A.P.S.omega.maskRows = 0) (H : SpShape A.P.codes A.P.S n) (L L' : Nat → Laid)
    (seeds : List (List E × E)) (hm : ∀ r j, (L 0).main r j = (L' 0).main r j)
    (hsp : readE (Desc.K14.Law.valueE (localOf (jobOmega A).Q.codes (jobOmega A).Q.sent)
        (K1.sampleRow (K1.Msg.of (jobOmega A).Q.codes ((jobOmega A).Q.sent.getD 1 default).shape) 1
          (seeds.getD 0 default).1 (seeds.getD 0 default).2 0 zeroE)
        (wordsOf (jobOmega A).Q.sent L)) =
      readE (Desc.K14.Law.valueE (localOf (jobOmega A).Q.codes (jobOmega A).Q.sent)
        (K1.sampleRow (K1.Msg.of (jobOmega A).Q.codes ((jobOmega A).Q.sent.getD 1 default).shape) 1
          (seeds.getD 0 default).1 (seeds.getD 0 default).2 0 zeroE)
        (wordsOf (jobOmega A).Q.sent L'))) :
    ((answersOf (jobOmega A).Q L seeds).map fun y => Said.answer (toE y.triple)) =
      (answersOf (jobOmega A).Q L' seeds).map fun y => Said.answer (toE y.triple) := by
  unfold answersOf
  rw [List.map_flatMap, List.map_flatMap]
  refine List.flatMap_congr fun k hk => ?_
  rw [List.map_map, List.map_map]
  refine List.map_congr_left fun i hi => ?_
  have hk2 : k < 2 := by
    have h1 := List.mem_range.1 (List.mem_filter.1 hk).1
    rw [omega_sent A hs] at h1
    exact h1
  refine congrArg Said.answer ?_
  obtain rfl | rfl : k = 0 ∨ k = 1 := by omega
  · exact omega_answer_congr A hs hz L L' hm _ _ _ i
  · rw [omega_shape1 A hs, H.oneAnswer] at hi
    obtain rfl : i = 0 := by
      have := List.mem_range.1 hi
      omega
    exact hsp

/-- **The place has a seed, and its number of coordinates is at least what o_sp's sample row
reads.** -/
theorem omega_seeds {n : Nat} (hs : A.P.S.sharedSplitNeeded = true)
    (H : SpShape A.P.codes A.P.S n) :
    (jobOmega A).Q.seeds ≠ 0 ∧
      (K1.Msg.of A.P.codes A.P.S.sharedSplit).v ≤ (jobOmega A).Q.coordinates := by
  have hm : A.P.S.sharedSplit ∈ (jobOmega A).Q.tuple := by
    unfold VerifiableInference.Desc.K1.Par.tuple
    rw [omega_sent A hs]
    refine List.mem_filter.2 ⟨?_, by rw [H.oneAnswer]; rfl⟩
    simp
  refine ⟨fun h0 => ?_,
    (OnBytes.Flat.foldl_max_ge (fun s => (K1.Msg.of (jobOmega A).Q.codes s).v) _ 0).2 _ hm⟩
  have h1 := (OnBytes.Flat.foldl_max_ge (fun s : OnBytes.OracleShape => s.answers) _ 0).2 _ hm
  have h2 : A.P.S.sharedSplit.answers ≤ (jobOmega A).Q.seeds := h1
  rw [H.oneAnswer, h0] at h2
  omega

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.size_main_zero
#print axioms ProofFile.Honest.K14.size_mask_one
#print axioms ProofFile.Honest.K14.local_sp
#print axioms ProofFile.Honest.K14.sp_word
#print axioms ProofFile.Honest.K14.sp_answer_read
#print axioms ProofFile.Honest.K14.sp_law
#print axioms ProofFile.Honest.K14.omega_words_congr
#print axioms ProofFile.Honest.K14.omega_answer_congr
#print axioms ProofFile.Honest.K14.answers_congr
#print axioms ProofFile.Honest.K14.omega_seeds
