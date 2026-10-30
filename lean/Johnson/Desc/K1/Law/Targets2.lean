-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/Targets2.lean: which of the answers received are the targets of which message's
sample rows: message number k of a place takes the answers from the number of all answers of the
messages in front of it on, as many as it has.

Main names: offset; outs_get; targets_indexed; offset_count (where no message has more than one
answer the offset is the number of the sampled messages in front); offset_rider (with the answers
1, 1, 1, 0, 1 the last message's answer is item 3 of the round).

What is not claimed. Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.K1.Law.Targets

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain

variable {L : Type}

/-- The number of all answers of the first k of a list of shapes. -/
def offsetOf (l : List OracleShape) (k : Nat) : Nat := ((l.take k).map fun s => s.answers).sum

/-- The number of all answers of the place's messages in front of number k. -/
def offset (P : Par) (k : Nat) : Nat := offsetOf (shapesOf P) k

/-- Message number k behind the sending is written with the answers from its offset on. -/
theorem outs_get (codes : Codes) (seeds : List (List E × E)) :
    ∀ (l : List OracleShape) (o : Nat) (ys : List E) (k : Nat) (hk : k < l.length),
      (outs codes seeds o l ys)[k]? =
        some (wr codes seeds (o + k) l[k] (ys.drop (offsetOf l k)))
  | [], _, _, _, hk => absurd hk (Nat.not_lt_zero _)
  | s :: l, o, ys, 0, _ => by simp [outs, offsetOf]
  | s :: l, o, ys, k + 1, hk => by
    have ih := outs_get codes seeds l (o + 1) (ys.drop s.answers) k (Nat.lt_of_succ_lt_succ hk)
    simp only [outs, List.getElem?_cons_succ, List.getElem_cons_succ]
    rw [ih, List.drop_drop]
    have e1 : o + 1 + k = o + (k + 1) := by omega
    have e2 : s.answers + offsetOf l k = offsetOf (s :: l) (k + 1) := by simp [offsetOf]
    rw [e1, e2]

/-- **Behind a yes: the targets of message number k's sample rows are the answers of the second
round from the message's offset on, as many as the message has.** -/
theorem targets_indexed (P : Par) (owed : Option Nat) (d d' : DState L) (r₁ r₂ : Fmt.RoundView)
    (ids : Array Nat) (hyes : decideSend P owed d [r₁, r₂] = .ok (ids, d'))
    (k : Fin (shapesOf P).length) :
    ∃ x, d'.st.oracles[d.st.oracles.size + k.val]? = some x ∧
      x.sampleRows.toList.map (fun r => r.target) =
        ((answersIn r₂).drop (offset P k.val)).take (shapesOf P)[k.val].answers := by
  obtain ⟨_, _, rfl⟩ := (decideSend_iff P owed d d' r₁ r₂ ids).1 hyes
  have hget := outs_get P.codes (seedsOf P r₁) (shapesOf P) d.st.oracles.size (answersIn r₂) k.val
    k.isLt
  have hx : (behind P d (seedsOf P r₁) (answersIn r₂)).st.oracles[d.st.oracles.size + k.val]? =
      some (wr P.codes (seedsOf P r₁) (d.st.oracles.size + k.val) (shapesOf P)[k.val]
        ((answersIn r₂).drop (offset P k.val))) := by
    show (d.st.oracles.toList ++ outs P.codes (seedsOf P r₁) d.st.oracles.size (shapesOf P)
      (answersIn r₂)).toArray[d.st.oracles.size + k.val]? = _
    rw [List.getElem?_toArray, List.getElem?_append_right (by simp)]
    simpa using hget
  refine ⟨_, hx, ?_⟩
  by_cases h0 : (shapesOf P)[k.val].answers = 0
  · simp [wr, h0, fresh]
  · have hw : (wr P.codes (seedsOf P r₁) (d.st.oracles.size + k.val) (shapesOf P)[k.val]
        ((answersIn r₂).drop (offset P k.val))).sampleRows =
        rowsOf P.codes (seedsOf P r₁) (d.st.oracles.size + k.val) (shapesOf P)[k.val]
          ((answersIn r₂).drop (offset P k.val)) := by simp [wr, h0]
    rw [hw]
    refine rowsOf_targets _ _ _ _ _ ?_
    rw [show (seedsOf P r₁).length = P.seeds from cutSeeds_length _ _ _]
    exact msgAt_answers_le P k

/-- Where no message has more than one answer, the offset is the number of the sampled messages in
front. -/
theorem offset_count : ∀ (l : List OracleShape) (k : Nat), (∀ s ∈ l, s.answers ≤ 1) →
    offsetOf l k = ((l.take k).filter fun s => s.answers != 0).length
  | [], k, _ => by simp [offsetOf]
  | _ :: _, 0, _ => by simp [offsetOf]
  | s :: l, k + 1, h => by
    have ih := offset_count l k fun t ht => h t (List.mem_cons_of_mem _ ht)
    have hs := h s List.mem_cons_self
    have e : offsetOf (s :: l) (k + 1) = s.answers + offsetOf l k := by simp [offsetOf]
    rw [e, ih, List.take_succ_cons, List.filter_cons]
    by_cases h0 : s.answers = 0
    · simp [h0]
    · have h1 : s.answers = 1 := by omega
      simp [h1, Nat.add_comm]

/-- A try with a message that is not sampled among the sampled ones: with the answers 1, 1, 1, 0, 1
the last message's answer is item 3 of the round, not item 4. -/
theorem offset_rider (l : List OracleShape) (h : l.map (fun s => s.answers) = [1, 1, 1, 0, 1]) :
    offsetOf l 4 = 3 := by
  unfold offsetOf
  rw [List.map_take, h]
  rfl

end VerifiableInference.Desc.K1
