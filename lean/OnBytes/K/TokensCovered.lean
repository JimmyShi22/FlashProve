-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/TokensCovered.lean: the prompt, the output and the further tokens of OnBytes/K/Tokens.lean
against what the program makes of a request (`Model.Head.coveredOf`). For proofs only.

  `covered_of`: where the program's reader of request and reply and `coveredOf` return: the field
    `tokv` is `tokensOf`; the field `hWin` at the covered positions r to e - 1 is `outputOf`; every
    token of the request and the reply are below the vocabulary's size.
  `reply_zero_of`: if e < T the reply is 0.
  `winOf_own`: at the caller's own reply, `Model.Head.winOf` returns the field `hWin` unturned.
What is not claimed. The check of the head's sub-proof does not read the field `hWin`: it reads
`winOf cov T yTok` (OnBytes/Model/HeadHeard.lean), in which, where the position T - 1 is covered,
the last entry is the token yTok that the prover names. The caller's reply comes in by another road:
it is an argument of `Proof.check`, and the first chain's block compares what it got with it
(OnBytes/Proof/File.lean). No law here ties yTok to the reply. So for the tokens of the request
itself the output is the list that the check reads; for the reply, where e = T, that is so only if
yTok is the reply, which is not shown here (OnBytes/K/ReplyRoot.lean has it,
for the run on which a yes rests).


-/
import OnBytes.K.TokensLaws
import OnBytes.Model.HeadHeard

set_option autoImplicit false

namespace OnBytes.K

open OnBytes OnBytes.Model OnBytes.Model.Verify

/-- The checked tokens of the covered positions, on lists. -/
theorem win_list (toks : List Nat) (T r e y : Nat) (hl : toks.length = T) (h1 : r < e)
    (h2 : e ≤ T) :
    (((List.range T).map fun t =>
        if (decide (r ≤ t) && decide (t < e)) = true then
          (if t + 1 < T then toks.getD (t + 1) 0 else y) else 0).drop r).take (e - r) =
      (toks.drop (r + 1)).take (e - r) ++ (if e = T then [y] else []) := by
  apply List.ext_getElem
  · simp only [List.length_take, List.length_drop, List.length_map, List.length_range,
      List.length_append, hl]
    split
    · simp only [List.length_singleton]
      omega
    · simp only [List.length_nil]
      omega
  · intro i hi1 hi2
    simp only [List.length_take, List.length_drop, List.length_map, List.length_range] at hi1
    have hi : i < e - r := by omega
    simp only [List.getElem_take, List.getElem_drop, List.getElem_map, List.getElem_range]
    have hon : (decide (r ≤ r + i) && decide (r + i < e)) = true := by
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      omega
    rw [if_pos hon]
    by_cases hlt : r + i + 1 < T
    · rw [if_pos hlt]
      have hlen : i < ((toks.drop (r + 1)).take (e - r)).length := by
        simp only [List.length_take, List.length_drop, hl]
        omega
      rw [List.getElem_append_left hlen, List.getElem_take, List.getElem_drop,
        List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
      congr 1
      omega
    · rw [if_neg hlt]
      have heT : e = T := by omega
      have hlen : ((toks.drop (r + 1)).take (e - r)).length ≤ i := by
        simp only [List.length_take, List.length_drop, hl]
        omega
      rw [List.getElem_append_right hlen]
      simp [heT]

/-- If the range ends before the window's end, the reply is 0. -/
theorem reply_zero_of {x : UserStm} {T : Nat} {so : Head.StOwn}
    (h : Head.stFromCall (words32 x.request) (words32 x.y) T = .ok so) :
    eOf x < T → yOf x = 0 := by
  obtain ⟨hT, _, _, _, _, _, _⟩ := read_of h
  unfold Head.stFromCall at h
  obtain ⟨_, _, h⟩ := Params.exc_bind h
  obtain ⟨_, _, h⟩ := Params.exc_bind h
  dsimp only at h
  obtain ⟨_, h3, _⟩ := Params.exc_bind h
  intro he
  unfold eOf at he
  rw [hT] at he
  unfold yOf
  unfold Head.needed at h3
  split at h3
  · rename_i hb
    simp only [Bool.not_eq_true', Bool.or_eq_false_iff, Bool.and_eq_false_iff,
      decide_eq_false_iff_not, bne_eq_false_iff_eq] at hb
    rcases hb.2 with hc | hc
    · exact absurd he hc
    · exact hc
  · cases h3

/-- The fields of what `coveredOf` returns, against the three lists. In words: the head of this
file. -/
theorem covered_of {x : UserStm} {T V : Nat} {so : Head.StOwn} {cov : Head.Covered}
    (h : Head.stFromCall (words32 x.request) (words32 x.y) T = .ok so)
    (hc : Head.coveredOf so T V = .ok cov) :
    cov.tokv.toList = tokensOf x ∧
      (cov.hWin.toList.drop so.r).take (so.e - so.r) = outputOf x ∧
      (∀ t ∈ tokensOf x, t < V) ∧ yOf x < V := by
  obtain ⟨hT, hl, e1, e2, e3, h1, h2⟩ := read_of h
  have hreq : so.req = words32 x.request := by
    unfold Head.stFromCall at h
    obtain ⟨_, _, h⟩ := Params.exc_bind h
    obtain ⟨_, _, h⟩ := Params.exc_bind h
    dsimp only at h
    obtain ⟨_, _, h⟩ := Params.exc_bind h
    cases h
    rfl
  unfold Head.coveredOf at hc
  obtain ⟨_, c1, hc⟩ := Params.exc_bind hc
  obtain ⟨_, _, hc⟩ := Params.exc_bind hc
  dsimp only at hc
  obtain ⟨_, c3, hc⟩ := Params.exc_bind hc
  obtain ⟨_, _, hc⟩ := Params.exc_bind hc
  cases hc
  have htok : ((so.req.extract 0 T).map (·.toNat)).toList = tokensOf x := by
    unfold tokensOf
    rw [hreq, hT]
    simp
  have hy : yOf x < V := by
    unfold Head.needed at c1
    split at c1
    · rename_i hb
      rw [← e3]
      exact of_decide_eq_true hb
    · cases c1
  have hall : ∀ t ∈ tokensOf x, t < V := by
    unfold Head.needed at c3
    split at c3
    · rename_i hb
      intro t ht
      rw [← htok] at ht
      have := (Array.all_eq_true'.1 hb) t (Array.mem_toList_iff.1 ht)
      exact of_decide_eq_true this
    · cases c3
  refine ⟨htok, ?_, hall, hy⟩
  have hr' : (so.req.getD T 0).toNat = rOf x := by
    unfold rOf
    rw [hreq, hT]
  have he' : (so.req.getD (T + 1) 0).toNat = eOf x := by
    unfold eOf
    rw [hreq, hT]
  show ((((Array.range T).map fun t =>
      if (decide ((so.req.getD T 0).toNat ≤ t) && decide (t < (so.req.getD (T + 1) 0).toNat)) = true
      then (if t + 1 < T then ((so.req.extract 0 T).map (·.toNat)).getD (t + 1) 0 else so.y)
      else 0).toList.drop so.r).take (so.e - so.r)) = outputOf x
  rw [hr', he', e1, e2, e3]
  have hg : ∀ k, ((so.req.extract 0 T).map (·.toNat)).getD k 0 = (tokensOf x).getD k 0 := by
    intro k
    rw [Array.getD_eq_getD_getElem?, ← Array.getElem?_toList, htok, List.getD_eq_getElem?_getD]
  simp only [hg, Array.toList_map, Array.toList_range]
  unfold outputOf
  rw [hT]
  exact win_list (tokensOf x) T (rOf x) (eOf x) (yOf x) hl h1 h2

/-- At the caller's own reply `winOf` returns the field `hWin` unturned. -/
theorem winOf_own {so : Head.StOwn} {T V : Nat} {cov : Head.Covered}
    (hc : Head.coveredOf so T V = .ok cov) : Head.winOf cov T so.y = cov.hWin := by
  unfold Head.coveredOf at hc
  obtain ⟨_, _, hc⟩ := Params.exc_bind hc
  obtain ⟨_, _, hc⟩ := Params.exc_bind hc
  dsimp only at hc
  obtain ⟨_, _, hc⟩ := Params.exc_bind hc
  obtain ⟨_, _, hc⟩ := Params.exc_bind hc
  cases hc
  have hset : ∀ (A : Array Nat) (k y : Nat), (∀ h : k < A.size, A[k] = y) →
      A.setIfInBounds k y = A := by
    intro A k y hA
    apply Array.ext
    · simp
    · intro i h1 h2
      rw [Array.getElem_setIfInBounds]
      split
      · rename_i hk
        subst hk
        exact (hA h2).symm
      · rfl
  unfold Head.winOf
  dsimp only
  split
  · rename_i hon
    apply hset
    intro hk
    simp only [Array.size_map, Array.size_range] at hk
    have hon' : (decide ((so.req.getD T 0).toNat ≤ T - 1) &&
        decide (T - 1 < (so.req.getD (T + 1) 0).toNat)) = true := by
      simpa [Array.getD_eq_getD_getElem?, hk] using hon
    simp only [Array.getElem_map, Array.getElem_range]
    rw [if_pos hon', if_neg (by omega)]
  · rfl

end OnBytes.K
