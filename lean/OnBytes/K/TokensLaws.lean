-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/TokensLaws.lean: the prompt, the output and the further tokens of OnBytes/K/Tokens.lean
against the program's own reader of request and reply. For proofs only.

  `read_of`: where `Model.Head.stFromCall` returns, its r, e and y are `rOf`, `eOf` and `yOf`, the
    request has T tokens, and r < e ≤ T.
  `lengths_of`, `split_of`: there the prompt has r + 1 tokens and the output e - r; prompt, output
    and further tokens, laid end to end, are the request's T tokens, with the reply behind them if e
    = T.
What is not claimed: nothing on a vocabulary, on an instance of a model, or on what a yes says of
these tokens. Elsewhere: by `covered_of` (OnBytes/K/TokensCovered.lean), where
`Model.Head.coveredOf` returns at a number V, every token and the reply are below V; V is a letter.

-/
import OnBytes.K.Tokens
import OnBytes.Params.ConfigureLaws

set_option autoImplicit false

namespace OnBytes.K

open OnBytes OnBytes.Model OnBytes.Model.Verify

/-- Where the program's reader of request and reply returns, its numbers are these. -/
theorem read_of {x : UserStm} {T : Nat} {so : Head.StOwn}
    (h : Head.stFromCall (words32 x.request) (words32 x.y) T = .ok so) :
    windowOf x = T ∧ (tokensOf x).length = T ∧ so.r = rOf x ∧ so.e = eOf x ∧ so.y = yOf x ∧
      rOf x < eOf x ∧ eOf x ≤ T := by
  unfold Head.stFromCall at h
  obtain ⟨_, _, h⟩ := Params.exc_bind h
  obtain ⟨_, h2, h⟩ := Params.exc_bind h
  dsimp only at h
  obtain ⟨_, h3, h⟩ := Params.exc_bind h
  cases h
  have s2 : (words32 x.request).size = T + 2 := by
    unfold Head.needed at h2
    split at h2
    · rename_i hb
      simp only [Bool.not_eq_true', Bool.or_eq_false_iff, bne_eq_false_iff_eq] at hb
      exact hb.1
    · cases h2
  have hT : windowOf x = T := by
    unfold windowOf
    omega
  have s3 : ((words32 x.request).getD T 0).toNat < ((words32 x.request).getD (T + 1) 0).toNat ∧
      ((words32 x.request).getD (T + 1) 0).toNat ≤ T := by
    unfold Head.needed at h3
    split at h3
    · rename_i hb
      simp only [Bool.not_eq_true', Bool.or_eq_false_iff, decide_eq_false_iff_not] at hb
      omega
    · cases h3
  refine ⟨hT, ?_, ?_, ?_, rfl, ?_, ?_⟩
  · unfold tokensOf
    rw [List.length_map, List.length_take, Array.length_toList, hT, s2]
    omega
  · unfold rOf
    rw [hT]
  · unfold eOf
    rw [hT]
  · unfold rOf eOf
    rw [hT]
    exact s3.1
  · unfold eOf
    rw [hT]
    exact s3.2

/-- The two lengths. -/
theorem lengths_of {x : UserStm} {T : Nat} {so : Head.StOwn}
    (h : Head.stFromCall (words32 x.request) (words32 x.y) T = .ok so) :
    (promptOf x).length = so.r + 1 ∧ (outputOf x).length = so.e - so.r := by
  obtain ⟨hT, hl, e1, e2, _, h1, h2⟩ := read_of h
  rw [e1, e2]
  constructor
  · unfold promptOf
    rw [List.length_take, hl]
    omega
  · unfold outputOf
    rw [List.length_append, List.length_take, List.length_drop, hl, hT]
    split
    · rw [List.length_singleton]
      omega
    · rw [List.length_nil]
      omega

/-- Prompt, output and further tokens, laid end to end. -/
theorem split_of {x : UserStm} {T : Nat} {so : Head.StOwn}
    (h : Head.stFromCall (words32 x.request) (words32 x.y) T = .ok so) :
    promptOf x ++ outputOf x ++ auxOf x =
      tokensOf x ++ (if so.e = T then [so.y] else []) := by
  obtain ⟨hT, hl, _, e2, e3, h1, h2⟩ := read_of h
  rw [e2, e3]
  unfold promptOf outputOf auxOf
  rw [hT]
  by_cases he : eOf x = T
  · rw [if_pos he]
    have d1 : (tokensOf x).drop (eOf x + 1) = [] := List.drop_eq_nil_of_le (by omega)
    have d2 : ((tokensOf x).drop (rOf x + 1)).take (eOf x - rOf x) =
        (tokensOf x).drop (rOf x + 1) := List.take_of_length_le (by rw [List.length_drop]; omega)
    rw [d1, d2, List.append_nil, ← List.append_assoc, List.take_append_drop]
  · rw [if_neg he, List.append_nil, List.append_nil]
    have d3 : (tokensOf x).drop (eOf x + 1) =
        ((tokensOf x).drop (rOf x + 1)).drop (eOf x - rOf x) := by
      rw [List.drop_drop]
      congr 1
      omega
    rw [d3, List.append_assoc, List.take_append_drop, List.take_append_drop]

end OnBytes.K

#print axioms OnBytes.K.read_of
#print axioms OnBytes.K.lengths_of
#print axioms OnBytes.K.split_of
