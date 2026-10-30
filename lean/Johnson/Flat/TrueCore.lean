-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Flat/TrueCore.lean: at any model sizes P: what a built instance's tokens are, and that a
matrix of field elements is said by at most one matrix of digits.

Four theorems, for the claim "the request is true by a function that gives the next token" (TrueBy,
Johnson/Flat/ClaimsAny.lean), which serves where the library has no relaxed relation: at other sizes
than the reference's.
  tokensBelow_some: the tokens that tokensBelow returns are the given numbers.
  requestAt_some: where requestAt builds: the lengths, r, e, and the tokens at the positions of the
    prompt and the output. The statement and the proof are those of IntegerModel.requestOf_some
    (VerifiableInference/RequestOfTokens.lean) with P in the place of the reference sizes.
  built_positions: if x is built from a prompt with output tokens, and at every covered position t
    the function next gives the checked token after the window's tokens up to t, then each output
    token is what next gives after the prompt and the output tokens before it.
  says_unique: two integer matrices with entries in [-2^7, 2^7) inside the shape that say one matrix
    of field elements are one.

Limits: nothing on a protocol, and nothing on which function next is.

-/
import Johnson.Flat.InstanceLaws
import Johnson.Flat.LedgerClaim

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles.Flat

open Inst.Model OnBytes.Flat

/-- The tokens that tokensBelow returns are the given numbers. -/
theorem tokensBelow_some {V : ℕ} : ∀ {l : List Token} {l' : List (Fin V)},
    tokensBelow V l = some l' → l'.map (·.val) = l
  | [], l', h => by
    cases h
    rfl
  | t :: rest, l', h => by
    unfold tokensBelow at h
    split at h
    · rename_i ht
      cases hr : tokensBelow V rest with
      | none =>
        rw [hr] at h
        cases h
      | some r =>
        rw [hr] at h
        cases h
        show t :: r.map (·.val) = t :: rest
        rw [tokensBelow_some hr]
    · cases h

/-- Where an instance is built: the lengths, r, e, and its tokens at the positions of the prompt and
the output. -/
theorem requestAt_some {P : Params} {hV : 0 < P.V} {prompt output padding : List (Fin P.V)}
    {x : Instance' P} (h : requestAt P hV prompt output padding = some x) :
    (0 < prompt.length ∧ 0 < output.length ∧ prompt.length + output.length ≤ P.T + 1)
    ∧ x.r = prompt.length - 1 ∧ x.e = prompt.length - 1 + output.length
    ∧ ∀ j, j < prompt.length + output.length →
      x.tok j = ((prompt ++ output).getD j ⟨0, hV⟩).val := by
  unfold requestAt at h
  split at h
  · rename_i hc
    injection h with h
    subst h
    refine ⟨hc, rfl, rfl, fun j hj => ?_⟩
    unfold Instance.tok
    split
    · show ((prompt ++ output ++ padding).getD j ⟨0, hV⟩).val =
        ((prompt ++ output).getD j ⟨0, hV⟩).val
      have hl : j < (prompt ++ output).length := by rw [List.length_append]; exact hj
      rw [IntegerModel.getD_app_left (prompt ++ output) padding ⟨0, hV⟩ j hl,
        List.getD_eq_getElem _ _ hl]
    · rename_i hjT
      have e : j = P.T := by have h3 := hc.2.2; omega
      rw [e]
  · cases h

/-- **Each output token of a built instance is what next gives**, if next gives the checked token at
every covered position. -/
theorem built_positions {P : Params} {hV : 0 < P.V} {x' : List Token × List Token}
    {b : List Token} {x : Instance' P} (h : buildAt P hV x' b = some x)
    (next : List Token → Option Token)
    (hT : ∀ t, x.r ≤ t → t < x.e → next ((List.range (t + 1)).map x.tok) = some (x.w t)) :
    ∀ position (hp : position < x'.2.length),
      next (x'.1 ++ x'.2.take position) = some x'.2[position] := by
  unfold buildAt at h
  split at h
  swap
  · cases h
  rename_i prompt output pad e1 e2 _
  obtain ⟨⟨h1, _, _⟩, hr, he, ht⟩ := requestAt_some h
  have m1 : prompt.map (·.val) = x'.1 := tokensBelow_some e1
  have m2 : output.map (·.val) = x'.2 := tokensBelow_some e2
  have l1 : x'.1.length = prompt.length := by rw [← m1, List.length_map]
  have l2 : x'.2.length = output.length := by rw [← m2, List.length_map]
  -- the instance's tokens at the prompt's and at the output's positions
  have tp : ∀ j (hj : j < x'.1.length), x.tok j = x'.1[j] := by
    intro j hj
    have hj' : j < prompt.length := l1 ▸ hj
    rw [ht j (by omega), IntegerModel.getD_app_left prompt output ⟨0, hV⟩ j hj']
    simp only [← m1, List.getElem_map]
  have tq : ∀ j (hj : j < x'.2.length), x.tok (x'.1.length + j) = x'.2[j] := by
    intro j hj
    have hj' : j < output.length := l2 ▸ hj
    rw [l1, ht (prompt.length + j) (by omega),
      IntegerModel.getD_app_right prompt output ⟨0, hV⟩ j hj']
    simp only [← m2, List.getElem_map]
  intro position hp
  have hpos := hT (x.r + position) (Nat.le_add_right _ _) (by rw [hr, he]; omega)
  have ew : x.w (x.r + position) = x'.2[position] := by
    show x.tok (x.r + position + 1) = _
    have e : x.r + position + 1 = x'.1.length + position := by rw [hr, l1]; omega
    rw [e]
    exact tq position hp
  have el : (List.range (x.r + position + 1)).map x.tok = x'.1 ++ x'.2.take position := by
    apply List.ext_getElem
    · rw [List.length_map, List.length_range, List.length_append, List.length_take, hr, l1]
      omega
    · intro j g1 g2
      rw [List.getElem_map, List.getElem_range]
      by_cases hj : j < x'.1.length
      · rw [List.getElem_append_left hj]
        exact tp j hj
      · have hj2 : x'.1.length ≤ j := Nat.le_of_not_lt hj
        rw [List.getElem_append_right hj2, List.getElem_take]
        have e : j = x'.1.length + (j - x'.1.length) := by omega
        have g3 : j - x'.1.length < x'.2.length := by
          rw [List.length_append, List.length_take] at g2
          omega
        rw [← tq (j - x'.1.length) g3, ← e]
  rw [← el, hpos, ew]

/-- **Two matrices of digits that say one matrix of field elements are one.** -/
theorem says_unique {rows cols : ℕ} {M : Fin rows → Fin cols → GE} {W W' : Mat}
    (h : SaysC M W) (h' : SaysC M W')
    (hb : ∀ y < rows, ∀ c < cols, -2 ^ 7 ≤ W y c ∧ W y c < 2 ^ 7)
    (hb' : ∀ y < rows, ∀ c < cols, -2 ^ 7 ≤ W' y c ∧ W' y c < 2 ^ 7) : W = W' := by
  funext y c
  by_cases hin : y < rows ∧ c < cols
  · exact digit_eq (hb y hin.1 c hin.2) (hb' y hin.1 c hin.2)
      ((h.1 ⟨y, hin.1⟩ ⟨c, hin.2⟩).symm.trans (h'.1 ⟨y, hin.1⟩ ⟨c, hin.2⟩))
  · rw [h.2 y c hin, h'.2 y c hin]

end VerifiableInference.OnPublicFiles.Flat
