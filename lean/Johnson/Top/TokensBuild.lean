-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/TokensBuild.lean: from the files to an instance: `Flat.buildOf`
(Johnson/Flat/Instance.lean) returns at the prompt, the output and the further tokens that
OnBytes/K/Tokens.lean reads off the user's request and reply, and the instance's numbers are the
program's. For proofs only.

  `tokensBelow_of`: a list of numbers below V is read as a list of tokens of the vocabulary, with
    the same numbers.
  `build_of_files`: where the program's reader of request and reply returns so at the window P.T,
    and `coveredOf` returns at P.T and P.V: `buildOf P (promptOf x, outputOf x) (auxOf x)` returns
    an instance i; its r, e and y are so's, and its window's token at each place is the request's.
What is not claimed: nothing on what a yes says of the instance. P is a letter: that P.T and P.V are
the parameter file's window and vocabulary is the caller's to show.


-/
import OnBytes.K.TokensCovered
import Johnson.Flat.Instance

set_option autoImplicit false

namespace OnBytes.K

open OnBytes OnBytes.Model OnBytes.Model.Verify
open OnBytes.Flat (tokensBelow requestAt buildAt buildOf Instance')

/-- Numbers below V are read as tokens of the vocabulary, with the same numbers. -/
theorem tokensBelow_of (V : ℕ) : ∀ l : List ℕ, (∀ t ∈ l, t < V) →
    ∃ l' : List (Fin V), tokensBelow V l = some l' ∧ l'.map Fin.val = l
  | [], _ => ⟨[], rfl, rfl⟩
  | t :: rest, h => by
    obtain ⟨r', h1, h2⟩ := tokensBelow_of V rest fun u hu => h u (List.mem_cons_of_mem _ hu)
    have ht : t < V := h t List.mem_cons_self
    refine ⟨⟨t, ht⟩ :: r', ?_, ?_⟩
    · show (if h : t < V then (tokensBelow V rest).map (⟨t, h⟩ :: ·) else none) = _
      rw [dif_pos ht, h1]
      rfl
    · rw [List.map_cons, h2]

/-- A place of a list of tokens, as a number. -/
theorem getD_val {V : ℕ} (l : List (Fin V)) (n : ℕ) (d : Fin V) :
    (l.getD n d).val = (l.map Fin.val).getD n d.val := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[n]? <;> rfl

/-- From the files to an instance. In words: the head of this file. -/
theorem build_of_files {P : Inst.Model.Params} {x : UserStm} {so : Head.StOwn}
    {cov : Head.Covered}
    (h : Head.stFromCall (words32 x.request) (words32 x.y) P.T = .ok so)
    (hc : Head.coveredOf so P.T P.V = .ok cov) :
    ∃ i : Instance' P, buildOf P (promptOf x, outputOf x) (auxOf x) = some i ∧
      i.r = so.r ∧ i.e = so.e ∧ i.y.val = so.y ∧
      ∀ t : Fin P.T, (i.prompt t).val = (tokensOf x).getD t.val 0 := by
  obtain ⟨_, _, hall, hy⟩ := covered_of h hc
  obtain ⟨hT, hl, e1, e2, e3, h1, h2⟩ := read_of h
  obtain ⟨l1, l2⟩ := lengths_of h
  have hsplit := split_of h
  have hz := reply_zero_of h
  have hV : 0 < P.V := Nat.lt_of_le_of_lt (Nat.zero_le _) hy
  have a1 : ∀ t ∈ promptOf x, t < P.V := fun t ht => hall t (List.mem_of_mem_take ht)
  have a2 : ∀ t ∈ outputOf x, t < P.V := by
    intro t ht
    unfold outputOf at ht
    rcases List.mem_append.1 ht with hm | hm
    · exact hall t (List.mem_of_mem_drop (List.mem_of_mem_take hm))
    · split at hm
      · rw [List.mem_singleton.1 hm]
        exact hy
      · cases hm
  have a3 : ∀ t ∈ auxOf x, t < P.V := fun t ht => hall t (List.mem_of_mem_drop ht)
  obtain ⟨p', b1, m1⟩ := tokensBelow_of P.V _ a1
  obtain ⟨o', b2, m2⟩ := tokensBelow_of P.V _ a2
  obtain ⟨x', b3, m3⟩ := tokensBelow_of P.V _ a3
  have n1 : p'.length = so.r + 1 := by rw [← l1, ← m1, List.length_map]
  have n2 : o'.length = so.e - so.r := by rw [← l2, ← m2, List.length_map]
  have hre : so.r < so.e := by rw [e1, e2]; exact h1
  have heT : so.e ≤ P.T := by rw [e2]; exact h2
  have hcond : 0 < p'.length ∧ 0 < o'.length ∧ p'.length + o'.length ≤ P.T + 1 := by
    rw [n1, n2]
    omega
  have hb : buildOf P (promptOf x, outputOf x) (auxOf x) = requestAt P hV p' o' x' := by
    unfold buildOf
    rw [dif_pos hV]
    unfold buildAt
    simp only [b1, b2, b3]
  unfold requestAt at hb
  rw [dif_pos hcond] at hb
  refine ⟨_, hb, ?_, ?_, ?_, ?_⟩
  · show p'.length - 1 = so.r
    omega
  · show p'.length - 1 + o'.length = so.e
    omega
  · show ((p' ++ o').getD P.T ⟨0, hV⟩).val = so.y
    rw [getD_val, List.map_append, m1, m2]
    by_cases he : so.e = P.T
    · have haux : auxOf x = [] := by
        unfold auxOf
        exact List.drop_eq_nil_of_le (by rw [hl, ← e2, he]; omega)
      rw [haux, List.append_nil, if_pos he] at hsplit
      rw [hsplit, List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [hl]), hl,
        Nat.sub_self]
      rfl
    · have hlen : (promptOf x ++ outputOf x).length ≤ P.T := by
        rw [List.length_append, l1, l2]
        omega
      rw [List.getD_eq_default _ _ hlen, e3]
      exact (hz (by rw [← e2]; omega)).symm
  · intro t
    show ((p' ++ o' ++ x').getD t.val ⟨0, hV⟩).val = _
    rw [getD_val, List.map_append, List.map_append, m1, m2, m3, hsplit,
      List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_append_left (by rw [hl]; exact t.isLt)]

end OnBytes.K
