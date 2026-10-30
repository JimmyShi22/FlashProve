-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Unfolds/SplitOn.lean: `String.splitOn` in a form that Lean's kernel can evaluate, and the
equation between the two, at all strings.
Adapted from Lean 4's core library (toolchain v4.29.1): `String.splitOnAux`, `String.splitOn`. What
is theirs: the routines' text, as Lean prints `String.splitOnAux.eq_def` and the body of
`String.splitOn`. What is ours: the laying in of a bound, and the laws but for this:
`splitBound`'s two parts (the bytes of s
behind i - j; the bytes of sep behind j) follow the routine's own termination measure, and
`splitF_returns` its proof's three arms.
Licence of the adapted text, from the toolchain's own file LICENSE (71 lines;
sha256 8b28515ffffc5c0fe2807d8ae3735b00b324d9b7ce807dd63ff6ac8922fbce7e): its first lines are
"Apache License 2.0 (Apache)", "Apache License", "Version 2.0, January 2004".
The adapted file's own header, from the toolchain's sources
(src/lean/Init/Data/String/Legacy.lean, 115 lines, sha256
7383f79fa34db227a5fc0c43997ef4ff47946794e77599243267f8ca743b556a; the two definitions stand at its
lines 61 and 112):
  Copyright (c) 2016 Microsoft Corporation. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Author: Leonardo de Moura, Mario Carneiro

Why. Asked by `decide +kernel` whether `"link 3, moment 1".splitOn ", moment "` is
`["link 3", "1"]`, Lean reports that the instance "did not reduce to `isTrue` or `isFalse`": the
kernel's check fails, at an input so small that no limit can be at work (seen at two strings). Our
reading: `String.splitOnAux` recurses by well-foundedness, and that recursion is not unfolded there.
So a closed statement whose evaluation reaches such a cut is not had that way. No theorem of the
library (toolchain v4.29.1, as far as our tree imports it) names `String.splitOn`. Behind one
rewriting with `splitOn_eq` the kernel evaluates it.

Main names.
  `splitF n`: `String.splitOnAux`'s text with a bound n in front: each call of itself stands at the
    bound less one; at the bound 0 the result is `none`. It recurses on the bound.
  `splitF_sound`: where the bounded text returns a list, the library's routine has that value. By
    induction on the bound; nothing on termination is used. `splitOn_of`: the same for
    `String.splitOn` at a separator that is not empty.
  `splitBound s sep i j`: (|s| - (i - j)) * (|sep| + 1) + (|sep| - j) + 1, lengths and positions in
    bytes. `splitF_returns`: at that bound or above the bounded text returns.
  `splitOnAux_eq`, `splitOn_eq`: the two routines are the bounded text at the bound.
How to use it: `simp only [splitOn_eq]` (it reaches under binders), then `decide +kernel`; or, at
one closed string, `splitOn_of (by decide +kernel) n (by decide +kernel)` at a bound n of one's
choice.
Tests: `cuts_under_a_binder`, `split_link`; negative: `split_link_no`.

Limits. The bounded text does the library's work over again and is no faster: it reads a character
by walking the string's list of characters from its start. The bound is of the order of the
product of the two lengths. Evaluation in the kernel at a long string has not been measured. No
import: Lean's own library alone.

-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Unfolds

/-- `String.splitOnAux` with a bound on its steps. -/
def splitF : Nat → String → String → String.Pos.Raw → String.Pos.Raw → String.Pos.Raw →
    List String → Option (List String)
  | 0, _, _, _, _, _, _ => none
  | n + 1, s, sep, b, i, j, r =>
    if String.Pos.Raw.atEnd s i = true then some (String.Pos.Raw.extract s b i :: r).reverse
    else
      if (String.Pos.Raw.get s i == String.Pos.Raw.get sep j) = true then
        if String.Pos.Raw.atEnd sep (String.Pos.Raw.next sep j) = true then
          splitF n s sep (String.Pos.Raw.next s i) (String.Pos.Raw.next s i) 0
            (String.Pos.Raw.extract s b
              ((String.Pos.Raw.next s i).unoffsetBy (String.Pos.Raw.next sep j)) :: r)
        else splitF n s sep b (String.Pos.Raw.next s i) (String.Pos.Raw.next sep j) r
      else splitF n s sep b (String.Pos.Raw.next s (i.unoffsetBy j)) 0 r

/-- **Where the bounded text returns a list, the library's routine has that value.** -/
theorem splitF_sound : ∀ (n : Nat) (s sep : String) (b i j : String.Pos.Raw) (r l : List String),
    splitF n s sep b i j r = some l → s.splitOnAux sep b i j r = l
  | 0, _, _, _, _, _, _, _, h => by
    rw [splitF] at h
    cases h
  | n + 1, s, sep, b, i, j, r, l, h => by
    rw [String.splitOnAux.eq_def]
    rw [splitF] at h
    by_cases h1 : String.Pos.Raw.atEnd s i = true
    · simp only [h1, ↓reduceIte] at h ⊢
      exact Option.some.inj h
    · simp only [h1] at h ⊢
      by_cases h2 : (String.Pos.Raw.get s i == String.Pos.Raw.get sep j) = true
      · simp only [h2, ↓reduceIte] at h ⊢
        by_cases h3 : String.Pos.Raw.atEnd sep (String.Pos.Raw.next sep j) = true
        · simp only [h3, ↓reduceIte] at h ⊢
          exact splitF_sound n _ _ _ _ _ _ _ h
        · simp only [h3] at h ⊢
          exact splitF_sound n _ _ _ _ _ _ _ h
      · simp only [h2] at h ⊢
        exact splitF_sound n _ _ _ _ _ _ _ h

/-- The same for `String.splitOn`, at a separator that is not empty. -/
theorem splitOn_of {s sep : String} {l : List String} (hs : (sep == "") = false) (n : Nat)
    (h : splitF n s sep 0 0 0 [] = some l) : s.splitOn sep = l := by
  show (if (sep == "") = true then [s] else s.splitOnAux sep 0 0 0 []) = l
  rw [hs]
  exact splitF_sound n _ _ _ _ _ _ _ h

/-- The bound: the bytes of s behind i - j and the bytes of sep behind j, laid into one number. -/
def splitBound (s sep : String) (i j : String.Pos.Raw) : Nat :=
  (s.utf8ByteSize - (i.byteIdx - j.byteIdx)) * (sep.utf8ByteSize + 1) +
    (sep.utf8ByteSize - j.byteIdx) + 1

/-- The bound falls where its first part falls. -/
private theorem step_lt (a a' K t t' n : Nat) (ha : a' + 1 ≤ a) (ht : t' + 1 ≤ K)
    (h : a * K + t + 1 ≤ n + 1) : a' * K + t' + 1 ≤ n := by
  have hm := Nat.mul_le_mul_right K ha
  rw [Nat.add_mul, Nat.one_mul] at hm
  omega

/-- The bound falls where its first part stays and its second falls. -/
private theorem step_eq (a K t t' n : Nat) (ht : t' + 1 ≤ t) (h : a * K + t + 1 ≤ n + 1) :
    a * K + t' + 1 ≤ n := by
  omega

/-- A position that is not at the end lies before the end. -/
private theorem lt_of_not_atEnd {s : String} {p : String.Pos.Raw}
    (h : ¬ String.Pos.Raw.atEnd s p = true) : p.byteIdx < s.utf8ByteSize := by
  simp only [String.Pos.Raw.atEnd, decide_eq_true_eq] at h
  omega

/-- **At the bound or above, the bounded text returns.** -/
theorem splitF_returns : ∀ (n : Nat) (s sep : String) (b i j : String.Pos.Raw) (r : List String),
    splitBound s sep i j ≤ n → ∃ l, splitF n s sep b i j r = some l
  | 0, s, sep, _, i, j, _, h => by
    unfold splitBound at h
    omega
  | n + 1, s, sep, b, i, j, r, h => by
    rw [splitF]
    unfold splitBound at h
    by_cases h1 : String.Pos.Raw.atEnd s i = true
    · rw [if_pos h1]
      exact ⟨_, rfl⟩
    · rw [if_neg h1]
      have hI := lt_of_not_atEnd h1
      have z : (0 : String.Pos.Raw).byteIdx = 0 := rfl
      by_cases h2 : (String.Pos.Raw.get s i == String.Pos.Raw.get sep j) = true
      · rw [if_pos h2]
        have hn := String.Pos.Raw.byteIdx_lt_byteIdx_next s i
        by_cases h3 : String.Pos.Raw.atEnd sep (String.Pos.Raw.next sep j) = true
        · rw [if_pos h3]
          refine splitF_returns n _ _ _ _ _ _ ?_
          unfold splitBound
          rw [z]
          exact step_lt _ _ _ _ _ n (by omega) (by omega) h
        · rw [if_neg h3]
          refine splitF_returns n _ _ _ _ _ _ ?_
          have hJ := lt_of_not_atEnd h3
          have hj := String.Pos.Raw.byteIdx_lt_byteIdx_next sep j
          have e1 : (String.Pos.Raw.next s i).byteIdx =
              i.byteIdx + (String.Pos.Raw.get s i).utf8Size := rfl
          have e2 : (String.Pos.Raw.next sep j).byteIdx =
              j.byteIdx + (String.Pos.Raw.get sep j).utf8Size := rfl
          have hc : String.Pos.Raw.get s i = String.Pos.Raw.get sep j := eq_of_beq h2
          have hd : (String.Pos.Raw.next s i).byteIdx - (String.Pos.Raw.next sep j).byteIdx =
              i.byteIdx - j.byteIdx := by
            rw [e1, e2, hc]
            omega
          unfold splitBound
          rw [hd]
          exact step_eq _ _ _ _ n (by omega) h
      · rw [if_neg h2]
        refine splitF_returns n _ _ _ _ _ _ ?_
        have hn := String.Pos.Raw.byteIdx_lt_byteIdx_next s (i.unoffsetBy j)
        have e : (i.unoffsetBy j).byteIdx = i.byteIdx - j.byteIdx := rfl
        unfold splitBound
        rw [z]
        exact step_lt _ _ _ _ _ n (by omega) (by omega) h

/-- **`String.splitOnAux` is the bounded text at the bound: at all strings and positions.** -/
theorem splitOnAux_eq (s sep : String) (b i j : String.Pos.Raw) (r : List String) :
    s.splitOnAux sep b i j r = (splitF (splitBound s sep i j) s sep b i j r).getD [] := by
  obtain ⟨l, hl⟩ := splitF_returns (splitBound s sep i j) s sep b i j r (Nat.le_refl _)
  rw [hl, splitF_sound _ _ _ _ _ _ _ _ hl, Option.getD_some]

/-- **`String.splitOn` without recursion by well-foundedness: at all strings.** -/
theorem splitOn_eq (s sep : String) :
    s.splitOn sep =
      if (sep == "") = true then [s]
      else (splitF (splitBound s sep 0 0) s sep 0 0 0 []).getD [] := by
  show (if (sep == "") = true then [s] else s.splitOnAux sep 0 0 0 []) = _
  rw [splitOnAux_eq]

/-- Cuts under a binder, decided whole behind one rewriting. -/
theorem cuts_under_a_binder :
    ["G0.2.call", "link 3, moment 1", "", "a..b"].map (fun s => s.splitOn ".") =
      [["G0", "2", "call"], ["link 3, moment 1"], [""], ["a", "", "b"]] := by
  simp only [splitOn_eq]
  decide +kernel

/-- A name cut at a separator of several characters. -/
theorem split_link : "link 3, moment 1".splitOn ", moment " = ["link 3", "1"] :=
  splitOn_of (by decide +kernel) 64 (by decide +kernel)

/-- A negative test, by the recipe of the head: the cut is no other list. -/
theorem split_link_no : "link 3, moment 1".splitOn ", moment " ≠ ["link 3,", "1"] := by
  simp only [splitOn_eq]
  decide +kernel

end Johnson.Unfolds

#print axioms Johnson.Unfolds.step_lt
#print axioms Johnson.Unfolds.step_eq
#print axioms Johnson.Unfolds.lt_of_not_atEnd
#print axioms Johnson.Unfolds.splitF_sound
#print axioms Johnson.Unfolds.splitOn_of
#print axioms Johnson.Unfolds.splitF_returns
#print axioms Johnson.Unfolds.splitOnAux_eq
#print axioms Johnson.Unfolds.splitOn_eq
#print axioms Johnson.Unfolds.cuts_under_a_binder
#print axioms Johnson.Unfolds.split_link
#print axioms Johnson.Unfolds.split_link_no
