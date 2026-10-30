-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LPFPol/FreeLine.lean: the step of the strict scan of the parameter file (`polStep`,
OnBytes/Model/Config.lean) returns on a value line that is written as the due name, one space, a
number below 2^32 in decimal, and a line feed.

Why. The laws on the strict scan in OnBytes/Model/ConfigReaders.lean and
Johnson/Goal/Meaning/ScopeScan.lean take the scan's return as a premise. A law that gives a return
at a file with other numbers needs the step's return at a line with a number that is a letter.

Main names.
* `len_digits`: a number below 10^(k+1) has at most k + 1 decimal digits. `head_digits`: the
  spelling of a number from 1 on does not begin with the digit 0. `lead_digits`: so a spelling
  begins with another digit than 0, or has one digit.
* `wordLineForm_of`: the test on the one spelling says yes at such a line.
* `beyond_short`, `beyond_of_short`: a line of at most 19 bytes has no more than 19 digits in a row.
  `runStep`: the step of that count.
* `noZero_of`: such a line holds no zero byte.
* `polStep_line`: THE LAW, on digits as a letter. `polStep_number`: the law at a number's spelling.

Premises of `polStep_number`. hd: the name due at the state is `due`. hn, hne, hlen: its bytes are
printable and no space, there is at least one and there are at most seven. hx: the number is below
2^32. hlast: the line is not the last value line. Then the step returns, and the state that it
returns has one value more.

Limits. The last value line, where the step also tests the frame's lines, is not covered. Names of
more than seven bytes are not covered (the proof bounds the line's length by 19). What the returned
state holds is said only as far as the number of its values. Nothing on soundness.

For proofs only; no program imports this file.


-/
import Johnson.LPFPol.HashReturns
import Johnson.Goal.Meaning.ScopeScan

set_option autoImplicit false

namespace LPFPol

open OnBytes OnBytes.Model OnBytes.Model.Config OnBytes.Model.ConfigReaders
open VerifierAndGoals.Lines (bytes_small bytes_step spelled)

/-! ### a number's decimal spelling -/

/-- A number below 10^(k+1) has at most k + 1 digits. -/
theorem len_digits : ∀ (k x : Nat), x < 10 ^ (k + 1) → (bytesOf (toString x)).length ≤ k + 1
  | 0, x, h => by
    rw [bytes_small (by simpa using h)]
    simp
  | k + 1, x, h => by
    by_cases c : x < 10
    · rw [bytes_small c]
      simp
    · rw [bytes_step (Nat.le_of_not_lt c), List.length_append]
      have e : (10 : Nat) ^ (k + 1 + 1) = 10 ^ (k + 1) * 10 := Nat.pow_succ 10 (k + 1)
      rw [e] at h
      have a := len_digits k (x / 10) (by omega)
      simp only [List.length_cons, List.length_nil]
      omega

theorem digit_ne_zero : ∀ d, d < 10 → 1 ≤ d → (48 + d).toUInt8 ≠ 0x30 := by decide

/-- The spelling of a number from 1 on does not begin with the digit 0. -/
theorem head_digits (x : Nat) : 1 ≤ x → (bytesOf (toString x)).head? ≠ some 0x30 := by
  induction x using Nat.strongRecOn with
  | _ x ih =>
    intro h1
    by_cases c : x < 10
    · rw [bytes_small c]
      intro e
      exact digit_ne_zero x c h1 (Option.some.inj e)
    · have h10 : 10 ≤ x := Nat.le_of_not_lt c
      rw [bytes_step h10]
      have hi := ih (x / 10) (by omega) (by omega)
      cases hD : bytesOf (toString (x / 10)) with
      | nil => exact absurd hD (spelled (x / 10)).2.1
      | cons a t =>
        rw [hD] at hi
        exact hi

/-- A spelling begins with another digit than 0, or has one digit. -/
theorem lead_digits (x : Nat) :
    ((bytesOf (toString x)).head? != some 0x30 || (bytesOf (toString x)).length == 1) = true := by
  by_cases c : 1 ≤ x
  · rw [bne_iff_ne.2 (head_digits x c)]
    rfl
  · have e : x = 0 := by omega
    subst e
    rw [bytes_small (by decide)]
    rfl

/-! ### the tests on a line -/

/-- The test on the one spelling says yes. -/
theorem wordLineForm_of {name digits : List UInt8}
    (hn : (name.all fun c => 0x20 < c && c < 0x7F) = true) (hne : name ≠ [])
    (hd : digits.all isDigit = true) (hde : digits ≠ []) (hl : digits.length ≤ 10)
    (h0 : (digits.head? != some 0x30 || digits.length == 1) = true)
    (hv : digitsValue digits < 2 ^ 32) :
    wordLineForm (name ++ 0x20 :: digits ++ [0x0A]) = true := by
  have hL : name ++ 0x20 :: digits ++ [0x0A] = name ++ 0x20 :: (digits ++ [0x0A]) := by simp
  have ht : (name ++ 0x20 :: (digits ++ [0x0A])).takeWhile (fun c => 0x20 < c && c < 0x7F) = name :=
    takeWhile_stop hn (by decide)
  have hw : (digits ++ [0x0A]).takeWhile isDigit = digits := takeWhile_stop hd (by decide)
  rw [hL]
  unfold wordLineForm
  dsimp only
  rw [ht, List.drop_left]
  split
  · rename_i rest heq
    obtain rfl : digits ++ [0x0A] = rest := (List.cons.inj heq).2
    rw [hw, List.drop_left, List.isEmpty_eq_false_iff.2 hne, List.isEmpty_eq_false_iff.2 hde,
      decide_eq_true hl, h0, decide_eq_true hv]
    rfl
  · rename_i hno
    exact absurd rfl (hno _)

/-- The step of `digitsBeyondScan`. -/
def runStep (s : Nat × Bool) (c : UInt8) : Nat × Bool :=
  let run := if isDigit c then s.1 + 1 else 0
  (run, s.2 || decide (19 < run))

/-- From a run of n digits on, over a list with which n stays at most 19, no run exceeds 19. -/
theorem beyond_short : ∀ (l : List UInt8) (n : Nat), n + l.length ≤ 19 →
    (l.foldl runStep (n, false)).2 = false
  | [], _, _ => rfl
  | c :: l, n, h => by
    rw [List.length_cons] at h
    rw [List.foldl_cons]
    by_cases hc : isDigit c = true
    · have e : runStep (n, false) c = (n + 1, false) := by
        unfold runStep
        dsimp only
        rw [if_pos hc, decide_eq_false (by omega)]
        rfl
      rw [e]
      exact beyond_short l (n + 1) (by omega)
    · have e : runStep (n, false) c = (0, false) := by
        unfold runStep
        dsimp only
        rw [if_neg hc]
        rfl
      rw [e]
      exact beyond_short l 0 (by omega)

/-- A line of at most 19 bytes has no more than 19 digits in a row. -/
theorem beyond_of_short {line : List UInt8} (h : line.length ≤ 19) :
    digitsBeyondScan line = false :=
  beyond_short line 0 (by omega)

/-- The line holds no zero byte. -/
theorem noZero_of {name digits : List UInt8}
    (hn : (name.all fun c => 0x20 < c && c < 0x7F) = true) (hd : digits.all isDigit = true) :
    (name ++ 0x20 :: digits ++ [0x0A]).contains 0 = false := by
  have hm : (0 : UInt8) ∉ name ++ 0x20 :: digits ++ [0x0A] := by
    intro hm
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with (h | h | h) | h
    · exact absurd (List.all_eq_true.1 hn 0 h) (by decide)
    · exact absurd h (by decide)
    · exact absurd (List.all_eq_true.1 hd 0 h) (by decide)
    · exact absurd h (by decide)
  simpa using hm

/-! ### the step -/

/-- **The step returns on a value line.** digits: the number's digits, as a letter. -/
theorem polStep_line {frame : Params.Lines} {prof : Nat} {names : Array String} {s : PolState}
    {due : String} {digits : List UInt8} (hd : names[s.vals.size]? = some due)
    (hn : ((bytesOf due).all fun c => 0x20 < c && c < 0x7F) = true) (hne : bytesOf due ≠ [])
    (hlen : (bytesOf due).length ≤ 7) (hdg : digits.all isDigit = true) (hde : digits ≠ [])
    (hl : digits.length ≤ 10)
    (h0 : (digits.head? != some 0x30 || digits.length == 1) = true)
    (hv : digitsValue digits < 2 ^ 32) (hlast : s.vals.size + 1 ≠ names.size) :
    ∃ s', polStep frame prof names s (bytesOf due ++ 0x20 :: digits ++ [0x0A]) = .ok s' ∧
      s'.vals.size = s.vals.size + 1 := by
  have hlen' : (bytesOf due ++ 0x20 :: digits ++ [0x0A]).length ≤ 19 := by
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  have hsc : scanned (bytesOf due ++ 0x20 :: digits ++ [0x0A]) =
      .ok (some (bytesOf due, digitsValue digits)) := by
    unfold scanned
    rw [beyond_of_short hlen', scanLine_short hn hne (by omega) hdg hde]
    rfl
  have hsp : oneSpelling (bytesOf due ++ 0x20 :: digits ++ [0x0A]) = .ok () := by
    unfold oneSpelling
    rw [wordLineForm_of hn hne hdg hde hl h0 hv]
    rfl
  have hc : ((s.vals.push (digitsValue digits)).size == names.size) = false := by
    rw [Array.size_push]
    exact beq_eq_false_iff_ne.2 hlast
  refine ⟨{ s with tblPrev := false, vals := s.vals.push (digitsValue digits) }, ?_,
    Array.size_push _⟩
  unfold polStep
  refine (bind_ok (refuseIf_no (decide_eq_false (by omega)))).trans ?_
  refine (bind_ok (refuseIf_no (noZero_of hn hdg))).trans ?_
  dsimp only
  rw [hd]
  dsimp only
  refine (bind_ok hsc).trans ?_
  dsimp only
  refine (bind_ok (refuseIf_no (decide_eq_false (by omega)))).trans ?_
  refine (bind_ok (refuseIf_no (by simp))).trans ?_
  refine (bind_ok hsp).trans ?_
  dsimp only
  rw [hc]
  rfl

/-- **The step returns on a value line with a number below 2^32.** -/
theorem polStep_number {frame : Params.Lines} {prof : Nat} {names : Array String} {s : PolState}
    {due : String} {x : Nat} (hd : names[s.vals.size]? = some due)
    (hn : ((bytesOf due).all fun c => 0x20 < c && c < 0x7F) = true) (hne : bytesOf due ≠ [])
    (hlen : (bytesOf due).length ≤ 7) (hx : x < 2 ^ 32) (hlast : s.vals.size + 1 ≠ names.size) :
    ∃ s', polStep frame prof names s (bytesOf due ++ 0x20 :: bytesOf (toString x) ++ [0x0A]) =
        .ok s' ∧ s'.vals.size = s.vals.size + 1 := by
  obtain ⟨a, b, c⟩ := spelled x
  exact polStep_line hd hn hne hlen a b
    (len_digits 9 x (Nat.lt_of_lt_of_le hx (by decide))) (lead_digits x) (by rw [c]; exact hx) hlast

end LPFPol

#print axioms LPFPol.polStep_number
