-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/ConfigReadersBehind.lean: what the strict scan of the parameter file itself reads by
name, before it goes through the lines, is what it then reads line by line.

Before its steps the strict scan `polScan` (OnBytes/Model/Config.lean) asks the reader by name,
`Config.polWord`, for three lines: prof, toksrc and lt. It asks at the bytes after the frame's
lines, not at the whole file. It tests the three numbers, and by the first it picks the list of
names that its steps then ask for, line by line. OnBytes/Model/ConfigReaders.lean proves that the
reader by name at the WHOLE file finds the scan's own values. This file carries that law to the
bytes after the frame's lines. So the three numbers that the scan tested are the values in its
result, and the list of names is that of the profile in its record.

How. Where the scan returns, the first line after the frame's lines is the value line of prof, and
the lines of a text laid end to end are the text. So these bytes begin with the letter p. The reader
of the frame's lines asks first for a line that begins with the word version, so it refuses them,
and `Config.polWord` then searches their lines: the list that it searches at the whole file.

Main theorems, each under the hypothesis that the scan returns P on the file. `polWord_behind`: the
reader by name gives at the bytes after the frame's lines what it gives at the whole file.
`polScan_names`: the names of the scan's value lines are `valueNames P.h.prof`. `polWord_of_prof`:
`polWord_of_scan` for every name of that list. `polScan_asked`: the line prof holds a number from 16
to 31, the line toksrc holds 1, and the line lt holds a number from 4 to 16. `polScan_prof`: the
line prof holds 16 plus the record's profile. The other lemmas are in the namespace
`ConfigReaders`.

What is not claimed. On a file that the scan refuses, nothing is said. No range is given for another
value line. Nothing is said of the lines outside prof to F, of a stage or of a whole call, or of the
C++ verifier's readers. Nothing on soundness. For proofs only; the program does not import this
file.


-/
import OnBytes.Model.ConfigReaders

set_option autoImplicit false

namespace OnBytes.Model

open Config ConfigReaders
open OnBytes.Params (exc_bind)

namespace ConfigReaders

/-- The walk of `linesOf`: its lines laid end to end are the complete lines, the current line and
the text that is left, in that order. -/
theorem flatten_linesLoop : ∀ (t cur : List UInt8) (acc : List (List UInt8)),
    (linesLoop t cur acc).flatten = acc.reverse.flatten ++ cur.reverse ++ t
  | [], cur, acc => by
    unfold linesLoop
    split
    · rename_i hc
      simp [List.isEmpty_iff.1 hc]
    · simp
  | c :: t, cur, acc => by
    unfold linesLoop
    split
    · rw [flatten_linesLoop]
      simp
    · rw [flatten_linesLoop]
      simp

/-- The lines of a text laid end to end are the text. -/
theorem flatten_linesOf (t : List UInt8) : (linesOf t).flatten = t := by
  unfold linesOf
  rw [flatten_linesLoop]
  simp

/-- The bytes of a text, as the list in its byte array. At a text that is spelled out Lean evaluates
this side by unfolding; the walk of `ByteArray.toList` it does not unfold. -/
theorem bytesOf_data (s : String) : bytesOf s = s.toUTF8.data.toList := by
  unfold bytesOf ByteArray.toList
  rw [toList_loop _ _ 0 [] rfl]
  rfl

/-- What `Params.cutAtFrom` gives as the part before the cut begins with the bytes passed so far. -/
theorem cutAtFrom_seen (c : UInt8) : ∀ (t seen l r : List UInt8),
    Params.cutAtFrom c seen t = some (l, r) → ∃ l', l = seen.reverse ++ l'
  | [], seen, l, r, h => by simp [Params.cutAtFrom] at h
  | x :: t, seen, l, r, h => by
    unfold Params.cutAtFrom at h
    split at h
    · cases h
      exact ⟨[], by simp⟩
    · obtain ⟨l', e⟩ := cutAtFrom_seen c t (x :: seen) l r h
      exact ⟨x :: l', by rw [e]; simp⟩

/-- The reader of the frame's lines refuses a text that begins with the letter p. -/
theorem lines_refuses (tail : List UInt8) : ∃ e, Params.lines (0x70 :: tail) = .error e := by
  have hw : ∃ e, Params.words "version" (some 1) (0x70 :: tail) = .error e := by
    unfold Params.words
    cases hc : Params.cutAt 0x0A (0x70 :: tail) with
    | none => exact ⟨_, rfl⟩
    | some x =>
      obtain ⟨l, r⟩ := x
      have h1 : Params.cutAtFrom 0x0A [0x70] tail = some (l, r) := by
        unfold Params.cutAt Params.cutAtFrom at hc
        exact hc
      obtain ⟨l', e⟩ := cutAtFrom_seen _ _ _ _ _ h1
      have hb : Params.behind ("version".toUTF8.toList ++ [0x20]) l = none := by
        have e2 : "version".toUTF8.toList = bytesOf "version" := rfl
        rw [e, e2, bytesOf_data]
        rfl
      simp only [hb]
      exact ⟨_, rfl⟩
  obtain ⟨e, he⟩ := hw
  refine ⟨e, ?_⟩
  unfold Params.lines Params.versionLine
  simp only [bind, StateT.bind, he, Except.bind]

/-- Where the scan returns, the bytes after the frame's lines begin with the letter p: their first
line is the value line of prof. -/
theorem rest_begins {pol : ByteArray} {P : PolScan} (h : polScan pol = .ok P)
    {frame : Params.Lines} {rest : ByteArray} (hr : Params.readLines pol = .ok (frame, rest)) :
    ∃ tail, rest.toList = 0x70 :: tail := by
  obtain ⟨frame', rest', prof, s, hr', _, _, hs, hsize, _, _⟩ := polScan_parts h
  rw [hr] at hr'
  cases hr'
  cases hl : linesOf rest.toList with
  | nil =>
    rw [hl] at hs
    cases hs
    have h0 : 0 < (valueNames prof).length := by
      unfold valueNames
      simp
    have h1 : ({} : PolState).vals.size = 0 := rfl
    omega
  | cons line more =>
    rw [hl, List.foldlM_cons] at hs
    obtain ⟨s1, h1, _⟩ := exc_bind hs
    obtain ⟨_, val, _, digits, hline, _⟩ := polStep_value (due := "prof") rfl h1
    have e := flatten_linesOf rest.toList
    rw [hl, List.flatten_cons, hline, bytesOf_data] at e
    exact ⟨_, e.symm⟩

/-- The three tests that a scan which returns has made on what the reader by name finds in the
bytes after the frame's lines. -/
theorem polScan_tests {pol : ByteArray} {P : PolScan} (h : polScan pol = .ok P) :
    ∃ frame rest plt, Params.readLines pol = .ok (frame, rest) ∧
      (polWord rest "prof").map (· / 16) = some 1 ∧ polWord rest "toksrc" = some 1 ∧
      polWord rest "lt" = some plt ∧ 4 ≤ plt ∧ plt ≤ 16 := by
  unfold polScan at h
  cases hr : Params.readLines pol with
  | error e =>
    rw [hr] at h
    cases h
  | ok x =>
    rw [hr] at h
    obtain ⟨frame, rest⟩ := x
    dsimp only at h
    obtain ⟨w, hw, h⟩ := exc_bind h
    cases hw
    dsimp only at h
    obtain ⟨_, t1, h⟩ := exc_bind h
    split at h
    · rename_i plt hlt
      obtain ⟨y, hy, h⟩ := exc_bind h
      cases hy
      obtain ⟨_, t2, h⟩ := exc_bind h
      have a1 := refuseIf_ok t1
      have a2 := refuseIf_ok t2
      simp only [Bool.or_eq_false_iff, bne_eq_false_iff_eq, decide_eq_false_iff_not,
        Nat.not_lt] at a1 a2
      exact ⟨frame, rest, plt, rfl, a1.1, a1.2, hlt, a2.1, a2.2⟩
    · cases h

end ConfigReaders

/-- If the strict scan returns on a parameter file, the reader by name gives at the bytes after the
frame's lines what it gives at the whole file, for every name. -/
theorem polWord_behind {pol : ByteArray} {P : PolScan} (h : polScan pol = .ok P)
    {frame : Params.Lines} {rest : ByteArray} (hr : Params.readLines pol = .ok (frame, rest))
    (n : String) : Config.polWord rest n = Config.polWord pol n := by
  obtain ⟨tail, ht⟩ := rest_begins h hr
  obtain ⟨e, he⟩ := lines_refuses tail
  have hre : Params.readLines rest = .error e := by
    unfold Params.readLines
    rw [ht, he]
    rfl
  have hb : begins "version " rest.toList = false := by
    unfold begins
    rw [ht, bytesOf_data]
    rfl
  unfold polWord
  rw [hre, hr]
  simp only [hb, Bool.false_eq_true, if_false]

/-- The names of the scan's value lines are those of the profile in the scan's record. -/
theorem polScan_names {pol : ByteArray} {P : PolScan} (h : polScan pol = .ok P) :
    P.values.map Prod.fst = valueNames P.h.prof := by
  obtain ⟨frame, rest, prof, s, hr, _, hprof, _, hsize, hv, hh⟩ := polScan_parts h
  rw [polWord_behind h hr, polWord_of_name h (by simp [valueNames])] at hprof
  have e : prof = P.h.prof := by
    rw [hprof, hh]
    rfl
  rw [hv, List.map_fst_zip (by simp [hsize]), e]

/-- `polWord_of_scan` with its second hypothesis said by the record's profile. -/
theorem polWord_of_prof {pol : ByteArray} {P : PolScan} (h : polScan pol = .ok P) {n : String}
    (hn : n ∈ valueNames P.h.prof) : Config.polWord pol n = some (P.value n) :=
  polWord_of_scan h (by rw [polScan_names h]; exact hn)

/-- The three tests that the scan makes on what the reader by name finds, said of the scan's own
values: the line prof holds a number from 16 to 31, the line toksrc holds 1, and the line lt a
number from 4 to 16. -/
theorem polScan_asked {pol : ByteArray} {P : PolScan} (h : polScan pol = .ok P) :
    P.value "prof" / 16 = 1 ∧ P.h.toksrc = 1 ∧ 4 ≤ P.h.lt ∧ P.h.lt ≤ 16 := by
  obtain ⟨frame, rest, plt, hr, a1, a2, a3, a4, a5⟩ := polScan_tests h
  rw [polWord_behind h hr, polWord_of_name h (by simp [valueNames])] at a1 a2 a3
  have hh := polScan_h h
  have e2 : P.h.toksrc = P.value "toksrc" := by
    rw [hh]
    rfl
  have e3 : P.h.lt = P.value "lt" := by
    rw [hh]
    rfl
  simp only [Option.map_some, Option.some.injEq] at a1 a2 a3
  rw [e2, e3, a2, a3]
  exact ⟨a1, rfl, a4, a5⟩

/-- The line prof holds 16 plus the record's profile. -/
theorem polScan_prof {pol : ByteArray} {P : PolScan} (h : polScan pol = .ok P) :
    P.value "prof" = 16 + P.h.prof := by
  have a := (polScan_asked h).1
  have e : P.h.prof = P.value "prof" % 16 := by
    rw [polScan_h h]
    rfl
  rw [e]
  omega

end OnBytes.Model

#print axioms OnBytes.Model.polWord_behind
#print axioms OnBytes.Model.polScan_names
#print axioms OnBytes.Model.polWord_of_prof
#print axioms OnBytes.Model.polScan_asked
#print axioms OnBytes.Model.polScan_prof
