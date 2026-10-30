-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Item/Tests.lean: tests, written as functions that return true or false, on the two
readers of a parameter file, and what they give.

Main names.
* `numbersB P L`: a test on the scan P and the lines L: the form that `requestItem` asks, at 2 ^ 10
  tokens; the 97 named numbers; the four tables' digests; the last five words.
* `textB L name t`: the lines of one name are there, and their text is t. `calls_of_text`: then the
  item's digest of these lines is the earlier hash, under 73, of t's words. No hash is evaluated:
  both sides hash one text.
* `parts_of_tests`: the test on the numbers and three equations on digests give `Parts`
  (Johnson/AtFull/Item/HeldOfParts.lean).

Limits. Definitions and general laws. That a test passes is shown at no file here. No soundness is
claimed.
-/
import Johnson.AtFull.Item.HeldOfParts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Item
open OnBytes OnBytes.Proof OnBytes.Model OnBytes.Model.Verify OnBytes.K

/-- The two readers give one digest for a table. -/
def eightB (P : PolScan) (L : ParamLines) (name : String) (t : PublicTable) : Bool :=
  match L.eight name, P.tableExpected t with
  | some a, some b => a == b
  | _, _ => false

/-- The two readers give one number for every name of the list. -/
def agreeB (P : PolScan) (L : ParamLines) (names : List String) : Bool :=
  names.all fun n => L.value n == some (P.value n)

/-- The test on the numbers: the form that `requestItem` asks, at 2 ^ 10 tokens; the named numbers;
the tables' digests; the last five words. -/
def numbersB (P : PolScan) (L : ParamLines) : Bool :=
  (((L.values "version").bind (·.head?)).any fun v => v.length == 4) &&
    L.value "prof" == some 20 && ((L.value "NE").any fun n => n != 0) &&
    L.value "lt" == some 10 &&
    agreeB P L names2L && agreeB P L names37L && agreeB P L names103L && agreeB P L names130L &&
    eightB P L "tsilu" .silu && eightB P L "tsig" .sigmoid && eightB P L "trope" .rope &&
    eightB P L "texp" .exp &&
    (L.lastWords.any fun w => w == Fmt.cat ([P.hb, P.lkW, P.frame.tableRowsLog, P.frame.tableLogN,
      P.frame.tableRandom].map word32))

/-- The lines of one name are there, and their text is t. -/
def textB (L : ParamLines) (name : String) (t : ByteArray) : Bool :=
  !(L.text name).isEmpty && L.text name == t

/-- A test that passes at an option passes at a value. -/
theorem any_some {α : Type} {o : Option α} {p : α → Bool} (h : o.any p = true) :
    ∃ a, o = some a ∧ p a = true := by
  cases o with
  | none => cases h
  | some a => exact ⟨a, rfl, h⟩

/-- What `eightB` says: the lines' digest of that name is there, and it is the one that the scan
expects of the table. -/
theorem eight_of {P : PolScan} {L : ParamLines} {name : String} {t : PublicTable}
    (h : eightB P L name t = true) : ∃ d, L.eight name = some d ∧ P.tableExpected t = some d := by
  unfold eightB at h
  split at h
  · rename_i a b ha hb
    exact ⟨a, ha, by rw [hb, Fmt.eq_of_bytes_beq _ _ h]⟩
  · cases h

/-- What `agreeB` says: at every name of the list the lines' value is the scan's. -/
theorem agree_of {P : PolScan} {L : ParamLines} {names : String} {l : List String}
    (hl : names.splitOn " " = l) (h : agreeB P L l = true) :
    ∀ n ∈ names.splitOn " ", L.value n = some (P.value n) := by
  rw [hl]
  intro n hn
  exact eq_of_beq (List.all_eq_true.1 h n hn)

/-- The item's digest of the lines of one name, from their text. -/
theorem calls_of_text {L : ParamLines} {name : String} {ifNone : Option String} {t : ByteArray}
    (h : textB L name t = true) : L.calls name ifNone = some (secondHashFunction 73 (textWords t)) := by
  unfold textB at h
  rw [Bool.and_eq_true] at h
  unfold ParamLines.calls
  dsimp only
  rw [if_pos h.1, Fmt.eq_of_bytes_beq _ _ h.2]

/-- **The test on the numbers and three equations on digests give `Parts`.** -/
theorem parts_of_tests {X : Public} {L : ParamLines} (hn : numbersB X.P L = true)
    (call : L.calls "call" = some X.digests.hCalls)
    (callA : L.calls "callA" = some X.digests.hCallsA)
    (callH : L.calls "callH" (some callHIfNone) = some X.digests.hCallsH) :
    Parts X L (4 * (2 ^ 10 + 2)) := by
  unfold numbersB at hn
  simp only [Bool.and_eq_true] at hn
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, a2⟩, a37⟩, a103⟩, a130⟩, t1⟩, t2⟩, t3⟩, t4⟩, hl⟩ := hn
  obtain ⟨v, hv, hv4⟩ := any_some h1
  obtain ⟨n, hne, hn0⟩ := any_some h3
  obtain ⟨w, hw, hw2⟩ := any_some hl
  exact
    { version := ⟨v, hv, eq_of_beq hv4⟩
      prof := eq_of_beq h2
      ne := ⟨n, hne, by simpa using hn0⟩
      lt := ⟨10, eq_of_beq h4, rfl⟩
      n2 := agree_of names2_list a2
      n37 := agree_of names37_list a37
      n103 := agree_of names103_list a103
      n130 := agree_of names130_list a130
      silu := eight_of t1
      sigmoid := eight_of t2
      rope := eight_of t3
      exp := eight_of t4
      call := call
      callA := callA
      callH := callH
      last := by rw [hw, Fmt.eq_of_bytes_beq _ _ hw2]; rfl }

end Johnson.AtFull.Item

#print axioms Johnson.AtFull.Item.any_some
#print axioms Johnson.AtFull.Item.eight_of
#print axioms Johnson.AtFull.Item.agree_of
#print axioms Johnson.AtFull.Item.calls_of_text
#print axioms Johnson.AtFull.Item.parts_of_tests
#print axioms Johnson.AtFull.Item.eightB
#print axioms Johnson.AtFull.Item.agreeB
#print axioms Johnson.AtFull.Item.numbersB
#print axioms Johnson.AtFull.Item.textB
