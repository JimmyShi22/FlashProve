-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/Rules4Laws.lean: what is hashed for a chain's first value (`firstBytes`) has a reader with both
laws, on the values with `First.ok`. So `firstBytes` is one to one on these values.

Definitions that compute, theorems, proofs, tests (#guard). No Mathlib.
What is hashed for a chain's first value: the format page's section
4, in an edition that is not the one that ships, R4.6; a second
edition's R4.6 says more on where a stored table's name and record
stand, among the statement's items: what is hashed is the same; read
at two further editions, neither of them the one that ships: the
formula of what is hashed is the same, letter for letter; an edition
between these two adds a passage on the root under which a stored
table is opened.

A chain's first value (a chain: the head of Fmt/Rules4.lean) is the hash of the bytes `firstBytes`
(`firstValueW`, Fmt/Rules4.lean). A spelling is an encoding of values as bytes; a reader (`Rd α`,
Fmt/Rules1.lean) is a decoder that starts at a place (an offset in bytes) of a string and may
refuse. The two laws are `Undoes` (Fmt/Rules1Laws.lean: the reader gives back what was spelled) and
`Only` (Fmt/Rules1Only.lean: what the reader accepts is the spelling of what it returns).
Fmt/Rules4.lean: `firstBytes pd statement record run`: the parameters' digest; the word of the
statement's length, the statement; the word of the record's length, the record; the word 1 and the
run's value, or the word 0.

Why: an encoding of the typed first query into the strings of a single oracle needs both a writer
and a reader, inverse to each other.

Main names:
  `First`, `First.ok`: the four parts as data; the values that have a spelling: both digests of 32
    bytes, both lengths below 2^64.
  `First.okB`, `First.okB_iff`: the same as a test that computes; so `First.ok` is decidable.
  `optRun`, `rdOptRun`: the last part and its reader (a word other than 0, 1 is refused; behind 1:
    32 bytes); `undoes_optRun`, `only_optRun`.
  `rdFirst`, `readFirst`: the reader at a place of a longer string; on a whole string (refused if
    bytes are left).
  `spFirst`, `firstBytes_eq`: `firstBytes` is the spelling made of the parts' spellings
    (Fmt/Rules1.lean: `pair`, `text`).
  `undoes_first`, `only_first`: the two laws in the forms of Fmt/Rules1Laws.lean,
    Fmt/Rules1Only.lean: in the middle of any string.
  `readFirst_firstBytes`: on `First.ok`: what is written is read back.
  `firstBytes_readFirst`: whatever is read back: the string is `firstBytes` of what is returned, and
    that lies in `First.ok`.
  `firstBytes_inj`: one to one on `First.ok`.

Limits: in each of the editions named at the top of this file
no chain fills the record: its length word is the constant 0 (R4.6). The
spelling keeps the place, and this reader reads any record. Whoever wants the page's form asks "the
record is empty" beside it.
The reader does not refuse a run's value of 32 zero bytes (R4.5's end): that is a test of the
verifier, not of the spelling. This file says nothing on what statement and record hold (lists of
items: R4.1, R4.2).

Terms: lean/GLOSSARY.md.
-/
import Fmt.Rules4
import Fmt.Rules1Only

set_option autoImplicit false

namespace Fmt

/-- what is hashed for a chain's first value, as data: parameters' digest, statement, record, the
run's value if there is one -/
abbrev First : Type := ByteArray × ByteArray × ByteArray × Option ByteArray

/-- the values that have a spelling: digests of 32 bytes; lengths that are words -/
def First.ok (x : First) : Prop :=
  x.1.size = 32 ∧ x.2.1.size < 2 ^ 64 ∧ x.2.2.1.size < 2 ^ 64 ∧ ∀ r, x.2.2.2 = some r → r.size = 32

/-- the same as a test that computes -/
def First.okB (x : First) : Bool :=
  x.1.size == 32 && decide (x.2.1.size < 2 ^ 64) && decide (x.2.2.1.size < 2 ^ 64) && (match x.2.2.2 with
    | none => true
    | some r => r.size == 32)

theorem First.okB_iff (x : First) : x.okB = true ↔ x.ok := by
  obtain ⟨pd, st, rc, run⟩ := x
  unfold First.okB First.ok
  cases run with
  | none => simp [and_assoc]
  | some r => simp [and_assoc]

instance (x : First) : Decidable x.ok := decidable_of_iff _ (First.okB_iff x)

/-- the last part: the word 0; or the word 1 and the run's value -/
def optRun : Option ByteArray → ByteArray
  | none => u64n 0
  | some r => u64n 1 ++ r

/-- its reader: a word 0 or 1, every other refused; behind 1: 32 bytes -/
def rdOptRun : Rd (Option ByteArray) := fun b i =>
  match rdBool b i with
  | some (false, j) => some (none, j)
  | some (true, j) =>
    match rdDigest b j with
    | some (r, k) => some (some r, k)
    | none => none
  | none => none

/-- The reader. -/
def rdFirst : Rd First := rdPair rdDigest (rdPair rdText (rdPair rdText rdOptRun))

/-- The reader on a whole string: refused if bytes are left. -/
def readFirst (b : ByteArray) : Option First := whole rdFirst b

/-- the spelling, from the parts' spellings -/
def spFirst : First → ByteArray := pair id (pair text (pair text optRun))

theorem firstBytes_eq (pd st rc : ByteArray) (run : Option ByteArray) :
    firstBytes pd st rc run = spFirst (pd, st, rc, run) := by
  unfold firstBytes spFirst pair text optRun
  cases run <;> simp only [id, ByteArray.append_assoc]

theorem undoes_optRun : Undoes rdOptRun optRun fun x => ∀ r, x = some r → r.size = 32 := by
  intro x hx pre post
  unfold rdOptRun
  cases x with
  | none =>
    have h := undoes_bool false trivial pre post
    have e : optRun none = bool false := rfl
    rw [e, h]
  | some r =>
    have e : optRun (some r) = bool true ++ r := rfl
    have e1 : pre ++ (bool true ++ r) ++ post = pre ++ bool true ++ (r ++ post) := by
      simp only [ByteArray.append_assoc]
    have e2 : pre ++ (bool true ++ r) ++ post = (pre ++ bool true) ++ r ++ post := by
      simp only [ByteArray.append_assoc]
    have h1 := undoes_bool true trivial pre (r ++ post)
    have h2 := undoes_digest r (hx r rfl) (pre ++ bool true) post
    simp only [id] at h2
    rw [ByteArray.size_append] at h2
    rw [← e1] at h1
    rw [← e2] at h2
    rw [e, h1]
    simp only
    rw [h2, ByteArray.size_append, Nat.add_assoc]

theorem only_optRun : Only rdOptRun optRun fun x => ∀ r, x = some r → r.size = 32 := by
  intro b i x j h
  unfold rdOptRun at h
  rcases hb : rdBool b i with _ | ⟨v, k⟩
  · rw [hb] at h
    exact absurd h (by simp)
  · rw [hb] at h
    obtain ⟨-, a2, a3, a4⟩ := only_bool b i v k hb
    cases v with
    | false =>
      simp only at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      exact ⟨fun r e => absurd e (by simp), a2, a3, a4⟩
    | true =>
      simp only at h
      rcases hd : rdDigest b k with _ | ⟨r, l⟩
      · rw [hd] at h
        exact absurd h (by simp)
      · rw [hd] at h
        simp only at h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
        obtain ⟨c1, c2, c3, c4⟩ := only_digest b k r l hd
        simp only [id] at c2 c4
        have e : optRun (some r) = bool true ++ r := rfl
        refine ⟨fun r' e' => by rw [← Option.some.inj e']; exact c1, ?_, c3, ?_⟩
        · rw [e, ByteArray.size_append, c2, a2, Nat.add_assoc]
        · rw [e, ByteArray.extract_eq_extract_append_extract k (by omega) (by omega), a4, c4]

theorem undoes_first : Undoes rdFirst spFirst First.ok := by
  have h :=
    undoes_pair undoes_digest (undoes_pair undoes_text (undoes_pair undoes_text undoes_optRun))
  intro x hx pre post
  exact h x hx pre post

theorem only_first : Only rdFirst spFirst First.ok := by
  have h := only_pair only_digest (only_pair only_text (only_pair only_text only_optRun))
  intro b i x j hh
  exact h b i x j hh

/-- (F1) What is hashed for the first value (`firstBytes`; under the hash's number 160 in
`firstValueW`, Fmt/Rules4.lean) is read back, on `First.ok`. -/
theorem readFirst_firstBytes
    (pd st rc : ByteArray) (run : Option ByteArray) (h : First.ok (pd, st, rc, run)) :
    readFirst (firstBytes pd st rc run) = some (pd, st, rc, run) := by
  rw [firstBytes_eq]
  exact whole_of_undoes undoes_first _ h

/-- (F2) What is read back is the spelling of what is returned. -/
theorem firstBytes_readFirst
    (b pd st rc : ByteArray) (run : Option ByteArray) (h : readFirst b = some (pd, st, rc, run)) :
    b = firstBytes pd st rc run ∧ First.ok (pd, st, rc, run) := by
  rw [firstBytes_eq]
  exact whole_only only_first b _ h

/-- (F3) One to one on `First.ok`. -/
theorem firstBytes_inj (pd st rc pd' st' rc' : ByteArray) (run run' : Option ByteArray)
    (h : First.ok (pd, st, rc, run)) (h' : First.ok (pd', st', rc', run'))
    (e : firstBytes pd st rc run = firstBytes pd' st' rc' run') :
    pd = pd' ∧ st = st' ∧ rc = rc' ∧ run = run' := by
  rw [firstBytes_eq, firstBytes_eq] at e
  have h1 := inj_of_undoes undoes_first _ _ h h' e
  simp only [Prod.mk.injEq] at h1
  exact h1

/-! ### Tests
The toy's first query (`Toy4`, Fmt/Rules4.lean) is read back; strings that are refused. -/

#guard readFirst (firstBytes (Toy4.pd .two) Toy4.statement ByteArray.empty (some (Toy4.run .two))) = some (Toy4.pd .two, Toy4.statement, ByteArray.empty, some (Toy4.run .two))
#guard readFirst (firstBytes (Toy4.pd .two) Toy4.statement (pattern 5) none) = some (Toy4.pd .two, Toy4.statement, pattern 5, none)
#guard First.okB (Toy4.pd .two, Toy4.statement, ByteArray.empty, some (Toy4.run .two)) && !First.okB (pattern 31, Toy4.statement, ByteArray.empty, none) && !First.okB (zero32, ByteArray.empty, ByteArray.empty, some (pattern 33))
#guard (readFirst ByteArray.empty).isNone && (readFirst (pattern 31)).isNone
#guard (readFirst (firstBytes (Toy4.pd .two) Toy4.statement ByteArray.empty none ++ pattern 1)).isNone    -- a byte is left
#guard (readFirst (zero32 ++ u64n 0 ++ u64n 0 ++ u64n 2)).isNone    -- the last word is neither 0 nor 1
#guard (readFirst (zero32 ++ u64n 0 ++ u64n 0 ++ u64n 1 ++ pattern 31)).isNone    -- a run's value of 31 bytes
#guard (readFirst (zero32 ++ u64n 9 ++ pattern 5)).isNone    -- a length beyond the end

end Fmt
