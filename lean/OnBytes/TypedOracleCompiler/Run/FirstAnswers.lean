-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/FirstAnswers.lean: a partial code of a chain's first typed query that holds one
outer root and, in the place of an instance, a list of a stored table's answers (with a fixed value
beside it), as the string of the format's call number 160.

"The library" is the Lean library of the soundness road (Iop/, Compile/, Run/, Fmt/); "the sibling"
is a second form of that road under OnBytes/TypedOracleCompiler/.

Why. A chain's first value is a hash of the parameters' digest, the statement, an empty field and
the run's value (Fmt/Rules4.lean: `firstBytes`). Where a chain reads a stored table, its statement
holds the table's item: the root and the list of the answers of the table's record (`tableItem`).
The library's code of a first query (Run/CodingPage160.lean: `pFirst`) takes the head
`.f1 [pd] x salt`, with the parameters' digest as the one digest of the list and the whole statement
as x. In the frame with a stored table as the external string the list holds the table's ROOT, and
the parameters' digest is a fixed value beside the code. OnBytes/TypedOracleCompiler/Run/PageXFit.lean has that case
for two roots and no instance. This file has it for one root and an instance. TWO ROOTS WITH ANSWERS
(an entry's chain where tables have records) is had by neither. What a first query holds in that
place is `early x` of an instance x (`recomputeChain`, OnBytes/TypedOracleCompiler/Compile/Batch/Verifier.lean): an
interface's instances are here pairs of a list of triples of words and a value in a type Sd, for an
`early` that puts a fixed value d in the place of the second part: a part of an instance that no
hash input holds (a record's seeds). With Sd a type of one element the instance is the list alone.
 - `T3`, `rdT3`, `rdVal`, `rdItem`, with `undoes_t3`, `undoes_val`, `undoes_item`: readers for three
   words, for an item's value (root, list of answers) and for an item (name, value); each undoes the
   format's spelling (Fmt/Rules1Laws.lean: `Undoes`). No test on the words: an answer need not be in
   canonical form;
 - `stmA name`, `unstmA name`, `unstm_stmA`, `stm_unstmA`: the statement of a root and fewer than 2
   ^ 32 answers, its reader, and both laws. The reader keeps what it has read only if its own
   spelling is the string;
 - `selA`, `mkA`, with their laws: a typed query of round 0 with the head
   `.f1 [cm] (some (x, d)) salt`, no root of the round's own and the round's fixed plain part, as
   (pd, (cm, x), salt), and back; a query with another value than d beside the answers is not read;
 - `firstPA`: the library's `pFirst0` along these, for an item's name of fewer than 2 ^ 32 bytes and
   a test that tells the round's fixed plain part; `firstPA_put`: for fewer than 2 ^ 32 answers and
   a salt that is empty or has 256 bits, what it writes is the bits of the format's string of the
   call number 160; `firstPA_hdr`: every string begins with that call's header.

The interface L, the type Sd with d and a test for d, the tag, the fixed plain part with its test,
the label, the item's name and the digest pd are parameters.

Main definitions: `T3`, `rdT3`, `rdVal`, `rdItem`, `stmA`, `unstmA`, `selA`, `mkA`, `first0A`,
`firstPA`.
Main theorems: `undoes_t3`, `undoes_val`, `undoes_item`, `unstm_stmA`, `stm_unstmA`, `selA_some`,
`mkA_selA`, `selA_mkA`, `firstPA_put`, `firstPA_hdr`.

Not claimed. A CODE, NO PAGE: it is put into no page of codes, and no implementation of typed
oracles is made of it. A statement of ONE item alone: a chain whose statement holds further items (a
binding tree's root, seals, a request) is not served. That any program's statement is `tableItem` at
some name is not shown here (by its text, of the statements in OnBytes/Params/Chains.lean the one of
a key's one-time chain alone has this form, at the name "table"). The seeds of a record stand in no
statement, and not in this code. The string is that of the chain value of the answer; the blocks of
a verifier's message of round 0 have no string. Nothing on soundness. The compiler under
OnBytes/TypedOracleCompiler/ is the one that `innerCompiledVerifier` is made with; it builds on definitions of
Compile/.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Compile.Batch.Oracles
import Run.CodingPage162
import Run.Toy1TieTree
import Fmt.Rules1Laws

set_option autoImplicit false

namespace TypedOracleCompiler.Run.FirstAnswers
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run

/-! ## The statement: one stored table's item, with its answers -/

/-- A word's spelling has eight bytes. -/
theorem size_u64n (x : ℕ) : (_root_.Fmt.u64n x).size = 8 := rfl

/-- An answer as the format spells it: three words. -/
abbrev T3 : Type := UInt64 × UInt64 × UInt64

/-- Reads three words. No test on the words. -/
def rdT3 : _root_.Fmt.Rd T3 :=
  _root_.Fmt.rdPair _root_.Fmt.rdWord (_root_.Fmt.rdPair _root_.Fmt.rdWord _root_.Fmt.rdWord)

/-- It undoes the format's spelling of an element of the extension field, at all words. -/
theorem undoes_t3 : _root_.Fmt.Undoes rdT3 _root_.Fmt.ext fun _ => True := by
  have h := _root_.Fmt.undoes_pair _root_.Fmt.undoes_word
    (_root_.Fmt.undoes_pair _root_.Fmt.undoes_word _root_.Fmt.undoes_word)
  intro e _ pre post
  have e0 : _root_.Fmt.ext e =
      _root_.Fmt.pair _root_.Fmt.u64 (_root_.Fmt.pair _root_.Fmt.u64 _root_.Fmt.u64) e := by
    unfold _root_.Fmt.ext _root_.Fmt.pair
    rw [ByteArray.append_assoc]
  rw [e0]
  exact h e ⟨trivial, trivial, trivial⟩ pre post

/-- Reads the value of a stored table's item: the root as a string of bytes, the list of answers. -/
def rdVal : _root_.Fmt.Rd (ByteArray × List T3) :=
  _root_.Fmt.rdPair _root_.Fmt.rdText (_root_.Fmt.rdList rdT3)

/-- It undoes the spelling of a root of fewer than 2 ^ 64 bytes and of fewer than 2 ^ 64 answers. -/
theorem undoes_val : _root_.Fmt.Undoes rdVal
    (_root_.Fmt.pair _root_.Fmt.text (_root_.Fmt.list _root_.Fmt.ext))
    fun v => v.1.size < 2 ^ 64 ∧ v.2.length < 2 ^ 64 ∧ ∀ x ∈ v.2, True :=
  _root_.Fmt.undoes_pair _root_.Fmt.undoes_text
    (_root_.Fmt.undoes_list undoes_t3 fun x _ => by
      unfold _root_.Fmt.ext
      simp only [ByteArray.size_append, _root_.Fmt.size_u64]
      omega)

/-- Reads an item: its name and its value, two strings of bytes. -/
def rdItem : _root_.Fmt.Rd (ByteArray × ByteArray) :=
  _root_.Fmt.rdPair _root_.Fmt.rdText _root_.Fmt.rdText

/-- It undoes the spelling of a name and a value of fewer than 2 ^ 64 bytes each. -/
theorem undoes_item : _root_.Fmt.Undoes rdItem
    (_root_.Fmt.pair _root_.Fmt.text _root_.Fmt.text)
    fun v => v.1.size < 2 ^ 64 ∧ v.2.size < 2 ^ 64 :=
  _root_.Fmt.undoes_pair _root_.Fmt.undoes_text _root_.Fmt.undoes_text

variable (name : String)

/-- The statement's bytes, of a root and a list of answers: the format's item of a stored table
under the given name. Nothing for 2 ^ 32 answers or more. -/
def stmA : Option (Dig 256 × List T3) → Option ByteArray
  | some r =>
      if r.2.length < 2 ^ 32 then some (_root_.Fmt.tableItem name (digToBytes r.1) r.2) else none
  | none => none

/-- Root and answers, of the statement's bytes: the item's value is read, and what was read is kept
only if its own spelling is the string. -/
def unstmA (b : ByteArray) : Option (Option (Dig 256 × List T3)) :=
  match _root_.Fmt.whole rdItem b with
  | some v =>
      match _root_.Fmt.whole rdVal v.2 with
      | some w =>
          if stmA name (some (bytesToDig w.1, w.2)) = some b then some (some (bytesToDig w.1, w.2))
          else none
      | none => none
  | none => none

/-- The size of the list's spelling. -/
theorem size_listExt : ∀ l : List T3,
    (_root_.Fmt.cat (l.map _root_.Fmt.ext)).size = 24 * l.length
  | [] => rfl
  | x :: l => by
      rw [List.map_cons, _root_.Fmt.cat_cons, ByteArray.size_append, size_listExt l,
        List.length_cons]
      unfold _root_.Fmt.ext
      simp only [ByteArray.size_append, _root_.Fmt.size_u64]
      omega

/-- The reading undoes the spelling, if the name has fewer than 2 ^ 32 bytes. -/
theorem unstm_stmA (hn : (_root_.Fmt.ascii name).size < 2 ^ 32) (x : Option (Dig 256 × List T3))
    (b : ByteArray) (h : stmA name x = some b) : unstmA name b = some x := by
  cases x with
  | none => cases h
  | some r =>
      have h0 : (if r.2.length < 2 ^ 32 then
          some (_root_.Fmt.tableItem name (digToBytes r.1) r.2) else none) = some b := h
      by_cases hl : r.2.length < 2 ^ 32
      · rw [if_pos hl] at h0
        have hb := Option.some.inj h0
        have hv : (_root_.Fmt.pair _root_.Fmt.text (_root_.Fmt.list _root_.Fmt.ext)
            (digToBytes r.1, r.2)).size < 2 ^ 64 := by
          unfold _root_.Fmt.pair _root_.Fmt.text _root_.Fmt.list
          simp only [ByteArray.size_append, size_u64n, size_digToBytes, size_listExt]
          omega
        have e1 : b = _root_.Fmt.pair _root_.Fmt.text _root_.Fmt.text (_root_.Fmt.ascii name,
            _root_.Fmt.pair _root_.Fmt.text (_root_.Fmt.list _root_.Fmt.ext)
              (digToBytes r.1, r.2)) := by
          rw [← hb]
          unfold _root_.Fmt.tableItem _root_.Fmt.item _root_.Fmt.textS _root_.Fmt.pair
          unfold _root_.Fmt.text
          simp only [ByteArray.append_assoc]
        have r1 := _root_.Fmt.whole_of_undoes undoes_item (_root_.Fmt.ascii name,
          _root_.Fmt.pair _root_.Fmt.text (_root_.Fmt.list _root_.Fmt.ext)
            (digToBytes r.1, r.2))
          ⟨(by show (_root_.Fmt.ascii name).size < 2 ^ 64; omega), hv⟩
        have r2 := _root_.Fmt.whole_of_undoes undoes_val (digToBytes r.1, r.2)
          ⟨by rw [size_digToBytes]; omega, (by show r.2.length < 2 ^ 64; omega), fun _ _ => trivial⟩
        unfold unstmA
        rw [e1, r1]
        dsimp only
        rw [r2]
        dsimp only
        rw [TieTree.bytes_dig, ← e1, if_pos h]
      · rw [if_neg hl] at h0
        cases h0

/-- The spelling undoes the reading. -/
theorem stm_unstmA (b : ByteArray) (x : Option (Dig 256 × List T3))
    (h : unstmA name b = some x) : stmA name x = some b := by
  unfold unstmA at h
  split at h
  · split at h
    · split at h
      · rename_i he
        rw [← Option.some.inj h]
        exact he
      · cases h
    · cases h
  · cases h

/-! ## The typed first query -/

/- Sd: the type of a part of an instance that the first query does not hold; d: the fixed value that
stands in its place in a query; isD: a test for d. -/
variable {I Sd : Type} (L : BatchProtocolWithLeafBody I (List T3 × Sd)) (t : Tag) (p0 : PlainPart (shapeOf L t) (annOf L t))
  (isP0 : PlainPart (shapeOf L t) (annOf L t) → Bool) (d : Sd) (isD : Sd → Bool) (pd : Dig 256)

/-- A chain query of round 0 in the first format, with ONE outer root, a list of answers with d
beside it in the place of an instance, no root of the round's own and the round's fixed plain part,
as (pd, root and answers, salt). -/
def selA (q : FbIn 256 L t) : Option (Dig 256 × Option (Dig 256 × List T3) × List Bool) :=
  match q.round, q.head, q.rt with
  | 0, .f1 [cm] (some x) salt, [] =>
      if isP0 q.plain = true ∧ isD x.2 = true then some (pd, some (cm, x.1), salt) else none
  | _, _, _ => none

/-- The way back: refused if the first digest is not pd, or there is no root. -/
def mkA (a : Dig 256 × Option (Dig 256 × List T3) × List Bool) : Option (FbIn 256 L t) :=
  match a.2.1 with
  | some r => if a.1 = pd then some ⟨0, .f1 [r.1] (some (r.2, d)) a.2.2, [], p0⟩ else none
  | none => none

variable (hp : ∀ p, isP0 p = true ↔ p = p0) (hd : ∀ s, isD s = true ↔ s = d)

include hp hd in
/-- What `selA` reads: the query's fields. -/
theorem selA_some (q : FbIn 256 L t) (a : Dig 256 × Option (Dig 256 × List T3) × List Bool)
    (h : selA L t isP0 isD pd q = some a) :
    ∃ cm x salt, q = ⟨0, .f1 [cm] (some (x, d)) salt, [], p0⟩ ∧ a = (pd, some (cm, x), salt) := by
  obtain ⟨round, head, rt, plain⟩ := q
  unfold selA at h
  split at h
  · rename_i cm x salt e1 e2 e3
    have e1' : round = 0 := e1
    have e2' : head = .f1 [cm] (some x) salt := e2
    have e3' : rt = [] := e3
    by_cases hq : isP0 plain = true ∧ isD x.2 = true
    · have h' : (if isP0 plain = true ∧ isD x.2 = true then some (pd, some (cm, x.1), salt)
          else none) = some a := h
      rw [if_pos hq] at h'
      refine ⟨cm, x.1, salt, ?_, (Option.some.inj h').symm⟩
      have ex : x = (x.1, d) := Prod.ext rfl ((hd x.2).1 hq.2)
      rw [e1', e2', e3', (hp plain).1 hq.1, ← ex]
    · have h' : (if isP0 plain = true ∧ isD x.2 = true then some (pd, some (cm, x.1), salt)
          else none) = some a := h
      rw [if_neg hq] at h'
      cases h'
  · cases h

include hp hd in
/-- The way back undoes `selA`. -/
theorem mkA_selA (q : FbIn 256 L t) (a : Dig 256 × Option (Dig 256 × List T3) × List Bool)
    (h : selA L t isP0 isD pd q = some a) : mkA L t p0 d pd a = some q := by
  obtain ⟨cm, x, salt, rfl, rfl⟩ := selA_some L t p0 isP0 d isD pd hp hd q a h
  exact if_pos rfl

include hp hd in
/-- `selA` undoes the way back. -/
theorem selA_mkA (a : Dig 256 × Option (Dig 256 × List T3) × List Bool) (q : FbIn 256 L t)
    (h : mkA L t p0 d pd a = some q) : selA L t isP0 isD pd q = some a := by
  obtain ⟨p, x, salt⟩ := a
  cases x with
  | none => cases h
  | some r =>
      have h0 : (if p = pd then
          some (⟨0, .f1 [r.1] (some (r.2, d)) salt, [], p0⟩ : FbIn 256 L t) else none) = some q := h
      by_cases hpd : p = pd
      · rw [if_pos hpd] at h0
        rw [← Option.some.inj h0, hpd]
        show (if isP0 p0 = true ∧ isD d = true then some (pd, some (r.1, r.2), salt) else none) = _
        rw [if_pos ⟨(hp p0).2 rfl, (hd d).2 rfl⟩]
      · rw [if_neg hpd] at h0
        cases h0

variable (lab : ℕ) (hn : (_root_.Fmt.ascii name).size < 2 ^ 32)

/-- The library's code of a first call, on (digest, root and answers, salt). -/
def first0A : PCode (Dig 256 × Option (Dig 256 × List T3) × List Bool) :=
  pFirst0 lab (stmA name) (unstmA name) (unstm_stmA name hn) (stm_unstmA name)

/-- The first chain query with a list of answers in the place of an instance. A query whose
instance has another value than d beside the answers is not written. -/
def firstPA : PCode (FbIn 256 L t) :=
  (first0A name lab hn).pull (selA L t isP0 isD pd) (mkA L t p0 d pd)
    (mkA_selA L t p0 isP0 d isD pd hp hd) (selA_mkA L t p0 isP0 d isD pd hp hd)

/-- What it writes is the string of the format's call number 160, for fewer than 2 ^ 32 answers
and a salt that is empty or has 256 bits: under the label lab, with pd in the place of the
parameters' digest, the stored table's item of root and answers as the statement, an empty record,
and the salt as the run's value. -/
theorem firstPA_put (cm : Dig 256) (x : List T3) (salt : List Bool) (hx : x.length < 2 ^ 32)
    (hl : salt = [] ∨ salt.length = 256) :
    (firstPA name L t p0 isP0 d isD pd hp hd lab hn).put ⟨0, .f1 [cm] (some (x, d)) salt, [], p0⟩ =
      some (bytesToBits (_root_.Fmt.oStr 0 160 0 lab _root_.Fmt.zero32
        (_root_.Fmt.firstBytes (digToBytes pd) (_root_.Fmt.tableItem name (digToBytes cm) x)
          ByteArray.empty (runOf salt)))) := by
  have hs : selA L t isP0 isD pd (⟨0, .f1 [cm] (some (x, d)) salt, [], p0⟩ : FbIn 256 L t) =
      some (pd, some (cm, x), salt) := if_pos ⟨(hp p0).2 rfl, (hd d).2 rfl⟩
  show (selA L t isP0 isD pd _).bind _ = _
  rw [hs]
  refine pFirst0_put lab (stmA name) (unstmA name) (unstm_stmA name hn) (stm_unstmA name) pd
    (some (cm, x)) salt _ (if_pos hx) ?_ hl
  unfold _root_.Fmt.tableItem _root_.Fmt.item _root_.Fmt.textS _root_.Fmt.text _root_.Fmt.list
  simp only [ByteArray.size_append, size_u64n, size_digToBytes, size_listExt]
  omega

/-- Every string that it writes begins with the header of the call number 160 under that label. -/
theorem firstPA_hdr (q : FbIn 256 L t) (s : List Bool)
    (h : (firstPA name L t p0 isP0 d isD pd hp hd lab hn).put q = some s) :
    ∃ r, s = hdr160 lab ++ r := by
  obtain ⟨a, -, ha⟩ := PCode.pull_put _ _ _ _ _ q s h
  exact pFirst0_hdr _ _ _ _ _ a s ha

end TypedOracleCompiler.Run.FirstAnswers
