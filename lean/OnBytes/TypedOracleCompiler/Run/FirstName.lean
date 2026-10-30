-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/FirstName.lean: a partial code of a chain's first typed query that holds one outer
root, no instance and no salt, as the string of the format's call number 160 whose statement is a
stored table's NAME: the first call of the chain from which the seeds of a table's record are drawn.

Why. The seeds of a stored table's record are drawn on a chain of hash calls of its own. Its first
value is a hash of 32 zero bytes in the place of the parameters' digest, the table's name as the
statement, an empty record, and no run's value, under a label of its own (`Fmt.recordLabel`,
`Fmt.recordFirstW`, `Fmt.tableName`, library, Fmt/Rules4.lean). A name is the root, then the
configuration's digest and six words, which do not hang on the table. In the sibling (a second
form of the library's soundness road, under OnBytes/TypedOracleCompiler/) that chain is typed as a protocol of its
own, whose first query has the head `.f1 [cm] none []`. OnBytes/TypedOracleCompiler/Run/FirstAnswers.lean has the
like for a first query with a root and answers.
 - `stmN rest`, `unstmN rest`, with both laws: the statement's bytes of a root: the root's 32 bytes,
   then the fixed bytes `rest`; and back;
 - `restOf`, `tableName_eq`: at `rest := restOf cfg …` that is the format's name of the table;
 - `selN`, `mkN`, with their laws: a typed query of round 0 with the head `.f1 [cm] none []`, no
   root of the round's own and the round's fixed plain part, as (pd, cm, []), and back;
 - `firstPN`: the library's `pFirst0` along these, for `rest` of fewer than 2 ^ 32 bytes and a test
   that tells the round's fixed plain part; `firstPN_put`: what it writes is the bits of the
   format's string of the call number 160; `firstPN_hdr`: every string begins with that call's
   header;
 - `firstPN_name`: at the label of the seeds' chain, at a pd whose bytes are 32 zero bytes (`zeroPd`
   is one: `zeroPd_bytes`), at `restOf`, for a configuration's digest of fewer than 2 ^ 31 bytes:
   the string is the format's string of the call number 160 under `Fmt.recordLabel` on
   `Fmt.firstBytes Fmt.zero32 name ByteArray.empty none`, with name the table's `Fmt.tableName`.

The interface L, the tag, the fixed plain part with its test, the label, `rest` and the digest pd
are parameters.

Main definitions: `stmN`, `unstmN`, `restOf`, `selN`, `mkN`, `firstPN`, `zeroPd`.
Main theorems: `unstm_stmN`, `stm_unstmN`, `tableName_eq`, `firstPN_put`, `firstPN_hdr`,
`firstPN_name`.

Not claimed. A CODE, NO PAGE: that its strings are apart from those of other codes is not said. The
string is that of the chain's first VALUE: the other blocks of the typed answer of round 0 have no
string. The chain's second query (the drawing round) has no code here. A first query with a salt, an
instance, several outer roots or none is not written. That any program hashes this string is not
shown here; that it is the string which another file of this tree writes out for the seeds' first
value is to be held there. Nothing on any hash. Nothing on soundness. The compiler under
OnBytes/TypedOracleCompiler/ is the one that `innerCompiledVerifier` is made with; it builds on definitions of
Compile/.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Compile.Batch.Oracles
import Run.CodingPage162
import Run.Toy1TieTree
import Fmt.Rules1Laws

set_option autoImplicit false

namespace TypedOracleCompiler.Run.FirstName
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run

/-! ## The statement: a root, then fixed bytes -/

variable (rest : ByteArray)

/-- The statement's bytes, of a root: the root's 32 bytes, then the fixed bytes. -/
def stmN : Option (Dig 256) → Option ByteArray
  | some cm => some (digToBytes cm ++ rest)
  | none => none

/-- The root, of the statement's bytes: the first 32 bytes are read, and what was read is kept only
if its own spelling is the string. -/
def unstmN (b : ByteArray) : Option (Option (Dig 256)) :=
  match _root_.Fmt.rdDigest b 0 with
  | some v =>
      if stmN rest (some (bytesToDig v.1)) = some b then some (some (bytesToDig v.1)) else none
  | none => none

/-- The reading undoes the spelling. -/
theorem unstm_stmN (x : Option (Dig 256)) (b : ByteArray) (h : stmN rest x = some b) :
    unstmN rest b = some x := by
  cases x with
  | none => cases h
  | some cm =>
      have hb : digToBytes cm ++ rest = b := Option.some.inj h
      have r1 := _root_.Fmt.undoes_digest (digToBytes cm) (size_digToBytes cm) ByteArray.empty rest
      have e0 : ByteArray.empty ++ id (digToBytes cm) ++ rest = b := by
        rw [ByteArray.empty_append]
        exact hb
      rw [e0] at r1
      unfold unstmN
      have r2 : _root_.Fmt.rdDigest b 0 = some (digToBytes cm, 0 + (digToBytes cm).size) := r1
      rw [r2]
      dsimp only
      rw [TieTree.bytes_dig, if_pos h]

/-- The spelling undoes the reading. -/
theorem stm_unstmN (b : ByteArray) (x : Option (Dig 256)) (h : unstmN rest b = some x) :
    stmN rest x = some b := by
  unfold unstmN at h
  split at h
  · split at h
    · rename_i he
      rw [← Option.some.inj h]
      exact he
    · cases h
  · cases h

/-- What stands behind the root in a stored table's name: the configuration's digest and six
words. -/
def restOf (cfg : ByteArray) (a message tail logRows answers saltBytes : ℕ) : ByteArray :=
  cfg ++ _root_.Fmt.u64n a ++ _root_.Fmt.u64n message ++ _root_.Fmt.u64n tail ++
    _root_.Fmt.u64n logRows ++ _root_.Fmt.u64n answers ++ _root_.Fmt.u64n saltBytes

/-- The format's name of a stored table is its root, then these bytes. -/
theorem tableName_eq (root cfg : ByteArray) (a message tail logRows answers saltBytes : ℕ) :
    _root_.Fmt.tableName root cfg a message tail logRows answers saltBytes =
      root ++ restOf cfg a message tail logRows answers saltBytes := by
  unfold _root_.Fmt.tableName restOf
  simp only [ByteArray.append_assoc]

/-! ## The typed first query -/

variable {I X : Type} (L : BatchProtocolWithLeafBody I X) (t : Tag) (p0 : PlainPart (shapeOf L t) (annOf L t))
  (isP0 : PlainPart (shapeOf L t) (annOf L t) → Bool) (pd : Dig 256)

/-- A chain query of round 0 in the first format, with ONE outer root, no instance, no salt, no root
of the round's own and the round's fixed plain part, as (pd, root, no salt). -/
def selN (q : FbIn 256 L t) : Option (Dig 256 × Option (Dig 256) × List Bool) :=
  match q.round, q.head, q.rt with
  | 0, .f1 [cm] none [], [] => if isP0 q.plain = true then some (pd, some cm, []) else none
  | _, _, _ => none

/-- The way back: refused if the first digest is not pd, there is no root, or there is a salt. -/
def mkN (a : Dig 256 × Option (Dig 256) × List Bool) : Option (FbIn 256 L t) :=
  match a.2.1, a.2.2 with
  | some cm, [] => if a.1 = pd then some ⟨0, .f1 [cm] none [], [], p0⟩ else none
  | _, _ => none

variable (hp : ∀ p, isP0 p = true ↔ p = p0)

include hp in
/-- What `selN` reads: the query's fields. -/
theorem selN_some (q : FbIn 256 L t) (a : Dig 256 × Option (Dig 256) × List Bool)
    (h : selN L t isP0 pd q = some a) :
    ∃ cm, q = ⟨0, .f1 [cm] none [], [], p0⟩ ∧ a = (pd, some cm, []) := by
  obtain ⟨round, head, rt, plain⟩ := q
  unfold selN at h
  split at h
  · rename_i cm e1 e2 e3
    have e1' : round = 0 := e1
    have e2' : head = .f1 [cm] none [] := e2
    have e3' : rt = [] := e3
    by_cases hq : isP0 plain = true
    · have h' : (if isP0 plain = true then some (pd, some cm, ([] : List Bool)) else none) =
          some a := h
      rw [if_pos hq] at h'
      refine ⟨cm, ?_, (Option.some.inj h').symm⟩
      rw [e1', e2', e3', (hp plain).1 hq]
    · have h' : (if isP0 plain = true then some (pd, some cm, ([] : List Bool)) else none) =
          some a := h
      rw [if_neg hq] at h'
      cases h'
  · cases h

include hp in
/-- The way back undoes `selN`. -/
theorem mkN_selN (q : FbIn 256 L t) (a : Dig 256 × Option (Dig 256) × List Bool)
    (h : selN L t isP0 pd q = some a) : mkN L t p0 pd a = some q := by
  obtain ⟨cm, rfl, rfl⟩ := selN_some L t p0 isP0 pd hp q a h
  exact if_pos rfl

include hp in
/-- `selN` undoes the way back. -/
theorem selN_mkN (a : Dig 256 × Option (Dig 256) × List Bool) (q : FbIn 256 L t)
    (h : mkN L t p0 pd a = some q) : selN L t isP0 pd q = some a := by
  obtain ⟨p, x, salt⟩ := a
  cases x with
  | none => cases h
  | some cm =>
    cases salt with
    | cons _ _ => cases h
    | nil =>
      have h0 : (if p = pd then
          some (⟨0, .f1 [cm] none [], [], p0⟩ : FbIn 256 L t) else none) = some q := h
      by_cases hpd : p = pd
      · rw [if_pos hpd] at h0
        rw [← Option.some.inj h0, hpd]
        show (if isP0 p0 = true then some (pd, some cm, ([] : List Bool)) else none) = _
        rw [if_pos ((hp p0).2 rfl)]
      · rw [if_neg hpd] at h0
        cases h0

variable (lab : ℕ)

/-- The library's code of a first call, on (digest, root, salt). -/
def first0N : PCode (Dig 256 × Option (Dig 256) × List Bool) :=
  pFirst0 lab (stmN rest) (unstmN rest) (unstm_stmN rest) (stm_unstmN rest)

/-- The first chain query with one outer root, no instance and no salt. -/
def firstPN : PCode (FbIn 256 L t) :=
  (first0N rest lab).pull (selN L t isP0 pd) (mkN L t p0 pd) (mkN_selN L t p0 isP0 pd hp)
    (selN_mkN L t p0 isP0 pd hp)

/-- What it writes is the string of the format's call number 160, for fixed bytes of fewer than
2 ^ 32: under the label lab, with pd in the place of the parameters' digest, the root and the fixed
bytes as the statement, an empty record, and no run's value. -/
theorem firstPN_put (cm : Dig 256) (hr : rest.size < 2 ^ 32) :
    (firstPN rest L t p0 isP0 pd hp lab).put ⟨0, .f1 [cm] none [], [], p0⟩ =
      some (bytesToBits (_root_.Fmt.oStr 0 160 0 lab _root_.Fmt.zero32
        (_root_.Fmt.firstBytes (digToBytes pd) (digToBytes cm ++ rest) ByteArray.empty none))) := by
  have hs : selN L t isP0 pd (⟨0, .f1 [cm] none [], [], p0⟩ : FbIn 256 L t) =
      some (pd, some cm, []) := if_pos ((hp p0).2 rfl)
  show (selN L t isP0 pd _).bind _ = _
  rw [hs]
  exact pFirst0_put lab (stmN rest) (unstmN rest) (unstm_stmN rest) (stm_unstmN rest) pd (some cm)
    [] _ rfl (by rw [ByteArray.size_append, size_digToBytes]; omega) (Or.inl rfl)

/-- Every string that it writes begins with the header of the call number 160 under that label. -/
theorem firstPN_hdr (q : FbIn 256 L t) (s : List Bool)
    (h : (firstPN rest L t p0 isP0 pd hp lab).put q = some s) : ∃ r, s = hdr160 lab ++ r := by
  obtain ⟨a, -, ha⟩ := PCode.pull_put _ _ _ _ _ q s h
  exact pFirst0_hdr _ _ _ _ _ a s ha

/-- The digest of 256 zero bits. -/
def zeroPd : Dig 256 := bytesToDig _root_.Fmt.zero32

/-- Its bytes are the format's 32 zero bytes. -/
theorem zeroPd_bytes : digToBytes zeroPd = _root_.Fmt.zero32 := TieTree.dig_bytes _ rfl

/-- At the label of the chain of a record's seeds, with 32 zero bytes in the place of the
parameters' digest: the string of that chain's first value, at the table's name. Asked: pd's bytes
are 32 zero bytes; the configuration's digest has fewer than 2 ^ 31 bytes. -/
theorem firstPN_name (cm : Dig 256) (cfg : ByteArray) (a message tail logRows answers saltBytes : ℕ)
    (hz : digToBytes pd = _root_.Fmt.zero32) (hc : cfg.size < 2 ^ 31) :
    (firstPN (restOf cfg a message tail logRows answers saltBytes) L t p0 isP0 pd hp
        _root_.Fmt.recordLabel).put ⟨0, .f1 [cm] none [], [], p0⟩ =
      some (bytesToBits (_root_.Fmt.oStr 0 160 0 _root_.Fmt.recordLabel _root_.Fmt.zero32
        (_root_.Fmt.firstBytes _root_.Fmt.zero32
          (_root_.Fmt.tableName (digToBytes cm) cfg a message tail logRows answers saltBytes)
          ByteArray.empty none))) := by
  rw [firstPN_put _ L t p0 isP0 pd hp _ cm (by
    unfold restOf
    simp only [ByteArray.size_append]
    have h8 : ∀ x : ℕ, (_root_.Fmt.u64n x).size = 8 := fun _ => rfl
    simp only [h8]
    omega), hz, tableName_eq]

end TypedOracleCompiler.Run.FirstName
