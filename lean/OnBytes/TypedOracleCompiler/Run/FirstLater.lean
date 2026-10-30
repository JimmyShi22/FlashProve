-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/FirstLater.lean: partial codes for the first values of a file's LATER chains, as
pairs (typed chain value, what a seam's plain part carries): the string of the format's hash under
the number 160, with the typed chain value as a part of the statement.

A key file has three chains. The shared chain's statement holds the table's item (root and answers)
and the binding tree's root; the second chain's statement holds the seals of the two earlier chains
(`Params.Shared.statement`, `Params.Second.statement`, OnBytes/Params/Chains.lean; library,
Fmt/Rules4.lean: `tableItem`, `item`, `bindRootName`, `sealItems`). In the sibling (a second
form of the library's soundness road, under OnBytes/TypedOracleCompiler/) the three are typed as one chain; the
first value of a later chain is the answer to a typed query at a seam (OnBytes/TypedOracleCompiler/Run/SeamAt.lean).
That query holds the chain value before it: the binding root, or the second seal. What else the
statement holds (root and answers; the first seal) and the chain's run value no later typed query
holds: the seam's plain part carries them.
 - `pFirstAt lab stm unstm h1 h2 pd`: the library's `pFirst0` along (chain value ρ of 256 bits, (y,
   run)) ↦ (pd, (ρ as a digest, y), run); `pFirstAt_str`: at a chain value of 256 bits, a statement
   of fewer than 2 ^ 64 bytes and a run value of 256 bits or none, it writes the bits of `Fmt.oStr`
   of the hash under 160 with the label lab, on `Fmt.firstBytes` of pd's bytes, the statement, an
   empty record and the run value or none; `pFirstAt_hdr`: every string that it writes begins with
   that call's header;
 - `item_eq`, `whole_two`: an item is a pair of two strings of bytes; two items in a row are read
   back, if names and values have fewer than 2 ^ 64 bytes;
 - `stm2 name`, `unstm2 name`, with both laws (the first for a name of fewer than 2 ^ 32 bytes): of
   (binding root, (root, answers)): the table's item under the name, then the binding root's item;
   `stm2_shared`: at the name "table", a table whose root is cm's bytes and fewer than 2 ^ 32
   answers, these are `Params.Shared.statement`'s bytes;
 - `stm3`, `unstm3`, with both laws: of (second seal, first seal): the two seals' items, the first
   seal first; `stm3_second`: these are `Params.Second.statement`'s bytes.

Main definitions: `pFirstAt`, `stm2`, `unstm2`, `stm3`, `unstm3`.
Main theorems: `pFirstAt_str`, `pFirstAt_hdr`, `unstm_stm2`, `stm_unstm2`, `unstm_stm3`,
`stm_unstm3`, `stm2_shared`, `stm3_second`.

Not claimed. CODES OF PAIRS, NO PAGE. Nothing asks that the root and the answers in a seam's plain
part are those of the chain's first query, nor that the first seal there is the first chain's: a
typing of a file puts the file's own there, and the protocol's verifier does not look at a seam.
That a run value is the hash that the format prescribes. That any program hashes these strings.
Nothing on any hash. Nothing on soundness. The compiler under OnBytes/TypedOracleCompiler/ is the one that
`innerCompiledVerifier` is made with; it builds on definitions of Compile/.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Run.FirstAnswers
import OnBytes.TypedOracleCompiler.Run.PutSome
import OnBytes.Params.Chains

set_option autoImplicit false

namespace TypedOracleCompiler.Run.FirstLater
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop
open TypedOracleCompiler.Run.PutSome TypedOracleCompiler.Run.FirstAnswers
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run

/-! ## The library's code of a first call, along a chain value -/

section
variable {Y : Type} (lab : ℕ) (stm : Option (Dig 256 × Y) → Option ByteArray)
  (unstm : ByteArray → Option (Option (Dig 256 × Y)))
  (h1 : ∀ x b, stm x = some b → unstm b = some x) (h2 : ∀ b x, unstm b = some x → stm x = some b)
  (pd : Dig 256)

/-- (chain value, (y, run)) as (pd, (the value as a digest, y), run). -/
def toF (a : Bits × (Y × Bits)) : Option (Dig 256 × Option (Dig 256 × Y) × List Bool) :=
  if a.1.length = 256 then some (pd, some (digOf a.1, a.2.1), a.2.2) else none

/-- And back: refused if the first digest is not pd or there is no statement's datum. -/
def ofF (t : Dig 256 × Option (Dig 256 × Y) × List Bool) : Option (Bits × (Y × Bits)) :=
  match t.2.1 with
  | some r => if t.1 = pd then some (List.ofFn r.1, (r.2, t.2.2)) else none
  | none => none

/-- The way back undoes the way there. -/
theorem ofF_toF (a : Bits × (Y × Bits)) (t : Dig 256 × Option (Dig 256 × Y) × List Bool)
    (h : toF pd a = some t) : ofF pd t = some a := by
  unfold toF at h
  by_cases hl : a.1.length = 256
  · rw [if_pos hl] at h
    rw [← Option.some.inj h]
    show (if pd = pd then some (List.ofFn (digOf a.1), (a.2.1, a.2.2)) else none) = some a
    rw [if_pos rfl, ofFn_digOf a.1 hl]
  · rw [if_neg hl] at h
    cases h

/-- The way there undoes the way back. -/
theorem toF_ofF (t : Dig 256 × Option (Dig 256 × Y) × List Bool) (a : Bits × (Y × Bits))
    (h : ofF pd t = some a) : toF pd a = some t := by
  obtain ⟨p, x, run⟩ := t
  cases x with
  | none => cases h
  | some r =>
    have h0 : (if p = pd then some (List.ofFn r.1, (r.2, run)) else none) = some a := h
    by_cases hp : p = pd
    · rw [if_pos hp] at h0
      rw [← Option.some.inj h0, hp]
      have hlen : (List.ofFn r.1).length = 256 := by rw [List.length_ofFn]
      have hd : digOf (List.ofFn r.1) = r.1 := digOf_ofFn r.1
      generalize List.ofFn r.1 = l at hlen hd ⊢
      unfold toF
      dsimp only
      rw [if_pos hlen, hd]
    · rw [if_neg hp] at h0
      cases h0

/-- The first value of a later chain, on (typed chain value, (y, run)). -/
def pFirstAt : PCode (Bits × (Y × Bits)) :=
  (pFirst0 lab stm unstm h1 h2).pull (toF pd) (ofF pd) (ofF_toF pd) (toF_ofF pd)

/-- What it writes is the format's string of the hash under 160, for a chain value of 256 bits,
a statement of fewer than 2 ^ 64 bytes, and a run value of 256 bits or none. -/
theorem pFirstAt_str (ρ : Bits) (hρ : ρ.length = 256) (y : Y) (run : Bits) (st : ByteArray)
    (hx : stm (some (digOf ρ, y)) = some st) (hs : st.size < 2 ^ 64)
    (hl : run = [] ∨ run.length = 256) :
    (pFirstAt lab stm unstm h1 h2 pd).put (ρ, (y, run)) =
      some (bytesToBits (_root_.Fmt.oStr 0 160 0 lab _root_.Fmt.zero32
        (_root_.Fmt.firstBytes (digToBytes pd) st ByteArray.empty (runOf run)))) :=
  pull_some _ _ _ _ _ _ _ _ (if_pos hρ) (pFirst0_put lab stm unstm h1 h2 pd _ run st hx hs hl)

/-- Every string that it writes begins with the header of the hash under 160 with that label. -/
theorem pFirstAt_hdr (a : Bits × (Y × Bits)) (s : List Bool)
    (h : (pFirstAt lab stm unstm h1 h2 pd).put a = some s) : ∃ r, s = hdr160 lab ++ r := by
  obtain ⟨t, -, ht⟩ := PCode.pull_put _ _ _ _ _ a s h
  exact pFirst0_hdr _ _ _ _ _ t s ht

end

/-! ## Two items in a row -/

/-- An item is its name and its value, two strings of bytes. -/
theorem item_eq (name : String) (v : ByteArray) :
    _root_.Fmt.item name v =
      _root_.Fmt.pair _root_.Fmt.text _root_.Fmt.text (_root_.Fmt.ascii name, v) := by
  unfold _root_.Fmt.item _root_.Fmt.textS _root_.Fmt.pair
  unfold _root_.Fmt.text
  simp only [ByteArray.append_assoc]

/-- Reads two items. -/
def rdTwo : _root_.Fmt.Rd ((ByteArray × ByteArray) × (ByteArray × ByteArray)) :=
  _root_.Fmt.rdPair rdItem rdItem

/-- Two items in a row are read back, if names and values have fewer than 2 ^ 64 bytes. -/
theorem whole_two (n1 n2 : String) (v1 v2 : ByteArray)
    (a1 : (_root_.Fmt.ascii n1).size < 2 ^ 64) (b1 : v1.size < 2 ^ 64)
    (a2 : (_root_.Fmt.ascii n2).size < 2 ^ 64) (b2 : v2.size < 2 ^ 64) :
    _root_.Fmt.whole rdTwo (_root_.Fmt.item n1 v1 ++ _root_.Fmt.item n2 v2) =
      some ((_root_.Fmt.ascii n1, v1), (_root_.Fmt.ascii n2, v2)) := by
  rw [item_eq, item_eq]
  exact _root_.Fmt.whole_of_undoes (_root_.Fmt.undoes_pair undoes_item undoes_item)
    ((_root_.Fmt.ascii n1, v1), (_root_.Fmt.ascii n2, v2)) ⟨⟨a1, b1⟩, ⟨a2, b2⟩⟩

/-! ## The shared chain's statement -/

variable (name : String)

/-- The statement's bytes, of (binding root, (root, answers)): the table's item under the given
name, then the binding root's item. Nothing for 2 ^ 32 answers or more. -/
def stm2 : Option (Dig 256 × (Dig 256 × List T3)) → Option ByteArray
  | some r =>
      if r.2.2.length < 2 ^ 32 then
        some (_root_.Fmt.tableItem name (digToBytes r.2.1) r.2.2 ++
          _root_.Fmt.item _root_.Fmt.bindRootName (digToBytes r.1))
      else none
  | none => none

/-- And back: two items are read, the first one's value as root and answers; what was read is kept
only if its own spelling is the string. -/
def unstm2 (b : ByteArray) : Option (Option (Dig 256 × (Dig 256 × List T3))) :=
  match _root_.Fmt.whole rdTwo b with
  | some v =>
      match _root_.Fmt.whole rdVal v.1.2 with
      | some w =>
          if stm2 name (some (bytesToDig v.2.2, (bytesToDig w.1, w.2))) = some b then
            some (some (bytesToDig v.2.2, (bytesToDig w.1, w.2)))
          else none
      | none => none
  | none => none

/-- The reading undoes the spelling, if the name has fewer than 2 ^ 32 bytes. -/
theorem unstm_stm2 (hn : (_root_.Fmt.ascii name).size < 2 ^ 32)
    (x : Option (Dig 256 × (Dig 256 × List T3))) (b : ByteArray) (h : stm2 name x = some b) :
    unstm2 name b = some x := by
  cases x with
  | none => cases h
  | some r =>
    have h0 : (if r.2.2.length < 2 ^ 32 then
        some (_root_.Fmt.tableItem name (digToBytes r.2.1) r.2.2 ++
          _root_.Fmt.item _root_.Fmt.bindRootName (digToBytes r.1)) else none) = some b := h
    by_cases hl : r.2.2.length < 2 ^ 32
    · rw [if_pos hl] at h0
      have hb := Option.some.inj h0
      have hv : (_root_.Fmt.pair _root_.Fmt.text (_root_.Fmt.list _root_.Fmt.ext)
          (digToBytes r.2.1, r.2.2)).size < 2 ^ 64 := by
        unfold _root_.Fmt.pair _root_.Fmt.text _root_.Fmt.list
        simp only [ByteArray.size_append, size_u64n, size_digToBytes, size_listExt]
        omega
      have et : _root_.Fmt.tableItem name (digToBytes r.2.1) r.2.2 =
          _root_.Fmt.item name (_root_.Fmt.pair _root_.Fmt.text (_root_.Fmt.list _root_.Fmt.ext)
            (digToBytes r.2.1, r.2.2)) := rfl
      have r1 := whole_two name _root_.Fmt.bindRootName
        (_root_.Fmt.pair _root_.Fmt.text (_root_.Fmt.list _root_.Fmt.ext)
          (digToBytes r.2.1, r.2.2)) (digToBytes r.1) (by omega) hv (by decide)
        (by rw [size_digToBytes]; omega)
      have r2 := _root_.Fmt.whole_of_undoes undoes_val (digToBytes r.2.1, r.2.2)
        ⟨by rw [size_digToBytes]; omega, (by show r.2.2.length < 2 ^ 64; omega),
          fun _ _ => trivial⟩
      rw [← et, hb] at r1
      unfold unstm2
      rw [r1]
      dsimp only
      rw [r2]
      dsimp only
      rw [TieTree.bytes_dig, TieTree.bytes_dig, if_pos h]
    · rw [if_neg hl] at h0
      cases h0

/-- The spelling undoes the reading. -/
theorem stm_unstm2 (b : ByteArray) (x : Option (Dig 256 × (Dig 256 × List T3)))
    (h : unstm2 name b = some x) : stm2 name x = some b := by
  unfold unstm2 at h
  split at h
  · split at h
    · split at h
      · rename_i he
        rw [← Option.some.inj h]
        exact he
      · cases h
    · cases h
  · cases h

/-! ## The second chain's statement -/

/-- The statement's bytes, of (second seal, first seal): the two seals' items, the first seal
first. -/
def stm3 : Option (Dig 256 × Dig 256) → Option ByteArray
  | some r => some (_root_.Fmt.sealItems [digToBytes r.2, digToBytes r.1])
  | none => none

/-- And back: two items are read; what was read is kept only if its own spelling is the string. -/
def unstm3 (b : ByteArray) : Option (Option (Dig 256 × Dig 256)) :=
  match _root_.Fmt.whole rdTwo b with
  | some v =>
      if stm3 (some (bytesToDig v.2.2, bytesToDig v.1.2)) = some b then
        some (some (bytesToDig v.2.2, bytesToDig v.1.2))
      else none
  | none => none

/-- Two seals' items, written out. -/
theorem sealItems_two (a b : ByteArray) :
    _root_.Fmt.sealItems [a, b] =
      _root_.Fmt.item "the seal of an earlier chain" a ++
        _root_.Fmt.item "the seal of an earlier chain" b := by
  unfold _root_.Fmt.sealItems
  rw [List.map_cons, List.map_cons, List.map_nil, _root_.Fmt.cat_cons, _root_.Fmt.cat_cons,
    _root_.Fmt.cat_nil, ByteArray.append_empty]
  rfl

/-- The reading undoes the spelling. -/
theorem unstm_stm3 (x : Option (Dig 256 × Dig 256)) (b : ByteArray) (h : stm3 x = some b) :
    unstm3 b = some x := by
  cases x with
  | none => cases h
  | some r =>
    have hb : _root_.Fmt.sealItems [digToBytes r.2, digToBytes r.1] = b := Option.some.inj h
    have r1 := whole_two "the seal of an earlier chain" "the seal of an earlier chain"
      (digToBytes r.2) (digToBytes r.1) (by decide) (by rw [size_digToBytes]; omega) (by decide)
      (by rw [size_digToBytes]; omega)
    rw [← sealItems_two, hb] at r1
    unfold unstm3
    rw [r1]
    dsimp only
    rw [TieTree.bytes_dig, TieTree.bytes_dig, if_pos h]

/-- The spelling undoes the reading. -/
theorem stm_unstm3 (b : ByteArray) (x : Option (Dig 256 × Dig 256)) (h : unstm3 b = some x) :
    stm3 x = some b := by
  unfold unstm3 at h
  split at h
  · split at h
    · rename_i he
      rw [← Option.some.inj h]
      exact he
    · cases h
  · cases h

/-! ## They are the program's statements -/

/-- At the name "table" the bytes are those of the program's statement of a shared chain, at a table
whose root is cm's bytes, with fewer than 2 ^ 32 answers. -/
theorem stm2_shared (br cm : Dig 256) (table : OnBytes.Params.TableName)
    (hr : table.root = digToBytes cm) (hl : (table.answers.map OnBytes.E.triple).length < 2 ^ 32) :
    stm2 "table" (some (br, (cm, table.answers.map OnBytes.E.triple))) =
      some (OnBytes.Params.Shared.statement table (digToBytes br)) := by
  show (if (table.answers.map OnBytes.E.triple).length < 2 ^ 32 then _ else none) = _
  rw [if_pos hl]
  unfold OnBytes.Params.Shared.statement
  rw [hr]

/-- The bytes are those of the program's statement of a second chain. -/
theorem stm3_second (s2 s1 : Dig 256) :
    stm3 (some (s2, s1)) =
      some (OnBytes.Params.Second.statement (digToBytes s1) (digToBytes s2)) := rfl

end TypedOracleCompiler.Run.FirstLater
