-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/IdRead.lean: a reader for the code of what enters the ID without seeds, so that the
first key of such an ID in a query log is found by a function in which nothing is taken by choice.

The ID without seeds is that of OnBytes/Tie/IdKey.lean: the hash of a string that leaves the
record's seeds out. It is not the programs' commitment ID, whose string holds them
(OnBytes/Key/Table.lean).

OnBytes/Tie/IdKey.lean codes the tables' shape, the digest of the public files and a table as one
bit string (`idCode`). The three together are a key (`IdKey`): the library's word for what a digest
stands for, not the key file. The library's `ZKCP.firstKey` looks in a query log for the first entry
with a given answer whose query is a key's code, and inverts the code by choice. Here the code is
inverted by a reader, `idRead`: it turns the bits into bytes, reads them as a string of the format's
oracle, reads a digest, a table's name and a list of answers out of its bytes, and a root and six
numbers out of the name; then it keeps the key that it has read only if that key's code is the very
string.

Main definitions: `nameParse`, `idParse`, `idRead`.
Main theorems.
- `idRead_iff`: `idRead s` is k exactly if the code of k is s. From left to right it holds by the
  last comparison in `idRead`; the content is from right to left: every code is read back
  (`idParse_idBytes`, `nameParse_tableName`).
- `firstKey_idRead`: `ZKCP.firstKey idCode d log` is the first value that `idRead` returns on a
  query of the log whose answer is d. It uses `keyOfCode_idRead`.

What is not claimed. Nothing on soundness and no probability. `idRead` refuses every string that is
no key's code: among these are bits that are no whole number of bytes, the second of the two strings
that the format's oracle has for a call, and strings that have the form of a call 179 and in which
the digest outside the table's name and the one inside it differ, or which hold a further byte. No
test here evaluates it. It is no part of the program, which is the Lean port built from OnBytes/.
All limits in the head of OnBytes/Tie/IdKey.lean hold here too. For proofs only; the program does
not import this file.

-/
import OnBytes.Tie.IdKey

set_option autoImplicit false

namespace OnBytes.Tie

/-- A reader of three words. -/
abbrev rdThree : Fmt.Rd (UInt64 × UInt64 × UInt64) :=
  Fmt.rdPair Fmt.rdWord (Fmt.rdPair Fmt.rdWord Fmt.rdWord)

/-- Reads a root, 32 further bytes and six words from the beginning of a string: the parts of a
table's name. The 32 further bytes are dropped here; `idRead` compares them through the code. -/
def nameParse (name : ByteArray) : Option (ByteArray × Params.IndexShape) := do
  let (root, a) ← Fmt.rdDigest name 0
  let (_, b) ← Fmt.rdDigest name a
  let (n1, c1) ← Fmt.rdWord name b
  let (n2, c2) ← Fmt.rdWord name c1
  let (n3, c3) ← Fmt.rdWord name c2
  let (n4, c4) ← Fmt.rdWord name c3
  let (n5, c5) ← Fmt.rdWord name c4
  let (n6, _) ← Fmt.rdWord name c5
  pure (root, ⟨⟨n1.toNat, n2.toNat, n3.toNat⟩, n4.toNat, n5.toNat, n6.toNat⟩)

/-- Reads a digest, a string with its length, and a list of triples of words, one after the other,
and the parts of a table's name out of the string: a key, if all readers succeed. Bytes behind the
list are not looked at here. -/
def idParse (B : ByteArray) : Option IdKey := do
  let (cfg, i) ← Fmt.rdDigest B 0
  let (name, j) ← Fmt.rdText B i
  let (ans, _) ← Fmt.rdList rdThree B j
  let (root, s) ← nameParse name
  pure (s, cfg, ⟨root, ans.map E.ofTriple⟩)

/-- The reader for `idCode`: bits to bytes, the bytes as a string of the format's oracle
(`Fmt.oParse`), a key out of its bytes (`idParse`), and then the test that the code of that key is
the string that was given. Nothing in it is taken by choice. -/
def idRead (s : ZKCP.Str) : Option IdKey :=
  match Fmt.oParse (Run.bitsToBytes s) with
  | none => none
  | some q =>
    match idParse q.bytes with
    | none => none
    | some k => if idCode k = some s then some k else none

/-- A number below 2^64 comes back from its word. -/
theorem toNat_ofNat_lt {x : Nat} (h : x < 2 ^ 64) : (UInt64.ofNat x).toNat = x := by
  rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt h]

/-- `nameParse` reads a table's name back, for a root and a digest of 32 bytes and six numbers below
2^64. -/
theorem nameParse_tableName (root cfg : ByteArray) (hr : root.size = 32) (hc : cfg.size = 32)
    (a1 a2 a3 a4 a5 a6 : Nat) (h1 : a1 < 2 ^ 64) (h2 : a2 < 2 ^ 64) (h3 : a3 < 2 ^ 64)
    (h4 : a4 < 2 ^ 64) (h5 : a5 < 2 ^ 64) (h6 : a6 < 2 ^ 64) :
    nameParse (Fmt.tableName root cfg a1 a2 a3 a4 a5 a6) =
      some (root, ⟨⟨a1, a2, a3⟩, a4, a5, a6⟩) := by
  have w : ∀ (pre post : ByteArray) (x : Nat),
      Fmt.rdWord (pre ++ Fmt.u64n x ++ post) pre.size = some (UInt64.ofNat x, pre.size + 8) :=
    fun pre post x => Fmt.undoes_word (UInt64.ofNat x) trivial pre post
  have d0 := Fmt.undoes_digest root hr ByteArray.empty
    (cfg ++ Fmt.u64n a1 ++ Fmt.u64n a2 ++ Fmt.u64n a3 ++ Fmt.u64n a4 ++ Fmt.u64n a5 ++ Fmt.u64n a6)
  have d1 := Fmt.undoes_digest cfg hc root
    (Fmt.u64n a1 ++ Fmt.u64n a2 ++ Fmt.u64n a3 ++ Fmt.u64n a4 ++ Fmt.u64n a5 ++ Fmt.u64n a6)
  have w1 := w (root ++ cfg)
    (Fmt.u64n a2 ++ Fmt.u64n a3 ++ Fmt.u64n a4 ++ Fmt.u64n a5 ++ Fmt.u64n a6) a1
  have w2 := w (root ++ cfg ++ Fmt.u64n a1)
    (Fmt.u64n a3 ++ Fmt.u64n a4 ++ Fmt.u64n a5 ++ Fmt.u64n a6) a2
  have w3 := w (root ++ cfg ++ Fmt.u64n a1 ++ Fmt.u64n a2)
    (Fmt.u64n a4 ++ Fmt.u64n a5 ++ Fmt.u64n a6) a3
  have w4 := w (root ++ cfg ++ Fmt.u64n a1 ++ Fmt.u64n a2 ++ Fmt.u64n a3)
    (Fmt.u64n a5 ++ Fmt.u64n a6) a4
  have w5 := w (root ++ cfg ++ Fmt.u64n a1 ++ Fmt.u64n a2 ++ Fmt.u64n a3 ++ Fmt.u64n a4)
    (Fmt.u64n a6) a5
  have w6 := w
    (root ++ cfg ++ Fmt.u64n a1 ++ Fmt.u64n a2 ++ Fmt.u64n a3 ++ Fmt.u64n a4 ++ Fmt.u64n a5)
    ByteArray.empty a6
  simp only [id, ByteArray.empty_append, ByteArray.append_empty, ByteArray.size_empty,
    ByteArray.size_append, Fmt.size_u64n, hr, hc, Nat.zero_add, ← ByteArray.append_assoc]
    at d0 d1 w1 w2 w3 w4 w5 w6
  unfold nameParse Fmt.tableName
  simp only [d0, d1, w1, w2, w3, w4, w5, w6, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
    toNat_ofNat_lt h1, toNat_ofNat_lt h2, toNat_ofNat_lt h3, toNat_ofNat_lt h4, toNat_ofNat_lt h5,
    toNat_ofNat_lt h6]

/-- Within `idOk`, `idParse` reads a key back from its bytes. -/
theorem idParse_idBytes {k : IdKey} (h : idOk k = true) : idParse (idBytes k) = some k := by
  have hz : (idBytes k).size ≤ 2 ^ 32 - 144 := by
    unfold idOk at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.2
  have al := answers_lt hz
  unfold idOk at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩, ac⟩, ar⟩, _⟩ := h
  obtain ⟨s, cfg, t⟩ := k
  dsimp only at a1 a2 a3 a4 a5 a6 ac ar al
  have hn : (Key.nameOf s cfg t).size = 112 := by
    unfold Key.nameOf
    rw [size_tableName, ac, ar]
  have hp : ∀ x : UInt64 × UInt64 × UInt64, True → 1 ≤ (Fmt.ext x).size := by
    intro x _
    unfold Fmt.ext
    simp only [ByteArray.size_append, Fmt.size_u64]
    omega
  have d0 := Fmt.undoes_digest cfg ac ByteArray.empty
    (Fmt.text (Key.nameOf s cfg t) ++ Fmt.list Fmt.ext (t.answers.map E.triple))
  have d1 := Fmt.undoes_text (Key.nameOf s cfg t)
    (by show (Key.nameOf s cfg t).size < 2 ^ 64; rw [hn]; decide) cfg
    (Fmt.list Fmt.ext (t.answers.map E.triple))
  have d2 := Fmt.undoes_list undoes_ext3 hp (t.answers.map E.triple) ⟨al, fun _ _ => trivial⟩
    (cfg ++ Fmt.text (Key.nameOf s cfg t)) ByteArray.empty
  have d3 : nameParse (Key.nameOf s cfg t) = some (t.root, s) :=
    nameParse_tableName t.root cfg ar ac _ _ _ _ _ _ a1 a2 a3 a4 a5 a6
  simp only [id, ByteArray.empty_append, ByteArray.append_empty, ByteArray.size_empty,
    Nat.zero_add, ← ByteArray.append_assoc] at d0 d1 d2
  have e2 : (t.answers.map E.triple).map E.ofTriple = t.answers := by
    rw [List.map_map]
    exact List.map_id' t.answers
  unfold idParse idBytes
  dsimp only
  rw [ac] at d0 d1
  have hsz : (cfg ++ Fmt.text (Key.nameOf s cfg t)).size =
      32 + (Fmt.text (Key.nameOf s cfg t)).size := by
    rw [ByteArray.size_append, ac]
  rw [hsz] at d2
  simp only [d0, d1, d2, d3, e2, rdThree, Option.bind_eq_bind, Option.bind_some, Option.pure_def]

/-- **`idRead` inverts `idCode`**: it returns k on s exactly if the code of k is s. -/
theorem idRead_iff (k : IdKey) (s : ZKCP.Str) : idRead s = some k ↔ idCode k = some s := by
  constructor
  · intro h
    unfold idRead at h
    split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · rename_i hk
          cases h
          exact hk
        · cases h
  · intro h
    have h' := h
    unfold idCode at h'
    split at h'
    · rename_i hok
      have es : s = Run.bytesToBits (idStr k) := (Option.some.inj h').symm
      unfold idRead
      rw [es, Run.bitsToBytes_bytesToBits]
      unfold idStr
      rw [Fmt.oParse_oStr 0 179 0 0 Fmt.zero32 (idBytes k) (Or.inl rfl) (idOk_dom hok)]
      dsimp only
      rw [idParse_idBytes hok]
      dsimp only
      rw [if_pos (by rw [h, es]; rfl)]
    · cases h'

open ZKCP in
/-- The library's inverse of the code, which is taken by choice, is `idRead`. -/
theorem keyOfCode_idRead (s : ZKCP.Str) : keyOfCode idCode s = idRead s := by
  cases h : idRead s with
  | some k => exact keyOfCode_enc idCode_oneToOne ((idRead_iff k s).1 h)
  | none =>
    unfold keyOfCode
    rw [dif_neg]
    rintro ⟨k, hk⟩
    rw [(idRead_iff k s).2 hk] at h
    cases h

open ZKCP in
/-- The library's first key of a digest in a log, at `idCode`, is the first value that `idRead`
returns on a query of the log whose answer is the digest. -/
theorem firstKey_idRead (d : Digest 256) (log : Trace 256) :
    firstKey idCode d log = log.findSome? fun e => if e.2 = d then idRead e.1 else none := by
  unfold firstKey
  simp only [keyOfCode_idRead]

end OnBytes.Tie
