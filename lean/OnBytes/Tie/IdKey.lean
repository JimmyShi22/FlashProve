-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/IdKey.lean: the ID without seeds as the hash of a code: what enters it, coded one to
one; that ID at any function in the place of the hash; and what that gives on query logs and under a
random oracle.

"The ID without seeds" is this file's name for the format's hash, under the number 179, of bytes
that are made of the tables' shape, the digest of the public files and a table's root and answers.
IT IS NOT THE PROGRAMS' COMMITMENT ID: their string holds the record's seeds and a closing list as
well (`Key.commitmentIdAt`, OnBytes/Key/Table.lean), and nothing here is tied to
`Key.commitmentId`. Here these three are one value, a key (`IdKey`), and the string at which
the format's oracle is asked for that hash (`Fmt.oStr`) is its code (`idCode`). "Key" is the
library's word for what a digest stands for; it is not the key file, of which only the table enters.
The library has theorems on a scheme whose verifier holds the digest of a key's code
(ZKCP/DigestKey.lean, Compile/DigestKeyBinding.lean); they ask of the coding that it is one to one.
This file proves that and states two of the library's theorems at this code.

Main definitions: `IdKey`, `idBytes`, `idOk`, `idStr`, `idCode`, `idAt`.
Main theorems.
- `idCode_oneToOne`: no bit string is the code of two keys. It rests on `idBytes_inj`: within
  `idOk`, equal bytes come from equal keys.
- `idAt_oB`: within `idOk`, the ID at the function that an oracle f on bit strings induces is the
  library's `ZKCP.digestUnder f idCode`, as bytes.
- `id_of_log`: on query logs, no probability. Take a first log, one query at a digest d written as
  bits, a second log, and the query at a key's code with the answer d. If the library's event
  `ZKCP.AnswerRepeats` has not happened in that one log, the key is the first in the first log whose
  code has the answer d (`ZKCP.firstKey`), and no two different entries of the two logs have one
  answer.
- `two_keys_one_id`: under a random oracle, an algorithm with at most t queries puts out two
  different keys that both have codes and have one ID with probability at most (t + 2)^2 / 2^256. It
  is `ZKCP.Pr_two_keys_one_digest_le` at `idCode`.
- `hex_inj`: `Fmt.hex` is one to one on byte strings.

What is not claimed. No probability is stated of the program, which is the Lean port built from
OnBytes/, or of BLAKE2b: `two_keys_one_id` is on an oracle that is drawn at random. What the
theorems tie to an ID without seeds, under a random oracle, is the shape, the digest, the root and
the answers, as bytes. What lies
under the root is not its matter, nor that the 32 bytes of the digest are the digest of any files:
in a key they are any 32 bytes. The key file's proofs, the entry, the request, the reply and the
proof file do not enter the ID; nor do the distances at which a table was tested, which are no field
of the shape. Outside `idOk` nothing is said: a key has a code only if its six numbers are below
2^64, where the format's spelling of a number wraps, digest and root have 32 bytes, and the bytes
are within the hash's bound. The digest stands twice in the bytes, outside the table's name and
inside it: in a code the two are one value; a string in which they differ is no key's code, though
it has the form of a call 179. A key within `idOk` need not be one that the program admits
(`Key.tableOk`): the number of answers is not tied to the shape, and the digest may be 32 zero
bytes. A caller names an ID as 64 digits; the step from these to the 256 bits of a digest, by
`hex_inj` and the library's coding of 32 bytes, is stated nowhere as one. `ZKCP.firstKey` inverts
the code by choice; OnBytes/Tie/IdRead.lean has a reader in its place. Nothing on soundness. Nothing
is said of the C++ program `cp_verify`. For proofs only; the program does not import this file.

-/
import OnBytes.Key.Table
import OnBytes.Field.ExtEq
import Fmt.Rules1Laws
import Fmt.Rules23Laws
import Fmt.Rules23In
import Run.CodingBitsLaws
import Run.LaxDomProofs
import ZKCP.DigestKey
import Compile.DigestKeyBinding
import Run.OCompM

set_option autoImplicit false

namespace OnBytes.Tie

/-- What enters the ID without seeds: the tables' shape, the digest of the public files, and a
table, that is a root and the answers of a record. -/
abbrev IdKey : Type := Params.IndexShape × ByteArray × Params.TableName

/-- The string of the ID without seeds: the digest, the table's name as a text and the list of the
answers. The programs' string holds the record's seeds and a closing list as well
(`Key.commitmentIdAt`, OnBytes/Key/Table.lean). -/
def idBytes (k : IdKey) : ByteArray :=
  k.2.1 ++ Fmt.text (Key.nameOf k.1 k.2.1 k.2.2) ++ Fmt.list Fmt.ext (k.2.2.answers.map E.triple)

/-- The keys that have a code: the six numbers of the shape are below 2^64, the digest and the root
have 32 bytes, and the bytes are within the bound of the format's hash. -/
def idOk (k : IdKey) : Bool :=
  decide (k.1.code.logN < 2 ^ 64) && decide (k.1.code.ell < 2 ^ 64) &&
    decide (k.1.code.r < 2 ^ 64) && decide (k.1.v < 2 ^ 64) && decide (k.1.answers < 2 ^ 64) &&
    decide (k.1.saltBytes < 2 ^ 64) && decide (k.2.1.size = 32) &&
    decide (k.2.2.root.size = 32) && decide ((idBytes k).size ≤ 2 ^ 32 - 144)

/-- The string at which an oracle is asked for the ID without seeds: that of the format's call 179
on `idBytes`. -/
def idStr (k : IdKey) : ByteArray := Fmt.oStr 0 179 0 0 Fmt.zero32 (idBytes k)

/-- The code of a key, as a bit string; none outside `idOk`. -/
def idCode (k : IdKey) : Option ZKCP.Str :=
  if idOk k then some (Run.bytesToBits (idStr k)) else none

/-- The format's spelling of a word is one to one. -/
theorem u64_inj {x y : UInt64} (h : Fmt.u64 x = Fmt.u64 y) : x = y := by
  have hx := Fmt.undoes_word x trivial ByteArray.empty ByteArray.empty
  have hy := Fmt.undoes_word y trivial ByteArray.empty ByteArray.empty
  rw [h, hy] at hx
  exact (congrArg (·.1) (Option.some.inj hx)).symm

/-- The format's spelling of a number is one to one below 2^64. From 2^64 on it wraps. -/
theorem u64n_inj {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) (h : Fmt.u64n x = Fmt.u64n y) :
    x = y := by
  have e := congrArg UInt64.toNat (u64_inj h)
  rw [UInt64.toNat_ofNat', UInt64.toNat_ofNat'] at e
  rw [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at e
  exact e

/-- A reader of three words undoes the spelling of a triple of words, whatever the words: no
canonical form is asked. -/
theorem undoes_ext3 :
    Fmt.Undoes (Fmt.rdPair Fmt.rdWord (Fmt.rdPair Fmt.rdWord Fmt.rdWord)) Fmt.ext
      fun _ => True := by
  have h := Fmt.undoes_pair Fmt.undoes_word (Fmt.undoes_pair Fmt.undoes_word Fmt.undoes_word)
  intro e _ pre post
  have e0 : Fmt.ext e = Fmt.pair Fmt.u64 (Fmt.pair Fmt.u64 Fmt.u64) e := by
    unfold Fmt.ext Fmt.pair
    rw [ByteArray.append_assoc]
  rw [e0]
  exact h e ⟨trivial, trivial, trivial⟩ pre post

/-- The spelling of a list of triples of words is one to one on lists of fewer than 2^64 entries. -/
theorem listExt_inj {l l' : List (UInt64 × UInt64 × UInt64)} (hl : l.length < 2 ^ 64)
    (hl' : l'.length < 2 ^ 64) (h : Fmt.list Fmt.ext l = Fmt.list Fmt.ext l') : l = l' := by
  have hp : ∀ x : UInt64 × UInt64 × UInt64, True → 1 ≤ (Fmt.ext x).size := by
    intro x _
    unfold Fmt.ext
    simp only [ByteArray.size_append, Fmt.size_u64]
    omega
  have u := Fmt.undoes_list undoes_ext3 hp
  have a := u l ⟨hl, fun _ _ => trivial⟩ ByteArray.empty ByteArray.empty
  have b := u l' ⟨hl', fun _ _ => trivial⟩ ByteArray.empty ByteArray.empty
  rw [h, b] at a
  exact (congrArg (·.1) (Option.some.inj a)).symm

/-- Where the bytes are within the hash's bound, the answers are fewer than 2^64. -/
theorem answers_lt {k : IdKey} (h : (idBytes k).size ≤ 2 ^ 32 - 144) :
    (k.2.2.answers.map E.triple).length < 2 ^ 64 := by
  have h1 := Fmt.length_le_cat (sp := Fmt.ext) (k.2.2.answers.map E.triple) (fun x _ => by
    unfold Fmt.ext
    simp only [ByteArray.size_append, Fmt.size_u64]
    omega)
  have h2 : (Fmt.cat ((k.2.2.answers.map E.triple).map Fmt.ext)).size ≤ (idBytes k).size := by
    unfold idBytes Fmt.list
    simp only [ByteArray.size_append]
    omega
  omega

/-- A table's name has 48 bytes more than root and digest together. -/
theorem size_tableName (root cfg : ByteArray) (a b c d e f : Nat) :
    (Fmt.tableName root cfg a b c d e f).size = root.size + cfg.size + 48 := by
  unfold Fmt.tableName
  simp only [ByteArray.size_append, Fmt.size_u64n]

/-- Within `idOk`, equal bytes come from equal keys. All parts but the list of answers have a fixed
length; the list carries its own. -/
theorem idBytes_inj {k k' : IdKey} (h : idOk k = true) (h' : idOk k' = true)
    (e : idBytes k = idBytes k') : k = k' := by
  unfold idOk at h h'
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h h'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩, ac⟩, ar⟩, az⟩ := h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨b1, b2⟩, b3⟩, b4⟩, b5⟩, b6⟩, bc⟩, br⟩, bz⟩ := h'
  have al := answers_lt az
  have bl := answers_lt bz
  obtain ⟨s, cfg, t⟩ := k
  obtain ⟨s', cfg', t'⟩ := k'
  dsimp only at a1 a2 a3 a4 a5 a6 ac ar al b1 b2 b3 b4 b5 b6 bc br bl
  unfold idBytes at e
  dsimp only at e
  have hn : (Key.nameOf s cfg t).size = (Key.nameOf s' cfg' t').size := by
    unfold Key.nameOf
    rw [size_tableName, size_tableName, ac, ar, bc, br]
  obtain ⟨e1, eL⟩ := Fmt.append_cancel _ _ _ _ (by
    unfold Fmt.text
    simp only [ByteArray.size_append, Fmt.size_u64n, hn, ac, bc]) e
  obtain ⟨eC, eT⟩ := Fmt.append_cancel _ _ _ _ (by rw [ac, bc]) e1
  unfold Fmt.text at eT
  obtain ⟨_, eN⟩ := Fmt.append_cancel _ _ _ _ (by rw [Fmt.size_u64n, Fmt.size_u64n]) eT
  unfold Key.nameOf Fmt.tableName at eN
  obtain ⟨n5, m6⟩ := Fmt.append_cancel _ _ _ _ (by
    simp only [ByteArray.size_append, Fmt.size_u64n, ac, ar, bc, br]) eN
  obtain ⟨n4, m5⟩ := Fmt.append_cancel _ _ _ _ (by
    simp only [ByteArray.size_append, Fmt.size_u64n, ac, ar, bc, br]) n5
  obtain ⟨n3, m4⟩ := Fmt.append_cancel _ _ _ _ (by
    simp only [ByteArray.size_append, Fmt.size_u64n, ac, ar, bc, br]) n4
  obtain ⟨n2, m3⟩ := Fmt.append_cancel _ _ _ _ (by
    simp only [ByteArray.size_append, Fmt.size_u64n, ac, ar, bc, br]) n3
  obtain ⟨n1, m2⟩ := Fmt.append_cancel _ _ _ _ (by
    simp only [ByteArray.size_append, Fmt.size_u64n, ac, ar, bc, br]) n2
  obtain ⟨n0, m1⟩ := Fmt.append_cancel _ _ _ _ (by
    simp only [ByteArray.size_append, ac, ar, bc, br]) n1
  obtain ⟨eR, _⟩ := Fmt.append_cancel _ _ _ _ (by rw [ar, br]) n0
  have c1 := u64n_inj a1 b1 m1
  have c2 := u64n_inj a2 b2 m2
  have c3 := u64n_inj a3 b3 m3
  have c4 := u64n_inj a4 b4 m4
  have c5 := u64n_inj a5 b5 m5
  have c6 := u64n_inj a6 b6 m6
  have eA : t.answers = t'.answers :=
    List.map_injective_iff.2 (fun _ _ hxy => triple_inj hxy)
      (listExt_inj al bl eL)
  obtain ⟨⟨x1, x2, x3⟩, x4, x5, x6⟩ := s
  obtain ⟨⟨y1, y2, y3⟩, y4, y5, y6⟩ := s'
  obtain ⟨r, an⟩ := t
  obtain ⟨r', an'⟩ := t'
  dsimp only at c1 c2 c3 c4 c5 c6 eR eA
  subst c1 c2 c3 c4 c5 c6 eR eA eC
  rfl

/-- Within `idOk` the call 179 on the bytes is in the domain of the format's hash. -/
theorem idOk_dom {k : IdKey} (h : idOk k = true) :
    Fmt.hDom 179 0 0 Fmt.zero32 (idBytes k) = true := by
  unfold idOk at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact Run.dom0 179 0 (idBytes k) (by decide) (by decide) (by decide) h.2

/-- **No bit string is the code of two keys.** The condition that the library's theorems on a key
behind a digest ask of a coding (`ZKCP.CodeIsOneToOne`). -/
theorem idCode_oneToOne : ZKCP.CodeIsOneToOne idCode := by
  intro k k' c hk hk'
  unfold idCode at hk hk'
  split at hk
  · rename_i h
    split at hk'
    · rename_i h'
      have e : Run.bytesToBits (idStr k) = Run.bytesToBits (idStr k') :=
        (Option.some.inj hk).trans (Option.some.inj hk').symm
      have e2 := Run.bytesToBits_inj e
      unfold idStr at e2
      exact idBytes_inj h h' (Fmt.oStr_inj 0 0 179 179 0 0 0 0 _ _ _ _ (Or.inl rfl) (Or.inl rfl)
        (idOk_dom h) (idOk_dom h') e2).2.2.2.2.2
    · cases hk'
  · cases hk

/-- The ID without seeds, with a function O on byte strings in the place of the hash's oracle. The
program does not call it. -/
def idAt (O : ByteArray → ByteArray) (k : IdKey) : ByteArray :=
  Fmt.HO O 179 0 0 Fmt.zero32 (idBytes k)

/-- The ID without seeds at O is the value of O at the key's string. -/
theorem idAt_eq (O : ByteArray → ByteArray) (k : IdKey) : idAt O k = O (idStr k) := by
  unfold idAt Fmt.HO idStr
  rw [if_neg (by decide)]

/-- Within `idOk`, the ID without seeds at the function that an oracle f on bit strings induces on
byte strings is, as bytes, the library's digest of the key under f at `idCode`. -/
theorem idAt_oB (f : ZKCP.Oracle 256) {k : IdKey} (h : idOk k = true) :
    idAt (Run.oB f) k = Run.digToBytes (ZKCP.digestUnder f idCode k) := by
  rw [idAt_eq]
  unfold Run.oB ZKCP.digestUnder idCode
  rw [if_pos h]
  rfl

open ZKCP ZKCP.DigestKey in
/-- On query logs; no probability. `trC` and `trP` are two logs, d a digest, k a key with the code
s. If the library's event `ZKCP.AnswerRepeats` has not happened in `trC`, then a query at d written
as bits, then `trP`, then the query at s with the answer d, then k is the first key in `trC` whose
code has the answer d, and no two different entries of `trC` and `trP` have one answer. The first
half is `answerRepeats_of_hit`, the second `answerRepeats_of_two` (Compile/DigestKeyBinding.lean),
read the other way. -/
theorem id_of_log (trC trP : ZKCP.Trace 256) (d r0 : ZKCP.Digest 256) (k : IdKey) (s : ZKCP.Str)
    (hs : idCode k = some s)
    (hno : ¬ AnswerRepeats (trC ++ (spelling d, r0) :: (trP ++ [(s, d)]))) :
    firstKey idCode d trC = some k ∧
      ∀ e1 ∈ trC ++ trP, ∀ e2 ∈ trC ++ trP, e1 ≠ e2 → e1.2 ≠ e2.2 := by
  have mem : ∀ e ∈ trC ++ trP, e ∈ trC ++ (spelling d, r0) :: (trP ++ [(s, d)]) := by
    intro e he
    rcases List.mem_append.1 he with h | h
    · exact List.mem_append_left _ h
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_append_left _ h))
  refine ⟨Classical.byContradiction fun hk =>
    hno (answerRepeats_of_hit idCode_oneToOne trC trP d r0 hs hk), fun e1 h1 e2 h2 hne ha =>
    hno (answerRepeats_of_two (mem e1 h1) (mem e2 h2) hne ha)⟩

/-- The byte that two digits of base 16 spell. -/
def unByte (a b : Char) : UInt8 := (Fmt.unhexDigit a <<< 4) ||| Fmt.unhexDigit b

/-- From a byte to its two digits and back gives the byte: 256 cases, evaluated in Lean's kernel. -/
theorem unByte_hex (x : UInt8) :
    unByte (Fmt.hexDigit (x >>> 4)) (Fmt.hexDigit (x &&& 15)) = x := by
  have key : ∀ n, n < 256 → unByte (Fmt.hexDigit (UInt8.ofNat n >>> 4))
      (Fmt.hexDigit (UInt8.ofNat n &&& 15)) = UInt8.ofNat n := by decide +kernel
  have h := key x.toNat x.toNat_lt
  rwa [UInt8.ofNat_toNat] at h

/-- The digits of a list of bytes determine the list. -/
theorem hexList_inj : ∀ l l' : List UInt8,
    (l.flatMap fun (x : UInt8) => [Fmt.hexDigit (x >>> 4), Fmt.hexDigit (x &&& 15)]) =
      (l'.flatMap fun (x : UInt8) => [Fmt.hexDigit (x >>> 4), Fmt.hexDigit (x &&& 15)]) →
    l = l'
  | [], [], _ => rfl
  | [], y :: l', h => by simp at h
  | x :: l, [], h => by simp at h
  | x :: l, y :: l', h => by
    simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.cons.injEq] at h
    obtain ⟨h1, h2, h3⟩ := h
    have e : x = y := by
      rw [← unByte_hex x, ← unByte_hex y, h1, h2]
    rw [e, hexList_inj l l' h3]

/-- `Fmt.hex` is one to one: equal digits mean equal bytes. -/
theorem hex_inj {a b : ByteArray} (h : Fmt.hex a = Fmt.hex b) : a = b := by
  unfold Fmt.hex at h
  have h2 := hexList_inj _ _ (String.ofList_injective h)
  exact ByteArray.ext (Array.toList_inj.1 h2)

open scoped ENNReal in
/-- **Two keys with one ID without seeds, under a random oracle.** An algorithm with at most t
queries puts out two different keys that both have codes and have the same digest under the drawn
oracle with probability at most (t + 2)^2 / 2^256; the two digests are computed after the algorithm
has stopped. It is `ZKCP.Pr_two_keys_one_digest_le` at `idCode`. No probability is stated of the
program or of BLAKE2b. -/
theorem two_keys_one_id (c : ZKCP.OComp 256 (IdKey × IdKey)) (t : ℕ) (hc : c.QueryBound t) :
    ZKCP.Pr (c.bind fun p => (ZKCP.keyDigest idCode p.1).bind fun d₁ =>
        (ZKCP.keyDigest idCode p.2).bind fun d₂ => .pure (p, d₁, d₂))
      (fun _ => {o | o.1.1 ≠ o.1.2 ∧ idCode o.1.1 ≠ none ∧ idCode o.1.2 ≠ none ∧ o.2.1 = o.2.2})
      ≤ (((t + 2) ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 :=
  ZKCP.Pr_two_keys_one_digest_le idCode_oneToOne c t hc

end OnBytes.Tie
