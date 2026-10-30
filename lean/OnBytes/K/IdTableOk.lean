-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/IdTableOk.lean: at a yes of the Lean program both of its tables, with the
planner's tables' shape and configuration digest, are keys that have a code of the ID without seeds
(`OnBytes.Tie.idOk`, OnBytes/Tie/IdKey.lean). That is not the programs' commitment ID, whose string
holds the record's seeds as well (OnBytes/Key/Table.lean).

Statements and proofs. The conclusions name no hash but the configuration digest, of which only the
length is read. The premises are the program's own checks, which hash by Lean's BLAKE2b; no property
of the hash is used but the length of a digest.

"The program" is the Lean port built from OnBytes/. `idOk` asks: the six numbers of the shape are
below 2 ^ 64; digest and root have 32 bytes; the bytes that the ID without seeds hashes are within
the bound of the format's hash.

Main names:
  `shape_lt`: a shape that passes the program's test `IndexShape.ok` has its six numbers below
    2 ^ 64.
  `readTable_room`: a table that `readTable` returns has a root of 32 bytes, and 24 bytes for each
    answer lie in the file.
  `idOk_of`: `idOk` from these, a digest of 32 bytes and a file within `fileLimit`.
  `port_idOk`; `port_idOk_table`, `port_idOk_further`: from `PortYesAt` and the planner's yes:
    `idOk` of the first and of the further table, at the plan's tables' shape and digest.

Limits: that some files meet `PortYesAt` is not shown; among its clauses are the program's limits on
the lengths of the key file and the entry file (`Shell.fileLimit`), and no length of a real file is
stated here. Nothing on the answers' words or number (OnBytes/K/IdTableAnswers.lean), on seeds, or
on soundness. For proofs only; no program imports this file.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.K.IdTableAnswers
import Fmt.ChainStmLaws
import OnBytes.Model.VerifyDigest

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.K.IdTable
open OnBytes OnBytes.Slice OnBytes.Tie Cb

/-- A shape that passes the program's test has its six numbers below 2 ^ 64. -/
theorem shape_lt (s : Params.IndexShape) (h : s.ok = true) :
    s.code.logN < 2 ^ 64 ∧ s.code.ell < 2 ^ 64 ∧ s.code.r < 2 ^ 64 ∧ s.v < 2 ^ 64 ∧
      s.answers < 2 ^ 64 ∧ s.saltBytes < 2 ^ 64 := by
  unfold Params.IndexShape.ok Code.ok Fmt.saltLenOK Params.IndexShape.pads at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨_, hN⟩, _⟩, hl⟩, hr⟩, _⟩, _⟩, hv⟩, hp⟩, ⟨_, _⟩, hs⟩ := h
  have h60 : 2 ^ s.code.logN ≤ 2 ^ mostLogN := Nat.pow_le_pow_right (by omega) hN
  have hm : 2 ^ mostLogN < 2 ^ 64 := by decide
  have hN' : mostLogN < 2 ^ 64 := by decide
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

/-- A table that `readTable` returns: its root; the room of its answers in the file. -/
theorem readTable_room (f : Fmt.Fld) (count : ℕ) (b : ByteArray) (i : ℕ)
    (t : Params.TableName) (j : ℕ) (h : readTable f count b i = .ok (t, j)) :
    t.root.size = 32 ∧ 24 * t.answers.length ≤ b.size := by
  unfold readTable at h
  split at h
  · cases h
  · rename_i root k hd
    split at h
    · cases h
    · rename_i ys m hm
      injection h with h'
      have ht : t = ⟨root, ys.map E.ofTriple⟩ := (congrArg (·.1) h').symm
      rw [rdManyT_eq] at hm
      obtain ⟨h32, _, hk, _⟩ := Fmt.only_digest b i root k hd
      obtain ⟨_, _, h3, h4, _⟩ := Fmt.only_many (Fmt.only_ext f) count b k ys m hk hm
      subst ht
      refine ⟨h32, ?_⟩
      show 24 * (ys.map E.ofTriple).length ≤ b.size
      rw [List.length_map, ← Fmt.size_exts]
      omega

/-- The number of bytes that the ID without seeds hashes. -/
theorem size_idBytes (k : IdKey) :
    (idBytes k).size = k.2.1.size + (8 + (k.2.2.root.size + k.2.1.size + 48)) +
      (8 + 24 * k.2.2.answers.length) := by
  unfold idBytes Fmt.list Key.nameOf
  rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_append, Fmt.size_text,
    size_tableName, Fmt.size_u64n, Fmt.size_exts, List.length_map]

/-- A key has a code, if its shape passes the program's test, digest and root have 32 bytes and its
answers lie in a file within the program's limit. -/
theorem idOk_of (s : Params.IndexShape) (cfg : ByteArray) (t : Params.TableName) (n : ℕ)
    (hs : s.ok = true) (hc : cfg.size = 32) (hr : t.root.size = 32)
    (ha : 24 * t.answers.length ≤ n) (hn : n ≤ Shell.fileLimit) : idOk (s, cfg, t) = true := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := shape_lt s hs
  have h7 : (idBytes (s, cfg, t)).size ≤ 2 ^ 32 - 144 := by
    rw [size_idBytes]
    show cfg.size + (8 + (t.root.size + cfg.size + 48)) + (8 + 24 * t.answers.length) ≤ _
    unfold Shell.fileLimit at hn
    omega
  unfold idOk
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, hc⟩, hr⟩, h7⟩

/-- A table that the key file's reader returns. -/
theorem key_readTable_ok (s : Params.IndexShape) (cfg file : ByteArray) (t : Params.TableName)
    (j : ℕ) (h : Key.readTable s cfg file = .ok (t, j)) :
    s.ok = true ∧ t.root.size = 32 ∧ 24 * t.answers.length ≤ file.size := by
  unfold Key.readTable at h
  split at h
  · cases h
  · rename_i hs
    split at h
    · cases h
    · rename_i i _
      split at h
      · cases h
      · rename_i table m hm
        split at h
        · injection h with h'
          obtain rfl : table = t := congrArg (·.1) h'
          refine ⟨?_, readTable_room .two _ file i table m hm⟩
          cases hk : s.ok with
          | true => rfl
          | false => exact absurd (by rw [hk]; rfl) hs
        · cases h

/-- A table that the check of a key file returns. -/
theorem key_check_ok (k : Params.KeyChains) (file : ByteArray) (t : Params.TableName)
    (h : Key.check k file = .ok t) :
    k.oneTime.lin.fold.index.ok = true ∧ t.root.size = 32 ∧
      24 * t.answers.length ≤ file.size := by
  unfold Key.check at h
  dsimp only at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · rename_i table j hr
        split at h
        · cases h
        · split at h
          · cases h
          · injection h with h'
            subst h'
            exact key_readTable_ok _ _ file table j hr

/-- The further table that the reader of an entry file returns. -/
theorem entry_read_room (p : Params.Link) (first : Params.TableName) (file : ByteArray)
    (r : Entry.EntryRead) (h : Entry.read p first file = .ok r) :
    r.further.root.size = 32 ∧ 24 * r.further.answers.length ≤ file.size := by
  unfold Entry.read at h
  dsimp only at h
  split at h
  · cases h
  · rename_i i _
    split at h
    · cases h
    · split at h
      · cases h
      · rename_i further j hr
        have key := readTable_room _ _ file i further j hr
        split at h
        · split at h
          · cases h
          · split at h
            · cases h
            · split at h
              · cases h
              · injection h with h'
                subst h'
                exact key
        · cases h

/-- A table that the check of an entry file returns. -/
theorem entry_check_room (params : ByteArray) (first : Params.TableName) (file : ByteArray)
    (t : Params.TableName) (h : Entry.check params first file = .ok t) :
    t.root.size = 32 ∧ 24 * t.answers.length ≤ file.size := by
  unfold Entry.check at h
  split at h
  · cases h
  · rename_i p _
    split at h
    · cases h
    · rename_i r hr
      split at h
      · injection h with h'
        subst h'
        exact entry_read_room p first file r hr
      · cases h

/-- **At a yes of the program both tables have a code**, at the shape and the digest of whatever
plan the planner returns on the three public files. -/
theorem port_idOk {F : Files} {id : String} {table further : Params.TableName}
    (h : PortYesAt F id table further) {pl : Model.Verify.Planned}
    (hpl : Model.Verify.planned F.pol F.KL (some F.lay) = .ok pl) :
    idOk (pl.chains.tableShape, pl.cfg, table) = true ∧
      idOk (pl.chains.tableShape, pl.cfg, further) = true := by
  obtain ⟨_, p, _, _, _, _, _, _, _, _, _, hkl, hel, hp, _, _, hk, he, _, _, hsame, _⟩ := h
  obtain rfl : p = pl := Except.ok.inj (hp.symm.trans hpl)
  obtain ⟨hs, hr, ha⟩ := key_check_ok _ _ _ hk
  obtain ⟨hr', ha'⟩ := entry_check_room _ _ _ _ he
  have hc : p.cfg.size = 32 := by
    rw [hsame.1.1]
    exact Params.configurationDigest_size _
  exact ⟨idOk_of _ _ _ _ hs hc hr ha hkl, idOk_of _ _ _ _ hs hc hr' ha' hel⟩

/-- The first table. -/
theorem port_idOk_table {F : Files} {id : String} {table further : Params.TableName}
    (h : PortYesAt F id table further) {pl : Model.Verify.Planned}
    (hpl : Model.Verify.planned F.pol F.KL (some F.lay) = .ok pl) :
    idOk (pl.chains.tableShape, pl.cfg, table) = true := (port_idOk h hpl).1

/-- The further table. -/
theorem port_idOk_further {F : Files} {id : String} {table further : Params.TableName}
    (h : PortYesAt F id table further) {pl : Model.Verify.Planned}
    (hpl : Model.Verify.planned F.pol F.KL (some F.lay) = .ok pl) :
    idOk (pl.chains.tableShape, pl.cfg, further) = true := (port_idOk h hpl).2

end OnBytes.K.IdTable
