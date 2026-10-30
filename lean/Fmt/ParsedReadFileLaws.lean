-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Fmt/ParsedReadFileLaws.lean: for a whole entry file, key file and proof file, without a hash: the
reader by the numbers (Fmt/ParsedReadFile.lean) gives a record exactly where the record fits the
declared structure, has the numbers that were told, and the file is the record's writing.

Fmt/ParsedReadLaws.lean has both laws of one chain's reader. A file is its chains and a few parts of
fixed length. Here these parts get their two laws, the parts are joined, and the two laws are said
in one sentence for each of the three files. The numbers are the file's chains' numbers
(`EntryParsed.counts`, `KeyParsed.counts`, `ProofParsed.counts`); they are given to the reader, not
derived.

How: by the two frames `Undoes` (Fmt/Rules1Laws.lean) and `Cuts` (Fmt/ParsedReadLaws.lean). At a
declared structure each chain is written under its own plan (`Declared.plan`), whose two widths are
the setting's by definition, so no premise speaks of a plan. No Mathlib, neither directly nor
through the imports.

1. What the file contains. Theorems; one small definition (`spThree`).

2. What is checked when the file compiles. The proofs. Tests: Fmt/ParsedReadFileKnown.lean
[not in this library]; so here read: not tested in this library.

3. Theorems. The laws of a file ask that a nonce and a listed position have at most eight bytes
(D.setting.nonce ≤ 8, D.setting.posB ≤ 8), and nothing else of D.
   Tools: `eq_of_bytes_beq`, `bytes_beq_self`; readers computed: `rdPair_some`, `rdMap_some`,
     `whole_some`.
   The parts that are in no chain: `size_headOf`; `undoes_table`, `cuts_table`; `undoes_slot`,
     `cuts_slot`; `undoes_copy`, `cuts_copy`.
   `undoes_three`, `cuts_three`: three chains with their slot.
   `undoes_entryFile`, `cuts_entryFile`, `EntryParsed.read_iff`:
     EntryParsed.read D N file = some F ↔ F.fits D = true ∧ F.counts = N ∧ file = F.bytes D.
   `undoes_keyFile`, `cuts_keyFile`, `KeyParsed.read_iff`; `undoes_proofFile`, `cuts_proofFile`,
     `ProofParsed.read_iff`: the same of a key file and of a proof file.
   `Declared.bounds`; `EntryParsed.read_iff_settingOk`, `KeyParsed.read_iff_settingOk`,
     `ProofParsed.read_iff_settingOk`: the two bounds follow from the test `Declared.settingOk`
     (Fmt/Parsed.lean), so the three laws hold at every D that passes it.
   `rdThree_of_parts`; `EntryParsed.read_of_parts`, `KeyParsed.read_of_parts`,
     `ProofParsed.read_of_parts`: from the parts to the file. If the first eight bytes are the
     declared head, the table (or the four bytes) is read behind them, each chain is read by
     `ChainParsed.readFit` from its place to the next, the last to the file's end, and the slot is
     read between the first two and fits, then the reader of the whole file gives the record of
     these parts. These ask no bound: they compute the reader. Behind the lenient cut:
     Run/ParsedCutFileLaws.lean.
   `EntryParsed.bytes_inj`, `KeyParsed.bytes_inj`, `ProofParsed.bytes_inj`: one file, with numbers,
     is the writing of at most one record that fits.

4. What is not claimed.
   No law is stated with the declared structure alone: without the numbers it is false (two records
   of a proof file fit one D and are written to the same bytes: said here without a theorem). Which
   numbers are the right ones is not said: they follow from the draws, chain by chain. The places of
   the slot and of the later chains hang on the numbers too (one file, two records, the border 32
   bytes apart: said here without a theorem).
   There is no cut of a whole file in this library's Fmt/ and Run/ that makes the later chains'
   statements itself: these hold seals and a binding tree's root, which are values of the hash.
   In each "exactly where", the half "only where F fits" holds because the reader tests `fits`.
   The laws do not say that two files give two typed proofs: that also needs that the step from a
   record to the typed value is one-to-one on fitting records, of which nothing is said here.
   `fits` does not test D, and neither do these laws: they hold for every D with the two bounds,
   also for one that no public files give.
   Nothing on soundness follows: no verifier calls these readers.
   `eq_of_bytes_beq` and `bytes_beq_self` stand a second time in this library, over Mathlib
   (Run/PageIsReaders.lean: `bytes_beq`, `bytes_beq_self`).

Terms: lean/GLOSSARY.md.
-/
import Fmt.ParsedReadFile
import Fmt.ParsedReadLaws

namespace Fmt

/-! ## 1. The frame -/

/-- The test == on strings of bytes gives equality. -/
theorem eq_of_bytes_beq (a b : ByteArray) (h : (a == b) = true) : a = b := by
  cases a with
  | mk x =>
    cases b with
    | mk y =>
      have h' : (x == y) = true := by
        simpa [BEq.beq, ByteArray.instBEq.beq] using h
      rw [beq_iff_eq.1 h']

/-- A string of bytes passes the test == with itself. -/
theorem bytes_beq_self (a : ByteArray) : (a == a) = true := by
  cases a with
  | mk x =>
    show (x == x) = true
    exact beq_self_eq_true x

/-- Two readers, one behind the other, computed. -/
theorem rdPair_some {α β : Type} {ra : Rd α} {rb : Rd β} {b : ByteArray} {i j k : Nat} {x : α}
    {y : β} (h1 : ra b i = some (x, j)) (h2 : rb b j = some (y, k)) :
    rdPair ra rb b i = some ((x, y), k) := by
  unfold rdPair
  rw [h1]
  simp only
  rw [h2]

/-- A turned reader, computed. -/
theorem rdMap_some {α β : Type} {f : α → β} {r : Rd α} {b : ByteArray} {i j : Nat} {x : α}
    (h : r b i = some (x, j)) : rdMap f r b i = some (f x, j) := by
  unfold rdMap
  rw [h]
  rfl

/-- A reader that ends at the string's end, on the whole string. -/
theorem whole_some {α : Type} {r : Rd α} {b : ByteArray} {x : α} (h : r b 0 = some (x, b.size)) :
    whole r b = some x := by
  unfold whole
  rw [h]
  simp

/-! ## 2. The parts of a file that are in no chain -/

/-- The first eight bytes of a file are eight. -/
theorem size_headOf (f : Fld) :
    (headOf tagKey f).size = 8 ∧ (headOf tagEntry f).size = 8 ∧ (headOf tagProof f).size = 8 := by
  cases f <;> decide

/-- A table in a file (ok: `TableSt.ok`). -/
theorem undoes_table (f : Fld) (s : TableShape) :
    Undoes (rdTable f s) TableSt.bytes fun t => t.ok f s = true := by
  unfold rdTable
  refine undoes_map (undoes_pair undoes_digest (undoes_count (undoes_ext f) s.count)) _
    (fun t => (t.root, t.answers)) ?_ ?_ ?_
  · intro _ _
    rfl
  · intro _ _
    rfl
  · intro t ht
    simp only [TableSt.ok, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at ht
    exact ⟨ht.1.1, ht.1.2, fun e he => lt_of_okE f e (ht.2 e he)⟩

/-- What the reader of a table accepts has a table's form (`TableSt.ok`) and is written to the bytes
that were read. -/
theorem cuts_table (f : Fld) (s : TableShape) :
    Cuts (rdTable f s) TableSt.bytes fun t => t.ok f s = true := by
  unfold rdTable
  refine cuts_map (cuts_pair (cuts_of_only only_digest) (cuts_count (cuts_of_only (only_ext f))
    s.count)) _ (fun _ _ => rfl) ?_
  intro x hx
  simp only [TableSt.ok, Bool.and_eq_true, beq_iff_eq, List.all_eq_true]
  exact ⟨⟨hx.1, hx.2.1⟩, fun e he => okE_of_lt f e (hx.2.2 e he)⟩

/-- A slot (ok: `SlotParsed.fits`). -/
theorem undoes_slot (s : BindShape) :
    Undoes (rdSlot s) SlotParsed.bytes fun x => x.fits s = true := by
  unfold rdSlot
  refine undoes_map
    (undoes_pair undoes_word (undoes_pair (undoes_bytes s.saltBytes)
      (undoes_count undoes_digest s.depth))) _ (fun x => (x.place, x.salt, x.path)) ?_ ?_ ?_
  · intro _ _
    rfl
  · intro x _
    simp only [SlotParsed.bytes, pair, id_eq, List.map_id, ByteArray.append_assoc]
  · intro x hx
    simp only [SlotParsed.fits, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hx
    exact ⟨trivial, hx.1.1.2, hx.1.2, hx.2⟩

/-- What the reader of a slot accepts is written to the bytes that were read. -/
theorem cuts_slot (s : BindShape) : Cuts (rdSlot s) SlotParsed.bytes fun _ => True := by
  unfold rdSlot
  refine cuts_map
    (cuts_pair (cuts_of_only only_word) (cuts_pair (cuts_of_only (only_bytes s.saltBytes))
      (cuts_count (cuts_of_only only_digest) s.depth))) _ ?_ fun _ _ => trivial
  intro x _
  simp only [SlotParsed.bytes, pair, id_eq, List.map_id, ByteArray.append_assoc]

/-- The four bytes behind a proof file's first eight. -/
theorem undoes_copy : Undoes rdCopy (fun c => lowBytes 4 c.toNat) fun _ => True :=
  undoes_map (undoes_readLE 4 (by omega)) UInt32.ofNat (fun c => c.toNat)
    (fun _ _ => UInt32.ofNat_toNat) (fun _ _ => rfl) fun c _ => c.toNat_lt

/-- What the reader of these four bytes accepts is written to the bytes that were read. -/
theorem cuts_copy : Cuts rdCopy (fun c => lowBytes 4 c.toNat) fun _ => True :=
  cuts_map (cuts_of_only (only_readLE 4 (by omega))) UInt32.ofNat
    (fun v hv => by
      show lowBytes 4 (UInt32.ofNat v).toNat = lowBytes 4 v
      rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (show v < 2 ^ 32 from hv)])
    fun _ _ => trivial

/-! ## 3. Three chains with their slot -/

/-- the bytes of three chains with the slot between the first two, under the declared plans -/
def spThree (D : Declared) (T : ThreeDecl)
    (x : ChainParsed × SlotParsed × ChainParsed × ChainParsed) : ByteArray :=
  x.1.bytes (D.plan T.first) ++ (x.2.1.bytes ++ (x.2.2.1.bytes (D.plan T.shared) ++
    x.2.2.2.bytes (D.plan T.second)))

/-- Three chains with their slot (ok: each fits; each chain has its numbers). -/
theorem undoes_three (D : Declared) (T : ThreeDecl) (N : ThreeCounts)
    (h1 : D.setting.nonce ≤ 8) (h2 : D.setting.posB ≤ 8) :
    Undoes (rdThree D T N) (spThree D T) fun x =>
      (x.1.fits D.setting T.first = true ∧ x.1.counts = N.1) ∧ x.2.1.fits T.bind = true ∧
        (x.2.2.1.fits D.setting T.shared = true ∧ x.2.2.1.counts = N.2.1) ∧
        x.2.2.2.fits D.setting T.second = true ∧ x.2.2.2.counts = N.2.2 :=
  undoes_pair (undoes_chain D.setting (D.plan T.first) rfl rfl h1 h2 T.first N.1)
    (undoes_pair (undoes_slot T.bind)
      (undoes_pair (undoes_chain D.setting (D.plan T.shared) rfl rfl h1 h2 T.shared N.2.1)
        (undoes_chain D.setting (D.plan T.second) rfl rfl h1 h2 T.second N.2.2)))

/-- What the reader of three chains accepts has the numbers that were told, and is written to the
bytes that were read. -/
theorem cuts_three (D : Declared) (T : ThreeDecl) (N : ThreeCounts)
    (h1 : D.setting.nonce ≤ 8) (h2 : D.setting.posB ≤ 8) :
    Cuts (rdThree D T N) (spThree D T) fun x =>
      x.1.counts = N.1 ∧ True ∧ x.2.2.1.counts = N.2.1 ∧ x.2.2.2.counts = N.2.2 :=
  cuts_pair (cuts_chain D.setting (D.plan T.first) rfl rfl h1 h2 T.first N.1)
    (cuts_pair (cuts_slot T.bind)
      (cuts_pair (cuts_chain D.setting (D.plan T.shared) rfl rfl h1 h2 T.shared N.2.1)
        (cuts_chain D.setting (D.plan T.second) rfl rfl h1 h2 T.second N.2.2)))

/-! ## 4. An entry file -/

/-- The parts of an entry file: the reader undoes the writer on the records that fit and have the
numbers N. -/
theorem undoes_entryFile (D : Declared) (N : ChainCounts) (h1 : D.setting.nonce ≤ 8)
    (h2 : D.setting.posB ≤ 8) :
    Undoes (EntryParsed.rd D N) (EntryParsed.bytes D) fun F =>
      F.fits D = true ∧ F.counts = N := by
  have A := undoes_pair (undoes_bytes 8)
    (undoes_pair (undoes_table D.setting.field D.table)
      (undoes_chain D.setting (D.plan D.link) rfl rfl h1 h2 D.link N))
  unfold EntryParsed.rd
  refine undoes_map A _ (fun F => (F.head, F.table, F.link)) ?_ ?_ ?_
  · intro _ _
    rfl
  · intro F _
    simp only [EntryParsed.bytes, pair, id_eq, ByteArray.append_assoc]
  · intro F hF
    obtain ⟨h, hc⟩ := hF
    simp only [EntryParsed.fits, Bool.and_eq_true] at h
    refine ⟨?_, h.1.2, h.2, hc⟩
    show F.head.size = 8
    rw [eq_of_bytes_beq _ _ h.1.1]
    exact (size_headOf D.setting.field).2.1

/-- What the reader of an entry file's parts accepts has the numbers N, and is written to the bytes
that were read. -/
theorem cuts_entryFile (D : Declared) (N : ChainCounts) (h1 : D.setting.nonce ≤ 8)
    (h2 : D.setting.posB ≤ 8) :
    Cuts (EntryParsed.rd D N) (EntryParsed.bytes D) fun F => F.counts = N := by
  have A := cuts_pair (cuts_of_only (only_bytes 8))
    (cuts_pair (cuts_table D.setting.field D.table)
      (cuts_chain D.setting (D.plan D.link) rfl rfl h1 h2 D.link N))
  unfold EntryParsed.rd
  refine cuts_map A _ ?_ ?_
  · intro x _
    simp only [EntryParsed.bytes, pair, id_eq, ByteArray.append_assoc]
  · intro x hx
    exact hx.2.2

/-- THE LAW OF AN ENTRY FILE. The reader of a whole entry file, told the numbers N, gives F exactly
where F fits the declared structure, has the numbers N, and the file is F's writing. -/
theorem EntryParsed.read_iff (D : Declared) (N : ChainCounts) (h1 : D.setting.nonce ≤ 8)
    (h2 : D.setting.posB ≤ 8) (file : ByteArray) (F : EntryParsed) :
    EntryParsed.read D N file = some F ↔ F.fits D = true ∧ F.counts = N ∧ file = F.bytes D := by
  unfold EntryParsed.read
  rw [whole_iff_both (undoes_fit _ (undoes_entryFile D N h1 h2) fun _ h => h.1)
    (cuts_fit _ (cuts_entryFile D N h1 h2)) file F, and_assoc]

/-! ## 5. A key file -/

/-- The parts of a key file: the reader undoes the writer on the records that fit and have the
numbers N. -/
theorem undoes_keyFile (D : Declared) (N : ThreeCounts) (h1 : D.setting.nonce ≤ 8)
    (h2 : D.setting.posB ≤ 8) :
    Undoes (KeyParsed.rd D N) (KeyParsed.bytes D) fun F => F.fits D = true ∧ F.counts = N := by
  have A := undoes_pair (undoes_bytes 8)
    (undoes_pair (undoes_table D.setting.field D.table) (undoes_three D D.key N h1 h2))
  unfold KeyParsed.rd
  refine undoes_map A _ (fun F => (F.head, F.table, F.first, F.slot, F.shared, F.second)) ?_ ?_ ?_
  · intro _ _
    rfl
  · intro F _
    simp only [KeyParsed.bytes, KeyParsed.bytesAt, spThree, pair, id_eq, ByteArray.append_assoc]
  · intro F hF
    obtain ⟨h, hc⟩ := hF
    simp only [KeyParsed.fits, Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩ := h
    refine ⟨?_, a2, ⟨a3, congrArg Prod.fst hc⟩, a4, ⟨a5, congrArg (fun y => y.2.1) hc⟩, a6,
      congrArg (fun y => y.2.2) hc⟩
    show F.head.size = 8
    rw [eq_of_bytes_beq _ _ a1]
    exact (size_headOf D.setting.field).1

/-- What the reader of a key file's parts accepts has the numbers N, and is written to the bytes
that were read. -/
theorem cuts_keyFile (D : Declared) (N : ThreeCounts) (h1 : D.setting.nonce ≤ 8)
    (h2 : D.setting.posB ≤ 8) :
    Cuts (KeyParsed.rd D N) (KeyParsed.bytes D) fun F => F.counts = N := by
  have A := cuts_pair (cuts_of_only (only_bytes 8))
    (cuts_pair (cuts_table D.setting.field D.table) (cuts_three D D.key N h1 h2))
  unfold KeyParsed.rd
  refine cuts_map A _ ?_ ?_
  · intro x _
    simp only [KeyParsed.bytes, KeyParsed.bytesAt, spThree, pair, id_eq, ByteArray.append_assoc]
  · intro x hx
    exact Prod.ext hx.2.2.1 (Prod.ext hx.2.2.2.2.1 hx.2.2.2.2.2)

/-- THE LAW OF A KEY FILE. The reader of a whole key file, told its three chains' numbers N, gives F
exactly where F fits the declared structure, has the numbers N, and the file is F's writing. -/
theorem KeyParsed.read_iff (D : Declared) (N : ThreeCounts)
    (h1 : D.setting.nonce ≤ 8) (h2 : D.setting.posB ≤ 8) (file : ByteArray) (F : KeyParsed) :
    KeyParsed.read D N file = some F ↔ F.fits D = true ∧ F.counts = N ∧ file = F.bytes D := by
  unfold KeyParsed.read
  rw [whole_iff_both (undoes_fit _ (undoes_keyFile D N h1 h2) fun _ h => h.1)
    (cuts_fit _ (cuts_keyFile D N h1 h2)) file F, and_assoc]

/-! ## 6. A proof file -/

/-- The parts of a proof file: the reader undoes the writer on the records that fit and have the
numbers N. -/
theorem undoes_proofFile (D : Declared) (N : ThreeCounts) (h1 : D.setting.nonce ≤ 8)
    (h2 : D.setting.posB ≤ 8) :
    Undoes (ProofParsed.rd D N) (ProofParsed.bytes D) fun F =>
      F.fits D = true ∧ F.counts = N := by
  have A := undoes_pair (undoes_bytes 8) (undoes_pair undoes_copy (undoes_three D D.proof N h1 h2))
  unfold ProofParsed.rd
  refine undoes_map A _ (fun F => (F.head, F.copy, F.first, F.slot, F.shared, F.second)) ?_ ?_ ?_
  · intro _ _
    rfl
  · intro F _
    simp only [ProofParsed.bytes, ProofParsed.bytesAt, spThree, pair, id_eq,
      ByteArray.append_assoc]
  · intro F hF
    obtain ⟨h, hc⟩ := hF
    simp only [ProofParsed.fits, Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨a1, a3⟩, a4⟩, a5⟩, a6⟩ := h
    refine ⟨?_, trivial, ⟨a3, congrArg Prod.fst hc⟩, a4, ⟨a5, congrArg (fun y => y.2.1) hc⟩, a6,
      congrArg (fun y => y.2.2) hc⟩
    show F.head.size = 8
    rw [eq_of_bytes_beq _ _ a1]
    exact (size_headOf D.setting.field).2.2

/-- What the reader of a proof file's parts accepts has the numbers N, and is written to the bytes
that were read. -/
theorem cuts_proofFile (D : Declared) (N : ThreeCounts) (h1 : D.setting.nonce ≤ 8)
    (h2 : D.setting.posB ≤ 8) :
    Cuts (ProofParsed.rd D N) (ProofParsed.bytes D) fun F => F.counts = N := by
  have A := cuts_pair (cuts_of_only (only_bytes 8))
    (cuts_pair cuts_copy (cuts_three D D.proof N h1 h2))
  unfold ProofParsed.rd
  refine cuts_map A _ ?_ ?_
  · intro x _
    simp only [ProofParsed.bytes, ProofParsed.bytesAt, spThree, pair, id_eq,
      ByteArray.append_assoc]
  · intro x hx
    exact Prod.ext hx.2.2.1 (Prod.ext hx.2.2.2.2.1 hx.2.2.2.2.2)

/-- THE LAW OF A PROOF FILE. The reader of a whole proof file, told its three chains' numbers N,
gives F exactly where F fits the declared structure, has the numbers N, and the file is F's writing.
-/
theorem ProofParsed.read_iff (D : Declared) (N : ThreeCounts)
    (h1 : D.setting.nonce ≤ 8) (h2 : D.setting.posB ≤ 8) (file : ByteArray) (F : ProofParsed) :
    ProofParsed.read D N file = some F ↔
      F.fits D = true ∧ F.counts = N ∧ file = F.bytes D := by
  unfold ProofParsed.read
  rw [whole_iff_both (undoes_fit _ (undoes_proofFile D N h1 h2) fun _ h => h.1)
    (cuts_fit _ (cuts_proofFile D N h1 h2)) file F, and_assoc]

/-! ## 7. At a declared structure that passes its test on the setting -/

/-- The two bounds, from the test on the setting and the shape that all chains share. -/
theorem Declared.bounds (D : Declared) (h : D.settingOk = true) :
    D.setting.nonce ≤ 8 ∧ D.setting.posB ≤ 8 := by
  simp only [Declared.settingOk, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨by omega, by omega⟩

/-- The law of an entry file, at a D that passes `Declared.settingOk`. -/
theorem EntryParsed.read_iff_settingOk (D : Declared) (h : D.settingOk = true) (N : ChainCounts)
    (file : ByteArray) (F : EntryParsed) :
    EntryParsed.read D N file = some F ↔ F.fits D = true ∧ F.counts = N ∧ file = F.bytes D :=
  EntryParsed.read_iff D N (D.bounds h).1 (D.bounds h).2 file F

/-- The law of a key file, at a D that passes `Declared.settingOk`. -/
theorem KeyParsed.read_iff_settingOk (D : Declared) (h : D.settingOk = true)
    (N : ThreeCounts) (file : ByteArray) (F : KeyParsed) :
    KeyParsed.read D N file = some F ↔ F.fits D = true ∧ F.counts = N ∧ file = F.bytes D :=
  KeyParsed.read_iff D N (D.bounds h).1 (D.bounds h).2 file F

/-- The law of a proof file, at a D that passes `Declared.settingOk`. -/
theorem ProofParsed.read_iff_settingOk (D : Declared) (h : D.settingOk = true)
    (N : ThreeCounts) (file : ByteArray) (F : ProofParsed) :
    ProofParsed.read D N file = some F ↔
      F.fits D = true ∧ F.counts = N ∧ file = F.bytes D :=
  ProofParsed.read_iff D N (D.bounds h).1 (D.bounds h).2 file F

/-! ## 8. From the parts to the file -/

/-- Three chains with their slot, from the parts: each chain is read by the reader that tests the
form, from its place to the next; the slot is read between the first two. -/
theorem rdThree_of_parts (D : Declared) (T : ThreeDecl) (N : ThreeCounts)
    (file : ByteArray) (i1 i2 i3 i4 i5 : Nat) (X1 X2 X3 : ChainParsed) (s : SlotParsed)
    (c1 : ChainParsed.readFit D.setting T.first N.1 file i1 = some (X1, i2))
    (hs : rdSlot T.bind file i2 = some (s, i3))
    (c2 : ChainParsed.readFit D.setting T.shared N.2.1 file i3 = some (X2, i4))
    (c3 : ChainParsed.readFit D.setting T.second N.2.2 file i4 = some (X3, i5)) :
    rdThree D T N file i1 = some ((X1, s, X2, X3), i5) :=
  rdPair_some (rdFit_some c1).2
    (rdPair_some hs (rdPair_some (rdFit_some c2).2 (rdFit_some c3).2))

/-- AN ENTRY FILE FROM ITS PARTS. The first eight bytes are the declared head; the table is read
behind them; the link's chain is read by the reader that tests the form, told the numbers N, from
the place behind the table to the file's end. Then the reader of the whole file, told N, gives the
record of these three parts. -/
theorem EntryParsed.read_of_parts (D : Declared) (N : ChainCounts) (file head : ByteArray)
    (t : TableSt) (X : ChainParsed) (i : Nat) (h0 : rdBytes 8 file 0 = some (head, 8))
    (hd : head = headOf tagEntry D.setting.field)
    (ht : rdTable D.setting.field D.table file 8 = some (t, i))
    (hc : ChainParsed.readFit D.setting D.link N file i = some (X, file.size)) :
    EntryParsed.read D N file = some ⟨head, t, X⟩ := by
  refine whole_some (rdFit_of (rdMap_some (rdPair_some h0 (rdPair_some ht (rdFit_some hc).2))) ?_)
  simp only [EntryParsed.fits, Bool.and_eq_true]
  exact ⟨⟨by rw [hd]; exact bytes_beq_self _, (cuts_table _ _ file 8 t i ht).1⟩, (rdFit_some hc).1⟩

/-- A KEY FILE FROM ITS PARTS. The head, the table, the three chains, each read by the reader that
tests the form from its place to the next, the last to the file's end, and the slot, which fits. -/
theorem KeyParsed.read_of_parts (D : Declared) (N : ThreeCounts)
    (file head : ByteArray) (t : TableSt) (i1 i2 i3 i4 : Nat) (X1 X2 X3 : ChainParsed)
    (s : SlotParsed) (h0 : rdBytes 8 file 0 = some (head, 8))
    (hd : head = headOf tagKey D.setting.field)
    (ht : rdTable D.setting.field D.table file 8 = some (t, i1))
    (c1 : ChainParsed.readFit D.setting D.key.first N.1 file i1 = some (X1, i2))
    (hs : rdSlot D.key.bind file i2 = some (s, i3)) (fs : s.fits D.key.bind = true)
    (c2 : ChainParsed.readFit D.setting D.key.shared N.2.1 file i3 = some (X2, i4))
    (c3 : ChainParsed.readFit D.setting D.key.second N.2.2 file i4 = some (X3, file.size)) :
    KeyParsed.read D N file = some ⟨head, t, X1, s, X2, X3⟩ := by
  refine whole_some (rdFit_of (rdMap_some (rdPair_some h0 (rdPair_some ht
    (rdThree_of_parts D D.key N file i1 i2 i3 i4 file.size X1 X2 X3 s c1 hs c2 c3)))) ?_)
  simp only [KeyParsed.fits, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨by rw [hd]; exact bytes_beq_self _, (cuts_table _ _ file 8 t i1 ht).1⟩,
    (rdFit_some c1).1⟩, fs⟩, (rdFit_some c2).1⟩, (rdFit_some c3).1⟩

/-- A PROOF FILE FROM ITS PARTS. The head, the four bytes, the three chains and the slot, as for a
key file. -/
theorem ProofParsed.read_of_parts (D : Declared) (N : ThreeCounts)
    (file head : ByteArray) (copy : UInt32) (i1 i2 i3 i4 : Nat) (X1 X2 X3 : ChainParsed)
    (s : SlotParsed) (h0 : rdBytes 8 file 0 = some (head, 8))
    (hd : head = headOf tagProof D.setting.field) (hk : rdCopy file 8 = some (copy, i1))
    (c1 : ChainParsed.readFit D.setting D.proof.first N.1 file i1 = some (X1, i2))
    (hs : rdSlot D.proof.bind file i2 = some (s, i3)) (fs : s.fits D.proof.bind = true)
    (c2 : ChainParsed.readFit D.setting D.proof.shared N.2.1 file i3 = some (X2, i4))
    (c3 : ChainParsed.readFit D.setting D.proof.second N.2.2 file i4 = some (X3, file.size)) :
    ProofParsed.read D N file = some ⟨head, copy, X1, s, X2, X3⟩ := by
  refine whole_some (rdFit_of (rdMap_some (rdPair_some h0 (rdPair_some hk
    (rdThree_of_parts D D.proof N file i1 i2 i3 i4 file.size X1 X2 X3 s c1 hs c2 c3)))) ?_)
  simp only [ProofParsed.fits, Bool.and_eq_true]
  exact ⟨⟨⟨⟨by rw [hd]; exact bytes_beq_self _, (rdFit_some c1).1⟩, fs⟩, (rdFit_some c2).1⟩,
    (rdFit_some c3).1⟩

/-! ## 9. One file, with numbers: at most one record -/

/-- Two records of an entry file that fit one declared structure, have the same numbers and are
written to the same bytes are equal. -/
theorem EntryParsed.bytes_inj (D : Declared) (h1 : D.setting.nonce ≤ 8) (h2 : D.setting.posB ≤ 8)
    (F G : EntryParsed) (hF : F.fits D = true) (hG : G.fits D = true) (hc : F.counts = G.counts)
    (e : F.bytes D = G.bytes D) : F = G :=
  inj_of_undoes (undoes_entryFile D F.counts h1 h2) F G ⟨hF, rfl⟩ ⟨hG, hc.symm⟩ e

/-- The same of a key file. -/
theorem KeyParsed.bytes_inj (D : Declared) (h1 : D.setting.nonce ≤ 8) (h2 : D.setting.posB ≤ 8)
    (F G : KeyParsed) (hF : F.fits D = true) (hG : G.fits D = true) (hc : F.counts = G.counts)
    (e : F.bytes D = G.bytes D) : F = G :=
  inj_of_undoes (undoes_keyFile D F.counts h1 h2) F G ⟨hF, rfl⟩ ⟨hG, hc.symm⟩ e

/-- The same of a proof file. -/
theorem ProofParsed.bytes_inj (D : Declared) (h1 : D.setting.nonce ≤ 8) (h2 : D.setting.posB ≤ 8)
    (F G : ProofParsed) (hF : F.fits D = true) (hG : G.fits D = true) (hc : F.counts = G.counts)
    (e : F.bytes D = G.bytes D) : F = G :=
  inj_of_undoes (undoes_proofFile D F.counts h1 h2) F G ⟨hF, rfl⟩ ⟨hG, hc.symm⟩ e

end Fmt

#print axioms Fmt.EntryParsed.read_iff
#print axioms Fmt.KeyParsed.read_iff
#print axioms Fmt.ProofParsed.read_iff
#print axioms Fmt.EntryParsed.read_iff_settingOk
#print axioms Fmt.KeyParsed.read_iff_settingOk
#print axioms Fmt.ProofParsed.read_iff_settingOk
#print axioms Fmt.EntryParsed.read_of_parts
#print axioms Fmt.KeyParsed.read_of_parts
#print axioms Fmt.ProofParsed.read_of_parts
#print axioms Fmt.EntryParsed.bytes_inj
#print axioms Fmt.KeyParsed.bytes_inj
#print axioms Fmt.ProofParsed.bytes_inj
