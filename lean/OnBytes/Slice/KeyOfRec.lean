-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/KeyOfRec.lean: a stored table's record over the field, written as the program's key of
the table.

The program's blocks take what a verifier knows of a table besides its shape as a `TableKey`
(OnBytes/Iop/Foldeq.lean): the number of the statement's item with the table's root; the record, an
array in which entry r * s + i is the answer of row r under seed i; the s seeds, each a point and a
factor. Over the field a record is a seed and the answers of every row (Cb/Ld/LdFoldEq.lean:
`LdIx.Rec`); at a sample map with s answers, a point of lg coordinates and a factor for each, that
is a pair of functions (`RecP`). `keyOf` writes such a pair as a key, with the item 0. It is a plain
definition: Lean's evaluator can run it. The type B of factors and how a factor is read (val) are
letters, so that it serves for the units of the field and for the elements other than 0.

What is shown: the key's sizes fit a shape with these numbers (`keyOf_fits`); read back in the
field, the key's record and seeds are the pair's (`keyOf_record`, `keyOf_seeds`, `keyOf_point`,
`keyOf_beta`). `KeyIs` is the relation "the key holds the record", for any key; the written key has
it (`keyIs_keyOf`).

Main definitions: `writeE`, `RecP`, `keyOf`, `KeyIs`.
Main theorems: `readE_writeE`, `keyOf_item`, `keyOf_size`, `keyOf_seeds_length`, `keyOf_fits`,
`keyOf_record`, `keyOf_seeds`, `keyOf_point`, `keyOf_beta`, `keyIs_keyOf`.

Not claimed. That a key which a reader has read is `keyOf` of some pair. Nothing on any sample map,
on a decoder or on soundness.

-/
import OnBytes.Slice.ProgField
import OnBytes.Slice.KeyPlaces
import OnBytes.Iop.Foldeq

set_option autoImplicit false

namespace OnBytes.Slice
open Cb

/-- The program's element, with words below the prime, that is read as x. -/
def writeE (x : GE) : E := E.ofTriple (ofE x)

/-- What is written is read back. -/
theorem readE_writeE (x : GE) : readE (writeE x) = x := by
  unfold writeE
  rw [readE_ofTriple, toE_ofE]

/-- **A record over the field, in plain letters**: for each of s answers a point of lg coordinates
and a factor; and the answers of each of the 2 ^ v rows. B: the type of factors. -/
abbrev RecP (B : Type) (v lg s : ℕ) : Type :=
  (Fin s → (Fin lg → GE) × B) × ((Fin v → Bool) × Fin s → GE)

section
variable {B : Type} (val : B → GE) {v lg s : ℕ} (rec : RecP B v lg s)

/-- There is an answer, if the record's array has a place. -/
theorem pos_of_place (n : Fin (2 ^ v * s)) : 0 < s :=
  Nat.pos_of_ne_zero fun h => by
    have h1 := n.isLt
    simp [h] at h1

/-- **The program's key of a table with this record**: the item 0; entry r * s + i of the array is
the answer of the row with the number r under seed i; the seeds in their order. -/
def keyOf : TableKey where
  item := 0
  record := Array.ofFn fun n : Fin (2 ^ v * s) =>
    writeE (rec.2 (vtx v (n.val / s), ⟨n.val % s, Nat.mod_lt _ (pos_of_place n)⟩))
  seeds := List.ofFn fun i : Fin s =>
    ⟨List.ofFn fun t : Fin lg => writeE ((rec.1 i).1 t), writeE (val (rec.1 i).2)⟩

/-- The table's root is the statement's item 0. -/
theorem keyOf_item : (keyOf val rec).item = 0 := rfl

/-- The array has an entry for each row and answer. -/
theorem keyOf_size : (keyOf val rec).record.size = 2 ^ v * s := Array.size_ofFn

/-- There is a seed for each answer. -/
theorem keyOf_seeds_length : (keyOf val rec).seeds.length = s := List.length_ofFn

/-- **The key's sizes fit a shape with these numbers.** -/
theorem keyOf_fits (sh : Params.IndexShape) (hv : sh.v = v) (hs : sh.answers = s)
    (hl : sh.cubeBits = lg) : (keyOf val rec).fits sh = true := by
  unfold TableKey.fits Params.IndexShape.rows
  rw [keyOf_size, keyOf_seeds_length, hv, hs, hl]
  simp only [beq_self_eq_true, Bool.true_and, List.all_eq_true]
  intro x hx
  obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hx
  simp [List.length_ofFn]

/-- **The array, read back**: entry r * s + i is the answer of row r under seed i. -/
theorem keyOf_record (r : Fin v → Bool) (i : Fin s) :
    readE ((keyOf val rec).record.getD (Sz.rowNo r * s + i.val) zeroE) = rec.2 (r, i) := by
  have hs : 0 < s := Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt
  have hlt : Sz.rowNo r * s + i.val < 2 ^ v * s := by
    have h1 : (Sz.rowNo r + 1) * s ≤ 2 ^ v * s := Nat.mul_le_mul_right s (rowNo_lt r)
    have h2 : Sz.rowNo r * s + i.val < (Sz.rowNo r + 1) * s := by
      rw [Nat.add_mul, Nat.one_mul]
      exact Nat.add_lt_add_left i.isLt _
    exact Nat.lt_of_lt_of_le h2 h1
  have hd : (Sz.rowNo r * s + i.val) / s = Sz.rowNo r := by
    rw [Nat.mul_comm, Nat.mul_add_div hs, Nat.div_eq_of_lt i.isLt, Nat.add_zero]
  have hm : (Sz.rowNo r * s + i.val) % s = i.val := by
    rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt i.isLt]
  have e : (keyOf val rec).record.getD (Sz.rowNo r * s + i.val) zeroE =
      writeE (rec.2 (vtx v ((Sz.rowNo r * s + i.val) / s),
        ⟨(Sz.rowNo r * s + i.val) % s, Nat.mod_lt _ hs⟩)) := by
    unfold keyOf
    simp [Array.getD, hlt]
  have hp : ((vtx v ((Sz.rowNo r * s + i.val) / s),
      ⟨(Sz.rowNo r * s + i.val) % s, Nat.mod_lt _ hs⟩) : (Fin v → Bool) × Fin s) = (r, i) :=
    Prod.ext (show vtx v ((Sz.rowNo r * s + i.val) / s) = r by
      rw [hd]
      exact funext fun t => testBit_rowNo r t) (Fin.ext hm)
  rw [e, readE_writeE, hp]

/-- **The seeds, read back**, as one list: each seed's point and factor. -/
theorem keyOf_seeds :
    ((keyOf val rec).seeds.map fun x => (x.z.map readE, readE x.beta)) =
      List.ofFn fun i : Fin s => (List.ofFn (rec.1 i).1, val (rec.1 i).2) := by
  unfold keyOf
  simp [List.map_ofFn, Function.comp_def, readE_writeE]

/-- **A seed's point, read back.** -/
theorem keyOf_point (i : Fin s) :
    (((keyOf val rec).seeds.getD i.val default).z.map readE) = List.ofFn (rec.1 i).1 := by
  have e : (keyOf val rec).seeds.getD i.val default =
      ⟨List.ofFn fun t : Fin lg => writeE ((rec.1 i).1 t), writeE (val (rec.1 i).2)⟩ := by
    unfold keyOf
    simp [List.getD, i.isLt]
  rw [e]
  simp [List.map_ofFn, Function.comp_def, readE_writeE]

/-- **A seed's factor, read back.** -/
theorem keyOf_beta (i : Fin s) :
    readE ((keyOf val rec).seeds.getD i.val default).beta = val (rec.1 i).2 := by
  have e : (keyOf val rec).seeds.getD i.val default =
      ⟨List.ofFn fun t : Fin lg => writeE ((rec.1 i).1 t), writeE (val (rec.1 i).2)⟩ := by
    unfold keyOf
    simp [List.getD, i.isLt]
  rw [e]
  exact readE_writeE _

end

/-- **The program's key of a table holds the record rec**, at a table of the shape sh: the table's
root is the statement's item 0; the shape has the record's three numbers; the key's sizes fit the
shape; read in the field, the key's seeds are the record's, and entry r * s + i of its array is the
record's answer of row r under seed i. -/
structure KeyIs {B : Type} (val : B → GE) {v lg s : ℕ} (sh : Params.IndexShape) (key : TableKey)
    (rec : RecP B v lg s) : Prop where
  item : key.item = 0
  vars : sh.v = v
  answers : sh.answers = s
  cube : sh.cubeBits = lg
  fits : key.fits sh = true
  seeds : (key.seeds.map fun x => (x.z.map readE, readE x.beta)) =
    List.ofFn fun i : Fin s => (List.ofFn (rec.1 i).1, val (rec.1 i).2)
  record : ∀ (r : Fin v → Bool) (i : Fin s),
    readE (key.record.getD (Sz.rowNo r * s + i.val) zeroE) = rec.2 (r, i)

/-- **The key that is written of a record holds it.** -/
theorem keyIs_keyOf {B : Type} (val : B → GE) {v lg s : ℕ} (rec : RecP B v lg s)
    (sh : Params.IndexShape) (hv : sh.v = v) (hs : sh.answers = s) (hl : sh.cubeBits = lg) :
    KeyIs val sh (keyOf val rec) rec :=
  ⟨rfl, hv, hs, hl, keyOf_fits val rec sh hv hs hl, keyOf_seeds val rec, keyOf_record val rec⟩

end OnBytes.Slice
