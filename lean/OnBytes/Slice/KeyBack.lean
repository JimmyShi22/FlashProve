-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/KeyBack.lean: a stored table's record is read back off the program's key that was
written of it.

Why. `keyOf` (OnBytes/Slice/KeyOfRec.lean) writes a record over the field as the program's key of
the table. A description of the proof file is handed that key as a part of its instance. A law that
goes from the description's instance back to the frame's own (a request and a record) wants the
record as a function of the key. `recOfKey` (OnBytes/Slice/BlkKeyRec.lean) is that function at a
table's shape, and `keyOf_recOfKey` (OnBytes/Slice/KeyOfRecBack.lean) says that a fitting key is
written anew of what is read off it. Here is the other direction.
  `recBack v lg s k`: `recOfKey`'s text at three plain numbers in the place of a shape's.
  `recBack_eq_recOfKey`: at a shape's three numbers it is `recOfKey`: by definition.
  `recBack_keyOf`: recBack v lg s (keyOf (fun β : NZ => β.val) rec) = rec.
That two records with one key are one is shown: `keyOf_injective` (OnBytes/Slice/KeyOfRecInj.lean).
Limits. Nothing is said of a key that is no `keyOf` of a record: there `recBack` returns some
record (an entry that is not there is read as 0; a factor 0 as 1). The item's number is not read:
two keys that part in the item alone give one record. No code is made for `recBack`: it is for
statements. Nothing on any sample map, on a decoder or on soundness.
Terms: lean/GLOSSARY.md.

-/
import OnBytes.Slice.BlkKeyRec
import OnBytes.Slice.RecordRead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Slice
open Cb

/-- The record that stands in a key, at three plain numbers. -/
noncomputable def recBack (v lg s : ℕ) (k : TableKey) : RecP NZ v lg s :=
  (fun i => (fun t => readE ((k.seeds.getD i.val default).z.getD t.val zeroE),
      asFactor (readE (k.seeds.getD i.val default).beta)),
    fun q => readE (k.record.getD (Sz.rowNo q.1 * s + q.2.val) zeroE))

/-- At a shape's three numbers it is `recOfKey` (OnBytes/Slice/BlkKeyRec.lean). -/
theorem recBack_eq_recOfKey (sh : Params.IndexShape) (k : TableKey) :
    recBack sh.v sh.cubeBits sh.answers k = recOfKey sh k := rfl

/-- **What was written is read back.** -/
theorem recBack_keyOf {v lg s : ℕ} (rec : RecP NZ v lg s) :
    recBack v lg s (keyOf (fun β : NZ => β.val) rec) = rec := by
  apply Prod.ext
  · funext i
    apply Prod.ext
    · funext t
      show readE (((keyOf (fun β : NZ => β.val) rec).seeds.getD i.val default).z.getD t.val zeroE) =
        (rec.1 i).1 t
      have hp := keyOf_point (fun β : NZ => β.val) rec i
      obtain ⟨z, hz⟩ : ∃ z, z = ((keyOf (fun β : NZ => β.val) rec).seeds.getD i.val default).z :=
        ⟨_, rfl⟩
      rw [← hz] at hp ⊢
      have hl : z.length = lg := by
        have h0 := congrArg List.length hp
        rwa [List.length_map, List.length_ofFn] at h0
      have ht : t.val < z.length := by
        rw [hl]
        exact t.isLt
      have h1 : (z.map readE).getD t.val 0 = (List.ofFn (rec.1 i).1).getD t.val 0 := by rw [hp]
      rw [List.getD_eq_getElem _ _ (by rw [List.length_map]; exact ht), List.getElem_map,
        List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact t.isLt),
        List.getElem_ofFn] at h1
      rw [List.getD_eq_getElem _ _ ht]
      exact h1
    · show asFactor (readE ((keyOf (fun β : NZ => β.val) rec).seeds.getD i.val default).beta) =
        (rec.1 i).2
      rw [keyOf_beta]
      exact Subtype.ext (asFactor_val (rec.1 i).2.property)
  · funext q
    exact keyOf_record (fun β : NZ => β.val) rec q.1 q.2

end OnBytes.Slice

#print axioms OnBytes.Slice.recBack_eq_recOfKey
#print axioms OnBytes.Slice.recBack_keyOf
