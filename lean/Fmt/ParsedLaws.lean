-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/ParsedLaws.lean: laws on the functions of Fmt/Parsed.lean: the roots that a reader takes out of
an entry's statement, the 32 bytes that it takes out of a shared chain's statement, and the
statement that the writer of a chain is one-to-one where form and numbers are fixed.

A chain that reads stored tables names them in its statement, and the readers take the root of a
stored tree out of an item of the statement (`itemRoot`, Fmt/Rules8X.lean). The first facts say that
for the statement of an entry's link these are the roots of the two tables from which the statement
was made. Each asks that the values of the statement's items have fewer than 2 ^ 64 bytes, since an
item's length is one word.

1. What the file contains.
    `TableSt.value`: the value of a table's item. `EntryStm.items`, `sharedItems`: names and values.
    `Spec.bytes_inj`: a statement. On chains that fit one declared chain under one setting and have
      the same numbers (`ChainParsed.counts`), the writer is one-to-one. Its proof:
      Fmt/ParsedReadLaws.lean (`bytes_inj`).

2. What is checked when the file compiles. The proofs.

3. Theorems. `EntryStm.bytes_read`; `EntryStm.root0`, `EntryStm.root1`; `TableSt.item_read`,
`TableSt.item_root`; `sharedStm_read`, `sharedStm_root`, `sharedStm_item`.

4. What is not claimed. `Spec.bytes_inj` is stated here and proved in Fmt/ParsedReadLaws.lean.
Nothing on the statements of the other chains. The port has the first facts for its own types
(OnBytes/Params/StatementLaws.lean: `Link.statement_root0`, `Link.statement_root1`,
`Shared.statement_root0`); the proofs here follow these line by line. Files of Fmt/ and Run/ import
no file of OnBytes/.

Terms: lean/GLOSSARY.md.

-/
import Fmt.Parsed
import Fmt.ParamsReadLawsProofs

namespace Fmt

/-- The value of a table's item: the root as a string of bytes, then the record's answers. -/
def TableSt.value (t : TableSt) : ByteArray := text t.root ++ list ext t.answers

/-- A table's item is the item of its name with this value. -/
theorem tableItem_value (name : String) (t : TableSt) :
    tableItem name t.root t.answers = item name t.value := rfl

/-- The value of a table's item begins with the root, if the root has fewer than 2 ^ 64 bytes. -/
theorem TableSt.value_root (t : TableSt) (h : t.root.size < 2 ^ 64) :
    (rdText t.value 0).map (·.1) = some t.root := by
  have a := undoes_text t.root h ByteArray.empty (list ext t.answers)
  rw [ByteArray.empty_append, ByteArray.size_empty] at a
  show (rdText (text t.root ++ list ext t.answers) 0).map (·.1) = some t.root
  rw [a]; rfl

/-- The root's bytes are among the value's. -/
theorem TableSt.root_size_le (t : TableSt) : t.root.size ≤ t.value.size := by
  simp only [TableSt.value, text, ByteArray.size_append]; omega

/-- The bytes of two items number at least two: as many as the items. -/
theorem two_le_items (a b : String × ByteArray) : 2 ≤ (items [a, b]).size := by
  simp only [items, List.map_cons, List.map_nil, cat_cons, cat_nil, item, textS, text, u64n,
    ByteArray.size_append, size_u64]
  omega

/-- The items of an entry's statement: names and values. -/
def EntryStm.items (x : EntryStm) : List (String × ByteArray) :=
  [("the first table", x.first.value), ("the further table", x.further.value)]

/-- An entry's statement spells its items. -/
theorem EntryStm.bytes_items (x : EntryStm) : x.bytes = Fmt.items x.items := by
  simp only [EntryStm.bytes, EntryStm.items, tableItem_value, Fmt.items, List.map_cons,
    List.map_nil, cat_cons, cat_nil, ByteArray.append_empty]

/-- What the reader of items makes of an entry's statement, if the values of both tables' items
have fewer than 2 ^ 64 bytes: its two items, and the place after the last byte. -/
theorem EntryStm.bytes_read (x : EntryStm) (h0 : x.first.value.size < 2 ^ 64)
    (h1 : x.further.value.size < 2 ^ 64) :
    rdItems x.bytes.size x.bytes 0 = some (x.items, x.bytes.size) := by
  have ok : ∀ y ∈ x.items, okItem y := by
    intro y hy
    simp only [EntryStm.items, List.mem_cons, List.mem_nil_iff, or_false] at hy
    rcases hy with rfl | rfl
    · exact ⟨(by decide : okName "the first table" = true),
        (by decide : (ascii "the first table").size < 2 ^ 64), h0⟩
    · exact ⟨(by decide : okName "the further table" = true),
        (by decide : (ascii "the further table").size < 2 ^ 64), h1⟩
  have a := items_back _ ok x.bytes.size (by
    rw [EntryStm.bytes_items]
    exact two_le_items _ _) ByteArray.empty
  rw [ByteArray.empty_append, ByteArray.size_empty, ← EntryStm.bytes_items] at a
  exact a

/-- A reader takes the first table's root out of item 0 of an entry's statement. -/
theorem EntryStm.root0 (x : EntryStm) (h0 : x.first.value.size < 2 ^ 64)
    (h1 : x.further.value.size < 2 ^ 64) : itemRoot x.bytes 0 = some x.first.root := by
  unfold itemRoot
  rw [EntryStm.bytes_read x h0 h1]
  exact TableSt.value_root x.first (Nat.lt_of_le_of_lt (TableSt.root_size_le x.first) h0)

/-- A reader takes the further table's root out of item 1 of an entry's statement. -/
theorem EntryStm.root1 (x : EntryStm) (h0 : x.first.value.size < 2 ^ 64)
    (h1 : x.further.value.size < 2 ^ 64) : itemRoot x.bytes 1 = some x.further.root := by
  unfold itemRoot
  rw [EntryStm.bytes_read x h0 h1]
  exact TableSt.value_root x.further (Nat.lt_of_le_of_lt (TableSt.root_size_le x.further) h1)

/-- The statement of a key file's one-time chain spells one item. -/
theorem TableSt.item_items (t : TableSt) : t.item = items [("table", t.value)] := by
  simp only [TableSt.item, tableItem_value, items, List.map_cons, List.map_nil, cat_cons, cat_nil,
    ByteArray.append_empty]

/-- The bytes of one item number at least one. -/
theorem one_le_items (a : String × ByteArray) : 1 ≤ (items [a]).size := by
  simp only [items, List.map_cons, List.map_nil, cat_cons, cat_nil, item, textS, text, u64n,
    ByteArray.size_append, size_u64]
  omega

/-- What the reader of items makes of the statement of a key file's one-time chain. -/
theorem TableSt.item_read (t : TableSt) (h : t.value.size < 2 ^ 64) :
    rdItems t.item.size t.item 0 = some ([("table", t.value)], t.item.size) := by
  have ok : ∀ y ∈ [("table", t.value)], okItem y := by
    intro y hy
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hy
    subst hy
    exact ⟨(by decide : okName "table" = true), (by decide : (ascii "table").size < 2 ^ 64), h⟩
  have a := items_back _ ok t.item.size (by
    rw [TableSt.item_items]
    exact one_le_items _) ByteArray.empty
  rw [ByteArray.empty_append, ByteArray.size_empty, ← TableSt.item_items] at a
  exact a

/-- A reader takes the table's root out of item 0 of that statement. -/
theorem TableSt.item_root (t : TableSt) (h : t.value.size < 2 ^ 64) :
    itemRoot t.item 0 = some t.root := by
  unfold itemRoot
  rw [TableSt.item_read t h]
  exact TableSt.value_root t (Nat.lt_of_le_of_lt (TableSt.root_size_le t) h)

/-- The items of a shared chain's statement: names and values. -/
def sharedItems (t : TableSt) (bindRoot : ByteArray) : List (String × ByteArray) :=
  [("table", t.value), (bindRootName, bindRoot)]

/-- A shared chain's statement spells its items. -/
theorem sharedStm_items (t : TableSt) (bindRoot : ByteArray) :
    sharedStm t bindRoot = items (sharedItems t bindRoot) := by
  simp only [sharedStm, TableSt.item, sharedItems, tableItem_value, items, List.map_cons,
    List.map_nil, cat_cons, cat_nil, ByteArray.append_empty]

/-- What the reader of items makes of a shared chain's statement. -/
theorem sharedStm_read (t : TableSt) (bindRoot : ByteArray) (h0 : t.value.size < 2 ^ 64)
    (h1 : bindRoot.size < 2 ^ 64) :
    rdItems (sharedStm t bindRoot).size (sharedStm t bindRoot) 0 =
      some (sharedItems t bindRoot, (sharedStm t bindRoot).size) := by
  have ok : ∀ y ∈ sharedItems t bindRoot, okItem y := by
    intro y hy
    simp only [sharedItems, List.mem_cons, List.mem_nil_iff, or_false] at hy
    rcases hy with rfl | rfl
    · exact ⟨(by decide : okName "table" = true), (by decide : (ascii "table").size < 2 ^ 64), h0⟩
    · exact ⟨(by decide : okName bindRootName = true),
        (by decide : (ascii bindRootName).size < 2 ^ 64), h1⟩
  have a := items_back _ ok (sharedStm t bindRoot).size (by
    rw [sharedStm_items]
    exact two_le_items _ _) ByteArray.empty
  rw [ByteArray.empty_append, ByteArray.size_empty, ← sharedStm_items] at a
  exact a

/-- A reader takes the table's root out of item 0 of a shared chain's statement. -/
theorem sharedStm_root (t : TableSt) (bindRoot : ByteArray) (h0 : t.value.size < 2 ^ 64)
    (h1 : bindRoot.size < 2 ^ 64) : itemRoot (sharedStm t bindRoot) 0 = some t.root := by
  unfold itemRoot
  rw [sharedStm_read t bindRoot h0 h1]
  exact TableSt.value_root t (Nat.lt_of_le_of_lt (TableSt.root_size_le t) h0)

/-- The value of item 1 of a shared chain's statement is the binding tree's root: the bytes that
stand for the chain's random bytes in case (b) of R4.5 (`RandAt.item 1`). -/
theorem sharedStm_item (t : TableSt) (bindRoot : ByteArray) (h0 : t.value.size < 2 ^ 64)
    (h1 : bindRoot.size < 2 ^ 64) : itemValue (sharedStm t bindRoot) 1 = some bindRoot := by
  unfold itemValue
  rw [sharedStm_read t bindRoot h0 h1]
  rfl

/-- The statement; its proof is `bytes_inj` (Fmt/ParsedReadLaws.lean). Two chains that fit one
declared chain under one setting, have the same numbers of listed positions, columns and given
digests, and are written to the same bytes under a plan with the setting's two widths, are equal. -/
def Spec.bytes_inj : Prop :=
  ∀ (S : PlanSetting) (P : Plan) (c : ChainDecl) (X Y : ChainParsed),
    P.nonce = S.nonce → P.posB = S.posB → S.nonce ≤ 8 → S.posB ≤ 8 →
    X.fits S c = true → Y.fits S c = true → X.counts = Y.counts → X.bytes P = Y.bytes P → X = Y

end Fmt

#print axioms Fmt.EntryStm.root0
#print axioms Fmt.EntryStm.root1
#print axioms Fmt.TableSt.item_root
#print axioms Fmt.sharedStm_root
#print axioms Fmt.sharedStm_item
