-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/PageXStm.lean: a reader for the statement (`StmInv`, Run/PageX.lean) from the format's own
reader of a statement's items; and that reader at the statement of an entry's chain: the items of
two tables.

Run/PageX.lean's encoding asks for a function that reads the two roots back out of the statement's
bytes `D.stm r0 r1`, with both laws. The format has a reader for the root that a statement's item
holds (`Fmt.itemRoot`, Fmt/Rules8X.lean: the strict reader takes a stored tree's root by it). If
item 0 of `D.stm r0 r1` holds r0 and item 1 holds r1, for all r0, r1 of 32 bytes, that reader gives
`StmInv D`. The statement of an entry's chain is of that kind: the item "the first table" and the
item "the further table", each a root and a list of answers (`Fmt.tableItem`).
Definitions that compute; theorems.

Main names:
  `BothRoots D`, `unOf D`, `StmInv.ofRoots`: the reader from the format's reader of items. The
    second law holds by a comparison in `unOf` itself; the content is in the first.
  `tabVal`, `twoItems a₀ a₁ r0 r1`: the value of a table's item; the statement of two tables with
    the answers a₀, a₁.

  `twoItems_read`, `twoItems_root0`, `twoItems_root1`: what the format's readers make of it, if both
    items' values have fewer than 2^64 bytes.
  `bothRoots_two`, `stmInvTwo D a₀ a₁ hs h0 h1`: so a description whose statement is
    `twoItems a₀ a₁` has a reader, if the answers' bytes are few enough.

All of this is stated for any answers a₀, a₁. That `Fmt.M3.stmOf` (Fmt/M3Plan.lean) is `twoItems` at
no answers is not proved in this library.



Limits: the answers are constants of the description here, not an instance: any list of triples of
words, of any length; that a word is below the field's modulus is not asked. The two bounds of
`stmInvTwo` are on the answers' bytes: no lemma here gives these bytes' number from the list's
length (Run/PageXStmSize.lean). Nothing on a hash. Nothing on soundness.

Terms: lean/GLOSSARY.md.

-/
import Run.PageX
import Fmt.ParamsReadLawsProofs
import Fmt.M3Entry

set_option autoImplicit false

namespace Run.PQ
open Rom Compile Compile.Batch Iop

/-! ### From the format's reader of items -/

section
variable (D : XD)

/-- Item 0 of the statement holds the first root and item 1 the second, for all roots of 32
bytes. -/
def BothRoots : Prop :=
  ∀ r0 r1 : ByteArray, r0.size = 32 → r1.size = 32 →
    _root_.Fmt.itemRoot (D.stm r0 r1) 0 = some r0 ∧ _root_.Fmt.itemRoot (D.stm r0 r1) 1 = some r1

/-- The two roots that a statement's items 0 and 1 hold, as digests: given only if both have 32
bytes and the statement of the two is the string that was read. -/
def unOf (s : ByteArray) : Option (Dig 256 × Dig 256) :=
  match _root_.Fmt.itemRoot s 0, _root_.Fmt.itemRoot s 1 with
  | some a, some b =>
      if a.size = 32 ∧ b.size = 32 ∧ D.stm a b = s then some (bytesToDig a, bytesToDig b) else none
  | _, _ => none

variable {D} in
/-- A reader for the statement, from the format's reader of items. -/
def StmInv.ofRoots (h : BothRoots D) : StmInv D where
  un := unOf D
  un_stm := fun a b => by
    obtain ⟨h0, h1⟩ := h (digToBytes a) (digToBytes b) (size_digToBytes a) (size_digToBytes b)
    unfold unOf
    rw [h0, h1]
    show (if (digToBytes a).size = 32 ∧ (digToBytes b).size = 32 ∧
      D.stm (digToBytes a) (digToBytes b) = D.stm (digToBytes a) (digToBytes b) then
      some (bytesToDig (digToBytes a), bytesToDig (digToBytes b)) else none) = some (a, b)
    rw [if_pos ⟨size_digToBytes a, size_digToBytes b, rfl⟩, TieTree.bytes_dig, TieTree.bytes_dig]
  stm_un := fun s a b hs => by
    unfold unOf at hs
    split at hs
    · rename_i x y _ _
      by_cases hc : x.size = 32 ∧ y.size = 32 ∧ D.stm x y = s
      · rw [if_pos hc] at hs
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hs)
        rw [TieTree.dig_bytes x hc.1, TieTree.dig_bytes y hc.2.1]
        exact hc.2.2
      · rw [if_neg hc] at hs
        cases hs
    · cases hs

end

/-! ### The statement of two tables -/

/-- An answer of a table's record, as three words. -/
abbrev W3 : Type := UInt64 × UInt64 × UInt64

/-- The value of a table's item: the root as a string of bytes, then the answers. -/
def tabVal (r : ByteArray) (a : List W3) : ByteArray :=
  _root_.Fmt.text r ++ _root_.Fmt.list _root_.Fmt.ext a

theorem tableItem_val (name : String) (r : ByteArray) (a : List W3) :
    _root_.Fmt.tableItem name r a = _root_.Fmt.item name (tabVal r a) := rfl

/-- The value of a table's item begins with the root. -/
theorem tabVal_root (r : ByteArray) (a : List W3) (h : r.size < 2 ^ 64) :
    (_root_.Fmt.rdText (tabVal r a) 0).map (·.1) = some r := by
  have e := _root_.Fmt.undoes_text r h ByteArray.empty (_root_.Fmt.list _root_.Fmt.ext a)
  rw [ByteArray.empty_append, ByteArray.size_empty] at e
  show (_root_.Fmt.rdText (_root_.Fmt.text r ++ _root_.Fmt.list _root_.Fmt.ext a) 0).map (·.1) =
    some r
  rw [e]
  rfl

theorem tabVal_size (r : ByteArray) (a : List W3) :
    (tabVal r a).size = 8 + r.size + (_root_.Fmt.list _root_.Fmt.ext a).size := by
  simp only [tabVal, _root_.Fmt.text, ByteArray.size_append, _root_.Fmt.size_u64n]

/-- The statement of two tables, with their answers, as a function of the two roots. -/
def twoItems (a₀ a₁ : List W3) (r0 r1 : ByteArray) : ByteArray :=
  _root_.Fmt.tableItem "the first table" r0 a₀ ++ _root_.Fmt.tableItem "the further table" r1 a₁

/-- Its items: names and values. -/
def twoList (a₀ a₁ : List W3) (r0 r1 : ByteArray) : List (String × ByteArray) :=
  [("the first table", tabVal r0 a₀), ("the further table", tabVal r1 a₁)]

theorem twoItems_items (a₀ a₁ : List W3) (r0 r1 : ByteArray) :
    twoItems a₀ a₁ r0 r1 = _root_.Fmt.items (twoList a₀ a₁ r0 r1) := by
  simp only [twoItems, twoList, tableItem_val, _root_.Fmt.items, List.map_cons, List.map_nil,
    _root_.Fmt.cat_cons, _root_.Fmt.cat_nil, ByteArray.append_empty]

theorem items_two_size (a b : String × ByteArray) : 2 ≤ (_root_.Fmt.items [a, b]).size := by
  simp only [_root_.Fmt.items, List.map_cons, List.map_nil, _root_.Fmt.cat_cons,
    _root_.Fmt.cat_nil, _root_.Fmt.item, _root_.Fmt.textS, _root_.Fmt.text, _root_.Fmt.u64n,
    ByteArray.size_append, _root_.Fmt.size_u64]
  omega

/-- What the reader of items makes of it. -/
theorem twoItems_read (a₀ a₁ : List W3) (r0 r1 : ByteArray) (h0 : (tabVal r0 a₀).size < 2 ^ 64)
    (h1 : (tabVal r1 a₁).size < 2 ^ 64) :
    _root_.Fmt.rdItems (twoItems a₀ a₁ r0 r1).size (twoItems a₀ a₁ r0 r1) 0 =
      some (twoList a₀ a₁ r0 r1, (twoItems a₀ a₁ r0 r1).size) := by
  have ok : ∀ x ∈ twoList a₀ a₁ r0 r1, _root_.Fmt.okItem x := by
    intro x hx
    simp only [twoList, List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl
    · exact ⟨(by decide : _root_.Fmt.okName "the first table" = true),
        (by decide : (_root_.Fmt.ascii "the first table").size < 2 ^ 64), h0⟩
    · exact ⟨(by decide : _root_.Fmt.okName "the further table" = true),
        (by decide : (_root_.Fmt.ascii "the further table").size < 2 ^ 64), h1⟩
  have e := _root_.Fmt.items_back _ ok (twoItems a₀ a₁ r0 r1).size (by
    rw [twoItems_items]
    exact items_two_size _ _) ByteArray.empty
  rw [ByteArray.empty_append, ByteArray.size_empty, ← twoItems_items] at e
  exact e

/-- The format's reader takes the first root out of item 0. -/
theorem twoItems_root0 (a₀ a₁ : List W3) (r0 r1 : ByteArray) (h0 : (tabVal r0 a₀).size < 2 ^ 64)
    (h1 : (tabVal r1 a₁).size < 2 ^ 64) :
    _root_.Fmt.itemRoot (twoItems a₀ a₁ r0 r1) 0 = some r0 := by
  unfold _root_.Fmt.itemRoot
  rw [twoItems_read a₀ a₁ r0 r1 h0 h1]
  exact tabVal_root r0 a₀ (by rw [tabVal_size] at h0; omega)

/-- And the second out of item 1. -/
theorem twoItems_root1 (a₀ a₁ : List W3) (r0 r1 : ByteArray) (h0 : (tabVal r0 a₀).size < 2 ^ 64)
    (h1 : (tabVal r1 a₁).size < 2 ^ 64) :
    _root_.Fmt.itemRoot (twoItems a₀ a₁ r0 r1) 1 = some r1 := by
  unfold _root_.Fmt.itemRoot
  rw [twoItems_read a₀ a₁ r0 r1 h0 h1]
  exact tabVal_root r1 a₁ (by rw [tabVal_size] at h1; omega)

/-- A description whose statement is that of two tables holds both roots in its items. -/
theorem bothRoots_two (D : XD) (a₀ a₁ : List W3) (hs : D.stm = twoItems a₀ a₁)
    (h0 : (_root_.Fmt.list _root_.Fmt.ext a₀).size + 40 < 2 ^ 64)
    (h1 : (_root_.Fmt.list _root_.Fmt.ext a₁).size + 40 < 2 ^ 64) : BothRoots D :=
  fun r0 r1 e0 e1 => by
    have k0 : (tabVal r0 a₀).size < 2 ^ 64 := by rw [tabVal_size, e0]; omega
    have k1 : (tabVal r1 a₁).size < 2 ^ 64 := by rw [tabVal_size, e1]; omega
    rw [hs]
    exact ⟨twoItems_root0 a₀ a₁ r0 r1 k0 k1, twoItems_root1 a₀ a₁ r0 r1 k0 k1⟩

/-- The reader for the statement of two tables. -/
def stmInvTwo (D : XD) (a₀ a₁ : List W3) (hs : D.stm = twoItems a₀ a₁)
    (h0 : (_root_.Fmt.list _root_.Fmt.ext a₀).size + 40 < 2 ^ 64)
    (h1 : (_root_.Fmt.list _root_.Fmt.ext a₁).size + 40 < 2 ^ 64) : StmInv D :=
  StmInv.ofRoots (bothRoots_two D a₀ a₁ hs h0 h1)

end Run.PQ
