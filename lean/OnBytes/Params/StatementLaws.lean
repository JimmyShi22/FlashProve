-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/StatementLaws.lean: the roots that the strict reader takes out of a statement.

A chain that reads stored tables names them in its statement. The strict reader takes the root of
a stored tree out of an item of the statement (`Fmt.itemRoot`). The facts here say that for the
statements of OnBytes/Params/Chains.lean these are the roots from which the statements were made.
Each fact asks that the values of the statement's items have fewer than 2 ^ 64 bytes.

Main statements: `tableValue_root`, `Link.statement_root0`, `Link.statement_root1`,
`Shared.statement_root0`.
What is not claimed: anything on the statements of the other chains.
-/
import Fmt.ParamsReadLawsProofs
import OnBytes.Params.Chains

namespace OnBytes.Params

/-- The value of a table's item: the root as a string of bytes, then the record's answers. -/
def tableValue (t : TableName) : ByteArray :=
  Fmt.text t.root ++ Fmt.list Fmt.ext (t.answers.map E.triple)

/-- A table's item is the item of its name with this value. -/
theorem tableItem_eq (name : String) (t : TableName) :
    Fmt.tableItem name t.root (t.answers.map E.triple) = Fmt.item name (tableValue t) := rfl

/-- The value of a table's item begins with the root, if the root has fewer than 2 ^ 64 bytes. -/
theorem tableValue_root (t : TableName) (h : t.root.size < 2 ^ 64) :
    (Fmt.rdText (tableValue t) 0).map (·.1) = some t.root := by
  have a := Fmt.undoes_text t.root h ByteArray.empty (Fmt.list Fmt.ext (t.answers.map E.triple))
  rw [ByteArray.empty_append, ByteArray.size_empty] at a
  show (Fmt.rdText (Fmt.text t.root ++ Fmt.list Fmt.ext (t.answers.map E.triple)) 0).map (·.1) =
    some t.root
  rw [a]; rfl

/-- The root's bytes are among the value's. -/
theorem root_size_le (t : TableName) : t.root.size ≤ (tableValue t).size := by
  simp only [tableValue, Fmt.text, ByteArray.size_append]; omega

/-- The bytes of two items number at least two: as many as the items. -/
theorem items_two_size (a b : String × ByteArray) : 2 ≤ (Fmt.items [a, b]).size := by
  simp only [Fmt.items, List.map_cons, List.map_nil, Fmt.cat_cons, Fmt.cat_nil, Fmt.item,
    Fmt.textS, Fmt.text, Fmt.u64n, ByteArray.size_append, Fmt.size_u64]
  omega

/-- The items of a link's statement: names and values. -/
def Link.items (first further : TableName) : List (String × ByteArray) :=
  [("the first table", tableValue first), ("the further table", tableValue further)]

/-- A link's statement spells its items. -/
theorem Link.statement_items (first further : TableName) :
    Link.statement first further = Fmt.items (Link.items first further) := by
  simp only [Link.statement, Link.items, tableItem_eq, Fmt.items, List.map_cons, List.map_nil,
    Fmt.cat_cons, Fmt.cat_nil, ByteArray.append_empty]

/-- What the reader of items makes of a link's statement, if the values of both tables' items have
fewer than 2 ^ 64 bytes: its two items, and the place after the last byte. -/
theorem Link.statement_read (first further : TableName) (h0 : (tableValue first).size < 2 ^ 64)
    (h1 : (tableValue further).size < 2 ^ 64) :
    Fmt.rdItems (Link.statement first further).size (Link.statement first further) 0 =
      some (Link.items first further, (Link.statement first further).size) := by
  have ok : ∀ x ∈ Link.items first further, Fmt.okItem x := by
    intro x hx
    simp only [Link.items, List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl
    · exact ⟨(by decide : Fmt.okName "the first table" = true),
        (by decide : (Fmt.ascii "the first table").size < 2 ^ 64), h0⟩
    · exact ⟨(by decide : Fmt.okName "the further table" = true),
        (by decide : (Fmt.ascii "the further table").size < 2 ^ 64), h1⟩
  have a := Fmt.items_back _ ok (Link.statement first further).size (by
    rw [Link.statement_items]
    exact items_two_size _ _) ByteArray.empty
  rw [ByteArray.empty_append, ByteArray.size_empty, ← Link.statement_items] at a
  exact a

/-- The strict reader takes the first table's root out of item 0 of a link's statement, if the
values of both tables' items have fewer than 2 ^ 64 bytes. -/
theorem Link.statement_root0 (first further : TableName) (h0 : (tableValue first).size < 2 ^ 64)
    (h1 : (tableValue further).size < 2 ^ 64) :
    Fmt.itemRoot (Link.statement first further) 0 = some first.root := by
  unfold Fmt.itemRoot
  rw [Link.statement_read first further h0 h1]
  exact tableValue_root first (Nat.lt_of_le_of_lt (root_size_le first) h0)

/-- The strict reader takes the further table's root out of item 1 of a link's statement, if the
values of both tables' items have fewer than 2 ^ 64 bytes. -/
theorem Link.statement_root1 (first further : TableName) (h0 : (tableValue first).size < 2 ^ 64)
    (h1 : (tableValue further).size < 2 ^ 64) :
    Fmt.itemRoot (Link.statement first further) 1 = some further.root := by
  unfold Fmt.itemRoot
  rw [Link.statement_read first further h0 h1]
  exact tableValue_root further (Nat.lt_of_le_of_lt (root_size_le further) h1)

/-- The items of a shared chain's statement: names and values. -/
def Shared.items (table : TableName) (bindingRoot : ByteArray) : List (String × ByteArray) :=
  [("table", tableValue table), (Fmt.bindRootName, bindingRoot)]

/-- A shared chain's statement spells its items. -/
theorem Shared.statement_items (table : TableName) (bindingRoot : ByteArray) :
    Shared.statement table bindingRoot = Fmt.items (Shared.items table bindingRoot) := by
  simp only [Shared.statement, Shared.items, tableItem_eq, Fmt.items, List.map_cons, List.map_nil,
    Fmt.cat_cons, Fmt.cat_nil, ByteArray.append_empty]

/-- The strict reader takes the table's root out of item 0 of a shared chain's statement, if the
value of the table's item and the binding tree's root have fewer than 2 ^ 64 bytes each. -/
theorem Shared.statement_root0 (table : TableName) (bindingRoot : ByteArray)
    (h0 : (tableValue table).size < 2 ^ 64) (h1 : bindingRoot.size < 2 ^ 64) :
    Fmt.itemRoot (Shared.statement table bindingRoot) 0 = some table.root := by
  have ok : ∀ x ∈ Shared.items table bindingRoot, Fmt.okItem x := by
    intro x hx
    simp only [Shared.items, List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl
    · exact ⟨(by decide : Fmt.okName "table" = true),
        (by decide : (Fmt.ascii "table").size < 2 ^ 64), h0⟩
    · exact ⟨(by decide : Fmt.okName Fmt.bindRootName = true),
        (by decide : (Fmt.ascii Fmt.bindRootName).size < 2 ^ 64), h1⟩
  have a := Fmt.items_back _ ok (Shared.statement table bindingRoot).size (by
    rw [Shared.statement_items]
    exact items_two_size _ _) ByteArray.empty
  rw [ByteArray.empty_append, ByteArray.size_empty, ← Shared.statement_items] at a
  unfold Fmt.itemRoot
  rw [a]
  exact tableValue_root table (Nat.lt_of_le_of_lt (root_size_le table) h0)

end OnBytes.Params
