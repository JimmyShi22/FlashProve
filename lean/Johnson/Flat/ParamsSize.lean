-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Flat/ParamsSize.lean: HOW MANY BYTES A CHAIN's PARAMETER BYTES HAVE: a law on the speller
(`Fmt.paramsBytes`, Fmt/Rules4.lean), general in the plan.

Why. The law by which spelled items are read back as they were spelled asks that the parameter bytes
are fewer than 2 ^ 64 (`Params.Given.read_items`, OnBytes/Params/ReadBackLaws.lean). No theorem
bounded them.
  `size_cat_map`      the size of spellings in a row is the sum of their sizes
  `size_list`         a list of values: a word and the sum of their sizes
  `size_entry`        an entry of a plan: 96 bytes and its name's
  `size_item`         an item: 16 bytes, its name's and its value's
  `size_paramsBytes`  **the whole, as a sum**
  `size_entries_le`   entries with names of at most B bytes: at most (their number) * (96 + B) bytes
Limits. Arithmetic on sizes. Nothing on any plan.

-/
import Fmt.Rules4
import Fmt.Rules1Laws
import Fmt.Rules23Laws

set_option autoImplicit false

namespace Fmt

theorem size_cat_map {α : Type} (f : α → ByteArray) :
    ∀ l : List α, (cat (l.map f)).size = (l.map fun x => (f x).size).sum
  | [] => rfl
  | x :: l => by
    rw [List.map_cons, cat_cons, ByteArray.size_append, size_cat_map f l, List.map_cons,
      List.sum_cons]

theorem size_list {α : Type} (sp : α → ByteArray) (l : List α) :
    (list sp l).size = 8 + (l.map fun x => (sp x).size).sum := by
  unfold list
  rw [ByteArray.size_append, size_u64n, size_cat_map]

theorem size_textS (s : String) : (textS s).size = 8 + (ascii s).size := by
  unfold textS text
  rw [ByteArray.size_append, size_u64n]

theorem size_entry (e : Entry) : e.bytes.size = 96 + (ascii e.name).size := by
  unfold Entry.bytes
  simp only [ByteArray.size_append, size_u64n, size_textS]
  omega

theorem size_item (n : String) (v : ByteArray) :
    (item n v).size = 16 + (ascii n).size + v.size := by
  unfold item
  simp only [ByteArray.size_append, size_u64n, size_textS]
  omega

theorem size_versionValue (f : Fld) : (versionValue f).size = 8 := by
  cases f <;> rfl

/-- **The parameter bytes' size, as a sum.** -/
theorem size_paramsBytes (P : Plan) (cfg : ByteArray) (others : List (String × ByteArray)) :
    (paramsBytes P cfg others).size =
      (24 + (ascii versionName).size) + 64 + (P.entries.map fun e => e.bytes.size).sum +
        (16 + (ascii configName).size + cfg.size) +
        (others.map fun x => (item x.1 x.2).size).sum := by
  unfold paramsBytes paramsHead Plan.bytes items
  simp only [ByteArray.size_append, size_u64n, size_item, size_versionValue, size_cat_map]
  omega

/-- At most N entries, each name of at most B bytes. -/
theorem size_entries_le (B : Nat) : ∀ (l : List Entry), (∀ e ∈ l, (ascii e.name).size ≤ B) →
    (l.map fun e => e.bytes.size).sum ≤ l.length * (96 + B)
  | [], _ => Nat.zero_le _
  | e :: l, h => by
    have h1 := h e (List.mem_cons_self ..)
    have h2 := size_entries_le B l fun x hx => h x (List.mem_cons_of_mem _ hx)
    rw [List.map_cons, List.sum_cons, size_entry, List.length_cons, Nat.succ_mul]
    omega

end Fmt

#print axioms Fmt.size_paramsBytes
#print axioms Fmt.size_entries_le
