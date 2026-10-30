-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HB/LLHARD/KB9/Spells.lean: A FRAME FOR "READING UNDOES SPELLING" OVER THE READERS OF
PARAMETER ITEMS. One definition and nine rules. General: no value is named.

The readers of a chain's parameter items (OnBytes/Params/Items.lean) are written in the monad `Cut`:
from a string of bytes and a place they give a value and the place behind it, or refuse. The
library's law on readers, `Fmt.Undoes r sp ok` (Fmt/Rules1Laws.lean), speaks of one reader and one
speller. Here the same sentence stands at one value, so that it can be carried along a `do` block,
step by step.

  `Spells c s y`: wherever the string s stands in the midst of bytes, the reader c, set at its first
    byte, returns y and the place behind s.
  `spells_pure`: the reader that reads nothing, at the empty string. `spells_bind`: one reader after
    another, at the two strings in a row. `spells_demand`: a demand that is met reads nothing.
    `Spells.cast`: at an equal string.
  `spells_word` (a number below 2 ^ 64), `spells_flag`, `spells_elt` (an element below the modulus):
    the three primitives, from `undoes_word`, `undoes_bool`, `undoes_elt`.
  `spells_list`: a list with the word of its length in front: fewer than 2 ^ 64 members, each read
    back, each spelt with at least one byte: from `undoes_list` and `rdListT_eq`
    (OnBytes/Chain/Loops.lean).
  `whole_of_spells`: so the reader on the whole string s returns y.

Limits. Nothing on what a reader does at a string that is no spelling. Nothing on soundness.

-/
import Fmt.Rules1Laws
import OnBytes.Params.Spell

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.KB9
open OnBytes OnBytes.Params

/-- **Wherever s stands in the midst of bytes, c reads y off it and ends behind it.** -/
def Spells {α : Type} (c : Cut α) (s : ByteArray) (y : α) : Prop :=
  ∀ pre post : ByteArray, c (pre ++ s ++ post) pre.size = some (y, pre.size + s.size)

theorem Spells.cast {α : Type} {c : Cut α} {s s' : ByteArray} {y : α} (h : Spells c s y)
    (e : s' = s) : Spells c s' y := e ▸ h

theorem spells_pure {α : Type} (y : α) : Spells (pure y : Cut α) ByteArray.empty y := by
  intro pre post
  rw [ByteArray.size_empty, Nat.add_zero]
  rfl

/-- **One reader after another.** -/
theorem spells_bind {α β : Type} {c : Cut α} {f : α → Cut β} {s t : ByteArray} {x : α} {y : β}
    (h1 : Spells c s x) (h2 : Spells (f x) t y) : Spells (c >>= f) (s ++ t) y := by
  intro pre post
  have e1 : pre ++ (s ++ t) ++ post = pre ++ s ++ (t ++ post) := by
    simp only [ByteArray.append_assoc]
  have e2 : pre ++ (s ++ t) ++ post = (pre ++ s) ++ t ++ post := by
    simp only [ByteArray.append_assoc]
  have a := h1 pre (t ++ post)
  rw [← e1] at a
  have b := h2 (pre ++ s) post
  rw [ByteArray.size_append, ← e2] at b
  show (c (pre ++ (s ++ t) ++ post) pre.size >>= fun r => f r.1 (pre ++ (s ++ t) ++ post) r.2) = _
  rw [a]
  show f x (pre ++ (s ++ t) ++ post) (pre.size + s.size) = _
  rw [b, ByteArray.size_append, Nat.add_assoc]

theorem spells_demand {t : Bool} (h : t = true) : Spells (Cut.demand t) ByteArray.empty () := by
  intro pre post
  unfold Cut.demand
  rw [if_pos h, ByteArray.size_empty, Nat.add_zero]

theorem spells_word {n : Nat} (h : n < 2 ^ 64) : Spells word (spellWord n) n := by
  intro pre post
  have hn : (UInt64.ofNat n).toNat = n := by
    rw [UInt64.toNat_ofNat']
    exact Nat.mod_eq_of_lt h
  show (Fmt.rdWord (pre ++ Fmt.u64 (UInt64.ofNat n) ++ post) pre.size).map
    (fun x => (x.1.toNat, x.2)) = some (n, pre.size + (Fmt.u64 (UInt64.ofNat n)).size)
  rw [Fmt.undoes_word (UInt64.ofNat n) trivial pre post, Option.map_some, hn]

theorem spells_flag (v : Bool) : Spells flag (Fmt.bool v) v :=
  fun pre post => Fmt.undoes_bool v trivial pre post

theorem spells_elt {x : F} (h : x.toNat < Fmt.Fld.two.p) : Spells elt (Fmt.elt x) x :=
  fun pre post => Fmt.undoes_elt .two x h pre post

/-- **A list with the word of its length in front.** -/
theorem spells_list {α : Type} {c : Cut α} {sp : α → ByteArray} {ok : α → Prop}
    (h : ∀ x, ok x → Spells c (sp x) x) (hp : ∀ x, ok x → 1 ≤ (sp x).size) {l : List α}
    (hl : l.length < 2 ^ 64) (ha : ∀ x ∈ l, ok x) : Spells (listOf c) (Fmt.list sp l) l := by
  intro pre post
  have U : Fmt.Undoes c.rd sp ok := fun x hx pre post => h x hx pre post
  show rdListT c.rd (pre ++ Fmt.list sp l ++ post) pre.size = _
  rw [rdListT_eq]
  exact Fmt.undoes_list U hp l ⟨hl, ha⟩ pre post

/-- **So the reader on the whole string returns the value.** -/
theorem whole_of_spells {α : Type} {c : Cut α} {s : ByteArray} {y : α} (h : Spells c s y) :
    c.whole s = some y := by
  have h1 := h ByteArray.empty ByteArray.empty
  rw [ByteArray.empty_append, ByteArray.append_empty, ByteArray.size_empty, Nat.zero_add] at h1
  have h2 : c.rd s 0 = some (y, s.size) := h1
  unfold Cut.whole Fmt.whole
  rw [h2]
  simp

end Johnson.KB9

#print axioms Johnson.KB9.Spells.cast
#print axioms Johnson.KB9.spells_pure
#print axioms Johnson.KB9.spells_bind
#print axioms Johnson.KB9.spells_demand
#print axioms Johnson.KB9.spells_word
#print axioms Johnson.KB9.spells_flag
#print axioms Johnson.KB9.spells_elt
#print axioms Johnson.KB9.spells_list
#print axioms Johnson.KB9.whole_of_spells
