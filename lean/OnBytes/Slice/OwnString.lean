-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/OwnString.lean: a leaf's own string, at the library's generic shape for any list of
rounds' data.

The library's code of one tree's leaves (`Run.PQ.leaf1`) writes, for a place and a column, what
stands between start and salt in the format's string of a leaf: the label with the index, the
column, the fill. `ownStr` is that string for a symbol with its position: its OWN tree's code,
whatever other trees the list has. `rdLeaf` reads a string at a position by the code of that
position's own tree.

Main definitions: `ownStr`, `rdLeaf`; `lower`, `raise` (between the shape with the library's round
in front and the shape behind it).
Main theorems: `rdLeaf_own` (an own string is read back at its own position), `ownStr_some` (every
leaf has one if no tree is deeper than 63), `ownStr_fit` (it is the bits of the format's label, with
its own tree's numbers, and of column and fill), `ownStr_tag` (it begins with the 16 bits of the
leaves' number, under the library's test `tagsOK`).

Not claimed. No condition is put on the trees' numbers, and nothing is said of when two leaves have
one own string. Nothing on the start, the salt, a tag, or a leaf query; nothing on stored leaves, or
on any file or program. The label's two numbers and the bytes are the library's `leafSL`; that they
lie in the domain of the format's hash is not shown.

Terms: lean/GLOSSARY.md.

-/
import Run.PageQFit
import Run.OneIsTypedLeaf

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Rom Compile Compile.Batch Run Run.PQ

/- salt: the length of a file's salt, in bytes -/
variable (C : CK) (salt : ℕ)

/-- A leaf's own string: what the code of its own tree writes for place and column. -/
def ownStr : (ds : List RD) → SymAny (uL C ds) → Option (List Bool)
  | [], y => y.1.elim
  | d :: _, ⟨.inl x, col⟩ => (leaf1 d.tree salt).put (x, col)
  | _ :: ds, ⟨.inr q, col⟩ => ownStr ds ⟨q, col⟩

/-- A string read at a position by the code of that position's own tree: the column, if the place is
the position's. -/
def rdLeaf : (ds : List RD) → (p : OPos (uL C ds)) → List Bool → Option (OSym (uL C ds) p)
  | [], p, _ => p.elim
  | d :: _, .inl x, s =>
    ((leaf1 d.tree salt).parse s).bind fun z => if z.1 = x then some z.2 else none
  | _ :: ds, .inr q, s => rdLeaf ds q s

/-- A leaf's own string, read at its own position, gives its column. -/
theorem rdLeaf_own : ∀ (ds : List RD) (p : OPos (uL C ds)) (a : OSym (uL C ds) p)
    (s : List Bool), ownStr C salt ds ⟨p, a⟩ = some s → rdLeaf C salt ds p s = some a
  | [], p, _, _, _ => p.elim
  | d :: _, .inl x, a, s, h => by
      have h1 : (leaf1 d.tree salt).parse s = some (x, a) := (leaf1 d.tree salt).parse_put _ s h
      show ((leaf1 d.tree salt).parse s).bind (fun z => if z.1 = x then some z.2 else none) = some a
      rw [h1]
      exact if_pos rfl
  | _ :: ds, .inr q, a, s, h => rdLeaf_own ds q a s h

/-- Every leaf has an own string if no tree is deeper than 63. -/
theorem ownStr_some : ∀ (ds : List RD), (∀ d ∈ ds, posN d.tree + posN d.tree ≤ 2 ^ 64) →
    ∀ y : SymAny (uL C ds), (ownStr C salt ds y).isSome = true
  | [], _, y => y.1.elim
  | d :: _, h, ⟨.inl x, col⟩ => leaf1_some d.tree salt (h d (List.mem_cons_self ..)) (x, col)
  | _ :: ds, h, ⟨.inr q, col⟩ =>
    ownStr_some ds (fun d hd => h d (List.mem_cons_of_mem _ hd)) ⟨q, col⟩

/-- A leaf's own string is the bits of the format's label, with its own tree's numbers, and of its
column and fill. -/
theorem ownStr_fit : ∀ (ds : List RD) (y : SymAny (uL C ds)) (m : List Bool),
    ownStr C salt ds y = some m →
      m = bytesToBits (_root_.Fmt.label 164 (leafSL C salt ds y).1 (leafSL C salt ds y).2.1) ++
          bytesToBits (leafSL C salt ds y).2.2
  | [], y, _, _ => y.1.elim
  | d :: _, ⟨.inl x, col⟩, m, h => leaf1_fit d.tree salt x col m h
  | _ :: ds, ⟨.inr q, col⟩, m, h => ownStr_fit ds ⟨q, col⟩ m h

/-- A leaf's own string begins with the 16 bits of the leaves' number, if every tree's word does
(the library's test `tagsOK`). -/
theorem ownStr_tag : ∀ (ds : List RD), tagsOK salt ds = true →
    ∀ (y : SymAny (uL C ds)) (m : List Bool), ownStr C salt ds y = some m →
      16 ≤ m.length ∧ m.take 16 = t164
  | [], _, y, _, _ => y.1.elim
  | d :: _, hk, ⟨.inl x, col⟩, m, h => by
      have hk' : (decide ((leafWord d.tree salt).take 16 = t164) && tagsOK salt _) = true := hk
      rw [Bool.and_eq_true, decide_eq_true_iff] at hk'
      obtain ⟨r, rfl⟩ := leaf1_pre d.tree salt (x, col) m h
      have hl : (leafWord d.tree salt).length = 64 := length_u64n _
      exact ⟨by rw [List.length_append, hl]; omega, (take16 _ r (by rw [hl]; omega)).trans hk'.1⟩
  | d :: ds, hk, ⟨.inr q, col⟩, m, h => by
      have hk' : (decide ((leafWord d.tree salt).take 16 = t164) && tagsOK salt ds) = true := hk
      rw [Bool.and_eq_true] at hk'
      exact ownStr_tag ds hk'.2 ⟨q, col⟩ m h

/-! ## The round in front -/

/-- A symbol with position of the shape with the round in front, as one of the shape behind it. -/
def lower (ds : List RD) : SymAny (Twin.up (SOf C ds)) → SymAny (uL C ds)
  | ⟨.inl p, _⟩ => p.elim
  | ⟨.inr q, a⟩ => ⟨q, a⟩

/-- And back. -/
def raise (ds : List RD) (y : SymAny (uL C ds)) : SymAny (Twin.up (SOf C ds)) := ⟨.inr y.1, y.2⟩

end OnBytes.Slice
