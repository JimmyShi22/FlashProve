-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/EntryDamageX.lean: damage behind the converter on the roots and on the instance.
NOT HONEST BY DESIGN.

(d1), (d2) a root's bit; (d3), (d4) one word of one answer; (d5) one coordinate of a seed's point;
(d6) a seed's factor; (d15) a third root; (d16) one root alone. Each is a plain function that Lean
compiles; each turns one thing. Nothing is proved. (d7) to (d14), on the string and on the chain as
read, are in OnBytes/TypedOracleCompiler/Slice/EntryDamage.lean.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.EntryConv

set_option autoImplicit false

namespace TypedOracleCompiler.Slice.DamageX

open OnBytes.Slice (GE NZ)

/-- Bit 0 of byte i of a byte string, turned. Beyond the end nothing is turned. -/
def bit (b : ByteArray) (i : Nat) : ByteArray :=
  if i < b.size then b.set! i (b.get! i ^^^ 1) else b

/-- Bit 0 of word 0 of entry i of a list of triples, turned. -/
def word (l : AnsT) (i : Nat) : AnsT :=
  l.modify i fun t => (t.1 ^^^ 1, t.2)

variable {lg s : ℕ}

/-- (d3): one word of answer i of the first table. -/
def ans0 (x : XE AnsT lg s) (i : Nat) : XE AnsT lg s := ((word x.1.1 i, x.1.2), x.2)

/-- (d4): of the copy. -/
def ans1 (x : XE AnsT lg s) (i : Nat) : XE AnsT lg s := ((x.1.1, word x.1.2 i), x.2)

/-- One added to coordinate t of the point of seed i. -/
def coord (σ : Sd1 lg s) (i : Fin s) (t : Fin lg) : Sd1 lg s :=
  fun j => if j = i then (fun u => if u = t then (σ j).1 u + 1 else (σ j).1 u, (σ j).2) else σ j

/-- Another factor than β: β + 1; or 1, should β + 1 be 0 (then β is -1, which is not 1 in this
field). -/
def other (β : NZ) : NZ :=
  if h : β.val + 1 = 0 then ⟨1, one_ne_zero⟩ else ⟨β.val + 1, h⟩

/-- The factor of seed i, turned. -/
def factor (σ : Sd1 lg s) (i : Fin s) : Sd1 lg s :=
  fun j => if j = i then ((σ j).1, other (σ j).2) else σ j

/-- (d5): one coordinate of a seed's point, in the first table's seeds. -/
def seed0 (x : XE AnsT lg s) (i : Fin s) (t : Fin lg) : XE AnsT lg s :=
  (x.1, (coord x.2.1 i t, x.2.2))

/-- (d6): a seed's factor, in the first table's seeds. -/
def fac0 (x : XE AnsT lg s) (i : Fin s) : XE AnsT lg s := (x.1, (factor x.2.1 i, x.2.2))

/-- (d15): a third root. -/
def third {α : Type} (cms : List α) : List α := cms ++ cms.take 1

/-- (d16): one root alone. -/
def alone {α : Type} (cms : List α) : List α := cms.take 1

end TypedOracleCompiler.Slice.DamageX
