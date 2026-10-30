-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/AskedSection.lean: every value that a parser of an entry file hands over
(`OnBytes.Tie.AskedE`: plain data) can be written into files and read back by plain functions.

Instances, one definition, and statements with their proofs. The bounds for the entry file
(OnBytes/TypedOracleCompiler/Slice/EntryFullTop.lean, EntrySmallTop.lean) speak of a maker of five files and of a
converter that is fixed before the hash function is drawn. To say them for a maker of a parsed
value, a converter is wanted that reads every such value back off some files. Here it is shown to
exist.

Main names (namespace `TypedOracleCompiler.Slice.AskedSection`):
  thirteen instances of `Countable`: bytes, words, arrays, byte strings, and the nine types of data
    of which `AskedE` is made, each by a map of its fields that is one to one.
  `filesOf n`, `filesOf_inj`: a number as files: the entry file has that many bytes.
  `exists_section`: there are enc : `AskedE → Files` and rd : `Files → Option AskedE` with
    rd (enc a) = some a for every a.

Limits.
  1. For proofs only. enc and rd are shown to exist, by counting and by a choice: they have no code,
     they are no format, and no program writes or reads them. They have nothing to do with the bytes
     of an entry file.
  2. Neither is given a hash function: that is what the bounds' converter asks. Nothing on soundness
     stands here.
  3. The thirteen instances are global: whoever imports this file has them.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Tie.EntryAsked
import OnBytes.TypedOracleCompiler.Slice.Shapes
import Mathlib.Data.Countable.Basic
import Mathlib.Logic.Equiv.List

set_option autoImplicit false

namespace TypedOracleCompiler.Slice.AskedSection
open OnBytes.Tie (AskedE)
open OnBytes.Slice.Shapes (Files)

/-- Bytes: by their numbers. -/
instance : Countable UInt8 :=
  Function.Injective.countable (f := UInt8.toNat) fun _ _ h => UInt8.toNat_inj.1 h

/-- Words: by their numbers. -/
instance : Countable UInt64 :=
  Function.Injective.countable (f := UInt64.toNat) fun _ _ h => UInt64.toNat_inj.1 h

/-- Arrays: by their lists. -/
instance {α : Type} [Countable α] : Countable (Array α) :=
  Function.Injective.countable (f := Array.toList) fun a b h => by
    cases a
    cases b
    exact congrArg Array.mk h

/-- Byte strings: by their arrays. -/
instance : Countable ByteArray :=
  Function.Injective.countable (f := ByteArray.data) fun a b h => by
    cases a
    cases b
    exact congrArg ByteArray.mk h

/-- An element of the extension field as data: by its three words. -/
instance : Countable OnBytes.E :=
  Function.Injective.countable (f := fun x : OnBytes.E => (x.c0, x.c1, x.c2)) fun a b h => by
    cases a
    cases b
    simp_all

/-- A table's name: by its fields. -/
instance : Countable OnBytes.Params.TableName :=
  Function.Injective.countable (f := fun x : OnBytes.Params.TableName => (x.root, x.answers))
    fun a b h => by
      cases a
      cases b
      simp_all

/-- An item of a round's message: by its case and what that holds. -/
instance : Countable _root_.Fmt.ItemValue :=
  Function.Injective.countable
    (f := fun x : _root_.Fmt.ItemValue =>
      (match x with
        | .f y => Sum.inl y
        | .e y => Sum.inr (Sum.inl y)
        | .word y => Sum.inr (Sum.inr (Sum.inl y))
        | .root y => Sum.inr (Sum.inr (Sum.inr (Sum.inl y)))
        | .answer y => Sum.inr (Sum.inr (Sum.inr (Sum.inr y))) :
        UInt64 ⊕ (UInt64 × UInt64 × UInt64) ⊕ UInt64 ⊕ ByteArray ⊕ (UInt64 × UInt64 × UInt64)))
    fun a b h => by
      cases a <;> cases b <;> simp_all

/-- What a round has drawn: by its fields. -/
instance : Countable _root_.Fmt.Drawn :=
  Function.Injective.countable
    (f := fun x : _root_.Fmt.Drawn => (x.elems, x.poss, x.trits, x.digest)) fun a b h => by
      cases a
      cases b
      simp_all

/-- A tree's shape: by its fields. -/
instance : Countable _root_.Fmt.Shape :=
  Function.Injective.countable
    (f := fun x : _root_.Fmt.Shape => (x.a, x.W, x.stored, x.tree)) fun a b h => by
      cases a
      cases b
      simp_all

/-- An opening as read: by its fields. -/
instance : Countable _root_.Fmt.OpenOut :=
  Function.Injective.countable
    (f := fun x : _root_.Fmt.OpenOut => (x.cols, x.salts, x.given, x.root, x.seen, x.next))
    fun a b h => by
      cases a
      cases b
      simp_all

/-- A round as read: by its fields. -/
instance : Countable _root_.Fmt.RoundOut :=
  Function.Injective.countable
    (f := fun x : _root_.Fmt.RoundOut => (x.msg, x.vals, x.nonce, x.drawn, x.list, x.opens))
    fun a b h => by
      cases a
      cases b
      simp_all

/-- A chain as read: by its fields. -/
instance : Countable _root_.Fmt.ChainOut :=
  Function.Injective.countable
    (f := fun x : _root_.Fmt.ChainOut => (x.pd, x.run, x.rho0, x.rho, x.seen, x.rounds))
    fun a b h => by
      cases a
      cases b
      simp_all

/-- A parsed value: by its five fields. -/
instance : Countable AskedE :=
  Function.Injective.countable
    (f := fun x : AskedE => (x.first, x.further, x.l0, x.l1, x.out)) fun a b h => by
      cases a
      cases b
      simp_all

/-- A number as files: the entry file has that many bytes, all 0; the four others are empty. -/
def filesOf (n : ℕ) : Files :=
  ⟨ByteArray.empty, ⟨Array.replicate n 0⟩, ByteArray.empty, ByteArray.empty, ByteArray.empty⟩

/-- Two numbers with the same files are one: by the entry file's length. -/
theorem filesOf_inj : Function.Injective filesOf := fun m n h => by
  have h2 := congrArg (fun d : Files => d.ent.size) h
  simpa [filesOf, ByteArray.size] using h2

/-- Every parsed value can be written into files and read back: there are a writing enc and a
reading rd, plain functions that see no hash function, with rd (enc a) = some a for every a. -/
theorem exists_section :
    ∃ (enc : AskedE → Files) (rd : Files → Option AskedE), ∀ a, rd (enc a) = some a := by
  obtain ⟨f, hf⟩ := exists_injective_nat AskedE
  have hi : Function.Injective fun a => filesOf (f a) := filesOf_inj.comp hf
  classical
  exact ⟨fun a => filesOf (f a), Function.partialInv fun a => filesOf (f a),
    fun a => Function.partialInv_left hi a⟩

end TypedOracleCompiler.Slice.AskedSection
