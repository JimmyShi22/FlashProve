-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Part/LdPartAllot.lean: the rule that allots mask entries to the blocks of a list: a running sum.
Numbers and names only: no field, no signature, no protocol.

In standard terms: book-keeping with natural numbers. Its use: a sub-protocol (block) of a list may
need some entries of oracle messages that were sent earlier. Here block after block takes the next
numbers of an enumeration of entries, and under the hypotheses of `Spec.ldAllot_places` the entries
so taken differ.
Definitions and statements (in `Cb.Spec`); the proofs are in Cb/Part/LdPartAllotProofs.lean.

Why: in the protocol that we follow no masked block sends its own masks: they are entries of oracle
messages that were sent before the block. Records on masks of a request can ask,
block by block, that the places of these entries differ, that they differ from block to block and
from the places of data. Whoever builds a request from a partition has to choose the places, for a
list of blocks whose length depends on the model. Here the choice is one rule, and what the records
ask of places follows once.


Main names:
  `LdAllot`: the input A. Blocks are numbered 0, 1, 2, ..; `A.Nm b`: the names of block b's own
    masks (any type); `A.n b`: how many entries it takes; `A.num b`: the own number of a name.
    `A.OK`: different names have different numbers, all below `A.n b`.
  `LdFreeNum fr cap Dat`: the free entries are given by number: fr : ℕ → N, a total function into
    whatever type N of entries (so that data built from it take no proof as an argument). Below cap
    different numbers are different entries, and none of them is a place of data (Dat: any set of
    entries).
  The rule (`A.off`, `A.pos`, `A.pl`): block b takes the next `A.n b` free entries.
  The capacity of a list of B blocks is one inequality between numbers: A.off B ≤ cap.
  `Spec.ldAllot_places`: `A.OK`, `LdFreeNum fr cap Dat`, A.off B ≤ cap ⇒ on the blocks below B:
    equal places have equal (block, name); no place is a place of data.
  `Spec.ldAllot_std`: the standard input for finite types of names (`A.n b` := the number of names;
    `A.num b` := a numbering, by choice) has `OK`.
  `Spec.ldAllot_need`: the capacity is needed: at the standard input, whatever family of places of
    the blocks below B is injective into a set of cap entries, A.off B ≤ cap.
  `Spec.ldFree_grid`: free entries in rows of equal width w: the entry number k is (row k / w,
    column k % w); if the entries of R rows differ and none is a place of data, R rows give the
    capacity R w.
  `Spec.ldFree_fin`: free entries of a finite type X, numbered by choice: if they differ and none
    is a place of data, the capacity is the number of elements of X.

Limits: one value of this record is one counter.




This file does not say what the blocks are and how many entries each takes.
It does not say that masks at these places are uniform and unused
when their block begins (Cb/Part/LdPartAllotRule.lean, Limits). It does not say that the capacity
holds at some model. The order of the blocks is the caller's.
A write-up of ours (lean/CREDITS.md), which we follow fixes no places and no order (by
inspection of it): where each mask entry of each block lies is there one of the public parameters, a
table; so the rule renders no sentence of it, it is one value of that table, and any other injective
choice of places that are no places of data serves as well. What the write-up asks of the
table is more than room: the entries of a segment's blocks differ, lie in mask rows and outside the
pads (a message with mask rows has its pad there, so the pad takes room); one kind of entry lies in
a message of the first sending, where the entries of different segments differ. Here: "outside the
pads" is the caller's: fr is to number free entries of a layout, which are neither data nor pads (or
Dat is to hold the pads' places).

Terms: lean/GLOSSARY.md.
"The write-up": one of our own texts on this protocol (lean/CREDITS.md); it is not in this
repository.
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.EquivFin
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb

/-- The input of the rule; the head tells its fields. -/
structure LdAllot : Type 1 where
  Nm  : ℕ → Type
  n   : ℕ → ℕ
  num : ∀ b, Nm b → ℕ

namespace LdAllot
variable (A : LdAllot)

/-- What is asked of the input. -/
structure OK : Prop where
  inj : ∀ b, Function.Injective (A.num b)
  lt  : ∀ b x, A.num b x < A.n b

/-- The rule: a running sum. -/
def off (b : ℕ) : ℕ := ∑ k ∈ Finset.range b, A.n k
def pos (b : ℕ) (x : A.Nm b) : ℕ := A.off b + A.num b x
def pl {N : Type} (fr : ℕ → N) (b : ℕ) (x : A.Nm b) : N := fr (A.pos b x)

/-- The standard input for finite types of names. -/
def std (Nm : ℕ → Type) [∀ b, Fintype (Nm b)] : LdAllot :=
  ⟨Nm, fun b => Fintype.card (Nm b), fun b x => (Fintype.equivFin (Nm b) x : ℕ)⟩

end LdAllot

/-- Free entries by number. -/
structure LdFreeNum {N : Type} (fr : ℕ → N) (cap : ℕ) (Dat : N → Prop) : Prop where
  inj : ∀ k < cap, ∀ k' < cap, fr k = fr k' → k = k'
  dat : ∀ k < cap, ¬ Dat (fr k)

/-- the elements of a finite type by number; beyond their number: x₀ -/
def ldFrFin {X : Type} [Fintype X] (x₀ : X) (k : ℕ) : X :=
  if h : k < Fintype.card X then (Fintype.equivFin X).symm ⟨k, h⟩ else x₀

namespace Spec

def ldAllot_lt : Prop := ∀ A : LdAllot, A.OK → ∀ B b, b < B → ∀ x, A.pos b x < A.off B

def ldAllot_inj : Prop :=
  ∀ A : LdAllot, A.OK → Function.Injective fun p : Σ b, A.Nm b => A.pos p.1 p.2

/-- The places. -/
def ldAllot_places : Prop :=
  ∀ (A : LdAllot) (N : Type) (fr : ℕ → N) (cap : ℕ) (Dat : N → Prop) (B : ℕ), A.OK →
    LdFreeNum fr cap Dat → A.off B ≤ cap →
    (∀ b < B, ∀ b' < B, ∀ x x', A.pl fr b x = A.pl fr b' x' → (⟨b, x⟩ : Σ b, A.Nm b) = ⟨b', x'⟩) ∧
    ∀ b < B, ∀ x, ¬ Dat (A.pl fr b x)

def ldAllot_in : Prop :=
  ∀ (A : LdAllot) (N : Type) (fr : ℕ → N) (cap : ℕ) (Dat : N → Prop) (B : ℕ),
    A.OK → LdFreeNum fr cap Dat → A.off B ≤ cap → ∀ b < B, Function.Injective (A.pl fr b)

def ldAllot_apart : Prop :=
  ∀ (A : LdAllot) (N : Type) (fr : ℕ → N) (cap : ℕ) (Dat : N → Prop) (B : ℕ), A.OK →
    LdFreeNum fr cap Dat → A.off B ≤ cap →
    ∀ b < B, ∀ b' < B, b ≠ b' → ∀ x x', A.pl fr b x ≠ A.pl fr b' x'

def ldAllot_bound : Prop := ∀ (A : LdAllot) (B c : ℕ), (∀ b < B, A.n b ≤ c) → A.off B ≤ B * c

def ldAllot_std : Prop := ∀ (Nm : ℕ → Type) [∀ b, Fintype (Nm b)], (LdAllot.std Nm).OK

/-- States that the capacity is needed, at the standard input. -/
def ldAllot_need : Prop :=
  ∀ (Nm : ℕ → Type) [∀ b, Fintype (Nm b)] (B cap : ℕ) (f : (Σ b : Fin B, Nm b) → Fin cap),
    Function.Injective f → (LdAllot.std Nm).off B ≤ cap

/-- Rows of equal width. -/
def ldFree_grid : Prop :=
  ∀ (N : Type) (at' : ℕ → ℕ → N) (R w : ℕ) (Dat : N → Prop),
    (∀ r < R, ∀ c < w, ∀ r' < R, ∀ c' < w, at' r c = at' r' c' → r = r' ∧ c = c') →
    (∀ r < R, ∀ c < w, ¬ Dat (at' r c)) → LdFreeNum (fun k => at' (k / w) (k % w)) (R * w) Dat

/-- A finite type of free entries. -/
def ldFree_fin : Prop :=
  ∀ (X N : Type) [Fintype X] (x₀ : X) (at' : X → N) (Dat : N → Prop), Function.Injective at' →
    (∀ x, ¬ Dat (at' x)) → LdFreeNum (fun k => at' (ldFrFin x₀ k)) (Fintype.card X) Dat

end Spec
end Cb
