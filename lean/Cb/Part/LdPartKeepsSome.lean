-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Part/LdPartKeepsSome.lean: a condition on a partition that the builder of a request needs by type
and that no law of a partition gives: behind every segment but the last some row is kept
(`P.KeepsSome`); under it and the hypotheses of `P.idle₀` below, the idle row of the kept messages'
naming is a term; without it that row's type is empty.

Book-keeping: a condition under which, with the other hypotheses of `P.idle₀` below, a type of rows
is inhabited, so that a default value can be named.
Definitions and statements (`Cb.Spec.ldPartKeepsSome_rp`, `Cb.Spec.ldPartKeepsSome_lt`,
`Cb.Spec.ldPartKeepsSome_need`); the proofs are in Cb/Part/LdPartKeepsSomeProofs.lean. Nothing
assumed beyond the hypotheses of the statements and whatever the arguments hold as proofs.

Why: the naming of the kept messages behind segment k (`P.nmS K (P.onKept k) ..`,
Cb/Part/LdPartNmOf.lean) takes a parameter (letter) d₀: the default of the naming's map of rows
(`rowAt`). Its type is the type of rows of the matrices that are kept behind k. Where nothing is
kept behind k that type has no member (`Spec.ldPartKeepsSome_need`), and all records that hold such
a letter are empty types there: their theorems are true for want
of a case, and the builder admits no run. `P.Props` does not forbid such a partition: a later
segment may read index and instance alone.



Main names:
  `P.idleRow K k hs hn hK`: for hs: s is kept behind k; hn: s < P.n; hK: 0 < K.P: the row (packed
    row 0 of s's matrix, lane 0).
  `P.idle₀ K p k hP hS hk hK`: the idle row as a term from `P.Props p`, `P.KeepsSome`, k + 1 < P.n,
    0 < K.P, at a kept segment by choice: it needs the second statement below, so it is defined in
    the proofs' file. Two callers who choose different rows get two namings, hence two readings that
    need not be equal as data: take `P.idle₀` everywhere.
  `Spec.ldPartKeepsSome_rp`: 0 < K.P ⇒ every segment has a packed row: 0 < P.rp K j (needed by a
    definition: it stands here with its proof, as `P.rp_pos`).
  `Spec.ldPartKeepsSome_lt`: `P.Props p`, k + 1 < P.n: what is kept behind k belongs to a segment of
    the partition.
  `Spec.ldPartKeepsSome_need`: nothing is kept behind k ⇒ the type of the idle row is empty.

Limits:
This file's statements are about data structures of this library.
The condition is a hypothesis (hS of `P.idle₀`), and a declared difference: this protocol's
technical report (lean/CREDITS.md) that we follow has no such condition (by reading, not
machine-checked: the number of kept slots may be 0, and nothing asks a later segment to read an
earlier one's cells).
This file does not say that a partition with the laws and without the condition exists: an argument
by reading, no theorem and no value. It does not say that the choice of the row does not matter for
what the ties say (by reading: at a segment of the partition and 0 < K.P the `else` branch (the
default) of the naming's map of rows is met only outside the shapes, and the ties speak of rows
inside): no theorem.
The better cure (a naming whose map of rows needs no default)
is a change to the
records on namings and to all that stands on them.

Terms: lean/GLOSSARY.md.
-/
import Cb.Part.LdPartNmOf

set_option autoImplicit false

namespace Cb
open Blocks Finset Cb.Rng Cb.RngPk

namespace LdPartD
variable {F E : Type} [Field F] [Fintype F] [Field E] [Algebra F E] {Cf : LdCf F E}
  (P : LdPartD Cf) (K : LdPartPk)

/-- Behind every segment but the last some row is kept. -/
def KeepsSome : Prop := ∀ k, k + 1 < P.n → ∃ s, P.onKept k s = true

omit [Fintype F] in
theorem rp_pos (hK : 0 < K.P) (j : ℕ) : 0 < P.rp K j := by
  unfold rp
  have h1 : 0 < 2 ^ (P.seg j).rowsLog := Nat.two_pow_pos _
  exact Nat.div_pos (by omega) hK

/-- the row (packed row 0 of a kept matrix, lane 0) -/
def idleRow (k : ℕ) {s : ℕ} (hs : P.onKept k s = true) (hn : s < P.n) (hK : 0 < K.P) :
    (Σ s : Fin P.n, Fin (P.rpS K (P.onKept k) s)) × Fin K.P :=
  (⟨⟨s, hn⟩, ⟨0, lt_of_lt_of_eq (P.rp_pos K hK s) (if_pos hs).symm⟩⟩, ⟨0, hK⟩)

end LdPartD

namespace Spec

def ldPartKeepsSome_rp : Prop :=
  ∀ (F E : Type) [Field F] [Field E] [Algebra F E] (Cf : LdCf F E) (P : LdPartD Cf) (K : LdPartPk),
    0 < K.P → ∀ j, 0 < P.rp K j

/-- States, under the hypotheses below: what is kept behind a segment belongs to a segment of the
partition. -/
def ldPartKeepsSome_lt : Prop :=
  ∀ (F E : Type) [Field F] [Fintype F] [Field E] [Algebra F E] (Cf : LdCf F E)
      (P : LdPartD Cf) (p k s : ℕ),
    P.Props p → k + 1 < P.n → P.onKept k s = true → s < P.n

/-- Where nothing is kept behind k the type of the idle row is empty. -/
def ldPartKeepsSome_need : Prop :=
  ∀ (F E : Type) [Field F] [Fintype F] [Field E] [Algebra F E] (Cf : LdCf F E)
      (P : LdPartD Cf) (K : LdPartPk) (k : ℕ),
    (∀ s, P.onKept k s = false) → IsEmpty ((Σ s : Fin P.n, Fin (P.rpS K (P.onKept k) s)) × Fin K.P)

end Spec
end Cb
