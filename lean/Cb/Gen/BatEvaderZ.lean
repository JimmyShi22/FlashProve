-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Gen/BatEvaderZ.lean: the random linear combination with independent coefficients, as a
zero-evader whose count is 0 on the empty set of rows. One definition, statements and proofs.
Generic: any finite field. Nothing assumed beyond the hypotheses of the statements and whatever the
arguments hold as proofs.

Why: `Evader.indep E J` (Cb/Gen/BatEvader.lean) has the count (its field `err`) |E|^(|J| − 1), with
the natural numbers' truncated subtraction: on no row it is 1, of 1 seed. That is a true bound and a
useless one: over the empty set there is no vector other than 0, so 0 seeds annihilate one. An
inequality "count · X ≤ seeds" is then false at the one degenerate point for every X > 1
(`Spec.indep_empty`), though the batching of no row has no error.

Main names:
  `Evader.indepZ E J`: seeds J → E, coefficients the seed itself, as `Evader.indep`; count: 0 if J
    is empty, |E|^(|J| − 1) otherwise.
  `Spec.ok_indepZ`: it is a zero-evader.
  `Spec.indepZ_same`: on a set that is not empty the count is that of `Evader.indep`; seeds and
    coefficients are the same by definition.
  `Spec.indepZ_le`: for every J: X ≤ |E| ⇒ count · X ≤ seeds.
  `Spec.indep_empty`: J empty, 1 < X ⇒ ¬ (the count of `Evader.indep E J`) · X ≤ its seeds.

(By a reading: the protocol that we follow states its batching for any number of rows
and any zero-evader with its error as a letter; its evaluation takes the equality kernel, whose
count is 0 on no coordinate.)

Notation: `Evader E J` (Cb/Gen/BatEvader.lean): a zero-evader, the data; `D` : Type: the seeds; `ze`
: D → J → E: the coefficients that a seed gives; `err` : ℕ: the number of seeds that may annihilate
a vector other than 0; `Evader.OK` : Evader E J → Prop (Cb/Gen/BatEvader.lean): the property of a
zero-evader, a vector other than 0 is annihilated by at most err seeds.

Limits: this file says nothing on cost: one field element a row.
Terms: lean/GLOSSARY.md.
-/
import Cb.Gen.BatEvaderProofs

set_option autoImplicit false

namespace Cb
open Blocks Iop Prob Alg

/-- Independent coefficients; on no row the count is 0. -/
@[reducible] def Evader.indepZ (E J : Type) [Field E] [Fintype E] [Fintype J] [DecidableEq J] :
    Evader E J :=
  { D := J → E, ze := fun ρ => ρ,
    err := if Fintype.card J = 0 then 0 else Fintype.card E ^ (Fintype.card J - 1) }

namespace Spec

def ok_indepZ : Prop :=
  ∀ (E J : Type) [Field E] [Fintype E] [Fintype J] [DecidableEq J], (Evader.indepZ E J).OK

def indepZ_same : Prop :=
  ∀ (E J : Type) [Field E] [Fintype E] [Fintype J] [DecidableEq J],
    Nonempty J → (Evader.indepZ E J).err = (Evader.indep E J).err

def indepZ_le : Prop :=
  ∀ (E J : Type) [Field E] [Fintype E] [Fintype J] [DecidableEq J] (X : ℕ),
    X ≤ Fintype.card E → (Evader.indepZ E J).err * X ≤ Fintype.card (Evader.indepZ E J).D

def indep_empty : Prop :=
  ∀ (E J : Type) [Field E] [Fintype E] [Fintype J] [DecidableEq J] (X : ℕ),
    IsEmpty J → 1 < X → ¬ (Evader.indep E J).err * X ≤ Fintype.card (Evader.indep E J).D

end Spec

theorem indepZ_same : Spec.indepZ_same := by
  intro E J _ _ _ _ hne
  show (if Fintype.card J = 0 then 0 else Fintype.card E ^ (Fintype.card J - 1)) = _
  rw [if_neg (Nat.ne_of_gt (Fintype.card_pos_iff.2 hne))]

theorem ok_indepZ : Spec.ok_indepZ := by
  intro E J _ _ _ _ v hv
  by_cases h0 : Fintype.card J = 0
  · haveI : IsEmpty J := Fintype.card_eq_zero_iff.1 h0
    exact absurd (funext fun j => (IsEmpty.false j).elim) hv
  · have hne : Nonempty J := Fintype.card_pos_iff.1 (Nat.pos_of_ne_zero h0)
    rw [indepZ_same E J hne]
    exact ok_indep E J v hv

theorem indepZ_le : Spec.indepZ_le := by
  intro E J _ _ _ _ X hX
  show (if Fintype.card J = 0 then 0 else Fintype.card E ^ (Fintype.card J - 1)) * X ≤
    Fintype.card (J → E)
  by_cases h0 : Fintype.card J = 0
  · rw [if_pos h0, Nat.zero_mul]
    exact Nat.zero_le _
  · rw [if_neg h0]
    calc
      Fintype.card E ^ (Fintype.card J - 1) * X ≤
          Fintype.card E ^ (Fintype.card J - 1) * Fintype.card E :=
        Nat.mul_le_mul_left _ hX
      _ = Fintype.card (J → E) := by
        rw [Fintype.card_fun, ← pow_succ, Nat.sub_add_cancel (Nat.pos_of_ne_zero h0)]

theorem indep_empty : Spec.indep_empty := by
  intro E J _ _ _ _ X he hX
  show ¬ Fintype.card E ^ (Fintype.card J - 1) * X ≤ Fintype.card (J → E)
  rw [Fintype.card_fun, Fintype.card_eq_zero_iff.2 he, Nat.zero_sub, pow_zero, Nat.one_mul]
  exact Nat.not_le.2 hX

end Cb
