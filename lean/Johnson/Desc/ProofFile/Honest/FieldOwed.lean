-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/FieldOwed.lean: what is left to prove of a list for `Owed.good`
(Owed.lean): `Owed.good` asks `goodAt` of the list with the field beside its A and its B
(`Lettered.withField`). By `Good.field` (FieldGood.lean) it is enough to prove `goodAt` of the list
with the field beside its A alone, and its own B.

  `Lettered.fieldBefore`   a list with the field beside its A alone
  `Lettered.goodAt_field`   the statement

Limits.
  * No example: no list is shown to meet the hypothesis.
  * The lemma proves no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Owed

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block Place OpenedColumn)

variable {S Cl V W Y Pb : Type} {Bk : ProverCoinCounts}

/-- A list with what the field holds beside its A alone. -/
def Lettered.fieldBefore (L : Lettered Bk S Cl V W Y Pb) (chain firstTree : Nat)
    (bs : List (Block S Cl)) (base : List OpenedColumn) (skip : Nat) : Lettered Bk S Cl V W Y Pb :=
  { L with A := WithField chain firstTree (roundsBefore bs L.place) base skip L.A }

/-- **Who proves `goodAt` of a list with the field beside its A, to the list's own B, has what
`Owed.good` asks of the list.** -/
theorem Lettered.goodAt_field {L : Lettered Bk S Cl V W Y Pb} {chain firstTree skip : Nat}
    {bs : List (Block S Cl)} {base : List OpenedColumn}
    {earlier : List (Nat × Nat × List Fmt.DeclaredRound)} {φ : Face V W Pb} {ord : List Place}
    {fs : List (Fall S)}
    (h : (L.fieldBefore chain firstTree bs base skip).goodAt earlier φ bs ord chain
      firstTree fs) :
    (L.withField chain firstTree bs base skip).goodAt earlier φ bs ord chain firstTree
      fs := by
  intro σ hσ
  have hσ' : L.side bs fs = some σ := hσ
  have g := Good.field (h σ hσ)
  rw [← roundsUpTo_seated hσ'] at g
  exact g

end ProofFile.Honest

#print axioms ProofFile.Honest.Lettered.goodAt_field
#print axioms ProofFile.Honest.Lettered.fieldBefore
