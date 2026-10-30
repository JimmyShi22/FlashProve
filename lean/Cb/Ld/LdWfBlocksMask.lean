-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdWfBlocksMask.lean: the zero-knowledge item of the lookups of the preamble of
weights-formedness.

Definitions and statements (in `Cb.Spec`); the proofs are in Cb/Ld/LdWfBlocksMaskProofs.lean. This
file goes on from Cb/Ld/LdWfBlocks.lean; the parameters (letters) of the item (`Honest.MM`,
Ior/Masked.lean) are those of Cb/Ld/LdWfMasksLkp.lean (`K.dm`).
The preamble of weights-formedness (`LdWfP.Blk.wf`, Cb/Ld/LdWf.lean) is the sub-protocol for the
claim that the encoded index decodes to a message that holds an index. By the law
`LdWfP.Laws.describes` the message holds an index if and only if every key of each forest is an
entry of that forest's table. The lookup of forest f, here the value `K.sub f`
(Cb/Ld/LdWfBlocks.lean), is the sub-protocol for that claim on one forest.
`K.OK p` (Cb/Ld/LdWfBlocks.lean) has the conditions on the lookups' numbers, multiplicities, rows
and public supports; p enters in its clause `adm` (`LkB.Adm`, Cb/Ld/LdLkp.lean), in the bound on
table size and bit positions.
Many statements of this library are written twice: a definition in the namespace `Spec` states a
proposition, and a theorem of the same name outside that namespace proves it (lean/GLOSSARY.md).

Main names:
  `K.MOK Rd`: the conditions on places, forest by forest: the own masks of all sumchecks of the
    lookup lie at pairwise different places, outside the data (Cb/Ld/LdLkpMaskAsm2.lean: `MaskOK`);
    the reading Rd f contains data and own masks.
  `Spec.ldWfB_reads`: the exact claim of a forest's lookup reads its data only (keys read the
    matrix; the clause on multiplicities reads keys and bits).
  `Spec.ldWfB_mm`: from `K.OK`, `K.MOK`, under `CharP E p` (p is the characteristic of E), where the
    index has a value (`[Nonempty C.E0.Str]`): each lookup as a whole has the item "masked
    messages", at the letters `K.dm Rd K.cc`. The conclusion is the field `lkpM` of
    Cb/Ld/LdWf.lean's `Blk.Hyp`, word for word.
  `Spec.ldWfB_cl`: from the laws of the data, `K.OK`, `K.MOK`: the exact input relation of the
    lookup gives the item's claim. The conclusion is the field `lkpC`, word for word.

So of what `Blk.Hyp` (Cb/Ld/LdWf.lean) asks of a lookup nothing is left as a hypothesis on a block,
but for `fresh`, `freshB` (see Limits): `lkp`, `lkpI`, `lkpP`, `lkpH`, `lkpN`, `lkpS`
(Cb/Ld/LdWfBlocks.lean), `lkpM`, `lkpC` (here) follow from conditions on data, numbers and places.

The conclusion of `Spec.ldWfB_mm` is `Honest.MM` (Ior/Masked.lean) of `(K.sub l).H`. `H.MM D` asks
five things: the block sends no oracle; `H.withheld w x` is always empty; the honest prover's plain
parts are `D.msg` at `D.kc w`, `D.pub x` and ρ; `D.Cl` is kept under `D.put`; and where `D.Cl xp k`
holds, `D.msg (D.put M k) xp ρ` over uniform M has the distribution `D.sim xp ρ`. `GoodM` is `GoodB`
(`GoodT` without the clause `exact`) with `H.MM D`, and the clause that every (x, y, w) in the
honest relation meets `D.Cl (D.pub x) (D.kc w)`. `GoodM` (Ior/Masked.lean) stands in no statement of
this file.

Limits: this file says nothing on masks sent in advance (`fresh`, `freshB`: Cb/Ld/LdWfMasks*.lean).
It does not say that `K.OK` and `K.MOK` can be met together.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdWfMasksLkp
import Cb.Ld.LdLkpAsm2GoodM

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop IOR Cb.LdLkp

namespace LdWfP.Lks
variable {E : Type} [Field E] [Fintype E] {C : ConfigurationWithOutOfDomainSample} {P : LdWfP E C} (K : P.Lks)

/-- The data of the lookup of forest f: the entries of the index's matrix, and the places of the
forest's bits. -/
def Dt (f : ℕ) : P.bt.J → Prop := fun j => (∃ rc, j = Sum.inl rc) ∨ ∃ u i, j = Sum.inr (K.bAt f u i)

/-- The claim with which the item starts: the lookup's exact claim itself (every key in the table;
the bits write valid multiplicities), on entries. -/
def cc (f : ℕ) : P.WSt → (P.bt.J → E) → Prop := (K.asm f).lk.inP (K.asm f).ValidMu

/-- The conditions on places. -/
structure MOK (Rd : ℕ → P.bt.J → Prop) : Prop where
  mask : ∀ f, f ≤ P.n → (K.asm f).MaskOK (K.Dt f)
  rd   : ∀ f, f ≤ P.n → ∀ j, (K.asm f).srAll (K.Dt f) j → Rd f j

end LdWfP.Lks
end Cb

namespace Cb.Spec
open Iop Prob Hiop IOR Cb.LdLkp

section
variable (E : Type) [Field E] [Fintype E]

/-- The exact claim of a forest's lookup reads its data only (keys read the matrix; the clause on
multiplicities reads keys and bits). -/
def ldWfB_reads : Prop :=
  ∀ (C : ConfigurationWithOutOfDomainSample) (P : LdWfP E C) (K : P.Lks) (f : ℕ), (K.asm f).ClaimReads (K.Dt f) (K.asm f).ValidMu

/-- States the field `lkpM` of `LdWfP.Blk.Hyp` (Cb/Ld/LdWf.lean) for `K.sub l` with
`K.dm Rd K.cc l`, under the hypotheses below. -/
def ldWfB_mm : Prop :=
  ∀ (p : ℕ) [CharP E p] (C : ConfigurationWithOutOfDomainSample) [Nonempty C.E0.Str] (P : LdWfP E C)
      (K : P.Lks) (Rd : ℕ → P.bt.J → Prop),
    K.OK p → K.MOK Rd → ∀ l, l ≤ P.n → (K.sub l).H.MM (K.dm Rd K.cc l)

/-- States the field `lkpC` of `LdWfP.Blk.Hyp` (Cb/Ld/LdWf.lean) for `K.sub l` with
`K.dm Rd K.cc l`, under the hypotheses below. -/
def ldWfB_cl : Prop :=
  ∀ (p : ℕ) (C : ConfigurationWithOutOfDomainSample) (P : LdWfP E C) (K : P.Lks) (Rd : ℕ → P.bt.J → Prop), P.Laws → K.OK p →
    K.MOK Rd →
    ∀ l, l ≤ P.n →
      ∀ x y w, (jt2 P.S C.E0 P.Wp P.onW (P.honAt l) ((P.lk l).inP (P.multAt l)) (P.lk l).inR).rel
          x y w →
        (K.dm Rd K.cc l).Cl ((K.dm Rd K.cc l).pub x) ((K.dm Rd K.cc l).kc w)

end
end Cb.Spec
