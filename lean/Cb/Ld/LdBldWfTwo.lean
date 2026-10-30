-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdBldWfTwo.lean: the builder of Cb/Ld/LdBldWf.lean at one choice of its parameters: two oracle
messages, with a fixed rule for which of them holds which digit and which mask.

In this library's terms: the builder of weights-formedness (Cb/Ld/LdBldWf.lean) at the placement of
a write-up of ours (lean/CREDITS.md): two oracle messages of a family built by
Cb/Ld/LdBldMsg.lean: the digits of the multiplicities and all masks of the lookups but the inner
masks of the keys' last levels in the first; these inner masks and the batching's hiding
coefficients in the second.

Definitions and statements; the proofs are in Cb/Ld/LdBldWfTwoProofs.lean. Generic: any finite field
F and any finite field E that is an algebra over it, any number of forests, any two members of any
family. Nothing assumed beyond the hypotheses of the statements and whatever the arguments hold as
proofs.

Main names:
  `x.Last E s`: the name s of a lookup's own mask is an inner mask of the last level of its keys'
    tree.
  `x.Msk1 E`, `x.Msk2 E`: the lookups' masks that are not such; those that are, beside the
    batching's hiding coefficients.
  `BldWfLin Cf Rw klo`: what the offline linear test needs beside, as one parameter (but for l and
    py it is overwritten by whoever builds the object).
  `BldWf2 F E`: the parameters.
  `T.X : BldWf F E E`: S, Sd, Y are the family's signature, its one joint seed, its layout (pads in
    E); gR f b is "a digit, or a lookup's mask that is no inner mask of a last level" (`inFirst`):
    what stands in a₁.
  `Spec.bldWf2_room`: a₁ ≠ a₂; pos, adm (numbers), zOK (the batching's zero-evader), describes (the
    model's clause) ⇒ `T.X.Room p`: injB, injM, supR, fair hold by construction.
  `Spec.bldWf2_where`: which message holds what, for whoever builds the offline plan: every name in
    the support of a row stands in a₁; every name in the support of a claim's mask form (forest f ≤
    n only: beyond n the place maps fall back to the fixed data name, which stands in a₁: without
    the bound the clause would be false; every record that reads gC quantifies over f ≤ n), and
    every hiding coefficient of the batching, stands in a₂.

Limits: this file does not say which free entry holds which mask: the embeddings are parameters, no
value is fixed (the write-up fixes the message, not the place). It does not say that
embeddings exist: a matter of counting (Cb/Ld/LdBldWfCount.lean gives the three numbers).

It says nothing on codes.
This file does not ask what the write-up's placement asks beside, and is the family's matter
(by reading): data entries are main rows, free entries mask rows; each pad in a mask row; a₂ has
mask rows only. One prover message, one joint seed: so by construction.

Terms: lean/GLOSSARY.md.
"The write-up": one of our own texts on this protocol (lean/CREDITS.md); it is not in this
repository.
-/
import Cb.Ld.LdBldWfSpec
import Cb.Ld.LdBldMsg
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR Cb.LdLkp Cb.Lkp

namespace BldWfN
variable (x : BldWfN) (E : Type) [Field E] [Fintype E]

/-- an inner mask of the last level of the keys' tree -/
def Last (s : Σ f : x.Fo, x.LkM E f.1) : Prop := ∃ h c, s.2 = .k (x.v' s.1.1) h (Sum.inr c)

abbrev Msk1 : Type := {s : Σ f : x.Fo, x.LkM E f.1 // ¬ x.Last E s}
abbrev Msk2 : Type :=
  {s : Σ f : x.Fo, x.LkM E f.1 // x.Last E s} ⊕ PIdx (List.replicate x.k (pfCube E 2))

end BldWfN

/-- what the offline linear test needs beside -/
structure BldWfLin {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]
    (Cf : LdCf F E) (Rw : Type) (klo : ℕ) : Type 1 where
  l   : ℕ
  py  : Rw → Fin l → Bool
  e'  : ℕ
  tt  : ℕ
  NW  : Sig E
  SdW : NW.Seeds
  iW  : NW.O
  lW  : ((Fin Cf.X.v ⊕ Fin klo) → Bool) → (NW.om iW).C.J
  NU  : Sig E
  SdU : NU.Seeds
  iU  : NU.O
  lU  : Fin Cf.C₀.k → (NU.om iU).C.J
  NO  : Sig E
  SdO : NO.Seeds
  iO  : NO.O
  lO  : Rw → (NO.om iO).C.J

/-- The parameters: those of `BldWf` on the configuration, the index matrix, the forests; Fm :
`BldF E`, a₁, a₂: the family and the two members; L, t; three embeddings: eB: the digits into the
data entries of a₁; e1: `x.Msk1` into the free entries of a₁; e2: `x.Msk2` into the free entries of
a₂; p0, r0: fixed values; Lt. -/
structure BldWf2 (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E]
    [DecidableEq E] [Algebra F E] : Type 1 where
  Cf  : LdCf F E
  Rw  : Type
  [finRw : Fintype Rw]
  klo : ℕ
  lay : Rw × (Fin klo → Bool) → Cf.J₀
  n   : ℕ
  rv  : ℕ → ℕ
  d   : ℕ → ℕ
  w   : ℕ → ℕ
  nd  : ℕ → ℕ
  o   : ℕ → ℕ → E
  co  : ℕ → ℕ → Rw → E
  tab : ℕ → ℕ → E
  Z   : Evader E (Fin (n + 1))
  /-- the family and the two members -/
  Fm  : BldF E
  a₁  : Fm.O
  a₂  : Fm.O
  L   : Fm.O → ℕ
  t   : Fm.O → ℕ
  /-- the three embeddings -/
  eB  : (BldWfN.mk n (Cf.X.v + klo) rv d w nd).Bit ↪ Fm.lay.Dt a₁
  e1  : (BldWfN.mk n (Cf.X.v + klo) rv d w nd).Msk1 E ↪ Fm.lay.Fr a₁
  e2  : (BldWfN.mk n (Cf.X.v + klo) rv d w nd).Msk2 E ↪ Fm.lay.Fr a₂
  p0  : Cf.conf.PIdx
  r0  : Fm.sig.Rnd
  Lt  : BldWfLin Cf Rw klo

attribute [instance] BldWf2.finRw

namespace BldWf2
variable {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E] [DecidableEq E]
  [Algebra F E] (T : BldWf2 F E)

@[reducible] def num : BldWfN := ⟨T.n, T.Cf.X.v + T.klo, T.rv, T.d, T.w, T.nd⟩

open Classical in
/-- where a mask stands -/
def pM : T.num.Msk E → Σ a, T.Fm.lay.Fr a :=
  Sum.elim (fun s =>
      if h : T.num.Last E s then ⟨T.a₂, T.e2 (Sum.inl ⟨s, h⟩)⟩ else ⟨T.a₁, T.e1 ⟨s, h⟩⟩)
    fun i => ⟨T.a₂, T.e2 (Sum.inr i)⟩

/-- what stands in the first message -/
def inFirst : T.num.N E → Prop
  | .inl _ => True
  | .inr (.inl s) => ¬ T.num.Last E s
  | .inr (.inr _) => False

/-- The parameters of Cb/Ld/LdBldWf.lean (`BldWf`). -/
@[reducible] def X : BldWf F E E where
  Cf := T.Cf
  Rw := T.Rw
  klo := T.klo
  lay := T.lay
  n := T.n
  rv := T.rv
  d := T.d
  w := T.w
  nd := T.nd
  o := T.o
  co := T.co
  tab := T.tab
  Z := T.Z
  S := T.Fm.sig
  Sd := T.Fm.Sd
  Y := T.Fm.lay
  L := T.L
  t := T.t
  pB := fun b => ⟨T.a₁, T.eB b⟩
  pM := T.pM
  gR := fun _ _ => T.inFirst
  p0 := T.p0
  r0 := T.r0
  l := T.Lt.l
  py := T.Lt.py
  e' := T.Lt.e'
  tt := T.Lt.tt
  NW := T.Lt.NW
  SdW := T.Lt.SdW
  iW := T.Lt.iW
  lW := T.Lt.lW
  NU := T.Lt.NU
  SdU := T.Lt.SdU
  iU := T.Lt.iU
  lU := T.Lt.lU
  NO := T.Lt.NO
  SdO := T.Lt.SdO
  iO := T.Lt.iO
  lO := T.Lt.lO

end BldWf2

namespace Spec
section
variable (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [DecidableEq E] [Algebra F E]

/-- States what is left of `X.Room p`: five premises give `T.X.Room p`. -/
def bldWf2_room : Prop :=
  ∀ (T : BldWf2 F E) (p : ℕ), T.a₁ ≠ T.a₂ → (∀ f, f ≤ T.n → 1 ≤ T.rv f + T.num.k) →
    (∀ f, f ≤ T.n →
      T.nd f + 1 ≤ 2 ^ T.w f ∧
      2 ^ (T.rv f + T.num.k) < 2 ^ (T.nd f + 1) ∧
      2 ^ T.d f * (2 ^ (T.nd f + 1) - 1) < p) →
    T.Z.OK →
    (∀ U,
      (T.Cf.conf.held U).isSome ↔
      ∀ f, f ≤ T.n → InTable (T.rv f + T.num.k) (T.d f) (T.X.key f U) (T.tab f)) → T.X.Room p

/-- States which message holds what. -/
def bldWf2_where : Prop :=
  ∀ T : BldWf2 F E,
    (∀ f b n, T.X.P.gR f b n → (T.X.nAt n).1 = T.a₁) ∧
    (∀ f, f ≤ T.n → ∀ n, T.X.P.gC f n → (T.X.nAt n).1 = T.a₂) ∧
    ∀ i, (T.X.nAt (T.X.P.wAt i)).1 = T.a₂

end
end Spec
end Cb
