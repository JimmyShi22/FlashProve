-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Part/LdPartKeepOf.lean: under the hypotheses below, the reading of all open messages of a body
restricts to the reading of the kept ones: the tie of Cb/Part/LdPartKeep.lean (`LdPartKeepTie`: two
clauses) for the concrete readings (`nm.out`, Cb/Part/LdPartCellsOut.lean).

Book-keeping for the range check with packing: under `T.OK P k pp` with pp the characteristic of E,
and where the open messages' packed entries are a packing, the cells read off the kept oracle
messages are, on the kept rows, those read off all open ones. Definitions, one statement
(`Cb.Spec.ldPartKeepOf`) and its proof: two applications of Cb/Part/LdPartTieNmProofs.lean.

Main names:
  `T : LdPartKeepL S Sk`: p, nm, at': parameters, naming and places of the body's matrix among the
    open messages S; p₀, nm₀, at₀: those of the matrix that the kept messages Sk hold; r: the kept
    messages of a tuple; ι, κ: where a kept packed row and its columns stand in the body's matrix.
  `T.OK P k pp`: the packing factors are equal, radix, bound and window the same; unique packing at
    pp; both namings meet `LdPartNm.OK`; nm₀ is the part of nm on ι, κ (`LdPartNm.PartOf`,
    Cb/Part/LdPartTieNm.lean); the entry of a kept message at a place of nm₀'s matrix is the entry
    of the tuple at the corresponding place of nm's; every row kept behind k is named by nm₀.
  `Spec.ldPartKeepOf`: pp the characteristic of E, `T.OK P k pp` ⇒
    `LdPartKeepTie P k (nm.out S at') (nm₀.out Sk at₀) r`. Exact: packed in the whole, packed in the
    part. Relaxed: where the body's matrix is a packing, both readings agree at every kept row, in
    all columns.

Limits: All parameters are variables: nothing here is stated of the model or of concrete numbers,
and nothing here shows that any parameters meet the hypotheses. This file does not say that r is a
restriction of tuples. As in Cb/Part/LdPartTieOf.lean, all kept rows stand in the body's matrix:
declared there.
This file gives no instance that meets its hypotheses, so as far as this file shows its theorems may
hold of nothing.

Terms: lean/GLOSSARY.md.
-/
import Cb.Part.LdPartKeep
import Cb.Part.LdPartCellsOut
import Cb.Part.LdPartTieNmProofs

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Finset Cb.Rng Cb.RngPk IOR

/-- The parameters. -/
structure LdPartKeepL {E : Type} [Field E] (S Sk : Sig E) where
  p   : RngPar
  p₀  : RngPar
  nm  : LdPartNm p
  nm₀ : LdPartNm p₀
  at' : p.Rp → p.C → S.Ent
  at₀ : p₀.Rp → p₀.C → Sk.Ent
  r   : S.Msg → Sk.Msg
  ι   : p₀.Rp → p.Rp
  κ   : p₀.C → p.C

/-- The conditions. -/
structure LdPartKeepL.OK {F E : Type} [Field F] [Field E] [Algebra F E] {Cf : LdCf F E}
    {S Sk : Sig E} (T : LdPartKeepL S Sk) (P : LdPartD Cf) (k pp : ℕ) : Prop where
  nP    : T.p₀.P = T.p.P
  rdx   : T.p₀.rdx = T.p.rdx
  B     : T.p₀.B = T.p.B
  D     : T.p₀.D = T.p.D
  uniq  : Uniq (2 * T.p.D) T.p.rdx T.p.P pp
  ok₀   : T.nm₀.OK
  ok    : T.nm.OK
  part  : T.nm₀.PartOf T.nm T.ι T.κ
  ent   : ∀ m i c, Sk.ents (T.r m) (T.at₀ i c) = S.ents m (T.at' (T.ι i) (T.κ c))
  named : ∀ q ∈ P.kept k, q.2 < T.nm₀.R q.1

def Spec.ldPartKeepOf : Prop :=
  ∀ (F E : Type) [Field F] [Field E] [Algebra F E] (Cf : LdCf F E) (P : LdPartD Cf) (k pp : ℕ)
      [CharP E pp] (S Sk : Sig E) (T : LdPartKeepL S Sk),
    T.OK P k pp → LdPartKeepTie P k (T.nm.out S T.at') (T.nm₀.out Sk T.at₀) T.r

theorem ldPartKeepOf : Spec.ldPartKeepOf := by
  intro F E _ _ _ Cf P k pp _ S Sk T h
  have he : ∀ m,
      (fun i κ => Sk.ents (T.r m) (T.at₀ i κ)) = resM T.ι T.κ fun i κ => S.ents m (T.at' i κ) :=
    fun m => funext fun i => funext fun c => h.ent m i c
  refine ⟨fun m g hx => ?_, fun m hr q hq c => ?_⟩
  · have hx' : PackBy T.p.B T.p.rdx (T.nm.lay g) (fun i κ => S.ents m (T.at' i κ)) := hx
    show PackBy T.p₀.B T.p₀.rdx (T.nm₀.lay g) (fun i κ => Sk.ents (T.r m) (T.at₀ i κ))
    rw [h.B, h.rdx, he m]
    exact ldPartTieNm_packPart E T.p₀ T.p T.nm₀ T.nm T.ι T.κ g _ _ _ h.nP h.ok₀ h.ok h.part hx'
  · have hr' : Packed T.p.P (2 * T.p.D) T.p.rdx (fun i κ => S.ents m (T.at' i κ)) := hr
    show ((T.nm.mats (cells T.p.P (2 * T.p.D) T.p.rdx fun i κ => S.ents m (T.at' i κ))
        q.1 q.2 c : ℤ) : E) =
      ((T.nm₀.mats (cells T.p₀.P (2 * T.p₀.D) T.p₀.rdx fun i κ => Sk.ents (T.r m) (T.at₀ i κ))
        q.1 q.2 c : ℤ) : E)
    rw [he m, h.D, h.rdx,
      ldPartTieNm_readPart E pp T.p₀ T.p T.nm₀ T.nm T.ι T.κ _ _ _ h.nP h.part h.uniq hr'
        q.1 q.2 c (h.named q hq)]

end Cb
