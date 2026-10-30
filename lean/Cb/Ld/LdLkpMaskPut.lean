-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLkpMaskPut.lean: the own masks of a chain of masked blocks are "overwrite the entries at
named places", under the hypotheses of `Spec.mjPl_chain`.
This file is book-keeping: the map `put` of an `MJ` record, written as the overwriting of
coordinates at named positions.

Definitions, and statements (in `Cb.Spec`); the proofs are in Cb/Ld/LdLkpMaskPutProofs.lean. No
protocol of its own, no code occurs here. This file has the places of the `MJ` records of the
sumcheck for a polynomial summand and of the verifier's draw.
This file uses Cb/Ld/LdLkpMaskChain.lean, Cb/Ld/LdLkpMaskPsc.lean, Cb/Ld/LdLkpMaskKit.lean,
Cb/Ld/LdLkpMaskOur.lean (the `MJ` record of the item "masked messages" over one tuple of entries,
and how such records are put together). The fields of an `MJ` record, `Mk` and `put` among them: the
head of Cb/Ld/LdLkpMaskChain.lean, the row of `MJ E J R`.

Why: the `MJ` record of a chain gives its own masks as a type `Mk` (a nest of pairs) and `put` (a
composition of overwritings). Whoever sends these masks (Cb/Ld/LdSendFresh.lean and the other files
whose names begin so), or carries the fact that they are fresh (Cb/Req1/LdSegCarry.lean), wants them
in one flat form: a set of places among the entries, and a value in E for each place, all values
free.

Main names:
  `D.PutAt pl ve`: pl : I → J is injective (the places); ve : D.Mk ≃ (I → E) (a mask value is a
    value for each place, none missing, none twice); `D.put M k` overwrites k at the places by ve M,
    and leaves all other entries.
  `D.Pl`: the data (I, pl, ve), so that they can be put together as the `MJ` records are; `P.OK` is
    `D.PutAt P.pl P.ve`; `P.At j`: j is one of the places.
  `PscPar.plOf`, `Pl.reJ`, `Pl.post`, `Pl.pre`, `Pl.narrow`, `Pl.silent`, `Pl.seq`, `Pl.chain`: the
    data for: the sumcheck for a polynomial summand (places: `O.at`); entries named otherwise; a map
    on the explicit part after or before; a stronger claim; a step in which only the verifier speaks
    (no place); two in a row (the places of both); the blocks b 0 .. b n in a row.
  `Spec.mjPl_psc`, `Spec.mjPl_reJ` to `Spec.mjPl_silent`: each of these is OK if its part is (the
    sumcheck: if its places are different: the first clause of `Y.OwnOK`, Cb/Ld/LdPscZk.lean).
  `PscOur.plJ`, `Spec.mjPl_our`: the instance with the dummy variable, over common entries
    (Cb/Ld/LdLkpMaskOur.lean).
  `Spec.mjPl_seq`: two in a row: if `P₁.OK`, `P₂.OK`, and no place of the first is a place of the
    second, then `(P₁.seq P₂).OK`.
  `Spec.mjPl_chain`: a chain of any length: if every block OK, places of different blocks different,
    then `(MJ.Pl.chain X b D P n).OK`.
  `Spec.mjPl_at_seq`, `Spec.mjPl_at_chain`, and, under the premise of their statement, the second
    halves of `Spec.mjPl_reJ` to `Spec.mjPl_silent`: the places of each: unchanged by post, pre,
    narrow; the images under a renaming; none; those of the first or of the second; those of some
    block l ≤ n.
  `Spec.mjPl_writes`: if `P.OK`, `D.Writes P.At`: so the set Sw of a link (`MJ.Link`,
    Cb/Ld/LdLkpMaskSp.lean) can be taken to be the places.
  `Spec.mjPl_over`: if `P.OK`, to overwrite twice is to overwrite once.

Limits: this file says nothing on what the blocks read.
It says nothing on the letters (the `MJ` records) of the lookup's parts: see
Cb/Ld/LdLkpMaskPutLkp.lean.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdLkpMaskOur
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop IOR Prob Hiop

namespace MJ
variable {E J J' : Type} {X₁ X₂ X₃ Xi Xi' Xo Xo' : Type} {E₁ E₂ E₃ Ei Ei' Eo Eo' : ExtSpec}

/-- The own masks are: overwrite the entries at the places pl. -/
structure PutAt {R : IOR Xi Ei Xo Eo} (D : MJ E J R) {I : Type} (pl : I → J) (ve : D.Mk ≃ (I → E)) :
    Prop where
  inj : Function.Injective pl
  put : ∀ M k, D.put M k = Function.extend pl (ve M) k

/-- The data. -/
structure Pl {R : IOR Xi Ei Xo Eo} (D : MJ E J R) : Type 1 where
  I  : Type
  pl : I → J
  ve : D.Mk ≃ (I → E)

namespace Pl

def OK {R : IOR Xi Ei Xo Eo} {D : MJ E J R} (P : D.Pl) : Prop := D.PutAt P.pl P.ve
/-- `j` is one of the places. -/
def At {R : IOR Xi Ei Xo Eo} {D : MJ E J R} (P : D.Pl) (j : J) : Prop := ∃ i, P.pl i = j

def reJ {R : IOR Xi Ei Xo Eo} {D : MJ E J' R} (P : D.Pl) (e : J' ≃ J) : (D.reJ e).Pl :=
  ⟨P.I, fun i => e (P.pl i), P.ve⟩
def post {R : IOR Xi Ei Xo Eo} {D : MJ E J R} (P : D.Pl) (f : Xo → Option Xo')
    (g : ExtMap Eo Eo') (φ : Xo → Xo') : (D.post f g φ).Pl :=
  ⟨P.I, P.pl, P.ve⟩
def pre {R : IOR Xi Ei Xo Eo} {D : MJ E J R} (P : D.Pl) (f : Xi' → Option Xi)
    (g : ExtMap Ei' Ei) (φ : Xi' → Xi) : (D.pre f g φ).Pl :=
  ⟨P.I, P.pl, P.ve⟩
def narrow {R : IOR Xi Ei Xo Eo} {D : MJ E J R} (P : D.Pl) (Cl' : Xi → (J → E) → Prop) :
    (D.narrow Cl').Pl :=
  ⟨P.I, P.pl, P.ve⟩

/-- No place. -/
def silent {X X' : Type} (Dd : Type) [Fintype Dd] [Nonempty Dd] (nx : X → Dd → X')
    (Ex : ExtSpec) (Cl : X → (J → E) → Prop) :
    (MJ.silent (E := E) (J := J) Dd nx Ex Cl).Pl :=
  ⟨Empty, Empty.elim,
    ⟨fun _ i => i.elim, fun _ => (), fun _ => rfl, fun _ => funext fun i => i.elim⟩⟩

/-- The places of both. -/
def seq {R₁ : IOR X₁ E₁ X₂ E₂} {R₂ : IOR X₂ E₂ X₃ E₃} {D₁ : MJ E J R₁} {D₂ : MJ E J R₂}
    (P₁ : D₁.Pl) (P₂ : D₂.Pl) : (D₁.seq D₂).Pl :=
  ⟨P₁.I ⊕ P₂.I,
    Sum.elim P₁.pl P₂.pl,
    (Equiv.prodCongr P₁.ve P₂.ve).trans (Equiv.sumArrowEquivProdArrow P₁.I P₂.I E).symm⟩

/-- The places of the blocks b 0, .., b n. -/
def chain {K M : Type} {Ex : ExtSpec} {Wp : Type} (X : ℕ → Type)
    (b : ∀ l, BkA K M (X l) (X (l + 1)) Ex Wp) (D : ∀ l, MJ E J (b l).R) (P : ∀ l, (D l).Pl) :
    ∀ n, (MJ.chain X b D n).Pl
  | 0 => P 0
  | n + 1 => (chain X b D P n).seq (P (n + 1))

end Pl
end MJ

/-- The places of the sumcheck for a polynomial summand. -/
def PscPar.plOf
    {E : Type} [Field E] [Fintype E] (Y : PscPar E) (Ex : ExtSpec) (O : Y.Own) : (Y.mj Ex O).Pl :=
  ⟨PIdx Y.fmt ⊕ O.Cx, O.at, (Equiv.sumArrowEquivProdArrow (PIdx Y.fmt) O.Cx E).symm⟩

/-- The instance with the dummy variable, over common entries. -/
def PscOur.plJ {E : Type} [Field E] [Fintype E] (T : PscOur E) (Ex : ExtSpec)
    {J : Type} (e : T.J ≃ J) (Rd : J → Prop) : (T.mjJ Ex e Rd).Pl :=
  (T.par.plOf Ex (T.own fun j' => Rd (e j'))).reJ e

namespace Spec

def mjPl_reJ : Prop :=
  ∀ (E J J' Xi Xo : Type) (Ei Eo : ExtSpec) (R : IOR Xi Ei Xo Eo) (D : MJ E J' R)
      (P : D.Pl) (e : J' ≃ J),
    P.OK → (P.reJ e).OK ∧ ∀ j, (P.reJ e).At j ↔ P.At (e.symm j)

def mjPl_post : Prop :=
  ∀ (E J Xi Xo Xo' : Type) (Ei Eo Eo' : ExtSpec) (R : IOR Xi Ei Xo Eo) (D : MJ E J R) (P : D.Pl)
      (f : Xo → Option Xo') (g : ExtMap Eo Eo') (φ : Xo → Xo'),
    P.OK → (P.post f g φ).OK ∧ ∀ j, (P.post f g φ).At j ↔ P.At j

def mjPl_pre : Prop :=
  ∀ (E J Xi Xi' Xo : Type) (Ei Ei' Eo : ExtSpec) (R : IOR Xi Ei Xo Eo) (D : MJ E J R) (P : D.Pl)
      (f : Xi' → Option Xi) (g : ExtMap Ei' Ei) (φ : Xi' → Xi),
    P.OK → (P.pre f g φ).OK ∧ ∀ j, (P.pre f g φ).At j ↔ P.At j

def mjPl_narrow : Prop :=
  ∀ (E J Xi Xo : Type) (Ei Eo : ExtSpec) (R : IOR Xi Ei Xo Eo) (D : MJ E J R)
      (P : D.Pl) (Cl' : Xi → (J → E) → Prop),
    P.OK → (P.narrow Cl').OK ∧ ∀ j, (P.narrow Cl').At j ↔ P.At j

def mjPl_silent : Prop :=
  ∀ (E J X X' : Type) (Dd : Type) [Fintype Dd] [Nonempty Dd] (nx : X → Dd → X')
      (Ex : ExtSpec) (Cl : X → (J → E) → Prop),
    (MJ.Pl.silent (E := E) (J := J) Dd nx Ex Cl).OK ∧
    ∀ j, ¬ (MJ.Pl.silent (E := E) (J := J) Dd nx Ex Cl).At j

/-- Two in a row. -/
def mjPl_seq : Prop :=
  ∀ (E J X₁ X₂ X₃ : Type) (E₁ E₂ E₃ : ExtSpec) (R₁ : IOR X₁ E₁ X₂ E₂) (R₂ : IOR X₂ E₂ X₃ E₃)
      (D₁ : MJ E J R₁) (D₂ : MJ E J R₂) (P₁ : D₁.Pl) (P₂ : D₂.Pl),
    P₁.OK → P₂.OK → (∀ j, P₁.At j → ¬ P₂.At j) → (P₁.seq P₂).OK

def mjPl_at_seq : Prop :=
  ∀ (E J X₁ X₂ X₃ : Type) (E₁ E₂ E₃ : ExtSpec) (R₁ : IOR X₁ E₁ X₂ E₂) (R₂ : IOR X₂ E₂ X₃ E₃)
      (D₁ : MJ E J R₁) (D₂ : MJ E J R₂) (P₁ : D₁.Pl) (P₂ : D₂.Pl) (j : J),
    (P₁.seq P₂).At j ↔ P₁.At j ∨ P₂.At j

def mjPl_at_chain : Prop :=
  ∀ (E J K M : Type) (Ex : ExtSpec) (Wp : Type) (X : ℕ → Type)
      (b : ∀ l, BkA K M (X l) (X (l + 1)) Ex Wp) (D : ∀ l, MJ E J (b l).R)
      (P : ∀ l, (D l).Pl) (n : ℕ) (j : J),
    (MJ.Pl.chain X b D P n).At j ↔ ∃ l ≤ n, (P l).At j

/-- A chain of any length. -/
def mjPl_chain : Prop :=
  ∀ (E J K M : Type) (Ex : ExtSpec) (Wp : Type) (X : ℕ → Type)
      (b : ∀ l, BkA K M (X l) (X (l + 1)) Ex Wp) (D : ∀ l, MJ E J (b l).R)
      (P : ∀ l, (D l).Pl) (n : ℕ),
    (∀ l ≤ n, (P l).OK) → (∀ l l', l < l' → l' ≤ n → ∀ j, (P l).At j → ¬ (P l').At j) →
    (MJ.Pl.chain X b D P n).OK

/-- If `P.OK`, the own masks lie at the places. -/
def mjPl_writes : Prop :=
  ∀ (E J Xi Xo : Type) (Ei Eo : ExtSpec) (R : IOR Xi Ei Xo Eo) (D : MJ E J R) (P : D.Pl),
    P.OK → D.Writes P.At

def mjPl_over : Prop :=
  ∀ (E J Xi Xo : Type) (Ei Eo : ExtSpec) (R : IOR Xi Ei Xo Eo) (D : MJ E J R) (P : D.Pl),
    P.OK → ∀ M M' k, D.put M (D.put M' k) = D.put M k

section
variable (E : Type) [Field E] [Fintype E]

/-- The sumcheck. -/
def mjPl_psc : Prop :=
  ∀ (Y : PscPar E) (Ex : ExtSpec) (O : Y.Own),
    Function.Injective O.at → (Y.plOf Ex O).OK ∧ ∀ j, (Y.plOf Ex O).At j ↔ ∃ i, j = O.at i

/-- The instance with the dummy variable, over common entries. -/
def mjPl_our : Prop :=
  ∀ (T : PscOur E) (Ex : ExtSpec) (J : Type) (e : T.J ≃ J) (Rd : J → Prop),
    Function.Injective (Sum.elim T.wAt T.cAt) →
    (T.plJ Ex e Rd).OK ∧ ∀ j, (T.plJ Ex e Rd).At j ↔ ∃ i, j = e (Sum.elim T.wAt T.cAt i)

end
end Spec
end Cb
