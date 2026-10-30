-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdTowerTwo.lean: the test that the joints fit: a tower of two stages and the base case,
written out at the blocks themselves.

In standard terms: a proximity test with two recursion steps (each a sumcheck that folds the word,
then a switch to a new code) and a base case, written as one term of type `LdTower`
(Cb/Ld/LdTower.lean).

Definitions, one statement (`Spec.ldTower_two`) and its proof (an assembly). Generic: any finite
field, any codes, any numbers. The three sets of long positions are not empty (`[Nonempty P₁]`,
`[Nonempty P₂]`, `[Nonempty P₃]`).
The file follows the paper that this protocol builds on (lean/CREDITS.md).

   fold Y₁ ; switch into the input code of Y₂ (`SumPar.Cin`, Cb/Ld/LdSum.lean) ; [cut the batched
   form] ; fold Y₂ ; switch into any code C₃ ; base case on C₃.
That the definition `twoTower` is accepted is the test: every block's output joint is the next
block's input joint, with nothing in between but the step without rounds that cuts the batched form.
In particular
   * the first switch's new code is the second fold's input code (a main table and a mask table side
     by side, rows on the cubes), and its new message is laid into it by `ldPlace`: the folded main
     word's message fills the next main table; the two folded masks' messages, the three encoding
     randomnesses and the pad fill the next mask table (two bijections of coordinates pm, pz: the
     text's two equations between sizes);
   * the second fold's two forms are the two parts of the first switch's batched form, both with
     that form's states (Cb/Ld/LdTowerSum.lean: `reform`).

Main names:
  `TwoPar.OK` has five fields: `SumGood` of each of the two folds (hypotheses:
    Cb/Ld/LdTowerSum.lean), the hypotheses of each of the two switches, each at what the rest needs,
    and the hypotheses of the base case.
  `Spec.ldTower_two`: under `TwoPar.OK` the tower is OK (`LdTower.OK`, Cb/Ld/LdTower.lean), and it
    needs ts₁ long positions of the input; so it has all that `Spec.ldTower_end`
    (Cb/Ld/LdTower.lean) says, from the relaxation of the first joint at e₁ (what it concludes,
    clause by clause: the row of `Spec.ldTower_end` in the head of Cb/Ld/LdTower.lean).
Three radii e₁, e₂, e₃: e₁ for the first stage's input and middle joint, e₂ for the second's, e₃ for
the base case.
A widening. The second switch goes into any code C₃ by any bijection of coordinates place₂, as the
switch's and the base case's own statements allow. The last stage of the paper that this protocol
builds on is the instance: C₃ again a main and a mask code side by side (no rows left to fold),
place₂ = `ldPlace`.

Limits: this file does not say that `TwoPar.OK` can be met.
What the heads of Cb/Ld/LdTower.lean and Cb/Ld/LdTowerSum.lean list as not said is not said here
either.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdTowerSum

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop IOR

/-- The data of a tower of two stages. -/
structure TwoPar (E P₁ P₂ P₃ : Type) [Field E] [Fintype E] [Fintype P₁] [Nonempty P₁] [Fintype P₂]
    [Nonempty P₂] [Fintype P₃] [Nonempty P₃] where
  Y₁ : SumPar E P₁
  /-- of Y₂ the forms are not read: they are replaced by the two parts of the first switch's batched
  form -/
  Y₂ : SumPar E P₂
  C₃ : LdCode E P₃
  [finA₁ : Fintype Y₁.Cout.Aa]
  [finA₂ : Fintype Y₂.Cout.Aa]
  Qo₁ : Type
  [finQ₁ : Fintype Qo₁]
  [decQ₁ : DecidableEq Qo₁]
  Qo₂ : Type
  [finQ₂ : Fintype Qo₂]
  [decQ₂ : DecidableEq Qo₂]
  /-- the folded main word's message fills the next main table; all the rest fills the next mask
  table -/
  pm : Y₁.C.J ≃ (Fin Y₂.k → Bool) × Y₂.C.J
  pz : ((Y₁.Z.J ⊕ Y₁.Zw.J) ⊕ (Y₁.C.Q ⊕ (Y₁.Z.Q ⊕ Y₁.Zw.Q))) ⊕ Qo₁ ≃ (Fin Y₂.h → Bool) × Y₂.Z.J
  place₂ : (Y₂.Cout.J ⊕ Y₂.Cout.Q) ⊕ Qo₂ ≃ C₃.J
  Zo₁ : Ood.Sample E ((Y₁.Cout.J ⊕ Y₁.Cout.Q) ⊕ Qo₁)
  ts₁ : ℕ
  Zb₁ : Evader E (LdRow Zo₁.S ts₁ Y₁.Cout.Aa)
  Zo₂ : Ood.Sample E ((Y₂.Cout.J ⊕ Y₂.Cout.Q) ⊕ Qo₂)
  ts₂ : ℕ
  Zb₂ : Evader E (LdRow Zo₂.S ts₂ Y₂.Cout.Aa)
  /-- the base case: positions, where a native position is looked up -/
  t₃ : ℕ
  cov : C₃.NP → P₃
  /-- the three radii -/
  e₁ : ℕ
  e₂ : ℕ
  e₃ : ℕ

attribute [instance] TwoPar.finA₁ TwoPar.finA₂ TwoPar.finQ₁ TwoPar.decQ₁ TwoPar.finQ₂ TwoPar.decQ₂

noncomputable section
namespace TwoPar
variable {E P₁ P₂ P₃ : Type} [Field E] [Fintype E] [Fintype P₁] [Nonempty P₁] [Fintype P₂]
  [Nonempty P₂] [Fintype P₃] [Nonempty P₃] (V : TwoPar E P₁ P₂ P₃)

/-- the first switch: into the input code of the second fold -/
def D₁ : LdSw E P₁ P₂ (V.Y₁.jOut V.e₁).St :=
  ldSwAfter V.Y₁ V.e₁ V.Y₂.Cin V.Qo₁ (ldPlace V.pm V.pz) V.Zo₁ V.ts₁ V.Zb₁

/-- the second fold, with the two parts of the first switch's batched form -/
def Y₂' : SumPar E P₂ := V.Y₂.reform V.D₁.sl'

instance : Fintype V.Y₂'.Cout.Aa := V.finA₂

/-- the second switch: into C₃ -/
def D₂ : LdSw E P₂ P₃ (V.Y₂'.jOut V.e₂).St :=
  ldSwAfter V.Y₂' V.e₂ V.C₃ V.Qo₂ V.place₂ V.Zo₂ V.ts₂ V.Zb₂

end TwoPar

/-- what is not data of the protocol: the two extractors, the numbers in the errors -/
structure TwoNums {E P₁ P₂ P₃ : Type} [Field E] [Fintype E] [Fintype P₁] [Nonempty P₁] [Fintype P₂]
    [Nonempty P₂] [Fintype P₃] [Nonempty P₃] (V : TwoPar E P₁ P₂ P₃) where
  ext₁ : (V.Y₁.jIn V.e₁).X × V.Y₁.Cin.ext.Str → Tr V.Y₁.ior.shape →
    (V.Y₁.jOut V.e₁).W → (V.Y₁.jIn V.e₁).W
  ext₂ : (V.Y₂'.jIn V.e₂).X × V.Y₂'.Cin.ext.Str → Tr V.Y₂'.ior.shape →
    (V.Y₂'.jOut V.e₂).W → (V.Y₂'.jIn V.e₂).W
  Lst₁ : ℕ → ℕ
  mC₁ : ℕ → ℕ
  mS₁ : ℕ → ℕ
  mW₁ : ℕ → ℕ
  Lst₂ : ℕ → ℕ
  mC₂ : ℕ → ℕ
  mS₂ : ℕ → ℕ
  mW₂ : ℕ → ℕ
  /-- the lists of the two new codes at their radii -/
  L₁ : ℕ
  L₂ : ℕ
  /-- the base case: the corrector's threshold, the exceptional coefficients, the list of the
  doubled code -/
  d : ℕ
  bad : ℕ
  L2 : ℕ

variable {E P₁ P₂ P₃ : Type} [Field E] [Fintype E] [Fintype P₁] [Nonempty P₁] [Fintype P₂]
  [Nonempty P₂] [Fintype P₃] [Nonempty P₃] (V : TwoPar E P₁ P₂ P₃) (M : TwoNums V)

/-- The tower. -/
def twoTower : LdTower (V.Y₁.jIn V.e₁) :=
  LdTower.step (V.Y₁.jIn V.e₁) V.D₁
    (ldSumBlock V.Y₁ V.e₁ M.ext₁ V.ts₁ M.Lst₁ M.mC₁ M.mS₁ M.mW₁) V.e₂ M.L₁
    (LdTower.step (V.D₁.jOut V.e₂) V.D₂
      (ldSumAfter V.Y₂ V.e₂ V.ts₂ M.Lst₂ M.mC₂ M.mS₂ M.mW₂ V.D₁.sl' M.ext₂) V.e₃ M.L₂
      (LdTower.base (V.D₂.jOut V.e₃) (ldBaseEnd (V.D₂.jOut V.e₃) V.t₃ V.cov M.d M.bad M.L2) V.t₃))

/-- The conditions. -/
structure TwoPar.OK : Prop where
  fold₁ : SumGood V.Y₁ V.e₁ M.ext₁ V.ts₁ M.Lst₁ M.mC₁ M.mS₁ M.mW₁
  sw₁   : V.D₁.Hyp V.e₂ M.L₁ V.ts₂
  fold₂ : SumGood V.Y₂' V.e₂ M.ext₂ V.ts₂ M.Lst₂ M.mC₂ M.mS₂ M.mW₂
  sw₂   : V.D₂.Hyp V.e₃ M.L₂ V.t₃
  base  : (V.D₂.jOut V.e₃).BaseHyp M.d M.bad M.L2

end

/-- The joints fit. `V.OK M` → the tower is OK; it needs ts₁ long positions of the input; it has
(k₁ + 3) + (k₂ + 3) + 2 rounds (k₁ = `V.Y₁.k`, k₂ = `V.Y₂.k`). (P₁, P₂, P₃ are not empty.) -/
def Spec.ldTower_two : Prop :=
  ∀ (E P₁ P₂ P₃ : Type) [Field E] [Fintype E] [Fintype P₁] [Nonempty P₁] [Fintype P₂] [Nonempty P₂]
      [Fintype P₃] [Nonempty P₃] (V : TwoPar E P₁ P₂ P₃) (M : TwoNums V),
    V.OK M →
    (twoTower V M).OK ∧
    (twoTower V M).q = V.ts₁ ∧
    (twoTower V M).toEnd.R.shape.length = (V.Y₁.k + 3) + (V.Y₂.k + 3) + 2

theorem ldTower_two : Spec.ldTower_two := by
  intro E P₁ P₂ P₃ _ _ _ _ _ _ _ _ V M h
  refine ⟨⟨ldTower_sum E P₁ V.Y₁ V.e₁ M.ext₁ V.ts₁ M.Lst₁ M.mC₁ M.mS₁ M.mW₁ h.fold₁,
      h.sw₁,
      (ldTower_sum_after E P₂ V.Y₂ V.e₂ V.ts₂ M.Lst₂ M.mC₂ M.mS₂ M.mW₂ _ V.D₁.sl' M.ext₂ h.fold₂).1,
      h.sw₂,
      ldTower_base E (V.D₂.jOut V.e₃) V.t₃ V.cov M.d M.bad M.L2 h.base⟩,
    rfl, ?_⟩
  rw [ldTower_rounds]
  show (V.Y₁.round0 :: List.replicate V.Y₁.k _).length + 2 +
      (([] ++ (V.Y₂'.round0 :: List.replicate V.Y₂.k _)).length + 2 + 2) = _
  rw [List.nil_append, List.length_cons, List.length_cons,
    List.length_replicate, List.length_replicate]
  omega

end Cb
