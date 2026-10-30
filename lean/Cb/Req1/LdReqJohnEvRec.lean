-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req1/LdReqJohnEvRec.lean: the forms of sample maps that have a theorem; and two generic records
with "the evader is of a form" in the place of "the evader evades".

Definitions, statements (each a `Prop` in `Cb.Spec`) and proofs: applications, and one count.
Generic: any finite fields. Nothing assumed beyond the hypotheses of the statements and whatever the
arguments hold as proofs.
A sample map `Z : Sample E J` (Cb/Gen/OodDec.lean) has seeds `Z.D`, names of answers `Z.S`, a matrix
`Z.mat ρ` for each seed and a number `Z.err`. `Z.OK`: a vector other than 0 has all answers 0 at no
more than `Z.err` seeds; `Z.OKOn V` (Cb/Gen/OodDecPad.lean): the same for the vectors in V.
Cb/Req1/LdReqJohnEvForm.lean has the forms of zero-evaders (`Z.Form`) with `Z.Form → Z.OK`.

Main names:
  `Z.PadFormOn F`: a sample map on (entries proper ⊕ pad entries) is the row with a pad
    (Cb/Gen/OodDecPad.lean: `Sample.pad`), the entries proper at different corners of the cube, the
    factor injective, the pad's weights independent over F.
  `Z.NoAnsForm`, `Z.CfForm F`: the sample has no answer at all and its number is at least the number
    of seeds; the configuration's sample: the row with a pad or no answer.



  `Z.PadForm F`: `PadFormOn F` with: the weights are a basis of E over F, the factor is never 0.
  `Spec.smpForm_okOn`: `Z.PadFormOn F → Z.OKOn (PadInF F)` (a zero-evader on the vectors whose pad
    part lies in F). `Spec.smpForm_cf`: `Z.CfForm F → Z.OKOn (PadInF F)` (the second case by a
    count).
  `Spec.smpForm_ok`: `Z.PadForm E → Z.OK ∧ Z.PrivateSim E` (pads in E itself: a zero-evader on all
    vectors; private with a simulator, error 0).
  `Z.Rest2Ev p`: Cb/Ld/LdWfEnd.lean's record `Z.Rest2 p` (weights-formedness: the conditions that
    speak neither of a code of an oracle message, nor of a list, nor of the sender, but for: its
    seeds are fair; the vectors that it computes are the multiplicities), field for field, with
    `zOK : Z.W.P.Z.Form`.
  `V.ProtoEv p`: Cb/Req1/LdReqModel.lean's record `V.Proto p` (the protocol's side of a body's
    front), field for field, with `ev : V.Fp.Z.ev.Form`.
  `Spec.evRec_rest2`, `Spec.evRec_front`: each gives the record that it copies (`Z.Rest2 p`,
    `V.Proto p`).

Limits: this file does not say that these are all the forms that this protocol's technical report
(lean/CREDITS.md) uses. It says nothing beyond one answer a sample (the row with a pad has one). It
does not say that a number is small against the number of seeds.
Terms: lean/GLOSSARY.md.
-/
import Cb.Req1.LdReqJohnEvForm
import Cb.Gen.OodDecPadProofs
import Cb.Ld.LdWfEnd
import Cb.Req1.LdReqModel

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR IOR.Chain Cb.Rng Cb.RngPk Cb.Lkp Cb.LdLkp

section
variable (F : Type) {E J₀ P : Type} [Field F] [Field E] [Fintype E] [Algebra F E] [Fintype P]

/-- The sample map is the row with a pad: what makes it a zero-evader on vectors with pads in F. -/
def Ood.Sample.PadFormOn (Z : Sample E (J₀ ⊕ P)) : Prop :=
  ∃ (μ B : Type) (_ : Fintype μ) (_ : DecidableEq μ) (_ : Fintype B) (_ : Nonempty B)
      (pl : J₀ → μ → Bool) (w : P → E) (b : B → E),
    Z = Sample.pad E μ J₀ P B pl w b ∧
    Function.Injective pl ∧
    Function.Injective b ∧
    Function.Injective (padVal (F := F) w)

/-- The sample map has no answer, and its number says so: every seed counts. -/
def Ood.Sample.NoAnsForm {J : Type} (Z : Sample E J) : Prop :=
  IsEmpty Z.S ∧ Fintype.card Z.D ≤ Z.err

/-- The configuration's sample: the row with a pad, or no answer at all. -/
def Ood.Sample.CfForm (Z : Sample E (J₀ ⊕ P)) : Prop := Z.PadFormOn F ∨ Z.NoAnsForm

/-- The same, and what makes it private. -/
def Ood.Sample.PadForm (Z : Sample E (J₀ ⊕ P)) : Prop :=
  ∃ (μ B : Type) (_ : Fintype μ) (_ : DecidableEq μ) (_ : Fintype B) (_ : Nonempty B)
      (pl : J₀ → μ → Bool) (w : P → E) (b : B → E),
    Z = Sample.pad E μ J₀ P B pl w b ∧ Function.Injective pl ∧ Function.Injective b ∧
    PadBasis F w ∧ ∀ β, b β ≠ 0

end

namespace LdWfE
variable {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] (Z : LdWfE F E)

/-- Z.Rest2 p with the evader's form -/
structure Rest2Ev (p : ℕ) : Prop where
  val       : Nonempty Z.W.Cf.conf.E0.Str
  describes : ∀ U, (Z.W.Cf.conf.held U).isSome ↔ ∀ f, f ≤ Z.W.P.n → Z.W.P.InT f U
  lin       : Z.W.P.LinKeys Z.rv Z.o Z.co
  lks       : Z.K.OK p
  deg       : 2 ≤ Z.W.P.deg
  zOK       : Z.W.P.Z.Form
  fair      : Z.W.P.Sd.Fair
  multOf    : ∀ U f, f ≤ Z.W.P.n → Z.W.P.InT f U → Z.W.P.mult f U (Z.W.P.bodyOf U)
  tie       : Z.W.Tie
  lkPl      : ∀ f, f ≤ Z.W.P.n → (Z.K.asm f).PlacesOK (Z.K.Dt f)
  rdL       : ∀ f, f ≤ Z.W.P.n → ∀ j, Z.Sr f j → Z.Rl f j
  own       : Z.W.P.OwnPlaces Z.RdB
  ent       : Z.W.P.EntAt Z.X.nAt
  inRd      : ∀ b i, Z.X.RdW (Z.X.nAt (Z.X.pa b i))
  rdJ       : ∀ b n, Z.X.rd Z.RdB b (Sum.inr n) → Z.X.RdW (Z.X.nAt n)
  atEq      : ∀ (l : Fin (Z.W.P.n + 1)) i,
    (Z.K.pl Z.Rl l).pl i = (Sum.inr (Z.X.atL l i) : Z.W.P.bt.J)
  ownL      : ∀ (l : Fin (Z.W.P.n + 1)) i, Z.Rl l (Sum.inr (Z.X.atL l i))
  apart     : ∀ b j,
    j < Z.G.B.upTo b → ∀ n, Z.Sr j (Sum.inr n) → Z.X.RdW (Z.X.nAt n) ∧ ∀ i, n ≠ Z.X.pa b i

end LdWfE

namespace LdFrontRef
variable {E Kc : Type} [Field E] [Fintype E] {z : LdStage E Kc} (V : LdFrontRef E Kc z)

/-- V.Proto p with the evader's form -/
structure ProtoEv (p : ℕ) : Prop where
  pre   : V.Fp.Proto p
  ev    : V.Fp.Z.ev.Form
  vars0 : V.Fp.Z.T.VarsOK
  inj0  : V.Fp.Z.T.ValInj
  vars  : ∀ i ≤ V.m, (V.T i).VarsOK
  inj   : ∀ i ≤ V.m, (V.T i).ValInj

end LdFrontRef

namespace Spec

def smpForm_okOn : Prop :=
  ∀ (F E J₀ P : Type) [Field F] [Field E] [Fintype E] [Algebra F E] [Fintype J₀]
      [Fintype P] (Z : Sample E (J₀ ⊕ P)),
    Z.PadFormOn F → Z.OKOn (PadInF F)

def smpForm_cf : Prop :=
  ∀ (F E J₀ P : Type) [Field F] [Field E] [Fintype E] [Algebra F E] [Fintype J₀]
      [Fintype P] (Z : Sample E (J₀ ⊕ P)),
    Z.CfForm F → Z.OKOn (PadInF F)

def smpForm_ok : Prop :=
  ∀ (E J₀ P : Type) [Field E] [Fintype E] [Fintype J₀] [Fintype P] (Z : Sample E (J₀ ⊕ P)),
    Z.PadForm E → Z.OK ∧ Z.PrivateSim E

def evRec_rest2 : Prop :=
  ∀ (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] (Z : LdWfE F E) (p : ℕ),
    Z.Rest2Ev p → Z.Rest2 p

def evRec_front : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (z : LdStage E Kc) (V : LdFrontRef E Kc z) (p : ℕ),
    V.ProtoEv p → V.Proto p

end Spec

theorem smpForm_okOn : Spec.smpForm_okOn := by
  rintro F E J₀ P _ _ _ _ _ _ Z ⟨μ, B, _, _, _, _, pl, w, b, rfl, hpl, hb, hw⟩
  exact ood_okOn_pad F E μ J₀ P B pl w b hpl hb hw

theorem smpForm_cf : Spec.smpForm_cf := by
  rintro F E J₀ P _ _ _ _ _ _ Z (h | ⟨-, h⟩)
  · exact smpForm_okOn F E J₀ P Z h
  · intro v _ _
    refine le_trans ?_ h
    rw [← Nat.card_eq_fintype_card]
    exact Nat.card_le_card_of_injective Subtype.val Subtype.val_injective

theorem smpForm_ok : Spec.smpForm_ok := by
  rintro E J₀ P _ _ _ _ Z ⟨μ, B, _, _, _, _, pl, w, b, rfl, hpl, hb, hw, h0⟩
  exact ⟨fun v hv => ood_okOn_pad E E μ J₀ P B pl w b hpl hb hw.1 v (fun _ => ⟨_, rfl⟩) hv,
    ood_privateSim_pad E E μ J₀ P B pl w b hw h0⟩

theorem evRec_rest2 : Spec.evRec_rest2 := fun _ E _ _ _ _ _ _ _ h =>
  { val := h.val, describes := h.describes, lin := h.lin, lks := h.lks, deg := h.deg,
    zOK := evForm_ok E _ _ h.zOK, fair := h.fair, multOf := h.multOf, tie := h.tie, lkPl := h.lkPl,
    rdL := h.rdL, own := h.own, ent := h.ent, inRd := h.inRd, rdJ := h.rdJ, atEq := h.atEq,
    ownL := h.ownL, apart := h.apart }

theorem evRec_front : Spec.evRec_front := fun E _ _ _ _ _ _ h =>
  { pre := h.pre, ev := evForm_ok E _ _ h.ev, vars0 := h.vars0, inj0 := h.inj0,
    vars := h.vars, inj := h.inj }

end Cb
