-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdSendToyFam7.lean: the family "a vector, and masks only" at a small code beyond half the
distance, for injective placements pl₁, pl₂: all that Cb/Ld/LdSendToyFam.lean asks of codes and
samples, nothing assumed beyond the hypotheses of the statement and whatever the arguments hold as
proofs.

Statement (`Cb.Spec.stdFam_toy7`) and proof. A guard against empty theorems; no parameter of a
protocol.

This file gives a small example: for injective placements pl₁, pl₂, Reed-Solomon codes and sample
maps that meet the hypotheses `StdFam.Hyp` of Cb/Ld/LdSendToyFam.lean, at a decoding radius that is
not below half the distance.

The codes. Cb/Ld/LdRelToy7.lean: Reed-Solomon over the field with 101 elements, seven points, one
message symbol and two symbols of randomness a row: distance 5; radius 3 (not below half the
distance); at most 7 codewords in a list; the encoding hides 2 long positions. One row for each
entry of the vector (of the masks), and one row for the pad.
The samples. The row with a pad of Cb/Gen/OodDecPad.lean: the entries stand at corners of a cube
(pl₁, pl₂: any injective placements), a seed is (a point of the cube's dimension, β other than 0),
the answer is (the multilinear extension of the entries at the point) + β · pad.

Main names:
  `Spec.stdFam_toy7`: for injective pl₁, pl₂: the record `StdFam.Hyp` at lists 7, 7 and 2, 2 hidden
    positions; the radius (3: `e₁`, `e₂` of `fam7`) is not below half the distance and is below the
    distance (`Dist 5`, a lower bound; ¬ 2 * 3 < 5; 3 < 5); for cubes of dimension at most 1: (7
    choose 2) · (the sample's number) is below the number of seeds (21 of 100 at dimension 0; 2121
    of 10100 at dimension 1).
So, for injective pl₁, pl₂, by `Spec.stdFam_all` (Cb/Ld/LdSendToyFam.lean), for every type Wr of
witnesses handed on, and every `r0 : Wr`, the sender `(fam7 ..).snd Wr r0` meets all conclusions of
`Spec.stdFam_all` together.

Limits: this file says nothing on real parameters.
Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdSendToyFam
import Cb.Ld.LdSendToy
import Cb.Ld.LdRelToy7

set_option autoImplicit false

namespace Cb
namespace LdToy7
open Iop Prob Hiop Blocks Cb.Ood LdToy

/-- each row holds one message symbol -/
def pl7 (R : Type) [Fintype R] [DecidableEq R] : (toyLd7 R).J ≃ R where
  toFun x := x.2.1
  invFun r := ⟨(), (r, (0 : Fin 1))⟩
  left_inv := by
    rintro ⟨⟨⟩, r, i⟩
    have h : i.val < 1 := i.isLt
    have hi : i = (0 : Fin 1) := Fin.ext (show i.val = 0 from Nat.lt_one_iff.1 h)
    subst hi
    rfl
  right_inv _ := rfl

variable (Ix Im μ₁ μ₂ : Type) [Fintype Ix] [DecidableEq Ix] [Fintype Im] [DecidableEq Im]
  [Fintype μ₁] [DecidableEq μ₁] [Fintype μ₂] [DecidableEq μ₂]

/-- The family at the small code. -/
@[reducible] def fam7 (pl₁ : Ix → μ₁ → Bool) (pl₂ : Im → μ₂ → Bool) : StdFam K where
  Ix := Ix
  Im := Im
  Pd₁ := Unit
  Pd₂ := Unit
  P₁ := P7
  P₂ := P7
  C₁ := toyLd7 (Ix ⊕ Unit)
  C₂ := toyLd7 (Im ⊕ Unit)
  ν₁ := pl7 (Ix ⊕ Unit)
  ν₂ := pl7 (Im ⊕ Unit)
  Z₁ := Sample.pad K μ₁ Ix Unit Bn pl₁ (fun _ => 1) fun β => β.1
  Z₂ := Sample.pad K μ₂ Im Unit Bn pl₂ (fun _ => 1) fun β => β.1
  e₁ := 3
  e₂ := 3

end LdToy7

namespace Spec
open LdToy LdToy7 Cb.Ood

def stdFam_toy7 : Prop :=
  ∀ (Ix Im μ₁ μ₂ : Type) [Fintype Ix] [DecidableEq Ix] [Fintype Im] [DecidableEq Im] [Fintype μ₁]
      [DecidableEq μ₁] [Fintype μ₂] [DecidableEq μ₂] (pl₁ : Ix → μ₁ → Bool) (pl₂ : Im → μ₂ → Bool),
    Function.Injective pl₁ → Function.Injective pl₂ →
    (fam7 Ix Im μ₁ μ₂ pl₁ pl₂).Hyp 7 7 2 2 ∧
    (fam7 Ix Im μ₁ μ₂ pl₁ pl₂).C₁.Dist 5 ∧
    (fam7 Ix Im μ₁ μ₂ pl₁ pl₂).C₂.Dist 5 ∧
    ¬ 2 * 3 < 5 ∧ 3 < 5 ∧
    (Fintype.card μ₁ ≤ 1 →
      Nat.choose 7 2 * (fam7 Ix Im μ₁ μ₂ pl₁ pl₂).Z₁.err <
        Fintype.card (fam7 Ix Im μ₁ μ₂ pl₁ pl₂).Z₁.D) ∧
    (Fintype.card μ₂ ≤ 1 →
      Nat.choose 7 2 * (fam7 Ix Im μ₁ μ₂ pl₁ pl₂).Z₂.err <
        Fintype.card (fam7 Ix Im μ₁ μ₂ pl₁ pl₂).Z₂.D)

end Spec

namespace LdToy7
open Iop Prob Hiop Blocks Cb.Ood LdToy

theorem pad_ok (J₀ μ : Type) [Fintype J₀] [Fintype μ] [DecidableEq μ]
    (pl : J₀ → μ → Bool) (h : Function.Injective pl) :
    (Sample.pad K μ J₀ Unit Bn pl (fun _ => 1) fun β => β.1).OK :=
  fun v hv =>
    ood_okOn_pad K K μ J₀ Unit Bn pl _ _ h (fun _ _ h => Subtype.ext h)
      padBasis.1 v (fun _ => ⟨_, rfl⟩) hv

theorem pad_priv (J₀ μ : Type) [Fintype J₀] [Fintype μ] [DecidableEq μ] (pl : J₀ → μ → Bool) :
    (Sample.pad K μ J₀ Unit Bn pl (fun _ => 1) fun β => β.1).Private K fun _ => True :=
  fun ρ _ a => ood_private_pad K K μ J₀ Unit Bn pl _ _ padBasis ρ ρ.2.2 a

theorem card_Bn : Fintype.card Bn = 100 := by
  rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, ZMod.card]

theorem pad_num (J₀ μ : Type) [Fintype μ] [DecidableEq μ]
    (pl : J₀ → μ → Bool) (h : Fintype.card μ ≤ 1) :
    Nat.choose 7 2 * (Sample.pad K μ J₀ Unit Bn pl (fun _ => 1) fun β => β.1).err <
      Fintype.card (Sample.pad K μ J₀ Unit Bn pl (fun _ => 1) fun β => β.1).D := by
  show Nat.choose 7 2 *
      max (Fintype.card μ * Fintype.card K ^ (Fintype.card μ - 1) * Fintype.card Bn)
        (Fintype.card K ^ Fintype.card μ) <
    Fintype.card ((μ → K) × Bn)
  rw [Fintype.card_prod, Fintype.card_fun, card_Bn, ZMod.card]
  interval_cases Fintype.card μ <;> decide

end LdToy7

open LdToy LdToy7 in
theorem stdFam_toy7 : Spec.stdFam_toy7 := by
  intro Ix Im μ₁ μ₂ _ _ _ _ _ _ _ _ pl₁ pl₂ h₁ h₂
  have T₁ := ld_toy7 (Ix ⊕ Unit)
  have T₂ := ld_toy7 (Im ⊕ Unit)
  exact ⟨⟨T₁.1, T₂.1, T₁.2.2.2.1, T₂.2.2.2.1, pad_ok Ix μ₁ pl₁ h₁, pad_ok Im μ₂ pl₂ h₂,
      pad_priv Ix μ₁ pl₁, pad_priv Im μ₂ pl₂, T₁.2.2.2.2.2.2.1, T₂.2.2.2.2.2.2.1⟩,
    T₁.2.1, T₂.2.1, by norm_num, by norm_num, pad_num Ix μ₁ pl₁, pad_num Im μ₂ pl₂⟩

end Cb
