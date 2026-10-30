-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/GlVal/GlToyFam.lean: a small test instance of a family of two oracle messages over a Reed-Solomon
code of length 8, read at the radius 1: every hypothesis on codes and sample maps of
`Spec.stdFam_all` (the record `StdFam.Hyp`, Cb/Ld/LdSendToyFam.lean) is proved for it, for injective
placements, nothing assumed beyond the hypotheses of the statements and whatever the arguments hold
as proofs.

For the guard over p = 2^64 - 2^32 + 1: the family "a vector, and masks only".
A definition, a statement (`Cb.Gl.Spec.fam8_hyp`) and its proof. No parameter of a protocol. The
analogue, over the fields of Cb/Gl/GlField.lean, of Cb/Ld/LdSendToyFam7.lean.

The codes. Cb/GlVal/GlToyBase.lean: Reed-Solomon over F on the subgroup of order 8, one message
symbol and two symbols of randomness a row, read over E: distance 6; radius 1 (3 · 1 < 6); lists of
at most one member; the encoding hides 2 long positions. One row for each entry of the vector (of
the masks), and one row for the pad.
The samples. The row with a pad of Cb/Gen/OodDecPad.lean, over E; the pad's coefficient is the one
value 1 (as in Cb/GlVal/GlToyMsg.lean: nothing may enumerate the field (see "Why the numerals" in
the head of Cb/GlVal/GlToyBase.lean); no condition asks for more than: different values, none of
them 0).

Main names:
  `fam8 Ix Im μ₁ μ₂ pl₁ pl₂`: for any finite index sets Ix (the vector), Im (the masks) and cubes
    μ₁, μ₂.
  `Spec.fam8_hyp`: for injective placements: the record `StdFam.Hyp` at lists 1, 1 and 2, 2 hidden
    positions; both codes have the distance 6; 3 · 1 < 6.
So, for injective placements, by `Spec.stdFam_all` (Cb/Ld/LdSendToyFam.lean), for every type Wr of
witnesses handed on the sender `(fam8 ..).snd Wr r0` meets all conditions of the theorems on
sendings together.

Limits: this file says nothing on real parameters. It says nothing on the size of the sample's
number against the number of seeds.
Terms: lean/GLOSSARY.md.
-/
import Cb.GlVal.GlToyMsg
import Cb.Ld.LdSendToyFam

set_option autoImplicit false

namespace Cb.Gl
open Iop Prob Hiop Blocks Cb.Ood

variable (Ix Im μ₁ μ₂ : Type) [Fintype Ix] [DecidableEq Ix] [Fintype Im] [DecidableEq Im]
  [Fintype μ₁] [DecidableEq μ₁] [Fintype μ₂] [DecidableEq μ₂]

/-- The family at the eight positions, radius 1. -/
@[reducible] def fam8 (pl₁ : Ix → μ₁ → Bool) (pl₂ : Im → μ₂ → Bool) : StdFam E where
  Ix := Ix
  Im := Im
  Pd₁ := Unit
  Pd₂ := Unit
  P₁ := P8
  P₂ := P8
  C₁ := toyLd8 (Ix ⊕ Unit)
  C₂ := toyLd8 (Im ⊕ Unit)
  ν₁ := (toyPlace8 (Ix ⊕ Unit)).symm
  ν₂ := (toyPlace8 (Im ⊕ Unit)).symm
  Z₁ := Sample.pad E μ₁ Ix Unit Unit pl₁ (fun _ => 1) fun _ => 1
  Z₂ := Sample.pad E μ₂ Im Unit Unit pl₂ (fun _ => 1) fun _ => 1
  e₁ := 1
  e₂ := 1

def Spec.fam8_hyp : Prop :=
  ∀ (Ix Im μ₁ μ₂ : Type) [Fintype Ix] [DecidableEq Ix] [Fintype Im] [DecidableEq Im] [Fintype μ₁]
      [DecidableEq μ₁] [Fintype μ₂] [DecidableEq μ₂] (pl₁ : Ix → μ₁ → Bool) (pl₂ : Im → μ₂ → Bool),
    Function.Injective pl₁ → Function.Injective pl₂ →
    (fam8 Ix Im μ₁ μ₂ pl₁ pl₂).Hyp 1 1 2 2 ∧
    (fam8 Ix Im μ₁ μ₂ pl₁ pl₂).C₁.Dist 6 ∧
    (fam8 Ix Im μ₁ μ₂ pl₁ pl₂).C₂.Dist 6 ∧
    3 * 1 < 6

theorem pad8_ok (J₀ μ : Type) [Fintype J₀] [Fintype μ] [DecidableEq μ]
    (pl : J₀ → μ → Bool) (h : Function.Injective pl) :
    (Sample.pad E μ J₀ Unit Unit pl (fun _ => 1) fun _ => 1).OK :=
  fun v hv =>
    ood_okOn_pad E E μ J₀ Unit Unit pl _ _ h (fun _ _ _ => rfl)
      std_padBasis.1 v (fun _ => ⟨_, rfl⟩) hv

theorem pad8_priv (J₀ μ : Type) [Fintype J₀] [Fintype μ] [DecidableEq μ] (pl : J₀ → μ → Bool) :
    (Sample.pad E μ J₀ Unit Unit pl (fun _ => 1) fun _ => 1).Private E fun _ => True :=
  fun ρ _ a => ood_private_pad E E μ J₀ Unit Unit pl _ _ std_padBasis ρ one_ne_zero a

theorem fam8_hyp : Spec.fam8_hyp := by
  intro Ix Im μ₁ μ₂ _ _ _ _ _ _ _ _ pl₁ pl₂ h₁ h₂
  obtain ⟨-, hL₁, hD₁, -, -, hZ₁, -, hl₁, -⟩ := gl_toy8 (Ix ⊕ Unit)
  obtain ⟨-, hL₂, hD₂, -, -, hZ₂, -, hl₂, -⟩ := gl_toy8 (Im ⊕ Unit)
  exact ⟨⟨hL₁, hL₂, hl₁, hl₂, pad8_ok Ix μ₁ pl₁ h₁, pad8_ok Im μ₂ pl₂ h₂, pad8_priv Ix μ₁ pl₁,
      pad8_priv Im μ₂ pl₂, hZ₁, hZ₂⟩,
    hD₁, hD₂, by norm_num⟩

end Cb.Gl
