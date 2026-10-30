-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Gen/BatEvaderNum.lean: the random linear combination of n numbered claims with the coefficients
eq(p, j) at a random point p of g coordinates, n ≤ 2^g: a zero-evader for rows that are numbered 0,
.., n - 1, the equality kernel at a point; and its error as a fraction.
Definitions and statements; the proofs are in Cb/Gen/BatEvaderNumProofs.lean.

Cb/Gen/BatEvader.lean has the notion (`Evader`, `Evader.OK`) and the kernel on the vertices of a
cube (`Evader.eqPt`). Records of claims (`Blocks.Ledger`, Blocks/Form.lean) keep their rows in
lists; for these the rows are numbered, and the kernel on numbers of Blocks/Basic.lean
(`Blocks.eqN`; top bit first) is the one in which the multilinear extensions of Blocks/Ext.lean are
written (`Blocks.ext`, `Blocks.extF`). eqN g 0 p j is eq(p, b) for the g bits b of j.

Main names:
  `Evader.eqNum E g n`: J = Fin n, seeds D = Fin g → E, ze(p)_j = eqN g 0 p j, err = g |E|^(g-1).
  `Spec.ok_eqNum`: it is an evader if n ≤ 2^g (`Blocks.cnt_eqN_zero_le`).
  `Spec.comb_eqNum`: if n ≤ 2^g, the combined form is the extension of the vector of forms at the
    point (`Blocks.extF`), the rows from n on being 0.
  `Spec.err_eqNum`: for `Evader.eqNum`, err ≤ κ |D| follows from g ≤ κ |E|: the fraction is g / |E|.
Terms: lean/GLOSSARY.md.
-/
import Blocks.Ext
import Blocks.StageNums
import Blocks.MergeStage
import Cb.Gen.BatEvader
import Cb.Gen.Tensor

set_option autoImplicit false

namespace Cb
open Blocks Iop Prob Alg
open scoped ENNReal

/-- The equality kernel at a point, on numbers. -/
@[reducible] def Evader.eqNum (E : Type) [Field E] [Fintype E] (g n : ℕ) : Evader E (Fin n) :=
  { D := Fin g → E, ze := fun p j => eqN g 0 (nat p) j.val, err := g * Fintype.card E ^ (g - 1) }

namespace Spec

def ok_eqNum : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (g n : ℕ), n ≤ 2 ^ g → (Evader.eqNum E g n).OK

def comb_eqNum : Prop :=
  ∀ (E N : Type) [Field E] [Fintype E] (g n : ℕ), n ≤ 2 ^ g →
    ∀ (p : Fin g → E) (f : ℕ → Form N E), (Evader.eqNum E g n).comb p (fun j : Fin n => f j.val) =
      extF g (fun X => if X < n then f X else 0) (nat p)

def err_eqNum : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (g n : ℕ) (κ : ℝ≥0∞), (g : ℝ≥0∞) ≤ κ * Fintype.card E →
    ((Evader.eqNum E g n).err : ℝ≥0∞) ≤ κ * Fintype.card (Evader.eqNum E g n).D

end Spec
end Cb
