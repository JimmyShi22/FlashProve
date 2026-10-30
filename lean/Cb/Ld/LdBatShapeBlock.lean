-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdBatShapeBlock.lean: the reduction without messages that brings a code into another shape
(Cb/Ld/LdBatShape.lean), in the form in which the steps of a proximity test are composed: a block
between two joints of a tower (Cb/Ld/LdTower.lean).

One definition, one statement, its proof.

Main names:
  `ldShapeBlock ρ s e`: the reshape as a block.
  `Spec.ldShape_block`: for non-empty P, under the laws of ρ it is `OK t t` (`LdBlock.OK`,
    Cb/Ld/LdTower.lean), for every t: what follows needs at most t long positions of the new word,
    and so many of the old word are needed.

Limits: this file says nothing beyond Cb/Ld/LdBatShape.lean's `Spec.ldShape_piece`: this is that
statement in the letters of the tower.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdBatShapeProofs
import Cb.Ld.LdTower

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop IOR

/-- The reshape as a block. -/
def ldShapeBlock {E P : Type} [Field E] [Fintype E] [Fintype P] [Nonempty P] {C C' : LdCode E P}
    (ρ : Reshape C C') {St : Type} (s : Slf E St C.J) (e : ℕ) :
    LdBlock (⟨P, C, St, s, e⟩ : LdJoint E) ⟨P, C', St, ρ.sl s, e⟩ :=
  ⟨IOR.pure (fun x : E × St => some x) ρ.map,
    Honest.pure (fun x : E × St => some x) ρ.map fun a => (a.1, ρ.up a.2),
    fun _ _ w => ρ.dn w,
    Nums.pure Unit (fun x : E × St => some x) ρ.map⟩

namespace Spec

def ldShape_block : Prop :=
  ∀ (E P : Type) [Field E] [Fintype E] [Fintype P] [Nonempty P] (C C' : LdCode E P)
      (ρ : Reshape C C') (St : Type) (s : Slf E St C.J) (e t : ℕ),
    ρ.Laws → (ldShapeBlock ρ s e).OK t t

end Spec

theorem ldShape_block : Spec.ldShape_block := fun E P _ _ _ _ C C' ρ St s e t hL =>
  ldShape_piece E P C C' ρ e St s (fun S => S.card ≤ t) hL

end Cb
