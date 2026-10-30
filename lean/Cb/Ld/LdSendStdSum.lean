-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdSendStdSum.lean: two families of oracle messages in one prover message: the sum of two
layouts is a layout, which meets its conditions (`Sig.StdL.OK`, Cb/Ld/LdSendStdL.lean) if both do.

This file is book-keeping for an honest prover's messages: two families of oracle messages go in one
prover message, and what is recorded of each (how the coordinates of each message are used; its
encoder) is put together, member by member.

Definitions, statement and proof.
Cb/Ld/LdSendStdL.lean makes the standard sender of a family N from a layout `Y : N.StdL F` of its
messages (data, free entries, pads; the format's encoder). One prover message may hold oracle
messages under different codes, at different sets of positions, in different formats.

Main names:
  `Y₁.sum Y₂ : (S.sum N).StdL F`: member by member.
  `sumDat Y₁ Y₂ dat₁ dat₂`: the data map of the whole from those of the parts.
  `Spec.stdL_sum`: `Y₁.OK t₁`, `Y₂.OK t₂` ⇒ `(Y₁.sum Y₂).OK (Sum.elim t₁ t₂)`; the places of data
    and of free entries are the parts' (by definition); an entry of the whole is no pad iff it is
    none in its part.
So, under `Y₁.OK t₁` and `Y₂.OK t₂`, the standard sender of the whole (all coins independent) has
all that `Cb.stdL_all` gives, and the theorems on masks (Cb/Ld/LdSendStdOwn.lean,
Cb/Ld/LdSendStdBlocks.lean, Cb/Ld/LdSendStdVis.lean, Cb/Req1/LdReqStdFresh.lean) apply to it
unchanged.

Limits: this file says nothing on two parts with different pads' fields: both layouts stand over one
F here. It says nothing on seeds. They may be drawn for the whole in any way: the theorems named
above hold at every joint seed.
Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdSendStdOwn
import Cb.Ld.LdSigSum

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

section
variable {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] {S N : Sig E}

/-- The sum of two layouts. -/
@[reducible] def Sig.StdL.sum (Y₁ : S.StdL F) (Y₂ : N.StdL F) : (S.sum N).StdL F where
  Dt := Sum.elim Y₁.Dt Y₂.Dt
  finDt := fun a => match a with
    | .inl a => Y₁.finDt a
    | .inr a => Y₂.finDt a
  Fr := Sum.elim Y₁.Fr Y₂.Fr
  finFr := fun a => match a with
    | .inl a => Y₁.finFr a
    | .inr a => Y₂.finFr a
  Pd := Sum.elim Y₁.Pd Y₂.Pd
  finPd := fun a => match a with
    | .inl a => Y₁.finPd a
    | .inr a => Y₂.finPd a
  ν := fun a => match a with
    | .inl a => Y₁.ν a
    | .inr a => Y₂.ν a
  En := fun a => match a with
    | .inl a => Y₁.En a
    | .inr a => Y₂.En a
  upM := fun a => match a with
    | .inl a => Y₁.upM a
    | .inr a => Y₂.upM a
  upR := fun a => match a with
    | .inl a => Y₁.upR a
    | .inr a => Y₂.upR a
  msgOf := fun a => match a with
    | .inl a => Y₁.msgOf a
    | .inr a => Y₂.msgOf a

/-- the data map of the whole -/
def sumDat {W : Type} (Y₁ : S.StdL F) (Y₂ : N.StdL F) (dat₁ : W → ∀ a, Y₁.Dt a → E)
    (dat₂ : W → ∀ a, Y₂.Dt a → E) (w : W) : ∀ a, (Y₁.sum Y₂).Dt a → E
  | .inl a => dat₁ w a
  | .inr a => dat₂ w a

end

def Spec.stdL_sum : Prop :=
  ∀ (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] (S N : Sig E)
      (Y₁ : S.StdL F) (Y₂ : N.StdL F) (t₁ : S.O → ℕ) (t₂ : N.O → ℕ),
    Y₁.OK t₁ → Y₂.OK t₂ →
    (Y₁.sum Y₂).OK (Sum.elim t₁ t₂) ∧
    (∀ a i, (Y₁.sum Y₂).atD (.inl a) i = Y₁.atD a i) ∧
    (∀ a i, (Y₁.sum Y₂).atD (.inr a) i = Y₂.atD a i) ∧
    (∀ a i, (Y₁.sum Y₂).atF (.inl a) i = Y₁.atF a i) ∧
    (∀ a i, (Y₁.sum Y₂).atF (.inr a) i = Y₂.atF a i) ∧
    (∀ n : S.Ent, (Y₁.sum Y₂).NoPad ⟨.inl n.1, n.2⟩ ↔ Y₁.NoPad n) ∧
    ∀ n : N.Ent, (Y₁.sum Y₂).NoPad ⟨.inr n.1, n.2⟩ ↔ Y₂.NoPad n

theorem stdL_sum : Spec.stdL_sum := by
  intro F E _ _ _ _ _ S N Y₁ Y₂ t₁ t₂ h₁ h₂
  refine ⟨⟨fun a => ?_, fun a => ?_, fun a => ?_, fun a => ?_⟩, fun _ _ => rfl, fun _ _ => rfl,
    fun _ _ => rfl, fun _ _ => rfl, fun _ => Iff.rfl, fun _ => Iff.rfl⟩
  · rcases a with a | a
    · exact h₁.enc a
    · exact h₂.enc a
  · rcases a with a | a
    · exact h₁.lay a
    · exact h₂.lay a
  · rcases a with a | a
    · exact h₁.priv a
    · exact h₂.priv a
  · rcases a with a | a
    · exact h₁.hides a
    · exact h₂.hides a

end Cb
