-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/GlVal/GlToyWfMasks.lean: book-keeping for the small test instance of the preamble of
weights-formedness in Cb/GlVal/GlToyWf.lean: where among the entries of the two oracle messages the
named entries stand, and how the second message's mask entries are divided into the lookup's, the
batching's and an idle one.

Definitions and proofs. A guard against empty theorems; no parameter of a protocol. The analogue of
the part on places of Cb/Ld/LdWfToyMasks.lean.
The named entries (`LdWfP.N`, Cb/Ld/LdWf.lean; here `Nm`) are the entries of the messages that rows
and mask forms may read; `mkAt`, `btAt`, `idle` (Cb/GlVal/GlToyWf.lean) name the lookup's, the
batching's and the idle one among them (the idle one: the levels that are never played name it:
`Kl`).

Main names:
  `TB`, `TB.I`, `Kb`: the mask-only member's 39 entries cut into three blocks: the lookup's 35, the
    batching's 3, the idle one (`StdFam.Blk`, Cb/Ld/LdSendToyFamLay.lean).
  `bkOf`: which block of the layout a masked block is (the one lookup; the batching).
  `nAt_inj`, `entAt`, `noPad`, `mkAt_inj`: the named entries are different entries of the messages,
    none is a pad.
  `famHyp`, `lks`: the family's record (`Fm.Hyp 1 1 2 2`, from Cb/GlVal/GlToyFam.lean); the lookup's
    conditions on numbers and public supports (`Kl.OK p`; `LdWfP.Lks.OK`, Cb/Ld/LdWfBlocks.lean).

Notation: `Fm.Hyp L₁ L₂ t₁ t₂` (`StdFam.Hyp`, Cb/Ld/LdSendToyFam.lean): what is asked of codes and
samples; its fields `list₁`, `list₂` take L₁, L₂; `zk₁`, `zk₂` take t₁, t₂.

But for two theorems nothing here reads the field F: all of it lives over E. The two: `lks`: its
clause `mult` speaks of every message U of the index, which is over F, through its keys; `famHyp`:
the family's codes are rows under `C8`, a code over F, read over E (`toyLd8`,
Cb/GlVal/GlToyBase.lean).
Terms: lean/GLOSSARY.md.
-/
import Cb.GlVal.GlToyWfProofs
import Cb.Ld.LdSendToyFamLay
import Cb.Ld.LdWfMasksAll

set_option autoImplicit false

namespace Cb.Gl
namespace Wf8
open Iop Prob Hiop Blocks Cb.Ood IOR Cb.LdLkp Cb.Lkp

noncomputable section

/-- The three blocks of mask entries. -/
inductive TB
  | lk
  | bt
  | id
  deriving DecidableEq, Fintype

def TB.I : TB → Type
  | .lk => LkpToyE.Mk E
  | .bt => WBt
  | .id => Unit

instance : ∀ b, Fintype (TB.I b)
  | .lk => inferInstanceAs (Fintype (LkpToyE.Mk E))
  | .bt => inferInstanceAs (Fintype WBt)
  | .id => inferInstanceAs (Fintype Unit)

/-- The mask entries cut into blocks. -/
def Kb : Fm.Blk where
  Bk := TB
  I := TB.I
  σ := { toFun := fun x => match x with
           | ⟨.lk, i⟩ => .inl i
           | ⟨.bt, i⟩ => .inr (.inl i)
           | ⟨.id, i⟩ => .inr (.inr i)
         invFun := fun y => match y with
           | .inl i => ⟨.lk, i⟩
           | .inr (.inl i) => ⟨.bt, i⟩
           | .inr (.inr i) => ⟨.id, i⟩
         left_inv := by rintro ⟨_ | _ | _, i⟩ <;> rfl
         right_inv := by rintro (i | i | i) <;> rfl }

/-- Where the named entries stand. -/
def nAt : Nm → Fm.sig.Ent :=
  Sum.elim (fun c => ⟨false, Fm.at₁ c⟩) fun i => ⟨true, Fm.ν₂.symm (Sum.inl i)⟩

def bkOf : Option (Fin (0 + 1)) → TB
  | some _ => .lk
  | none => .bt

end

theorem nAt_inj : Function.Injective nAt := by
  rintro (a | a) (b | b) h
  · have h' : (⟨false, Fm.at₁ a⟩ : Fm.sig.Ent) = ⟨false, Fm.at₁ b⟩ := h
    exact congrArg Sum.inl
      (Sum.inl_injective (Fm.ν₁.symm.injective (eq_of_heq (Sigma.mk.inj h').2)))
  · exact absurd (show false = true from congrArg Sigma.fst h) (by decide)
  · exact absurd (show true = false from congrArg Sigma.fst h) (by decide)
  · have h' : (⟨true, Fm.ν₂.symm (Sum.inl a)⟩ : Fm.sig.Ent) = ⟨true, Fm.ν₂.symm (Sum.inl b)⟩ := h
    exact congrArg Sum.inr
      (Sum.inl_injective (Fm.ν₂.symm.injective (eq_of_heq (Sigma.mk.inj h').2)))

theorem entAt : P.EntAt nAt where
  ent := fun _ n => by cases n <;> rfl
  inj := nAt_inj

theorem noPad (n : Nm) : Fm.NoPad (nAt n) := by
  cases n with
  | inl c =>
    show (Fm.ν₁ (Fm.ν₁.symm (Sum.inl c))).isLeft = true
    rw [Equiv.apply_symm_apply]
    rfl
  | inr i =>
    show (Fm.ν₂ (Fm.ν₂.symm (Sum.inl i))).isLeft = true
    rw [Equiv.apply_symm_apply]
    rfl

theorem mkAt_inj : Function.Injective mkAt := fun _ _ h => Sum.inl_injective (Sum.inr_injective h)

/-! ### The family; the lookup's conditions on numbers -/

theorem famHyp : Fm.Hyp 1 1 2 2 := (fam8_hyp Ix Im Ix Im _ _ oneHot_inj oneHot_inj).1

theorem valid_congr {n T w W : ℕ} {ky ky' t : ℕ → E} {M : ℕ → ℕ → E}
    (h : ∀ b, b < 2 ^ n → ky b = ky' b) (hv : Valid n T w W ky t M) : Valid n T w W ky' t M := by
  refine ⟨hv.1, hv.2.1, fun x => ?_⟩
  rw [hv.2.2 x]
  congr 1
  ext b
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨fun e => ⟨e.1, (h b e.1).symm.trans e.2⟩, fun e => ⟨e.1, (h b e.1).trans e.2⟩⟩

theorem lks : Kl.OK p where
  v := fun _ _ => rfl
  adm := fun f _ => adm f
  mult := fun f hf _ U _ h => valid_congr (fun b hb => ldWfB_key E Cf.conf P laws f hf U b hb) h
  rows := fun f _ => rows f
  supC := fun _ _ _ => ⟨_, rfl⟩
  supR := fun f _ _ => (places f).toR

end Wf8
end Cb.Gl
