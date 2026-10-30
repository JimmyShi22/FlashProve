-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdWfToyMasks.lean: at the toy of weights-formedness: the mask entries cut into blocks, and
where the named entries are among the entries of the family sent.


Definitions and proofs. No parameter of a protocol.
Data: Cb/Ld/LdWfToy.lean; first conditions: Cb/Ld/LdWfToyProofs.lean.
The preamble of weights-formedness (`LdWfP.Blk.wf`, Cb/Ld/LdWf.lean) is the sub-protocol for the
claim that the encoded index decodes to a message that holds an index.














The places. The mask-only member's 39 entries are cut into three blocks: the lookup's 35,
the batching's 3, the idle one (Cb/Ld/LdSendToyFamLay.lean).


Main names:
  `WfToy.Kb`: the mask entries cut into the three blocks (`TB`: `lk`, `bt`, `id`).
  `WfToy.nAt`: where the named entries are among the entries of the family sent (`nAt_inj`: it is
    injective; `noPad`: `F.NoPad` at each of them).
  `mkAt_inj`: `mkAt` is injective.








Limits: this file says nothing on the size of errors: with 39 entries under one sample over 101
elements the sending's error is not below its number of seeds. No level of security: no statement
of this file evaluates an error or a budget.








Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdWfToyProofs

set_option autoImplicit false

namespace Cb

variable [WfToy.ToyModel]
namespace WfToy
open Iop Prob Hiop Blocks Cb.Ood IOR LdToy LdToy7 Cb.LdLkp Cb.Lkp

omit [WfToy.ToyModel] in
theorem valid_congr {n T w W : ℕ} {ky ky' t : ℕ → K} {M : ℕ → ℕ → K}
    (h : ∀ b, b < 2 ^ n → ky b = ky' b) (hv : Valid n T w W ky t M) : Valid n T w W ky' t M := by
  refine ⟨hv.1, hv.2.1, fun x => ?_⟩
  rw [hv.2.2 x]
  congr 1
  ext b
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨fun e => ⟨e.1, (h b e.1).symm.trans e.2⟩, fun e => ⟨e.1, (h b e.1).trans e.2⟩⟩

noncomputable section

/-- the three blocks of mask entries -/
inductive TB
  | lk
  | bt
  | id
  deriving DecidableEq, Fintype

def TB.I : TB → Type
  | .lk => LkpToy.Mk
  | .bt => WBt
  | .id => Unit

instance : ∀ b, Fintype (TB.I b)
  | .lk => inferInstanceAs (Fintype LkpToy.Mk)
  | .bt => inferInstanceAs (Fintype WBt)
  | .id => inferInstanceAs (Fintype Unit)

/-- The mask entries cut into blocks. -/
def Kb : F.Blk where
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

/-- Where the named entries are among the entries of the family sent. -/
def nAt : Nm → F.sig.Ent :=
  Sum.elim (fun c => ⟨false, F.at₁ c⟩) fun i => ⟨true, F.ν₂.symm (Sum.inl i)⟩

def bkOf : Option (Fin (0 + 1)) → TB
  | some _ => .lk
  | none => .bt

end

/-! ### The condition on places -/

omit [WfToy.ToyModel] in
theorem nAt_inj : Function.Injective nAt := by
  rintro (a | a) (b | b) h
  · have h' : (⟨false, F.at₁ a⟩ : F.sig.Ent) = ⟨false, F.at₁ b⟩ := h
    exact congrArg Sum.inl (Sum.inl_injective (F.ν₁.symm.injective (eq_of_heq (Sigma.mk.inj h').2)))
  · exact absurd (show false = true from congrArg Sigma.fst h) (by decide)
  · exact absurd (show true = false from congrArg Sigma.fst h) (by decide)
  · have h' : (⟨true, F.ν₂.symm (Sum.inl a)⟩ : F.sig.Ent) = ⟨true, F.ν₂.symm (Sum.inl b)⟩ := h
    exact congrArg Sum.inr (Sum.inl_injective (F.ν₂.symm.injective (eq_of_heq (Sigma.mk.inj h').2)))

omit [WfToy.ToyModel] in
theorem noPad (n : Nm) : F.NoPad (nAt n) := by
  cases n with
  | inl c =>
    show (F.ν₁ (F.ν₁.symm (Sum.inl c))).isLeft = true
    rw [Equiv.apply_symm_apply]
    rfl
  | inr i =>
    show (F.ν₂ (F.ν₂.symm (Sum.inl i))).isLeft = true
    rw [Equiv.apply_symm_apply]
    rfl

omit [WfToy.ToyModel] in
theorem mkAt_inj : Function.Injective mkAt := fun _ _ h => Sum.inl_injective (Sum.inr_injective h)

end WfToy

end Cb
