-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdSendToyFamLay.lean: the standard family (a named member and a mask-only member): its mask
entries cut into blocks, one layout for all coming blocks.

Definitions, one statement (`Cb.Spec.stdFamL_all`) and proofs.

This file is book-keeping for those coins of an honest prover that go into its messages
(`Sig.Sender.Mk`). In the example of Cb/Ld/LdSendToyFam.lean the masks in the second message are
divided among several later reductions of a chain, and the conditions that
Cb/Ld/LdSendFreshMany.lean puts on such a division are proved from `F.Hyp`.

Cb/Ld/LdSendToyFam.lean has a family of two oracle messages (the first holds a vector and a pad, the
second mask entries F.Im and a pad) with its honest sender, and shows, under `F.Hyp`, all conditions
of a sending that `Spec.stdFam_all` names, with all mask entries as the own masks of one coming
block.
A protocol uses these mask entries in several later blocks.

Main names:
  `F.Blk`: the data: the blocks Bk; for each block its index set I b; a bijection σ from all pairs
    (b, i) to the mask entries F.Im: every mask entry belongs to exactly one block (entries that
    nobody uses: a block of their own).
  `K.lay Wr r0`: the layout: the masks of b are the vectors I b → E; no further coins; pads: both
    pads.
  `Spec.stdFamL_all`: from `F.Hyp`:
    (pad) the one condition on the pads (`L.PadLaw Sd`: the head of Cb/Ld/LdSendFreshMany.lean), at
      every way of drawing seeds;
    (inj), (inRd) a block's places (`K.at'`) are different entries and no pads;
    places of different blocks differ;
    (own) the entry at place i of b is the value i of b's masks;
    (off) an entry that is no pad, off b's places, reads neither b's masks nor the pads.
So, under `F.Hyp`, the conditions pad, inj, inRd, own, off of Cb/Ld/LdWfMasks.lean (five of the
eight fields of `MaskLay.OK`; its rd, com, blind are not shown here) hold for this sender at Rd :=
F.NoPad.

Limits: this file says nothing on the blocks that use the masks.
Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdSendToyFam
import Cb.Ld.LdSendFreshMany
import Cb.Ld.LdBatSig
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

namespace StdFam
variable {E : Type} [Field E] [Fintype E] (F : StdFam E)

/-- The mask entries cut into blocks: the data. -/
structure Blk where
  Bk : Type
  [finBk : Fintype Bk]
  [decBk : DecidableEq Bk]
  I  : Bk → Type
  [finI : ∀ b, Fintype (I b)]
  σ  : (Σ b, I b) ≃ F.Im

attribute [instance] Blk.finBk Blk.decBk Blk.finI

/-- the entry is no pad -/
def NoPad : F.sig.Ent → Prop
  | ⟨false, j⟩ => (F.ν₁ j).isLeft = true
  | ⟨true, j⟩ => (F.ν₂ j).isLeft = true

variable {F} (K : F.Blk)

/-- all mask entries, as vectors by block, and back -/
def Blk.toB : (F.Im → E) ≃ ∀ b, K.I b → E where
  toFun M b i := M (K.σ ⟨b, i⟩)
  invFun ms x := ms (K.σ.symm x).1 (K.σ.symm x).2
  left_inv M := funext fun x => by
    show M (K.σ ⟨(K.σ.symm x).1, (K.σ.symm x).2⟩) = M x
    rw [Sigma.eta, Equiv.apply_symm_apply]
  right_inv ms := funext fun b => funext fun i => by
    show ms (K.σ.symm (K.σ ⟨b, i⟩)).1 (K.σ.symm (K.σ ⟨b, i⟩)).2 = ms b i
    rw [Equiv.symm_apply_apply]

/-- the place of the entry i of block b -/
def Blk.at' (b : K.Bk) (i : K.I b) : F.sig.Ent := ⟨true, F.ν₂.symm (Sum.inl (K.σ ⟨b, i⟩))⟩

variable (Wr : Type) (r0 : Wr)

open Classical in
/-- The layout. -/
@[reducible] def Blk.lay : (F.snd Wr r0).Layout where
  Bk := K.Bk
  Mk := fun b => K.I b → E
  F0 := Unit
  Pd := (F.Pd₁ → E) × (F.Pd₂ → E)
  κ :=
    (F.own Wr r0).κ.trans (Equiv.prodCongr (Equiv.prodCongr K.toB (Equiv.refl Unit)) (Equiv.refl _))

end StdFam

namespace Spec

/-- All conditions on the layout (those that Cb/Ld/LdSendFreshMany.lean puts on it:
`Spec.layout_laws_entries`). -/
def stdFamL_all : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (F : StdFam E) (K : F.Blk)
      (L₁ L₂ t₁ t₂ : ℕ) (Wr : Type) (r0 : Wr),
    F.Hyp L₁ L₂ t₁ t₂ →
    (∀ Sd : F.sig.Seeds, (K.lay Wr r0).PadLaw Sd) ∧
    (∀ b, Function.Injective (K.at' b)) ∧
    (∀ b i, F.NoPad (K.at' b i)) ∧
    (∀ b b' i i', K.at' b i = K.at' b' i' → b = b') ∧
    (∀ b w ms f η i,
      F.sig.ents ((F.snd Wr r0).upM ((F.snd Wr r0).put w ((K.lay Wr r0).mk' ms f η))) (K.at' b i) =
        ms b i) ∧
    (∀ b w ms ms' f η η' n, (K.lay Wr r0).oth b ms = (K.lay Wr r0).oth b ms' →
      F.NoPad n → (∀ i, n ≠ K.at' b i) →
      F.sig.ents ((F.snd Wr r0).upM ((F.snd Wr r0).put w ((K.lay Wr r0).mk' ms f η))) n =
        F.sig.ents ((F.snd Wr r0).upM ((F.snd Wr r0).put w ((K.lay Wr r0).mk' ms' f η'))) n)

end Spec

namespace StdFam
variable {E : Type} [Field E] [Fintype E] {F : StdFam E} (K : F.Blk) (Wr : Type) (r0 : Wr)

/-- the coins of the layout are those of the one split, at all mask entries together -/
theorem Blk.mk_eq (ms : ∀ b, K.I b → E) (f : Unit) (η : (F.Pd₁ → E) × (F.Pd₂ → E)) :
    (K.lay Wr r0).mk' ms f η = (F.own Wr r0).mk' (K.toB.symm ms) () η := rfl

/-- a mask entry of the message sent -/
theorem Blk.ent_mask (w : (F.Ix → E) × Wr) (ms : ∀ b, K.I b → E) (f : Unit)
    (η : (F.Pd₁ → E) × (F.Pd₂ → E)) (x : F.Im) :
    F.sig.ents ((F.snd Wr r0).upM ((F.snd Wr r0).put w ((K.lay Wr r0).mk' ms f η)))
        ⟨true, F.ν₂.symm (Sum.inl x)⟩ =
      K.toB.symm ms x := by
  show withPad (F := E) (K.toB.symm ms) η.2 (F.ν₂ (F.ν₂.symm (Sum.inl x))) = _
  rw [Equiv.apply_symm_apply]
  rfl

end StdFam

theorem stdFamL_all : Spec.stdFamL_all := by
  intro E _ _ F K L₁ L₂ t₁ t₂ Wr r0 h
  obtain ⟨-, -, -, -, -, -, -, -, hU, -, -⟩ := stdFam_all E F L₁ L₂ t₁ t₂ Wr r0 h
  have hat : ∀ b b' i i',
      K.at' b i = K.at' b' i' → (⟨b, i⟩ : Σ b, K.I b) = ⟨b', i'⟩ := fun b b' i i' e => by
    have e1 : F.ν₂.symm (Sum.inl (K.σ ⟨b, i⟩)) = F.ν₂.symm (Sum.inl (K.σ ⟨b', i'⟩)) :=
      eq_of_heq (Sigma.mk.inj e).2
    exact K.σ.injective (Sum.inl.inj (F.ν₂.symm.injective e1))
  refine ⟨fun Sd s w w' ms ms' f f' => ?_,
    fun b i i' e => eq_of_heq (Sigma.mk.inj (hat b b i i' e)).2,
    fun b i => ?_,
    fun b b' i i' e => (Sigma.mk.inj (hat b b' i i' e)).1,
    fun b w ms f η i => ?_,
    ?_⟩
  · exact (hU Sd).pad s w w' (K.toB.symm ms) (K.toB.symm ms') () ()
  · show (F.ν₂ (F.ν₂.symm (Sum.inl (K.σ ⟨b, i⟩)))).isLeft = true
    rw [Equiv.apply_symm_apply]
    rfl
  · rw [show K.at' b i = ⟨true, F.ν₂.symm (Sum.inl (K.σ ⟨b, i⟩))⟩ from rfl,
      K.ent_mask Wr r0 w ms f η]
    exact congrFun (congrFun (K.toB.apply_symm_apply ms) b) i
  · intro b w ms ms' f η η' n ho hn hoff
    obtain ⟨a, j⟩ := n
    cases a with
    | false =>
        have hj : (F.ν₁ j).isLeft = true := hn
        show withPad (F := E) w.1 η.1 (F.ν₁ j) = withPad (F := E) w.1 η'.1 (F.ν₁ j)
        cases hc : F.ν₁ j with
        | inl c => rfl
        | inr p =>
            rw [hc] at hj
            cases hj
    | true =>
        have hj : (F.ν₂ j).isLeft = true := hn
        cases hc : F.ν₂ j with
        | inl x =>
            have ej : j = F.ν₂.symm (Sum.inl x) := by rw [← hc, Equiv.symm_apply_apply]
            subst ej
            rw [K.ent_mask Wr r0 w ms f η, K.ent_mask Wr r0 w ms' f η']
            show ms (K.σ.symm x).1 (K.σ.symm x).2 = ms' (K.σ.symm x).1 (K.σ.symm x).2
            have hb : (K.σ.symm x).1 ≠ b := by
              intro e
              subst e
              refine hoff (K.σ.symm x).2 ?_
              show (⟨true, F.ν₂.symm (Sum.inl x)⟩ : F.sig.Ent) =
                ⟨true, F.ν₂.symm (Sum.inl (K.σ ⟨(K.σ.symm x).1, (K.σ.symm x).2⟩))⟩
              rw [Sigma.eta, Equiv.apply_symm_apply]
            exact congrFun (congrFun ho ⟨(K.σ.symm x).1, hb⟩) (K.σ.symm x).2
        | inr p =>
            rw [hc] at hj
            cases hj

end Cb
