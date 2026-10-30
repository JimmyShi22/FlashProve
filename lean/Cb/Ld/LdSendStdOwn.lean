-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdSendStdOwn.lean: under the hypotheses of its statement, at a standard sender, any set of
free entries are masks of a coming block: the conditions on the sender's coins are a theorem.

This file is book-keeping for those coins of an honest prover that go into its messages
(`Sig.Sender.Mk`). A layout marks coordinates of the prover's messages as free, for coins; this file
takes any finite set of them as the masks that one later reduction of a chain will use, and proves,
under `Y.OK t` (`Sig.StdL.OK`, Cb/Ld/LdSendStdL.lean), the three conditions on the coins that
Cb/Ld/LdSendFresh.lean asks.

Definitions, one statement and its proof. Generic: any family, any format.
Cb/Ld/LdSendFresh.lean states (proved in Cb/Ld/LdSendFreshProofs.lean), under the hypotheses of
`Spec.ldSendFam_fresh`, that a sending leaves the own masks of a coming block fresh, from a split U
of the sender's coins ((own masks × other coins) × pads) with three conditions (`U.Laws`).
Cb/Ld/LdSendStdL.lean has the standard sender on a layout Y of the members' messages (data, free
entries, pad) and, for every split of the free entries into blocks, under `Y.OK t`, the law of the
pads. Here are the split and the three conditions, for the case of `Spec.layout_laws_entries`
(Cb/Ld/LdSendFreshMany.lean).

Main names:
  `pl : I → Σ a, Y.Fr a`: the places of the coming block's masks: any injective family of free
    entries, in whichever members.
  `Y.ownAt pl hpl dat rest w0`: the split of the coins: own masks: the entries at pl (a vector
    I → E); other coins: all other free entries; pads: all pads.
  `Y.rdNoPad`, `Y.putAt pl`: the reading: all entries of all messages that are no pads (pads read as
    0), and the whole further witness that is handed on; the overwriting: the entries at pl.
  `Spec.stdL_own`: `Y.OK t` ⇒ `(Y.ownAt ..).Laws Sd Y.rdNoPad (Y.putAt pl)`, at every way Sd to draw
    the seeds.
So, under `Y.OK t`, Cb/Ld/LdSendFresh.lean's `Spec.ldSendFam_fresh` applies with no hypothesis on
the sender. A coarser reading is had by the rules on coarser readings (`Spec.fresh_conseq`,
Ior/KnowCollRulesMask.lean, under the hypotheses of its statement).

Limits: the reading forgets the encoding randomness of the whole family (Cb/Ld/LdSendFreshVis.lean
has the wider theorem; its conditions are not derived here).
Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdSendStdL
import Cb.Ld.LdBatSig
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

namespace Sig.StdL
variable {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]
  {N : Sig E} (Y : N.StdL F)

/-- a free entry, as an entry of the family -/
def entF (x : Σ a, Y.Fr a) : N.Ent := ⟨x.1, Y.atF x.1 x.2⟩

theorem entF_injective : Function.Injective Y.entF := by
  rintro ⟨a, u⟩ ⟨b, v⟩ h
  obtain ⟨rfl, h2⟩ := Sigma.mk.inj_iff.1 (show (⟨a, Y.atF a u⟩ : N.Ent) = ⟨b, Y.atF b v⟩ from h)
  exact congrArg (Sigma.mk a) (Sum.inr.inj (Sum.inl.inj ((Y.ν a).symm.injective (eq_of_heq h2))))

/-- no pad entry -/
def NoPad (n : N.Ent) : Prop := ∃ x, n.2 = (Y.ν n.1).symm (Sum.inl x)

variable {I : Type} (pl : I → Σ a, Y.Fr a) (hpl : Function.Injective pl)

open Classical in
/-- The free entries as (those at pl; all others). -/
def splitAt :
    (∀ a, Y.Fr a → E) ≃ (Unit → I → E) × ({x : Σ a, Y.Fr a // ∀ i, pl i ≠ x} → E) where
  toFun φ := (fun _ i => φ (pl i).1 (pl i).2, fun x => φ x.1.1 x.1.2)
  invFun z := fun a j =>
    if h : ∃ i, pl i = ⟨a, j⟩ then z.1 () h.choose else z.2 ⟨⟨a, j⟩, fun i hi => h ⟨i, hi⟩⟩
  left_inv φ := by
    funext a j
    by_cases h : ∃ i, pl i = ⟨a, j⟩
    · simp only [dif_pos h]
      rw [h.choose_spec]
    · simp only [dif_neg h]
  right_inv z := by
    refine Prod.ext (funext fun u => funext fun i => ?_) (funext fun x => ?_)
    · have h : ∃ i', pl i' = ⟨(pl i).1, (pl i).2⟩ := ⟨i, rfl⟩
      simp only [dif_pos h]
      exact congrArg (z.1 u) (hpl h.choose_spec)
    · have h : ¬ ∃ i, pl i = ⟨x.1.1, x.1.2⟩ := fun ⟨i, hi⟩ => x.2 i hi
      simp only [dif_neg h]

theorem splitAt_symm_at (z : (Unit → I → E) × ({x : Σ a, Y.Fr a // ∀ i, pl i ≠ x} → E)) (i : I) :
    (Y.splitAt pl hpl).symm z (pl i).1 (pl i).2 = z.1 () i :=
  congrFun (congrFun (congrArg Prod.fst ((Y.splitAt pl hpl).apply_symm_apply z)) ()) i

theorem splitAt_symm_off (z : (Unit → I → E) × ({x : Σ a, Y.Fr a // ∀ i, pl i ≠ x} → E))
    (x : Σ a, Y.Fr a) (hx : ∀ i, pl i ≠ x) :
    (Y.splitAt pl hpl).symm z x.1 x.2 = z.2 ⟨x, hx⟩ :=
  congrFun (congrArg Prod.snd ((Y.splitAt pl hpl).apply_symm_apply z)) ⟨x, hx⟩

variable {W W' : Type} (dat : W → ∀ a, Y.Dt a → E) (rest : W → W') (w0 : W) [Fintype I]

open Classical in
/-- the layout of the coins with one block -/
@[reducible] def layAt : (Y.snd dat rest w0).Layout :=
  Y.layout dat rest w0 Unit (fun _ => I → E)
    ({x : Σ a, Y.Fr a // ∀ i, pl i ≠ x} → E) (Y.splitAt pl hpl)

/-- The split of the sender's coins for a coming block with masks at pl. -/
@[reducible] def ownAt : (Y.snd dat rest w0).Own (I → E) :=
  (Y.layAt pl hpl dat rest w0).own ()

/-- The reading: all entries that are no pads, and the whole further witness handed on. -/
def rdNoPad (m : N.Msg) (w' : W') : (N.Ent → E) × W' := (cutTo Y.NoPad (N.ents m), w')

/-- the entries at pl overwritten -/
def putAt (M : I → E) (k : (N.Ent → E) × W') : (N.Ent → E) × W' :=
  (Function.extend (fun i => Y.entF (pl i)) M k.1, k.2)

end Sig.StdL

/-- The conditions on the sender's coins. -/
def Spec.stdL_own : Prop :=
  ∀ (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] (N : Sig E)
      (Y : N.StdL F) (t : N.O → ℕ) (W W' : Type) (dat : W → ∀ a, Y.Dt a → E)
      (rest : W → W') (w0 : W) (I : Type) [Fintype I] (pl : I → Σ a, Y.Fr a)
      (hpl : Function.Injective pl) (Sd : N.Seeds),
    Y.OK t → (Y.ownAt pl hpl dat rest w0).Laws Sd Y.rdNoPad (Y.putAt pl)

theorem stdL_own : Spec.stdL_own := by
  classical
  intro F E _ _ _ _ _ N Y t W W' dat rest w0 I _ pl hpl Sd h
  obtain ⟨-, aD, aF, -, -, -, -⟩ := stdL_all F E N Y t W W' dat rest w0 h
  have hinj : Function.Injective fun i => Y.entF (pl i) := Y.entF_injective.comp hpl
  have hoffL : ∀ (w : W) (ms ms' : ∀ b, (Y.layAt pl hpl dat rest w0).Mk b)
          (f : (Y.layAt pl hpl dat rest w0).F0)
          (η η' : (Y.layAt pl hpl dat rest w0).Pd) (n : N.Ent),
        (Y.layAt pl hpl dat rest w0).oth () ms = (Y.layAt pl hpl dat rest w0).oth () ms' →
        Y.NoPad n → (∀ i, n ≠ Y.entF (pl i)) →
        N.ents ((Y.snd dat rest w0).upM
              ((Y.snd dat rest w0).put w ((Y.layAt pl hpl dat rest w0).mk' ms f η))) n =
          N.ents ((Y.snd dat rest w0).upM
              ((Y.snd dat rest w0).put w ((Y.layAt pl hpl dat rest w0).mk' ms' f η'))) n := by
    rintro w ms ms' f η η' ⟨a, j⟩ - ⟨x, hx⟩ hoff
    have hx' : j = (Y.ν a).symm (Sum.inl x) := hx
    show (Y.snd dat rest w0).upM
        ((Y.snd dat rest w0).put w ((Y.layAt pl hpl dat rest w0).mk' ms f η)) a j =
      (Y.snd dat rest w0).upM
        ((Y.snd dat rest w0).put w ((Y.layAt pl hpl dat rest w0).mk' ms' f η')) a j
    rw [hx']
    rcases x with d | u
    · exact (aD w _ a d).trans (aD w _ a d).symm
    · have hu : ∀ i, pl i ≠ ⟨a, u⟩ := fun i hi => hoff i (by
        rw [hx', hi]
        rfl)
      exact ((aF w _ a u).trans (Y.splitAt_symm_off pl hpl (ms, f) ⟨a, u⟩ hu)).trans
        ((aF w _ a u).trans (Y.splitAt_symm_off pl hpl (ms', f) ⟨a, u⟩ hu)).symm
  have l1 := layout_laws_entries (E := E) N W W' (Y.snd dat rest w0) (Y.layAt pl hpl dat rest w0) Sd
    () N.Ent I (fun m _ => N.ents m) Y.NoPad (fun i => Y.entF (pl i)) (fun M i => M i)
    (stdL_padLaw F E N Y t W W' dat rest w0 Unit (fun _ => I → E) _ (Y.splitAt pl hpl) Sd h) hinj
    (fun i => ⟨_, rfl⟩)
    (fun w ms f η i => (aF w _ (pl i).1 (pl i).2).trans (Y.splitAt_symm_at pl hpl (ms, f) i)) hoffL
  exact own_laws_keep (E := E) N W W' (Y.snd dat rest w0) (I → E)
    (Y.ownAt pl hpl dat rest w0) Sd _ _ _ l1

end Cb
