-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/RuleKitMoreProofs.lean: the proofs of the statements of
Johnson/Desc/Sound/RuleKitMore.lean. Theorems and the lemmas that they need.

Limits: those of that file.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.RuleKitMore
import Johnson.Desc.Sound.RuleKitProofs
import Johnson.Desc.Sound.RuleKitShareProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Sound
open TypedOracleCompiler.Run.PQ (RD)
open _root_.Run (Vals DVal toU toU3 toU_toNat bsRound EV)
open scoped ENNReal

theorem kitShareCard : KitShareCard := by
  intro f d h
  have e : Fintype.card (_root_.Iop.GChal d.entry.work ((_root_.Run.ckP f).Ch d.entry d.kind)) =
      2 ^ d.entry.work *
        Fintype.card (Fin (bsRound f d.entry d.kind).b → _root_.Iop.Dig 256) := by
    rw [_root_.Iop.GChal.card_eq, Nat.mul_comm]
    rfl
  rw [e]
  exact kitShare f d h

theorem kapIs : KapIs := rfl

theorem below_toU3 (f : Fmt.Fld) (a : EV f) :
    (toU3 a).1.toNat < f.p ∧ (toU3 a).2.1.toNat < f.p ∧ (toU3 a).2.2.toNat < f.p := by
  refine ⟨?_, ?_, ?_⟩
  · show (toU a.1).toNat < f.p
    rw [toU_toNat]
    exact a.1.isLt
  · show (toU a.2.1).toNat < f.p
    rw [toU_toNat]
    exact a.2.1.isLt
  · show (toU a.2.2).toNat < f.p
    rw [toU_toNat]
    exact a.2.2.isLt

theorem elsOf_below (f : Fmt.Fld) (ds : List Fmt.Draw) :
    ∀ (v : Vals f ds) (x : Fmt.Ext), x ∈ elsOf f ds v →
      x.1.toNat < f.p ∧ x.2.1.toNat < f.p ∧ x.2.2.toNat < f.p := by
  induction ds with
  | nil =>
    intro v x hx
    have hx' : x ∈ ([] : List Fmt.Ext) := hx
    exact absurd hx' List.not_mem_nil
  | cons d ds ih =>
    intro v x hx
    cases d with
    | elem =>
      have hx' : x ∈ toU3 (f := f) v.1 :: elsOf f ds v.2 := hx
      rcases List.mem_cons.1 hx' with e | h
      · rw [e]
        exact below_toU3 f v.1
      · exact ih v.2 x h
    | elemNZ =>
      have hx' : x ∈ toU3 (f := f) v.1.1 :: elsOf f ds v.2 := hx
      rcases List.mem_cons.1 hx' with e | h
      · rw [e]
        exact below_toU3 f v.1.1
      · exact ih v.2 x h
    | pos k => exact ih v.2 x hx
    | trits m => exact ih v.2 x hx
    | sealed => exact ih v.2 x hx

theorem kitBelow : KitBelow := fun f d c x hx =>
  elsOf_below f (Fmt.dsOf d.entry d.kind)
    ((bsRound f d.entry d.kind).φ (_root_.Iop.GChal.old (b := d.entry.work) c)) x hx

end VerifiableInference.Desc.Sound
