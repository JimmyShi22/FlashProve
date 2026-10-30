-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Ior/LinkVMaskedRulesLocal.lean: the proof of `Iop.Spec.freshV_local` (Ior/LinkVMaskedRules.lean;
under the hypotheses of its statement: an IOR in every slot that is Fresh for one instance is
FreshV for the slots' masks).

In standard terms: the proof of one rule, which carries a property of an interactive oracle
reduction's honest side for one instance over to the same reduction run in every slot of a batch.

Main names:
  `freshV_local`: see its statement in Ior/LinkVMaskedRules.lean.

The notions: `HonestV.FreshV` (Ior/LinkVMasked.lean), `Honest.Fresh` (Ior/KnowCollRulesMask.lean),
`Honest.localV` (Ior/LinkV.lean); slot: the head of Ior/LinkV.lean.

How: the slots have coins and masks of their own and the shared part is silent. So both tuples
(`HonestV.seenV`, with and without `HonestV.overV`) are products over the slots of J
(Blocks/Batch/ProbPi.lean: `map_unif_shared`) beside a constant (what is read of the shared
witness, which is handed on); the property for one instance is used slot by slot; a slot that is
withheld shows the notice on both sides.

Limits: see Limits in the head of Ior/LinkVMaskedRules.lean.

Terms: lean/GLOSSARY.md.
-/
import Ior.LinkVMaskedRulesSeq

set_option autoImplicit false

namespace Iop
open Prob Prob.Indep
open scoped ENNReal
open IOR LinkVSeq MaskKit

open Classical in
theorem freshV_local : Spec.freshV_local := by
  intro X X' Ei Eo R Wi Wo W0 H Ri RiV bud N K0 Kc k0 kc Mk _ _ put hF hH hi w0 J as ha ρ Ts hbud
  -- what one slot contributes
  let F : J → H.Coin → Option (View R × X' × Kc) := fun j c =>
    if ρ.slot j.1 ∈ H.Bad then none else some (H.seen kc (as j).2.2 (as j).1 (ρ.slot j.1) (Ts j) c)
  let F' : J → H.Coin × Mk → Option (View R × X' × Kc) := fun j a =>
    (F j a.1).map fun t => (t.1, t.2.1, put a.2 t.2.2)
  have hseen : ∀ c : Unit × (Fin N → H.Coin),
      (H.localV W0).seenV k0 kc w0 J (fun j => ((as j).1, (as j).2.2)) ρ Ts c =
        (fun j => F j (c.2 j.1), k0 w0) := fun c => by
    refine Prod.ext (funext fun j => ?_) ?_
    · show ite (ρ.slot j.1 ∈ (H.localV W0).withheld) _ _ = ite (ρ.slot j.1 ∈ H.Bad) _ _
      by_cases hw : ρ.slot j.1 ∈ H.Bad
      · rw [if_pos hw, if_pos ((LinkV.local_withheld H W0 _).mpr hw)]
      · rw [if_neg hw, if_neg fun h => hw ((LinkV.local_withheld H W0 _).mp h)]
        dsimp only
        rw [LinkV.local_run]
        rfl
    · show k0 ((SStratR.silentR R.shape w0).res _) = k0 w0
      rw [SStratR.res_silentR]
  have hslot : ∀ j : J, (unif (H.Coin × Mk)).map (F' j) = (unif H.Coin).map (F j) := fun j => by
    by_cases hw : ρ.slot j.1 ∈ H.Bad
    · have e1 : F' j = fun _ => none := funext fun a => by
        show Option.map _ (ite (ρ.slot j.1 ∈ H.Bad) _ _) = none
        rw [if_pos hw]
        rfl
      have e2 : F j = fun _ => none := funext fun c => if_pos hw
      rw [e1, e2]
      exact (PMF.map_const _ _).trans (PMF.map_const _ _).symm
    · have hw' : ρ.slot j.1 ∉ H.withheld (as j).2.2 (as j).1 := fun h => h.elim hw fun h => by
        rw [hH] at h
        exact h
      have e := congrArg (PMF.map some)
        (hF (as j).1 (as j).2.1 (as j).2.2 (hi _ _ (w0, (as j).2.2) (ha j))
          (ρ.slot j.1) hw' (Ts j) (hbud j))
      rw [PMF.map_comp, PMF.map_comp] at e
      refine Eq.trans (congrArg (fun f => PMF.map f _) (funext fun a => ?_))
        (e.trans (congrArg (fun f => PMF.map f _) (funext fun c => ?_)))
      · show Option.map _ (ite (ρ.slot j.1 ∈ H.Bad) _ _) = _
        rw [if_neg hw]
        rfl
      · exact (if_neg hw).symm
  have L : (unif ((Unit × (Fin N → H.Coin)) × (Unit × (Fin N → Mk)))).map
        (fun a =>
          HonestV.overV (fun (_ : Unit) (k : K0) => k) put a.2
            ((H.localV W0).seenV k0 kc w0 J (fun j => ((as j).1, (as j).2.2)) ρ Ts a.1)) =
      (pis fun j : J => (unif (H.Coin × Mk)).map (F' j)).map fun f => (f, k0 w0) := by
    have h1 := map_unif_shared (ι := Fin N) (C0 := Unit × Unit) (Ω := H.Coin × Mk) J
      (fun (j : J) (_ : Unit × Unit) (a : H.Coin × Mk) => F' j a)
    rw [BatchOne.pmf_subsingleton (unif (Unit × Unit)) (PMF.pure ((), ())), PMF.pure_bind] at h1
    rw [← h1, PMF.map_comp, ← map_unif_of_equiv (coinE (Fin N) Unit Unit H.Coin Mk)]
    refine congrArg (fun f => PMF.map f _) (funext fun a => ?_)
    rw [hseen]
    rfl
  have Rr : (unif (Unit × (Fin N → H.Coin))).map
        ((H.localV W0).seenV k0 kc w0 J (fun j => ((as j).1, (as j).2.2)) ρ Ts) =
      (pis fun j : J => (unif H.Coin).map (F j)).map fun f => (f, k0 w0) := by
    have h1 := map_unif_shared
      (ι := Fin N) (C0 := Unit) (Ω := H.Coin) J (fun (j : J) (_ : Unit) (c : H.Coin) => F j c)
    rw [BatchSeqZk.pmf_unit (unif Unit), PMF.pure_bind] at h1
    rw [← h1, PMF.map_comp]
    exact congrArg (fun f => PMF.map f _) (funext hseen)
  refine L.trans (Eq.trans ?_ Rr.symm)
  rw [show (fun j : J => (unif (H.Coin × Mk)).map (F' j)) =
      fun j => (unif H.Coin).map (F j) from funext hslot]

end Iop
