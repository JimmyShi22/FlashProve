-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Ior/LinkVMaskedRulesShared.lean: the proofs of `Iop.Spec.freshV_shared`
(Ior/LinkVMaskedRules.lean; under the hypotheses of its statement: a sending run by the shared
part alone that is Fresh for one instance is FreshV for shared masks, at the union of the slots'
further positions) and of `Iop.Spec.blindV_shared` (the same file).

In standard terms: rules that carry a property of an interactive oracle reduction for one instance
over to its run on a batch of instances.

The notions (`HonestV.FreshV`, `HonestV.BlindV`; batch link, slot): the heads of
Ior/LinkVMasked.lean and Ior/LinkVMaskedRules.lean.

How: all rounds are shared, so all slots see one transcript at one value of the verifier messages.
If these are withheld, or J is empty, the slots' part of the tuple is a constant, and the
hypothesis on the bare shared run is the claim. Else take a slot j0 of J. The whole tuple is one
function Φ of what the property for one instance speaks of in slot j0, at the union of the further
positions: (the view, the one-instance reading of the result): each slot's view is a part of that
view; what a slot hands on is G of its own data, the plain parts and the reading; the reading of
the shared witness is the one-instance reading. Φ commutes with the overwriting, because G is
blind to the masks.

Limits: see Limits in the head of Ior/LinkVMaskedRules.lean.
-/
import Ior.LinkVMaskedRulesLocal

set_option autoImplicit false

namespace Iop
open Prob
open scoped ENNReal

theorem SStratR.res_ofStrat :
    ∀ {s : Shape} {β : Type} (σ : Strat s β) (l : RhoSh s (RoundSplits.const (RAnn.ofShared .sh) s)),
      (SStratR.ofStrat σ).res l = (σ.run (RhoSh.all s l)).2
  | [], _, _, _ => rfl
  | _ :: _, _, (_, k), (c, l) => SStratR.res_ofStrat (k c) l

namespace MaskKit
variable {C M U γ : Type} [Fintype C] [Nonempty C] [Fintype M] [Nonempty M] [Fintype U] [Unique U]

/-- coins of which there is one value do not matter -/
theorem map_unif_drop1 (f : C → γ) : (unif (C × U)).map (fun c => f c.1) = (unif C).map f :=
  map_unif_of_equiv (Equiv.prodUnique C U) f

theorem map_unif_drop2 (f : C × M → γ) :
    (unif ((C × U) × (M × U))).map (fun a => f (a.1.1, a.2.1)) = (unif (C × M)).map f :=
  map_unif_of_equiv ((Equiv.prodUnique C U).prodCongr (Equiv.prodUnique M U)) f

end MaskKit

open IOR MaskKit

open Classical in
theorem freshV_shared : Spec.freshV_shared := by
  intro X X' Ei Eo R Wi Wo W0 W0' H s0 Ri RiV bud N Kc Kj kc k0 kj Mk _ _ put G hF hH hi hag htie hG
    hGb hbare w0 J as ha ρ Ts hbud
  simp only [BatchSeqZk.slot_eq ρ] at hbud
  have hseen : ∀ c : H.Coin × (Fin N → Unit),
      (H.sharedV s0).seenV k0 kj w0 J (fun j => ((as j).1, (as j).2.2)) ρ Ts c =
        (fun j =>
            if RhoSh.all R.shape (BRho.shared ρ) ∈ H.Bad then none
            else
              some (R.view (Ts j) ((s0 w0 c.1).run (RhoSh.all R.shape (BRho.shared ρ))).1,
                  ((H.strat (as j).2.2 (as j).1 c.1).run (RhoSh.all R.shape (BRho.shared ρ))).2.1,
                  kj ((H.strat (as j).2.2 (as j).1 c.1).run
                      (RhoSh.all R.shape (BRho.shared ρ))).2.2),
          k0 ((s0 w0 c.1).run (RhoSh.all R.shape (BRho.shared ρ))).2) := fun c => by
    refine Prod.ext (funext fun j => ?_) ?_
    · show ite (ρ.slot j.1 ∈ (H.sharedV s0).withheld) _ _ = ite _ _ _
      simp only [BatchSeqZk.slot_eq ρ]
      by_cases hw : RhoSh.all R.shape (BRho.shared ρ) ∈ H.Bad
      · rw [if_pos hw, if_pos ((LinkV.shared_withheld H s0 _).mpr hw)]
      · rw [if_neg hw, if_neg fun h => hw ((LinkV.shared_withheld H s0 _).mp h), LinkV.shared_run]
    · show k0 ((SStratR.ofStrat (s0 w0 c.1)).res (BRho.shared ρ)) = _
      rw [SStratR.res_ofStrat]
  generalize RhoSh.all R.shape (BRho.shared ρ) = ρ' at hbud hseen
  rw [funext hseen]
  beta_reduce
  by_cases hcase : ρ' ∈ H.Bad ∨ IsEmpty J
  · -- the slots' part is a constant
    have hconst : ∀ c : H.Coin,
        (fun j : J =>
            if ρ' ∈ H.Bad then none
            else
              some (R.view (Ts j) ((s0 w0 c).run ρ').1,
                  ((H.strat (as j).2.2 (as j).1 c).run ρ').2.1,
                  kj ((H.strat (as j).2.2 (as j).1 c).run ρ').2.2)) =
          fun _ => none := fun c =>
      funext fun j => hcase.elim (fun hw => if_pos hw) fun he => (he.false j).elim
    simp only [hconst]
    have e := congrArg
      (PMF.map fun k : Kc => ((fun _ => none, k) : (J → Option (View R × X' × Kj)) × Kc))
      (hbare w0 ρ')
    rw [PMF.map_comp, PMF.map_comp] at e
    exact (map_unif_drop2 (U := Fin N → Unit) (fun a : H.Coin × Mk =>
        ((fun _ => none,
          put a.2 (k0 ((s0 w0 a.1).run ρ').2)) : (J → Option (View R × X' × Kj)) × Kc))).trans
      (e.trans (map_unif_drop1 (U := Fin N → Unit) (fun c : H.Coin =>
          ((fun _ => none, k0 ((s0 w0 c).run ρ').2) : (J → Option (View R × X' × Kj)) × Kc))).symm)
  · have hw : ρ' ∉ H.Bad := fun h => hcase (Or.inl h)
    obtain ⟨j0⟩ : Nonempty J := not_isEmpty_iff.mp fun h => hcase (Or.inr h)
    simp only [if_neg hw]
    have hw' : ρ' ∉ H.withheld (as j0).2.2 (as j0).1 := fun h => h.elim hw fun h => by
      rw [hH] at h
      exact h
    have e :=
      hF (as j0).1 (as j0).2.1 (as j0).2.2 (hi _ _ (w0, (as j0).2.2) (ha j0)) ρ' hw' _ (hbud j0)
    let Φ : View R × X' × Kc → (J → Option (View R × X' × Kj)) × Kc := fun z =>
      (fun j =>
          some (BatchSeqZk.restrict R ρ' (Ts j) z.1,
              (G (as j).1 (as j).2.2 z.1.plains ρ' z.2.2).1,
              (G (as j).1 (as j).2.2 z.1.plains ρ' z.2.2).2),
        z.2.2)
    have hreal : ∀ c : H.Coin, Φ (H.seen kc (as j0).2.2 (as j0).1 ρ' (Finset.univ.biUnion Ts) c) =
        (fun j =>
            some (R.view (Ts j) ((s0 w0 c).run ρ').1,
                ((H.strat (as j).2.2 (as j).1 c).run ρ').2.1,
                kj ((H.strat (as j).2.2 (as j).1 c).run ρ').2.2),
          k0 ((s0 w0 c).run ρ').2) := fun c => by
      have t0 := hag _ _ (w0, (as j0).2.2) c ρ' (ha j0)
      have k00 := htie _ _ (w0, (as j0).2.2) c ρ' (ha j0)
      refine Prod.ext (funext fun j => ?_) k00
      have tj := hag _ _ (w0, (as j).2.2) c ρ' (ha j)
      have kjj := htie _ _ (w0, (as j).2.2) c ρ' (ha j)
      have gj := hG _ _ (w0, (as j).2.2) c ρ' (ha j)
      dsimp only at t0 k00 tj kjj gj
      show some (BatchSeqZk.restrict R ρ' (Ts j)
              (R.view (Finset.univ.biUnion Ts) ((H.strat (as j0).2.2 (as j0).1 c).run ρ').1),
            (G (as j).1 (as j).2.2 ((H.strat (as j0).2.2 (as j0).1 c).run ρ').1.plains ρ'
              (kc ((H.strat (as j0).2.2 (as j0).1 c).run ρ').2.2)).1,
            (G (as j).1 (as j).2.2 ((H.strat (as j0).2.2 (as j0).1 c).run ρ').1.plains ρ'
              (kc ((H.strat (as j0).2.2 (as j0).1 c).run ρ').2.2)).2) = _
      rw [t0, k00, ← kjj, ← tj, ← gj, tj]
      have hr : ((s0 w0 c).run ρ').1.rho = ρ' := Strat.rho_run _ _
      have h3 := BatchSeqZk.restrict_view R (T := Ts j) (T' := Finset.univ.biUnion Ts)
        (fun p hp => Finset.mem_biUnion.2 ⟨j, Finset.mem_univ j, hp⟩) ((s0 w0 c).run ρ').1
      rw [hr] at h3
      rw [h3]
    have hover : ∀ (z : View R × X' × Kc) (M : Mk × (Fin N → Unit)),
        HonestV.overV put (fun (_ : Unit) (k : Kj) => k) M (Φ z) =
          Φ (z.1, z.2.1, put M.1 z.2.2) := fun z M => by
      refine Prod.ext (funext fun j => ?_) rfl
      show some (_, (G (as j).1 (as j).2.2 z.1.plains ρ' z.2.2).1,
            (G (as j).1 (as j).2.2 z.1.plains ρ' z.2.2).2) =
        some (_, (G (as j).1 (as j).2.2 z.1.plains ρ' (put M.1 z.2.2)).1,
            (G (as j).1 (as j).2.2 z.1.plains ρ' (put M.1 z.2.2)).2)
      rw [hGb]
    simp only [← hreal, hover]
    have e' := congrArg (PMF.map Φ) e
    rw [PMF.map_comp, PMF.map_comp] at e'
    exact (map_unif_drop2 (U := Fin N → Unit) (fun a : H.Coin × Mk =>
        Φ ((H.seen kc (as j0).2.2 (as j0).1 ρ' (Finset.univ.biUnion Ts) a.1).1,
            (H.seen kc (as j0).2.2 (as j0).1 ρ' (Finset.univ.biUnion Ts) a.1).2.1,
            put a.2 (H.seen kc (as j0).2.2 (as j0).1 ρ' (Finset.univ.biUnion Ts) a.1).2.2))).trans
      (e'.trans (map_unif_drop1 (U := Fin N → Unit) (fun c : H.Coin =>
          Φ (H.seen kc (as j0).2.2 (as j0).1 ρ' (Finset.univ.biUnion Ts) c))).symm)

theorem blindV_shared : Spec.blindV_shared := by
  intro X X' Ei Eo R Wi Wo W0 W0' H s0 K0 K0' Ki Ko k0 k0' kci kco M0 Mk put0 put0' puti puto hs hB
  refine ⟨fun w0 v0 M c0 σ h => ?_, fun w0 v0 wj vj M Ms x c ρ h0 hj => ?_⟩
  · show k0' ((SStratR.ofStrat (s0 v0 c0)).res σ) =
      put0' M (k0' ((SStratR.ofStrat (s0 w0 c0)).res σ))
    rw [SStratR.res_ofStrat, SStratR.res_ofStrat]
    exact (hs w0 v0 M c0 _ h).2
  · rw [LinkV.shared_run, LinkV.shared_run]
    obtain ⟨-, b2, b3⟩ := hB wj vj Ms x c.1 ρ hj
    exact ⟨(hs w0 v0 M c.1 ρ h0).1, b2, b3⟩

end Iop
