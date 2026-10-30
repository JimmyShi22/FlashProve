-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Ior/LinkVMaskedRulesProofs.lean: proofs of four statements of Ior/LinkVMaskedRules.lean, each
proved as it stands there: `blindV_local`, `mmV_local`, `mmV_shared`, `freshV_conseq`; and helpers
on strategies with results and on shared verifier messages.

In standard terms: rules that carry a property of an interactive oracle reduction for one instance
over to its run on a batch of instances, and a weakening rule.

The notions (`HonestV.FreshV`, `HonestV.MMV`, `HonestV.BlindV`; batch link, slot): the heads of
Ior/LinkVMasked.lean and Ior/LinkVMaskedRules.lean.

How: `mmV_local`: the slots have masks of their own, so the law is a product over the slots of J
(Blocks/Batch/ProbPi.lean: `map_unif_shared`), and the item for one instance is used slot by slot.
`mmV_shared`: all slots see one transcript and, by the claim, one public part. `freshV_conseq`:
both sides are mapped by the coarser readings.

Limits: see Limits in the head of Ior/LinkVMaskedRules.lean.
-/
import Ior.LinkVMaskedRules
import Ior.LinkVMaskedProofs

set_option autoImplicit false

namespace Iop
open Prob Prob.Indep
open scoped ENNReal

/-! ## 1. Helpers -/

theorem SStratR.res_silentR :
    ∀ (s : Shape) {β : Type} (b : β) (σ : RhoSh s (RoundSplits.allLocal s)),
      (SStratR.silentR s b).res σ = b
  | [], _, _, _ => rfl
  | _ :: s, _, b, (_, σ) => SStratR.res_silentR s b σ

theorem SStratR.res_bindR :
    ∀ {s t : Shape} {A : RoundSplits s} {B : RoundSplits t} {β γ : Type} (S : SStratR s A β)
        (f : β → SStratR t B γ) (σ : RhoSh (s ++ t) (RoundSplits.app A B)),
      (S.bindR f).res σ = (f (S.res (RhoSh.fstA A B σ))).res (RhoSh.sndA A B σ)
  | [], _, _, _, _, _, _, _, _ => rfl
  | _ :: _, _, (_, _), _, _, _, (_, k), f, (c, σ) => SStratR.res_bindR (k c) f σ

theorem BRho.shared_fstA {N : ℕ} :
    ∀ {s t : Shape} (A : RoundSplits s) (B : RoundSplits t) (ρ : BRho N (s ++ t) (RoundSplits.app A B)),
      BRho.shared (BRho.fstA A B ρ) = RhoSh.fstA A B (BRho.shared ρ)
  | [], _, _, _, _ => rfl
  | _ :: _, _, (a, A), B, (v, ρ) => congrArg (Prod.mk (a.kind.allSh v)) (BRho.shared_fstA A B ρ)

theorem BRho.shared_sndA {N : ℕ} :
    ∀ {s t : Shape} (A : RoundSplits s) (B : RoundSplits t) (ρ : BRho N (s ++ t) (RoundSplits.app A B)),
      BRho.shared (BRho.sndA A B ρ) = RhoSh.sndA A B (BRho.shared ρ)
  | [], _, _, _, _ => rfl
  | _ :: _, _, (_, A), B, (_, ρ) => BRho.shared_sndA A B ρ

open IOR

/-! ## 2. The rules that come from one instance, and `freshV_conseq` -/

theorem blindV_local : Spec.blindV_local := by
  intro X X' Ei Eo R Wi Wo W0 H K0 Ki Ko k0 kci kco M0 Mk put0 puti puto hB
  refine ⟨fun w0 v0 M c0 σ h => ?_, fun w0 v0 wj vj M Ms x c ρ _ h => ?_⟩
  · show k0 ((SStratR.silentR R.shape v0).res σ) = put0 M (k0 ((SStratR.silentR R.shape w0).res σ))
    rw [SStratR.res_silentR, SStratR.res_silentR]
    exact h
  · rw [LinkV.local_run, LinkV.local_run]
    exact hB wj vj Ms x c.2 ρ h

theorem mmV_local : Spec.mmV_local := by
  classical
  intro X X' Ei Eo R Wi Wo W0 H D N m hBad
  refine ⟨m.noOrc,
    Set.eq_empty_of_forall_notMem fun ρ hρ => ?_,
    fun w0 x wj c ρ _ => ?_,
    fun xp _ κ _ Ms h => m.stable xp κ Ms h,
    fun J _ κ xp ρ hCl => ?_⟩
  · have h := (LinkV.local_withheld H W0 ρ).mp hρ
    rw [hBad] at h
    exact h
  · rw [LinkV.local_run]
    exact m.run wj x c.2 ρ
  · have h1 := map_unif_shared (ι := Fin N) (C0 := Unit) (Ω := D.Mk) J
      (fun (j : J) (_ : Unit) (M : D.Mk) => D.msg (D.put M (κ j)) (xp j) (ρ.slot j.1))
    refine h1.trans ?_
    rw [BatchSeqZk.pmf_unit (unif Unit), PMF.pure_bind]
    exact congrArg pis (funext fun j => m.law (κ j) (xp j) (ρ.slot j.1) (hCl j))

theorem mmV_shared : Spec.mmV_shared := by
  classical
  intro X X' Ei Eo R Wi Wo W0 W0' H s0 D k N m hBad hs0 hdet
  refine ⟨m.noOrc,
    Set.eq_empty_of_forall_notMem fun ρ hρ => ?_,
    fun w0 x wj c ρ hCl => ?_,
    fun xp κ _ M _ h => m.stable xp κ M h,
    fun J κ _ xp ρ hCl => ?_⟩
  · have h := (LinkV.shared_withheld H s0 ρ).mp hρ
    rw [hBad] at h
    exact h
  · rw [LinkV.shared_run]
    exact hs0 w0 c.1 ρ (D.pub x) hCl
  · by_cases hJ : Nonempty J
    · show _ = dite (Nonempty J) _ _
      rw [dif_pos hJ]
      generalize Classical.choice hJ = j0
      simp only [BatchSeqZk.slot_eq ρ]
      rw [← m.law κ (xp j0) _ (hCl j0), PMF.map_comp,
        ← map_fst_unif (C := D.Mk) (D := Fin N → Unit), PMF.map_comp]
      refine congrArg (fun φ => PMF.map φ _) (funext fun M => funext fun j => ?_)
      show D.msg (D.put M.1 κ) (xp j) _ = D.msg (D.put M.1 κ) (xp j0) _
      rw [hdet (xp j) (xp j0) κ (hCl j) (hCl j0)]
    · haveI : IsEmpty J := not_nonempty_iff.mp hJ
      exact BatchOne.pmf_subsingleton _ _

theorem freshV_conseq : Spec.freshV_conseq := by
  classical
  intro X X' Ei Eo R A W0 Wj W0' Wj' H Ri Ri' N bud bud' K0 Kj K0' Kj' k0 kj g0 gj M0 _ _ Mj _ _
    put0 putj put0' putj' hR hb h0 hj hF w0 J as ha ρ Ts hT
  have e := congrArg
    (PMF.map fun z : (J → Option (View R × X' × Kj)) × K0 =>
      ((fun j => (z.1 j).map fun t => (t.1, t.2.1, gj t.2.2),
        g0 z.2) : (J → Option (View R × X' × Kj')) × K0'))
    (hF w0 J as (fun j => hR _ _ _ (ha j)) ρ Ts (hb _ _ _ hT))
  rw [PMF.map_comp, PMF.map_comp] at e
  refine Eq.trans (congrArg (fun f => PMF.map f _) (funext fun a => ?_))
    (e.trans (congrArg (fun f => PMF.map f _) (funext fun c => ?_)))
  · refine Prod.ext (funext fun j => ?_) ?_
    · show Option.map _ (ite _ _ _) = Option.map _ (Option.map _ (ite _ _ _))
      by_cases hw : ρ.slot j.1 ∈ H.withheld
      · rw [if_pos hw, if_pos hw]
        rfl
      · rw [if_neg hw, if_neg hw]
        show some (_, _, putj' _ (gj _)) = some (_, _, gj (putj _ _))
        rw [hj]
    · show put0' a.2.1 (g0 _) = g0 (put0 a.2.1 _)
      rw [h0]
      rfl
  · refine Prod.ext (funext fun j => ?_) rfl
    show Option.map _ (ite _ _ _) = ite _ _ _
    by_cases hw : ρ.slot j.1 ∈ H.withheld
    · rw [if_pos hw, if_pos hw]
      rfl
    · rw [if_neg hw, if_neg hw]
      rfl

end Iop
