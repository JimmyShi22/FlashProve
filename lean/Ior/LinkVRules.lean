-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Ior/LinkVRules.lean: the two kinds of links that come from an IOR for one instance, and the bridge
to batch IOPs.

In standard terms: an interactive oracle reduction for one instance, run in every instance of a
batch or once for all.

Proofs of six statements of Ior/LinkV.lean.

What a link and a slot are: the head of Ior/LinkV.lean; a batch IOP: `BIOP`, Ior/Batch.lean.

Main names (statements and hypotheses: Ior/LinkV.lean):
  `accV_local`: completeness of an IOR in every slot
  `accV_shared`: completeness of an IOR run by the shared part alone
  `acc_toB`: the bridge: completeness
  `exactV_local`, `exactV_shared`, `exact_toB`: see their statements.

An IOR in every slot (`H.localV`). The slots have coins of their own and the shared part is
silent: the outputs of the slots of J are independent. The simulator: the IOR's simulator in each
slot of J, independently.

An IOR run by the shared part alone (`H.sharedV s0`). All rounds are shared, so all slots see one
transcript, each at its own further positions T_j. The simulator: the IOR's simulator once, with
the instance of some slot of J, at the union of the T_j; it is given the union of what is given
for the slots (by hypothesis these symbols are determined by the shared witness, so they fit
together); each slot is shown the part of the simulated view that it may see.

The bridge (`H.toB mk`). Results are dropped; the given symbols are laid into the disclosed view.

Limits: this file says nothing on running times; nothing on soundness. See also Limits in the head
of Ior/LinkV.lean.

Terms: lean/GLOSSARY.md.
-/
import Ior.LinkV
import Ior.BatchSeqZkRules

set_option autoImplicit false

namespace Iop
open Prob Prob.Indep
open scoped ENNReal

/-! ## 1. Helpers -/

theorem SStratR.zip_silentR_ofStrat :
    ∀ {s : Shape} {β γ : Type} (b : γ) (σ : Strat s β),
      (SStratR.silentR s b).zip (LStratR.ofStrat σ) = Strat.map (fun r => (b, r)) σ
  | [], _, _, _, _ => rfl
  | _ :: _, _, _, b, (m, k) =>
    congrArg (Prod.mk m) (funext fun c => SStratR.zip_silentR_ofStrat b (k c))

theorem SStratR.run_zip_ofStrat_muteF :
    ∀ {s : Shape} {β γ : Type} (σ : Strat s β) (f : Rho s → γ) (ρ : Rho s),
      Strat.run ((SStratR.ofStrat σ).zip (LStratR.muteF s f)) ρ = ((σ.run ρ).1, ((σ.run ρ).2, f ρ))
  | [], _, _, _, _, () => rfl
  | _ :: _, _, _, (m, k), f, (c, ρ) => by
      have ih := SStratR.run_zip_ofStrat_muteF (k c) (fun ρ' => f (c, ρ')) ρ
      show ((m, c,
            (Strat.run ((SStratR.ofStrat (k c)).zip (LStratR.muteF _ fun ρ' => f (c, ρ'))) ρ).1),
          (Strat.run ((SStratR.ofStrat (k c)).zip (LStratR.muteF _ fun ρ' => f (c, ρ'))) ρ).2) = _
      rw [ih]
      rfl

theorem SStratR.zip_forget :
    ∀ {s : Shape} {A : RoundSplits s} {β γ : Type} (σ₀ : SStratR s A β) (σ : LStratR s A γ),
      SStrat.zip σ₀.forget σ.forget = Strat.map (fun _ => ()) (σ₀.zip σ)
  | [], _, _, _, _, _ => rfl
  | _ :: _, (a, _), _, _, (m0, k0), (mj, kj) =>
    congrArg (Prod.mk (a.join m0 mj))
      (funext fun c => SStratR.zip_forget (k0 (a.kind.shOf c)) (kj c))

namespace LinkV
open IOR OnlineHon BatchSeqZk

section Local
variable {X X' : Type} {Ei Eo : ExtSpec} {R : IOR X Ei X' Eo} {Wi Wo : Type}
  (H : R.Honest Wi Wo) (W0 : Type)

theorem local_withheld (ρ : Rho R.shape) : ρ ∈ (H.localV W0).withheld ↔ ρ ∈ H.Bad := by
  show (RhoLo.all R.shape (Rho.lo (RoundSplits.allLocal R.shape) ρ) ∈ H.Bad ∨ false = true) ↔ _
  rw [RhoLo.all_lo]
  exact ⟨fun h => h.elim id fun h => Bool.noConfusion h, Or.inl⟩

theorem local_run (w0 : W0) (x : X) (wi : Wi) (c : Unit × H.Coin) (ρ : Rho R.shape) :
    Strat.run ((H.localV W0).one w0 x wi c) ρ =
      (((H.strat wi x c.2).run ρ).1, (w0, ((H.strat wi x c.2).run ρ).2)) := by
  show Strat.run ((SStratR.silentR R.shape w0).zip (LStratR.ofStrat (H.strat wi x c.2))) ρ = _
  rw [SStratR.zip_silentR_ofStrat, Strat.run_map]

end Local

section Shared
variable {X X' : Type} {Ei Eo : ExtSpec} {R : IOR X Ei X' Eo} {Wi Wo W0 W0' : Type}
  (H : R.Honest Wi Wo) (s0 : W0 → H.Coin → Strat R.shape W0')

theorem shared_withheld (ρ : Rho R.shape) : ρ ∈ (H.sharedV s0).withheld ↔ ρ ∈ H.Bad := by
  classical
  show ((Rho.lo (RoundSplits.const (RAnn.ofShared .sh) R.shape) ρ ∈ (∅ : Set _)) ∨
      decide (RhoSh.all R.shape (Rho.sh (RoundSplits.const (RAnn.ofShared .sh) R.shape) ρ) ∈ H.Bad) =
        true) ↔
    _
  rw [RhoSh.all_sh, decide_eq_true_eq]
  exact ⟨fun h => h.elim (fun h => h.elim) id, Or.inr⟩

theorem shared_run (w0 : W0) (x : X) (wi : Wi) (c : H.Coin × Unit) (ρ : Rho R.shape) :
    Strat.run ((H.sharedV s0).one w0 x wi c) ρ =
      (((s0 w0 c.1).run ρ).1, (((s0 w0 c.1).run ρ).2, ((H.strat wi x c.1).run ρ).2)) := by
  show Strat.run
      ((SStratR.ofStrat (s0 w0 c.1)).zip
        (LStratR.muteF R.shape fun ρ => ((H.strat wi x c.1).run ρ).2)) ρ = _
  rw [SStratR.run_zip_ofStrat_muteF]

end Shared

open Classical in
/-- At one `ρ`, with a slot `j0`: what is given for the slots of `ι`, if the slots' oracles agree
wherever something is given, is what is given at the union of the further positions. -/
theorem merge_ansV {X X' : Type} {Ei Eo : ExtSpec} (R : IOR X Ei X' Eo) {ι : Type} [Fintype ι]
    (ρ : Rho R.shape) (Ts : ι → Finset (OPos R.shape)) (ys : ι → Ei.Str)
    (hsame : ∀ j j' T q, q ∈ R.given ρ T → Ei.rd (ys j) q = Ei.rd (ys j') q) (j0 : ι) :
    merge (fun j => Ei.ans (R.given ρ (Ts j)) (ys j)) =
      Ei.ans (R.given ρ (Finset.univ.biUnion Ts)) (ys j0) := by
  funext q
  by_cases hq : q ∈ R.given ρ (Finset.univ.biUnion Ts)
  · have hex : ∃ j, (Ei.ans (R.given ρ (Ts j)) (ys j) q).isSome = true := by
      rcases IOR.mem_given.1 hq with h | ⟨p, hp, h⟩
      · exact ⟨j0, by rw [Ei.ans_of_mem _ (IOR.mem_given.2 (Or.inl h))]; rfl⟩
      · rcases hp with hp | hp
        · exact ⟨j0, by rw [Ei.ans_of_mem _ (IOR.mem_given.2 (Or.inr ⟨p, Or.inl hp, h⟩))]; rfl⟩
        · obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.1 hp
          exact ⟨j, by rw [Ei.ans_of_mem _ (IOR.mem_given.2 (Or.inr ⟨p, Or.inr hj, h⟩))]; rfl⟩
    refine (dif_pos hex).trans ?_
    have hm : q ∈ R.given ρ (Ts hex.choose) := by
      by_contra hn
      have h := hex.choose_spec
      rw [Ei.ans_of_not_mem _ hn] at h
      cases h
    show Ei.ans (R.given ρ (Ts hex.choose)) (ys hex.choose) q = _
    rw [Ei.ans_of_mem _ hm, Ei.ans_of_mem _ hq, hsame _ j0 _ q hq]
  · have hnex : ¬ ∃ j, (Ei.ans (R.given ρ (Ts j)) (ys j) q).isSome = true := by
      rintro ⟨j, hj⟩
      have hm : q ∈ R.given ρ (Ts j) := by
        by_contra hn
        rw [Ei.ans_of_not_mem _ hn] at hj
        cases hj
      refine hq ?_
      rcases IOR.mem_given.1 hm with h | ⟨p, hp, h⟩
      · exact IOR.mem_given.2 (Or.inl h)
      · exact IOR.mem_given.2
          (Or.inr ⟨p, hp.imp id fun h' => Finset.mem_biUnion.2 ⟨j, Finset.mem_univ j, h'⟩, h⟩)
    exact (dif_neg hnex).trans (Ei.ans_of_not_mem _ hq).symm

section Bridge
variable {X : Type} {E0 Ej : ExtSpec} {R : IOR X (E0.prod Ej) Unit extNone} {A : RoundSplits R.shape}
  {W0 Wi Wj W0' Wo : Type} (H : R.HonestV A W0 Wi W0' Wo) (mk : W0 → Wj → Wi)

theorem toB_run (w0 : W0) (x : X) (wj : Wj) (c : H.Coin0 × H.Coin) (ρ : Rho R.shape) :
    (Strat.run ((H.toB mk).one w0 x wj c) ρ).1 = (Strat.run (H.one w0 x (mk w0 wj) c) ρ).1 := by
  show (Strat.run
      (SStrat.zip (H.strat0 w0 c.1).forget (H.strat w0 c.1 x (mk w0 wj) c.2).forget) ρ).1 = _
  rw [SStratR.zip_forget, Strat.run_map]
  rfl

end Bridge
end LinkV

open IOR

/-! ## 2. An IOR in every slot -/

theorem accV_local : Spec.accV_local := by
  intro X X' Ei Eo R Wi Wo W0 H Ri Ro RiV RoV hA hH hi ho x y w c ρ hR hρ
  have hB : ρ ∉ H.Bad := fun h => hρ ((LinkV.local_withheld H W0 ρ).mpr h)
  have h1 : ρ ∉ H.withheld w.2 x := fun h => h.elim hB fun h => by
    rw [hH] at h
    exact h
  obtain ⟨h2, h3⟩ := hA x y w.2 c.2 ρ (hi x y w hR) h1
  rw [LinkV.local_run]
  exact ⟨h2, ho x y w c.2 ρ hR hB h3⟩

open Classical in
theorem exactV_local : Spec.exactV_local := by
  intro X X' Ei Eo R Wi Wo W0 H Ri RiV bud N hE hH hi
  obtain ⟨S, hS⟩ := hE
  refine ⟨fun J xs ρs Ts as => pis fun j : J => S (xs j) (ρs j) (Ts j) (as j), ?_⟩
  intro w0 J as ha ρ Ts hbud
  have h1 := map_unif_shared (ι := Fin N) (C0 := Unit) (Ω := H.Coin) J (fun (j : J) (_ : Unit) (c : H.Coin) =>
    if ρ.slot j.1 ∈ (H.localV W0).withheld then none
    else
      some (R.view (Ts j)
          (Strat.run ((H.localV W0).one w0 (as j).1 (as j).2.2 ((), c)) (ρ.slot j.1)).1))
  refine h1.trans ?_
  rw [BatchSeqZk.pmf_unit (unif Unit), PMF.pure_bind]
  refine congrArg pis (funext fun j => ?_)
  have hj := hS (as j).1 (as j).2.1 (as j).2.2 (hi _ _ (w0, (as j).2.2) (ha j)) (ρ.slot j.1)
    (by rw [hH]; exact fun h => h) (Ts j) (hbud j)
  show _ = S (as j).1 (ρ.slot j.1) (Ts j) (Ei.ans (R.given (ρ.slot j.1) (Ts j)) (as j).2.1)
  rw [← hj]
  by_cases hw : ρ.slot j.1 ∈ H.Bad
  · rw [H.output_of_mem (Ts j) (Or.inl hw)]
    have : (fun c : H.Coin =>
          if ρ.slot j.1 ∈ (H.localV W0).withheld then none
          else
            some (R.view (Ts j)
                (Strat.run ((H.localV W0).one w0 (as j).1 (as j).2.2 ((), c)) (ρ.slot j.1)).1)) =
        fun _ => none :=
      funext fun c => if_pos ((LinkV.local_withheld H W0 _).mpr hw)
    rw [this]
    exact PMF.map_const _ _
  · have hw' : ρ.slot j.1 ∉ H.withheld (as j).2.2 (as j).1 := fun h => h.elim hw fun h => by
      rw [hH] at h
      exact h
    rw [H.output_of_not_mem (Ts j) hw']
    refine congrArg (fun φ => PMF.map φ _) (funext fun c => ?_)
    refine (if_neg fun h => hw ((LinkV.local_withheld H W0 _).mp h)).trans ?_
    rw [LinkV.local_run]

/-! ## 3. An IOR run by the shared part alone -/

theorem accV_shared : Spec.accV_shared := by
  intro X X' Ei Eo R Wi Wo W0 W0' H s0 Ri Ro RiV RoV hA hH hi hrun ho x y w c ρ hR hρ
  have hB : ρ ∉ H.Bad := fun h => hρ ((LinkV.shared_withheld H s0 ρ).mpr h)
  have h1 : ρ ∉ H.withheld w.2 x := fun h => h.elim hB fun h => by
    rw [hH] at h
    exact h
  obtain ⟨h2, h3⟩ := hA x y w.2 c.1 ρ (hi x y w hR) h1
  have h4 := ho x y w c.1 ρ hR hB h3
  rw [LinkV.shared_run]
  rw [hrun x y w c.1 ρ hR] at h2 h4
  exact ⟨h2, h4⟩

open Classical in
theorem exactV_shared : Spec.exactV_shared := by
  intro X X' Ei Eo R Wi Wo W0 W0' H s0 Ri RiV bud N f hE hH hi hrun hf
  obtain ⟨S, hS⟩ := hE
  refine ⟨fun J xs ρs Ts as =>
      if h : Nonempty J then
        (S (xs (Classical.choice h)) (ρs (Classical.choice h))
            (Finset.univ.biUnion Ts) (BatchSeqZk.merge as)).map
          fun o j => o.map (BatchSeqZk.restrict R (ρs j) (Ts j)) else PMF.pure fun _ => none,
    ?_⟩
  intro w0 J as ha ρ Ts hbud
  by_cases hJ : Nonempty J
  · beta_reduce
    rw [dif_pos hJ]
    generalize Classical.choice hJ = j0
    unfold IOR.HonestV.output
    simp only [BatchSeqZk.slot_eq ρ] at hbud ⊢
    generalize RhoSh.all R.shape (BRho.shared ρ) = ρ' at hbud ⊢
    rw [LinkV.merge_ansV R ρ' Ts (fun j => (as j).2.1)
        (fun j j' T q hq =>
          (hf _ _ (w0, (as j).2.2) ρ' T q (ha j) hq).trans
            (hf _ _ (w0, (as j').2.2) ρ' T q (ha j') hq).symm) j0]
    rw [← hS (as j0).1 (as j0).2.1 (as j0).2.2 (hi _ _ (w0, (as j0).2.2) (ha j0)) ρ'
        (by rw [hH]; exact fun h => h) _ (hbud j0)]
    by_cases hw : ρ' ∈ H.Bad
    · rw [H.output_of_mem _ (Or.inl hw), PMF.pure_map]
      have : (fun (c : H.Coin × (Fin N → Unit)) (j : J) =>
            if ρ' ∈ (H.sharedV s0).withheld then none
            else
              some (R.view (Ts j)
                  (Strat.run ((H.sharedV s0).one w0 (as j).1 (as j).2.2 (c.1, c.2 j.1)) ρ').1)) =
          fun _ _ => none :=
        funext fun c => funext fun j => if_pos ((LinkV.shared_withheld H s0 ρ').mpr hw)
      exact (congrArg (fun φ => PMF.map φ _) this).trans (PMF.map_const _ _)
    · have hw' : ρ' ∉ H.withheld (as j0).2.2 (as j0).1 := fun h => h.elim hw fun h => by
        rw [hH] at h
        exact h
      rw [H.output_of_not_mem _ hw', PMF.map_comp,
        ← map_fst_unif (C := H.Coin) (D := Fin N → Unit), PMF.map_comp]
      refine congrArg (fun φ => PMF.map φ _) (funext fun c => funext fun j => ?_)
      refine (if_neg fun h => hw ((LinkV.shared_withheld H s0 ρ').mp h)).trans ?_
      rw [LinkV.shared_run]
      show some (R.view (Ts j) ((s0 w0 c.1).run ρ').1) =
        some (BatchSeqZk.restrict R ρ' (Ts j)
            (R.view (Finset.univ.biUnion Ts) ((H.strat (as j0).2.2 (as j0).1 c.1).run ρ').1))
      rw [hrun (as j0).1 (as j0).2.1 (w0, (as j0).2.2) c.1 ρ' (ha j0)]
      have hr : ((s0 w0 c.1).run ρ').1.rho = ρ' := Strat.rho_run _ _
      have h3 := BatchSeqZk.restrict_view R (T := Ts j) (T' := Finset.univ.biUnion Ts)
        (fun p hp => Finset.mem_biUnion.2 ⟨j, Finset.mem_univ j, hp⟩) ((s0 w0 c.1).run ρ').1
      rw [hr] at h3
      rw [h3]
  · haveI : IsEmpty J := not_nonempty_iff.mp hJ
    exact BatchOne.pmf_subsingleton _ _

/-! ## 4. The bridge -/

theorem acc_toB : Spec.acc_toB := by
  intro X E0 Ej R A W0 Wi Wj W0' Wo H mk RiV RoV hA x y w c ρ hR hρ
  have h := (hA x y (w.1, mk w.1 w.2) c ρ hR hρ).1
  show (R.out x y (Strat.run ((H.toB mk).one w.1 x w.2 c) ρ).1).isSome = true
  rw [LinkV.toB_run, h]
  rfl

open Classical in
theorem exact_toB : Spec.exact_toB := by
  intro X E0 Ej R A W0 Wi Wj W0' Wo H mk RiV N bud ⟨Sim, hS⟩
  refine ⟨fun J xs ρs Ts as => (Sim J xs ρs Ts as).map fun o j => (o j).map (BatchSeqZk.toD (as j)),
    ?_⟩
  intro w0 y0 a ha J as has ρ Ts hbud
  rw [OnlineHon.outputQ_eq (H.toB mk) w0 y0 a ρ J Ts as has]
  have h := hS w0 J (fun j => ((as j).1, (y0, (as j).2.1), mk w0 (as j).2.2))
    (fun j => ha j.1 (as j) (has j)) ρ Ts hbud
  show _ = PMF.map _
      (Sim J (fun j => (as j).1) (fun j => ρ.slot j.1) Ts fun j =>
        (E0.prod Ej).ans (R.given (ρ.slot j.1) (Ts j)) (y0, (as j).2.1))
  rw [← h]
  unfold IOR.HonestV.output
  rw [PMF.map_comp]
  refine congrArg (fun φ => PMF.map φ _) (funext fun c => funext fun j => ?_)
  show (if ρ.slot j.1 ∈ H.withheld then none else some _) =
    Option.map _ (if ρ.slot j.1 ∈ H.withheld then none else some _)
  by_cases hw : ρ.slot j.1 ∈ H.withheld
  · rw [if_pos hw, if_pos hw]
    rfl
  · rw [if_neg hw, if_neg hw, LinkV.toB_run, BatchSeqZk.dviewT_eq, Strat.rho_run]
    rfl

end Iop
