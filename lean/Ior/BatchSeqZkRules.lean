-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Ior/BatchSeqZkRules.lean: a protocol for one instance, run on a batch: an interactive oracle proof
(IOP) in every slot, or an interactive oracle reduction (IOR) run by the shared part alone.

Notions for one instance (Ior/Honest.lean; R an IOR, H its honest side):
  Further positions T: `IOR.view`, Ior/Honest.lean.
  `H.ExactWith Ri bud S`: for every (x, y, w) in Ri, every ρ outside `H.Hid w x` and every T with
    `bud ρ T`, the distribution `H.output w x ρ T` equals `S x ρ T a`, where a gives the symbols
    of y at the positions `R.given ρ T` and `none` at the others. `Exact` says that some S does.
    Here `H.Exact Ri bud` is a premise, of `Spec.exact_localB` and `Spec.exactB_shared`. Their
    conclusions are the forms for batches (`BIOP.Honest.Exact`, Ior/Batch.lean; `HonestB.ExactB`,
    Ior/BatchSeqZk.lean): what stands above is not said of them.

Proofs of four statements of Ior/BatchSeqZk.lean, and `budSeqB_empty_iff`: the composed budget at
"no further reads". What a slot and the shared part are: the head of Ior/BatchSeqZk.lean.

Main names (statements and hypotheses: Ior/BatchSeqZk.lean):
  `acc_localB`: completeness of an IOP in every slot
  `accB_shared`: completeness of an IOR run by the shared part alone
  `exact_localB`, `exactB_shared`: see their statements.

An IOP in every slot (`localB`, `localH`). The slots have coins of their own and there is no
shared part: the outputs of the slots of J are independent. The simulator:
  the IOP's simulator in each slot of J, independently;
  the given symbols are laid into the disclosed view.

An IOR run by the shared part alone (`sharedH`). All rounds are shared, so all slots see one
transcript, each at its own further positions T_j. The simulator:
  the IOR's simulator once, with the instance of some slot of J, at the union of the T_j;
  it is given the union of what is given for the slots (these are symbols of the shared oracles
    alone, by hypothesis, so they fit together);
  each slot is shown the part of the simulated view that it may see.

Limits: this file says nothing on running times; nothing on soundness. See also Limits in the head
of Ior/BatchSeqZk.lean.

Terms: lean/GLOSSARY.md.
-/
import Ior.BatchSeqZkProofs
import Iop.BatchOne
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Iop
open Prob Prob.Indep
open scoped ENNReal

/-! ## 1. Helpers -/

theorem RhoLo.all_lo : ∀ (s : Shape) (ρ : Rho s), RhoLo.all s (Rho.lo (RoundSplits.allLocal s) ρ) = ρ
  | [], _ => rfl
  | _ :: s, (c, ρ) => congrArg (Prod.mk c) (RhoLo.all_lo s ρ)

theorem RhoSh.all_sh :
    ∀ (s : Shape) (ρ : Rho s), RhoSh.all s (Rho.sh (RoundSplits.const (RAnn.ofShared .sh) s) ρ) = ρ
  | [], _ => rfl
  | _ :: s, (c, ρ) => congrArg (Prod.mk c) (RhoSh.all_sh s ρ)

theorem SStratR.zip_ofStrat_mute :
    ∀ {s : Shape} {β γ : Type} (σ : Strat s β) (b : γ),
      (SStratR.ofStrat σ).zip (LStratR.mute s b) = Strat.map (fun r => (r, b)) σ
  | [], _, _, _, _ => rfl
  | _ :: _, _, _, (m, k), b =>
    congrArg (Prod.mk m) (funext fun c => SStratR.zip_ofStrat_mute (k c) b)

namespace BatchSeqZk
open IOR OnlineHon

theorem pmf_unit (p : PMF Unit) : p = PMF.pure () := BatchOne.pmf_subsingleton _ _

/-- the disclosed view from a view and the symbols of the external oracles -/
def toD {X : Type} {E : ExtSpec} {B : IOR X E Unit extNone}
    (a : E.Pos → Option E.Sym) (v : View B) : DView B.toInteractiveOracleProof :=
  ⟨v.plains, a, v.orc⟩

theorem dviewT_eq {X : Type} {E : ExtSpec} (B : IOR X E Unit extNone) (T : Finset (OPos B.shape))
    (y : E.Str) (τ : Tr B.shape) :
    B.dviewT T y τ = toD (E.ans (B.given τ.rho T) y) (B.view T τ) := rfl

/-! ## 2. An IOP in every slot -/

section Local
variable {X : Type} {E0 Ej : ExtSpec} {B : IOR X (E0.prod Ej) Unit extNone} {Wi W0 Wj : Type}
  (H : B.Honest Wi Unit) (mk : W0 → Wj → Wi)

theorem local_withheld (ρ : Rho B.shape) : ρ ∈ (localH H mk).withheld ↔ ρ ∈ H.Bad := by
  show (RhoLo.all B.shape (Rho.lo (RoundSplits.allLocal B.shape) ρ) ∈ H.Bad ∨ false = true) ↔ _
  rw [RhoLo.all_lo]
  exact ⟨fun h => h.elim id fun h => Bool.noConfusion h, Or.inl⟩

theorem local_run (w0 : W0) (x : X) (wj : Wj) (c : Unit × H.Coin) (ρ : Rho B.shape) :
    (Strat.run ((localH H mk).one w0 x wj c) ρ).1 = ((H.strat (mk w0 wj) x c.2).run ρ).1 := by
  show (Strat.run
      (SStrat.zip (SStrat.silent .lo B.shape)
        (LStrat.last .lo (Strat.map (fun _ => ()) (H.strat (mk w0 wj) x c.2)))) ρ).1 = _
  rw [zip_silent_last, Strat.run_map]

end Local
end BatchSeqZk

theorem acc_localB : Spec.acc_localB := by
  intro X E0 Ej B Wi W0 Wj H mk Ri hA hH x y w c ρ hR hρ
  have h1 : ρ ∉
      H.withheld (mk w.1 w.2)
        x := fun h => h.elim (fun h => hρ ((BatchSeqZk.local_withheld H mk ρ).mpr h)) fun h => by
    rw [hH] at h
    exact h
  have h2 := (hA x y (mk w.1 w.2) c.2 ρ hR h1).1
  show (B.out x y (Strat.run ((localH H mk).one w.1 x w.2 c) ρ).1).isSome = true
  rw [BatchSeqZk.local_run, h2]
  rfl

open Classical in
theorem exact_localB : Spec.exact_localB := by
  intro X E0 Ej B Wi W0 Wj H mk Ri bud N hE hH
  obtain ⟨S, hS⟩ := hE
  refine ⟨fun J xs ρs Ts as =>
      pis fun j : J => (S (xs j) (ρs j) (Ts j) (as j)).map (Option.map (BatchSeqZk.toD (as j))),
    ?_⟩
  intro w0 y0 a ha J as has ρ Ts hbud
  rw [OnlineHon.outputQ_eq (localH H mk) w0 y0 a ρ J Ts as has]
  have h1 := map_unif_shared (ι := Fin N) (C0 := Unit) (Ω := H.Coin) J (fun (j : J) (_ : Unit) (c : H.Coin) =>
    if ρ.slot j.1 ∈ (localH H mk).withheld then none
    else
      some (B.dviewT (Ts j) (y0, (as j).2.1)
          (Strat.run ((localH H mk).one w0 (as j).1 (as j).2.2 ((), c)) (ρ.slot j.1)).1))
  refine h1.trans ?_
  rw [BatchSeqZk.pmf_unit (unif Unit), PMF.pure_bind]
  refine congrArg pis (funext fun j => ?_)
  have hj := hS (as j).1 (y0, (as j).2.1) (mk w0 (as j).2.2) (ha j.1 (as j) (has j)) (ρ.slot j.1)
    (by rw [hH]; exact fun h => h) (Ts j) (hbud j)
  show _ = PMF.map
      (Option.map
        (BatchSeqZk.toD ((E0.prod Ej).ans (B.given (ρ.slot j.1) (Ts j)) (y0, (as j).2.1))))
      (S (as j).1 (ρ.slot j.1) (Ts j)
        ((E0.prod Ej).ans (B.given (ρ.slot j.1) (Ts j)) (y0, (as j).2.1)))
  rw [← hj]
  by_cases hw : ρ.slot j.1 ∈ H.Bad
  · rw [H.output_of_mem (Ts j) (Or.inl hw), PMF.pure_map]
    have : (fun c : H.Coin =>
          if ρ.slot j.1 ∈ (localH H mk).withheld then none
          else
            some (B.dviewT (Ts j) (y0, (as j).2.1)
                (Strat.run ((localH H mk).one w0 (as j).1 (as j).2.2 ((), c)) (ρ.slot j.1)).1)) =
        fun _ => none :=
      funext fun c => if_pos ((BatchSeqZk.local_withheld H mk _).mpr hw)
    rw [this]
    exact PMF.map_const _ _
  · have hw' : ρ.slot j.1 ∉ H.withheld (mk w0 (as j).2.2) (as j).1 := fun h => h.elim hw fun h => by
      rw [hH] at h
      exact h
    rw [H.output_of_not_mem (Ts j) hw', PMF.map_comp]
    refine congrArg (fun φ => PMF.map φ _) (funext fun c => ?_)
    refine (if_neg fun h => hw ((BatchSeqZk.local_withheld H mk _).mp h)).trans ?_
    rw [BatchSeqZk.local_run, BatchSeqZk.dviewT_eq, Strat.rho_run]
    rfl

/-! ## 3. An IOR run by the shared part alone -/

namespace BatchSeqZk
open IOR OnlineHon

section Shared
variable {X X' : Type} {E0 Ej Eo : ExtSpec} (R : IOR X (E0.prod Ej) X' Eo) {W0 Wj W0' Wj' : Type}
  (Coin : Type) [Fintype Coin] [Nonempty Coin] (s0 : W0 → Coin → Strat R.shape W0')
  (nx : X → Wj → X' × Wj') (Bad0 : Set (Rho R.shape))

theorem shared_withheld (ρ : Rho R.shape) :
    ρ ∈ (sharedH R Coin s0 nx Bad0).withheld ↔ ρ ∈ Bad0 := by
  classical
  show ((Rho.lo (RoundSplits.const (RAnn.ofShared .sh) R.shape) ρ ∈ (∅ : Set _)) ∨
      decide (RhoSh.all R.shape (Rho.sh (RoundSplits.const (RAnn.ofShared .sh) R.shape) ρ) ∈ Bad0) =
        true) ↔
    _
  rw [RhoSh.all_sh, decide_eq_true_eq]
  exact ⟨fun h => h.elim (fun h => h.elim) id, Or.inr⟩

theorem shared_run (w0 : W0) (x : X) (wj : Wj) (c : Coin × Unit) (ρ : Rho R.shape) :
    Strat.run ((sharedH R Coin s0 nx Bad0).one w0 x wj c) ρ =
      (((s0 w0 c.1).run ρ).1, (((s0 w0 c.1).run ρ).2, nx x wj)) := by
  show Strat.run (SStratR.zip (SStratR.ofStrat (s0 w0 c.1)) (LStratR.mute R.shape (nx x wj))) ρ = _
  rw [SStratR.zip_ofStrat_mute, Strat.run_map]

end Shared

/-- With shared rounds only, all slots see the same verifier messages. -/
theorem slot_eq {N : ℕ} {s : Shape} (ρ : BRho N s (RoundSplits.const (RAnn.ofShared .sh) s)) (j : Fin N) :
    ρ.slot j = RhoSh.all s (BRho.shared ρ) := by
  rw [← BRho.sh_slot_shared j ρ, RhoSh.all_sh]

section Merge
variable {X X' : Type} {Ei Eo : ExtSpec} (R : IOR X Ei X' Eo)

open Classical in
/-- what is given for some slot -/
def merge {ι : Type} {E : ExtSpec} (as : ι → E.Pos → Option E.Sym) :
    E.Pos → Option E.Sym :=
  fun q => if h : ∃ j, (as j q).isSome = true then as h.choose q else none

open Classical in
/-- of a view, what is shown at ρ with the further positions T -/
def restrict (ρ : Rho R.shape) (T : Finset (OPos R.shape)) (V : View R) : View R :=
  ⟨V.plains, fun p => if R.Shown ρ T p then V.orc p else none⟩

theorem restrict_view {T T' : Finset (OPos R.shape)} (h : T ⊆ T') (τ : Tr R.shape) :
    restrict R τ.rho T (R.view T' τ) = R.view T τ := by
  classical
  refine View.ext' rfl (funext fun p => ?_)
  by_cases hp : R.Shown τ.rho T p
  · refine (if_pos hp).trans ?_
    rw [view_orc_of_shown T τ hp,
      view_orc_of_shown T' τ (hp.imp id fun h' => h'.imp (fun h'' => h h'') id)]
  · exact (if_neg hp).trans (view_orc_of_not_shown T τ hp).symm

end Merge

open Classical in
/-- Under `hE`, `hT`, at one `ρ`, with a slot `j0`: what is given for the slots of `ι`, all of it
in the shared oracles, is what is given at the union of the further positions. -/
theorem merge_ans {X X' : Type} {E0 Ej Eo : ExtSpec} (R : IOR X (E0.prod Ej) X' Eo)
    (hE : ∀ ρ q, q ∈ R.extReads ρ → q.isLeft = true) (hT : ∀ ρ p q, q ∈ R.tie ρ p → q.isLeft = true)
    {ι : Type} [Fintype ι] (ρ : Rho R.shape) (Ts : ι → Finset (OPos R.shape)) (y0 : E0.Str)
    (own : ι → Ej.Str) (j0 : ι) :
    merge (fun j => (E0.prod Ej).ans (R.given ρ (Ts j)) (y0, own j)) =
      (E0.prod Ej).ans (R.given ρ (Finset.univ.biUnion Ts)) (y0, own j0) := by
  funext q
  have hleft : ∀ T, q ∈ R.given ρ T → q.isLeft = true := fun T hq => by
    rcases IOR.mem_given.1 hq with h | ⟨p, _, h⟩
    · exact hE ρ q h
    · exact hT ρ p q h
  have hsame : ∀ j j', q.isLeft = true →
      (E0.prod Ej).rd (y0, own j) q = (E0.prod Ej).rd (y0, own j') q := fun j j' h => by
    cases q with
    | inl q => rfl
    | inr q => cases h
  by_cases hq : q ∈ R.given ρ (Finset.univ.biUnion Ts)
  · have hex : ∃ j, ((E0.prod Ej).ans (R.given ρ (Ts j)) (y0, own j) q).isSome = true := by
      rcases IOR.mem_given.1 hq with h | ⟨p, hp, h⟩
      · exact ⟨j0, by rw [(E0.prod Ej).ans_of_mem _ (IOR.mem_given.2 (Or.inl h))]; rfl⟩
      · rcases hp with hp | hp
        · exact ⟨j0,
            by rw [(E0.prod Ej).ans_of_mem _ (IOR.mem_given.2 (Or.inr ⟨p, Or.inl hp, h⟩))]; rfl⟩
        · obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.1 hp
          exact ⟨j, by
              rw [(E0.prod Ej).ans_of_mem _ (IOR.mem_given.2 (Or.inr ⟨p, Or.inr hj, h⟩))]; rfl⟩
    refine (dif_pos hex).trans ?_
    have hm : q ∈ R.given ρ (Ts hex.choose) := by
      by_contra hn
      have h := hex.choose_spec
      rw [(E0.prod Ej).ans_of_not_mem _ hn] at h
      cases h
    show (E0.prod Ej).ans (R.given ρ (Ts hex.choose)) (y0, own hex.choose) q = _
    rw [(E0.prod Ej).ans_of_mem _ hm, (E0.prod Ej).ans_of_mem _ hq, hsame _ j0 (hleft _ hq)]
  · have hnex : ¬ ∃ j, ((E0.prod Ej).ans (R.given ρ (Ts j)) (y0, own j) q).isSome = true := by
      rintro ⟨j, hj⟩
      have hm : q ∈ R.given ρ (Ts j) := by
        by_contra hn
        rw [(E0.prod Ej).ans_of_not_mem _ hn] at hj
        cases hj
      refine hq ?_
      rcases IOR.mem_given.1 hm with h | ⟨p, hp, h⟩
      · exact IOR.mem_given.2 (Or.inl h)
      · exact IOR.mem_given.2
          (Or.inr ⟨p, hp.imp id fun h' => Finset.mem_biUnion.2 ⟨j, Finset.mem_univ j, h'⟩, h⟩)
    exact (dif_neg hnex).trans ((E0.prod Ej).ans_of_not_mem _ hq).symm

end BatchSeqZk

theorem accB_shared : Spec.accB_shared := by
  intro X X' E0 Ej Eo R Wi Wo W0 Wj W0' Wj' H s0 nx mk mk' Ri Ro hA hH hrun x y w c ρ hR hρ
  have h1 : ρ ∉
      H.withheld (mk w.1 w.2)
        x := fun h => h.elim (fun h =>
          hρ ((BatchSeqZk.shared_withheld R H.Coin s0 nx H.Bad ρ).mpr h)) fun h => by
    rw [hH] at h
    exact h
  have h2 := hA x y (mk w.1 w.2) c.1 ρ hR h1
  rw [hrun x y w.1 w.2 c.1 ρ hR] at h2
  rw [BatchSeqZk.shared_run]
  exact h2

open Classical in
theorem exactB_shared : Spec.exactB_shared := by
  intro X X' E0 Ej Eo R Wi Wo W0 Wj W0' Wj' H s0 nx mk Ri bud N hE hH hrun hEx hTie
  obtain ⟨S, hS⟩ := hE
  refine ⟨fun J xs ρs Ts as =>
      if h : Nonempty J then
        (S (xs (Classical.choice h)) (ρs (Classical.choice h))
            (Finset.univ.biUnion Ts) (BatchSeqZk.merge as)).map
          fun o j => o.map (BatchSeqZk.restrict R (ρs j) (Ts j)) else PMF.pure fun _ => none,
    ?_⟩
  intro w0 y0 a ha J as has ρ Ts hbud
  by_cases hJ : Nonempty J
  · beta_reduce
    rw [dif_pos hJ]
    generalize Classical.choice hJ = j0
    rw [BatchSeqZk.outputL_eq (sharedH (Wj' := Wj') R H.Coin s0 nx H.Bad) w0 a ρ J Ts as has]
    simp only [BatchSeqZk.slot_eq ρ] at hbud ⊢
    generalize RhoSh.all R.shape (BRho.shared ρ) = ρ' at hbud ⊢
    rw [BatchSeqZk.merge_ans R hEx hTie ρ' Ts y0 (fun j => (as j).2.1) j0]
    rw [← hS (as j0).1 (y0, (as j0).2.1) (mk w0 (as j0).2.2) (ha j0.1 (as j0) (has j0)) ρ'
        (by rw [hH]; exact fun h => h) _ (hbud j0)]
    by_cases hw : ρ' ∈ H.Bad
    · rw [H.output_of_mem _ (Or.inl hw), PMF.pure_map]
      have : (fun (c : H.Coin × (Fin N → Unit)) (j : J) =>
            if ρ' ∈ (sharedH (Wj' := Wj') R H.Coin s0 nx H.Bad).withheld then none
            else
              some (R.view (Ts j)
                  (Strat.run
                    ((sharedH (Wj' := Wj') R H.Coin s0 nx H.Bad).one
                      w0 (as j).1 (as j).2.2 (c.1, c.2 j.1)) ρ').1)) =
          fun _ _ => none :=
        funext fun c =>
          funext fun j => if_pos ((BatchSeqZk.shared_withheld R H.Coin s0 nx H.Bad ρ').mpr hw)
      exact (congrArg (fun φ => PMF.map φ _) this).trans (PMF.map_const _ _)
    · have hw' : ρ' ∉ H.withheld (mk w0 (as j0).2.2) (as j0).1 := fun h => h.elim hw fun h => by
        rw [hH] at h
        exact h
      rw [H.output_of_not_mem _ hw', PMF.map_comp,
        ← map_fst_unif (C := H.Coin) (D := Fin N → Unit), PMF.map_comp]
      refine congrArg (fun φ => PMF.map φ _) (funext fun c => funext fun j => ?_)
      refine (if_neg fun h =>
        hw ((BatchSeqZk.shared_withheld R H.Coin s0 nx H.Bad ρ').mp h)).trans ?_
      rw [BatchSeqZk.shared_run]
      show some (R.view (Ts j) ((s0 w0 c.1).run ρ').1) =
        some (BatchSeqZk.restrict R ρ' (Ts j)
            (R.view (Finset.univ.biUnion Ts)
              ((H.strat (mk w0 (as j0).2.2) (as j0).1 c.1).run ρ').1))
      rw [hrun (as j0).1 (y0, (as j0).2.1) w0 (as j0).2.2 c.1 ρ' (ha j0.1 (as j0) (has j0))]
      have hr : ((s0 w0 c.1).run ρ').1.rho = ρ' := Strat.rho_run _ _
      have h3 := BatchSeqZk.restrict_view R (T := Ts j) (T' := Finset.univ.biUnion Ts)
        (fun p hp => Finset.mem_biUnion.2 ⟨j, Finset.mem_univ j, hp⟩) ((s0 w0 c.1).run ρ').1
      rw [hr] at h3
      rw [h3]
  · haveI : IsEmpty J := not_nonempty_iff.mp hJ
    exact BatchOne.pmf_subsingleton _ _

/-! ## 4. The composed budget at "no further reads" -/

open Classical in
/-- At no further reads the first simulator is run at the sources of what Q's verifier reads
(`extReads`), if Q's verifier reads all that is tied to its positions (`ht`: `IOR.Tied`,
Ior/Batch.lean). -/
theorem firstT_empty {X X' : Type} {Ei Eo : ExtSpec} (R : IOR X Ei X' Eo) (Q : BIOP X' Eo)
    (ht : Q.ior.Tied) (ρ : Rho (R.shape ++ Q.ior.shape)) :
    IOR.firstT R Q.ior ρ ∅ =
      (Q.ior.extReads (Rho.snd (s := R.shape) ρ)).biUnion (R.srcO (Rho.fst ρ)) := by
  unfold IOR.firstT
  rw [show IOR.partL (s := R.shape) (t := Q.ior.shape) ∅ = ∅ from Finset.preimage_empty,
    show IOR.partR R.shape (t := Q.ior.shape) ∅ = ∅ from Finset.preimage_empty,
    Finset.empty_union, OnlineHon.given_empty Q ht]

open Classical in
/-- The composed budget at "no further reads". -/
theorem budSeqB_empty_iff {X X' : Type} {E0 Ej E0' Ej' : ExtSpec}
    (R : IOR X (E0.prod Ej) X' (E0'.prod Ej')) (Q : BIOP X' (E0'.prod Ej')) {N : ℕ}
    (bR : BudB R.shape N) (bQ : BudB Q.ior.shape N) (ht : Q.ior.Tied) (J : Finset (Fin N))
    (ρs : J → Rho (R.shape ++ Q.ior.shape)) :
    budSeqB R Q bR bQ J ρs (fun _ => ∅) ↔
    bR J (fun j => Rho.fst (ρs j)) (fun j =>
      (Q.ior.extReads (Rho.snd (s := R.shape) (ρs j))).biUnion (R.srcO (Rho.fst (ρs j)))) ∧
    ∀ (J' : Finset (Fin N)) (h : J' ⊆ J),
      bQ J' (fun j => Rho.snd (s := R.shape) (ρs ⟨j.1, h j.2⟩)) (fun _ => ∅) := by
  unfold budSeqB
  simp only [firstT_empty R Q ht,
    show IOR.partR R.shape (t := Q.ior.shape) ∅ = ∅ from Finset.preimage_empty]

end Iop
