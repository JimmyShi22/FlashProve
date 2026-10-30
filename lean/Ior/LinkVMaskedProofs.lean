-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Ior/LinkVMaskedProofs.lean: the proof of `Iop.Spec.exactV_seq_masked` (Ior/LinkVMasked.lean): a
prefix that is honest-verifier zero knowledge for sets of slots and fresh, then a masked link.
(not all hypotheses are named here: see its statement)

In standard terms: a composition rule for interactive oracle reductions that run on a batch of
instances.

Notions: the head of Ior/LinkVMasked.lean.

How: as for one instance (Ior/KnowCollRulesMaskProofs.lean), for families. What the whole shows to
the slots of J is a function G of (the prefix's coins c; what the link reads of the shared
witness; what it reads of the slots' witnesses): in each slot that the prefix does not withhold,
the link's plain parts in closed form, glued to the prefix's transcript in that slot. G depends on
c only through the prefix's views (at the further positions of "a link, then a link") and the
explicit parts handed on. The real run is the law over c of G c (the readings of the witnesses
handed on): the link's own coins do not matter. The simulator is, by exactness of the prefix and
the item "masked messages" for the set of the slots that are not withheld, the law over (c, M) of
G c (the readings with the own masks overwritten by M). `FreshV` says that the arguments of G have
the same law in both. No honest link is ever run after a simulated prefix.

Limits: see Limits in the head of Ior/LinkVMasked.lean.
-/
import Ior.LinkVMasked
import Ior.KnowCollRulesMaskProofs
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Iop
open Prob
open scoped ENNReal

namespace LinkVSeq
open IOR OnlineHon BatchSeqZk

variable {X X' X'' : Type} {Ei Eo Eo' : ExtSpec} {R₁ : IOR X Ei X' Eo} {R₂ : IOR X' Eo X'' Eo'}
  {A₁ : RoundSplits R₁.shape} {A₂ : RoundSplits R₂.shape} {W0 Wj W0' Wj' W0'' Wj'' : Type}

open Classical in
/-- What the whole shows to the slots of J, as a function of the prefix's coins and of what the
masked link reads. -/
def mGV (H₁ : R₁.HonestV A₁ W0 Wj W0' Wj') {N : ℕ} (D : MaskDataV R₂ W0' Wj' N)
    (h : IsEmpty (OPos R₂.shape)) (w0 : W0) (J : Finset (Fin N)) (as : J → X × Ei.Str × Wj)
    (ρs : J → Rho (R₁.shape ++ R₂.shape)) (Ts : J → Finset (OPos (R₁.shape ++ R₂.shape)))
    (c : H₁.Coin0 × (Fin N → H₁.Coin)) (k : D.K0) (κ : J → D.Kj) : J → Option (View (R₁.seq R₂)) :=
  fun j =>
    if Rho.fst (ρs j) ∈ H₁.withheld then none
    else
      glue R₁ R₂ (Rho.snd (s := R₁.shape) (ρs j)) (Ts j)
        ((H₁.one w0 (as j).1 (as j).2.2 (c.1, c.2 j.1)).run (Rho.fst (ρs j))).1
        (some (bareView h
            (D.msg k (κ j)
              (D.pub ((H₁.one w0 (as j).1 (as j).2.2 (c.1, c.2 j.1)).run (Rho.fst (ρs j))).2.2.1)
              (Rho.snd (s := R₁.shape) (ρs j)))))

open Classical in
theorem exactWith_seqV_masked (H₁ : R₁.HonestV A₁ W0 Wj W0' Wj')
    (H₂ : R₂.HonestV A₂ W0' Wj' W0'' Wj'') {Ra : X → Ei.Str → W0 × Wj → Prop}
    {Rb : X' → Eo.Str → W0' × Wj' → Prop} {N : ℕ} {b₁ : BudB R₁.shape N} (S₁ : R₁.SimV N)
    (D : MaskDataV R₂ W0' Wj' N) (m : H₂.MMV D) (hL : R₁.IsLocal) (hA : H₁.AccV Ra Rb)
    (hS₁ : H₁.ExactVWith N Ra b₁ S₁) (hF : H₁.FreshV N Ra b₁ D.k0 D.kj D.M0 D.put0 D.Mj D.putj)
    (hCl : ∀ x y w, Rb x y w → D.Cl (D.pub x) (D.k0 w.1) (D.kj w.2)) :
    (H₁.seqV H₂).ExactVWith N Ra (budSeqV R₁ R₂ b₁ fun _ _ _ => True)
      (sim R₁ R₂ H₁.withheld S₁ (D.simOwnV m.noOrc)) := by
  intro w0 J as ha (ρ : BRho N (R₁.shape ++ R₂.shape) (RoundSplits.app A₁ A₂)) Ts hbud
  -- the run of the prefix in slot j; the shared witness handed on
  let r : H₁.Coin0 × (Fin N → H₁.Coin) → J → Tr R₁.shape × W0' × X' × Wj' := fun c j =>
    (H₁.one w0 (as j).1 (as j).2.2 (c.1, c.2 j.1)).run (Rho.fst (ρ.slot j.1))
  let w0' : H₁.Coin0 × (Fin N → H₁.Coin) → W0' := fun c =>
    (H₁.strat0 w0 c.1).res (BRho.shared (BRho.fstA A₁ A₂ ρ))
  let G := mGV H₁ D m.noOrc w0 J as (fun j => ρ.slot j.1) Ts
  have hw0 : ∀ c (j : J), (r c j).2.1 = w0' c := fun c j => by
    show ((SStratR.zip (H₁.strat0 w0 c.1) (H₁.strat w0 c.1 (as j).1 (as j).2.2 (c.2 j.1))).run
        (Rho.fst (ρ.slot j.1))).2.1 = _
    rw [SStratR.res_zip, ← BRho.slot_fstA, BRho.sh_slot_shared]
  have hslot1 : (fun j : J => (BRho.fstA A₁ A₂ ρ).slot j.1) = fun j => Rho.fst (ρ.slot j.1) :=
    funext fun j => BRho.slot_fstA j.1 A₁ A₂ ρ
  -- the real run
  have L : (H₁.seqV H₂).output w0 J (fun j => ((as j).1, (as j).2.2)) ρ Ts =
      (unif (H₁.Coin0 × (Fin N → H₁.Coin))).map fun c =>
        G c (D.k0 (w0' c)) fun j => D.kj (r c j).2.2.2 := by
    unfold HonestV.output
    refine (law_split2 (fun c => G c (D.k0 (w0' c)) fun j => D.kj (r c j).2.2.2)
        _ PMF.pure fun c => ?_).trans
      (PMF.bind_pure _)
    refine Eq.trans (congrArg (fun φ => PMF.map φ _) (funext fun d => ?_)) (PMF.map_const _ _)
    funext j
    by_cases hw : Rho.fst (ρ.slot j.1) ∈ H₁.withheld
    · exact (if_pos ((mem_withheld H₁ H₂ _).mpr (Or.inl hw))).trans (if_pos hw).symm
    · refine (if_neg fun h => ((mem_withheld H₁ H₂ _).mp h).elim hw fun h' => ?_).trans
        (Eq.trans ?_ (if_neg hw).symm)
      · rw [m.free] at h'
        exact h'
      · have e := congrArg Prod.fst
          (run_one H₁ H₂ w0 (as j).1 (as j).2.2 c.1 d.1 (c.2 j.1) (d.2 j.1) (ρ.slot j.1))
        refine (congrArg (fun τ => some ((R₁.seq R₂).view (Ts j) τ)) e).trans ?_
        refine (glue_view (ρ.slot j.1) (Ts j) (Strat.rho_run _ _) (Strat.rho_run _ _)).symm.trans ?_
        rw [IOR.view_eq_bare R₂ m.noOrc,
          m.run _ _ _ _ _
            (hCl _ _ _ (hA (as j).1 (as j).2.1 (w0, (as j).2.2) (c.1, c.2 j.1) _ (ha j) hw).2)]
        show glue R₁ R₂ _ _ (r c j).1 (some (bareView m.noOrc (D.msg (D.k0 (r c j).2.1) _ _ _))) = _
        rw [hw0 c j]
  -- the simulator
  let hh : H₁.Coin0 × (Fin N → H₁.Coin) → J → Option (View R₁) := fun c j =>
    if Rho.fst (ρ.slot j.1) ∈ H₁.withheld then none
    else some (R₁.view (firstT R₁ R₂ (ρ.slot j.1) (Ts j)) (r c j).1)
  have hlaw : S₁ J (fun j => (as j).1) (fun j => Rho.fst (ρ.slot j.1))
        (fun j => firstT R₁ R₂ (ρ.slot j.1) (Ts j)) (fun j =>
          cut (R₁.given (Rho.fst (ρ.slot j.1)) (firstT R₁ R₂ (ρ.slot j.1) (Ts j)))
            (Ei.ans ((R₁.seq R₂).given (ρ.slot j.1) (Ts j)) (as j).2.1)) =
      (unif (H₁.Coin0 × (Fin N → H₁.Coin))).map hh := by
    have h := hS₁ w0 J as ha (BRho.fstA A₁ A₂ ρ)
      (fun j => firstT R₁ R₂ (ρ.slot j.1) (Ts j)) (by rw [hslot1]; exact hbud.1)
    unfold HonestV.output at h
    simp only [BRho.slot_fstA] at h
    exact Eq.trans
      (congrArg _ (funext fun j => cut_ans (given_first_subset (ρ.slot j.1) (Ts j)) (as j).2.1))
      h.symm
  have Rr : sim R₁ R₂ H₁.withheld S₁ (D.simOwnV m.noOrc) J (fun j => (as j).1) (fun j => ρ.slot j.1)
        Ts (fun j => Ei.ans ((R₁.seq R₂).given (ρ.slot j.1) (Ts j)) (as j).2.1) =
      (unif ((H₁.Coin0 × (Fin N → H₁.Coin)) × (D.M0 × (Fin N → D.Mj)))).map fun a =>
        G a.1 (D.put0 a.2.1 (D.k0 (w0' a.1))) fun j =>
            D.putj (a.2.2 j.1) (D.kj (r a.1 j).2.2.2) := by
    show PMF.bind
        (S₁ J (fun j => (as j).1) (fun j => Rho.fst (ρ.slot j.1))
          (fun j => firstT R₁ R₂ (ρ.slot j.1) (Ts j)) (fun j =>
            cut (R₁.given (Rho.fst (ρ.slot j.1)) (firstT R₁ R₂ (ρ.slot j.1) (Ts j)))
              (Ei.ans ((R₁.seq R₂).given (ρ.slot j.1) (Ts j)) (as j).2.1))) _ = _
    rw [hlaw, PMF.bind_map, map_unif_prod]
    refine congrArg _ (funext fun c => ?_)
    have hnw : ∀ j : J, j.1 ∈ alive R₁ R₂ H₁.withheld J (fun j => ρ.slot j.1) →
        Rho.fst (ρ.slot j.1) ∉ H₁.withheld :=
      fun j hj => (mem_alive j).mp hj
    have hacc : ∀ j : J, j.1 ∈ alive R₁ R₂ H₁.withheld J (fun j => ρ.slot j.1) →
        R₁.out (as j).1 (as j).2.1 (r c j).1 = some (r c j).2.2.1 ∧
        Rb (r c j).2.2.1 (R₁.imp (as j).2.1 (r c j).1) (w0' c, (r c j).2.2.2) := fun j hj => by
      have h := hA (as j).1 (as j).2.1 (w0, (as j).2.2) (c.1, c.2 j.1) _ (ha j) (hnw j hj)
      refine ⟨h.1, ?_⟩
      rw [← hw0 c j]
      exact h.2
    let g : alive R₁ R₂ H₁.withheld J (fun j => ρ.slot j.1) → Info R₁ R₂ := fun j =>
      ((r c (up j)).2.2.1,
        Eo.ans (R₂.given (Rho.snd (s := R₁.shape) (ρ.slot (up j).1)) (partR R₁.shape (Ts (up j))))
          (R₁.imp (as (up j)).2.1 (r c (up j)).1),
        glue R₁ R₂ (Rho.snd (s := R₁.shape) (ρ.slot (up j).1)) (Ts (up j)) (r c (up j)).1)
    have hseq : (seqOpt fun j : alive R₁ R₂ H₁.withheld J (fun j => ρ.slot j.1) =>
          info R₁ R₂ (as (up j)).1 (ρ.slot (up j).1) (Ts (up j))
            (Ei.ans ((R₁.seq R₂).given (ρ.slot (up j).1) (Ts (up j))) (as (up j)).2.1)
            (hh c (up j))) = some g := by
      refine seqOpt_some _ _ fun j => ?_
      have e : hh c (up j) =
          some (R₁.view (firstT R₁ R₂ (ρ.slot (up j).1) (Ts (up j))) (r c (up j)).1) :=
        if_neg (hnw (up j) j.2)
      rw [e]
      exact info_view R₁ R₂ hL _ _ _ _ _ (Strat.rho_run _ _) _ (hacc (up j) j.2).1
    refine (kern_of_some R₁ R₂ H₁.withheld (D.simOwnV m.noOrc) J (fun j => (as j).1)
      (fun j => ρ.slot j.1) Ts
      (fun j => Ei.ans ((R₁.seq R₂).given (ρ.slot j.1) (Ts j)) (as j).2.1) (hh c) g hseq).trans ?_
    have hslot2 : (fun j : alive R₁ R₂ H₁.withheld J (fun j => ρ.slot j.1) =>
          (BRho.sndA A₁ A₂ ρ).slot j.1) =
        fun j => Rho.snd (s := R₁.shape) (ρ.slot (up j).1) :=
      funext fun j => BRho.slot_sndA j.1 A₁ A₂ ρ
    have hlaw2 := m.law (alive R₁ R₂ H₁.withheld J (fun j => ρ.slot j.1)) (D.k0 (w0' c))
      (fun j => D.kj (r c (up j)).2.2.2) (fun j => D.pub (r c (up j)).2.2.1) (BRho.sndA A₁ A₂ ρ)
      (fun j => hCl _ _ _ (hacc (up j) j.2).2)
    rw [hslot2] at hlaw2
    show PMF.map _
        (PMF.map _
          (D.sim _ (fun j => D.pub (r c (up j)).2.2.1) fun j =>
            Rho.snd (s := R₁.shape) (ρ.slot (up j).1))) = _
    rw [← hlaw2, PMF.map_comp, PMF.map_comp]
    refine congrArg (fun φ => PMF.map φ _) (funext fun M => funext fun j => ?_)
    by_cases hj : j.1 ∈ alive R₁ R₂ H₁.withheld J (fun j => ρ.slot j.1)
    · refine (dif_pos hj).trans (Eq.trans ?_ (if_neg (hnw j hj)).symm)
      simp only [BRho.slot_sndA]
      rfl
    · exact (dif_neg hj).trans (if_pos (not_not.mp fun h => hj ((mem_alive j).mpr h))).symm
  -- the two have the same law
  refine L.trans (Eq.trans ?_ Rr.symm)
  have hFr := hF w0 J as ha (BRho.fstA A₁ A₂ ρ)
    (fun j => firstT R₁ R₂ (ρ.slot j.1) (Ts j)) (by rw [hslot1]; exact hbud.1)
  refine (map_eq_of_factor _ _ ?_ hFr).symm
  intro a c' hg
  have g0 : D.put0 a.2.1 (D.k0 (w0' a.1)) = D.k0 (w0' c') := congrArg Prod.snd hg
  funext j
  have gj := congrFun (congrArg Prod.fst hg) j
  unfold HonestV.overV HonestV.seenV at gj
  simp only [BRho.slot_fstA] at gj
  show mGV H₁ D m.noOrc w0 J as (fun j => ρ.slot j.1) Ts a.1 _ _ j =
    mGV H₁ D m.noOrc w0 J as (fun j => ρ.slot j.1) Ts c' _ _ j
  unfold mGV
  by_cases hw : Rho.fst (ρ.slot j.1) ∈ H₁.withheld
  · rw [if_pos hw, if_pos hw]
  · rw [if_neg hw, if_neg hw]
    rw [if_neg hw, if_neg hw, Option.map_some] at gj
    have gj' := Option.some.inj gj
    have g1 : R₁.view (firstT R₁ R₂ (ρ.slot j.1) (Ts j)) (r a.1 j).1 =
        R₁.view (firstT R₁ R₂ (ρ.slot j.1) (Ts j)) (r c' j).1 :=
      congrArg (fun z => z.1) gj'
    have g2 : (r a.1 j).2.2.1 = (r c' j).2.2.1 := congrArg (fun z => z.2.1) gj'
    have g3 : D.putj (a.2.2 j.1) (D.kj (r a.1 j).2.2.2) = D.kj (r c' j).2.2.2 :=
      congrArg (fun z => z.2.2) gj'
    show glue R₁ R₂ _ _ (r a.1 j).1
        (some (bareView m.noOrc (D.msg _ _ (D.pub (r a.1 j).2.2.1) _))) =
      glue R₁ R₂ _ _ (r c' j).1 (some (bareView m.noOrc (D.msg _ _ (D.pub (r c' j).2.2.1) _)))
    rw [glue_left_congr (ρ.slot j.1) (Ts j) (Strat.rho_run _ _) (Strat.rho_run _ _) g1, g2]
    beta_reduce
    rw [g3, g0]

end LinkVSeq

theorem exactV_seq_masked :
    Spec.exactV_seq_masked := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H₁ H₂ _ _ _ _ S₁ D m hL hA hS₁ hF hCl =>
  LinkVSeq.exactWith_seqV_masked H₁ H₂ S₁ D m hL hA hS₁ hF hCl

end Iop
