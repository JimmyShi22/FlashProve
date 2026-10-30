-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Ior/LinkVMaskedRulesSeq.lean: the proofs of `Iop.Spec.freshV_seq` and `Iop.Spec.freshV_snd`
(Ior/LinkVMaskedRules.lean): FreshV through "a link, then a link".

In standard terms: composition rules for interactive oracle reductions that run on a batch of
instances.

The notions (`HonestV.FreshV`, `HonestV.BlindV`; batch link, slot): the heads of
Ior/LinkVMasked.lean and Ior/LinkVMaskedRules.lean.

How: as for one instance (Ior/KnowCollRulesMaskProofs.lean: `fresh_seq`, `fresh_snd`), for
families.
`freshV_seq`: the tuple of the composition is determined, in the same way on both sides, by (the
tuple of the first link, the second link's coins): the second link does not look at the masks, so
from two runs of the first link whose readings differ by an overwriting it goes on with the same
messages and explicit parts, and readings that differ by the same overwriting.
`freshV_snd`: the first link's coins are fixed; the slots that it does not withhold hand on
statements of the middle relation with one shared witness; the second link's FreshV is used for
the set of these slots; the tuple of the composition is determined by the second link's tuple.
A slot that one of the two links withholds shows the notice on both sides.

Limits: see Limits in the head of Ior/LinkVMaskedRules.lean.
-/
import Ior.LinkVMaskedRulesProofs

set_option autoImplicit false

namespace Iop
open Prob
open scoped ENNReal

namespace LinkVSeq
open IOR OnlineHon BatchSeqZk MaskKit

/-- the coins of "a link, then a link" -/
def coinE (ι C0 D0 C D : Type) : (C0 × (ι → C)) × (D0 × (ι → D)) ≃ (C0 × D0) × (ι → C × D) where
  toFun := fun p => ((p.1.1, p.2.1), fun i => (p.1.2 i, p.2.2 i))
  invFun := fun c => ((c.1.1, fun i => (c.2 i).1), (c.1.2, fun i => (c.2 i).2))
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

variable {X X' X'' : Type} {Ei Eo Eo' : ExtSpec} {R₁ : IOR X Ei X' Eo} {R₂ : IOR X' Eo X'' Eo'}
  {A₁ : RoundSplits R₁.shape} {A₂ : RoundSplits R₂.shape} {W0 Wj W0' Wj' W0'' Wj'' : Type}

/-- the shared witness with which the composition ends -/
theorem res_seqV (H₁ : R₁.HonestV A₁ W0 Wj W0' Wj') (H₂ : R₂.HonestV A₂ W0' Wj' W0'' Wj'') {N : ℕ}
    (w0 : W0) (c0 : H₁.Coin0) (d0 : H₂.Coin0) (ρ : BRho N (R₁.shape ++ R₂.shape) (RoundSplits.app A₁ A₂)) :
    ((H₁.seqV H₂).strat0 w0 (c0, d0)).res (BRho.shared ρ) =
      (H₂.strat0 ((H₁.strat0 w0 c0).res (BRho.shared (BRho.fstA A₁ A₂ ρ))) d0).res
        (BRho.shared (BRho.sndA A₁ A₂ ρ)) := by
  show ((H₁.strat0 w0 c0).bindR fun w0' => H₂.strat0 w0' d0).res (BRho.shared ρ) = _
  rw [SStratR.res_bindR, BRho.shared_fstA, BRho.shared_sndA]

/-- the shared witness that a slot computes for itself is the shared part's result -/
theorem one_shared (H₁ : R₁.HonestV A₁ W0 Wj W0' Wj') {N : ℕ} (w0 : W0) (x : X) (wj : Wj)
    (c : H₁.Coin0 × H₁.Coin) (ρ : BRho N R₁.shape A₁) (j : Fin N) :
    ((H₁.one w0 x wj c).run (ρ.slot j)).2.1 = (H₁.strat0 w0 c.1).res (BRho.shared ρ) := by
  show ((SStratR.zip (H₁.strat0 w0 c.1) (H₁.strat w0 c.1 x wj c.2)).run (ρ.slot j)).2.1 = _
  rw [SStratR.res_zip, BRho.sh_slot_shared]

end LinkVSeq

open IOR LinkVSeq MaskKit

open Classical in
theorem freshV_seq : Spec.freshV_seq := by
  intro X X' X'' Ei Eo Eo' R₁ R₂ A₁ A₂ W0 Wj W0' Wj' W0'' Wj'' H₁ H₂ Ra N b₁ b₂ K0 Kj K0' Kj' k0 kj
    k0' kj' M0 _ _ Mj _ _ put0 putj put0' putj' hF hB w0 J as ha
    (ρ : BRho N (R₁.shape ++ R₂.shape) (RoundSplits.app A₁ A₂)) Ts hbud
  have hslot1 : (fun j : J => (BRho.fstA A₁ A₂ ρ).slot j.1) = fun j => Rho.fst (ρ.slot j.1) :=
    funext fun j => BRho.slot_fstA j.1 A₁ A₂ ρ
  have e := hF w0 J as ha (BRho.fstA A₁ A₂ ρ)
    (fun j => firstT R₁ R₂ (ρ.slot j.1) (Ts j)) (by rw [hslot1]; exact hbud.1)
  let seen₁ := H₁.seenV k0 kj w0 J (fun j => ((as j).1, (as j).2.2)) (BRho.fstA A₁ A₂ ρ)
    (fun j => firstT R₁ R₂ (ρ.slot j.1) (Ts j))
  let seenS := (H₁.seqV H₂).seenV k0' kj' w0 J (fun j => ((as j).1, (as j).2.2)) ρ Ts
  let eC := coinE (Fin N) H₁.Coin0 H₂.Coin0 H₁.Coin H₂.Coin
  have hg : (unif (((H₁.Coin0 × (Fin N → H₁.Coin)) × (H₂.Coin0 × (Fin N → H₂.Coin))) ×
            (M0 × (Fin N → Mj)))).map
        (fun a => (HonestV.overV put0 putj a.2 (seen₁ a.1.1), a.1.2)) =
      (unif ((H₁.Coin0 × (Fin N → H₁.Coin)) × (H₂.Coin0 × (Fin N → H₂.Coin)))).map
        (fun c => (seen₁ c.1, c.2)) := by
    rw [← map_pair_indep (β := H₂.Coin0 × (Fin N → H₂.Coin)) _ _ e]
    exact map_unif_of_equiv
      (⟨fun a => ((a.1.1, a.2), a.1.2), fun b => ((b.1.1, b.2), b.1.2),
        fun _ => rfl, fun _ => rfl⟩ : ((H₁.Coin0 × (Fin N → H₁.Coin)) ×
              (H₂.Coin0 × (Fin N → H₂.Coin))) ×
            (M0 × (Fin N → Mj)) ≃
          ((H₁.Coin0 × (Fin N → H₁.Coin)) × (M0 × (Fin N → Mj))) × (H₂.Coin0 × (Fin N → H₂.Coin)))
      (fun a : ((H₁.Coin0 × (Fin N → H₁.Coin)) × (M0 × (Fin N → Mj))) ×
        (H₂.Coin0 × (Fin N → H₂.Coin)) => (HonestV.overV put0 putj a.1.2 (seen₁ a.1.1), a.2))
  refine (map_unif_of_equiv (eC.prodCongr (Equiv.refl (M0 × (Fin N → Mj))))
      (fun a => HonestV.overV put0' putj' a.2 (seenS a.1))).symm.trans
    (Eq.trans ?_ (map_unif_of_equiv eC seenS))
  refine map_eq_of_factor _ _ ?_ hg
  rintro ⟨⟨c, d⟩, M⟩ ⟨c', d'⟩ h
  have g4 : d = d' := congrArg (fun z => z.2) h
  subst g4
  have h1 : HonestV.overV put0 putj M (seen₁ c) = seen₁ c' := congrArg (fun z => z.1) h
  have g0 : put0 M.1 (k0 ((H₁.strat0 w0 c.1).res (BRho.shared (BRho.fstA A₁ A₂ ρ)))) =
      k0 ((H₁.strat0 w0 c'.1).res (BRho.shared (BRho.fstA A₁ A₂ ρ))) :=
    congrArg Prod.snd h1
  show HonestV.overV put0' putj' M (seenS ((c.1, d.1), fun i => (c.2 i, d.2 i))) =
    seenS ((c'.1, d.1), fun i => (c'.2 i, d.2 i))
  refine Prod.ext (funext fun j => ?_) ?_
  · have gj := congrFun (congrArg Prod.fst h1) j
    show Option.map _ (ite (ρ.slot j.1 ∈ (H₁.seqV H₂).withheld) _ _) =
      ite (ρ.slot j.1 ∈ (H₁.seqV H₂).withheld) _ _
    by_cases hw : ρ.slot j.1 ∈ (H₁.seqV H₂).withheld
    · rw [if_pos hw, if_pos hw]
      rfl
    · rw [if_neg hw, if_neg hw]
      have hw₁ : (BRho.fstA A₁ A₂ ρ).slot j.1 ∉ H₁.withheld := fun h' =>
        hw ((mem_withheld H₁ H₂ _).mpr (Or.inl (by rw [← BRho.slot_fstA]; exact h')))
      have gj' : Option.map _ (ite ((BRho.fstA A₁ A₂ ρ).slot j.1 ∈ H₁.withheld) _ _) =
          ite ((BRho.fstA A₁ A₂ ρ).slot j.1 ∈ H₁.withheld) _ _ := gj
      rw [if_neg hw₁, if_neg hw₁, Option.map_some] at gj'
      have gq := Option.some.inj gj'
      simp only [BRho.slot_fstA] at gq
      have g1 : R₁.view (firstT R₁ R₂ (ρ.slot j.1) (Ts j))
            ((H₁.one w0 (as j).1 (as j).2.2 (c.1, c.2 j.1)).run (Rho.fst (ρ.slot j.1))).1 =
          R₁.view (firstT R₁ R₂ (ρ.slot j.1) (Ts j))
            ((H₁.one w0 (as j).1 (as j).2.2 (c'.1, c'.2 j.1)).run (Rho.fst (ρ.slot j.1))).1 :=
        congrArg (fun z => z.1) gq
      have g2 : ((H₁.one w0 (as j).1 (as j).2.2 (c.1, c.2 j.1)).run (Rho.fst (ρ.slot j.1))).2.2.1 =
          ((H₁.one w0 (as j).1 (as j).2.2 (c'.1, c'.2 j.1)).run (Rho.fst (ρ.slot j.1))).2.2.1 :=
        congrArg (fun z => z.2.1) gq
      have g3 : putj (M.2 j.1)
            (kj ((H₁.one w0 (as j).1 (as j).2.2 (c.1, c.2 j.1)).run (Rho.fst (ρ.slot j.1))).2.2.2) =
          kj ((H₁.one w0 (as j).1 (as j).2.2 (c'.1, c'.2 j.1)).run (Rho.fst (ρ.slot j.1))).2.2.2 :=
        congrArg (fun z => z.2.2) gq
      have s1 : ∀ cc : H₁.Coin0 × (Fin N → H₁.Coin),
          ((H₁.one w0 (as j).1 (as j).2.2 (cc.1, cc.2 j.1)).run (Rho.fst (ρ.slot j.1))).2.1 =
            (H₁.strat0 w0 cc.1).res (BRho.shared (BRho.fstA A₁ A₂ ρ)) := fun cc => by
        rw [← BRho.slot_fstA]
        exact one_shared H₁ w0 _ _ _ _ j.1
      obtain ⟨b1, b2, b3⟩ := hB.slot
        ((H₁.one w0 (as j).1 (as j).2.2 (c.1, c.2 j.1)).run (Rho.fst (ρ.slot j.1))).2.1
        ((H₁.one w0 (as j).1 (as j).2.2 (c'.1, c'.2 j.1)).run (Rho.fst (ρ.slot j.1))).2.1
        ((H₁.one w0 (as j).1 (as j).2.2 (c.1, c.2 j.1)).run (Rho.fst (ρ.slot j.1))).2.2.2
        ((H₁.one w0 (as j).1 (as j).2.2 (c'.1, c'.2 j.1)).run (Rho.fst (ρ.slot j.1))).2.2.2 M.1
        (M.2 j.1)
        ((H₁.one w0 (as j).1 (as j).2.2 (c'.1, c'.2 j.1)).run (Rho.fst (ρ.slot j.1))).2.2.1
        (d.1, d.2 j.1) (Rho.snd (s := R₁.shape) (ρ.slot j.1))
        (by rw [s1 c, s1 c']; exact g0.symm) g3.symm
      rw [Option.map_some]
      refine congrArg some ?_
      dsimp only
      erw [run_one H₁ H₂ w0 (as j).1 (as j).2.2 c.1 d.1 (c.2 j.1) (d.2 j.1) (ρ.slot j.1),
        run_one H₁ H₂ w0 (as j).1 (as j).2.2 c'.1 d.1 (c'.2 j.1) (d.2 j.1) (ρ.slot j.1)]
      dsimp only
      rw [g2, ← b2, ← b3]
      refine congrArg (fun v => (v, _)) ?_
      exact view_app_of_views (ρ.slot j.1) (Ts j) (Strat.rho_run _ _) (Strat.rho_run _ _)
        (Strat.rho_run _ _) (Strat.rho_run _ _) g1 (congrArg _ b1.symm)
  · show put0' M.1 (k0' (((H₁.seqV H₂).strat0 w0 (c.1, d.1)).res (BRho.shared ρ))) =
      k0' (((H₁.seqV H₂).strat0 w0 (c'.1, d.1)).res (BRho.shared ρ))
    rw [res_seqV, res_seqV]
    exact (hB.shared _ _ M.1 d.1 _ g0.symm).symm

open Classical in
theorem freshV_snd : Spec.freshV_snd := by
  intro X X' X'' Ei Eo Eo' R₁ R₂ A₁ A₂ W0 Wj W0' Wj' W0'' Wj'' H₁ H₂ Ra Rb N b₁ b₂ K0 Kj k0 kj M0 _
    _ put0 Mj _ _ putj hA hF w0 J as ha (ρ : BRho N (R₁.shape ++ R₂.shape) (RoundSplits.app A₁ A₂)) Ts hbud
  let seenS := (H₁.seqV H₂).seenV k0 kj w0 J (fun j => ((as j).1, (as j).2.2)) ρ Ts
  let eC := coinE (Fin N) H₁.Coin0 H₂.Coin0 H₁.Coin H₂.Coin
  refine (map_unif_of_equiv (eC.prodCongr (Equiv.refl (M0 × (Fin N → Mj))))
      (fun a => HonestV.overV put0 putj a.2 (seenS a.1))).symm.trans
    (Eq.trans ?_ (map_unif_of_equiv eC seenS))
  refine (map_unif_of_equiv
    (Equiv.prodAssoc (H₁.Coin0 × (Fin N → H₁.Coin))
      (H₂.Coin0 × (Fin N → H₂.Coin)) (M0 × (Fin N → Mj))).symm
    (fun a : ((H₁.Coin0 × (Fin N → H₁.Coin)) × (H₂.Coin0 × (Fin N → H₂.Coin))) ×
      (M0 × (Fin N → Mj)) => HonestV.overV put0 putj a.2 (seenS (eC a.1)))).symm.trans ?_
  refine (map_unif_prod _).trans
    (Eq.trans ?_
      (map_unif_prod (α := H₁.Coin0 × (Fin N → H₁.Coin))
        (β := H₂.Coin0 × (Fin N → H₂.Coin)) _).symm)
  refine congrArg _ (funext fun c => ?_)
  -- the coins of the first link are fixed
  let r : J → Tr R₁.shape × W0' × X' × Wj' := fun j =>
    (H₁.one w0 (as j).1 (as j).2.2 (c.1, c.2 j.1)).run (Rho.fst (ρ.slot j.1))
  let w0' : W0' := (H₁.strat0 w0 c.1).res (BRho.shared (BRho.fstA A₁ A₂ ρ))
  have hw0 : ∀ j : J, (r j).2.1 = w0' := fun j => by
    show ((H₁.one w0 (as j).1 (as j).2.2 (c.1, c.2 j.1)).run (Rho.fst (ρ.slot j.1))).2.1 = _
    rw [← BRho.slot_fstA]
    exact one_shared H₁ w0 _ _ _ _ j.1
  have hRb : ∀ j : alive R₁ R₂ H₁.withheld J (fun j => ρ.slot j.1),
      Rb (r (up j)).2.2.1 (R₁.imp (as (up j)).2.1 (r (up j)).1)
        (w0', (r (up j)).2.2.2) := fun j => by
    have h := (hA (as (up j)).1 (as (up j)).2.1 (w0, (as (up j)).2.2) (c.1, c.2 (up j).1) _
      (ha (up j)) ((mem_alive (up j)).mp j.2)).2
    rw [← hw0 (up j)]
    exact h
  have hslot2 : (fun j : alive R₁ R₂ H₁.withheld J (fun j => ρ.slot j.1) =>
        (BRho.sndA A₁ A₂ ρ).slot j.1) =
      fun j => Rho.snd (s := R₁.shape) (ρ.slot (up j).1) :=
    funext fun j => BRho.slot_sndA j.1 A₁ A₂ ρ
  have e := hF w0' (alive R₁ R₂ H₁.withheld J (fun j => ρ.slot j.1))
    (fun j => ((r (up j)).2.2.1, R₁.imp (as (up j)).2.1 (r (up j)).1, (r (up j)).2.2.2)) hRb
    (BRho.sndA A₁ A₂ ρ) (fun j => partR R₁.shape (Ts (up j)))
    (by rw [hslot2]; exact hbud.2 _ fun j hj => alive_sub hj)
  refine map_eq_of_factor _ _ ?_ e
  rintro ⟨d, M⟩ d' h
  show HonestV.overV put0 putj M (seenS ((c.1, d.1), fun i => (c.2 i, d.2 i))) =
    seenS ((c.1, d'.1), fun i => (c.2 i, d'.2 i))
  refine Prod.ext (funext fun j => ?_) ?_
  · show Option.map _ (ite (ρ.slot j.1 ∈ (H₁.seqV H₂).withheld) _ _) =
      ite (ρ.slot j.1 ∈ (H₁.seqV H₂).withheld) _ _
    by_cases hw : ρ.slot j.1 ∈ (H₁.seqV H₂).withheld
    · rw [if_pos hw, if_pos hw]
      rfl
    · rw [if_neg hw, if_neg hw]
      have hj : j.1 ∈ alive R₁ R₂ H₁.withheld J (fun j => ρ.slot j.1) :=
        (mem_alive j).mpr fun h' => hw ((mem_withheld H₁ H₂ _).mpr (Or.inl h'))
      have hw₂ : (BRho.sndA A₁ A₂ ρ).slot j.1 ∉ H₂.withheld := fun h' =>
        hw ((mem_withheld H₁ H₂ _).mpr (Or.inr (by rw [← BRho.slot_sndA]; exact h')))
      have gj := congrFun (congrArg Prod.fst h) ⟨j.1, hj⟩
      have gj' : Option.map _ (ite ((BRho.sndA A₁ A₂ ρ).slot j.1 ∈ H₂.withheld) _ _) =
          ite ((BRho.sndA A₁ A₂ ρ).slot j.1 ∈ H₂.withheld) _ _ := gj
      rw [if_neg hw₂, if_neg hw₂, Option.map_some] at gj'
      have gq := Option.some.inj gj'
      simp only [BRho.slot_sndA] at gq
      have g1 : R₂.view (partR R₁.shape (Ts j))
            ((H₂.one w0' (r j).2.2.1 (r j).2.2.2 (d.1, d.2 j.1)).run
              (Rho.snd (s := R₁.shape) (ρ.slot j.1))).1 =
          R₂.view (partR R₁.shape (Ts j))
            ((H₂.one w0' (r j).2.2.1 (r j).2.2.2 (d'.1, d'.2 j.1)).run
              (Rho.snd (s := R₁.shape) (ρ.slot j.1))).1 :=
        congrArg (fun z => z.1) gq
      have g2 : ((H₂.one w0' (r j).2.2.1 (r j).2.2.2 (d.1, d.2 j.1)).run
            (Rho.snd (s := R₁.shape) (ρ.slot j.1))).2.2.1 =
          ((H₂.one w0' (r j).2.2.1 (r j).2.2.2 (d'.1, d'.2 j.1)).run
            (Rho.snd (s := R₁.shape) (ρ.slot j.1))).2.2.1 :=
        congrArg (fun z => z.2.1) gq
      have g3 : putj (M.2 j.1)
            (kj ((H₂.one w0' (r j).2.2.1 (r j).2.2.2 (d.1, d.2 j.1)).run
                (Rho.snd (s := R₁.shape) (ρ.slot j.1))).2.2.2) =
          kj ((H₂.one w0' (r j).2.2.1 (r j).2.2.2 (d'.1, d'.2 j.1)).run
              (Rho.snd (s := R₁.shape) (ρ.slot j.1))).2.2.2 :=
        congrArg (fun z => z.2.2) gq
      rw [Option.map_some]
      refine congrArg some ?_
      dsimp only
      erw [run_one H₁ H₂ w0 (as j).1 (as j).2.2 c.1 d.1 (c.2 j.1) (d.2 j.1) (ρ.slot j.1),
        run_one H₁ H₂ w0 (as j).1 (as j).2.2 c.1 d'.1 (c.2 j.1) (d'.2 j.1) (ρ.slot j.1)]
      dsimp only
      have e0 : ((H₁.one w0 (as j).1 (as j).2.2 (c.1, c.2 j.1)).run (Rho.fst (ρ.slot j.1))).2.1 =
          w0' := hw0 j
      rw [e0]
      show (_, ((H₂.one w0' (r j).2.2.1 (r j).2.2.2 (d.1, d.2 j.1)).run
            (Rho.snd (s := R₁.shape) (ρ.slot j.1))).2.2.1,
          putj (M.2 j.1)
            (kj ((H₂.one w0' (r j).2.2.1 (r j).2.2.2 (d.1, d.2 j.1)).run
                (Rho.snd (s := R₁.shape) (ρ.slot j.1))).2.2.2)) = _
      rw [g2, g3]
      refine congrArg (fun v => (v, _)) ?_
      exact view_app_of_views (ρ.slot j.1) (Ts j) (Strat.rho_run _ _) (Strat.rho_run _ _)
        (Strat.rho_run _ _) (Strat.rho_run _ _) rfl g1
  · show put0 M.1 (k0 (((H₁.seqV H₂).strat0 w0 (c.1, d.1)).res (BRho.shared ρ))) =
      k0 (((H₁.seqV H₂).strat0 w0 (c.1, d'.1)).res (BRho.shared ρ))
    rw [res_seqV, res_seqV]
    exact congrArg Prod.snd h

end Iop
