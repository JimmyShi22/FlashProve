-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdTowerProofs.lean: proofs of the statements of Cb/Ld/LdTower.lean (a proximity test beyond
unique decoding, put together from folds, code switches and an end block (the base case is one)).
Many statements of this library are written twice: a definition in the namespace `Spec` states a
proposition, and a theorem of the same name outside that namespace proves it (lean/GLOSSARY.md).

Eight of the fourteen "Spec.name" there are "theorem name" here; the other six are "theorem name_of"
here, from a hypothesis (below). The proofs combine: the rules for pieces and tails
(Cb/Ld/LdTowerKit.lean), the two blocks' own bundles, and for each block what it reads, ties and
bears, read off its definition.
Two theorems are stated here "from the block's own theorem": `ldTower_switch_of` takes
`Spec.ldSwitch_goodT` (Cb/Ld/LdSwitch.lean), `ldTower_base_of` takes `Spec.ldBase_good`
(Cb/Ld/LdBase.lean) as a hypothesis; the four theorems that use the first (`ldTower_stage_of`,
`ldTower_tail_of`, `ldTower_end_of`, `ldTower_run_of`) take `Spec.ldSwitch_goodT` as a hypothesis in
the same way. Cb/Ld/LdTowerMain.lean puts the hypotheses in.

Main names, each under the hypotheses of its statement (Cb/Ld/LdTower.lean; each `…_of` also from
the hypothesis named above):
  `ldTower_seq`, `ldTower_cons`: under the hypotheses of their statements, blocks compose
    (`LdBlock.seq`, `LdBlock.cons`).
  `ldTower_place`: where each kind of coordinate lands.
  `ldTower_split`: for P not empty, cutting the form is a piece, and changes neither claim nor word
    nor witness (word and witness: by the definition `ldSplit`).
  `ldTower_cutThen`: cut, then G (P not empty): OK as G is; the same rounds, the same errors.
  `ldTower_switch_of`: under `D.Hyp e' L t'`, P and P' not empty, the code switch is a piece: from
    at most t' long positions of the new word to at most D.t of the input word.
  `ldTower_base_of`: under `a.BaseHyp d bad L2`, the base case is a tail: at most t long positions
    of the input word.
  `ldTower_stage_of`: fold, then code switch, as one block.
  `ldTower_tail_of`: under `T.OK`, a tower is a tail of a chain.
  `ldTower_end_of`: what the whole test has: see the row of `Spec.ldTower_end` in the head of
    Cb/Ld/LdTower.lean.
  `ldTower_rounds`, `ldTower_err`: the number of rounds; the errors of a tower that begins with a
    stage: the stage's, then the rest's.
  `ldTower_run_of`: under `R.OK t'`, a run is a piece of a chain.
  `ldTower_run_rounds`: see its statement in Cb/Ld/LdTower.lean.

Limits: see the head of Cb/Ld/LdTower.lean.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdTower
import Ior.SeqProofs

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop IOR

/-- Membership in a union and in an image, whatever the instance that decides equality (definitions
made under "open Classical" carry another one than the types' own). -/
theorem mem_biUnion_at {α β : Type} (inst : DecidableEq β) {s : Finset α}
    {t : α → Finset β} {b : β} :
    b ∈ @Finset.biUnion α β inst s t ↔ ∃ a ∈ s, b ∈ t a :=
  Finset.mem_biUnion
theorem mem_image_at {α β : Type} (inst : DecidableEq β) {f : α → β} {s : Finset α} {b : β} :
    b ∈ @Finset.image α β inst f s ↔ ∃ a ∈ s, f a = b := Finset.mem_image

theorem ldTower_seq : Spec.ldTower_seq := fun _ _ _ _ _ _ B₁ B₂ _ _ _ h₁ h₂ =>
  pieceTr_seq _ _ _ _ _ _ _ B₁.R B₂.R _ _ _ B₁.H B₂.H _ _ _ B₁.ext B₂.ext 0 B₁.N B₂.N _ _ _ h₁ h₂

theorem ldTower_cons : Spec.ldTower_cons := fun _ _ _ _ _ B Z _ _ h₁ h₂ =>
  tailTr_cons _ _ _ _ _ _ B.R Z.R _ _ _ B.H Z.H _ _ _ B.ext Z.ext 0 B.N Z.N _ _ h₁ h₂

theorem ldTower_place : Spec.ldTower_place := fun _ _ _ _ _ _ _ _ _ _ _ =>
  ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

/-- a form is its two parts side by side, at the doubled state -/
theorem Slf.pair_left_right {E St J₁ J₂ : Type} (sl : Slf E St (J₁ ⊕ J₂)) (st : St) :
    sl.left.pair sl.right (st, st) = sl st := by
  funext j
  cases j <;> rfl

open Classical in
theorem ldTower_split : Spec.ldTower_split := by
  intro E P St _ _ _ _ C₁ C₂ sl e t
  have hH : ∀ (τ : E) (st : St) (m : C₁.J ⊕ C₂.J → E),
      (sl.left.pair sl.right).Holds (τ, (st, st)) m ↔ sl.Holds (τ, st) m := by
    intro τ st m
    unfold Slf.Holds
    rw [show sl.left.pair sl.right ((τ, (st, st)) : E × St × St).2 = sl st
        from Slf.pair_left_right sl st]
  refine ⟨?_, rfl, hH⟩
  have hp : ∀ h1 h2, (ldSplit C₁ C₂ sl e).OK t t := fun h1 h2 =>
    pieceTr_pure Unit (ldWhole C₁ C₂ sl e).X (ldCut C₁ C₂ sl e).X _ _ _ _ (ldWhole C₁ C₂ sl e).rels
      (ldCut C₁ C₂ sl e).rels (fun x => some (x.1, (x.2, x.2))) (ExtMap.id _)
      (fun xw => ((xw.1.1, (xw.1.2, xw.1.2)), xw.2)) (fun _ w => w) ((ldWhole C₁ C₂ sl e).atMost t)
      ((ldCut C₁ C₂ sl e).atMost t) h1 h2
  refine hp ?_ ?_
  · exact
      { isLocal := extMap_isLocal.1 _
        acc := fun x y w h => ⟨rfl, h.1, (hH x.1 x.2 w.1).2 h.2⟩
        onOut := fun _ _ _ _ _ => trivial
        keeps := fun _ _ => rfl
        know := fun x y x' w' _ hx h => by
          obtain rfl := Option.some.inj hx
          exact ⟨h.1, (hH x.1 x.2 w'.1).1 h.2⟩ }
  · intro U hU
    have e1 : U.biUnion (ExtMap.id (C₁.pair C₂).ext).src = U := by
      ext q
      constructor
      · intro h
        obtain ⟨u, hu, hq⟩ := (mem_biUnion_at _).1 h
        obtain rfl := Finset.mem_singleton.1 hq
        exact hu
      · intro h
        exact (mem_biUnion_at _).2 ⟨q, h, Finset.mem_singleton_self q⟩
    show (U.biUnion (ExtMap.id (C₁.pair C₂).ext).src).card ≤ t
    rw [e1]
    exact hU

open Classical in
/-- The code switch is a piece (`Spec.ldTower_switch`, with its hypotheses), from `hS`: the switch's
own bundle (`Spec.ldSwitch_goodT`), taken as a hypothesis. -/
theorem ldTower_switch_of (hS : Spec.ldSwitch_goodT) : Spec.ldTower_switch := by
  intro E P P' St _ _ _ _ _ _ D e e' L t' h
  refine ⟨(hS E P P' St D e e' L t' h.laws h.reads h.list h.okO h.okB h.priv h.zk).1,
    fun _ _ => rfl, fun _ _ => rfl,
    fun ρ U hU => ⟨⟨U, hU, ?_⟩, ?_⟩⟩
  · intro p hp
    have hp' : (Sum.inl p : OPos D.sh) ∈ U.biUnion ((ldSwitch D).srcO ρ) := Finset.mem_toLeft.1 hp
    obtain ⟨q, hq, hpq⟩ := (mem_biUnion_at _).1 hp'
    obtain ⟨p', hp'', e1⟩ := (mem_image_at _).1 hpq
    obtain rfl := Sum.inl.inj e1
    exact Finset.mem_biUnion.2 ⟨q, hq, hp''⟩
  · have hsub : (ldSwitch D).need ρ U ⊆ Finset.univ.image ρ.2.1.1 := by
      intro q hq
      rcases mem_need.1 hq with h1 | ⟨u, _, h2⟩
      · rcases mem_given.1 h1 with h3 | ⟨p, _, h4⟩
        · exact h3
        · exact absurd h4 (Finset.notMem_empty _)
      · exact absurd h2 (Finset.notMem_empty _)
    exact (Finset.card_le_card hsub).trans (Finset.card_image_le.trans (by simp))

open Classical in
/-- The base case is a tail (`Spec.ldTower_base`, with its hypotheses), from `hB`: the base case's
own bundle (`Spec.ldBase_good`), taken as a hypothesis. -/
theorem ldTower_base_of (hB : Spec.ldBase_good) : Spec.ldTower_base := by
  intro E _ _ a t cov d bad L2 h
  have hpick : ∀ (ρ : Rho (ldBaseShape a.C t)) (p : OPos (ldBaseShape a.C t)), p ∈
        (ldBaseIOR a.C a.sl t cov).reads ρ →
      (ldBaseIOR a.C a.sl t cov).tie ρ p ⊆ Finset.univ.image ρ.2.1 := by
    intro ρ p hp q hq
    obtain ⟨p', hp', rfl⟩ := (mem_image_at _).1 hp
    obtain ⟨x, hx, hpx⟩ := (mem_biUnion_at _).1 hp'
    obtain ⟨i, _, rfl⟩ := (mem_image_at _).1 hx
    have hex : ∃ i, p' ∈ a.C.src (ρ.2.1 i) := ⟨i, hpx⟩
    have hq' : q = ldPick a.C cov ρ.2.1 p' := Finset.mem_singleton.1 hq
    rw [hq']
    unfold ldPick
    rw [dif_pos hex]
    exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
  refine ⟨hB E a.P a.C a.St a.sl t cov d a.e bad L2 h.laws h.transp h.lt h.mca h.list,
    fun _ _ => rfl, hpick,
    fun ρ U _ => ⟨?_, ?_⟩⟩
  · intro p hp
    obtain ⟨u, _, hu⟩ := (mem_biUnion_at _).1 hp
    exact absurd hu (Finset.notMem_empty _)
  · have hsub : (ldBaseIOR a.C a.sl t cov).need ρ U ⊆ Finset.univ.image ρ.2.1 := by
      intro q hq
      rcases mem_need.1 hq with h1 | ⟨u, _, h2⟩
      · rcases mem_given.1 h1 with h3 | ⟨p, hp, h4⟩
        · exact h3
        · rcases hp with hp | hp
          · exact hpick ρ p hp h4
          · obtain ⟨u, _, hu⟩ := (mem_biUnion_at _).1 hp
            exact absurd hu (Finset.notMem_empty _)
      · exact absurd h2 (Finset.notMem_empty _)
    exact (Finset.card_le_card hsub).trans (Finset.card_image_le.trans (by simp))

/-- Fold, then code switch (`Spec.ldTower_stage`, with its hypotheses), from `hS`: the switch's own
bundle (`Spec.ldSwitch_goodT`), taken as a hypothesis. -/
theorem ldTower_stage_of (hS : Spec.ldSwitch_goodT) : Spec.ldTower_stage := by
  intro E _ _ a P' StM _ _ D F e' L t' hF hD
  refine ⟨ldTower_seq E a (D.jIn a.e) (D.jOut e') F (ldSwBlock D a.e e' L t') D.t D.t t' hF
      (ldTower_switch_of hS E a.P P' StM D a.e e' L t' hD),
    ?_, rfl, ?_, ?_⟩
  · show (F.R.shape ++ D.sh).length = _
    rw [List.length_append]
    rfl
  · show F.N.pBad + (ldSwNums D Unit (fun _ => True) a.e L t').pBad = F.N.pBad
    rw [(hS E a.P P' StM D a.e e' L t' hD.laws hD.reads hD.list hD.okO hD.okB hD.priv hD.zk).2,
      add_zero]
  · intro x τ₁ τ₂ y w' hy
    obtain ⟨xo, hx, rfl⟩ := Option.map_eq_some_iff.1 hy
    exact IOR.extSeq_app F.R (ldSwitch D) F.ext (fun _ _ w' => D.back w') 0 x τ₁ τ₂ xo w' hx

/-- A tower is a tail (`Spec.ldTower_tail`, with its hypothesis), from `hS`: the switch's own bundle
(`Spec.ldSwitch_goodT`), taken as a hypothesis. -/
theorem ldTower_tail_of (hS : Spec.ldSwitch_goodT) : Spec.ldTower_tail := by
  intro E _ _ a T
  induction T with
  | base a Z t => exact fun h => h
  | step a D F e' L rest ih =>
    intro h
    exact ldTower_cons E a (D.jOut e') (ldStage D F e' L rest.q) rest.toEnd D.t rest.q
      (ldTower_stage_of hS E a _ _ D F e' L rest.q h.1 h.2.1).1 (ih h.2.2)

theorem ldTower_end_of (hS : Spec.ldSwitch_goodT) : Spec.ldTower_end := fun E _ _ a T h =>
  tailTr_end Unit _ _ _ T.toEnd.R _ _ T.toEnd.H a.rels trivRels T.toEnd.ext T.toEnd.N
    (a.atMost T.q) (ldTower_tail_of hS E a T h)

theorem ldTower_rounds : Spec.ldTower_rounds := by
  intro E _ _ a T
  induction T with
  | base a Z t => rfl
  | step a D F e' L rest ih =>
    show ((F.R.shape ++ D.sh) ++ rest.toEnd.R.shape).length = F.R.shape.length + 2 + rest.rounds
    rw [List.length_append, List.length_append, ih]
    rfl

theorem ldTower_err : Spec.ldTower_err := fun _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl

theorem ldTower_cutThen : Spec.ldTower_cutThen := by
  intro E P St _ _ _ _ C₁ C₂ sl e b G t t' hG
  refine ⟨ldTower_seq E _ _ b (ldSplit C₁ C₂ sl e) G t t t'
      (ldTower_split E P St C₁ C₂ sl e t).1 hG,
    rfl, HEq.rfl, ?_⟩
  show (0 : ENNReal) + G.N.pBad = G.N.pBad
  rw [zero_add]

/-- A run is a piece (`Spec.ldTower_run`, with its hypothesis), from `hS`: the switch's own bundle
(`Spec.ldSwitch_goodT`), taken as a hypothesis. -/
theorem ldTower_run_of (hS : Spec.ldSwitch_goodT) : Spec.ldTower_run := by
  intro E _ _ a b R t'
  induction R with
  | last a b B t => exact fun h => h
  | step a b D F e' L rest ih =>
    intro h
    exact ldTower_seq E a (D.jOut e') b (ldStage D F e' L rest.q) rest.toBlock D.t rest.q t'
      (ldTower_stage_of hS E a _ _ D F e' L rest.q h.1 h.2.1).1 (ih h.2.2)

theorem ldTower_run_rounds : Spec.ldTower_run_rounds := by
  intro E _ _ a b R
  induction R with
  | last a b B t => rfl
  | step a b D F e' L rest ih =>
    show ((F.R.shape ++ D.sh) ++ rest.toBlock.R.shape).length = F.R.shape.length + 2 + rest.rounds
    rw [List.length_append, List.length_append, ih]
    rfl

end Cb
