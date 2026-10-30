-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ent/TowerKnowProofs.lean: the proofs of the statements of Cb/Ent/TowerKnow.lean: round-by-round
knowledge soundness of the whole test, alone.

An assembly. The three blocks' own theorems on knowledge soundness (`ld_sum_know`,
Cb/Ld/LdSumKnowProofs.lean; `ldSwitch_know`, Cb/Ld/LdSwitchProofs.lean; `ldBase_know`,
Cb/Ld/LdBaseProofs.lean) are joined by the rule for two reductions in a row (`Iop.know_seq`,
Ior/SeqProofs.lean). The clause of the two steps without rounds is read off the library's bundles
(`ldTower_split`, `ldShape_block`). Cutting a form asks nothing. A reshape asks its laws
(`Reshape.Laws`, Cb/Ld/LdBatShape.lean), whole, as the library's bundle does: knowledge soundness
uses `off` and `val`; `enc` and `inj` speak of the map `up`, which the honest side applies, `loc` of
the verifier's reads; `winj` is used in no clause of that bundle (the library uses it for
`ldShape_same` and for the laws of reshapes made from others, Cb/Ld/LdBatShapeProofs.lean).
Below the Johnson radius the lists come from `ld_list_johnson`: for a fold by way of
`ldJohn_errOK`, for a switch and the base case outright.

Main names: one theorem for each statement, of the same name; nine helpers: `LdTowC.knowOK`, and
`.hypK`, `.johnK` of the records.

Limits: those in the head of Cb/Ent/TowerKnow.lean.

Terms: lean/GLOSSARY.md.

-/
import Cb.Ent.TowerKnow

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop IOR

theorem ldEnt_know_of_ok : Spec.ldEnt_know_of_ok := fun _ _ _ _ _ =>
  ⟨fun _ _ _ h => h.good.know, fun _ _ h => h.good.know⟩

theorem ldEnt_seq_know : Spec.ldEnt_seq_know := fun _ _ _ a b c B₁ B₂ h₁ h₂ =>
  know_seq _ _ _ _ _ _ B₁.R B₂.R _ _ _ a.rels.on b.rels.on a.rels.relR b.rels.relR c.rels.relR
    B₁.ext B₂.ext B₁.N.err B₂.N.err 0 h₁ h₂ fun _ _ _ _ _ => trivial

theorem ldEnt_cons_know : Spec.ldEnt_cons_know := fun _ _ _ a b B Z h₁ h₂ =>
  know_seq _ _ _ _ _ _ B.R Z.R _ _ _ a.rels.on b.rels.on a.rels.relR b.rels.relR trivRels.relR
    B.ext Z.ext B.N.err Z.N.err 0 h₁ h₂ fun _ _ _ _ _ => trivial

theorem ldEnt_split_know : Spec.ldEnt_split_know := fun E P St _ _ _ _ C₁ C₂ sl e =>
  (ldTower_split E P St C₁ C₂ sl e 0).1.good.know

theorem ldEnt_shape_know : Spec.ldEnt_shape_know := fun E P _ _ _ _ C C' ρ St s e h =>
  (ldShape_block E P C C' ρ St s e 0 h).good.know

theorem ldEnt_sum_know : Spec.ldEnt_sum_know := fun E P _ _ _ _ Y d e _ Lst mC mS mW h =>
  ld_sum_know E P Y d e Lst mC mS mW h.codes h.errs h.inj h.deg h.qw

theorem ldEnt_sumAfter_know : Spec.ldEnt_sumAfter_know :=
  fun E P _ _ _ _ Y d e t Lst mC mS mW St sl h =>
    ldEnt_seq_know E _ _ _ _ _
      (ldEnt_split_know E P St (Y.C.il (Fin Y.k → Bool)) (Y.Z.il (Fin Y.h → Bool)) sl e)
      (ldEnt_sum_know E P (Y.reform sl) d e t Lst mC mS mW h)

theorem ldEnt_group_know : Spec.ldEnt_group_know := by
  intro E B _ _ _ S G _ Sh Sb sl Z d t Lst mC mS mW h hY
  have hY' : (Sh.fold Sb sl Z).HypK d G.e Lst mC mS mW :=
    ⟨hY.codes, ⟨hY.errs.list, hY.errs.mcaC, hY.errs.mcaS, hY.errs.mcaW⟩, hY.inj, hY.deg, hY.qw⟩
  exact ldEnt_seq_know E _ _ _ _ _
    (ldEnt_shape_know E G.P _ _ Sh.rho _ _ G.e (ldGroup_shape_laws E S G Sh h).1)
    (ldEnt_sumAfter_know E G.P Sh.par d G.e t Lst mC mS mW _ (Sh.form Sb sl Z) hY')

theorem ldEnt_switch_know : Spec.ldEnt_switch_know := fun E P P' St _ _ _ _ _ _ D e e' L _ h =>
  ldSwitch_know E P P' St D e e' L h.laws h.list h.okO h.okB

theorem ldEnt_base_know : Spec.ldEnt_base_know := fun _ _ _ a t cov _ _ _ h =>
  ldBase_know a.C a.sl t cov h.laws h.lt h.mca h.list

theorem ldEnt_tower_know : Spec.ldEnt_tower_know := by
  intro E _ _ a T
  induction T with
  | base a Z t => exact fun h => h
  | step a D F e' L rest ih =>
    rintro ⟨h1, h2, h3⟩
    exact ldEnt_cons_know E _ _ _ _
      (ldEnt_seq_know E _ _ _ _ _ h1 (ldEnt_switch_know E _ _ _ D a.e e' L rest.q h2)) (ih h3)

/-- a concrete tower's conditions give the abstract tower's -/
theorem LdTowC.knowOK {E : Type} [Field E] [Fintype E] {a : LdJoint E} (T : LdTowC a) :
    T.HypK → T.toTower.KnowOK := by
  induction T with
  | base a t cov d bad L2 => exact fun h => ldEnt_base_know E a t cov d bad L2 h
  | step Y sl e S d Lst mC mS mW e' L rest ih =>
    rintro ⟨h1, h2, h3⟩
    exact ⟨ldEnt_sumAfter_know E _ Y d e S.ts Lst mC mS mW _ sl h1, h2, ih h3⟩

theorem ldEnt_towC_know : Spec.ldEnt_towC_know := fun E _ _ a T h =>
  ldEnt_tower_know E a T.toTower (T.knowOK h)

theorem ldEnt_towG_know : Spec.ldEnt_towG_know := by
  intro E B _ _ _ S G _ Sb sl Z T h
  refine ldEnt_tower_know E _ T.toTower ?_
  cases T with
  | plain T => exact T.knowOK h
  | shaped Sh Sw d Lst mC mS mW e' L rest =>
    obtain ⟨h0, h1, h2, h3⟩ := h
    exact ⟨ldEnt_group_know E B S G Sh Sb sl Z d Sw.ts Lst mC mS mW h0 h1, h2, rest.knowOK h3⟩

/-- a fold below the Johnson radius: the fold's conditions, the lists at the Johnson bound -/
theorem SumPar.JohnK.hypK {E P : Type} [Field E] [Fintype E] [Fintype P] {Y : SumPar E P}
    {d e bC bZ bW : ℕ} (h : Y.JohnK d e bC bZ bW) :
    Y.HypK d e (fun _ => listMax (Fintype.card P) d e) (fun _ => bC) (fun _ => bZ) (fun _ => bW) :=
  ⟨⟨⟨h.lawsC, h.lawsZ, h.lawsW⟩, ⟨h.distC, h.distZ, h.distW⟩, ldJohn_lt _ d e h.john⟩,
    ldJohn_errOK E P Y d e bC bZ bW h.lawsC h.lawsZ h.lawsW h.distC h.distZ h.distW h.john h.mcaC
      h.mcaZ h.mcaW,
    h.inj, h.deg, h.qw⟩

/-- a code switch below the Johnson radius: the switch's conditions, the list at the Johnson
bound -/
theorem LdSw.JohnK.hypK {E P P' St : Type} [Field E] [Fintype E] [Fintype P] [Nonempty P]
    [Fintype P'] [Nonempty P'] {D : LdSw E P P' St} {d' e' : ℕ} (h : D.JohnK d' e') :
    D.HypK e' (listMax (Fintype.card P') d' e') :=
  ⟨h.lawsI, ld_list_johnson E P' D.Cout d' e' h.lawsO h.distO h.john, h.okO, h.okB⟩

theorem ldEnt_towJ_hypK : Spec.ldEnt_towJ_hypK := by
  intro E _ _ a T
  induction T with
  | base a t cov d b =>
    rintro ⟨hL, hD, hJ, hM⟩
    exact ⟨hL, ldJohn_lt _ d a.e hJ, hM,
      ld_list_johnson E a.P (a.C.il Bool) d a.e (ld_laws_il E a.P a.C Bool hL)
        (ld_dist_il E a.P a.C Bool d hD) hJ⟩
  | step Y sl e S d bC bZ bW e' d' rest ih =>
    rintro ⟨h1, h2, h3⟩
    exact ⟨h1.hypK, h2.hypK, ih h3⟩

theorem ldEnt_towJ_know : Spec.ldEnt_towJ_know := fun E _ _ a T h =>
  ldEnt_towC_know E a T.toC (ldEnt_towJ_hypK E a T h)

theorem ldEnt_towGJ_hypK : Spec.ldEnt_towGJ_hypK := by
  intro E B _ _ _ S G _ Sb sl Z T h
  cases T with
  | plain T => exact ldEnt_towJ_hypK E _ T h
  | shaped Sh Sw d bC bZ bW e' d' rest =>
    obtain ⟨h0, h1, h2, h3⟩ := h
    exact ⟨h0, h1.hypK, h2.hypK, ldEnt_towJ_hypK E _ rest h3⟩

theorem ldEnt_towKnow : Spec.ldEnt_towKnow := fun E B _ _ _ S G _ Sb sl Z T h =>
  ldEnt_towG_know E B S G Sb sl Z T.toG (ldEnt_towGJ_hypK E B S G Sb sl Z T h)

/-- the fold's record without the conditions that knowledge soundness does not use -/
theorem SumPar.Hyp.hypK {E P : Type} [Field E] [Fintype E] [Fintype P] {Y : SumPar E P}
    {d e t : ℕ} {Lst mC mS mW : ℕ → ℕ} (h : Y.Hyp d e t Lst mC mS mW) :
    Y.HypK d e Lst mC mS mW := ⟨h.codes, h.errs, h.inj, h.deg, h.qw⟩

/-- the switch's record without the conditions that knowledge soundness does not use -/
theorem LdSw.Hyp.hypK {E P P' St : Type} [Field E] [Fintype E] [Fintype P] [Nonempty P]
    [Fintype P'] [Nonempty P'] {D : LdSw E P P' St} {e' L t' : ℕ} (h : D.Hyp e' L t') :
    D.HypK e' L := ⟨h.laws, h.list, h.okO, h.okB⟩

/-- concrete towers -/
theorem LdTowC.Hyp.hypK {E : Type} [Field E] [Fintype E] {a : LdJoint E} (T : LdTowC a) :
    T.Hyp → T.HypK := by
  induction T with
  | base a t cov d bad L2 => exact fun h => ⟨h.laws, h.lt, h.mca, h.list⟩
  | step Y sl e S d Lst mC mS mW e' L rest ih =>
    rintro ⟨h1, h2, h3⟩
    exact ⟨h1.hypK, h2.hypK, ih h3⟩

theorem ldEnt_hypK_of_hyp : Spec.ldEnt_hypK_of_hyp := by
  refine ⟨fun E _ _ a T => LdTowC.Hyp.hypK T, ?_⟩
  intro E B _ _ _ S G _ Sb sl Z T h
  cases T with
  | plain T => exact LdTowC.Hyp.hypK T h
  | shaped Sh Sw d Lst mC mS mW e' L rest =>
    obtain ⟨h0, h1, h2, h3⟩ := h
    exact ⟨h0, h1.hypK, h2.hypK, LdTowC.Hyp.hypK rest h3⟩

/-- the fold's record below the Johnson radius without the conditions that knowledge soundness does
not use -/
theorem SumPar.John.johnK {E P : Type} [Field E] [Fintype E] [Fintype P] {Y : SumPar E P}
    {d e t bC bZ bW : ℕ} (h : Y.John d e t bC bZ bW) : Y.JohnK d e bC bZ bW :=
  ⟨h.lawsC, h.lawsZ, h.lawsW, h.distC, h.distZ, h.distW, h.john, h.mcaC, h.mcaZ, h.mcaW, h.inj,
    h.deg, h.qw⟩

/-- the switch's record below the Johnson radius without the conditions that knowledge soundness
does not use -/
theorem LdSw.John.johnK {E P P' St : Type} [Field E] [Fintype E] [Fintype P] [Nonempty P]
    [Fintype P'] [Nonempty P'] {D : LdSw E P P' St} {d' e' t' : ℕ} (h : D.John d' e' t') :
    D.JohnK d' e' := ⟨h.lawsO, h.distO, h.john, h.lawsI, h.okO, h.okB⟩

/-- towers below the Johnson radius -/
theorem LdTowJ.John.johnK {E : Type} [Field E] [Fintype E] {a : LdJoint E} (T : LdTowJ a) :
    T.John → T.JohnK := by
  induction T with
  | base a t cov d b => exact fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩
  | step Y sl e S d bC bZ bW e' d' rest ih =>
    rintro ⟨h1, h2, h3⟩
    exact ⟨h1.johnK, h2.johnK, ih h3⟩

theorem ldEnt_johnK_of_john : Spec.ldEnt_johnK_of_john := by
  refine ⟨fun E _ _ a T => LdTowJ.John.johnK T, ?_⟩
  intro E B _ _ _ S G _ Sb sl Z T h
  cases T with
  | plain T => exact LdTowJ.John.johnK T h
  | shaped Sh Sw d bC bZ bW e' d' rest =>
    obtain ⟨h0, h1, h2, h3⟩ := h
    exact ⟨h0, h1.johnK, h2.johnK, LdTowJ.John.johnK rest h3⟩

end Cb
