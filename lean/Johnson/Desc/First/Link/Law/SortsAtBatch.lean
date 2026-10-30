-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/SortsAtBatch.lean: THE THREE SORTS' Ok (`OkLayers`, `OkAtt`, `OkHead`:
OkOne.lean) AT EVERY STATE REACHED IN FRONT OF A LINK's BATCHING: each clause laid in from the
theorem that has it; what no theorem has stays a field of one named structure a sort. Three
structures and six theorems: a joining.
Why. As CoreAtBatch.lean's: so that WHAT IS STILL OPEN OF THE ONE DEBT A LINK IS A LEAN STRUCTURE,
NOT A PAGE.
  `OkLayersLeft`: core (`OkCoreLeft`); front, back, entsFront, entsBack: the four clauses
    themselves: NO THEOREM HAS THEM. `OkAttLeft`: core; okThere: a public test of the table's
    promise says yes at s (OkK5Paid.lean's `okThere_of_onQ` has it from the promise); hrd: what rd
    reads back is what s has heard; entsFirst, entsSecond: the clauses themselves. `OkHeadLeft`:
    core; ledger: the promise's test on the ledger says yes at s (MergeOkAt.lean's `ledger_at_347`);
    k6, join, entsK6, entsJoin, entsMerge: the clauses themselves.
  `okLayers_at_batch`, `okAtt_at_batch`, `okHead_at_batch`: **the sort's Ok of what is fixed at a
    state reached at 14 (2 g) + 9, at 14 (2 g + 1) + 9 (g < 12), at 347.** k5 by `k5_of_okThere`
    (OkK5Paid.lean); merge by `merge_clause_347` (MergeOkAt.lean); the core by `core_at_batch`,
    `core_at_head`.
  `okAt_layers`, `okAt_att`, `okAt_head`: the sort's Ok is `OkAt` at that sort.
Limits. A JOINING: NOTHING IS PAID BY THIS FILE. The three structures are shown of no state here.
Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.CoreAtBatch
import Johnson.Desc.First.Link.Law.OkK5Paid
import Johnson.LPFE1R.MergeOkAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.LinkJoin
open Inst.Model
open OnBytes OnBytes.Model
open OnBytes.Model.Stages (LinkH)
open OnBytes.PscRun (Sized Filled)
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.K4Values (backForms frontForms frontWins winOf)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.First (S ledgerB)
open VerifiableInference.Desc.PhiAll
open VerifiableInference.Desc.StillRun
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (ParC)
open VerifiableInference.Desc.Kinds.Head
open VerifiableInference.Desc.Kinds.Head.Law
open H2K5.Door (okThereB)
open K5Law
open Johnson.Desc.First.Walk.Tied (Reach rchAt_raw)
open ProofFile (Cl)

variable {β : Type}

/-- **WHAT IS LEFT AT A LAYERS' LINK.** -/
structure OkLayersLeft (c : Chain S Cl) (Z : ProofFile.Pub) (Xl : LinkH) (p : OnBytes.Desc.First.K4.Par)
    (nU : Array ℕ) (tlD u : HTailF2) (ψ : S → β) (kd : ℕ) (z : ProofFile.InstPub) (s : S) : Prop where
  core : OkCoreLeft c Z Xl tlD u ψ kd z s
  /-- the four clauses themselves -/
  front : ∀ o v, (fixed9 (phiAll u ψ) s).1.own = some o → (fixed9 (phiAll u ψ) s).2 = some v →
    Sized v.F ∧
    (∀ i, i < 4 * p.P.y.NI → Filled v.F (o.H.tV.sEnd + i)) ∧
    ∀ l, frontForms (!p.k3Runs) p.P p.g o v.F = some l → ∀ f ∈ l, ∀ x ∈ f.slots.toList,
      (∃ w ∈ frontWins o, K4Values.InWin w x.1) ∨ Filled v.F x.1
  back : ∀ o v, (fixed9 (phiAll u ψ) s).1.own = some o → (fixed9 (phiAll u ψ) s).2 = some v →
    Sized v.F ∧
    ∀ f ∈ backForms o, ∀ x ∈ f.slots.toList,
      K4Values.InWin (winOf o.wo.toWsMerged.p) x.1 ∨ Filled v.F x.1
  entsFront : ∀ o v, (fixed9 (phiAll u ψ) s).1.own = some o → (fixed9 (phiAll u ψ) s).2 = some v →
    ∀ l, frontForms (!p.k3Runs) p.P p.g o v.F = some l → EntsOk nU (fixed9 (phiAll u ψ) s) l
  entsBack : ∀ o, (fixed9 (phiAll u ψ) s).1.own = some o →
    EntsOk nU (fixed9 (phiAll u ψ) s) (backForms o)

/-- **WHAT IS LEFT AT AN ATTENTION LINK.** -/
structure OkAttLeft (c : Chain S Cl) (Z : ProofFile.Pub) (Xl : LinkH)
    (rd : Phi β → Option (Forest.Heard × First.Att.P.Heard)) (cA : ParC) (nU : Array ℕ)
    (tlD u : HTailF2) (ψ : S → β) (kd : ℕ) (z : ProofFile.InstPub) (s : S) : Prop where
  core : OkCoreLeft c Z Xl tlD u ψ kd z s
  /-- a public test of the table's promise -/
  okThere : okThereB cA.geo s = true
  /-- what rd reads back is what s has heard -/
  hrd : ∀ g h, rd (phiAll u ψ s) = some (g, h) → s.heard5? = some h
  /-- the two clauses themselves -/
  entsFirst : ∀ l, fsFirst rd cA (fixed9 (phiAll u ψ) s) = some l →
    EntsOk nU (fixed9 (phiAll u ψ) s) l
  entsSecond : ∀ l, fsSecond rd cA (fixed9 (phiAll u ψ) s) = some l →
    EntsOk nU (fixed9 (phiAll u ψ) s) l

/-- **WHAT IS LEFT AT THE HEAD's LINK.** -/
structure OkHeadLeft (c : Chain S Cl) (Z : ProofFile.Pub) (Xl : LinkH) (hh : OnBytes.Model.Head.Shape)
    (iU3 : ℕ) (p : Kinds.Head.Par) (kap : Phi β → Option Seen) (nU : Array ℕ) (tlD u : HTailF2)
    (ψ : S → β) (kd : ℕ) (z : ProofFile.InstPub) (s : S) : Prop where
  core : OkCoreLeft c Z Xl tlD u ψ kd z s
  /-- the promise's test on the ledger -/
  ledger : ledgerB s = true
  /-- the five clauses themselves -/
  k6 : ∀ y w, kap (fixed9 (phiAll u ψ) s).1 = some y → (fixed9 (phiAll u ψ) s).2 = some w →
    K6Ready hh iU3 p y w.F
  join : ∀ y w g, kap (fixed9 (phiAll u ψ) s).1 = some y → (fixed9 (phiAll u ψ) s).2 = some w →
    y.lookHeard = some g → CEndFilled g w.F
  entsK6 : ∀ name ∈ ["norm", "policy", "logits"], ∀ l,
    fsK6 hh iU3 p kap name (fixed9 (phiAll u ψ) s) = some l → EntsOk nU (fixed9 (phiAll u ψ) s) l
  entsJoin : ∀ l, fsJoin hh iU3 p kap (fixed9 (phiAll u ψ) s) = some l →
    EntsOk nU (fixed9 (phiAll u ψ) s) l
  entsMerge : ∀ wo, (fixed9 (phiAll u ψ) s).1.wo = some wo →
    EntsOk nU (fixed9 (phiAll u ψ) s) [wo.p.rowForm wo.fvp {}]

variable {P : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

/-- **`OkLayers` AT EVERY STATE REACHED IN FRONT OF A LAYERS' LINK's BATCHING.** -/
theorem okLayers_at_batch (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {g : ℕ} (hg : g < 12)
    {Xl : LinkH} (e3 : Bs.G₀.built[2 * g]? = some Xl) {Str : Type}
    (a : (ProofFile.InstPub × S) × Str)
    (h : Johnson.Desc.First.Walk.Tied.RchAt
      (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c)
      (14 * (2 * g) + 9) a)
    (p : OnBytes.Desc.First.K4.Par) (nU : Array ℕ) (tlD u : HTailF2) (ψ : S → β)
    (Lf : OkLayersLeft c Z Xl p nU tlD u ψ (14 * (2 * g) + 8) a.1.1 a.1.2) :
    OkLayers p nU tlD (fixed9 (phiAll u ψ) a.1.2) :=
  ⟨core_at_batch hS hR O (by omega) e3 a h nU tlD u ψ Lf.core, Lf.front, Lf.back, Lf.entsFront,
    Lf.entsBack⟩

/-- **`OkAtt` AT EVERY STATE REACHED IN FRONT OF AN ATTENTION LINK's BATCHING.** -/
theorem okAtt_at_batch (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {g : ℕ} (hg : g < 12)
    {Xl : LinkH} (e3 : Bs.G₀.built[2 * g + 1]? = some Xl) {Str : Type}
    (a : (ProofFile.InstPub × S) × Str)
    (h : Johnson.Desc.First.Walk.Tied.RchAt
      (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c)
      (14 * (2 * g + 1) + 9) a)
    (rd : Phi β → Option (Forest.Heard × First.Att.P.Heard)) (cA : ParC) (nU : Array ℕ)
    (tlD u : HTailF2) (ψ : S → β)
    (Lf : OkAttLeft c Z Xl rd cA nU tlD u ψ (14 * (2 * g + 1) + 8) a.1.1 a.1.2) :
    OkAtt rd cA nU tlD (fixed9 (phiAll u ψ) a.1.2) :=
  ⟨core_at_batch hS hR O (by omega) e3 a h nU tlD u ψ Lf.core,
    k5_of_okThere cA a.1.2 Lf.okThere (phiAll u ψ) rd Lf.hrd, Lf.entsFirst, Lf.entsSecond⟩

/-- **`OkHead` AT EVERY STATE REACHED IN FRONT OF THE HEAD's BATCHING.** -/
theorem okHead_at_batch (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {Xl : LinkH} (e3 : Bs.G₀.built[24]? = some Xl) {Str : Type} (a : (ProofFile.InstPub × S) × Str)
    (h : Johnson.Desc.First.Walk.Tied.RchAt
      (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c)
      347 a)
    (hh : OnBytes.Model.Head.Shape) (iU3 : ℕ) (p : Kinds.Head.Par) (kap : Phi β → Option Seen)
    (nU : Array ℕ) (tlD u : HTailF2) (ψ : S → β)
    (Lf : OkHeadLeft c Z Xl hh iU3 p kap nU tlD u ψ 345 a.1.1 a.1.2) :
    OkHead hh iU3 p kap nU tlD (fixed9 (phiAll u ψ) a.1.2) :=
  ⟨core_at_head hS hR O e3 a h nU tlD u ψ Lf.core, Lf.k6, Lf.join,
    merge_clause_347 hS hR O (a := a.1) (rchAt_raw h) Lf.ledger u ψ, Lf.entsK6, Lf.entsJoin,
    Lf.entsMerge⟩

/-! ## The one function -/

section
variable (pL : OnBytes.Desc.First.K4.Par)
  (rd : Phi β → Option (Forest.Heard × First.Att.P.Heard)) (cA : ParC)
  (hh : OnBytes.Model.Head.Shape) (iU3 : ℕ) (pH : Kinds.Head.Par) (kap : Phi β → Option Seen)
  (nU : Array ℕ) (tlD : HTailF2) (q : Q β)

theorem okAt_layers (h : OkLayers pL nU tlD q) : OkAt .layers pL rd cA hh iU3 pH kap nU tlD q := h

theorem okAt_att (h : OkAtt rd cA nU tlD q) : OkAt .attention pL rd cA hh iU3 pH kap nU tlD q := h

theorem okAt_head (h : OkHead hh iU3 pH kap nU tlD q) :
    OkAt .head pL rd cA hh iU3 pH kap nU tlD q := h

end

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.okLayers_at_batch
#print axioms VerifiableInference.Desc.LinkJoin.okAtt_at_batch
#print axioms VerifiableInference.Desc.LinkJoin.okHead_at_batch
#print axioms VerifiableInference.Desc.LinkJoin.okAt_layers
#print axioms VerifiableInference.Desc.LinkJoin.okAt_att
#print axioms VerifiableInference.Desc.LinkJoin.okAt_head
