-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5J/K09Aready.lean: THE FIELD `Aready` OF `CoreLeft`
(Johnson/Desc/First/Link/Law/CoreLeft.lean), TO THE LETTER, AT THE CLOSED CONSTANT's LETTERS, A SORT
AT A TIME. What has a payer is laid in; what has none stays, by name. Structures, one line by the
kernel, and theorems: joins of other files' lemmas.
Why. `Aready` says: at every state in front of a link's batching at which the table's promise holds,
what is fixed there meets Ok. Ok is the sort's named Ok (OkOne.lean) and `kxAll2`
(SortLetters2.lean). This file breaks that one debt into what is left of it.
  `K9Closed Xl tlD`: FOUR CLOSED SENTENCES ON THE BUILT SEGMENT: static, dig, fits, ms. `K9OwnL`,
    `K9OwnA`, `K9OwnH`: THE SORT's OWN CLAUSES THAT ARE STILL OPEN, on what is fixed: front, back,
    entsFront, entsBack; k5, entsFirst, entsSecond; k6, join, entsK6, entsJoin.
    `digHeard_of_leftOn`: what the digits' lookup returned is there. `ledgerB_of_sized`.
  `batchIsFront`: the batching's number in the written list is `frontAt m`, m < 25: by the kernel.
    `front_at_mg`: WHAT THE CONDITION IN FRONT GIVES AT THE CONSTANT, in one: every sub-protocol
    passes its test on the plan (`IM.plan_flat`, from the head's own field planOk); "reached", in
    both forms; the ledger is open and has its sizes; K9's part is there.
  `kx_at_front`: **`kxAll` at the constant's letters, from the head and the condition in front
    alone.** `core_layers_at`, `core_att_at`, `core_head_at`: `OkCore`, from `K9Closed` and
    `PosPlan`. `numOk_layers`, `numOk_att`, `numOk_head`: `NumbersOk len`, hlen a premise.
  `aready_layers`, `aready_att`, `aready_head`: **the field's own text**, from `K9Closed`,
    `PosPlan`, the sort's own open clauses, and hlen.
Limits. A JOINING. `K9Closed`, `PosPlan`, `K9OwnL`, `K9OwnA`, `K9OwnH` and hlen are shown of nothing
here. The letters nU, tlD, u, lm, len and the sorts' parameters are free. Nothing on soundness.

-/
import Johnson.P5J.K09Left
import Johnson.Desc.First.Link.Law.CoreAtFront
import Johnson.Desc.First.Link.Law.KxOfTable
import Johnson.Desc.First.Link.Law.SortLetters2
import Johnson.Desc.First.Link.Law.K9LensAskLaw
import Johnson.Desc.First.Link.Law.HmsAtFront
import Johnson.Desc.First.Link.Law.EntsMerge
import Johnson.LPFE1R.MergeOkAt
import Johnson.LPFE1R.PartAtBatch
import Johnson.IMR.PlanAt

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.LinkJoin
open Inst.Model
open OnBytes OnBytes.Model
open OnBytes.Model.Stages (LinkH)
open OnBytes.PscRun (Sized Filled)
open OnBytes.Tie.Pv.Tail.Port (Fits)
open VerifiableInference.Desc.K4Values (backForms frontForms frontWins winOf)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.First (S ledgerB)
open VerifiableInference.Desc.First.TailClaims.Law (blank)
open VerifiableInference.Desc.PhiAll
open VerifiableInference.Desc.StillRun
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (ParC)
open VerifiableInference.Desc.Kinds.Head
open VerifiableInference.Desc.Kinds.Head.Law
open VerifiableInference.OnPublicFiles (K3LeftOn)
open K5Law

variable {β : Type}

/-- **FOUR CLOSED SENTENCES ON THE BUILT SEGMENT.** -/
structure K9Closed (Xl : LinkH) (tlD : HTailF2) : Prop where
  static : StaticOk Xl.tl Xl.Fp
  dig : DigStatic tlD Xl.tl Xl.Fp
  fits : Fits Xl.tl
  ms : MsPlan Xl.tl

/-- **A LAYERS' LINK's OWN CLAUSES THAT ARE STILL OPEN.** -/
structure K9OwnL (p : OnBytes.Desc.First.K4.Par) (nU : Array ℕ) (q : Q β) : Prop where
  front : ∀ o v, q.1.own = some o → q.2 = some v → Sized v.F ∧
    (∀ i, i < 4 * p.P.y.NI → Filled v.F (o.H.tV.sEnd + i)) ∧
    ∀ l, frontForms (!p.k3Runs) p.P p.g o v.F = some l → ∀ f ∈ l, ∀ x ∈ f.slots.toList,
      (∃ w ∈ frontWins o, K4Values.InWin w x.1) ∨ Filled v.F x.1
  back : ∀ o v, q.1.own = some o → q.2 = some v → Sized v.F ∧
    ∀ f ∈ backForms o, ∀ x ∈ f.slots.toList,
      K4Values.InWin (winOf o.wo.toWsMerged.p) x.1 ∨ Filled v.F x.1
  entsFront : ∀ o v, q.1.own = some o → q.2 = some v →
    ∀ l, frontForms (!p.k3Runs) p.P p.g o v.F = some l → EntsOk nU q l
  entsBack : ∀ o, q.1.own = some o → EntsOk nU q (backForms o)

/-- **AN ATTENTION LINK's.** -/
structure K9OwnA (rd : Phi β → Option (Forest.Heard × First.Att.P.Heard)) (c : ParC)
    (nU : Array ℕ) (q : Q β) : Prop where
  k5 : ∀ v g h, q.2 = some v → rd q.1 = some (g, h) → K5OkAt c g.zk h v.F
  entsFirst : ∀ l, fsFirst rd c q = some l → EntsOk nU q l
  entsSecond : ∀ l, fsSecond rd c q = some l → EntsOk nU q l

/-- **THE HEAD's LINK's.** -/
structure K9OwnH (h : OnBytes.Model.Head.Shape) (iU3 : ℕ) (p : Kinds.Head.Par)
    (kap : Phi β → Option Seen) (nU : Array ℕ) (q : Q β) : Prop where
  k6 : ∀ z u, kap q.1 = some z → q.2 = some u → K6Ready h iU3 p z u.F
  join : ∀ z u g, kap q.1 = some z → q.2 = some u → z.lookHeard = some g → CEndFilled g u.F
  entsK6 : ∀ name ∈ ["norm", "policy", "logits"], ∀ l, fsK6 h iU3 p kap name q = some l →
    EntsOk nU q l
  entsJoin : ∀ l, fsJoin h iU3 p kap q = some l → EntsOk nU q l

/-- What the digits' lookup returned is there. -/
theorem digHeard_of_leftOn {s : S} {hh : Forest.Shape} {lm first : ℕ} {Qf : Fork → Prop}
    (L : K3LeftOn S.fork? heardDig hh lm first Qf s) (u : HTailF2) (ψ : S → β) :
    ∀ tlb, (pi8 (fixed9 (phiAll u ψ) s).1).1 = some tlb → tlb.heard.isSome = true := by
  obtain ⟨-, -, -, g, -, -, -, -, hg, -⟩ := L
  intro tlb e
  obtain ⟨tl, htl, rfl⟩ := Option.map_eq_some_iff.1
    (show s.tl?.map (blank u) = some tlb from e)
  have k : tl.heard = some g := by
    unfold heardDig at hg
    rw [htl] at hg
    exact hg
  show tl.heard.isSome = true
  rw [k]
  rfl

/-- The promise's test on the ledger, from its sizes. -/
theorem ledgerB_of_sized {s : S} (hB : ∃ G', s.fork? = some G' ∧ Sized G') :
    ledgerB s = true := by
  obtain ⟨G', hG', h1, h2, h3⟩ := hB
  unfold ledgerB
  rw [hG']
  simp [h1, h2, h3]

end VerifiableInference.Desc.LinkJoin

noncomputable section

namespace P5J

open Meaning
open Inst.Model
open OnBytes OnBytes.Model OnBytes.Road OnBytes.Flat OnBytes.Maker OnBytes.Slice OnBytes.RunA
open OnBytes.Model.Stages (LinkH)
open OnBytes.PscRun (Sized)
open OnBytes.Tie.Pv.Tail.Closed (shapesOf layShapes attShapes nScores)
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Block FileDescription Place Link Chain)
open VerifiableInference.Desc.First (S ModelPart)
open VerifiableInference.Desc.First.Look (placeAt)
open VerifiableInference.Desc.First.Att.P (ParC)
open VerifiableInference.Desc.Kinds.Head.Law (tabsOfPlan)
open VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open VerifiableInference.Desc.K9 (atS Where)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.K9Asks (funs_layers funs_att funs_head)
open VerifiableInference.Desc.PhiAll
open VerifiableInference.Desc.LinkJoin (batchAt onTR frontAt kx_of_table ledger_at_front
  part_at_batch_all K9Closed K9OwnL K9OwnA K9OwnH PosPlan OkCoreLess core_layers_front
  core_att_front core_head_front NumbersOk hmS_at digHeard_of_leftOn leftOn_digits_front
  leftOn_digits_head ledgerB_of_sized merge_clause_347 entsMerge_at_347 OkCore OkLayers OkAtt
  OkHead pi8)
open Johnson.Desc.First.Walk.Tied (Reach)
open _root_.Desc.K14.Law (seatZ secondAt)

/-- The batching's number in the written list is the front's. -/
def batchIsFrontB (m : ℕ) : Bool := batchAt fullLinks At.ps m == frontAt m

set_option maxRecDepth 1000000 in
theorem batchIsFront_full : (List.range 25).all batchIsFrontB = true := by decide +kernel

theorem batchIsFront {m : ℕ} (hm : m < 25) : batchAt fullLinks At.ps m = frontAt m :=
  beq_iff_eq.1 (List.all_eq_true.1 batchIsFront_full m (List.mem_range.2 hm))

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

set_option quotPrecheck false in
local notation "FrK" => frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0

/-- **WHAT THE CONDITION IN FRONT GIVES AT THE CONSTANT.** -/
theorem front_at_mg (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bs : ProofFile.PureBase}
    {base : List (Block S ProofFile.Cl)}
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) {m : ℕ} (hm : m < 25) (z : ProofFile.InstPub) (a : S × (FrK).E.Str)
    (ho : onTR h.𝔇.N (mgAll h.𝔇 mgBase) fullLinks At.ps (fun s : S => (z, s))
      (VerifiableInference.Desc.LinkJoin.RchAt (F := FrK) h.toAtMg.rch z)
      (batchAt fullLinks At.ps m) a) :
    (∀ b ∈ cF.blocksInOrder, b.planOk = true) ∧ Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (frontAt m) (z, a.1) ∧
      Johnson.Desc.First.Walk.Tied.RchAt
        (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Zp (seatZ Zp Np) (secondAt Zp Np)
        (fun s => s) (ProofFile.startS Zp) cF)
        (frontAt m) ((z, a.1), a.2) ∧
      (∃ G', a.1.fork? = some G' ∧ Sized G') ∧ (atS.get? a.1).isSome = true := by
  have hr := list_rchIs h z _ _ ho.2
  have hq := ho.2.1
  have ha := ho.1
  have hpart := part_at_batch_all h.scope h.reads O (list_rchIs h z) hm ho
  rw [batchIsFront hm] at hr hq ha
  exact ⟨IM.plan_flat O h.laid.planOk, hr, hq, ledger_at_front h.𝔇 h.𝔇.N z hm a ha, hpart⟩

/-- **`kxAll` AT THE CONSTANT's LETTERS, FROM THE HEAD AND THE CONDITION IN FRONT ALONE.** -/
theorem kx_at_front (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {m : ℕ} (hm : m < 25)
    (z : ProofFile.InstPub) (a : S × (FrK).E.Str)
    (ho : onTR h.𝔇.N (mgAll h.𝔇 mgBase) fullLinks At.ps (fun s : S => (z, s))
      (VerifiableInference.Desc.LinkJoin.RchAt (F := FrK) h.toAtMg.rch z)
      (batchAt fullLinks At.ps m) a) (lm : ℕ) (u : HTailF2) :
    ∀ pC pD, placeAt (At.X Zp) m false = some pC → placeAt (At.X Zp) m true = some pD →
      kxAll pC.lm pC.first lm pD.first (fixed9 (phiAll u psiAll) a.1) := by
  intro pC pD hC hD
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨hp, hr, -, -, -⟩ := front_at_mg h O hm z a ho
  have ha := ho.1
  rw [batchIsFront hm] at ha
  have hD' : placeAt Bs.G₀.W m true = some pD := by
    rw [O.W]
    exact hD
  exact kx_of_table h.𝔇 h.scope h.reads O hp hm a hr h.𝔇.N z ha lm u pC pD hC hD'

/-! ## The layers' links -/

theorem core_layers_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bs : ProofFile.PureBase}
    {base : List (Block S ProofFile.Cl)}
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) {g : ℕ} (hg : g < 12) {Xl : LinkH}
    (e3 : Bs.G₀.built[2 * g]? = some Xl) (z : ProofFile.InstPub) (a : S × (FrK).E.Str)
    (ho : onTR h.𝔇.N (mgAll h.𝔇 mgBase) fullLinks At.ps (fun s : S => (z, s))
      (VerifiableInference.Desc.LinkJoin.RchAt (F := FrK) h.toAtMg.rch z)
      (batchAt fullLinks At.ps (2 * g)) a) (nU : Array ℕ) (tlD u : HTailF2) (C : K9Closed Xl tlD)
    (H : PosPlan Xl.tl Xl.Fp (layShapes Bs.G₀.W.layers g)) :
    OkCore nU tlD (fixed9 (phiAll u psiAll) a.1) := by
  obtain ⟨hp, -, hq, hB, hpart⟩ := front_at_mg h O (by omega : 2 * g < 25) z a ho
  have e : VerifiableInference.Desc.LinkJoin.frontAt (2 * g) = 28 * g + 9 := by
    unfold VerifiableInference.Desc.LinkJoin.frontAt
    rw [if_neg (by omega : ¬ 2 * g = 24)]
    omega
  rw [e] at hq
  exact core_layers_front h.scope h.reads O hg e3 ((z, a.1), a.2) hq nU tlD u psiAll
    ⟨hpart, hB, C.static, C.dig, C.fits, hp⟩ H

theorem numOk_layers (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bs : ProofFile.PureBase}
    {base : List (Block S ProofFile.Cl)}
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) {g : ℕ} (hg : g < 12) {Xl : LinkH}
    (e3 : Bs.G₀.built[2 * g]? = some Xl) (z : ProofFile.InstPub) (a : S × (FrK).E.Str)
    (ho : onTR h.𝔇.N (mgAll h.𝔇 mgBase) fullLinks At.ps (fun s : S => (z, s))
      (VerifiableInference.Desc.LinkJoin.RchAt (F := FrK) h.toAtMg.rch z)
      (batchAt fullLinks At.ps (2 * g)) a) (tlD u : HTailF2) (C : K9Closed Xl tlD)
    (len : Phi BetaAll × Option Pub9 → ℕ)
    (hlen : ∀ v, (fixed9 (phiAll u psiAll) a.1).2 = some v →
      len (fixed9 (phiAll u psiAll) a.1) ≤ v.F.planClaimsF) :
    NumbersOk len (fixed9 (phiAll u psiAll) a.1) := by
  obtain ⟨hp, hr, -, hB, -⟩ := front_at_mg h O (by omega : 2 * g < 25) z a ho
  have e : VerifiableInference.Desc.LinkJoin.frontAt (2 * g) = 28 * g + 9 := by
    unfold VerifiableInference.Desc.LinkJoin.frontAt
    rw [if_neg (by omega : ¬ 2 * g = 24)]
    omega
  rw [e] at hr
  have hx : ((2 * g, 4, 2) : ℕ × ℕ × ℕ) ∈ P1K8S.stretches :=
    List.mem_map.2 ⟨2 * g, List.mem_range.2 (by omega), by
      rw [if_neg (by omega : ¬ 2 * g = 24), if_neg (by omega : ¬ 2 * g = 24)]⟩
  have hr' : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (14 * (2 * g) + 9) (z, a.1) := by
    rw [show 14 * (2 * g) + 9 = 28 * g + 9 by omega]
    exact hr
  obtain ⟨P', hh, -, -, -, L⟩ := leftOn_digits_front h.scope h.reads O hp
    (by omega : 2 * g < 24) hr' hB 0
  exact ⟨funs_layers h.scope h.reads O hg hr u psiAll, digHeard_of_leftOn L u psiAll,
    hmS_at h.scope h.reads O hx e3 hr' C.ms C.fits u psiAll, hlen⟩

/-- **Aready AT A LAYERS' LINK.** -/
theorem aready_layers (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bs : ProofFile.PureBase}
    {base : List (Block S ProofFile.Cl)}
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) {g : ℕ} (hg : g < 12) {Xl : LinkH}
    (e3 : Bs.G₀.built[2 * g]? = some Xl) (z : ProofFile.InstPub) (p : Where)
    (p4 : OnBytes.Desc.First.K4.Par) (nU : Array ℕ) (tlD u : HTailF2) (lm : ℕ)
    (len : Phi BetaAll × Option Pub9 → ℕ) {pC pD : VerifiableInference.Desc.First.Look.P}
    (hC : placeAt (At.X Zp) (2 * g) false = some pC)
    (hD : placeAt (At.X Zp) (2 * g) true = some pD) (C : K9Closed Xl tlD)
    (H : PosPlan Xl.tl Xl.Fp (layShapes Bs.G₀.W.layers g))
    (Own : ∀ a : S × (FrK).E.Str,
      onTR h.𝔇.N (mgAll h.𝔇 mgBase) fullLinks At.ps (fun s : S => (z, s))
      (VerifiableInference.Desc.LinkJoin.RchAt (F := FrK) h.toAtMg.rch z)
      (batchAt fullLinks At.ps (2 * g)) a →
      K9OwnL p4 nU (fixed9 (phiAll u psiAll) a.1))
    (hlen : ∀ a : S × (FrK).E.Str,
      onTR h.𝔇.N (mgAll h.𝔇 mgBase) fullLinks At.ps (fun s : S => (z, s))
      (VerifiableInference.Desc.LinkJoin.RchAt (F := FrK) h.toAtMg.rch z)
      (batchAt fullLinks At.ps (2 * g)) a →
      ∀ v, (fixed9 (phiAll u psiAll) a.1).2 = some v →
        len (fixed9 (phiAll u psiAll) a.1) ≤ v.F.planClaimsF) :
    ∀ a : S × (FrK).E.Str, ((onTR h.𝔇.N (mgAll h.𝔇 mgBase) fullLinks At.ps (fun s : S => (z, s))
      (VerifiableInference.Desc.LinkJoin.RchAt (F := FrK) h.toAtMg.rch z)
      (batchAt fullLinks At.ps (2 * g)) a ∧ k9OnA a.1 = true) ∧
        (rowsFit p.rows pi8) (fixed9 (phiAll u psiAll) a.1)) →
      (fun q => OkLayers p4 nU tlD q ∧ kxAll2 pC.lm pC.first lm pD.first len q)
        (fixed9 (phiAll u psiAll) a.1) := by
  rintro a ⟨⟨ho, -⟩, -⟩
  have W := Own a ho
  exact ⟨⟨core_layers_at h O hg e3 z a ho nU tlD u C H, W.front, W.back, W.entsFront,
      W.entsBack⟩,
    kxAll2_of (kx_at_front h (by omega : 2 * g < 25) z a ho lm u pC pD hC hD)
      (numOk_layers h O hg e3 z a ho tlD u C len (hlen a ho))⟩

/-! ## The attention links -/

theorem core_att_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bs : ProofFile.PureBase}
    {base : List (Block S ProofFile.Cl)}
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) {g : ℕ} (hg : g < 12) {Xl : LinkH}
    (e3 : Bs.G₀.built[2 * g + 1]? = some Xl) (z : ProofFile.InstPub) (a : S × (FrK).E.Str)
    (ho : onTR h.𝔇.N (mgAll h.𝔇 mgBase) fullLinks At.ps (fun s : S => (z, s))
      (VerifiableInference.Desc.LinkJoin.RchAt (F := FrK) h.toAtMg.rch z)
      (batchAt fullLinks At.ps (2 * g + 1)) a) (nU : Array ℕ) (tlD u : HTailF2)
    (C : K9Closed Xl tlD)
    (H : ∀ p, Bs.G₀.W.A[g]? = some p → PosPlan Xl.tl Xl.Fp (attShapes p.S (nScores p.S))) :
    OkCore nU tlD (fixed9 (phiAll u psiAll) a.1) := by
  obtain ⟨hp, -, hq, hB, hpart⟩ := front_at_mg h O (by omega : 2 * g + 1 < 25) z a ho
  have e : VerifiableInference.Desc.LinkJoin.frontAt (2 * g + 1) = 14 * (2 * g + 1) + 9 := by
    unfold VerifiableInference.Desc.LinkJoin.frontAt
    rw [if_neg (by omega : ¬ 2 * g + 1 = 24)]
  rw [e] at hq
  exact core_att_front h.scope h.reads O hg e3 ((z, a.1), a.2) hq nU tlD u psiAll
    ⟨hpart, hB, C.static, C.dig, C.fits, hp⟩ H

theorem numOk_att (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bs : ProofFile.PureBase}
    {base : List (Block S ProofFile.Cl)}
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) {g : ℕ} (hg : g < 12) {Xl : LinkH}
    (e3 : Bs.G₀.built[2 * g + 1]? = some Xl) (z : ProofFile.InstPub) (a : S × (FrK).E.Str)
    (ho : onTR h.𝔇.N (mgAll h.𝔇 mgBase) fullLinks At.ps (fun s : S => (z, s))
      (VerifiableInference.Desc.LinkJoin.RchAt (F := FrK) h.toAtMg.rch z)
      (batchAt fullLinks At.ps (2 * g + 1)) a) (tlD u : HTailF2) (C : K9Closed Xl tlD)
    (len : Phi BetaAll × Option Pub9 → ℕ)
    (hlen : ∀ v, (fixed9 (phiAll u psiAll) a.1).2 = some v →
      len (fixed9 (phiAll u psiAll) a.1) ≤ v.F.planClaimsF) :
    NumbersOk len (fixed9 (phiAll u psiAll) a.1) := by
  obtain ⟨hp, hr, -, hB, -⟩ := front_at_mg h O (by omega : 2 * g + 1 < 25) z a ho
  have e : VerifiableInference.Desc.LinkJoin.frontAt (2 * g + 1) = 14 * (2 * g + 1) + 9 := by
    unfold VerifiableInference.Desc.LinkJoin.frontAt
    rw [if_neg (by omega : ¬ 2 * g + 1 = 24)]
  rw [e] at hr
  have hx : ((2 * g + 1, 4, 2) : ℕ × ℕ × ℕ) ∈ P1K8S.stretches :=
    List.mem_map.2 ⟨2 * g + 1, List.mem_range.2 (by omega), by
      rw [if_neg (by omega : ¬ 2 * g + 1 = 24), if_neg (by omega : ¬ 2 * g + 1 = 24)]⟩
  obtain ⟨P', hh, -, -, -, L⟩ := leftOn_digits_front h.scope h.reads O hp
    (by omega : 2 * g + 1 < 24) hr hB 0
  exact ⟨funs_att h.scope h.reads O hg hr u psiAll, digHeard_of_leftOn L u psiAll,
    hmS_at h.scope h.reads O hx e3 hr C.ms C.fits u psiAll, hlen⟩

/-- **Aready AT AN ATTENTION LINK.** -/
theorem aready_att (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bs : ProofFile.PureBase}
    {base : List (Block S ProofFile.Cl)}
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) {g : ℕ} (hg : g < 12) {Xl : LinkH}
    (e3 : Bs.G₀.built[2 * g + 1]? = some Xl) (z : ProofFile.InstPub) (p : Where) (c : ParC)
    (nU : Array ℕ) (tlD u : HTailF2) (lm : ℕ) (len : Phi BetaAll × Option Pub9 → ℕ)
    {pC pD : VerifiableInference.Desc.First.Look.P}
    (hC : placeAt (At.X Zp) (2 * g + 1) false = some pC)
    (hD : placeAt (At.X Zp) (2 * g + 1) true = some pD) (C : K9Closed Xl tlD)
    (H : ∀ p, Bs.G₀.W.A[g]? = some p → PosPlan Xl.tl Xl.Fp (attShapes p.S (nScores p.S)))
    (Own : ∀ a : S × (FrK).E.Str,
      onTR h.𝔇.N (mgAll h.𝔇 mgBase) fullLinks At.ps (fun s : S => (z, s))
      (VerifiableInference.Desc.LinkJoin.RchAt (F := FrK) h.toAtMg.rch z)
      (batchAt fullLinks At.ps (2 * g + 1)) a →
      K9OwnA rdAll c nU (fixed9 (phiAll u psiAll) a.1))
    (hlen : ∀ a : S × (FrK).E.Str,
      onTR h.𝔇.N (mgAll h.𝔇 mgBase) fullLinks At.ps (fun s : S => (z, s))
      (VerifiableInference.Desc.LinkJoin.RchAt (F := FrK) h.toAtMg.rch z)
      (batchAt fullLinks At.ps (2 * g + 1)) a →
      ∀ v, (fixed9 (phiAll u psiAll) a.1).2 = some v →
        len (fixed9 (phiAll u psiAll) a.1) ≤ v.F.planClaimsF) :
    ∀ a : S × (FrK).E.Str, ((onTR h.𝔇.N (mgAll h.𝔇 mgBase) fullLinks At.ps (fun s : S => (z, s))
      (VerifiableInference.Desc.LinkJoin.RchAt (F := FrK) h.toAtMg.rch z)
      (batchAt fullLinks At.ps (2 * g + 1)) a ∧ k9OnA a.1 = true) ∧
        (rowsFit p.rows pi8) (fixed9 (phiAll u psiAll) a.1)) →
      (fun q => OkAtt rdAll c nU tlD q ∧ kxAll2 pC.lm pC.first lm pD.first len q)
        (fixed9 (phiAll u psiAll) a.1) := by
  rintro a ⟨⟨ho, -⟩, -⟩
  have W := Own a ho
  exact ⟨⟨core_att_at h O hg e3 z a ho nU tlD u C H, W.k5, W.entsFirst, W.entsSecond⟩,
    kxAll2_of (kx_at_front h (by omega : 2 * g + 1 < 25) z a ho lm u pC pD hC hD)
      (numOk_att h O hg e3 z a ho tlD u C len (hlen a ho))⟩

/-! ## The head's link -/

theorem core_head_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bs : ProofFile.PureBase}
    {base : List (Block S ProofFile.Cl)}
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) {Xl : LinkH}
    (e3 : Bs.G₀.built[24]? = some Xl) (z : ProofFile.InstPub) (a : S × (FrK).E.Str)
    (ho : onTR h.𝔇.N (mgAll h.𝔇 mgBase) fullLinks At.ps (fun s : S => (z, s))
      (VerifiableInference.Desc.LinkJoin.RchAt (F := FrK) h.toAtMg.rch z)
      (batchAt fullLinks At.ps 24) a) (nU : Array ℕ) (tlD u : HTailF2) (C : K9Closed Xl tlD)
    (H : ∀ t0, tabsOfPlan Bs.G₀.W.hS Bs.G₀.W.H = some t0 →
      PosPlan Xl.tl Xl.Fp (shapesOf t0.funs)) : OkCore nU tlD (fixed9 (phiAll u psiAll) a.1) := by
  obtain ⟨hp, -, hq, hB, hpart⟩ := front_at_mg h O (by decide : 24 < 25) z a ho
  exact core_head_front h.scope h.reads O e3 ((z, a.1), a.2) hq nU tlD u psiAll
    ⟨hpart, hB, C.static, C.dig, C.fits, hp⟩ H

theorem numOk_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bs : ProofFile.PureBase}
    {base : List (Block S ProofFile.Cl)}
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) {Xl : LinkH}
    (e3 : Bs.G₀.built[24]? = some Xl) (z : ProofFile.InstPub) (a : S × (FrK).E.Str)
    (ho : onTR h.𝔇.N (mgAll h.𝔇 mgBase) fullLinks At.ps (fun s : S => (z, s))
      (VerifiableInference.Desc.LinkJoin.RchAt (F := FrK) h.toAtMg.rch z)
      (batchAt fullLinks At.ps 24) a) (tlD u : HTailF2) (C : K9Closed Xl tlD)
    (len : Phi BetaAll × Option Pub9 → ℕ)
    (hlen : ∀ v, (fixed9 (phiAll u psiAll) a.1).2 = some v →
      len (fixed9 (phiAll u psiAll) a.1) ≤ v.F.planClaimsF) :
    NumbersOk len (fixed9 (phiAll u psiAll) a.1) := by
  obtain ⟨hp, hr, -, hB, -⟩ := front_at_mg h O (by decide : 24 < 25) z a ho
  have hr' : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) 347 (z, a.1) := hr
  have hx : ((24, 5, 3) : ℕ × ℕ × ℕ) ∈ P1K8S.stretches := by decide
  obtain ⟨P', hh, -, -, -, L⟩ := leftOn_digits_head h.scope h.reads O hp hr' hB 0
  exact ⟨funs_head h.scope h.reads O hr' u psiAll, digHeard_of_leftOn L u psiAll,
    hmS_at h.scope h.reads O hx e3 hr' C.ms C.fits u psiAll, hlen⟩

/-- **Aready AT THE HEAD's LINK.** -/
theorem aready_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bs : ProofFile.PureBase}
    {base : List (Block S ProofFile.Cl)}
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) {Xl : LinkH}
    (e3 : Bs.G₀.built[24]? = some Xl) (z : ProofFile.InstPub) (p : Where)
    (hS : OnBytes.Model.Head.Shape) (iU3 : ℕ) (p6 : VerifiableInference.Desc.Kinds.Head.Par)
    (nU : Array ℕ) (tlD u : HTailF2) (lm : ℕ) (len : Phi BetaAll × Option Pub9 → ℕ)
    {pC pD : VerifiableInference.Desc.First.Look.P}
    (hC : placeAt (At.X Zp) 24 false = some pC) (hD : placeAt (At.X Zp) 24 true = some pD)
    (C : K9Closed Xl tlD)
    (H : ∀ t0, tabsOfPlan Bs.G₀.W.hS Bs.G₀.W.H = some t0 →
      PosPlan Xl.tl Xl.Fp (shapesOf t0.funs))
    (Own : ∀ a : S × (FrK).E.Str,
      onTR h.𝔇.N (mgAll h.𝔇 mgBase) fullLinks At.ps (fun s : S => (z, s))
      (VerifiableInference.Desc.LinkJoin.RchAt (F := FrK) h.toAtMg.rch z)
      (batchAt fullLinks At.ps 24) a →
      K9OwnH hS iU3 p6 kapAll nU (fixed9 (phiAll u psiAll) a.1))
    (hlen : ∀ a : S × (FrK).E.Str,
      onTR h.𝔇.N (mgAll h.𝔇 mgBase) fullLinks At.ps (fun s : S => (z, s))
      (VerifiableInference.Desc.LinkJoin.RchAt (F := FrK) h.toAtMg.rch z)
      (batchAt fullLinks At.ps 24) a →
      ∀ v, (fixed9 (phiAll u psiAll) a.1).2 = some v →
        len (fixed9 (phiAll u psiAll) a.1) ≤ v.F.planClaimsF) :
    ∀ a : S × (FrK).E.Str, ((onTR h.𝔇.N (mgAll h.𝔇 mgBase) fullLinks At.ps (fun s : S => (z, s))
      (VerifiableInference.Desc.LinkJoin.RchAt (F := FrK) h.toAtMg.rch z)
      (batchAt fullLinks At.ps 24) a ∧ k9OnA a.1 = true) ∧
        (rowsFit p.rows pi8) (fixed9 (phiAll u psiAll) a.1)) →
      (fun q => OkHead hS iU3 p6 kapAll nU tlD q ∧ kxAll2 pC.lm pC.first lm pD.first len q)
        (fixed9 (phiAll u psiAll) a.1) := by
  rintro a ⟨⟨ho, -⟩, -⟩
  have W := Own a ho
  obtain ⟨-, hr, -, hB, -⟩ := front_at_mg h O (by decide : 24 < 25) z a ho
  have hr' : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) 347 (z, a.1) := hr
  exact ⟨⟨core_head_at h O e3 z a ho nU tlD u C H, W.k6, W.join,
      merge_clause_347 h.scope h.reads O (a := (z, a.1)) hr' (ledgerB_of_sized hB) u psiAll,
      W.entsK6, W.entsJoin, entsMerge_at_347 h.scope h.reads O hr' pi8 (phiAll u psiAll) nU⟩,
    kxAll2_of (kx_at_front h (by decide : 24 < 25) z a ho lm u pC pD hC hD)
      (numOk_head h O e3 z a ho tlD u C len (hlen a ho))⟩

end P5J

#print axioms VerifiableInference.Desc.LinkJoin.digHeard_of_leftOn
#print axioms VerifiableInference.Desc.LinkJoin.ledgerB_of_sized
#print axioms P5J.batchIsFront_full
#print axioms P5J.batchIsFront
#print axioms P5J.front_at_mg
#print axioms P5J.kx_at_front
#print axioms P5J.core_layers_at
#print axioms P5J.numOk_layers
#print axioms P5J.aready_layers
#print axioms P5J.core_att_at
#print axioms P5J.numOk_att
#print axioms P5J.aready_att
#print axioms P5J.core_head_at
#print axioms P5J.numOk_head
#print axioms P5J.aready_head
