-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5J/K09OwnH.lean: AT THE HEAD's LINK: OF `K9OwnH`'s FOUR CLAUSES (K09Aready.lean) TWO ARE
LAID IN, SO THAT WHAT `Aready` STILL ASKS OF STATES THERE IS k6 AND join ALONE. Two theorems: joins
of other files' lemmas.
  `ownH_at`: `K9OwnH` of what is fixed, from its own clauses k6 and join: entsK6 by `entsK6_at_347`
    (EntsHeadAt.lean), entsJoin by `entsJoin_at_347'` (HbAtHead.lean), whose premise on the calls'
    lookup is `leftC_at` (K09LeftD.lean); "there" and the static clause are the core's.
  `aready_headC_two`: **the field's text at the head's link, on the second road**, from closed
    premises and K6, J: the clauses k6, join at every state that meets the condition in front.
Limits. A JOINING. `K9Closed`, `PosPlan`, h0, hi, hok, hsz, K6 and J are shown of nothing here.
Nothing on soundness.

-/
import Johnson.P5J.K09AreadyC
import Johnson.P5J.K09LeftD
import Johnson.Desc.First.Link.Law.HbAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

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

open VerifiableInference.Desc.LinkJoin (entsK6_at_347 entsJoin_at_347')
open VerifiableInference.Desc.Kinds.Head
open VerifiableInference.Desc.Kinds.Head.Law

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

set_option quotPrecheck false in
local notation "FrK" => frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0

/-- **`K9OwnH` FROM ITS OWN k6 AND join.** -/
theorem ownH_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bs : ProofFile.PureBase}
    {base : List (Block S ProofFile.Cl)}
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) {Xl : LinkH}
    (e3 : Bs.G₀.built[24]? = some Xl) (z : ProofFile.InstPub) (a : S × (FrK).E.Str)
    (ho : onTR h.𝔇.N (mgAll h.𝔇 mgBase) fullLinks At.ps (fun s : S => (z, s))
      (VerifiableInference.Desc.LinkJoin.RchAt (F := FrK) h.toAtMg.rch z)
      (batchAt fullLinks At.ps 24) a) (hS : OnBytes.Model.Head.Shape) (iU3 : ℕ)
    (p6 : VerifiableInference.Desc.Kinds.Head.Par) (nU : Array ℕ) (tlD u : HTailF2)
    (C : K9Closed Xl tlD)
    (H : ∀ t0, tabsOfPlan Bs.G₀.W.hS Bs.G₀.W.H = some t0 →
      PosPlan Xl.tl Xl.Fp (shapesOf t0.funs))
    (h0 : 0 < nU.getD 2 0) (hi : Bs.G₀.W.H.tl.ix.U.getD 2 none = some iU3)
    (hok : p6.ok = true)
    (hsz : p6.sizes = VerifiableInference.Desc.Kinds.Head.sizesOf hS)
    (k6 : ∀ y w, kapAll (fixed9 (phiAll u psiAll) a.1).1 = some y →
      (fixed9 (phiAll u psiAll) a.1).2 = some w →
      K6Ready hS iU3 p6 y w.F)
    (join : ∀ y w g, kapAll (fixed9 (phiAll u psiAll) a.1).1 = some y →
      (fixed9 (phiAll u psiAll) a.1).2 = some w →
      y.lookHeard = some g → CEndFilled g w.F) :
    K9OwnH hS iU3 p6 kapAll nU (fixed9 (phiAll u psiAll) a.1) := by
  obtain ⟨-, -, hq, -, -⟩ := front_at_mg h O (by decide : 24 < 25) z a ho
  have Co := core_head_at h O e3 z a ho nU tlD u C H
  obtain ⟨pl, -, ⟨hC, -, LC⟩, -⟩ := leftC_at h (by decide : 24 < 25) z a ho
  exact ⟨k6, join,
    fun name _ => entsK6_at_347 pi8 (phiAll u psiAll) u hS iU3 p6 kapAll h.scope h.reads O hi e3 H
      ((z, a.1), a.2) hq (fun _ => rfl) (hkap_all u) h0 Co.there Co.static hok hsz k6 name,
    entsJoin_at_347' pi8 (phiAll u psiAll) u hS iU3 p6 kapAll h.scope h.reads O hi e3 H
      ((z, a.1), a.2) hq (fun _ => rfl) (hkap_all u) h0 Co.there Co.static hok hsz k6 LC⟩

/-- **Aready AT THE HEAD's LINK, ON THE SECOND ROAD: ON STATES k6 AND join ALONE.** -/
theorem aready_headC_two (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bs : ProofFile.PureBase}
    {base : List (Block S ProofFile.Cl)}
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) {Xl : LinkH}
    (e3 : Bs.G₀.built[24]? = some Xl) (z : ProofFile.InstPub) (p : Where)
    (hS : OnBytes.Model.Head.Shape) (iU3 : ℕ) (p6 : VerifiableInference.Desc.Kinds.Head.Par)
    (nU : Array ℕ) (tlD u : HTailF2) (lm : ℕ) {pC pD : VerifiableInference.Desc.First.Look.P}
    (hC : placeAt (At.X Zp) 24 false = some pC) (hD : placeAt (At.X Zp) 24 true = some pD)
    (C : K9Closed Xl tlD)
    (H : ∀ t0, tabsOfPlan Bs.G₀.W.hS Bs.G₀.W.H = some t0 →
      PosPlan Xl.tl Xl.Fp (shapesOf t0.funs))
    (h0 : 0 < nU.getD 2 0) (hi : Bs.G₀.W.H.tl.ix.U.getD 2 none = some iU3)
    (hok : p6.ok = true)
    (hsz : p6.sizes = VerifiableInference.Desc.Kinds.Head.sizesOf hS)
    (K6 : ∀ a : S × (FrK).E.Str,
      onTR h.𝔇.N (mgAll h.𝔇 mgBase) fullLinks At.ps (fun s : S => (z, s))
      (VerifiableInference.Desc.LinkJoin.RchAt (F := FrK) h.toAtMg.rch z)
      (batchAt fullLinks At.ps 24) a →
      ∀ y w, kapAll (fixed9 (phiAll u psiAll) a.1).1 = some y →
      (fixed9 (phiAll u psiAll) a.1).2 = some w →
      K6Ready hS iU3 p6 y w.F)
    (J : ∀ a : S × (FrK).E.Str,
      onTR h.𝔇.N (mgAll h.𝔇 mgBase) fullLinks At.ps (fun s : S => (z, s))
      (VerifiableInference.Desc.LinkJoin.RchAt (F := FrK) h.toAtMg.rch z)
      (batchAt fullLinks At.ps 24) a →
      ∀ y w g, kapAll (fixed9 (phiAll u psiAll) a.1).1 = some y →
      (fixed9 (phiAll u psiAll) a.1).2 = some w →
      y.lookHeard = some g → CEndFilled g w.F) :
    ∀ a : S × (FrK).E.Str, ((onTR h.𝔇.N (mgAll h.𝔇 mgBase) fullLinks At.ps (fun s : S => (z, s))
      (VerifiableInference.Desc.LinkJoin.RchAt (F := FrK) h.toAtMg.rch z)
      (batchAt fullLinks At.ps 24) a ∧ k9OnA a.1 = true) ∧
        (rowsFit p.rows pi8) (fixed9 (phiAll u psiAll) a.1)) →
      (fun q => OkHead hS iU3 p6 kapAll nU tlD q ∧ kxAll3 pC.lm pC.first lm pD.first q)
        (fixed9 (phiAll u psiAll) a.1) :=
  aready_headC h O e3 z p hS iU3 p6 nU tlD u lm hC hD C H fun a ho =>
    ownH_at h O e3 z a ho hS iU3 p6 nU tlD u C H h0 hi hok hsz (K6 a ho) (J a ho)

end P5J

#print axioms P5J.ownH_at
#print axioms P5J.aready_headC_two
