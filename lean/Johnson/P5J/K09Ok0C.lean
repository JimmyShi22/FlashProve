-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5J/K09Ok0C.lean: THE BARE PROMISE OF A LINK's SORT (the sort's named Ok and `kxAll3`) OF
WHAT IS FIXED, UNDER THE CONDITION IN FRONT OF THE BATCHING ALONE, AT THE CLOSED CONSTANT. Three
theorems: joins of other files' lemmas.
  `ok0_layersC`, `ok0_attC`, `ok0_headC`: the sentences of `aready_layersC` (K09AreadyC.lean),
    `aready_attC_closed` (K09OwnA.lean), `aready_headC_two` (K09OwnH.lean) without the two halves of
    their left side that these never spent: the stronger sentences, from the same premises.
Limits. A JOINING. MUCH OF THE END IS READ BACK OUT OF THE TABLE's PROMISE, WHICH STANDS IN THE
CONDITION IN FRONT: which clauses, and by which road: the head of K09AreadyHd.lean. These theorems
show nothing of that promise. No state is shown to meet the condition in front; a member of the head
is proved at `storedPublicFiles` and `zGap` alone (at secondHashFunction; side library AtFullSide/Top/). The closed
premises, and at the head's link K6 and J, are shown of nothing here. Nothing on soundness.

-/
import Johnson.P5J.K09OwnA
import Johnson.P5J.K09OwnH

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

open VerifiableInference.Desc.First.Att.P (parCOf)
open VerifiableInference.Desc.Kinds.Head
open VerifiableInference.Desc.Kinds.Head.Law

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

set_option quotPrecheck false in
local notation "FrK" => frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0

/-- **AT A LAYERS' LINK.** -/
theorem ok0_layersC (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bs : ProofFile.PureBase}
    {base : List (Block S ProofFile.Cl)}
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) {g : ℕ} (hg : g < 12) {Xl : LinkH}
    (e3 : Bs.G₀.built[2 * g]? = some Xl) (z : ProofFile.InstPub)
    (p4 : OnBytes.Desc.First.K4.Par) (nU : Array ℕ) (tlD u : HTailF2) (lm : ℕ)
    {pC pD : VerifiableInference.Desc.First.Look.P}
    (hC : placeAt (At.X Zp) (2 * g) false = some pC)
    (hD : placeAt (At.X Zp) (2 * g) true = some pD) (C : K9Closed Xl tlD)
    (H : PosPlan Xl.tl Xl.Fp (layShapes Bs.G₀.W.layers g))
    (h0 : 0 < nU.getD 2 0) (hP : p4.P = Bs.G₀.W.layers) (hgp : p4.g = g) :
    ∀ a : S × (FrK).E.Str, onTR h.𝔇.N (mgAll h.𝔇 mgBase) fullLinks At.ps (fun s : S => (z, s))
      (VerifiableInference.Desc.LinkJoin.RchAt (F := FrK) h.toAtMg.rch z)
      (batchAt fullLinks At.ps (2 * g)) a →
      (fun q => OkLayers p4 nU tlD q ∧ kxAll3 pC.lm pC.first lm pD.first q)
        (fixed9 (phiAll u psiAll) a.1) := by
  intro a ho
  have W := ownL_at h O hg e3 z a ho p4 nU tlD u C H h0 hP hgp
  exact ⟨⟨core_layers_at h O hg e3 z a ho nU tlD u C H, W.front, W.back, W.entsFront,
      W.entsBack⟩,
    kxAll3_of (kx_at_front h (by omega : 2 * g < 25) z a ho lm u pC pD hC hD)
      (numThree_layers h O hg e3 z a ho tlD u C)⟩

/-- **AT AN ATTENTION LINK.** -/
theorem ok0_attC (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bs : ProofFile.PureBase}
    {base : List (Block S ProofFile.Cl)}
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) {g : ℕ} (hg : g < 12) {A : Attention.Plan}
    (hA : Bs.G₀.W.A[g]? = some A) {Xl : LinkH} (e3 : Bs.G₀.built[2 * g + 1]? = some Xl)
    (z : ProofFile.InstPub) (nU : Array ℕ) (tlD u : HTailF2) (lm : ℕ)
    {pC pD : VerifiableInference.Desc.First.Look.P}
    (hC : placeAt (At.X Zp) (2 * g + 1) false = some pC)
    (hD : placeAt (At.X Zp) (2 * g + 1) true = some pD) (C : K9Closed Xl tlD)
    (H : ∀ p, Bs.G₀.W.A[g]? = some p → PosPlan Xl.tl Xl.Fp (attShapes p.S (nScores p.S)))
    (h0 : 0 < nU.getD 2 0) :
    ∀ a : S × (FrK).E.Str, onTR h.𝔇.N (mgAll h.𝔇 mgBase) fullLinks At.ps (fun s : S => (z, s))
      (VerifiableInference.Desc.LinkJoin.RchAt (F := FrK) h.toAtMg.rch z)
      (batchAt fullLinks At.ps (2 * g + 1)) a →
      (fun q => OkAtt rdAll (parCOf A) nU tlD q ∧ kxAll3 pC.lm pC.first lm pD.first q)
        (fixed9 (phiAll u psiAll) a.1) := by
  intro a ho
  have W := ownA_at h O hg hA e3 z a ho nU tlD u C H h0
  exact ⟨⟨core_att_at h O hg e3 z a ho nU tlD u C H, W.k5, W.entsFirst, W.entsSecond⟩,
    kxAll3_of (kx_at_front h (by omega : 2 * g + 1 < 25) z a ho lm u pC pD hC hD)
      (numThree_att h O hg e3 z a ho tlD u C)⟩

/-- **AT THE HEAD's LINK.** -/
theorem ok0_headC (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bs : ProofFile.PureBase}
    {base : List (Block S ProofFile.Cl)}
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) {Xl : LinkH}
    (e3 : Bs.G₀.built[24]? = some Xl) (z : ProofFile.InstPub)
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
    ∀ a : S × (FrK).E.Str, onTR h.𝔇.N (mgAll h.𝔇 mgBase) fullLinks At.ps (fun s : S => (z, s))
      (VerifiableInference.Desc.LinkJoin.RchAt (F := FrK) h.toAtMg.rch z)
      (batchAt fullLinks At.ps 24) a →
      (fun q => OkHead hS iU3 p6 kapAll nU tlD q ∧ kxAll3 pC.lm pC.first lm pD.first q)
        (fixed9 (phiAll u psiAll) a.1) := by
  intro a ho
  have W := ownH_at h O e3 z a ho hS iU3 p6 nU tlD u C H h0 hi hok hsz (K6 a ho) (J a ho)
  obtain ⟨-, hr, -, hB, -⟩ := front_at_mg h O (by decide : 24 < 25) z a ho
  have hr' : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) 347 (z, a.1) := hr
  exact ⟨⟨core_head_at h O e3 z a ho nU tlD u C H, W.k6, W.join,
      merge_clause_347 h.scope h.reads O (a := (z, a.1)) hr' (ledgerB_of_sized hB) u psiAll,
      W.entsK6, W.entsJoin, entsMerge_at_347 h.scope h.reads O hr' pi8 (phiAll u psiAll) nU⟩,
    kxAll3_of (kx_at_front h (by decide : 24 < 25) z a ho lm u pC pD hC hD)
      (numThree_head h O e3 z a ho tlD u C)⟩

end P5J

#print axioms P5J.ok0_layersC
#print axioms P5J.ok0_attC
#print axioms P5J.ok0_headC
