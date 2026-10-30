-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5J/K09AreadyC.lean: `Aready` ON THE SECOND ROAD: THE END IS THE SORT's NAMED Ok AND
`kxAll3` (SortLetters3.lean): WITHOUT hlen; AND AT THE LAYERS' LINKS NO CLAUSE ON STATES IS
LEFT AS A PREMISE. Theorems: joins of other files' lemmas.
Why. That the runs' claims are at most the plan's number (hlen) follows from the batching's own yes
(Johnson/Desc/First/Batch/Law/LenOfYes.lean), which wants Ok at the state first: so hlen may not
stand inside Ok. K09Aready.lean, whose ends hold it as a premise, stands unturned.
  `numThree_layers`, `numThree_att`, `numThree_head`: `NumbersThree` of what is fixed: `numOk_*`
    (K09Aready.lean) at len := fun _ => 0. `ownL_at`: **`K9OwnL`: all four of a layers' link's own
    clauses:** front, back by FrontBackAt.lean; entsFront, entsBack by EntsLayersAt.lean, their
    static clause from the core.
  `aready_layersC`: **the field's text at a layers' link: EVERY PREMISE IS CLOSED:** `K9Closed`,
    `PosPlan`, h0 : 0 < nU[2], hP, hgp: the clause's parameters are the seat's; the two places.
    `aready_attC`, `aready_headC`: the like, the sort's own clauses (`K9OwnA`, `K9OwnH`) still a
    premise.
The left side is the first road's (rowsFit): a field that asked the second road's wider condition
there could not be called where hlen is still to be drawn. These theorems spend neither half of it.
Limits. A JOINING. MUCH OF THE END IS READ BACK OUT OF THE TABLE's PROMISE, WHICH STANDS IN THE
CONDITION IN FRONT: which clauses, and by which road: the head of K09AreadyHd.lean. These theorems
show nothing of that promise. No state is shown to meet the condition in front; a member of the head
is proved at `storedPublicFiles` and `zGap` alone (at secondHashFunction; side library AtFullSide/Top/). The closed
premises, `K9OwnA` and `K9OwnH` are shown of nothing here. Nothing on soundness.

-/
import Johnson.P5J.K09Aready
import Johnson.Desc.First.Link.Law.SortLetters3
import Johnson.Desc.First.Link.Law.FrontBackAt
import Johnson.Desc.First.Link.Law.EntsLayersAt

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

open VerifiableInference.Desc.LinkJoin (NumbersThree okFront_at okBack_at entsFront_at entsBack_at)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

set_option quotPrecheck false in
local notation "FrK" => frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0

/-! ## The three numbers -/

theorem numThree_layers (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bs : ProofFile.PureBase}
    {base : List (Block S ProofFile.Cl)}
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) {g : ℕ} (hg : g < 12) {Xl : LinkH}
    (e3 : Bs.G₀.built[2 * g]? = some Xl) (z : ProofFile.InstPub) (a : S × (FrK).E.Str)
    (ho : onTR h.𝔇.N (mgAll h.𝔇 mgBase) fullLinks At.ps (fun s : S => (z, s))
      (VerifiableInference.Desc.LinkJoin.RchAt (F := FrK) h.toAtMg.rch z)
      (batchAt fullLinks At.ps (2 * g)) a) (tlD u : HTailF2) (C : K9Closed Xl tlD) :
    NumbersThree (fixed9 (phiAll u psiAll) a.1) := by
  have N := numOk_layers h O hg e3 z a ho tlD u C (fun _ => 0) (fun _ _ => Nat.zero_le _)
  exact ⟨N.funs, N.heard, N.hmS⟩

theorem numThree_att (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bs : ProofFile.PureBase}
    {base : List (Block S ProofFile.Cl)}
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) {g : ℕ} (hg : g < 12) {Xl : LinkH}
    (e3 : Bs.G₀.built[2 * g + 1]? = some Xl) (z : ProofFile.InstPub) (a : S × (FrK).E.Str)
    (ho : onTR h.𝔇.N (mgAll h.𝔇 mgBase) fullLinks At.ps (fun s : S => (z, s))
      (VerifiableInference.Desc.LinkJoin.RchAt (F := FrK) h.toAtMg.rch z)
      (batchAt fullLinks At.ps (2 * g + 1)) a) (tlD u : HTailF2) (C : K9Closed Xl tlD) :
    NumbersThree (fixed9 (phiAll u psiAll) a.1) := by
  have N := numOk_att h O hg e3 z a ho tlD u C (fun _ => 0) (fun _ _ => Nat.zero_le _)
  exact ⟨N.funs, N.heard, N.hmS⟩

theorem numThree_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bs : ProofFile.PureBase}
    {base : List (Block S ProofFile.Cl)}
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) {Xl : LinkH}
    (e3 : Bs.G₀.built[24]? = some Xl) (z : ProofFile.InstPub) (a : S × (FrK).E.Str)
    (ho : onTR h.𝔇.N (mgAll h.𝔇 mgBase) fullLinks At.ps (fun s : S => (z, s))
      (VerifiableInference.Desc.LinkJoin.RchAt (F := FrK) h.toAtMg.rch z)
      (batchAt fullLinks At.ps 24) a) (tlD u : HTailF2) (C : K9Closed Xl tlD) :
    NumbersThree (fixed9 (phiAll u psiAll) a.1) := by
  have N := numOk_head h O e3 z a ho tlD u C (fun _ => 0) (fun _ _ => Nat.zero_le _)
  exact ⟨N.funs, N.heard, N.hmS⟩

/-! ## The layers' links -/

/-- **ALL FOUR OF A LAYERS' LINK's OWN CLAUSES.** -/
theorem ownL_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bs : ProofFile.PureBase}
    {base : List (Block S ProofFile.Cl)}
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) {g : ℕ} (hg : g < 12) {Xl : LinkH}
    (e3 : Bs.G₀.built[2 * g]? = some Xl) (z : ProofFile.InstPub) (a : S × (FrK).E.Str)
    (ho : onTR h.𝔇.N (mgAll h.𝔇 mgBase) fullLinks At.ps (fun s : S => (z, s))
      (VerifiableInference.Desc.LinkJoin.RchAt (F := FrK) h.toAtMg.rch z)
      (batchAt fullLinks At.ps (2 * g)) a) (p4 : OnBytes.Desc.First.K4.Par) (nU : Array ℕ)
    (tlD u : HTailF2)
    (C : K9Closed Xl tlD) (H : PosPlan Xl.tl Xl.Fp (layShapes Bs.G₀.W.layers g))
    (h0 : 0 < nU.getD 2 0) (hP : p4.P = Bs.G₀.W.layers) (hgp : p4.g = g) :
    K9OwnL p4 nU (fixed9 (phiAll u psiAll) a.1) := by
  obtain ⟨hp, hr, hq, hB, -⟩ := front_at_mg h O (by omega : 2 * g < 25) z a ho
  have e : VerifiableInference.Desc.LinkJoin.frontAt (2 * g) = 28 * g + 9 := by
    unfold VerifiableInference.Desc.LinkJoin.frontAt
    rw [if_neg (by omega : ¬ 2 * g = 24)]
    omega
  rw [e] at hr hq
  have Co := core_layers_at h O hg e3 z a ho nU tlD u C H
  exact ⟨okFront_at h.scope h.reads O hp hg hr hB u psiAll p4 hP hgp,
    okBack_at h.scope h.reads O hp hg hr hB u psiAll,
    entsFront_at h.scope h.reads O hp hg ((z, a.1), a.2) hq hB u psiAll h0 Co.static p4,
    entsBack_at h.scope h.reads O hp hg ((z, a.1), a.2) hq hB u psiAll h0 Co.static⟩

/-- **Aready AT A LAYERS' LINK, ON THE SECOND ROAD: EVERY PREMISE IS CLOSED.** -/
theorem aready_layersC (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bs : ProofFile.PureBase}
    {base : List (Block S ProofFile.Cl)}
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) {g : ℕ} (hg : g < 12) {Xl : LinkH}
    (e3 : Bs.G₀.built[2 * g]? = some Xl) (z : ProofFile.InstPub) (p : Where)
    (p4 : OnBytes.Desc.First.K4.Par) (nU : Array ℕ) (tlD u : HTailF2) (lm : ℕ)
    {pC pD : VerifiableInference.Desc.First.Look.P}
    (hC : placeAt (At.X Zp) (2 * g) false = some pC)
    (hD : placeAt (At.X Zp) (2 * g) true = some pD) (C : K9Closed Xl tlD)
    (H : PosPlan Xl.tl Xl.Fp (layShapes Bs.G₀.W.layers g))
    (h0 : 0 < nU.getD 2 0) (hP : p4.P = Bs.G₀.W.layers) (hgp : p4.g = g) :
    ∀ a : S × (FrK).E.Str, ((onTR h.𝔇.N (mgAll h.𝔇 mgBase) fullLinks At.ps (fun s : S => (z, s))
      (VerifiableInference.Desc.LinkJoin.RchAt (F := FrK) h.toAtMg.rch z)
      (batchAt fullLinks At.ps (2 * g)) a ∧ k9OnA a.1 = true) ∧
        (rowsFit p.rows pi8) (fixed9 (phiAll u psiAll) a.1)) →
      (fun q => OkLayers p4 nU tlD q ∧ kxAll3 pC.lm pC.first lm pD.first q)
        (fixed9 (phiAll u psiAll) a.1) := by
  rintro a ⟨⟨ho, -⟩, -⟩
  have W := ownL_at h O hg e3 z a ho p4 nU tlD u C H h0 hP hgp
  exact ⟨⟨core_layers_at h O hg e3 z a ho nU tlD u C H, W.front, W.back, W.entsFront,
      W.entsBack⟩,
    kxAll3_of (kx_at_front h (by omega : 2 * g < 25) z a ho lm u pC pD hC hD)
      (numThree_layers h O hg e3 z a ho tlD u C)⟩

/-! ## The attention links; the head's link -/

/-- **Aready AT AN ATTENTION LINK, ON THE SECOND ROAD.** -/
theorem aready_attC (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bs : ProofFile.PureBase}
    {base : List (Block S ProofFile.Cl)}
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) {g : ℕ} (hg : g < 12) {Xl : LinkH}
    (e3 : Bs.G₀.built[2 * g + 1]? = some Xl) (z : ProofFile.InstPub) (p : Where) (c : ParC)
    (nU : Array ℕ) (tlD u : HTailF2) (lm : ℕ) {pC pD : VerifiableInference.Desc.First.Look.P}
    (hC : placeAt (At.X Zp) (2 * g + 1) false = some pC)
    (hD : placeAt (At.X Zp) (2 * g + 1) true = some pD) (C : K9Closed Xl tlD)
    (H : ∀ p, Bs.G₀.W.A[g]? = some p → PosPlan Xl.tl Xl.Fp (attShapes p.S (nScores p.S)))
    (Own : ∀ a : S × (FrK).E.Str,
      onTR h.𝔇.N (mgAll h.𝔇 mgBase) fullLinks At.ps (fun s : S => (z, s))
      (VerifiableInference.Desc.LinkJoin.RchAt (F := FrK) h.toAtMg.rch z)
      (batchAt fullLinks At.ps (2 * g + 1)) a →
      K9OwnA rdAll c nU (fixed9 (phiAll u psiAll) a.1)) :
    ∀ a : S × (FrK).E.Str, ((onTR h.𝔇.N (mgAll h.𝔇 mgBase) fullLinks At.ps (fun s : S => (z, s))
      (VerifiableInference.Desc.LinkJoin.RchAt (F := FrK) h.toAtMg.rch z)
      (batchAt fullLinks At.ps (2 * g + 1)) a ∧ k9OnA a.1 = true) ∧
        (rowsFit p.rows pi8) (fixed9 (phiAll u psiAll) a.1)) →
      (fun q => OkAtt rdAll c nU tlD q ∧ kxAll3 pC.lm pC.first lm pD.first q)
        (fixed9 (phiAll u psiAll) a.1) := by
  rintro a ⟨⟨ho, -⟩, -⟩
  have W := Own a ho
  exact ⟨⟨core_att_at h O hg e3 z a ho nU tlD u C H, W.k5, W.entsFirst, W.entsSecond⟩,
    kxAll3_of (kx_at_front h (by omega : 2 * g + 1 < 25) z a ho lm u pC pD hC hD)
      (numThree_att h O hg e3 z a ho tlD u C)⟩

/-- **Aready AT THE HEAD's LINK, ON THE SECOND ROAD.** -/
theorem aready_headC (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bs : ProofFile.PureBase}
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
    (Own : ∀ a : S × (FrK).E.Str,
      onTR h.𝔇.N (mgAll h.𝔇 mgBase) fullLinks At.ps (fun s : S => (z, s))
      (VerifiableInference.Desc.LinkJoin.RchAt (F := FrK) h.toAtMg.rch z)
      (batchAt fullLinks At.ps 24) a →
      K9OwnH hS iU3 p6 kapAll nU (fixed9 (phiAll u psiAll) a.1)) :
    ∀ a : S × (FrK).E.Str, ((onTR h.𝔇.N (mgAll h.𝔇 mgBase) fullLinks At.ps (fun s : S => (z, s))
      (VerifiableInference.Desc.LinkJoin.RchAt (F := FrK) h.toAtMg.rch z)
      (batchAt fullLinks At.ps 24) a ∧ k9OnA a.1 = true) ∧
        (rowsFit p.rows pi8) (fixed9 (phiAll u psiAll) a.1)) →
      (fun q => OkHead hS iU3 p6 kapAll nU tlD q ∧ kxAll3 pC.lm pC.first lm pD.first q)
        (fixed9 (phiAll u psiAll) a.1) := by
  intro a ha
  have T := aready_head h O e3 z p hS iU3 p6 nU tlD u lm (fun _ => 0) hC hD C H Own
    (fun _ _ _ _ => Nat.zero_le _) a ha
  exact ⟨T.1, kxAll3_of_two T.2⟩

end P5J

#print axioms P5J.numThree_layers
#print axioms P5J.numThree_att
#print axioms P5J.numThree_head
#print axioms P5J.ownL_at
#print axioms P5J.aready_layersC
#print axioms P5J.aready_attC
#print axioms P5J.aready_headC
