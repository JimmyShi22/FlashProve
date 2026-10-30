-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5J/K09AreadyHd2.lean: K9's FIELD `AreadyS`, AND THE BARE PROMISE UNDER THE CONDITION IN
FRONT ALONE, AT THE 13 LINKS WHERE Kx HAS GROWN (the 12 attention links and the head's), AT THE
GROWN Kx (`kxAtt`, `kxHead`, SortLetters4.lean), FROM THE HEAD. Theorems: joins of other files'
lemmas.
How. `ok0_att_hd`, `ok0_head_hd` (K09AreadyHd.lean) give the sort's named Ok and `kxAll3`. The new
conjunct (`PlanesAttOk`, `PlanesHeadOk`, OkPlanes.lean) is `planesAttOk_mg`, `planesHeadOk_mg`
(K09PlanesAt.lean) at `closed_at_hd` and `reads_at_hd`. `kxAtt_of`, `kxHead_of` join them.
  `ok0_att_hd2`, `ok0_head_hd2`: **the bare promise.** `aready_att_hd2`, `aready_head_hd2`: **the
    field's text.** The binders are K09AreadyHd.lean's; no premise is new.
Limits. A JOINING. MUCH OF THE END IS READ BACK OUT OF THE TABLE's PROMISE, WHICH STANDS IN THE
CONDITION IN FRONT: which clauses, and by which road: the head of K09AreadyHd.lean. These theorems
show nothing of that promise. No state is shown to meet the condition in front; a member of the head
is proved at `storedPublicFiles` and `zGap` alone (at secondHashFunction; side library AtFullSide/Top/). At the format's
second hash function and the full size, as the head stands. Kx as it stands. Nothing on soundness.

-/
import Johnson.P5J.K09AreadyHd
import Johnson.P5J.K09PlanesAt
import Johnson.Desc.First.Link.Law.SortLetters4

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
open VerifiableInference.Desc.Kinds.Head (parOf)
open VerifiableInference.Desc.Kinds.Head.Law (readsOf workOf)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

set_option quotPrecheck false in
local notation "FrK" => frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0

/-- **THE BARE PROMISE AT AN ATTENTION LINK, AT THE GROWN Kx.** -/
theorem ok0_att_hd2 (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bs : ProofFile.PureBase}
    {base : List (Block S ProofFile.Cl)}
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) {g : ℕ} (hg : g < 12) {A : Attention.Plan}
    (hA : Bs.G₀.W.A[g]? = some A) {Xl : LinkH} (e3 : Bs.G₀.built[2 * g + 1]? = some Xl)
    {xx : VerifiableInference.Desc.First.Look.Place} {tlD : HTailF2}
    (hd : VerifiableInference.Desc.First.Look.digAt (At.X Zp) (2 * g + 1) = some (xx, tlD))
    (z : ProofFile.InstPub) (u : HTailF2) (lm : ℕ)
    {pC pD : VerifiableInference.Desc.First.Look.P}
    (hC : placeAt (At.X Zp) (2 * g + 1) false = some pC)
    (hD : placeAt (At.X Zp) (2 * g + 1) true = some pD) :
    ∀ a : S × (FrK).E.Str, onTR h.𝔇.N (mgAll h.𝔇 mgBase) fullLinks At.ps (fun s : S => (z, s))
      (VerifiableInference.Desc.LinkJoin.RchAt (F := FrK) h.toAtMg.rch z)
      (batchAt fullLinks At.ps (2 * g + 1)) a →
      (fun q => OkAtt rdAll (parCOf A) (ProofFile.k8NU Bs.G₀ Xl) tlD q ∧
          kxAtt pC.lm pC.first lm pD.first (parCOf A) (ProofFile.k8NU Bs.G₀ Xl) q)
        (fixed9 (phiAll u psiAll) a.1) := by
  intro a ho
  have T := ok0_att_hd h O hg hA e3 hd z u lm hC hD a ho
  exact ⟨T.1, kxAtt_of T.2 (planesAttOk_mg h O hg hA e3 z a ho tlD u
    (closed_at_hd h O (by omega : 2 * g + 1 < 25) e3 hd))⟩

/-- **THE BARE PROMISE AT THE HEAD's LINK, AT THE GROWN Kx.** -/
theorem ok0_head_hd2 (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bs : ProofFile.PureBase}
    {base : List (Block S ProofFile.Cl)}
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) {Xl : LinkH}
    (e3 : Bs.G₀.built[24]? = some Xl)
    {xx : VerifiableInference.Desc.First.Look.Place} {tlD : HTailF2}
    (hd : VerifiableInference.Desc.First.Look.digAt (At.X Zp) 24 = some (xx, tlD))
    (z : ProofFile.InstPub) (u : HTailF2) (lm : ℕ)
    {pC pD : VerifiableInference.Desc.First.Look.P}
    (hC : placeAt (At.X Zp) 24 false = some pC)
    (hD : placeAt (At.X Zp) 24 true = some pD) :
    ∀ a : S × (FrK).E.Str, onTR h.𝔇.N (mgAll h.𝔇 mgBase) fullLinks At.ps (fun s : S => (z, s))
      (VerifiableInference.Desc.LinkJoin.RchAt (F := FrK) h.toAtMg.rch z)
      (batchAt fullLinks At.ps 24) a →
      (fun q => OkHead Bs.G₀.W.hS (readsOf Bs.G₀.W) (parOf Bs.G₀.W.hS (workOf Bs.G₀.W)) kapAll
          (ProofFile.k8NU Bs.G₀ Xl) tlD q ∧
          kxHead pC.lm pC.first lm pD.first (readsOf Bs.G₀.W) (ProofFile.k8NU Bs.G₀ Xl) q)
        (fixed9 (phiAll u psiAll) a.1) := by
  intro a ho
  have T := ok0_head_hd h O e3 hd z u lm hC hD a ho
  exact ⟨T.1, kxHead_of T.2 (planesHeadOk_mg h O (reads_at_hd O) e3 z a ho tlD u
    (closed_at_hd h O (by decide : 24 < 25) e3 hd))⟩

/-! ## The field's text -/

theorem aready_att_hd2 (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bs : ProofFile.PureBase}
    {base : List (Block S ProofFile.Cl)}
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) {g : ℕ} (hg : g < 12) {A : Attention.Plan}
    (hA : Bs.G₀.W.A[g]? = some A) {Xl : LinkH} (e3 : Bs.G₀.built[2 * g + 1]? = some Xl)
    {xx : VerifiableInference.Desc.First.Look.Place} {tlD : HTailF2}
    (hd : VerifiableInference.Desc.First.Look.digAt (At.X Zp) (2 * g + 1) = some (xx, tlD))
    (z : ProofFile.InstPub) (p : Where) (u : HTailF2) (lm : ℕ)
    {pC pD : VerifiableInference.Desc.First.Look.P}
    (hC : placeAt (At.X Zp) (2 * g + 1) false = some pC)
    (hD : placeAt (At.X Zp) (2 * g + 1) true = some pD) :
    ∀ a : S × (FrK).E.Str, ((onTR h.𝔇.N (mgAll h.𝔇 mgBase) fullLinks At.ps (fun s : S => (z, s))
      (VerifiableInference.Desc.LinkJoin.RchAt (F := FrK) h.toAtMg.rch z)
      (batchAt fullLinks At.ps (2 * g + 1)) a ∧ k9OnA a.1 = true) ∧
        (rowsFit p.rows pi8) (fixed9 (phiAll u psiAll) a.1)) →
      (fun q => OkAtt rdAll (parCOf A) (ProofFile.k8NU Bs.G₀ Xl) tlD q ∧
          kxAtt pC.lm pC.first lm pD.first (parCOf A) (ProofFile.k8NU Bs.G₀ Xl) q)
        (fixed9 (phiAll u psiAll) a.1) :=
  fun a ha => ok0_att_hd2 h O hg hA e3 hd z u lm hC hD a ha.1.1

theorem aready_head_hd2 (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bs : ProofFile.PureBase}
    {base : List (Block S ProofFile.Cl)}
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) {Xl : LinkH}
    (e3 : Bs.G₀.built[24]? = some Xl)
    {xx : VerifiableInference.Desc.First.Look.Place} {tlD : HTailF2}
    (hd : VerifiableInference.Desc.First.Look.digAt (At.X Zp) 24 = some (xx, tlD))
    (z : ProofFile.InstPub) (p : Where) (u : HTailF2) (lm : ℕ)
    {pC pD : VerifiableInference.Desc.First.Look.P}
    (hC : placeAt (At.X Zp) 24 false = some pC)
    (hD : placeAt (At.X Zp) 24 true = some pD) :
    ∀ a : S × (FrK).E.Str, ((onTR h.𝔇.N (mgAll h.𝔇 mgBase) fullLinks At.ps (fun s : S => (z, s))
      (VerifiableInference.Desc.LinkJoin.RchAt (F := FrK) h.toAtMg.rch z)
      (batchAt fullLinks At.ps 24) a ∧ k9OnA a.1 = true) ∧
        (rowsFit p.rows pi8) (fixed9 (phiAll u psiAll) a.1)) →
      (fun q => OkHead Bs.G₀.W.hS (readsOf Bs.G₀.W) (parOf Bs.G₀.W.hS (workOf Bs.G₀.W)) kapAll
          (ProofFile.k8NU Bs.G₀ Xl) tlD q ∧
          kxHead pC.lm pC.first lm pD.first (readsOf Bs.G₀.W) (ProofFile.k8NU Bs.G₀ Xl) q)
        (fixed9 (phiAll u psiAll) a.1) :=
  fun a ha => ok0_head_hd2 h O e3 hd z u lm hC hD a ha.1.1

end P5J

#print axioms P5J.ok0_att_hd2
#print axioms P5J.ok0_head_hd2
#print axioms P5J.aready_att_hd2
#print axioms P5J.aready_head_hd2
