-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/- Johnson/P5J/K09AreadyHd.lean: K9's FIELD `AreadyS` (CoreLeftC.lean), AND THE BARE PROMISE UNDER
THE CONDITION IN FRONT ALONE, AT ALL 25 LINKS, FROM THE HEAD: NO PREMISE ON A STATE, AND NO CLOSED
SENTENCE BUT WHAT PUBLIC READERS RETURN. Theorems: joins of other files'
lemmas.
What is laid into `ok0_layersC`, `ok0_attC`, `ok0_headC` (K09Ok0C.lean). `K9Closed`: static, dig:
`AtMg.staticOk_ground`, `AtMg.digStatic_ground` (Johnson/P5T/StaticWholeAtMg.lean,
DigStaticAtMg.lean); fits, ms: `fits_built`, `ms_built` (FitsMsBuilt.lean). `PosPlan`, h0:
`posPlan_layers`, `posPlan_attention`, `posPlan_head`, `h0_of_head` (PosPlanBuilt.lean). hP, hgp:
`k4Par_of_open` (Johnson/P1K9R/AreadyClosed.lean). At the head's link: k6: `k6_at_347`
(K6HeardAtBatch.lean); join: `join_of_leftOn` (JoinAtBatch.lean) at `leftC_at` (K09LeftD.lean); hi:
`ReadsNamed.public_third`; hok: `InScope.ok_in_scope`; hsz: by definition.
  `closed_at_hd`: `K9Closed Xl tlD` at every built segment. `reads_at_hd`: the head's plan names the
    array of reads as `readsOf W`. `ok0_layers_hd`, `ok0_att_hd`, `ok0_head_hd`: **the bare promise
    under the condition in front.** `aready_layers_hd`, `aready_att_hd`, `aready_head_hd`: **the
    field's text.**
THE BINDERS THAT STAY: the head h; an opening O, which the head gives (`h.laid.opened`); and
equations "a public reader returns this letter": the built segment; what `digAt` returns; the two
places; at a layers' link what `k4ParAt` returns; at an attention link the plan's entry. IT PINS nU
:= `ProofFile.k8NU Bs.G₀ Xl`; at the head's link hS, iU3, p6 := W.hS, `readsOf W`, `parOf W.hS (workOf
W)`, W := Bs.G₀.W.
WHAT OF THE ENDS IS READ BACK OUT OF THE TABLE's PROMISE. The ends stand under the condition in
front of the batching, which holds that promise. From "reached" and the head alone come funs, hmS,
k6, entsMerge. Through "the ledger is open and has its sizes" or "K9's part is there", both of which
the promise gives: the core, heard, Kx's half at the digits, front, back, merge, entsFront,
entsBack, entsK6, entsJoin, and in K09AreadyHd2.lean the head's planes. Through its public items: k5
("K5.okAt"); entsFirst, entsSecond, and in K09AreadyHd2.lean the attention's planes and keysEnts
("K5.plain"); join and Kx's half at the calls (leftOn). THESE THEOREMS SHOW NOTHING OF THAT PROMISE:
it is owed by the laws of the kinds that make and keep its items. NO STATE IS SHOWN TO MEET THE
CONDITION IN FRONT, AND A MEMBER OF THE HEAD IS PROVED AT `storedPublicFiles` AND `zGap` ALONE (AT secondHashFunction; SIDE
LIBRARY AtFullSide/Top/). Most clauses speak only where a reader
answers; that one answers is not shown.
Limits. A JOINING. At the second hash function and the full size, as the head stands. Kx is
`kxAll3`, as it stands. Nothing on soundness.

-/
import Johnson.P5J.K09Ok0C
import Johnson.P5T.StaticWholeAtMg
import Johnson.P5T.DigStaticAtMg
import Johnson.Desc.First.Link.Law.PosPlanBuilt
import Johnson.Desc.First.Link.Law.FitsMsBuilt
import Johnson.P1K9R.AreadyClosed
import Johnson.Desc.First.Link.Law.K6HeardAtBatch
import Johnson.Desc.First.Link.Law.JoinAtBatch
import Johnson.Desc.Kinds.Law.ReadsNamed
import Johnson.Goal.Meaning.HeadCondScope

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
open VerifiableInference.Desc.LinkJoin (fits_built ms_built k6_at_347 join_of_leftOn)
open VerifiableInference.Desc.K9Asks (posPlan_layers posPlan_attention posPlan_head h0_of_head)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

set_option quotPrecheck false in
local notation "FrK" => frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0

/-- **THE FOUR CLOSED SENTENCES, AT EVERY BUILT SEGMENT.** -/
theorem closed_at_hd (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bs : ProofFile.PureBase}
    {base : List (Block S ProofFile.Cl)}
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) {m : ℕ} (hm : m < 25) {Xl : LinkH}
    (e3 : Bs.G₀.built[m]? = some Xl)
    {xx : VerifiableInference.Desc.First.Look.Place} {tlD : HTailF2}
    (hd : VerifiableInference.Desc.First.Look.digAt (At.X Zp) m = some (xx, tlD)) :
    K9Closed Xl tlD :=
  ⟨h.toAtMg.staticOk_ground O.blank hm e3, h.toAtMg.digStatic_ground O.blank hm e3 hd,
    fits_built h.scope h.reads O.pub O.blank hm e3, ms_built h.scope h.reads O.pub O.blank hm e3⟩

/-- The head's plan names the array of reads. -/
theorem reads_at_hd {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) :
    Bs.G₀.W.H.tl.ix.U.getD 2 none = some (readsOf Bs.G₀.W) := by
  have e : Bs.G₀.W.H.tl.ix.U.getD 2 none = some 0 :=
    VerifiableInference.Desc.Kinds.Head.Law.ReadsNamed.public_third O.public
  unfold VerifiableInference.Desc.Kinds.Head.Law.readsOf
  rw [e]
  rfl

/-! ## The bare promise under the condition in front -/

/-- **AT A LAYERS' LINK.** -/
theorem ok0_layers_hd (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bs : ProofFile.PureBase}
    {base : List (Block S ProofFile.Cl)}
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) {g : ℕ} (hg : g < 12) {Xl : LinkH}
    (e3 : Bs.G₀.built[2 * g]? = some Xl)
    {xx : VerifiableInference.Desc.First.Look.Place} {tlD : HTailF2}
    (hd : VerifiableInference.Desc.First.Look.digAt (At.X Zp) (2 * g) = some (xx, tlD))
    {p4 : OnBytes.Desc.First.K4.Par} (hk : LPFK9.k4ParAt Zp Bs.G₀ (2 * g) = some p4)
    (z : ProofFile.InstPub) (u : HTailF2) (lm : ℕ) {pC pD : VerifiableInference.Desc.First.Look.P}
    (hC : placeAt (At.X Zp) (2 * g) false = some pC)
    (hD : placeAt (At.X Zp) (2 * g) true = some pD) :
    ∀ a : S × (FrK).E.Str, onTR h.𝔇.N (mgAll h.𝔇 mgBase) fullLinks At.ps (fun s : S => (z, s))
      (VerifiableInference.Desc.LinkJoin.RchAt (F := FrK) h.toAtMg.rch z)
      (batchAt fullLinks At.ps (2 * g)) a →
      (fun q => OkLayers p4 (ProofFile.k8NU Bs.G₀ Xl) tlD q ∧ kxAll3 pC.lm pC.first lm pD.first q)
        (fixed9 (phiAll u psiAll) a.1) := by
  obtain ⟨hP, hgp, -⟩ := P1K9.k4Par_of_open h.scope h.reads O g hg p4 hk
  exact ok0_layersC h O hg e3 z p4 _ tlD u lm hC hD
    (closed_at_hd h O (by omega : 2 * g < 25) e3 hd) (posPlan_layers h.scope h.reads O hg e3)
    (h0_of_head h.toAtMg O (by omega : 2 * g < 25) e3) hP hgp

/-- **AT AN ATTENTION LINK.** -/
theorem ok0_att_hd (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bs : ProofFile.PureBase}
    {base : List (Block S ProofFile.Cl)}
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) {g : ℕ} (hg : g < 12) {A : Attention.Plan}
    (hA : Bs.G₀.W.A[g]? = some A) {Xl : LinkH} (e3 : Bs.G₀.built[2 * g + 1]? = some Xl)
    {xx : VerifiableInference.Desc.First.Look.Place} {tlD : HTailF2}
    (hd : VerifiableInference.Desc.First.Look.digAt (At.X Zp) (2 * g + 1) = some (xx, tlD))
    (z : ProofFile.InstPub) (u : HTailF2) (lm : ℕ) {pC pD : VerifiableInference.Desc.First.Look.P}
    (hC : placeAt (At.X Zp) (2 * g + 1) false = some pC)
    (hD : placeAt (At.X Zp) (2 * g + 1) true = some pD) :
    ∀ a : S × (FrK).E.Str, onTR h.𝔇.N (mgAll h.𝔇 mgBase) fullLinks At.ps (fun s : S => (z, s))
      (VerifiableInference.Desc.LinkJoin.RchAt (F := FrK) h.toAtMg.rch z)
      (batchAt fullLinks At.ps (2 * g + 1)) a →
      (fun q => OkAtt rdAll (parCOf A) (ProofFile.k8NU Bs.G₀ Xl) tlD q ∧
          kxAll3 pC.lm pC.first lm pD.first q)
        (fixed9 (phiAll u psiAll) a.1) :=
  ok0_attC h O hg hA e3 z _ tlD u lm hC hD (closed_at_hd h O (by omega : 2 * g + 1 < 25) e3 hd)
    (posPlan_attention h.scope h.reads O hg e3)
    (h0_of_head h.toAtMg O (by omega : 2 * g + 1 < 25) e3)

/-- **AT THE HEAD's LINK.** -/
theorem ok0_head_hd (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bs : ProofFile.PureBase}
    {base : List (Block S ProofFile.Cl)}
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) {Xl : LinkH}
    (e3 : Bs.G₀.built[24]? = some Xl)
    {xx : VerifiableInference.Desc.First.Look.Place} {tlD : HTailF2}
    (hd : VerifiableInference.Desc.First.Look.digAt (At.X Zp) 24 = some (xx, tlD))
    (z : ProofFile.InstPub) (u : HTailF2) (lm : ℕ) {pC pD : VerifiableInference.Desc.First.Look.P}
    (hC : placeAt (At.X Zp) 24 false = some pC) (hD : placeAt (At.X Zp) 24 true = some pD) :
    ∀ a : S × (FrK).E.Str, onTR h.𝔇.N (mgAll h.𝔇 mgBase) fullLinks At.ps (fun s : S => (z, s))
      (VerifiableInference.Desc.LinkJoin.RchAt (F := FrK) h.toAtMg.rch z)
      (batchAt fullLinks At.ps 24) a →
      (fun q => OkHead Bs.G₀.W.hS (readsOf Bs.G₀.W) (parOf Bs.G₀.W.hS (workOf Bs.G₀.W)) kapAll
          (ProofFile.k8NU Bs.G₀ Xl) tlD q ∧
          kxAll3 pC.lm pC.first lm pD.first q)
        (fixed9 (phiAll u psiAll) a.1) := by
  refine ok0_headC h O e3 z _ _ _ _ tlD u lm hC hD (closed_at_hd h O (by decide : 24 < 25) e3 hd)
    (posPlan_head h.scope h.reads O e3) (h0_of_head h.toAtMg O (by decide : 24 < 25) e3)
    (reads_at_hd O)
    (VerifiableInference.Desc.Kinds.Head.Law.InScope.ok_in_scope h.scope h.reads O.public _) rfl
    ?_ ?_
  · intro a ho
    obtain ⟨-, -, hq, -, -⟩ := front_at_mg h O (by decide : 24 < 25) z a ho
    exact k6_at_347 h.scope h.reads O h.laid.planOk (phiAll u psiAll) kapAll (hkap_all u)
      ((z, a.1), a.2) hq
  · intro a ho
    obtain ⟨pl, -, ⟨hCs, -, LC⟩, -⟩ := leftC_at h (by decide : 24 < 25) z a ho
    exact join_of_leftOn (phiAll u psiAll) kapAll (hkap_all u) LC

/-! ## The field's text -/

theorem aready_layers_hd (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bs : ProofFile.PureBase}
    {base : List (Block S ProofFile.Cl)}
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) {g : ℕ} (hg : g < 12) {Xl : LinkH}
    (e3 : Bs.G₀.built[2 * g]? = some Xl)
    {xx : VerifiableInference.Desc.First.Look.Place} {tlD : HTailF2}
    (hd : VerifiableInference.Desc.First.Look.digAt (At.X Zp) (2 * g) = some (xx, tlD))
    {p4 : OnBytes.Desc.First.K4.Par} (hk : LPFK9.k4ParAt Zp Bs.G₀ (2 * g) = some p4)
    (z : ProofFile.InstPub) (p : Where) (u : HTailF2) (lm : ℕ)
    {pC pD : VerifiableInference.Desc.First.Look.P}
    (hC : placeAt (At.X Zp) (2 * g) false = some pC)
    (hD : placeAt (At.X Zp) (2 * g) true = some pD) :
    ∀ a : S × (FrK).E.Str, ((onTR h.𝔇.N (mgAll h.𝔇 mgBase) fullLinks At.ps (fun s : S => (z, s))
      (VerifiableInference.Desc.LinkJoin.RchAt (F := FrK) h.toAtMg.rch z)
      (batchAt fullLinks At.ps (2 * g)) a ∧ k9OnA a.1 = true) ∧
        (rowsFit p.rows pi8) (fixed9 (phiAll u psiAll) a.1)) →
      (fun q => OkLayers p4 (ProofFile.k8NU Bs.G₀ Xl) tlD q ∧ kxAll3 pC.lm pC.first lm pD.first q)
        (fixed9 (phiAll u psiAll) a.1) :=
  fun a ha => ok0_layers_hd h O hg e3 hd hk z u lm hC hD a ha.1.1

theorem aready_att_hd (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bs : ProofFile.PureBase}
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
          kxAll3 pC.lm pC.first lm pD.first q)
        (fixed9 (phiAll u psiAll) a.1) :=
  fun a ha => ok0_att_hd h O hg hA e3 hd z u lm hC hD a ha.1.1

theorem aready_head_hd (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bs : ProofFile.PureBase}
    {base : List (Block S ProofFile.Cl)}
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) {Xl : LinkH}
    (e3 : Bs.G₀.built[24]? = some Xl)
    {xx : VerifiableInference.Desc.First.Look.Place} {tlD : HTailF2}
    (hd : VerifiableInference.Desc.First.Look.digAt (At.X Zp) 24 = some (xx, tlD))
    (z : ProofFile.InstPub) (p : Where) (u : HTailF2) (lm : ℕ)
    {pC pD : VerifiableInference.Desc.First.Look.P}
    (hC : placeAt (At.X Zp) 24 false = some pC) (hD : placeAt (At.X Zp) 24 true = some pD) :
    ∀ a : S × (FrK).E.Str, ((onTR h.𝔇.N (mgAll h.𝔇 mgBase) fullLinks At.ps (fun s : S => (z, s))
      (VerifiableInference.Desc.LinkJoin.RchAt (F := FrK) h.toAtMg.rch z)
      (batchAt fullLinks At.ps 24) a ∧ k9OnA a.1 = true) ∧
        (rowsFit p.rows pi8) (fixed9 (phiAll u psiAll) a.1)) →
      (fun q => OkHead Bs.G₀.W.hS (readsOf Bs.G₀.W) (parOf Bs.G₀.W.hS (workOf Bs.G₀.W)) kapAll
          (ProofFile.k8NU Bs.G₀ Xl) tlD q ∧
          kxAll3 pC.lm pC.first lm pD.first q)
        (fixed9 (phiAll u psiAll) a.1) :=
  fun a ha => ok0_head_hd h O e3 hd z u lm hC hD a ha.1.1

end P5J

#print axioms P5J.closed_at_hd
#print axioms P5J.reads_at_hd
#print axioms P5J.ok0_layers_hd
#print axioms P5J.ok0_att_hd
#print axioms P5J.ok0_head_hd
#print axioms P5J.aready_layers_hd
#print axioms P5J.aready_att_hd
#print axioms P5J.aready_head_hd
