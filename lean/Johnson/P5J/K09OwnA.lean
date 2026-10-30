-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5J/K09OwnA.lean: THE ATTENTION LINKS' THREE OWN CLAUSES (`K9OwnA`, K09Aready.lean: k5,
entsFirst, entsSecond) AT THE CLOSED CONSTANT; SO `Aready` AT AN ATTENTION LINK, ON THE SECOND ROAD,
WITH NO PREMISE ON A STATE. Theorems: joins of other files' lemmas.

How. The table's promise in front of an attention link's batching holds two public items of kind K5,
"K5.okAt" and "K5.plain"; that both are open at that border is shown by the kernel
(Johnson/LPFK9R/OkAskedFull.lean, PlainAskedFull.lean). `okAtt_k5_at` (OkK5Paid.lean) has k5 from
the first, `entsFirst_at`, `entsSecond_at` (PlainOfPromise.lean) the other two from the second.
  `att_at_full`: the written list has an attention link at 2 g + 1, g < 12. `isAtt_at_mg`: so the
    filling's own test says. `ownA_at`: **`K9OwnA rdAll (parCOf A) nU` of what is fixed**, A the
    plan's entry g. `aready_attC_closed`: **the field's text: EVERY PREMISE IS CLOSED.**
Limits. A JOINING. `K9Closed`, `PosPlan` and h0 : 0 < nU[2] are shown of nothing here. It pins c :=
`parCOf A`. Nothing on soundness.

-/
import Johnson.P5J.K09AreadyC
import Johnson.Desc.First.Link.Law.PlainOfPromise
import Johnson.Desc.First.Link.Law.AttThirdVector
import Johnson.LPFK9R.OkAskedFull
import Johnson.LPFK9R.PlainAskedFull

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

open VerifiableInference.Desc.LinkJoin (okAtt_k5_at entsFirst_at entsSecond_at hU_att)
open VerifiableInference.Desc.First.Att.P (parCOf)

/-- The written list has an attention link at 2 g + 1. -/
theorem att_at_full {g : ℕ} (hg : g < 12) : fullLinks[2 * g + 1]? = some ModelPart.attention := by
  interval_cases g <;> rfl

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

set_option quotPrecheck false in
local notation "FrK" => frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0

/-- The filling's own test says so. -/
theorem isAtt_at_mg (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {g : ℕ} (hg : g < 12) :
    h.𝔇.pubD.d5.isAtt (2 * g + 1) = true := by
  show (fullLinks[2 * g + 1]? == some ModelPart.attention) = true
  rw [att_at_full hg]
  rfl

/-- **ALL THREE OF AN ATTENTION LINK's OWN CLAUSES.** -/
theorem ownA_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bs : ProofFile.PureBase}
    {base : List (Block S ProofFile.Cl)}
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) {g : ℕ} (hg : g < 12) {A : Attention.Plan}
    (hA : Bs.G₀.W.A[g]? = some A) {Xl : LinkH} (e3 : Bs.G₀.built[2 * g + 1]? = some Xl)
    (z : ProofFile.InstPub) (a : S × (FrK).E.Str)
    (ho : onTR h.𝔇.N (mgAll h.𝔇 mgBase) fullLinks At.ps (fun s : S => (z, s))
      (VerifiableInference.Desc.LinkJoin.RchAt (F := FrK) h.toAtMg.rch z)
      (batchAt fullLinks At.ps (2 * g + 1)) a) (nU : Array ℕ) (tlD u : HTailF2)
    (C : K9Closed Xl tlD)
    (H : ∀ p, Bs.G₀.W.A[g]? = some p → PosPlan Xl.tl Xl.Fp (attShapes p.S (nScores p.S)))
    (h0 : 0 < nU.getD 2 0) : K9OwnA rdAll (parCOf A) nU (fixed9 (phiAll u psiAll) a.1) := by
  obtain ⟨-, -, hq, -, -⟩ := front_at_mg h O (by omega : 2 * g + 1 < 25) z a ho
  have e : VerifiableInference.Desc.LinkJoin.frontAt (2 * g + 1) = 14 * (2 * g + 1) + 9 := by
    unfold VerifiableInference.Desc.LinkJoin.frontAt
    rw [if_neg (by omega : ¬ 2 * g + 1 = 24)]
  rw [e] at hq
  have Co := core_att_at h O hg e3 z a ho nU tlD u C H
  have hu : a.1.failed = none := not_not.1 ho.1.2
  have hm : 2 * g + 1 < 25 := by omega
  have e2 : (2 * g + 1) / 2 = g := by omega
  have hp : ∀ p, h.𝔇.pubD.d5.W.A[(2 * g + 1) / 2]? = some p → p = A := by
    intro p hp
    rw [e2] at hp
    have hp' : (At.X Zp).A[g]? = some p := hp
    rw [O.W] at hA
    exact Option.some.inj (hp'.symm.trans hA)
  have q1 := LPFK9.okAsked_at (2 * g + 1) hm (att_at_full hg)
  have q2 := LPFK9.plainAsked_at (2 * g + 1) hm (att_at_full hg)
  rw [← mgAll_more_base h.𝔇] at q1 q2
  have hU := hU_att h.scope h.reads O hg hA ((z, a.1), a.2) hq pi8 (phiAll u psiAll) u
    (fun _ => rfl)
  exact ⟨okAtt_k5_at h.𝔇 mgBase fullLinks At.ps (fun s : S => (z, s)) _ (2 * g + 1) a ho.1.1 hu
      (isAtt_at_mg h hg) q1 (parCOf A) (fun p e => by rw [hp p e]; rfl) (phiAll u psiAll) rdAll
      (heard5_of_rdAll u a.1),
    entsFirst_at h.𝔇 mgBase fullLinks At.ps (fun s : S => (z, s)) _ (2 * g + 1) a ho.1.1 hu
      (isAtt_at_mg h hg) q2 (parCOf A) (fun p e => by rw [hp p e]; exact ⟨rfl, rfl⟩) pi8
      (phiAll u psiAll) rdAll (heard5_of_rdAll u a.1) Co.static hU h0,
    entsSecond_at h.𝔇 mgBase fullLinks At.ps (fun s : S => (z, s)) _ (2 * g + 1) a ho.1.1 hu
      (isAtt_at_mg h hg) q2 (parCOf A) (fun p e => by rw [hp p e]; exact ⟨rfl, rfl⟩) pi8
      (phiAll u psiAll) rdAll (heard5_of_rdAll u a.1) Co.static hU h0⟩

/-- **Aready AT AN ATTENTION LINK, ON THE SECOND ROAD: EVERY PREMISE IS CLOSED.** -/
theorem aready_attC_closed (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bs : ProofFile.PureBase}
    {base : List (Block S ProofFile.Cl)}
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) {g : ℕ} (hg : g < 12) {A : Attention.Plan}
    (hA : Bs.G₀.W.A[g]? = some A) {Xl : LinkH} (e3 : Bs.G₀.built[2 * g + 1]? = some Xl)
    (z : ProofFile.InstPub) (p : Where) (nU : Array ℕ) (tlD u : HTailF2) (lm : ℕ)
    {pC pD : VerifiableInference.Desc.First.Look.P}
    (hC : placeAt (At.X Zp) (2 * g + 1) false = some pC)
    (hD : placeAt (At.X Zp) (2 * g + 1) true = some pD) (C : K9Closed Xl tlD)
    (H : ∀ p, Bs.G₀.W.A[g]? = some p → PosPlan Xl.tl Xl.Fp (attShapes p.S (nScores p.S)))
    (h0 : 0 < nU.getD 2 0) :
    ∀ a : S × (FrK).E.Str, ((onTR h.𝔇.N (mgAll h.𝔇 mgBase) fullLinks At.ps (fun s : S => (z, s))
      (VerifiableInference.Desc.LinkJoin.RchAt (F := FrK) h.toAtMg.rch z)
      (batchAt fullLinks At.ps (2 * g + 1)) a ∧ k9OnA a.1 = true) ∧
        (rowsFit p.rows pi8) (fixed9 (phiAll u psiAll) a.1)) →
      (fun q => OkAtt rdAll (parCOf A) nU tlD q ∧ kxAll3 pC.lm pC.first lm pD.first q)
        (fixed9 (phiAll u psiAll) a.1) :=
  aready_attC h O hg e3 z p (parCOf A) nU tlD u lm hC hD C H
    fun a ho => ownA_at h O hg hA e3 z a ho nU tlD u C H h0

end P5J

#print axioms P5J.att_at_full
#print axioms P5J.isAtt_at_mg
#print axioms P5J.ownA_at
#print axioms P5J.aready_attC_closed
