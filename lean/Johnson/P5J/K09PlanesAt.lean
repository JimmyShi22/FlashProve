-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5J/K09PlanesAt.lean (kind K9): THE TWO STRUCTURES `PlanesAttOk` AND
`PlanesHeadOk`, WHOLE (Johnson/Desc/First/Link/Law/OkPlanes.lean: what the caller's
clauses of the lookup's runs "planes" and "join" ask of the fixed part) AT THE CLOSED CONSTANT: AT
WHAT IS FIXED AT EVERY STATE WITH THE TABLE's PROMISE IN FRONT OF THE BATCHING OF AN ATTENTION
SEGMENT (12) AND OF THE HEAD's. Theorems: joins, in the form of `ownA_at`
(K09OwnA.lean), by its own calls.

  `planesAtt_mg`, `keysEnts_mg`: **the two clauses at rd := rdAll, c := parCOf A, nU := ProofFile.k8NU
    Bs.G₀ Xl, q := fixed9 (phiAll u psiAll) a.1**, a with the promise at the batching's number of
    segment 2 g + 1, g < 12; A the plan's entry g.
  `planesAttOk_mg`: **`PlanesAttOk rdAll (parCOf A) nU q`: the structure whole (two fields).**
  `planesHeadOk_mg`: **`PlanesHeadOk iU3 kapAll nU q`: the structure whole (it has one field).**
  `planesHead_mg`: **the clause at kap := kapAll, the same nU and q**, a with the promise at the
    head's batching's number.
What is laid in: hatt, hq, hc, hrd, hU: `ownA_at`'s calls (isAtt_at_mg; the kernel's fact that
"K5.plain" is open at that border; c := parCOf A; heard5_of_rdAll; hU_att). The static clause at
what is fixed: `core_att_at`, `core_head_at` (K09Aready.lean). `PosPlan`: posPlan_attention,
posPlan_head (PosPlanBuilt.lean: over four files beside it). h0: h0_of_head (the same).
PREMISES THAT STAY: the head (AtMgA); the opening O; the table's promise ho; **C : K9Closed Xl tlD**
(four closed sentences: had from the head and the opening by `closed_at_hd`,
Johnson/P5J/K09AreadyHd.lean); at the head hi : the plan names iU3 for the third vector
(`reads_at_hd`, the same file: from the opening).
Limits. A JOINING. No soundness statement.

-/
import Johnson.P5J.K09OwnA
import Johnson.Desc.First.Link.Law.KeysEntsAt
import Johnson.Desc.First.Link.Law.PlanesHeadAt
import Johnson.Desc.First.Link.Law.PosPlanBuilt

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
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Block FileDescription Place Link Chain)
open VerifiableInference.Desc.First (S ModelPart)
open VerifiableInference.Desc.First.Att.P (ParC parCOf readersOfK keysOfK)
open VerifiableInference.Desc.Kinds.Head (callerReaders)
open VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.K9Asks (posPlan_attention posPlan_head h0_of_head)
open VerifiableInference.Desc.PhiAll
open VerifiableInference.Desc.LinkJoin (batchAt onTR K9Closed pi8 EntsOk seatCQ planesQ hU_att
  planesAtt_at keysEnts_at planesHead_at_347)
open _root_.Desc.K14.Law (seatZ secondAt)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

set_option quotPrecheck false in
local notation "FrK" => frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0

/-- **planesAtt AT THE CONSTANT.** -/
theorem planesAtt_mg (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bs : ProofFile.PureBase}
    {base : List (Block S ProofFile.Cl)}
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) {g : ℕ} (hg : g < 12) {A : Attention.Plan}
    (hA : Bs.G₀.W.A[g]? = some A) {Xl : LinkH} (e3 : Bs.G₀.built[2 * g + 1]? = some Xl)
    (z : ProofFile.InstPub) (a : S × (FrK).E.Str)
    (ho : onTR h.𝔇.N (mgAll h.𝔇 mgBase) fullLinks At.ps (fun s : S => (z, s))
      (VerifiableInference.Desc.LinkJoin.RchAt (F := FrK) h.toAtMg.rch z)
      (batchAt fullLinks At.ps (2 * g + 1)) a) (tlD u : HTailF2) (C : K9Closed Xl tlD) :
    ∀ rr, readersOfK (seatCQ rdAll (parCOf A)) (parCOf A) (fixed9 (phiAll u psiAll) a.1) =
        some rr →
      (∀ e col f, rr.1 e col = some f →
        EntsOk (ProofFile.k8NU Bs.G₀ Xl) (fixed9 (phiAll u psiAll) a.1) [f]) ∧
        ∀ col f, rr.2 col = some f →
          EntsOk (ProofFile.k8NU Bs.G₀ Xl) (fixed9 (phiAll u psiAll) a.1) [f] := by
  obtain ⟨-, -, hq, -, -⟩ := front_at_mg h O (by omega : 2 * g + 1 < 25) z a ho
  have e : VerifiableInference.Desc.LinkJoin.frontAt (2 * g + 1) = 14 * (2 * g + 1) + 9 := by
    unfold VerifiableInference.Desc.LinkJoin.frontAt
    rw [if_neg (by omega : ¬ 2 * g + 1 = 24)]
  rw [e] at hq
  have hm : 2 * g + 1 < 25 := by omega
  have Co := core_att_at h O hg e3 z a ho (ProofFile.k8NU Bs.G₀ Xl) tlD u C
    (posPlan_attention h.scope h.reads O hg e3)
  have h0 := h0_of_head h.toAtMg O hm e3
  have hu : a.1.failed = none := not_not.1 ho.1.2
  have e2 : (2 * g + 1) / 2 = g := by omega
  have hp : ∀ p, h.𝔇.pubD.d5.W.A[(2 * g + 1) / 2]? = some p → p = A := by
    intro p hp
    rw [e2] at hp
    have hp' : (At.X Zp).A[g]? = some p := hp
    rw [O.W] at hA
    exact Option.some.inj (hp'.symm.trans hA)
  have q2 := LPFK9.plainAsked_at (2 * g + 1) hm (att_at_full hg)
  rw [← mgAll_more_base h.𝔇] at q2
  have hU := hU_att h.scope h.reads O hg hA ((z, a.1), a.2) hq pi8 (phiAll u psiAll) u
    (fun _ => rfl)
  exact planesAtt_at h.𝔇 mgBase fullLinks At.ps (fun s : S => (z, s)) _ (2 * g + 1) a ho.1.1 hu
    (isAtt_at_mg h hg) q2 (parCOf A) (fun p e => by rw [hp p e]; exact ⟨rfl, rfl⟩)
    (phiAll u psiAll) rdAll Co.static hU h0

/-- **keysEnts AT THE CONSTANT.** -/
theorem keysEnts_mg (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bs : ProofFile.PureBase}
    {base : List (Block S ProofFile.Cl)}
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) {g : ℕ} (hg : g < 12) {A : Attention.Plan}
    (hA : Bs.G₀.W.A[g]? = some A) {Xl : LinkH} (e3 : Bs.G₀.built[2 * g + 1]? = some Xl)
    (z : ProofFile.InstPub) (a : S × (FrK).E.Str)
    (ho : onTR h.𝔇.N (mgAll h.𝔇 mgBase) fullLinks At.ps (fun s : S => (z, s))
      (VerifiableInference.Desc.LinkJoin.RchAt (F := FrK) h.toAtMg.rch z)
      (batchAt fullLinks At.ps (2 * g + 1)) a) (tlD u : HTailF2) (C : K9Closed Xl tlD) :
    ∀ KF, keysOfK (seatCQ rdAll (parCOf A)) (parCOf A) (fixed9 (phiAll u psiAll) a.1) =
        some KF →
      EntsOk (ProofFile.k8NU Bs.G₀ Xl) (fixed9 (phiAll u psiAll) a.1) KF.toList := by
  obtain ⟨-, -, hq, -, -⟩ := front_at_mg h O (by omega : 2 * g + 1 < 25) z a ho
  have e : VerifiableInference.Desc.LinkJoin.frontAt (2 * g + 1) = 14 * (2 * g + 1) + 9 := by
    unfold VerifiableInference.Desc.LinkJoin.frontAt
    rw [if_neg (by omega : ¬ 2 * g + 1 = 24)]
  rw [e] at hq
  have hm : 2 * g + 1 < 25 := by omega
  have Co := core_att_at h O hg e3 z a ho (ProofFile.k8NU Bs.G₀ Xl) tlD u C
    (posPlan_attention h.scope h.reads O hg e3)
  have h0 := h0_of_head h.toAtMg O hm e3
  have hu : a.1.failed = none := not_not.1 ho.1.2
  have e2 : (2 * g + 1) / 2 = g := by omega
  have hp : ∀ p, h.𝔇.pubD.d5.W.A[(2 * g + 1) / 2]? = some p → p = A := by
    intro p hp
    rw [e2] at hp
    have hp' : (At.X Zp).A[g]? = some p := hp
    rw [O.W] at hA
    exact Option.some.inj (hp'.symm.trans hA)
  have q2 := LPFK9.plainAsked_at (2 * g + 1) hm (att_at_full hg)
  rw [← mgAll_more_base h.𝔇] at q2
  have hU := hU_att h.scope h.reads O hg hA ((z, a.1), a.2) hq pi8 (phiAll u psiAll) u
    (fun _ => rfl)
  exact keysEnts_at h.𝔇 mgBase fullLinks At.ps (fun s : S => (z, s)) _ (2 * g + 1) a ho.1.1 hu
    (isAtt_at_mg h hg) q2 (parCOf A) (fun p e => by rw [hp p e]; exact ⟨rfl, rfl⟩)
    (phiAll u psiAll) rdAll (heard5_of_rdAll u a.1) Co.static hU h0

/-- **`PlanesAttOk` WHOLE, AT THE CONSTANT.** -/
theorem planesAttOk_mg (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bs : ProofFile.PureBase}
    {base : List (Block S ProofFile.Cl)}
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) {g : ℕ} (hg : g < 12) {A : Attention.Plan}
    (hA : Bs.G₀.W.A[g]? = some A) {Xl : LinkH} (e3 : Bs.G₀.built[2 * g + 1]? = some Xl)
    (z : ProofFile.InstPub) (a : S × (FrK).E.Str)
    (ho : onTR h.𝔇.N (mgAll h.𝔇 mgBase) fullLinks At.ps (fun s : S => (z, s))
      (VerifiableInference.Desc.LinkJoin.RchAt (F := FrK) h.toAtMg.rch z)
      (batchAt fullLinks At.ps (2 * g + 1)) a) (tlD u : HTailF2) (C : K9Closed Xl tlD) :
    VerifiableInference.Desc.LinkJoin.PlanesAttOk rdAll (parCOf A) (ProofFile.k8NU Bs.G₀ Xl)
      (fixed9 (phiAll u psiAll) a.1) :=
  ⟨planesAtt_mg h O hg hA e3 z a ho tlD u C, keysEnts_mg h O hg hA e3 z a ho tlD u C⟩

/-- **planesHead AT THE CONSTANT.** -/
theorem planesHead_mg (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bs : ProofFile.PureBase}
    {base : List (Block S ProofFile.Cl)}
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) {iU3 : ℕ}
    (hi : Bs.G₀.W.H.tl.ix.U.getD 2 none = some iU3) {Xl : LinkH}
    (e3 : Bs.G₀.built[24]? = some Xl) (z : ProofFile.InstPub) (a : S × (FrK).E.Str)
    (ho : onTR h.𝔇.N (mgAll h.𝔇 mgBase) fullLinks At.ps (fun s : S => (z, s))
      (VerifiableInference.Desc.LinkJoin.RchAt (F := FrK) h.toAtMg.rch z)
      (batchAt fullLinks At.ps 24) a) (tlD u : HTailF2) (C : K9Closed Xl tlD) :
    ∀ rr, callerReaders (planesQ iU3 kapAll) (fixed9 (phiAll u psiAll) a.1) = some rr →
      (∀ e col f, rr.1 e col = some f →
        EntsOk (ProofFile.k8NU Bs.G₀ Xl) (fixed9 (phiAll u psiAll) a.1) [f]) ∧
        ∀ col f, rr.2 col = some f →
          EntsOk (ProofFile.k8NU Bs.G₀ Xl) (fixed9 (phiAll u psiAll) a.1) [f] := by
  obtain ⟨-, -, hq, -, -⟩ := front_at_mg h O (by decide : 24 < 25) z a ho
  have H := posPlan_head h.scope h.reads O e3
  have Co := core_head_at h O e3 z a ho (ProofFile.k8NU Bs.G₀ Xl) tlD u C H
  exact planesHead_at_347 h.scope h.reads O hi e3 H ((z, a.1), a.2) hq u
    (h0_of_head h.toAtMg O (by decide : 24 < 25) e3) Co.static

/-- **`PlanesHeadOk` WHOLE, AT THE CONSTANT.** -/
theorem planesHeadOk_mg (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bs : ProofFile.PureBase}
    {base : List (Block S ProofFile.Cl)}
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) {iU3 : ℕ}
    (hi : Bs.G₀.W.H.tl.ix.U.getD 2 none = some iU3) {Xl : LinkH}
    (e3 : Bs.G₀.built[24]? = some Xl) (z : ProofFile.InstPub) (a : S × (FrK).E.Str)
    (ho : onTR h.𝔇.N (mgAll h.𝔇 mgBase) fullLinks At.ps (fun s : S => (z, s))
      (VerifiableInference.Desc.LinkJoin.RchAt (F := FrK) h.toAtMg.rch z)
      (batchAt fullLinks At.ps 24) a) (tlD u : HTailF2) (C : K9Closed Xl tlD) :
    VerifiableInference.Desc.LinkJoin.PlanesHeadOk iU3 kapAll (ProofFile.k8NU Bs.G₀ Xl)
      (fixed9 (phiAll u psiAll) a.1) :=
  ⟨planesHead_mg h O hi e3 z a ho tlD u C⟩

end P5J

#print axioms P5J.planesAtt_mg
#print axioms P5J.keysEnts_mg
#print axioms P5J.planesAttOk_mg
#print axioms P5J.planesHead_mg
#print axioms P5J.planesHeadOk_mg
