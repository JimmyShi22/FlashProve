-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5J/InsideAtMg.lean (kind K9): THE FIELD Ainside OF A LINK's «REST» AT THE CONSTANT's OWN LETTERS: the letters at which `AtMgA.K9Sorts` (K09Sorts.lean) asks `CoreRest2`. Theorems: calls.

What is said.
  `AtMg.layoutOk`: where the value is laid (every o): the programs' own test on the layout accepts at the facts' own public numbers: reqLayoutOk (At.foldD Zp cF Ld).sent.codes … .shape … .layout = true: by
    `pub_layoutOk` (Johnson/IMR/LayoutOkPub.lean: the first state is made by S.startP, which asks that test). NO KERNEL LINE, NO WRITTEN VALUE, NO SCOPE.
  `AtMgA.ainside`: **h : AtMgA OnBytes.secondHashFunction … · FF : FoldFacts h.toAtMg.rch (fun a => a.1) (At.foldD Zp cF Ld) At.reqW fullLinks At.ps [K9Sorts' own first conjunct] ⊢ THE FIELD's TEXT at o2 := onTR h.𝔇.N (mgAll h.𝔇 mgBase) fullLinks
    At.ps (fun s => (z, s)) (RchAt h.toAtMg.rch z) (k + 1 + 1): every z, every k.** So at all 25 links and all three sorts.

Limits. AtMgA and FoldFacts are premises. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.InsideOfFacts
import Johnson.IMR.LayoutOkPub
import Johnson.P5J.FoldAt
import Johnson.P5J.MgAtAll
import Johnson.P5J.FourAtMg

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P5J

open Meaning
open Inst.Model
open OnBytes OnBytes.Model OnBytes.Road OnBytes.Flat OnBytes.Maker OnBytes.Slice OnBytes.RunA
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Block FileDescription Place Strs Wit Link Chain)
open VerifiableInference.Desc.First (S ModelPart Numbers FoldFacts)
open VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open VerifiableInference.Desc.K9 (atS)
open VerifiableInference.Desc.K9L (Inside)
open VerifiableInference.Desc.LinkJoin (ainside_of_facts onTR)
open _root_.Run _root_.Run.PQ

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

set_option quotPrecheck false in
local notation "FrK" => frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0

/-- **THE PROGRAMS' OWN TEST ON THE LAYOUT ACCEPTS AT THE FACTS' PUBLIC NUMBERS.** -/
theorem AtMg.layoutOk {o : ProofFile.SecondHashFunctionArgument} (h : AtMg o Z D r Zp Np cF)
    (Ld : VerifiableInference.Desc.K12.Door.Laid) :
    reqLayoutOk (At.foldD Zp cF Ld).sent.codes (At.foldD Zp cF Ld).sent.shape
      (At.foldD Zp cF Ld).sent.layout = true :=
  Meaning.K2.pub_layoutOk h.laid.pub

/-- **THE FIELD Ainside AT K9Sorts' LETTERS.** -/
theorem AtMgA.ainside (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (Ld : VerifiableInference.Desc.K12.Door.Laid)
    (FF : FoldFacts h.toAtMg.rch (fun a => a.1) (At.foldD Zp cF Ld) At.reqW fullLinks At.ps)
    (z : (F0T OnBytes.secondHashFunction Zp Np cF).XiPub) (k : ℕ) :
    ∀ s : S × (FrK).E.Str, onTR h.𝔇.N (mgAll h.𝔇 mgBase) fullLinks At.ps (fun s : S => (z, s))
        (VerifiableInference.Desc.LinkJoin.RchAt h.toAtMg.rch z) (k + 1 + 1) s →
      ∀ a, atS.get? s.1 = some a → ∀ born name r,
        reqArray a.L.check.rows.layout born name = some r → ∀ bl ∈ r.blocks, Inside r bl :=
  ainside_of_facts (F := FrK) FF (h.toAtMg.layoutOk Ld) h.𝔇.N (mgAll h.𝔇 mgBase) fullLinks At.ps z
    (k + 1 + 1)

end P5J

#print axioms P5J.AtMg.layoutOk
#print axioms P5J.AtMgA.ainside
