-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P2LawR/LastLeftOfCoreJ.lean: THE JOIN's FIRST HALF ONCE MORE, WITH planOk₃_at_join's OWN
PREMISE C IN THE PLACE OF THE CLOSED TEST core: `AtMgA.LastLeftAt` from the head,
K2Told, the shared table's named tests, three ends (hn · hE · hEnd), C, and LastLeft's own hRc and
hS. One theorem: calls. WHY. A file that
proves a FIELD of PlanCore₃ in its own text can be laid in through C as it is
(coreJ_at_head); through the test core it would want the converse law "field → test = true".
Johnson/P2LawR/LastLeftOfTwo.lean (core as a closed test, for a file of evaluations) stands
beside this file and does not turn.
IS IT EMPTY? NO MEMBER. Nothing on soundness. A raised limit stands in this file (maxRecDepth
40000).
-/
import Johnson.P5J.L0.LastLeftB
import Johnson.P5J.L0.PlanAtJoin
import Johnson.Desc.Book.ThreeAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P5J

open Meaning
open Inst.Model
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun OnBytes.Maker OnBytes.Flat
open OnBytes.Road OnBytes.RunA
open Iop Prob _root_.Run _root_.Run.PQ
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.Last
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Plain VerifiableInference.Desc.K12.Coin
open VerifiableInference.Desc.Shared VerifiableInference.Desc.Last
open VerifiableInference.Desc.Third (SharedOut firstOfS sharedOfEnd)
open VerifiableInference.Desc.Third.Law
open VerifiableInference.Desc.First (ModelPart Item Numbers openSets sampledIn start)
open _root_.Desc.K14 (St)
open _root_.Desc.K14.Law
open ToldDesc (p14At)
open LLT25

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r' : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **LastLeftAt from the head, K2Told, the named tests, three ends, C, hRc and hS.** -/
theorem AtMgA.lastLeft_of_coreJ (h : AtMgA OnBytes.secondHashFunction Z D r' Zp Np cF x) (hK :
                _root_.Meaning.Carry.K2Told) (hT : Sh.Tests h.toAtMg.shPlan) (hn : 1 < (D.at frS.P.T.a).t₂) (hE
                : (At.N Zp cF).index.1 < (D.at frS.P.T.a).t₁ ∧ (At.N Zp cF).w.1 < (D.at frS.P.T.a).t₁) (hEnd :
                sampledBelow ((D.at frS.P.T.a).t₁ + (D.at frS.P.T.a).t₂) (At.N Zp cF) ((openSets fullLinks
                (First.flatPlaces true fullLinks true) (start fullLinks))[(First.flatPlaces true fullLinks
                true).length]?.getD []) = true ∧ (At.N Zp cF).w ∈ sampledIn (At.N Zp cF) ((openSets fullLinks
                (First.flatPlaces true fullLinks true) (start fullLinks))[(First.flatPlaces true fullLinks
                true).length]?.getD []) ∧ (At.N Zp cF).index ∈ sampledIn (At.N Zp cF) ((openSets fullLinks
                (First.flatPlaces true fullLinks true) (start fullLinks))[(First.flatPlaces true fullLinks
                true).length]?.getD [])) (C : ∀ dB dt, L0.StretchJ OnBytes.secondHashFunction D Zp Np cF dB dt → L0.CoreJ
                OnBytes.secondHashFunction Z D Zp Np cF (L0.sevenJ OnBytes.secondHashFunction Zp Np cF) dB dt (L0.ldAt Zp)) (hRc : ∀ q
                                        y, ocEnd (L0.getL OnBytes.secondHashFunction Zp Np cF) (At.N Zp cF) (h.toAtMg.mq h.𝔇) fullLinks
                                        (First.flatPlaces true fullLinks true) q y → h.toAtMg.rc q → ((L0.getL OnBytes.secondHashFunction Zp Np cF)
                                        q).2.failed = none → ToldDesc.rcLastB 0 (vAt Zp (At.N Zp cF)) (L0.ldAt Zp) (p14At Zp).codes
                                        ((L0.getL OnBytes.secondHashFunction Zp Np cF) q).2 = true) (hS : ∀ q y, ocEnd (L0.getL OnBytes.secondHashFunction Zp Np
                                                    cF) (At.N Zp cF) (h.toAtMg.mq h.𝔇) fullLinks (First.flatPlaces true fullLinks true) q y →
                                                    h.toAtMg.rc q → ((L0.getL OnBytes.secondHashFunction Zp Np cF) q).2.failed = none → ∀ f, firstOfS ((L0.getL
                                                                OnBytes.secondHashFunction Zp Np cF) q).2 = some f → SeatsNumber (At.seats Zp) f.book) :
    h.LastLeftAt := by
  obtain ⟨dB, dt, hP⟩ := L0.planOk₃_at_join h.toAtMg (L0.ldAt Zp) hn hE hEnd C
  have e : L0.l3At OnBytes.secondHashFunction D Zp Np cF = dB :: dt := hP.stretch
  unfold AtMgA.LastLeftAt
  rw [e]
  exact h.left_of_leftB ⟨hT, hRc, hP, hS,
    fun p hp _ => VerifiableInference.Desc.Book.three_at_head h.toAtMg hK p hp.1⟩

end P5J

#print axioms P5J.AtMgA.lastLeft_of_coreJ
