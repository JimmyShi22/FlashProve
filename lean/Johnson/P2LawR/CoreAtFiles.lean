-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P2LawR/CoreAtFiles.lean: THE ONE FIELD OF AtMgA.LastRest (core;
Johnson/P2LawR/LastLeftAtHead.lean) AS ONE Bool OF THE PUBLIC FILES ALONE. One definition, two
theorems.

  P5J.coreAt Z         closed in Z alone: it makes D, Zp, Np, cF of Z's three files itself
  (lettersOf,
                   Johnson/P2LawR/HeadLetters.lean), opens the third piece's stretch
                   (L0.l3At) and asks coreB there, at the very terms of the field
                   core; false where a call fails or the stretch is empty
  P5J.rest_of_coreAt   coreAt Z = true → at EVERY head over Z at OnBytes.secondHashFunction: h.LastRest
  P5J.lastLeft_of_coreAt   so h.LastLeftAt there
WHY. A top that binds "∀ Zp Np cF x (h : AtMgA …), h.LastRest" asks core at every head; an
evaluation shows it at one triple. With this file the top's hypothesis can be "coreAt Z = true": the
very constant that a sheet evaluates.
IS IT EMPTY? coreAt IS EVALUATED BY NOBODY AT THIS TERM. Whether Lean makes code for it is not tried
here (coreB stands in a noncomputable section). If it is false at the real files, the theorems say
nothing of them. NO MEMBER. The full size alone.
Nothing on soundness. A raised limit stands in this file (maxRecDepth 40000).
-/
import Johnson.P2LawR.LastLeftAtHead
import Johnson.P2LawR.HeadLetters

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

/-- **core as one Bool of the public files.** -/
def coreAt (Z : VerifierAndGoals.PublicFiles) : Bool :=
  match lettersOf OnBytes.secondHashFunction Z.pol Z.lay Z.KL with
  | none => false
  | some (D, Zp, Np, cF) =>
    match L0.l3At OnBytes.secondHashFunction D Zp Np cF with
    | [] => false
    | dB :: dt =>
        P2Law.PlanLeft.coreB OnBytes.secondHashFunction ProofFile.pureRoad.links Zp Np cF (D.at frS.P.T.a)
          (F0T OnBytes.secondHashFunction Zp Np cF) (At.arr Zp) dB dt (At.ms Zp Z.lay)
          (L0.ms2J (L0.sevenJ OnBytes.secondHashFunction Zp Np cF)) (At.N Zp cF)
          (L0.nsJ (L0.sevenJ OnBytes.secondHashFunction Zp Np cF)) H2K.Member.rWFull
          ((At.N Zp cF).treesAt none) 0 1 (vAt Zp (At.N Zp cF)) (L0.ldAt Zp)

/-- **From that one Bool: LastRest at every head over these files.** -/
theorem rest_of_coreAt (hc : coreAt Z = true) (h : AtMgA OnBytes.secondHashFunction Z D r' Zp Np cF x) :
    h.LastRest := by
  unfold coreAt at hc
  rw [h.toAtMg.letters] at hc
  refine ⟨?_⟩
  cases e : L0.l3At OnBytes.secondHashFunction D Zp Np cF with
  | nil =>
    simp only [e] at hc
    exact absurd hc (by decide)
  | cons dB dt =>
    simp only [e] at hc
    exact hc

/-- **So what is left of the last chain's field, at every head over these files.** -/
theorem lastLeft_of_coreAt (hc : coreAt Z = true) (h : AtMgA OnBytes.secondHashFunction Z D r' Zp Np cF x) :
    h.LastLeftAt :=
  h.lastLeft_at_head (rest_of_coreAt hc h)

end P5J

#print axioms P5J.rest_of_coreAt
#print axioms P5J.lastLeft_of_coreAt
