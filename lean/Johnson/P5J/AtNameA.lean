-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/AtNameA.lean: THE HEAD OF THE CLOSED CONSTANT (AtMgA, Johnson/P5J/MgAtAll.lean) AT THE NAME, FROM ONE NAMED CONDITION; AND THAT CONDITION FROM ACCEPTS AT THE LETTERS THAT A RUN CAN MAKE. Two definitions, two theorems. A joint build of several kinds' files.
  At.Nine Z Zp Np cF : Prop: At.Five (PlanOk's share: namedThere · seatsNamedC · seatsFitP · endsThere · radIsB) AND AtMgA's share: (headAt (X Zp)).isSome · fullShapeB (P13 Zp).lin (it gives cols13) · At.OptsOk Zp Z.lay (seven Bools) · k3SeatsB.
  At.Conds Z : Prop: these at whatever letters the laid value opens: **THE WHOLE OF WHAT THE HEAD ASKS BESIDE "in scope · live · readFiles returns": ONE NAME FOR A LAW's LIST OF HYPOTHESES.**
  headA_at_name: in scope · live · readFiles returns · At.Conds Z → ∃ Zp Np cF x, AtMgA OnBytes.secondHashFunction Z (dpZ Z) (theProofRun (asDescriptionFiles Z)) Zp Np cF x.
  conds_of_run: At.Conds Z where At.Nine holds at pubPlain secondHashFunction's · placesOfMade's · onlineFirstChainAt's values.
None of these is itself a test that verify() runs: they are named conditions with code. In scope they follow from its tests: some by the road "laid ⇒ the pins accept ⇒ the plan's parts are the written ones", each a closed Bool at the written value, the others from "laid" and `rowsRead Z` and, for k3SeatsB, the yes of `protocolDataWellFormed`: `P5J.pins_of_laid` (Johnson/Goal/Skeleton/PinsOfLaid.lean), `P5J.nine_of_laid`, `P5J.conds_of_laid` (CondsOfLaid.lean beside it).
THE RANGE: At.Conds Z IS A CONDITION AT ONE Z. In scope the scale file and eight numbers of the policy are free. As a hypothesis "for every Z in scope and live" ONE Z at which a condition fails makes it false, and a top that takes it says nothing at any files; taken at one Z it narrows what is said to that Z. Over the scope six of the nine are theorems under "laid"; three ask `rowsRead Z`, had where `protocolDataWellFormed` accepts: `P5J.nine_of_laid`, `P5J.owed_of_live`.
Limits. This file shows no condition to hold. At OnBytes.secondHashFunction. The full size alone. No member is shown here. At `VerifierAndGoals.storedPublicFiles` and `VerifierAndGoals.zGap` alone (the library's two written sets of public files, not the release's files), at secondHashFunction, with `fixedConfigurationDigest` in the digest's place, `AtFullSide.Top.headMember_zFull` and `headMember_zGap` (AtFullSide/Top/, a side library) prove a member of the head `P5J.AtMgA` (the first also that `protocolDataWellFormed` accepts and that `rowsRead` holds); their statements do not name `At.Nine` or `At.Conds`. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.P5J.MgAtAll
import Johnson.P5J.TestsAtRun
import Johnson.P5J.Cols13

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P5J
open VerifiableInference.Desc (Chain)
open VerifierAndGoals (asDescriptionFiles)
open FlashProve (protocolDataWellFormed theProofRun)
open VerifierAndGoals.AtTheName (dpZ)

/-- What the closed constant's head asks, at letters. -/
def At.Nine (Z : VerifierAndGoals.PublicFiles) (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain TS ProofFile.Cl) : Prop :=
  At.Five Z Zp Np cF ∧
  (VerifiableInference.Desc.Kinds.Head.Law.headAt (At.X Zp)).isSome = true ∧
  Desc.K14.Law.fullShapeB (At.P13 Zp).lin = true ∧
  At.OptsOk Zp Z.lay ∧
  At.k3SeatsB Zp cF Z.lay = true

/-- **The one named condition.** -/
def At.Conds (Z : VerifierAndGoals.PublicFiles) : Prop :=
  ∀ Zp Np cF, LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL (dpZ Z) (theProofRun (asDescriptionFiles Z)) Zp Np cF →
    At.Nine Z Zp Np cF

/-- **THE CLOSED CONSTANT's HEAD AT THE NAME.** -/
theorem headA_at_name {Z : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Z = true)
    (hl : protocolDataWellFormed (asDescriptionFiles Z) = true) {pp : Inst.Model.ScalesAndPolicy} (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (C : At.Conds Z) :
    ∃ Zp Np cF x, AtMgA OnBytes.secondHashFunction Z (dpZ Z) (theProofRun (asDescriptionFiles Z)) Zp Np cF x := by
  obtain ⟨Zp, Np, cF, h⟩ := head_of_tests hZ hl hR (fun Zp Np cF L => (C Zp Np cF L).1)
  obtain ⟨-, hx, hs, ho, hk⟩ := C Zp Np cF h.laid
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 hx
  exact ⟨Zp, Np, cF, x, { h with headAt := hx, cols13 := At.cols13_of Zp hs, opts := ho, k3 := hk }⟩

/-- **The condition is met where the nine hold at the three letters that a run can make.** -/
theorem conds_of_run {Z : VerifierAndGoals.PublicFiles} {Zp₀ : ProofFile.Pub} {Np₀ : H2U.Places4} {cF₀ : Chain TS ProofFile.Cl}
    (hp : ProofFile.pubPlain OnBytes.secondHashFunction Z.pol Z.lay Z.KL = .ok Zp₀)
    (hn : H2U.placesOfMade Zp₀.made = .ok Np₀) (hc : ProofFile.onlineFirstChainAt Zp₀ = .ok cF₀)
    (T : At.Nine Z Zp₀ Np₀ cF₀) : At.Conds Z := by
  intro Zp Np cF L
  obtain rfl : Zp₀ = Zp := Except.ok.inj (hp.symm.trans L.pub)
  obtain rfl : Np₀ = Np := Except.ok.inj (hn.symm.trans L.places)
  obtain rfl : cF₀ = cF := Except.ok.inj (hc.symm.trans L.chain)
  exact T

end P5J

#print axioms P5J.headA_at_name
#print axioms P5J.conds_of_run
