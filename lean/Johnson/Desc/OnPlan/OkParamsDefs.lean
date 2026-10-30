-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/OnPlan/OkParamsDefs.lean: one test on a planner's answer p: nine
clauses on the parameters of the proof file's three chains, and the five terms of p that it and its
laws name. Definitions with code alone; no theorem. Over files of the library's build alone.

THIS FILE STANDS OVER NO FILE THAT IMPORTS Mathlib, so that running code can ask the test. No law on
these definitions is in this file.

Main names:
  proofFirst p: the first chain's parameters as read. proofTail p: what is public about the proof
    file's tail (Proof.tailPublic), at the table's name that holds nothing (Maker.noTable): the very
    term in the proof file's decision (Maker.decideProof, OnBytes/Maker/Decide3.lean).
  proofWu p, proofStage₀ p, proofStages p: what linWithU returns at the tail's test on the table;
    the first stage of that test's own proximity test; the stages behind it. They are total: where
    linWithU returns nothing proofWu is the empty array; where the list of stages is empty
    proofStage₀ is the type's default value and proofStages the empty list. UNDER A YES OF THE TEST
    THESE DEFAULTS ARE IDLE: lines (7) and (8).
  Ok.params p: **the test**: (1) the first chain's plan has one sample; (2) its masks ride; (3), (4)
    the shared and the second chain's plans have one sample each; (5) the masks of the test on the
    table ride; (6) that test needs no split of its own tree; (7) linWithU returns; (8) the list of
    its own proximity test's stages is not empty; (9) the first chain has a link.

What is not claimed. THAT THE TEST SAYS YES AT ANY p: nothing is evaluated here. That these nine are
all that the laws which have them as premises ask of public data (no such law is in this directory).
Whether clauses (5) and (9) follow by themselves at a planner's answer has not been looked into.
Nothing on soundness, on an honest prover or on hiding.

-/
import OnBytes.Maker.Decide3
import OnBytes.Model.Verify

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open OnBytes

/-- The first chain's parameters in a planner's answer. -/
abbrev proofFirst (p : Model.Verify.Planned) : Params.First := p.chains.proof.first

/-- What is public about the proof file's tail, as the proof file's decision has it. -/
abbrev proofTail (p : Model.Verify.Planned) : Proof.TailPublic :=
  Proof.tailPublic p.chains.proof Maker.noTable

/-- What linWithU returns at the tail's test on the table; the empty array where it returns
nothing. -/
def proofWu (p : Model.Verify.Planned) : Array OracleNotice :=
  (linWithU (proofTail p).lin).getD #[]

/-- The first stage of the test's own proximity test; the default value where there is none. -/
def proofStage₀ (p : Model.Verify.Planned) : Params.IoppStage :=
  (proofTail p).lin.testOwn.headD default

/-- The stages behind the first. -/
def proofStages (p : Model.Verify.Planned) : List Params.IoppStage :=
  (proofTail p).lin.testOwn.tail

/-- **Nine clauses on the parameters of the proof file's three chains.** -/
def Ok.params (p : Model.Verify.Planned) : Bool :=
  (proofFirst p).given.plan.samples == 1 && (proofFirst p).shape.choice.masksRide &&
    (proofTail p).shared.given.plan.samples == 1 && (proofTail p).second.given.plan.samples == 1 &&
    (proofTail p).lin.choice.masksRide && !(proofTail p).lin.ownSplitNeeded &&
    (linWithU (proofTail p).lin).isSome && !(proofTail p).lin.testOwn.isEmpty &&
    !(proofFirst p).shape.link.isEmpty
end VerifiableInference.OnPublicFiles
