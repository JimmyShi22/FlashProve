-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/OnPlan/OkRead.lean: a test on a planner's answer p: at the proof file's shared chain,
what the planner has sized is what is read back out of the parameter bytes. Definitions with code
alone; no theorem.

Why. A planner's answer holds the shared chain twice: as the planner sized it
(p.chains.made.sized.proof), where the groups stand by which a round's error is priced, and as its
parameter bytes are read back (p.chains.proof.shared), from which a verifier's steps take their
shape, codes and entries. A test that reads the one and a test that reads the other speak of one
chain only where the two agree.

Main names (namespace VerifiableInference.OnPublicFiles.OkD):
  readShape, readCodes, readSamples: at the shared chain the shape of the test on the table, the
    codes and the number of answers to a sample are the same in both.
  readPlans: the entries of the three plans that the planner has made for the proof file's chains,
    in which a round's error stands beside its entry, are the entries of the three plans as read
    back.
  remadeF, remadeS, remadeW: the planner's own routines for the proof file's three chains
    (firstPlan, OnBytes/Params/DeriveReq.lean; sharedPlan and secondPlan, DeriveLin.lean beside it),
    RUN ANEW at what is sized, return, and their entries are the entries as read back. These
    routines reckon each round's numbers (the positions of a test's last round among them) and its
    error out of the sizes and the setting, and refuse a plan of which a round does not hold.
    WITHOUT THEM NOTHING HERE MAKES A NUMBER ANEW: readPlans holds two copies of a number against
    each other, and the test on the made plans' verdict (heldS, Johnson/Desc/OnPlan/OkDesc.lean)
    reads the error that is STORED beside an entry, not the entry's numbers: a plan with one
    position fewer in both copies passed both.
  settingZ, madeSets: p holds the setting (the target among its fields) in five places: the
    parameter file's lines in p.X, what is sized, and each made plan. settingZ: the second is what
    the first fixes (settingOf, OnBytes/Params/Setting.lean). madeSets: the last three are the
    second.
  read p: **the test**: the nine.

WHAT THE NINE PIN, AND WHAT NOT. They pin: the entries as read back of all three chains are what the
planner's own routines return at p's OWN sizes and p.X, at the target of p.X's own parameter lines.
THEY DO NOT PIN THAT THE SIZES AND p.X COME OF THE PUBLIC FILES, NOR WHICH TARGET A CALLER ASKS: a
planner's answer at another parameter file passes, and must. That p is the planner's answer at the
public files is no test's to say: it is so where p is MADE of them (Model.Verify.planned).

IT STANDS OVER NO FILE THAT IMPORTS Mathlib: it is meant to be asked by running code.

THESE ARE NOT ALL: of the first chain readPlans and remadeF speak, of its entries: its shape,
layout and codes as sized are held against nothing.

What is not claimed. THAT ANY OF THEM SAYS YES AT ANY p: nothing is evaluated here. Nothing on
soundness, on an honest prover or on hiding.

-/
import OnBytes.Model.Verify

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles.OkD
open OnBytes

/-- The shape of the test on the table is the same as sized and as read back. -/
def readShape (p : Model.Verify.Planned) : Bool :=
  decide (p.chains.made.sized.proof.batch.shape = p.chains.proof.shared.lin)

/-- So are the codes. -/
def readCodes (p : Model.Verify.Planned) : Bool :=
  decide (p.chains.made.sized.proof.codes = p.chains.proof.shared.codes)

/-- So is the number of answers to a sample. -/
def readSamples (p : Model.Verify.Planned) : Bool :=
  p.chains.made.sized.proof.set.samples == p.chains.proof.shared.given.plan.samples

/-- The three made plans' entries are the three plans' entries as read back. -/
def readPlans (p : Model.Verify.Planned) : Bool :=
  decide (p.chains.made.proof.map (·.plan.entries) =
    [p.chains.proof.first.given.plan.entries, p.chains.proof.shared.given.plan.entries,
      p.chains.proof.second.given.plan.entries])

/-- The planner's own routine for the first chain, run anew at what is sized and at the sub-proofs'
sizes made out of p.X and the links that are sized, returns, and its entries are the first chain's
entries as read back. -/
def remadeF (p : Model.Verify.Planned) : Bool :=
  let z := p.chains.made.sized.proof
  match Params.firstPlan z (Model.Verify.subproofsWith p.X z.request.link) with
  | .ok P => decide (P.plan.entries = p.chains.proof.first.given.plan.entries)
  | .error _ => false

/-- The same for the shared chain. -/
def remadeS (p : Model.Verify.Planned) : Bool :=
  let z := p.chains.made.sized.proof
  match Params.sharedPlan z.set z.codes z.batch with
  | .ok P => decide (P.plan.entries = p.chains.proof.shared.given.plan.entries)
  | .error _ => false

/-- The same for the second chain. -/
def remadeW (p : Model.Verify.Planned) : Bool :=
  let z := p.chains.made.sized.proof
  match Params.secondPlan z.set z.batch with
  | .ok P => decide (P.plan.entries = p.chains.proof.second.given.plan.entries)
  | .error _ => false

/-- The setting in what is sized is what the parameter file's lines, as p.X holds them, fix. -/
def settingZ (p : Model.Verify.Planned) : Bool :=
  decide (p.chains.made.sized.proof.set = Params.settingOf p.X.P.frame)

/-- Each of the three made plans has that setting as its own. -/
def madeSets (p : Model.Verify.Planned) : Bool :=
  p.chains.made.proof.all fun P => decide (P.set = p.chains.made.sized.proof.set)

/-- **The test that what is sized, and what the planner makes of it, is what is read back.** -/
def read (p : Model.Verify.Planned) : Bool :=
  readShape p && readCodes p && readSamples p && readPlans p && remadeF p && remadeS p &&
    remadeW p && settingZ p && madeSets p

end VerifiableInference.OnPublicFiles.OkD
