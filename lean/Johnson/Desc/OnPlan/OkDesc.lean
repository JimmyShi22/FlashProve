-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/OnPlan/OkDesc.lean: tests on a planner's answer p that read p alone and name no size:
what the steps of the description of the proof file's shared chain are written for, and the
program's own tests on that chain's parameters. Definitions with code alone; no theorem.

IT STANDS OVER NO FILE THAT IMPORTS Mathlib: it is meant to be asked by running code.

Main names (namespace VerifiableInference.OnPublicFiles.OkD):
  codesS p, linS p: the shared chain's codes and the shape of the test on the table, as the chain's
    parameter bytes are read back (p.chains.proof.shared).
  sentU p, sentO p: the notices of the chain's two sendings: the folded row with what goes out
    beside it (proofWu, Johnson/Desc/OnPlan/OkParamsDefs.lean), and Omega with the split's message
    (linMessageOmega, OnBytes/Iop/Lin.lean).
  ahead, split: in the test on the table the masks go ahead; the shared tree needs a split.
  lengths, shape: lengthsFit; linFits, which holds foldFits: the description's own texts
    (Johnson/Desc/Own/Lin.lean; equal to the program's Codes.lengthsOk and linOk: LinAgree.lean).
  groupU, groupO: the codes of the two groups are there, and the mask code is not longer than the
    main code: groupOk of the description's ground (namespace VerifiableInference.Desc.Ground).
  sendU, sendO: at each sending: every notice's shape fits the codes; the trees can be laid: the
    two clauses of that ground's sentL, which its step for a prover's message asks too.
  stagesU, stagesO, stagesW: the stages of the three proximity tests fit together: ioppOk
    (OnBytes/Iop/Prox.lean) at the test on the folded row's group, at the test on Omega's group
    where it has one, both with the shared chain's number of answers, and at the test on a
    request's own group, with the second chain's.
  firstU, firstO, firstW: the first stage of each has the code and the mask code with which its
    group is laid: two of the four equations that ioppVerify asks behind its first round.
  sizedS: the sizes from which the planner writes the shared chain's rounds follow (linSizeOf,
    OnBytes/Params/DeriveLin.lean). heldS: the three plans that the planner has made for the proof
    file's chains hold (Planned.holds, OnBytes/Params/Planner.lean): the planner's routines ask both
    before they return a plan. heldS READS THE ERROR STORED BESIDE EACH ENTRY, ITS BITS OF WORK AND
    THE TARGET, NOT THE ENTRY's NUMBERS: that the numbers are the planner's own is asked by remadeF,
    remadeS, remadeW (Johnson/Desc/OnPlan/OkRead.lean).
  desc p: **the test**: Ok.params p (nine clauses, Johnson/Desc/OnPlan/OkParamsDefs.lean) and the
    sixteen.

That file's proofTail p has p.chains.proof's shared and second chain as its fields, so its shape of
the test on the table is linS p by unfolding; no law is typed for it.

Not here: Tie.shortB: a premise of laws on the plan at another digest, which cannot say no at a
value that a machine holds: no test of this directory asks Tie.shortB.

Not here: ioppVerify's other two equations (the first stage's numbers of row variables are the
group's layout's): they read the group's members.

Not here, though the program asks them at the same places: the tests on the table's key (its sizes;
no seed with the factor 0; its words below the prime): a key is no value of the plan. That the
digest of the public files is not 32 zero bytes.

What is not claimed. THAT ANY OF THEM SAYS YES AT ANY p: nothing is evaluated here. That these are
all the tests on parameters that the program makes on that chain. Nothing on soundness, on an
honest prover or on hiding.

-/
import OnBytes.Iop.Lin
import OnBytes.Params.DeriveLin
import Johnson.Desc.OnPlan.OkParamsDefs
import Johnson.Desc.First.Base.Ground
import Johnson.Desc.Own.Lin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles.OkD
open OnBytes

/-- The codes of the proof file's shared chain, as its parameter bytes are read back. -/
abbrev codesS (p : Model.Verify.Planned) : Codes := p.chains.proof.shared.codes

/-- The shape of the test on the table, as the shared chain's parameter bytes are read back. -/
abbrev linS (p : Model.Verify.Planned) : Params.LinShape := p.chains.proof.shared.lin

/-- The notices of the sending of the folded row. -/
def sentU (p : Model.Verify.Planned) : Array OracleNotice :=
  #[(⟨(linS p).fold.u, (linS p).fold.leafClass⟩ : OracleNotice)] ++ proofWu p

/-- The notices of the sending of Omega. -/
def sentO (p : Model.Verify.Planned) : Array OracleNotice := linMessageOmega (linS p)

/-- In the test on the table the masks go ahead. -/
def ahead (p : Model.Verify.Planned) : Bool := (linS p).masksAhead

/-- In the test on the table the shared tree needs a split. -/
def split (p : Model.Verify.Planned) : Bool := (linS p).sharedSplitNeeded

/-- Every message length of the codes is a power of two. -/
def lengths (p : Model.Verify.Planned) : Bool := Desc.Own.lengthsFit (codesS p)

/-- The shape of the test on the table fits the codes. -/
def shape (p : Model.Verify.Planned) : Bool := Desc.Own.linFits (codesS p) (linS p)

/-- The codes of the folded row's group are in order. -/
def groupU (p : Model.Verify.Planned) : Bool :=
  Desc.Ground.groupOk (codesS p) (linS p).fold.u.code (linS p).sharedMaskCode

/-- The codes of Omega's group are in order, where it has a group of its own. -/
def groupO (p : Model.Verify.Planned) : Bool :=
  !(linS p).sharedSplitNeeded ||
    Desc.Ground.groupOk (codesS p) (linS p).omega.code (linS p).sharedMaskCode

/-- At the sending of the folded row: every notice's shape fits the codes; the trees can be laid. -/
def sendU (p : Model.Verify.Planned) : Bool :=
  Desc.Ground.ok (Desc.Ground.sentL (codesS p) (sentU p))

/-- The same at the sending of Omega. -/
def sendO (p : Model.Verify.Planned) : Bool :=
  Desc.Ground.ok (Desc.Ground.sentL (codesS p) (sentO p))

/-- The stages of the test on the folded row's group fit together. -/
def stagesU (p : Model.Verify.Planned) : Bool :=
  ioppOk (codesS p) (linS p).testU p.chains.proof.shared.given.plan.samples

/-- So do those of the test on Omega's group, where it has a group of its own. -/
def stagesO (p : Model.Verify.Planned) : Bool :=
  !(linS p).sharedSplitNeeded ||
    ioppOk (codesS p) (linS p).testOmega p.chains.proof.shared.given.plan.samples

/-- So do those of the test on a request's own group. -/
def stagesW (p : Model.Verify.Planned) : Bool :=
  ioppOk (codesS p) (linS p).testOwn p.chains.proof.second.given.plan.samples

/-- There is a first stage, and it has this code and this mask code. -/
def firstIs (stages : List Params.IoppStage) (code maskCode : Nat) : Bool :=
  match stages with
  | [] => false
  | f :: _ => f.code == code && f.maskCode == maskCode

/-- The first stage of the test on the folded row's group has the group's two codes. -/
def firstU (p : Model.Verify.Planned) : Bool :=
  firstIs (linS p).testU (linS p).fold.u.code (linS p).sharedMaskCode

/-- So has that of the test on Omega's group, where it has a group of its own. -/
def firstO (p : Model.Verify.Planned) : Bool :=
  !(linS p).sharedSplitNeeded ||
    firstIs (linS p).testOmega (linS p).omega.code
      (linS p).sharedMaskCode

/-- So has that of the test on a request's own group. -/
def firstW (p : Model.Verify.Planned) : Bool :=
  firstIs (linS p).testOwn (linS p).w.code (linS p).ownMaskCode

/-- The sizes from which the planner writes the shared chain's rounds follow. -/
def sizedS (p : Model.Verify.Planned) : Bool :=
  (Params.linSizeOf p.chains.made.sized.proof.codes p.chains.made.sized.proof.batch).isSome

/-- Each of the three plans that the planner has made for the proof file's chains holds. -/
def heldS (p : Model.Verify.Planned) : Bool := p.chains.made.proof.all (·.holds)

/-- **The test on the plan alone.** -/
def desc (p : Model.Verify.Planned) : Bool :=
  Ok.params p && ahead p && split p && lengths p && shape p && groupU p && groupO p &&
    sendU p && sendO p && stagesU p && stagesO p && stagesW p && firstU p && firstO p &&
    firstW p && sizedS p && heldS p

end VerifiableInference.OnPublicFiles.OkD
