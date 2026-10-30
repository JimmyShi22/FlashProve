-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/HonestTrace/ReadyAtFullIn.lean

The clause on the trace in "ReadyInput" (Johnson/Desc/ProofFile/Honest/Thread/ReadyInput.lean: what
the prover's function "trace" returns at the input's index and instance is the input's trace), at a
choice of fields whose trace is that of "fullIn" (Johnson/Desc/ProofFile/Honest/AtPureFullIn.lean:
the full-size trace "theTrace", read by "cellOf"). Theorems alone; no definition. This file states
no goal, and no part of one: each theorem is a few calls of theorems of the library.

The way in: where that trace is there.
* "fullIn_trace_isSome_iff_serves": no scope: at the library's own instance of a request that the
  programs' reader takes, it is there exactly if the index serves the request.
* "fullIn_trace_isSome_iff": at public files in the goals' scope, at a request built of a prompt, an
  output and any padding: exactly if the model has a value on the request's window and the output
  meets the files' policy. It names no "CanServe". "fullIn_trace_isSome_iff_weights": the same at
  weights of the goals' type. "fullIn_trace_eq_none_iff": the other side.
* "fullIn_trace_of_canServe", "fullIn_trace_of_modelOutput", and the two with "_weights": so it is
  there, at the request built without padding, wherever the claim of "VerifierAndGoals.G3'pol"
  (Ladder.lean) holds or prompt and output can be served and the output is the model's own.
  "fullIn_trace_of_result",
  "fullIn_trace_isSome_iff_result_exact": in the words of "requestResult".
* "fullIn_trace_isSome_iff_canServe_meets": both sides in the letters of the claim of
  "VerifierAndGoals.G3'pol", at weights of the goals' type and the request built without padding.
  "fullIn_trace_there_iff_canServe_meets": the same at every prompt and output, built or not, with
  "the trace is there" said outright. "fullIn_trace_isSome_iff_form_result_exact",
  "fullIn_trace_there_iff_result_exact": at exact match alone, with "RequestForm" and
  "requestResult" on the right.
* "readyInput_of_servesAt", "readyInput_of_canServe", "readyInput_of_modelOutput": there
  "ReadyInput" holds of the input with that trace, if the instance passes the description's test
  "okStart".

The way out: what "ReadyInput" gives at such a choice of fields.
* "cells_of_readyInput": no scope: the input's trace is "cellOf X (theTrace X i x)" at the input's
  own index i and at an instance x that the input's bytes are read as and that i serves.
  "cellsForm_of_readyInput": the same with index and instance under one "there are".
* "laws_of_readyInput": in scope, moreover: "MeetsAll", "BorrowedSame" and "NamesFit" of that trace,
  "PartsFit" and "PlanMarks" of the public part. "laws_of_readyInput_open": the same at the letters
  of an opening of the maker ("IM.Open", Johnson/IMR/SeatOpen.lean).
* "public_one_of_open": under such an opening the three spellings of the public part are one: what
  "onlineProverFromPublicFiles" returns is the opening's, and the blank ground's W is its X.

Beside them: "publicInScope_of_pub", "pub_of_atPure": the premises on the public files, out of the
return of the set-up function and of "onlineProverFromPublicFiles". "fullIn_trace_of_servesAt": at a served request the
trace is "theTrace", read by "cellOf". "widerFillAt_fullIn_fields", "widerFillAtC_fullIn_fields":
the two premises on the choice of fields hold at "widerFillAt fullIn o S O" and at "widerFillAtC
fullIn o S O".

Nearest kin. "CellsOwnAt" (Johnson/FrontRoad/CellsOwnAtSpec.lean) is the library's named form of
"the cells that are read of the prover's trace are the model's". It stands at a prover with the
index type FullSizeMatrix and the randomness type (protocolAtFiles Z).EncodingRandomness, at tied requests of a relation, and binds each
index that the matrix holds; by its own head the rows and the choice of fields of
Honest/AtPureWiderAt.lean and Honest/AtPureFullIn.lean stand at another index type and another
randomness type, are no value of its letters G and H, and nothing there carries a prover from those
types to these. "cells_of_readyInput" stands at the index type "Cm.Idx" and at any type of
randomness: it does not go through "CellsOwnAt", and no theorem here ties the two. Both end in one
term: "cellsC X T" (Johnson/HonestTrace/DigitsAtTrace.lean) is the record with the field "cellOf X
T", by its text. "modelTrace_served" and "hinge_modelTrace" (Johnson/FrontRoad/TracePremises.lean)
are the like of "fullIn_trace_of_servesAt" and of the way out at the type "Tr" of traces, not at a
reader of cells.

Limits.
* Not given: that any instance passes "okStart": it stays a premise. Not given: that "ready"
  (Johnson/Desc/ProofFile/Honest/Frame.lean) returns; that "onlineProverFromPublicFiles" returns; that a part plays; that
  a thread stands; what a script lays; that a verifier accepts.
* No input is shown to meet "ReadyInput" at such a choice of fields, in this file or by a theorem
  that it calls: so "cells_of_readyInput", "cellsForm_of_readyInput", "laws_of_readyInput" and
  "laws_of_readyInput_open" may hold emptily, and the three theorems that end in "ReadyInput"
  conclude under a premise that is shown here of no instance.
* "The output is the model's own" stands in this file for "VerifierAndGoals.ModelOutput". That this
  agrees with "IsModelOutput" at the goals' system is the field "package" of "MeaningAt"
  (Johnson/Goal/Meaning/NextToken.lean), which is not called here.
* The theorems of the way in that stand in scope have one premise that the goal has not: that
  the set-up function "ProofFile.pureRoad.pub" returns. At the two named sets of files that return is
  shown in AtFullSide/E2E/StartAtWrittenFiles.lean ("okStart_zFull_whole", "okStart_zGap_whole": the
  field "pub" of "LaidAt"), which the main library cannot import. The three that end in "ReadyInput"
  ask more: that "onlineProverFromPublicFiles" returns at the choice of fields, the two equations on its trace and its
  range, and "okStart".
* All limits of Honest/AtPureFullIn.lean and Honest/Thread/ReadyInput.lean hold here: "fullIn" is
  noncomputable and at the full size alone; "ReadyInput" reads the private input: no theorem of this
  file may be told as a public fact, or as something that a simulator has. Its clause "okStart", at
  the description of the proof file, tests the table's key too: no fact on the key is to be taken
  out of "ReadyInput". And where the instance's key is the one made from rc or from a seed, the
  premise "okStart" of the three theorems that end in "ReadyInput" becomes a condition on that
  randomness: on what terms such a theorem may stand in front of a law over rc or the seed is said
  in the head of Honest/Thread/ReadyInput.lean, in its bullet on distributions.
* The instance is the library's own ("LPFD.Full.instanceAsPlainRecord") at a typed request; "rec", the record of
  the table's key, is free. The description "Fd" in "ReadyInput" is free too: nothing ties it to
  what "onlineProverFromPublicFiles" returns.
* Under a policy that admits more than exact match the trace is there, at a request on whose window
  the model has a value, as soon as the output meets the policy, be the output the model's result or
  not. Whether a request is served depends on the weights, and a client sees it; which condition
  fails is told by no program.
* The executable model of Johnson/HonestTrace/Run/ is not named: nothing here compares it with
  "theTrace".
* That "ReadyInput" has a member: "readyInput_at_zFull" (AtFullSide/K5/ItemAtFull.lean): some input
  is ready at the stored full-size files; that the premises of the way in hold together anywhere is
  not shown here.

Not claimed: completeness, soundness, hiding or any other property of the protocol.
-/
import Johnson.Goal.HonestTrace.ServesAtOfGoal
import Johnson.HonestTrace.CellOfOwner
import Johnson.Goal.HonestTrace.PlanMarksInScope
import Johnson.Desc.ProofFile.Honest.AtPureFullIn
import Johnson.Desc.ProofFile.Honest.AtPureWiderK10
import Johnson.Desc.ProofFile.Honest.AtPureLaw
import Johnson.Desc.ProofFile.Honest.Thread.ReadyInput
import Johnson.Desc.ProofFile.InstOfTies
import Johnson.Desc.Reads.RunIsAtSecondHashFunction
import Johnson.IMR.SeatOpen

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.HonestTrace

open Inst.Model
open VerifiableInference
open VerifiableInference.Desc (FileDescription)
open ProofFile.Honest (Cells OnlineProverParts OnlineProverWithDescription onlineProverFromPublicFiles fullIn ReadyInput Local widerFillAt widerFillAtC IndexCommitterCoins
  OnlineProverArguments)

/-! ## 0. The public files -/

/-- The three premises on the public files as one structure ("PublicInScope",
Johnson/Goal/HonestTrace/TraceHingeInScope.lean). Two of them are hypotheses here as well; the
third, that "publicOf" returns, is drawn from the set-up function's return by "public_older"
(Johnson/Desc/Reads/RunIsAtSecondHashFunction.lean). -/
theorem publicInScope_of_pub {F : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {Z : ProofFile.Pub}
    (hC : VerifierAndGoals.InScope F = true) (hF : VerifierAndGoals.readFiles F = .ok pp)
    (hZ : ProofFile.pureRoad.pub OnBytes.secondHashFunction F.pol F.lay F.KL = .ok Z) :
    PublicInScope F pp (some F.lay) Z.p.X := by
  exact ⟨hC, hF, VerifiableInference.Reads.AtSeat.public_older hZ⟩

/-! ## 1. The way in -/

/-- No scope. At the library's own instance of a request that the programs' reader takes and that
the index serves, the trace of "fullIn" is "theTrace", read by "cellOf". By "fullIn_trace_served"
(Johnson/Desc/ProofFile/Honest/AtPureFullIn.lean) and "instOf_at_frame"
(Johnson/Desc/ProofFile/InstOfTies.lean). -/
theorem fullIn_trace_of_servesAt {Z : ProofFile.Pub} {i : Cm.Idx} {x : Instance ppref}
    (hs : ServesAt Z.p.X i x) (hx : VerifiableInference.OnPublicFiles.Flat.WellFormed x)
    (rec : OnBytes.Flat.RecFull) :
    fullIn.trace Z i (LPFD.Full.instanceAsPlainRecord (⟨x, hx⟩, rec)) =
      some ⟨cellOf Z.p.X (theTrace Z.p.X i x)⟩ := by
  exact ProofFile.Honest.fullIn_trace_served (ProofFile.instOf_at_frame (⟨x, hx⟩, rec)) hs

/-- **No scope.** At the library's own instance of a request that the programs' reader takes: the
trace of "fullIn" is there exactly if the index serves the request. By "fullIn_trace_some",
"instOf_at_frame" and "fullIn_trace_of_servesAt". -/
theorem fullIn_trace_isSome_iff_serves (Z : ProofFile.Pub) (i : Cm.Idx) {x : Instance ppref}
    (hx : VerifiableInference.OnPublicFiles.Flat.WellFormed x) (rec : OnBytes.Flat.RecFull) :
    (fullIn.trace Z i (LPFD.Full.instanceAsPlainRecord (⟨x, hx⟩, rec))).isSome = true ↔ ServesAt Z.p.X i x := by
  constructor
  · intro h
    obtain ⟨C, hC⟩ := Option.isSome_iff_exists.1 h
    obtain ⟨x', hx', hs, -⟩ := ProofFile.Honest.fullIn_trace_some hC
    obtain rfl : x = x' :=
      Option.some.inj ((ProofFile.instOf_at_frame (⟨x, hx⟩, rec)).symm.trans hx')
    exact hs
  · intro hs
    rw [fullIn_trace_of_servesAt hs hx rec]
    rfl

section Scope
variable {F : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {Z : ProofFile.Pub}

/-- **The main form: both sides; no "CanServe".** At public files in the goals' scope, at the public
part that the set-up function returns, at every index and every request built of a prompt, an output
and a padding, at the library's own instance with any record of the key: the trace of "fullIn" is
there exactly if the model has a value on the request's window and the output meets the policy that
the files state. "valid" is met by "VerifierAndGoals.valid_of_read hF", "hx" by "wellFormed_of_built built"
(Johnson/Flat/BuiltOK.lean). By "fullIn_trace_isSome_iff_serves" and "servesAt_iff_value_meets"
(Johnson/Goal/HonestTrace/ServesAtOfGoal.lean). -/
theorem fullIn_trace_isSome_iff (hC : VerifierAndGoals.InScope F = true) (hF : VerifierAndGoals.readFiles F = .ok pp)
    (hZ : ProofFile.pureRoad.pub OnBytes.secondHashFunction F.pol F.lay F.KL = .ok Z)
    (valid : settingsAreValid (VerifierAndGoals.settingsOfRead pp) = true) (i : Cm.Idx)
    {x : Instance ppref} {prompt output padding : List Token}
    (built : requestOfTokens (prompt, output) padding = some x)
    (hx : VerifiableInference.OnPublicFiles.Flat.WellFormed x) (rec : OnBytes.Flat.RecFull) :
    (fullIn.trace Z i (LPFD.Full.instanceAsPlainRecord (⟨x, hx⟩, rec))).isSome = true ↔
      (modelNextToken (VerifierAndGoals.settingsOfRead pp) (weightsOfIndex valid i)
          (VerifiableInference.Meaning.windowOf x)).isSome = true ∧
        Policy.MeetsPolicy (VerifierAndGoals.settingsOfRead pp) pp.pol (weightsOfIndex valid i) prompt
          output := by
  exact (fullIn_trace_isSome_iff_serves Z i hx rec).trans
    (servesAt_iff_value_meets (publicInScope_of_pub hC hF hZ) valid i built)

/-- "fullIn_trace_isSome_iff" at weights of the goals' type, at the index of their own digits: the
right side speaks of these weights themselves. By "weightsOfIndex_indexOfWeights"
(IntegerModel/Arrays/OfIndex.lean). -/
theorem fullIn_trace_isSome_iff_weights (hC : VerifierAndGoals.InScope F = true)
    (hF : VerifierAndGoals.readFiles F = .ok pp)
    (hZ : ProofFile.pureRoad.pub OnBytes.secondHashFunction F.pol F.lay F.KL = .ok Z)
    (valid : settingsAreValid (VerifierAndGoals.settingsOfRead pp) = true)
    (w : ModelWeights (VerifierAndGoals.settingsOfRead pp))
    {x : Instance ppref} {prompt output padding : List Token}
    (built : requestOfTokens (prompt, output) padding = some x)
    (hx : VerifiableInference.OnPublicFiles.Flat.WellFormed x) (rec : OnBytes.Flat.RecFull) :
    (fullIn.trace Z (indexOfWeights valid w) (LPFD.Full.instanceAsPlainRecord (⟨x, hx⟩, rec))).isSome = true ↔
      (modelNextToken (VerifierAndGoals.settingsOfRead pp) w
          (VerifiableInference.Meaning.windowOf x)).isSome = true ∧
        Policy.MeetsPolicy (VerifierAndGoals.settingsOfRead pp) pp.pol w prompt output := by
  have h := fullIn_trace_isSome_iff hC hF hZ valid (indexOfWeights valid w) built hx rec
  rw [weightsOfIndex_indexOfWeights valid w] at h
  exact h

/-- The other side, said outright: the trace is "none" exactly if it is not so that the model has a
value on the window and the output meets the policy. -/
theorem fullIn_trace_eq_none_iff (hC : VerifierAndGoals.InScope F = true) (hF : VerifierAndGoals.readFiles F = .ok pp)
    (hZ : ProofFile.pureRoad.pub OnBytes.secondHashFunction F.pol F.lay F.KL = .ok Z)
    (valid : settingsAreValid (VerifierAndGoals.settingsOfRead pp) = true) (i : Cm.Idx)
    {x : Instance ppref} {prompt output padding : List Token}
    (built : requestOfTokens (prompt, output) padding = some x)
    (hx : VerifiableInference.OnPublicFiles.Flat.WellFormed x) (rec : OnBytes.Flat.RecFull) :
    fullIn.trace Z i (LPFD.Full.instanceAsPlainRecord (⟨x, hx⟩, rec)) = none ↔
      ¬ ((modelNextToken (VerifierAndGoals.settingsOfRead pp) (weightsOfIndex valid i)
            (VerifiableInference.Meaning.windowOf x)).isSome = true ∧
          Policy.MeetsPolicy (VerifierAndGoals.settingsOfRead pp) pp.pol (weightsOfIndex valid i) prompt
            output) := by
  exact Option.not_isSome_iff_eq_none.symm.trans
    (not_congr (fullIn_trace_isSome_iff hC hF hZ valid i built hx rec))

/-- **Where the claim of "VerifierAndGoals.G3'pol" holds**, at the weights that an index holds: the request
built without padding exists, the programs' reader takes it, the index serves it, and at every
record of the key the trace of "fullIn" is "theTrace", read by "cellOf". -/
theorem fullIn_trace_of_canServe (hC : VerifierAndGoals.InScope F = true)
    (hF : VerifierAndGoals.readFiles F = .ok pp)
    (hZ : ProofFile.pureRoad.pub OnBytes.secondHashFunction F.pol F.lay F.KL = .ok Z)
    (valid : settingsAreValid (VerifierAndGoals.settingsOfRead pp) = true) (i : Cm.Idx)
    {prompt output : List Token}
    (can : CanServe (VerifierAndGoals.settingsOfRead pp) (weightsOfIndex valid i) prompt output)
    (meets : Policy.MeetsPolicy (VerifierAndGoals.settingsOfRead pp) pp.pol (weightsOfIndex valid i) prompt
      output) :
    ∃ (x : Instance ppref) (hx : VerifiableInference.OnPublicFiles.Flat.WellFormed x),
      requestOfTokens (prompt, output) [] = some x ∧ ServesAt Z.p.X i x ∧
      ∀ rec : OnBytes.Flat.RecFull, fullIn.trace Z i (LPFD.Full.instanceAsPlainRecord (⟨x, hx⟩, rec)) =
        some ⟨cellOf Z.p.X (theTrace Z.p.X i x)⟩ := by
  obtain ⟨x, built, hx, hs⟩ :=
    servesAt_of_canServe (publicInScope_of_pub hC hF hZ) valid i can meets
  exact ⟨x, hx, built, hs, fun rec => fullIn_trace_of_servesAt hs hx rec⟩

/-- **Where the output is the model's own**, at the weights that an index holds: the same. -/
theorem fullIn_trace_of_modelOutput (hC : VerifierAndGoals.InScope F = true)
    (hF : VerifierAndGoals.readFiles F = .ok pp)
    (hZ : ProofFile.pureRoad.pub OnBytes.secondHashFunction F.pol F.lay F.KL = .ok Z)
    (valid : settingsAreValid (VerifierAndGoals.settingsOfRead pp) = true) (i : Cm.Idx)
    {prompt output : List Token}
    (can : CanServe (VerifierAndGoals.settingsOfRead pp) (weightsOfIndex valid i) prompt output)
    (own : VerifierAndGoals.ModelOutput (VerifierAndGoals.settingsOfRead pp) (weightsOfIndex valid i) prompt output) :
    ∃ (x : Instance ppref) (hx : VerifiableInference.OnPublicFiles.Flat.WellFormed x),
      requestOfTokens (prompt, output) [] = some x ∧ ServesAt Z.p.X i x ∧
      ∀ rec : OnBytes.Flat.RecFull, fullIn.trace Z i (LPFD.Full.instanceAsPlainRecord (⟨x, hx⟩, rec)) =
        some ⟨cellOf Z.p.X (theTrace Z.p.X i x)⟩ := by
  obtain ⟨x, built, hx, hs⟩ :=
    servesAt_of_modelOutput (publicInScope_of_pub hC hF hZ) valid i can own
  exact ⟨x, hx, built, hs, fun rec => fullIn_trace_of_servesAt hs hx rec⟩

/-- "fullIn_trace_of_canServe" at weights of the goals' type, at the index of their own digits: the
letters of the claim under "CompleteFor" in "VerifierAndGoals.G3'pol". -/
theorem fullIn_trace_of_canServe_weights (hC : VerifierAndGoals.InScope F = true)
    (hF : VerifierAndGoals.readFiles F = .ok pp)
    (hZ : ProofFile.pureRoad.pub OnBytes.secondHashFunction F.pol F.lay F.KL = .ok Z)
    (valid : settingsAreValid (VerifierAndGoals.settingsOfRead pp) = true)
    (w : ModelWeights (VerifierAndGoals.settingsOfRead pp)) {prompt output : List Token}
    (can : CanServe (VerifierAndGoals.settingsOfRead pp) w prompt output)
    (meets : Policy.MeetsPolicy (VerifierAndGoals.settingsOfRead pp) pp.pol w prompt output) :
    ∃ (x : Instance ppref) (hx : VerifiableInference.OnPublicFiles.Flat.WellFormed x),
      requestOfTokens (prompt, output) [] = some x ∧
      ServesAt Z.p.X (indexOfWeights valid w) x ∧
      ∀ rec : OnBytes.Flat.RecFull,
        fullIn.trace Z (indexOfWeights valid w) (LPFD.Full.instanceAsPlainRecord (⟨x, hx⟩, rec)) =
          some ⟨cellOf Z.p.X (theTrace Z.p.X (indexOfWeights valid w) x)⟩ := by
  obtain ⟨x, built, hx, hs⟩ :=
    servesAt_of_canServe_weights (publicInScope_of_pub hC hF hZ) valid w can meets
  exact ⟨x, hx, built, hs, fun rec => fullIn_trace_of_servesAt hs hx rec⟩

/-- "fullIn_trace_of_modelOutput" at weights of the goals' type. That "VerifierAndGoals.ModelOutput"
agrees with "IsModelOutput" at the goals' system is the field
"package" of "MeaningAt" (Johnson/Goal/Meaning/NextToken.lean), which is not called here. -/
theorem fullIn_trace_of_modelOutput_weights (hC : VerifierAndGoals.InScope F = true)
    (hF : VerifierAndGoals.readFiles F = .ok pp)
    (hZ : ProofFile.pureRoad.pub OnBytes.secondHashFunction F.pol F.lay F.KL = .ok Z)
    (valid : settingsAreValid (VerifierAndGoals.settingsOfRead pp) = true)
    (w : ModelWeights (VerifierAndGoals.settingsOfRead pp)) {prompt output : List Token}
    (can : CanServe (VerifierAndGoals.settingsOfRead pp) w prompt output)
    (own : VerifierAndGoals.ModelOutput (VerifierAndGoals.settingsOfRead pp) w prompt output) :
    ∃ (x : Instance ppref) (hx : VerifiableInference.OnPublicFiles.Flat.WellFormed x),
      requestOfTokens (prompt, output) [] = some x ∧
      ServesAt Z.p.X (indexOfWeights valid w) x ∧
      ∀ rec : OnBytes.Flat.RecFull,
        fullIn.trace Z (indexOfWeights valid w) (LPFD.Full.instanceAsPlainRecord (⟨x, hx⟩, rec)) =
          some ⟨cellOf Z.p.X (theTrace Z.p.X (indexOfWeights valid w) x)⟩ := by
  obtain ⟨x, built, hx, hs⟩ :=
    servesAt_of_modelOutput_weights (publicInScope_of_pub hC hF hZ) valid w can own
  exact ⟨x, hx, built, hs, fun rec => fullIn_trace_of_servesAt hs hx rec⟩

/-- In the words of "requestResult": where prompt and output make a request whose result is these
output tokens, the trace is there. -/
theorem fullIn_trace_of_result (hC : VerifierAndGoals.InScope F = true) (hF : VerifierAndGoals.readFiles F = .ok pp)
    (hZ : ProofFile.pureRoad.pub OnBytes.secondHashFunction F.pol F.lay F.KL = .ok Z)
    (valid : settingsAreValid (VerifierAndGoals.settingsOfRead pp) = true)
    (w : ModelWeights (VerifierAndGoals.settingsOfRead pp)) {prompt output : List Token}
    (form : RequestForm (VerifierAndGoals.settingsOfRead pp) prompt output)
    (result : requestResult (VerifierAndGoals.settingsOfRead pp) w prompt output = some output) :
    ∃ (x : Instance ppref) (hx : VerifiableInference.OnPublicFiles.Flat.WellFormed x),
      requestOfTokens (prompt, output) [] = some x ∧
      ∀ rec : OnBytes.Flat.RecFull,
        fullIn.trace Z (indexOfWeights valid w) (LPFD.Full.instanceAsPlainRecord (⟨x, hx⟩, rec)) =
          some ⟨cellOf Z.p.X (theTrace Z.p.X (indexOfWeights valid w) x)⟩ := by
  obtain ⟨x, built, hx, hs⟩ :=
    servesAt_of_result (publicInScope_of_pub hC hF hZ) valid w form result
  exact ⟨x, hx, built, fun rec => fullIn_trace_of_servesAt hs hx rec⟩

/-- **At the policy of exact match alone**, both sides in the words of "requestResult": at a request
built without padding the trace is there exactly if the model's result on the request is these
output tokens. -/
theorem fullIn_trace_isSome_iff_result_exact (hC : VerifierAndGoals.InScope F = true)
    (hF : VerifierAndGoals.readFiles F = .ok pp)
    (hZ : ProofFile.pureRoad.pub OnBytes.secondHashFunction F.pol F.lay F.KL = .ok Z)
    (valid : settingsAreValid (VerifierAndGoals.settingsOfRead pp) = true) (exactMatch : pp.pol = AcceptancePolicy.exact)
    (i : Cm.Idx) {x : Instance ppref} {prompt output : List Token}
    (built : requestOfTokens (prompt, output) [] = some x)
    (hx : VerifiableInference.OnPublicFiles.Flat.WellFormed x) (rec : OnBytes.Flat.RecFull) :
    (fullIn.trace Z i (LPFD.Full.instanceAsPlainRecord (⟨x, hx⟩, rec))).isSome = true ↔
      requestResult (VerifierAndGoals.settingsOfRead pp) (weightsOfIndex valid i) prompt output
        = some output := by
  exact (fullIn_trace_isSome_iff_serves Z i hx rec).trans
    (servesAt_iff_result_exact (publicInScope_of_pub hC hF hZ) valid exactMatch i built)

/-- **Both sides, in the letters of the claim of "VerifierAndGoals.G3'pol"**: at weights of the goals' type,
at the request built without padding: the trace of "fullIn" is there exactly if prompt and output
can be served and the output meets the files' policy. By "fullIn_trace_isSome_iff_serves" and
"servesAt_iff_canServe_meets" (Johnson/Goal/HonestTrace/ServesAtOfGoal.lean). -/
theorem fullIn_trace_isSome_iff_canServe_meets (hC : VerifierAndGoals.InScope F = true)
    (hF : VerifierAndGoals.readFiles F = .ok pp)
    (hZ : ProofFile.pureRoad.pub OnBytes.secondHashFunction F.pol F.lay F.KL = .ok Z)
    (valid : settingsAreValid (VerifierAndGoals.settingsOfRead pp) = true)
    (w : ModelWeights (VerifierAndGoals.settingsOfRead pp)) {x : Instance ppref} {prompt output : List Token}
    (built : requestOfTokens (prompt, output) [] = some x)
    (hx : VerifiableInference.OnPublicFiles.Flat.WellFormed x) (rec : OnBytes.Flat.RecFull) :
    (fullIn.trace Z (indexOfWeights valid w) (LPFD.Full.instanceAsPlainRecord (⟨x, hx⟩, rec))).isSome = true ↔
      CanServe (VerifierAndGoals.settingsOfRead pp) w prompt output ∧
        Policy.MeetsPolicy (VerifierAndGoals.settingsOfRead pp) pp.pol w prompt output := by
  have h := (fullIn_trace_isSome_iff_serves Z (indexOfWeights valid w) hx rec).trans
    (servesAt_iff_canServe_meets (publicInScope_of_pub hC hF hZ) valid (indexOfWeights valid w)
      built)
  rw [weightsOfIndex_indexOfWeights valid w] at h
  exact h

/-- **At the policy of exact match alone**: the same with the right side in the words of
"requestResult": prompt and output make a request, and its result is these output tokens. At a built
request the first clause holds anyway; it stands here so that the right side is that of
"VerifierAndGoals.canServe_and_meetsPolicy_exact_iff" (Ladder/RequestResultTies.lean), clause for clause. -/
theorem fullIn_trace_isSome_iff_form_result_exact (hC : VerifierAndGoals.InScope F = true)
    (hF : VerifierAndGoals.readFiles F = .ok pp)
    (hZ : ProofFile.pureRoad.pub OnBytes.secondHashFunction F.pol F.lay F.KL = .ok Z)
    (valid : settingsAreValid (VerifierAndGoals.settingsOfRead pp) = true)
    (exactMatch : pp.pol = AcceptancePolicy.exact) (w : ModelWeights (VerifierAndGoals.settingsOfRead pp))
    {x : Instance ppref} {prompt output : List Token}
    (built : requestOfTokens (prompt, output) [] = some x)
    (hx : VerifiableInference.OnPublicFiles.Flat.WellFormed x) (rec : OnBytes.Flat.RecFull) :
    (fullIn.trace Z (indexOfWeights valid w) (LPFD.Full.instanceAsPlainRecord (⟨x, hx⟩, rec))).isSome = true ↔
      RequestForm (VerifierAndGoals.settingsOfRead pp) prompt output ∧
        requestResult (VerifierAndGoals.settingsOfRead pp) w prompt output = some output := by
  refine (fullIn_trace_isSome_iff_canServe_meets hC hF hZ valid w built hx rec).trans ?_
  rw [exactMatch]
  exact VerifierAndGoals.canServe_and_meetsPolicy_exact_iff valid w prompt output

/-- **At every prompt and output, built or not.** "The trace is there" is said outright: the request
built without padding exists, the programs' reader takes it, and at its instance, with the given
record of the key, the trace of "fullIn" is there. That holds exactly if prompt and output can be
served and the output meets the files' policy. Where no request is built both sides fail. No built
request is a premise: the left side is a sentence on the weights, the prompt and the output (and the
record of the key), as a completeness statement for every request wants it. -/
theorem fullIn_trace_there_iff_canServe_meets (hC : VerifierAndGoals.InScope F = true)
    (hF : VerifierAndGoals.readFiles F = .ok pp)
    (hZ : ProofFile.pureRoad.pub OnBytes.secondHashFunction F.pol F.lay F.KL = .ok Z)
    (valid : settingsAreValid (VerifierAndGoals.settingsOfRead pp) = true)
    (w : ModelWeights (VerifierAndGoals.settingsOfRead pp)) (prompt output : List Token)
    (rec : OnBytes.Flat.RecFull) :
    (∃ (x : Instance ppref) (hx : VerifiableInference.OnPublicFiles.Flat.WellFormed x),
        requestOfTokens (prompt, output) [] = some x ∧
        (fullIn.trace Z (indexOfWeights valid w)
          (LPFD.Full.instanceAsPlainRecord (⟨x, hx⟩, rec))).isSome = true) ↔
      CanServe (VerifierAndGoals.settingsOfRead pp) w prompt output ∧
        Policy.MeetsPolicy (VerifierAndGoals.settingsOfRead pp) pp.pol w prompt output := by
  constructor
  · rintro ⟨x, hx, built, there⟩
    exact (fullIn_trace_isSome_iff_canServe_meets hC hF hZ valid w built hx rec).1 there
  · rintro ⟨can, meets⟩
    obtain ⟨x, hx, built, -, tr⟩ := fullIn_trace_of_canServe_weights hC hF hZ valid w can meets
    exact ⟨x, hx, built, by rw [tr rec]; rfl⟩

/-- **At the policy of exact match alone**, at every prompt and output, built or not: the trace is
there, in the sense of "fullIn_trace_there_iff_canServe_meets", exactly if prompt and output make a
request whose result is these output tokens. -/
theorem fullIn_trace_there_iff_result_exact (hC : VerifierAndGoals.InScope F = true)
    (hF : VerifierAndGoals.readFiles F = .ok pp)
    (hZ : ProofFile.pureRoad.pub OnBytes.secondHashFunction F.pol F.lay F.KL = .ok Z)
    (valid : settingsAreValid (VerifierAndGoals.settingsOfRead pp) = true)
    (exactMatch : pp.pol = AcceptancePolicy.exact) (w : ModelWeights (VerifierAndGoals.settingsOfRead pp))
    (prompt output : List Token) (rec : OnBytes.Flat.RecFull) :
    (∃ (x : Instance ppref) (hx : VerifiableInference.OnPublicFiles.Flat.WellFormed x),
        requestOfTokens (prompt, output) [] = some x ∧
        (fullIn.trace Z (indexOfWeights valid w)
          (LPFD.Full.instanceAsPlainRecord (⟨x, hx⟩, rec))).isSome = true) ↔
      RequestForm (VerifierAndGoals.settingsOfRead pp) prompt output ∧
        requestResult (VerifierAndGoals.settingsOfRead pp) w prompt output = some output := by
  refine (fullIn_trace_there_iff_canServe_meets hC hF hZ valid w prompt output rec).trans ?_
  rw [exactMatch]
  exact VerifierAndGoals.canServe_and_meetsPolicy_exact_iff valid w prompt output

end Scope

/-! ## 2. "ReadyInput" itself

General in the choice of fields P: all that is asked of it is that its trace and its range are those
of "fullIn". -/

/-- At "widerFillAt fullIn o S O" (Johnson/Desc/ProofFile/Honest/AtPureWiderAt.lean) the two
premises on the choice of fields hold by unfolding. The first half is "fullIn_fill_trace". -/
theorem widerFillAt_fullIn_fields (o : ProofFile.SecondHashFunctionArgument) (S : Sz) (O : OnlineProverArguments) :
    (widerFillAt fullIn o S O).trace = fullIn.trace ∧
      (widerFillAt fullIn o S O).inRange = fullIn.inRange := by
  exact ⟨rfl, rfl⟩

/-- And at "widerFillAtC fullIn o S O" (Johnson/Desc/ProofFile/Honest/AtPureWiderK10.lean), which
turns the field "lots" alone. -/
theorem widerFillAtC_fullIn_fields (o : ProofFile.SecondHashFunctionArgument) (S : Sz) (O : OnlineProverArguments) :
    (widerFillAtC fullIn o S O).trace = fullIn.trace ∧
      (widerFillAtC fullIn o S O).inRange = fullIn.inRange := by
  exact ⟨rfl, rfl⟩

section Ready
variable {Rc X₀ Xo : Type} {P : OnlineProverParts Cm.Idx Rc Cells X₀ Xo} {A : OnlineProverWithDescription Cm.Idx Rc Cells X₀ Xo}
  {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray}

/-- **"ReadyInput" at a served request**, no scope. Beside the return of "onlineProverFromPublicFiles" and the two
equations on the choice of fields, "okStart" is the premise that is left. The range: the sixth
clause of "atPure_ok" (Johnson/Desc/ProofFile/Honest/AtPureLaw.lean); "fullIn.inRange" is true
everywhere. The trace: "atPure_trace" and "fullIn_trace_of_servesAt". The description "Fd" is free:
nothing ties it to A. The limits of Honest/Thread/ReadyInput.lean go with this theorem. One of them
bears on the premise hok: if the key in the instance is the key made from rc or from a seed, hok is
a condition on that randomness, and whoever sets this theorem in front of a law over rc or the seed
meets the terms of that head's bullet on distributions. As stated here, rec and rc are two free
letters and no distribution is named. -/
theorem readyInput_of_servesAt (hT : P.trace = fullIn.trace) (hR : P.inRange = fullIn.inRange)
    (hA : onlineProverFromPublicFiles o pol lay KL P = .ok A) (Fd : FileDescription ProofFile.Inst) {i : Cm.Idx}
    {x : Instance ppref} (hs : ServesAt A.Z.p.X i x)
    (hx : VerifiableInference.OnPublicFiles.Flat.WellFormed x) (rec : OnBytes.Flat.RecFull) (rc : Rc)
    (hok : Fd.okStart (LPFD.Full.instanceAsPlainRecord (⟨x, hx⟩, rec)) = true) :
    ReadyInput Fd A.H
      ⟨i, rc, LPFD.Full.instanceAsPlainRecord (⟨x, hx⟩, rec), ⟨cellOf A.Z.p.X (theTrace A.Z.p.X i x)⟩⟩ := by
  unfold ReadyInput
  refine ⟨hok, ?_, ?_⟩
  · show A.H.inRange i = true
    rw [(ProofFile.Honest.atPure_ok hA).2.2.2.2.2.1, hR]
    rfl
  · show A.H.trace i (LPFD.Full.instanceAsPlainRecord (⟨x, hx⟩, rec)) =
      some ⟨cellOf A.Z.p.X (theTrace A.Z.p.X i x)⟩
    rw [ProofFile.Honest.atPure_trace hA, hT]
    exact fullIn_trace_of_servesAt hs hx rec

/-- **The way out, no scope.** What "ReadyInput" says of the input's trace at such a choice of
fields: it is "theTrace" at the input's own index and at an instance that the input's bytes are read
as and that the index serves, read by "cellOf"; the record on the right is "cellsC A.Z.p.X (theTrace
…)" (Johnson/HonestTrace/DigitsAtTrace.lean) by that definition's text. It spends the third clause
of "ReadyInput" alone. It may hold emptily: no input is shown to meet "ReadyInput" at such a choice
of fields. The limits of Honest/Thread/ReadyInput.lean go with it: what it yields is a fact on the
private input, for the real world alone, and it yields nothing on the table's key. By "atPure_trace"
and "fullIn_trace_some". -/
theorem cells_of_readyInput (hT : P.trace = fullIn.trace) (hA : onlineProverFromPublicFiles o pol lay KL P = .ok A)
    {Fd : FileDescription ProofFile.Inst} {v : Local Cm.Idx Rc ProofFile.Inst Cells} (hv : ReadyInput Fd A.H v) :
    ∃ x : Instance ppref, ProofFile.instOf v.x = some x ∧ ServesAt A.Z.p.X v.w₀ x ∧
      v.trace = ⟨cellOf A.Z.p.X (theTrace A.Z.p.X v.w₀ x)⟩ := by
  have h : fullIn.trace A.Z v.w₀ v.x = some v.trace := by
    rw [← hT, ← ProofFile.Honest.atPure_trace hA]
    exact hv.2.2
  exact ProofFile.Honest.fullIn_trace_some h

/-- "cells_of_readyInput" in a weaker form, for a caller that has it as a binder: at every input
that meets "ReadyInput" there are an index and an instance at which the field "cell" of the input's
trace is "cellOf" of "theTrace", and the index serves the instance. It no longer says that the index
is the input's own, nor that the input's bytes are read as the instance. It may hold emptily, as
that theorem. -/
theorem cellsForm_of_readyInput (hT : P.trace = fullIn.trace)
    (hA : onlineProverFromPublicFiles o pol lay KL P = .ok A) (Fd : FileDescription ProofFile.Inst) :
    ∀ v : Local Cm.Idx Rc ProofFile.Inst Cells, ReadyInput Fd A.H v →
      ∃ (i : Cm.Idx) (x : Instance ppref),
        v.trace.cell = cellOf A.Z.p.X (theTrace A.Z.p.X i x) ∧ ServesAt A.Z.p.X i x := by
  intro v hv
  obtain ⟨x, -, hs, e⟩ := cells_of_readyInput hT hA hv
  exact ⟨v.w₀, x, by rw [e], hs⟩

end Ready

section ReadyScope
variable {Rc X₀ Xo : Type} {P : OnlineProverParts Cm.Idx Rc Cells X₀ Xo} {A : OnlineProverWithDescription Cm.Idx Rc Cells X₀ Xo}
  {F : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy}

/-- The set-up function's return, out of the return of "onlineProverFromPublicFiles": the first clause of "atPure_ok";
"ProofFile.pureRoad.pub" is "ProofFile.pubPlain" by its text (Johnson/Desc/ProofFile/OnlineDescriptionPublicPart.lean). -/
theorem pub_of_atPure {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray}
    (hA : onlineProverFromPublicFiles o pol lay KL P = .ok A) : ProofFile.pureRoad.pub o pol lay KL = .ok A.Z := by
  exact (ProofFile.Honest.atPure_ok hA).1

/-- **"ReadyInput" where the claim of "VerifierAndGoals.G3'pol" holds**, at weights of the goals' type: at the
request built without padding, at every record of the key and every value rc of the type Rc, if the
instance passes "okStart". Rc is a letter for any type; at "widerFillAt" and "widerFillAtC" it is
"IndexCommitterCoins". -/
theorem readyInput_of_canServe (hC : VerifierAndGoals.InScope F = true) (hF : VerifierAndGoals.readFiles F = .ok pp)
    (hT : P.trace = fullIn.trace) (hR : P.inRange = fullIn.inRange)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction F.pol F.lay F.KL P = .ok A) (Fd : FileDescription ProofFile.Inst)
    (valid : settingsAreValid (VerifierAndGoals.settingsOfRead pp) = true)
    (w : ModelWeights (VerifierAndGoals.settingsOfRead pp)) {prompt output : List Token}
    (can : CanServe (VerifierAndGoals.settingsOfRead pp) w prompt output)
    (meets : Policy.MeetsPolicy (VerifierAndGoals.settingsOfRead pp) pp.pol w prompt output) :
    ∃ (x : Instance ppref) (hx : VerifiableInference.OnPublicFiles.Flat.WellFormed x),
      requestOfTokens (prompt, output) [] = some x ∧
      ∀ (rec : OnBytes.Flat.RecFull) (rc : Rc),
        Fd.okStart (LPFD.Full.instanceAsPlainRecord (⟨x, hx⟩, rec)) = true →
        ReadyInput Fd A.H ⟨indexOfWeights valid w, rc, LPFD.Full.instanceAsPlainRecord (⟨x, hx⟩, rec),
          ⟨cellOf A.Z.p.X (theTrace A.Z.p.X (indexOfWeights valid w) x)⟩⟩ := by
  obtain ⟨x, built, hx, hs⟩ :=
    servesAt_of_canServe_weights (publicInScope_of_pub hC hF (pub_of_atPure hA)) valid w can meets
  exact ⟨x, hx, built, fun rec rc hok => readyInput_of_servesAt hT hR hA Fd hs hx rec rc hok⟩

/-- The same where the output is the model's own. -/
theorem readyInput_of_modelOutput (hC : VerifierAndGoals.InScope F = true)
    (hF : VerifierAndGoals.readFiles F = .ok pp)
    (hT : P.trace = fullIn.trace) (hR : P.inRange = fullIn.inRange)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction F.pol F.lay F.KL P = .ok A) (Fd : FileDescription ProofFile.Inst)
    (valid : settingsAreValid (VerifierAndGoals.settingsOfRead pp) = true)
    (w : ModelWeights (VerifierAndGoals.settingsOfRead pp)) {prompt output : List Token}
    (can : CanServe (VerifierAndGoals.settingsOfRead pp) w prompt output)
    (own : VerifierAndGoals.ModelOutput (VerifierAndGoals.settingsOfRead pp) w prompt output) :
    ∃ (x : Instance ppref) (hx : VerifiableInference.OnPublicFiles.Flat.WellFormed x),
      requestOfTokens (prompt, output) [] = some x ∧
      ∀ (rec : OnBytes.Flat.RecFull) (rc : Rc),
        Fd.okStart (LPFD.Full.instanceAsPlainRecord (⟨x, hx⟩, rec)) = true →
        ReadyInput Fd A.H ⟨indexOfWeights valid w, rc, LPFD.Full.instanceAsPlainRecord (⟨x, hx⟩, rec),
          ⟨cellOf A.Z.p.X (theTrace A.Z.p.X (indexOfWeights valid w) x)⟩⟩ := by
  obtain ⟨x, built, hx, hs⟩ :=
    servesAt_of_modelOutput_weights (publicInScope_of_pub hC hF (pub_of_atPure hA)) valid w can own
  exact ⟨x, hx, built, fun rec rc hok => readyInput_of_servesAt hT hR hA Fd hs hx rec rc hok⟩

/-- **The way out, in scope.** "cells_of_readyInput", and of that trace the library's laws:
"MeetsAll" (among its fields: every entry is below 129 in absolute value), "BorrowedSame" (each
borrowed matrix has its owner's entries), "NamesFit" (the numbers of parts are the full size's, and
the trace is 0 where a sub-proof's list has no label); and of the public part "PartsFit", which is
also the first field of "NamesFit", and "PlanMarks" (the plans' lists bear the marks of the names).
By "meetsAll_theTrace" (Johnson/Goal/HonestTrace/FullPlanesInScope.lean), "borrowedSame_of_meetsAll"
(Johnson/HonestTrace/CellOfOwner.lean), "namesFit_theTrace" and "partsFit_in_scope"
(Johnson/Goal/HonestTrace/FromCellsInScope.lean), "planMarks_in_scope"
(Johnson/Goal/HonestTrace/PlanMarksInScope.lean). It may hold emptily, as "cells_of_readyInput". -/
theorem laws_of_readyInput (hC : VerifierAndGoals.InScope F = true) (hF : VerifierAndGoals.readFiles F = .ok pp)
    (hT : P.trace = fullIn.trace) (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction F.pol F.lay F.KL P = .ok A)
    {Fd : FileDescription ProofFile.Inst} {v : Local Cm.Idx Rc ProofFile.Inst Cells} (hv : ReadyInput Fd A.H v) :
    ∃ x : Instance ppref, ProofFile.instOf v.x = some x ∧ ServesAt A.Z.p.X v.w₀ x ∧
      v.trace = ⟨cellOf A.Z.p.X (theTrace A.Z.p.X v.w₀ x)⟩ ∧
      MeetsAll A.Z.p.X v.w₀ x (theTrace A.Z.p.X v.w₀ x) ∧
      BorrowedSame A.Z.p.X (theTrace A.Z.p.X v.w₀ x) ∧
      NamesFit A.Z.p.X (theTrace A.Z.p.X v.w₀ x) ∧ PartsFit A.Z.p.X ∧ PlanMarks A.Z.p.X := by
  obtain ⟨x, hx, hs, hc⟩ := cells_of_readyInput hT hA hv
  have B := publicInScope_of_pub hC hF (pub_of_atPure hA)
  have M := meetsAll_theTrace B.scope B.reads B.pub hs
  exact ⟨x, hx, hs, hc, M, borrowedSame_of_meetsAll M,
    namesFit_theTrace B.scope B.reads B.pub hs, partsFit_in_scope B.scope B.reads B.pub,
    planMarks_in_scope B.scope B.reads B.pub⟩

/-- **The three spellings of the public part are one.** Under an opening of the maker at the same
three files: the public part that "onlineProverFromPublicFiles" returns is the opening's, and the W of the opening's
blank ground is its X. By the field "pub" of "IM.Open" and "IM.Open.W" (Johnson/IMR/SeatOpen.lean).
-/
theorem public_one_of_open {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray}
    (hA : onlineProverFromPublicFiles o pol lay KL P = .ok A) {Fo : FileDescription ProofFile.Inst} {Zp : ProofFile.Pub}
    {Bs : ProofFile.PureBase}
    {base : List (VerifiableInference.Desc.Block VerifiableInference.Desc.First.S ProofFile.Cl)}
    {c : VerifiableInference.Desc.Chain VerifiableInference.Desc.First.S ProofFile.Cl}
    {As : ProofFile.SharedSeat} {Bsec : ProofFile.SecondSeat}
    (O : IM.Open o pol lay KL Fo Zp Bs base c As Bsec) :
    A.Z = Zp ∧ Bs.G₀.W = Zp.p.X := by
  exact ⟨Except.ok.inj ((ProofFile.Honest.atPure_ok hA).1.symm.trans O.pub), O.W⟩

/-- **The way out at the letters of an opening**: "laws_of_readyInput" at X := Zp.p.X, with the
equation by which it is also at Bs.G₀.W. The opening's description Fo and the description Fd in
"ReadyInput" are two letters, tied by nothing. An opening can be had wherever "onlineProverFromPublicFiles" returns:
among the clauses of "atPure_ok" is the return of "onlineDescription", which "seat_open"
(Johnson/IMR/SeatOpen.lean) opens; neither step is taken here. -/
theorem laws_of_readyInput_open (hC : VerifierAndGoals.InScope F = true) (hF : VerifierAndGoals.readFiles F = .ok pp)
    (hT : P.trace = fullIn.trace) (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction F.pol F.lay F.KL P = .ok A)
    {Fo : FileDescription ProofFile.Inst} {Zp : ProofFile.Pub} {Bs : ProofFile.PureBase}
    {base : List (VerifiableInference.Desc.Block VerifiableInference.Desc.First.S ProofFile.Cl)}
    {c : VerifiableInference.Desc.Chain VerifiableInference.Desc.First.S ProofFile.Cl}
    {As : ProofFile.SharedSeat} {Bsec : ProofFile.SecondSeat}
    (O : IM.Open OnBytes.secondHashFunction F.pol F.lay F.KL Fo Zp Bs base c As Bsec)
    {Fd : FileDescription ProofFile.Inst} {v : Local Cm.Idx Rc ProofFile.Inst Cells} (hv : ReadyInput Fd A.H v) :
    ∃ x : Instance ppref, ProofFile.instOf v.x = some x ∧ ServesAt Zp.p.X v.w₀ x ∧
      v.trace = ⟨cellOf Zp.p.X (theTrace Zp.p.X v.w₀ x)⟩ ∧
      MeetsAll Zp.p.X v.w₀ x (theTrace Zp.p.X v.w₀ x) ∧
      BorrowedSame Zp.p.X (theTrace Zp.p.X v.w₀ x) ∧
      NamesFit Zp.p.X (theTrace Zp.p.X v.w₀ x) ∧ PartsFit Zp.p.X ∧ PlanMarks Zp.p.X ∧
      Bs.G₀.W = Zp.p.X := by
  obtain ⟨rfl, hW⟩ := public_one_of_open hA O
  obtain ⟨x, hx, hs, hc, M, Bo, N, Pf, Pm⟩ := laws_of_readyInput hC hF hT hA hv
  exact ⟨x, hx, hs, hc, M, Bo, N, Pf, Pm, hW⟩

end ReadyScope

end OnBytes.HonestTrace

#print axioms OnBytes.HonestTrace.publicInScope_of_pub
#print axioms OnBytes.HonestTrace.fullIn_trace_of_servesAt
#print axioms OnBytes.HonestTrace.fullIn_trace_isSome_iff_serves
#print axioms OnBytes.HonestTrace.fullIn_trace_isSome_iff
#print axioms OnBytes.HonestTrace.fullIn_trace_isSome_iff_weights
#print axioms OnBytes.HonestTrace.fullIn_trace_eq_none_iff
#print axioms OnBytes.HonestTrace.fullIn_trace_of_canServe
#print axioms OnBytes.HonestTrace.fullIn_trace_of_modelOutput
#print axioms OnBytes.HonestTrace.fullIn_trace_of_canServe_weights
#print axioms OnBytes.HonestTrace.fullIn_trace_of_modelOutput_weights
#print axioms OnBytes.HonestTrace.fullIn_trace_of_result
#print axioms OnBytes.HonestTrace.fullIn_trace_isSome_iff_result_exact
#print axioms OnBytes.HonestTrace.fullIn_trace_isSome_iff_canServe_meets
#print axioms OnBytes.HonestTrace.fullIn_trace_isSome_iff_form_result_exact
#print axioms OnBytes.HonestTrace.fullIn_trace_there_iff_canServe_meets
#print axioms OnBytes.HonestTrace.fullIn_trace_there_iff_result_exact
#print axioms OnBytes.HonestTrace.widerFillAt_fullIn_fields
#print axioms OnBytes.HonestTrace.widerFillAtC_fullIn_fields
#print axioms OnBytes.HonestTrace.readyInput_of_servesAt
#print axioms OnBytes.HonestTrace.cells_of_readyInput
#print axioms OnBytes.HonestTrace.cellsForm_of_readyInput
#print axioms OnBytes.HonestTrace.pub_of_atPure
#print axioms OnBytes.HonestTrace.readyInput_of_canServe
#print axioms OnBytes.HonestTrace.readyInput_of_modelOutput
#print axioms OnBytes.HonestTrace.laws_of_readyInput
#print axioms OnBytes.HonestTrace.public_one_of_open
#print axioms OnBytes.HonestTrace.laws_of_readyInput_open
