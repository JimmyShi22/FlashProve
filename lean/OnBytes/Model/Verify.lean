-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/Verify.lean: the result of a call, as one pure function of the bytes of all inputs.

This file renders the checking calls of cpMain (verifier/src/cp_verify.cpp): the whole call, -key
and -leaf. Not rendered: the calls -plan (`planBytes` makes the tests of two of them and no more),
the parsing of the command line except three of its tests (`idAsked`, `kindNamed`, `partCall`), and
the guards of main on the machine (core dumps, no memory, no thread). It reads no file and prints
nothing: a shell reads the files, calls `wholeCall` and prints the result (OnBytes/Shell/Whole.lean,
OnBytes/Shell/Lines.lean). The inputs are described in OnBytes/Model/VerifyInputs.lean.

The parts of the computation, all in OnBytes/Model/: VerifyHeads.lean (the tests before the stages);
VerifyPublic.lean and VerifyCross.lean (what follows from the configuration files);
VerifyLinks.lean, VerifySubproofs.lean and VerifyHiding.lean (what the planner takes from the
sub-proofs); VerifyChains.lean (the chains' parameter bytes and plans); VerifyAccount.lean (the
rounds' errors against the target); VerifyStatement.lean (the statement that the first chain binds);
VerifyStages.lean (the three stages).

How a shell uses this file. It reads every file but the entry and calls `entryNumber`. That gives
the number k of the entry, or the result of a call that ends before the entry is read. It then
reads leaf/<k>.bin and calls `wholeCall`.

The parameter bytes of all seven chains are made from the configuration files
(OnBytes/Model/VerifyChains.lean), and the errors of their rounds are computed and compared with the
target.

Main definitions: `entryNumber`, `Planned`, `planned`, `commonOfCall`, `stagesOf`, `wholeCall`,
`partCall`, `keyCall`, `leafCall`, `planBytes`.
What is not claimed: no theorem is stated here.
-/
import OnBytes.Model.VerifyStages

namespace OnBytes.Model.Verify

open OnBytes.Model.Stages

/-- The tests that come before the entry is read, in the order of cp_verify: those of `readCall`
(OnBytes/Model/VerifyHeads.lean). Returns the number of the entry that the proof names, or the
result of the call. -/
def entryNumber (o : Options) (f : Files) : Except CallEnd Nat :=
  (readCall o f).map (·.entry)

/-- All that follows from the three configuration files. -/
structure Planned where
  /-- the parameter file as read, and the sub-proofs' layouts and plans -/
  X : Public
  /-- the digest of the three files -/
  cfg : ByteArray
  /-- the seven chains -/
  chains : Chains
  /-- the links of a request's chain as `buildLinksH` returns them: each with the names of the
  arrays that it reads -/
  built : LinksH

/-- Computes all that follows from the three configuration files. Without a layout file `chainsOf`
refuses, and the digest is not used. -/
def planned (pol KL : ByteArray) (layout : Option ByteArray) : Except String Planned := do
  let X ← publicOf pol KL layout
  let cfg := configuration pol (layout.getD .empty) KL
  let chains ← chainsOf X layout cfg
  pure { X := X, cfg := cfg, chains := chains, built := ← builtOf X chains }

/-- What every stage has computed when it turns to its own file. -/
def Planned.common (p : Planned) (r : Read) : Except Refused Common :=
  commonOf p.X p.cfg p.chains p.built r.key r.id.asked

/-- The three stages' results when the common beginning refuses: all three refuse with the same
name. -/
def allRefuse (x : Refused) : List StageOut :=
  ([.key, .leaf, .request] : List StageName).map fun s =>
    { name := s, ending := .no x.name, why := x.why }

/-- What every stage has computed when it turns to its own file, from the files of a call. -/
def commonOfCall (r : Read) : Except Refused Common :=
  (named (planned r.pol r.KL r.layout)).bind (·.common r)

/-- The three stages' results, and the policy's lines under which the stage request judges. From
these lines and the request the call says what its answer is about. Where the stages end in their
common beginning there are no such lines: the call ends with the stages' refusal, and the lines are
not looked at. -/
def stagesOf (o : Options) (r : Read) (entry : ByteArray) : List StageOut × PolicyLines :=
  match commonOfCall r with
  | .error x => (allRefuse x, default)
  | .ok C =>
    ([C.oneTimeOut .key (keyStage C o.bits r.key),
      C.oneTimeOut .leaf (leafStage C o.bits entry),
      stageOut .request C.idHex (requestStage C o r entry)],
     C.policyLines)

/-- The result of a whole call. It makes the tests of `entryNumber` first, then runs the three
stages key, leaf and request on the same bytes and forms the result of the call from theirs. A call
that passes, with a yes or as within limits, is about the positions r to e - 1 of the request alone:
it says nothing of any other token and, if e < T, nothing of the reply. -/
def wholeCall (o : Options) (f : Files) : CallEnd :=
  match readCall o f with
  | .error e => e
  | .ok r =>
    match f.entry with
    | none => .no "cp-entry-missing"
    | some entry =>
      let (stages, lines) := stagesOf o r entry
      cpStagesRun stages none (askedBelowBar o.bits) o.bits r.id
        (some (words32 r.request, lines))

/-- A call on one file alone. part: the stage key or the stage leaf. run: that stage. The options
-next-token and -policy belong to a whole call: with one of them the command line is bad. Such calls
are for the committer's own test and never say yes. -/
def partCall (o : Options) (f : Files) (part : StageName)
    (run : Common → Read → Except Refused Found) : CallEnd :=
  if o.nextToken || o.policy.isSome then .usage "" else
  match readFirst o f false with
  | .error e => e
  | .ok r =>
    let out : StageOut :=
      match commonOfCall r with
      | .error x => { name := part, ending := .no x.name, why := x.why }
      | .ok C => C.oneTimeOut part (run C r)
    cpStagesRun [out] (some part) (askedBelowBar o.bits) o.bits r.id none

/-- The call on a key file alone: cp_verify -key <config folder> <key file>. Of the files it reads
the configuration files and the key. -/
def keyCall (o : Options) (f : Files) : CallEnd :=
  partCall o f .key fun C r => keyStage C o.bits r.key

/-- The call on an entry file alone: cp_verify -leaf <config folder> <key file> <entry file>. Of the
key's table only the form is tested here, so a pass counts only beside a call -key that passed on
the same key file, configuration folder and bits. Here the caller names the entry file, so an
entry that cannot be read ends the call without a verdict. In a whole call the proof names the
entry, and a missing one is refused. -/
def leafCall (o : Options) (f : Files) : CallEnd :=
  match readFirst o f false, f.entry with
  | .ok _, none =>
    if o.nextToken || o.policy.isSome then .usage "" else .unreadable .entry
  | _, entry => partCall o f .leaf fun C _ => leafStage C o.bits (entry.getD .empty)

/-- The seven chains, in the order of the files key, entry, proof. -/
def allChains : List ChainName :=
  [.keyOneTime, .keyShared, .keySecond, .link, .proofFirst, .proofShared, .proofSecond]

/-- The parameter bytes of the seven chains as they follow from the three configuration files, each
paired with its chain's name, in the order of `allChains`. No key, entry, request or proof is looked
at. bits: the requested bits. The C++ verifier has no call that returns these bytes. The tests are
those that its planning calls -plan accounting and -plan request make on the three files
(cpPlanMain), in their order. A file that cannot be read ends this call without a verdict. The
other tests end it with a no and a name: all that a stage tests up to the plans, and that the bits
do not exceed the parameter file's target. These planning calls do not make a whole call's early
tests on the bits and on the parameter file's first line: there the stage's own scan refuses, with
its own names. The calls -plan arrays and -plan id take another course and are not followed here. -/
def planBytes (bits : Nat) (policy KL : FileIn) (layout : Option FileIn) :
    Except CallEnd (List (String × ByteArray)) := do
  let (pol, KL, layout) ← cpConfRead policy KL layout
  let p ← callNamed (planned pol KL layout)
  callNeeds (decide (bits ≤ p.X.P.frame.sec)) "security-bits"
  pure (allChains.map fun c => (c.text, p.chains.bytes c))

/-- The names with which this file and VerifyHeads, VerifyPublic, VerifyChains, VerifyStatement and
VerifyStages themselves refuse. VerifyCross, VerifyAccount and VerifySubproofs have lists of their
own, and so have the other steps that these files call. -/
def names : List String :=
  namesHeads ++ namesPublic ++ namesChains ++ namesStatement ++ namesStages ++
    ["cp-entry-missing", "security-bits"]

end OnBytes.Model.Verify
