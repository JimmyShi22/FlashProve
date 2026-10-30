-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/ChecksWithHashAsArgument/M/Model/Verify.lean: CUT OUT BY A PROGRAM FROM A TEXT WRITTEN BY HAND: the program
chooses the declarations that differ from the port's and turns names; it does not make the turn over
m. The definitions of OnBytes/Model/Verify.lean that hash, or hand a hash on, written once more
over a monad m in which the hash is asked. The port's own file is untouched. What does not hash is
the port's own. The text written by hand is this project's authors' own rewriting of the port's
file. THE TWINS OF MODEL/ (Verify.lean, VerifyChains.lean, VerifyStages.lean: sixteen definitions).
ONE TIE TO THE PORT: at the identity monad, `formatHashFastForm` and, for the request file's digest,
`fun b => secondHashFunctionTree b`, each of the sixteen has the value of the port's of the same name at all
arguments (`namedT`: of `named`; `partCall`: with the stage's run a letter on each side, the two
related): the theorems whose names end in `_port`, and `relX_namedT`, of
OnBytes/ChecksWithHashAsArgument/M/AtPort/Spine.lean. For the twins at another hash see
OnBytes/ChecksWithHashAsArgument/M/AtPort/SpineAt.lean [not in this library], SpinePass.lean [not in this library]
and Calls.lean, whose heads name their premises; over another monad, or with another function for
the request file's digest, see the statements of OnBytes/ChecksWithHashAsArgument/M/Model/SpineHom.lean and
SpineKeeps.lean. The list is not whole, and nothing of it is summed up here. That the text is the
port's with a letter for the hash is held by eye. That `hh` reaches every call of the format's hash
is no theorem. The second hash function's other calls are fixed in the text: no argument stands for
them.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Model.Verify
import OnBytes.ChecksWithHashAsArgument.M.Chain.EngineM
import OnBytes.ChecksWithHashAsArgument.M.Chain.Reader
import OnBytes.ChecksWithHashAsArgument.M.Chain.Session
import OnBytes.ChecksWithHashAsArgument.M.Chain.Why
import OnBytes.ChecksWithHashAsArgument.M.Entry.File
import OnBytes.ChecksWithHashAsArgument.M.Entry.Table
import OnBytes.ChecksWithHashAsArgument.M.Key.File
import OnBytes.ChecksWithHashAsArgument.M.Key.Table
import OnBytes.ChecksWithHashAsArgument.M.Model.VerifyChains
import OnBytes.ChecksWithHashAsArgument.M.Model.VerifyStages
import OnBytes.ChecksWithHashAsArgument.M.Params.Configure
import OnBytes.ChecksWithHashAsArgument.M.Proof.File
import OnBytes.ChecksWithHashAsArgument.M.Proof.Place
import OnBytes.ChecksWithHashAsArgument.M.Proof.Reading
import OnBytes.ChecksWithHashAsArgument.M.Proof.RequestItem
import OnBytes.ChecksWithHashAsArgument.M.Proof.Tail

namespace OnBytes.TwoPort.M.Model.Verify

open OnBytes.Model OnBytes.Model.Verify

open OnBytes.Model.Stages

/-- Computes all that follows from the three configuration files. Without a layout file `chainsOf`
refuses, and the digest is not used. -/
def planned {m : Type → Type} [Monad m] (hh : HashM m) (pol KL : ByteArray)
    (layout : Option ByteArray) :
    ExceptT String m Planned := do
  let X ← publicOf pol KL layout
  let cfg ← configuration (m := m) hh pol (layout.getD .empty) KL
  let chains ← chainsOf X layout cfg
  pure { X := X, cfg := cfg, chains := chains, built := ← builtOf X chains }

/-- What every stage has computed when it turns to its own file. -/
def Planned.common {m : Type → Type} [Monad m] (hh : HashM m) (p : Planned) (r : Read) :
    ExceptT Refused m Common :=
  commonOf hh p.X p.cfg p.chains p.built r.key r.id.asked

/-- What every stage has computed when it turns to its own file, from the files of a call. -/
def commonOfCall {m : Type → Type} [Monad m] (hh : HashM m) (r : Read) :
    ExceptT Refused m Common := do
  let p ← namedT (planned hh r.pol r.KL r.layout)
  Planned.common hh p r

/-- The three stages' results, and the policy's lines under which the stage request judges. From
these lines and the request the call says what its answer is about. Where the stages end in their
common beginning there are no such lines: the call ends with the stages' refusal, and the lines are
not looked at. -/
def stagesOf {m : Type → Type} [Monad m] (hh : HashM m) (hr : ByteArray → m (Option ByteArray))
    (o : Options) (r : Read) (entry : ByteArray) :
    m (List StageOut × PolicyLines) := do
  match ← (commonOfCall hh r).run with
  | .error x => pure (allRefuse x, default)
  | .ok C =>
    let k ← (keyStage hh C o.bits r.key).run
    let l ← (leafStage hh C o.bits entry).run
    let q ← (requestStage hh hr C o r entry).run
    pure ([C.oneTimeOut .key k, C.oneTimeOut .leaf l, stageOut .request C.idHex q],
      C.policyLines)

/-- The result of a whole call. It makes the tests of `entryNumber` first, then runs the three
stages key, leaf and request on the same bytes and forms the result of the call from theirs. A call
that passes, with a yes or as within limits, is about the positions r to e - 1 of the request alone:
it says nothing of any other token and, if e < T, nothing of the reply. -/
def wholeCall {m : Type → Type} [Monad m] (hh : HashM m) (hr : ByteArray → m (Option ByteArray))
    (o : Options) (f : Files) : m CallEnd :=
  match readCall o f with
  | .error e => pure e
  | .ok r =>
    match f.entry with
    | none => pure (.no "cp-entry-missing")
    | some entry => do
      let (stages, lines) ← stagesOf hh hr o r entry
      pure (cpStagesRun stages none (askedBelowBar o.bits) o.bits r.id
        (some (words32 r.request, lines)))

/-- A call on one file alone. part: the stage key or the stage leaf. run: that stage. The options
-next-token and -policy belong to a whole call: with one of them the command line is bad. Such calls
are for the committer's own test and never say yes. -/
def partCall {m : Type → Type} [Monad m] (hh : HashM m) (o : Options) (f : Files) (part : StageName)
    (run : Common → Read → ExceptT Refused m Found) : m CallEnd :=
  if o.nextToken || o.policy.isSome then pure (.usage "") else
  match readFirst o f false with
  | .error e => pure e
  | .ok r => do
    let out : StageOut ←
      match ← (commonOfCall hh r).run with
      | .error x => pure { name := part, ending := .no x.name, why := x.why }
      | .ok C => do
        let x ← (run C r).run
        pure (C.oneTimeOut part x)
    pure (cpStagesRun [out] (some part) (askedBelowBar o.bits) o.bits r.id none)

/-- The call on a key file alone: cp_verify -key <config folder> <key file>. Of the files it reads
the configuration files and the key. -/
def keyCall {m : Type → Type} [Monad m] (hh : HashM m) (o : Options) (f : Files) : m CallEnd :=
  partCall hh o f .key fun C r => keyStage hh C o.bits r.key

/-- The call on an entry file alone: cp_verify -leaf <config folder> <key file> <entry file>. Of the
key's table only the form is tested here, so a pass counts only beside a call -key that passed on
the same key file, configuration folder and bits. Here the caller names the entry file, so an
entry that cannot be read ends the call without a verdict. In a whole call the proof names the
entry, and a missing one is refused. -/
def leafCall {m : Type → Type} [Monad m] (hh : HashM m) (o : Options) (f : Files) : m CallEnd :=
  match readFirst o f false, f.entry with
  | .ok _, none =>
    pure (if o.nextToken || o.policy.isSome then .usage "" else .unreadable .entry)
  | _, entry => partCall hh o f .leaf fun C _ => leafStage hh C o.bits (entry.getD .empty)

/-- The parameter bytes of the seven chains as they follow from the three configuration files, each
paired with its chain's name, in the order of `allChains`. No key, entry, request or proof is looked
at. bits: the requested bits. The C++ verifier has no call that returns these bytes. The tests are
those that its planning calls -plan accounting and -plan request make on the three files
(cpPlanMain), in their order. A file that cannot be read ends this call without a verdict. The
other tests end it with a no and a name: all that a stage tests up to the plans, and that the bits
do not exceed the parameter file's target. These planning calls do not make a whole call's early
tests on the bits and on the parameter file's first line: there the stage's own scan refuses, with
its own names. The calls -plan arrays and -plan id take another course and are not followed here. -/
def planBytes {m : Type → Type} [Monad m] (hh : HashM m) (bits : Nat) (policy KL : FileIn)
    (layout : Option FileIn) : ExceptT CallEnd m (List (String × ByteArray)) := do
  let (pol, KL, layout) ← cpConfRead policy KL layout
  let p ← (ExceptT.mk do
    let r ← (planned hh pol KL layout).run
    pure (callNamed r) : ExceptT CallEnd m Planned)
  callNeeds (decide (bits ≤ p.X.P.frame.sec)) "security-bits"
  pure (allChains.map fun c => (c.text, p.chains.bytes c))

end OnBytes.TwoPort.M.Model.Verify
