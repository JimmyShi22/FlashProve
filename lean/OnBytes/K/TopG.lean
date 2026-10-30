-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/TopG.lean: `PortYesAt` (OnBytes/K/Top.lean) with the hash function a letter.

One definition. `PortYesAt F id table further` is what OnBytes/K/Top.lean hands on from the exit
code 0 of the Lean program about the bytes. Its routines hash with the program's own hash functions.
`PortYesAtG h hr F id table further` is the same text, clause for clause, with the twins of
OnBytes/ChecksWithHashAsArgument/M, run in the monad `Id`, in the place of every routine that hashes: h stands for
the format's hash, hr for the earlier mode's hash of a request file.
  with h:  the planner (its configuration digest), the shared record of a call, the check of the key
           file, of the entry file and of the proof file, the commitment ID, the digest in
           `Tie.SameChains`, the stage request;
  with hr: the request's item, the stage request.
The clauses in which no routine hashes stand as they are: the eight equations on what was read, the
limits on the files' sizes, `stFromCall`, `coveredOf`, `linksOf`, `runLinksH`, `idAsked`,
`StagesPassed`, and that the shared record holds the planner's own data.
What it is for: sentences "the program's yes gives the typed arm's yes" that are to hold at every
hash function (Johnson/Top/OnFilesPort.lean [not in this library]) start from this one record.
What is not claimed. No theorem stands here. That a yes of the whole call's twin
(`OnBytes.TwoPort.M.Model.Verify.wholeCall`) gives it is `twinGivesRecord`
(OnBytes/K/Oracle/SpineTwinAll.lean [not in this library]): at the format's hash over every g, at hr
:= `secondHashFunctionTree`, on files within the program's limits, at the entry's number that the proof file names.
The limits are premises there: eight clauses are bounds on the files' sizes, which the whole call
does not test (Johnson/Top/PortWritten.lean [not in this library] tests them behind the call). That
`PortYesAt` gives it at one fixed function, the format's hash over the realised oracle, and at hr :=
`secondHashFunctionTree`, is `recordCrosses` (OnBytes/K/Oracle/SpineRecord.lean [not in this library]; the
proposition `RecordCrosses` is defined in OnBytes/K/Oracle/SpineAsked.lean [not in this library]):
one function, one direction. That the clauses named as free of a hash are so is not shown: the
twin's own text of the stage request
(OnBytes/ChecksWithHashAsArgument/M/Model/VerifyStages.lean) calls `stFromCall`, `coveredOf`, `linksOf`, `runLinksH`
and `workHeldH` unturned, and this file follows it; of their bodies this file's writer has read
`workHeldH`'s and the fields of `StagesPassed` and `Tie.SameChains` alone; nobody has walked Lean's
environment from them. A fixed hash still stands inside: the planner's twin calls the program's own
`publicOf`, `chainsOf` and `builtOf` unturned, and `publicOf` hashes with the programs' earlier
mode, as a fixed function, at seven places of its text (three tables' digests; `hPar`; two digests
of calls; the attention's) (by reading the text). All seven read the three public files alone: at
pinned public files they are constants, fixed before a hash function is drawn; this record has no
pins. So the earlier mode is a letter at one use (hr, on a request file) and a fixed function at
seven. That count is not the whole: the request's item keeps further uses of the earlier mode as a
fixed function (the twin of `requestItemOf` hashes the scale file by it and takes the digests of the
parameter file's lines' calls as they stand): only the request file's own digest moves with the
letter. All of these are hashes of public files. The three twins `planned`, `commonOfCall` and
`requestStage`, on which this record stands, are tied to the port at one point: the identity monad,
`formatHashFastForm` and `fun b => secondHashFunctionTree b` (`planned_port`, `commonOfCall_port`, `requestStage_port`,
OnBytes/ChecksWithHashAsArgument/M/AtPort/Spine.lean); what is shown elsewhere stands in that folder's heads. For
proofs only; the program does not import this file.


-/
import OnBytes.K.Top
import OnBytes.ChecksWithHashAsArgument.M.Model.Verify

set_option autoImplicit false

namespace OnBytes.K

open OnBytes.Shell (fileLimit)
open OnBytes.Proof
open OnBytes.TwoPort.M (HashM)

/-- `PortYesAt` with the format's hash h and the earlier mode's hash hr of a request file as
letters. -/
def PortYesAtG (h : HashM Id) (hr : ByteArray → Id (Option ByteArray)) (F : Files) (id : String)
    (table further : Params.TableName) : Prop :=
  ∃ (r : Model.Verify.Read) (p : Model.Verify.Planned) (C : Model.Verify.Common),
    r.pol = F.pol ∧ r.KL = F.KL ∧ r.layout = some F.lay ∧ r.key = F.key ∧ r.request = F.request ∧
    r.y = F.y ∧ r.proof = F.proof ∧ r.entry = F.entry ∧
    F.key.size ≤ fileLimit ∧ F.ent.size ≤ fileLimit ∧
    (TwoPort.M.Model.Verify.planned (m := Id) h F.pol F.KL (some F.lay)).run = Except.ok p ∧
    (TwoPort.M.Model.Verify.commonOfCall (m := Id) h r).run = Except.ok C ∧
    C.chains = p.chains ∧
    TwoPort.M.Key.check (m := Id) h p.chains.key F.key = Except.ok table ∧
    TwoPort.M.Entry.check (m := Id) h (p.chains.bytes .link) table F.ent = Except.ok further ∧
    (∃ so cov item links,
      Model.Head.stFromCall (Model.Verify.words32 F.request) (Model.Verify.words32 F.y) C.X.T =
        .ok so ∧
      Model.Head.coveredOf so C.X.T C.X.P.h.V = .ok cov ∧
      TwoPort.M.Proof.requestItem (m := Id) hr F.pol F.KL F.request = some item ∧
      Model.Verify.linksOf C.X cov = .ok links ∧
      TwoPort.M.Proof.check (m := Id) h p.chains.proof further F.entry item F.request
        (Model.ofNat so.y)
        (Model.Stages.runLinksH (C.built.links.zipWith (fun b l => { b with run := l.run }) links)
          p.chains.proof.first C.X.layers.wsLay) F.proof = Verdict.accepted) ∧
    Model.Verify.idAsked id =
      some (Fmt.hex (TwoPort.M.Key.commitmentId (m := Id) h p.chains.tableShape p.cfg table)) ∧
    Tie.SameChains p (TwoPort.M.Params.configurationDigest (m := Id) h [F.pol, F.lay, F.KL]) ∧
    StagesPassed C 128 ∧
    (∃ o ac w, o.id = some id ∧ o.bits = 128 ∧
      (TwoPort.M.Model.Verify.requestStage (m := Id) h hr C o r F.ent).run =
        Except.ok (.passed, ac, w)) ∧
    (C.X = p.X ∧ C.built = p.built) ∧
    (F.pol.size ≤ Shell.textLimit ∧ F.lay.size ≤ Shell.textLimit ∧ F.KL.size ≤ fileLimit ∧
      F.request.size ≤ fileLimit ∧ F.y.size ≤ fileLimit ∧ F.proof.size ≤ fileLimit)

end OnBytes.K
