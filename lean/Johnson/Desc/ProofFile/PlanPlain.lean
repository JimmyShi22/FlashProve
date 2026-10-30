-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/PlanPlain.lean: the planner's records, computed without the program
`verify-on-bytes`'s routines for the segments and without naming a hash function in its own text.

Why. `verify-on-bytes`'s record of a segment (`LinkH`, OnBytes/Model/StagesLinks.lean) has a field
`run`, which holds the whole routine that checks the segment's sub-proof. One function fills it,
`Verify.linksOf`, and each of the six functions copied here calls that one, directly or not. Nothing
in the planner runs the field. But a description whose public part comes from that planner would
reach these routines as a term.
What is here. Copies of six functions of the library: `shapesOf`, `chainsOf`, `builtOf`, `planned`
(namespace `ProofFile.Plain`), `sendsOf`, `madeOf` (namespace `ProofFile.PlainG`). Each body is the library's,
except that
  * `linksPlain X` stands for `linksOf X default`: the same records, with a routine in `run` that
    refuses at once;
  * each calls the copy in this file where the library's function calls the library's;
  * `planned` differs in two more lines, which its own comment explains, and takes an argument `o`,
    which `sendsOf` and `madeOf` pass down.
The types (`Planned`, `LinksH`, `LinkH`, `Made`) are the library's.
Limits. These are copies: if the library's text changes, they have to be made again. A parameter
for the segments' records in the library's six functions would make them unnecessary. The type
`LinkH` still mentions `verify-on-bytes`'s monads as types. Whether `publicOfO`, `Params.sized`,
`Params.configure`, `shapesWith` or `buildLinksH` reach a routine or a hash function of
`verify-on-bytes` in some other way has not been traced. Law/PlainIsPlanned.lean and
Law/PlainIsMade.lean prove equations between the copies and the library's functions (up to the field
run, and for the planner at the constant configuration fixedConfigurationDigest, not at the files' own digest); their
heads say how far these go.

-/
import Johnson.G.RoundsOfPlan
import OnBytes.Model.Verify
import Johnson.Desc.Ok.PlanWritten.PublicAt
import Johnson.Desc.TheCfg

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Plain
open OnBytes OnBytes.Model OnBytes.Model.Verify
open OnBytes.Model.Stages

/-- A routine that refuses at once. It fills the field `run`, which nothing here calls. -/
def notToBeRun : LinkM (Option WsForkOut) :=
  (refuse "a link's placeholder routine was run; nothing should call it" : Blk (Option WsForkOut))

/-- The segments' records, from the public fields of the three kinds of plan. -/
def linksPlain (X : Public) : Except String (Array LinkH) :=
  listLinksH X.NGr X.p4
    (X.G.map fun hp =>
      { tl := hp.tl, Fp := hp.Fp, Tp := hp.Tp, ns := hp.ns, NCL := hp.NCL, run := notToBeRun })
    (X.A.map fun A =>
      { tl := A.seam.tl, Fp := A.seam.Fp, Tp := A.seam.Tp, ns := A.ns, run := notToBeRun })
    { tl := X.H.tl, Fp := X.H.Fp, Tp := X.H.Tp, ns := X.H.ns, NCL := X.H.NCL, run := notToBeRun }

/-- `shapesOf` (OnBytes/Model/VerifyChains.lean), with `linksPlain`. -/
def shapesOf (X : Public) (layoutFile : Option ByteArray) :
    Except String (Array LinkH × Params.Shapes) := do
  let links ← ProofFile.Plain.linksPlain X
  headLast links
  linksCount links
  let (links, declared) ← declareLinks links X.NGr X.p4
  let file ←
    match layoutFile.bind Plan.layoutRead with
    | some f => pure f
    | none => throw "plan-layout"
  let (reqLinks, layout) ←
    match Plan.reqFrame declared file X.P.frame.answers with
    | some x => pure x
    | none => throw "plan-layout"
  pure (links, ← shapesWith X reqLinks layout (links.toList.map (·.gid)))

/-- `chainsOf` (OnBytes/Model/VerifyChains.lean), over this file's `shapesOf`. -/
def chainsOf (X : Public) (layoutFile : Option ByteArray) (cfg : ByteArray) :
    Except String Chains := do
  let (links, shapes) ← ProofFile.Plain.shapesOf X layoutFile
  let z ← Params.sized X.P.frame shapes
  linksFit links z.proof.codes z.proof.request shapes.layout z.proof.batch.shape.kCol
  let made ← Params.configure X.P.frame shapes cfg 0
  match Params.KeyChains.read made.keyOneTime made.keyShared made.keySecond,
      Params.Link.read made.entryLink,
      Params.ProofChains.read made.first made.shared made.second with
  | some key, some link, some proof =>
    pure { made := made, key := key, link := link, proof := proof }
  | _, _, _ => throw "internal-parameter-bytes-not-read"

/-- `builtOf` (OnBytes/Model/VerifyStages.lean), with `linksPlain`. -/
def builtOf (X : Public) (chains : Chains) : Except String LinksH := do
  buildLinksH (← ProofFile.Plain.linksPlain X) X.NGr X.p4 X.layers.wsLay chains.proof.first

/-- `planned` (OnBytes/Model/Verify.lean), over this file's `chainsOf` and `builtOf`, with two
changes, so that this text names no hash function. (1) The public record is `publicOfO o`
(Johnson/Desc/Ok/PlanWritten/PublicAt.lean): the text of `publicOf` with the second hash function
as the argument `o`. (2) The constant `fixedConfigurationDigest` (Johnson/Desc/TheCfg.lean), which the descriptions of
all three files use, stands for the digest of the public files. `Params.configure` writes that
digest into the field `cfg` and into the seven chains' parameter bytes, and nowhere else. So the
parameter bytes in this record are not the ones that a transcript starts from, and nobody may start
one from them. The description is not meant to read them; no theorem says that it does not. The
digest's length matters: without 32 bytes the library's reader of parameter bytes refuses. -/
def planned (o : Nat → ByteArray → ByteArray) (pol KL : ByteArray) (layout : Option ByteArray) :
    Except String Planned := do
  let X ← VerifiableInference.PlanWritten.publicOfO o pol KL layout
  let cfg := VerifiableInference.Desc.fixedConfigurationDigest
  let chains ← ProofFile.Plain.chainsOf X layout cfg
  pure { X := X, cfg := cfg, chains := chains, built := ← ProofFile.Plain.builtOf X chains }

end ProofFile.Plain

namespace ProofFile.PlainG
open Johnson.G Johnson.G.OfPlan
open OnBytes OnBytes.Params

/-- `sendsOf` (Johnson/G/Sends.lean), over this file's `planned`. -/
def sendsOf (o : Nat → ByteArray → ByteArray) (pol lay KL : ByteArray) :
    Except String (List ChainSends) := do
  let p ← ProofFile.Plain.planned o pol KL (some lay)
  let c := p.chains.made
  let z := c.sized
  let a := z.set.samples
  let one (file : String) (ch : Nat) (codes : Codes) (l : List Listed) (P : Planned) :
      Except String ChainSends := do
    let R := P.rounds.toArray
    let seeds := P.rounds.zipIdx.filter fun r => r.1.entry.name == "SEND seed"
    unless seeds.length == l.length do
      throw s!"{file} {ch}: {l.length} sendings listed, {seeds.length} entries SEND seed"
    let out ← (seeds.zip l).mapM fun (r, s) => do
      unless treesOf codes s.sent.toArray == some r.1.entry.roots do
        throw s!"{file} {ch}, entry {r.2 + 1} ({s.label}): the trees are not the entry's roots"
      match R[r.2 + 1]? with
      | some b => pure (⟨r.2 + 1, s.label, s.sent, r.1.entry, b.entry⟩ : Sending)
      | none => throw s!"{file} {ch}, entry {r.2 + 1}: no entry behind it"
    pure ⟨file, ch, codes, out⟩
  let K := z.key.once.shape
  let B := z.proof.batch.shape
  let x := z.key.ranges.x
  match c.key, c.proof with
  | [k0, k1, k2], [p0, p1, p2] =>
    [ one "key" 0 z.key.codes
        ([⟨"the index-mask message", [z.key.once.input]⟩,
          ⟨"the multiplicities", (Wf.messageOf x).toList⟩] ++
          ioppSends "the ranges' test" a x.choice.masksRide 1 x.stages ++ [← wSend K]) k0,
      one "key" 1 z.key.codes (← linSharedSends K a) k1,
      one "key" 2 z.key.codes (ioppSends "the own test" a K.choice.masksRide 1 K.testOwn) k2,
      one "entry" 0 z.entryCodes
        (⟨"the link's message", (linkMessage z.link.shape a).toList⟩ ::
          ioppSends "the link's test" a z.link.shape.choice.masksRide 1 z.link.shape.test) c.entry,
      one "proof" 0 z.proof.codes
        (frameSends z.proof a 0 (reqGroups z.proof.request).toList z.proof.request.link ++
          [← wSend B]) p0,
      one "proof" 1 z.proof.codes (← linSharedSends B a) p1,
      one "proof" 2 z.proof.codes (ioppSends "the own test" a B.choice.masksRide 1 B.testOwn) p2
    ].mapM id
  | _, _ => throw "the key or the proof has not three plans"

/-- `madeOf` (Johnson/G/RoundsOfPlan.lean), over this file's `planned` and `sendsOf`. -/
def madeOf (o : Nat → ByteArray → ByteArray) (pol lay KL : ByteArray) : Except String Made := do
  let p ← ProofFile.Plain.planned o pol KL (some lay)
  match ← ProofFile.PlainG.sendsOf o pol lay KL with
  | [k0, k1, k2, _, p0, p1, p2] => pure ⟨p, (k0, k1, k2), (p0, p1, p2)⟩
  | _ => throw "the list of sendings has not seven chains (key 0 1 2, entry, proof 0 1 2)"

end ProofFile.PlainG
