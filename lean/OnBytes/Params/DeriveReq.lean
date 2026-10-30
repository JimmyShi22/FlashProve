-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/DeriveReq.lean: the sizes and the plan of a proof's first chain, and the parameter
bytes of a proof's three chains.

A request is proved by a chain of links, all on the proof's first hash chain. (A proof's or a file's
chain is a hash chain.) Each link has a sub-proof of a part of the model. Its oracle messages go out
at a few moments, that is, in a few prover's messages. The frame is what runs the links: it sends
and samples their oracle messages and closes each link's group into the next (blocks/iop/req.h). It
knows only a few things of a sub-proof: the oracle messages of its link, the number of open rows
that it leaves (linear claims on the messages of the link's group that are still to be proved), and
the rounds that it adds between the frame's own. These are arguments here (`Subproofs`). The file
renders the frame's share: what the links' groups ask of the one distance that is chosen for all of
them (blocks/iop/req.h; the groups themselves are those of OnBytes/Iop/Req.lean), the sizing of the
links' group and of the last proximity test (blocks/frame/derive.h, files.h), and the frame's rounds
(req_plan, file_proof).

Main definitions: `Subproofs`, `reqLoad`, `ProofSized`, `proofSized`, `reqPlan`, `firstPlan`,
`ProofParams`, `proofParams`. The program takes the parameter bytes from `configure`
(OnBytes/Params/Configure.lean); `proofParams` asks none of that routine's tests.
What is not claimed: no theorem is stated here. Not asked in this file: the C++ tests that the
finished shapes fit themselves, the codes and the layout (req_fault, req_layout_fault). The first
(`reqOk`) is asked in OnBytes/Params/Configure.lean, the second (`reqLayoutOk`) in
OnBytes/Model/StagesLinks.lean. Nor does `reqPlan` compare the sizes from which it prices the rounds
with the shape's codes and stages. The C++ ends the process if they differ (req_plan,
iopp_sized_fault). Here `proofSized` makes both from the same values.
-/
import OnBytes.Iop.Req
import OnBytes.Params.DeriveLin

namespace OnBytes.Params

/-- What the frame asks of the sub-proofs of a request's links. -/
structure Subproofs where
  /-- the links with their oracle messages. The numbers of their codes are filled in by the frame
  and are not read -/
  links : List ReqLink
  /-- for each link: how many open rows its sub-proof leaves -/
  openRows : List Nat
  /-- by a link's number and a moment: the rounds of the link's sub-proof that follow the sending of
  that moment's oracle messages -/
  plan : Nat → Nat → Planning Unit
  /-- how many rows on the table a request's sub-proofs leave -/
  pendingRows : Nat
  /-- what a stand-in for sub-proofs still sends after the last test of the links; by default
  nothing -/
  afterLinks : Planning Unit := pure ()
  /-- the rows of the committed matrix -/
  matrixRows : Nat

/-- What the links' groups ask of the one distance that is chosen for all of them: the largest of
each number over the links. It needs only the two message lengths, so it can be asked before the
codes' random entries are known. -/
structure ReqLoad where
  /-- the row variables of a group -/
  k : Nat := 0
  /-- 1 + the kept rows, rounded up to a power of two -/
  slots : Nat := 1
  /-- the variables of a sample's cube -/
  cubeBits : Nat := 0
  /-- a closing batches at most rows + rowsADraw * (draws of positions) rows -/
  rows : Nat := 0
  rowsADraw : Nat := 0
  deriving DecidableEq, Repr, Inhabited

/-- The variables of a sample's cube, from the logarithms of the two message lengths alone. -/
def cubeOfLengths (logL logLz : Nat) (o : OracleShape) : Nat :=
  let main := if o.mainRows != 0 then clog2 o.mainRows + logL else 0
  let mask := if o.maskRows != 0 then clog2 o.maskRows + logLz else 0
  if o.mainRows != 0 && o.maskRows != 0 then max main mask + 1 else main + mask

/-- The kept oracle messages that are sent anew in a group. -/
def keptOf (g : ReqGroup) : List KeptTarget := g.target.kept.toList

/-- The load, group by group. `gs` are the groups from number l on. -/
def reqLoadFrom (answers logL logLz : Nat) :
    Nat → List ReqGroup → List ReqLink → List Nat → ReqLoad → ReqLoad
  | _, [], _, _, load => load
  | l, g :: gs, links, open_, load =>
    let cube := cubeOfLengths logL logLz
    let msgs := (links.head?.map (·.messages)).getD []
    let rows := (if links.isEmpty then 0 else open_.headD 0) + (if 0 < l then 1 + answers else 0) +
      sumT (keptOf g |>.map fun k => 2 * k.shape.answers) + sumT (msgs.map fun m => m.shape.answers)
    let keptBefore := sumT (keptOf g |>.map fun k => k.shape.mainRows)
    let keptHere := sumT (((gs.head?.map keptOf).getD []).map fun k => k.shape.mainRows)
    let cubes := (if 0 < l then [cube g.target.shape] else []) ++
      msgs.map fun m => cube m.shape
    reqLoadFrom answers logL logLz (l + 1) gs (links.drop 1) (open_.drop 1)
      { k := max load.k g.k
        slots := max load.slots (2 ^ clog2 (1 + keptHere))
        cubeBits := cubes.foldl max load.cubeBits
        rows := max load.rows rows
        rowsADraw := if 0 < l then max load.rowsADraw (3 + keptBefore) else load.rowsADraw }

/-- The load of a chain of links. What rides at the start (`atStart`) is not read, whereas req_load
also counts its cubes: the one caller, `proofSized`, passes a shape without it. -/
def reqLoad (s : ReqShape) (logL logLz : Nat) (openRows : List Nat) : ReqLoad :=
  reqLoadFrom s.answers logL logLz 0 (reqGroups s).toList s.link openRows {}

/-- What follows from the lines and the sub-proofs' shapes for a proof's chains. -/
structure ProofSized where
  set : Setting
  codes : Codes
  /-- the links' group -/
  link : Solved
  /-- the message into which the last link is closed, with the stages of the last test. It is under
  the links' codes, at their distance; it has at most as many rows as a link's group, and all are
  over the extension field -/
  last : TestSizes
  request : ReqShape
  batch : LinSized

/-- Fills the numbers of the links' two codes into the links' oracle messages. Both are 0:
`proofSized` enters these codes into the empty lists first. The messages' numbers of answers stay as
the caller gave them; a shape in which they differ from the request's is refused where the finished
shape is tested (`reqOk`). -/
def fillLinks (links : List ReqLink) : List ReqLink :=
  links.map fun l => { l with messages := l.messages.map fun m =>
    { m with shape := canonical { m.shape with code := 0, maskCode := 0 } } }

/-- The links with a number of answers put into all their oracle messages: for a caller whose own
shapes do not say it. -/
def withAnswers (answers : Nat) (links : List ReqLink) : List ReqLink :=
  links.map fun l => { l with messages := l.messages.map fun m =>
    { m with shape := { m.shape with answers := answers } } }

/-- The shape of a chain of links before anything is sized: the links alone. The groups of the
chain follow from it. -/
def shapeOfLinks (links : List ReqLink) (answers : Nat) : ReqShape :=
  { code := 0, maskCode := 0, link := links, atStart := [], answers := answers, last := [],
    choice := ⟨true⟩ }

/-- Sizes a proof's chains. The links' group is sized for `rows + rowsADraw * 4096` batched rows:
4096 is meant to be more draws than any list has, and the plan's exact comparison has the last word.
The masks of the request's rows on the table go out with its first message. They are read at the
list of the request's own test on the table and at no link's, so they get a class of leaves, and
with it a tree, of their own (`rider`). -/
def proofSized (l : Lines) (sub : Subproofs) : Option ProofSized := do
  let s := settingOf l
  let links := fillLinks sub.links
  if sub.openRows.length != links.length then none
  let before := shapeOfLinks links l.answers
  let load := reqLoad before l.link.logL l.link.maskLogL sub.openRows
  let groups := (reqGroups before).toList
  let shape := { shapeOf l.link load.k false with slots := load.slots }
  let messages := links.foldl (fun m x => max m (2 * x.messages.length + 2)) 8
  let linkLoad : GroupLoad :=
    { cubeBits := max (stageCubeBits shape) load.cubeBits, messages := messages,
      batchedRows := load.rows + load.rowsADraw * 4096 }
  let link ← solveGroup s .request linkLoad id shape
  let lastGroup : GroupSize :=
    { link.group with k := (groups.getLast?.map (·.k)).getD 1, slots := 1,
                      main := { link.group.main with overE := true } }
  let stages ← solveStages s .request lastGroup link.t l.link.stages
  let T ← deriveTable s l
  let (last, codes1) := ioppStages stages {}
  let rows := Send.maskRowsFor
    (sub.pendingRows + (if 1 < sub.pendingRows then Batt.masksOf l.blockLog else 0))
    (2 ^ l.own.maskLogL) l.answers
  if rows == 0 then none
  let (batch, codes2) ← linSized s (linLines l sub.matrixRows rows false) T codes1
  let rider := links.foldl (fun c x => x.messages.foldl (fun c m => max c (m.leafClass + 1)) c) 0
  pure { set := s, codes := codes2, link := link, last := ⟨lastGroup, link.t, stages⟩,
         request := { code := 0, maskCode := 0, link := links,
                      atStart := [{ batch.input with leafClass := rider }], answers := l.answers,
                      last := last, choice := ⟨true⟩ },
         batch := batch }

/-- The sending of oracle messages of a link's group, `group`. The last `riders` of them only share
the prover's message: their samples are priced with the list of their own group, `atStart`.
`ownRound`: the answers are taken in by a round of the sending itself; else by the round of
positions of the switch that sends these oracle messages. -/
def reqSend (codes : Codes) (sent : List OracleNotice) (group atStart : GroupSize) (riders : Nat)
    (ownRound : Bool) : Planning Unit := do
  let own := sent.length - riders
  let sampled := (zipT (List.range sent.length) sent).filter (fun x => 0 < x.2.shape.answers) |>.map
    fun x => (⟨cubeBitsOf codes x.2.shape, [if x.1 < own then group else atStart]⟩ : SampleSize)
  planSend sampled (← must (treesOf codes sent.toArray)) ownRound

/-- The moments of a link from `moment` on, as many as the fuel: the sending of the moment's oracle
messages and the sub-proof's rounds after it. Under which scope the frame's rounds are planned is
not for a sub-proof's routine to say: the scope is set again after it. Returns the sample rows that
are added. Not `OnBytes.reqMoments` (OnBytes/Iop/Req.lean), the number of a link's moments. -/
def reqMoments (z : ProofSized) (sub : Subproofs) (l : Nat) (msgs : List ReqMessage) :
    Nat → Nat → Planning Nat
  | 0, _ => pure 0
  | fuel + 1, moment => do
    let sent : List OracleNotice :=
      (msgs.filter fun m => m.moment == moment).map fun m => ⟨m.shape, m.leafClass⟩
    reqSend z.codes sent z.link.group z.batch.own.first 0 true
    sub.plan l moment
    modify fun p => { p with scope := .request }
    let more ← reqMoments z sub l msgs fuel (moment + 1)
    pure (sumT (sent.map (·.shape.answers)) + more)

/-- The frame's rounds from group number l on. The last argument is the group of the link that was
closed last. In the body, `carried` counts the rows that the switch into the present group leaves on
it: the carried claim, the kept messages' old sample rows, and 3 + (kept rows) for each drawn
position. -/
def reqPlanFrom (z : ProofSized) (sub : Subproofs) :
    Nat → List ReqGroup → List ReqLink → List Nat → GroupSize → Planning Unit
  | _, [], _, _, _ => pure ()
  | l, g :: gs, links, open_, before => do
    let S := z.request
    let link := links.head?
    let msgs := (link.map (·.messages)).getD []
    let members : List OracleNotice :=
      (if 0 < l then [⟨g.target.shape, g.target.leafClass⟩] else []) ++
      (keptOf g).map (fun k => ⟨k.shape, k.leafClass⟩) ++
      (msgs.filter fun m => m.moment == 0).map (fun m => ⟨m.shape, m.leafClass⟩) ++
      [foldMaskNotice (ioppFoldShape ⟨S.code, S.maskCode, g.k, g.h⟩ {})]
    let sampleRows := sumT (members.map (·.shape.answers))
    let sent := if l == 0 then members ++ S.atStart else members
    if (link.map (·.plain)).getD 0 != 0 then
      planScalars ((link.map (·.plain)).getD 0)
      closeNone "REPLY"
    reqSend z.codes sent (if link.isSome then z.link.group else z.last.first) z.batch.own.first
      (if l == 0 then S.atStart.length else 0) (l == 0)
    let carried ← if 0 < l then do
        let t ← planLoc before
        pure (1 + sumT ((keptOf g).map (·.shape.answers)) +
          t * (3 + sumT ((keptOf g).map (·.shape.mainRows))))
      else pure 0
    match link with
    | none => planIopp z.last.stages (carried + sampleRows) 0 S.choice.masksRide
    | some _ =>
      sub.plan l 0
      modify fun p => { p with scope := .request }
      let moments := (msgs.getLast?.map (·.moment + 1)).getD 0
      let more ← reqMoments z sub l msgs (moments - 1) 1
      let keptRows := sumT (((gs.head?.map keptOf).getD []).map (·.shape.mainRows))
      let closed : GroupSize :=
        { z.link.group with k := g.k, h := g.h, slots := 2 ^ clog2 (1 + keptRows) }
      planBat [closed] (open_.headD 0 + carried + sampleRows + more)
      planFold closed 0
      reqPlanFrom z sub (l + 1) gs (links.drop 1) (open_.drop 1) closed

/-- Every round of the frame of a chain of links, with the sub-proofs' rounds between them. -/
def reqPlan (z : ProofSized) (sub : Subproofs) : Planning Unit :=
  reqPlanFrom z sub 0 (reqGroups z.request).toList z.request.link sub.openRows z.link.group

/-- The plan of a proof's first chain. -/
def firstPlan (z : ProofSized) (sub : Subproofs) : Except String Planned :=
  finishHeld z.set .request do
    reqPlan z sub
    sub.afterLinks
    modify fun p => { p with scope := .request }
    if 1 < sub.pendingRows then planBatt sub.pendingRows z.batch.shape.kCol
    linPlanFirst z.codes z.batch
    planSeal

/-- The plans of a proof's three chains, in the order of the file. Each holds. -/
def proofPlans (z : ProofSized) (sub : Subproofs) : Except String (List Planned) := do
  pure [← firstPlan z sub, ← sharedPlan z.set z.codes z.batch, ← secondPlan z.set z.batch]

/-- The parameter bytes of a proof's three chains. -/
structure ProofParams where
  first : ByteArray
  shared : ByteArray
  second : ByteArray

/-- The parameter bytes of a proof's three chains, from the lines of the parameter file, the
sub-proofs' shapes, the layout, the links' identifiers and the digest of the public files. Refused
if no admissible numbers follow, or if a round of a plan does not hold at the target. Nothing calls
this function: the program forms these bytes in `configure` (OnBytes/Params/Configure.lean), which
also asks the tests and conditions that are not asked here. -/
def proofParams (l : Lines) (sub : Subproofs) (layout : ReqLayout) (identifiers : List Nat)
    (cfg : ByteArray) : Except String ProofParams := do
  let z ← orRefuse (proofSized l sub)
  let p ← firstPlan z sub
  let first := Fmt.paramsBytes p.plan cfg
    [("codes", spellCodes z.codes), ("the test on the table", spellLin z.batch.shape),
     ("request's shape", spellReq z.request), ("layout", spellLayout layout),
     ("links' identifiers", spellWords identifiers), ("pending rows", spellWord sub.pendingRows),
     ("binding tree", spellBinding ⟨clog2 l.slots, z.set.saltBytes⟩)]
  pure ⟨first, ← sharedParams z.set z.codes z.batch cfg, ← secondParams z.set z.batch cfg⟩

end OnBytes.Params
