-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/RowsRun.lean: A TEST WITH CODE ON THE PROOF FILE's PUBLIC PART: "THE
SENDINGS' ROWS CAN BE MADE OF WHAT THE PLANNER HAS MADE, AND IN THE FIRST PROOF CHAIN's ROWS ONE
SHAPE HAS ONE RADIUS". Definitions alone. IT STANDS IN THE VERIFIER's LIST OF TESTS ON THE PUBLIC
FILES (Johnson/Desc/Laid/ProofAsks.lean): so it imports running texts alone and declares nothing but
definitions.

What it is for. Laws on the IOP as written in Lean read, for every sampled oracle message of the
first proof chain, a decoding radius off the rows of the sendings (Johnson/G/LinkSig.lean:
sendRowsOf). That maker reads the three public files a second time, through the program
`verify-on-bytes`'s planner, and refuses on its own at several places. Here the same rows are made
of what the public part already holds. Model.Verify.planned and Params.configure are not called; BUT
EACH OF THE SEVEN CHAINS' PLANS IS WRITTEN ANEW FROM THE SIZES, TWICE, by the planner's routines as
Johnson/G/Calls.lean notes them (noted; replay), and held against the plan that the public part
holds. No file is read, and no written value is compared. That the test reaches no hash function is
held by a walk over the names and modules that it reaches, not by a theorem.
  `Arm`, `armOf X link`   what the planner's routine for a link reads of the public part: the
                    head's, a layers' or an attention's routine with its sizes; or none.
  `nArm`, `nMomentsA`, `nFrameA`   Johnson/G/Calls.lean's nLink, nMoments, nFrame, over a table of
                    arms.
  `callsFrom`       that file's callsOf behind its planner: the seven lists of calls; it refuses
                    unless, at each chain, the plan written while the calls are noted, and the plan
                    that the calls alone give, agree with the planner's plan, round for round, in
                    four of the seven fields of each round (PlanRound, OnBytes/Params/Planner.lean):
                    entry, error, why and scope. The fields group, rests and wordFault are not
                    compared (same, Johnson/G/Calls.lean).
  `samplesOf`, `codeIs`, `radiusAt`, `mainOf`, `maskOf`, `lengthOf`, `cubeOf`, `cubeMax`, `radiusOf`
                      the numbers of Johnson/G/PackList.lean and Johnson/Pack/Port.lean | PortZ.lean
                      | PortS.lean, written once more.
  `packRun`         PackList.lean's packListOf behind its two readings: for every sending its
                    sampled messages' shapes, each with a radius.
  `firstRun`        the sampled messages of the first proof chain's sendings, in order, each with
                    its radius; it refuses where the two lists have not as many sendings.
  `oneRadius`       one shape has one radius.
  `rowsMadeB Z`     THE TEST.
What a yes gives: Johnson/Desc/First/Link/Law/RowsRunLaws.lean. Of a no that file says nothing that
can be spent: its law no_of_no takes "the live test accepts" as a premise, and the live test asks
this very test.

WHAT THE TEST IS FOR, PLAINLY. It is NOT KNOWN TO REJECT ANY PUBLIC FILES THAT THE VERIFIER's OTHER
TESTS ON THE PUBLIC FILES LET THROUGH: what it holds against each other (the plans, and what the
planner's routines read of the public part) comes, from files, out of one run of one planner. It
turns an assumption into a check that the verifier makes: laws take "the sendings' rows can be made,
with one radius a shape" as a premise; we believe that it holds wherever the tests on what the
planner has made accept, but have no proof. So it guards against a gap in our proofs, not against a
known bad file; its negative tests turn one field of the parsed value, never a file's bytes. WERE
THAT PREMISE A THEOREM, NO LAW WOULD NEED THIS TEST.

What a no rejects, plainly. The test replays all seven chains (callsFrom), as the named condition's
own test does. So it rejects also where the plan written anew, or the calls' replay, parts from the
public part's plan at one of the KEY FILE's three chains or at the ENTRY FILE's chain, though the
laws that lean on it read the first proof chain's rows alone.
Defaults in this text (each is Calls.lean's or PackList.lean's own). mainOf and maskOf take the
default code where a shape names none: such a shape then fails the comparison of codes in radiusOf
(codeIs none = false) where that code is asked: the main code where the shape has main rows, the
mask code where it has mask rows or no main rows. o.headD ⟨0, []⟩ stands under o.length == 1. In
nFrameA: the messages and the
plain scalars of a link that is not there are the empty list and 0, and the arm behind is then the
last test's; open_.headD 0, the last message's moment and the next group's kept rows are read under
"some link" alone; a wrong value there gives another plan, which the comparison of plans rejects.
The words that are thrown bear marks ((k1), (k2), (p1) to (p5)): rowsMadeB drops them: no
user sees them. OnBytes/Params/JohnsonLaws.lean is imported for the definition upperRadius alone.

Limits. SECOND TEXTS: tied to the texts that they repeat by theorems in the file just named and in
Johnson/Desc/First/Link/Law/RowsFrom.lean. Nothing is proved
here. Nothing on what a radius means. Nothing on soundness or on hiding.

-/
import Johnson.G.SendsFrom
import OnBytes.Params.JohnsonLaws
import OnBytes.Model.VerifySubproofs
import OnBytes.Model.RoundSizes
import Johnson.Desc.ProofFile.Pub

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Params
open Johnson.G

/-- What the noted routine of a link reads of the public part. -/
inductive Arm where
  | head (look : ForestSize) (x : HeadRounds) (small : SmallSize)
  | layer (look : ForestSize) (x : LayerRounds) (small : SmallSize) (claims : Nat)
  | attention (look : ForestSize) (x : AttentionRounds) (small : SmallSize)
  | none

/-- The arm of a link, off the public part: nLink's own case distinction. -/
def armOf (X : OnBytes.Model.Verify.Public) (link : Nat) : Arm :=
  let step := if X.p4 then 2 else 1
  let g := link / step
  if link == step * X.NGr then
    .head (OnBytes.Model.forestSize X.HLy.fs) (X.H.own X.hS) (OnBytes.Model.smallSize X.H.tl)
  else if link % step == 0 then
    match X.G[g]? with
    | some hp =>
      .layer (OnBytes.Model.forestSize X.y.fo) (OnBytes.Model.Verify.layerNumbers X.layers hp g)
        (OnBytes.Model.smallSize hp.tl) hp.nBatched
    | none => .none
  else
    match X.A[g]? with
    | some a =>
      .attention (OnBytes.Model.forestSize a.fs) a.own (OnBytes.Model.smallSize a.seam.tl)
    | none => .none

/-- The noted routine of an arm. -/
def nArm : Arm → Nat → N Unit
  | .head l x s, moment => nHead l x s moment
  | .layer l x s c, moment => nLayer l x s c moment
  | .attention l x s, moment => nAttention l x s moment
  | .none, _ => (needs false : Planning Unit)

/-- `nMoments`, over a table of arms. -/
def nMomentsA (A : Nat → Arm) (z : ProofSized) (l : Nat) (msgs : List ReqMessage) :
    Nat → Nat → N Nat
  | 0, _ => pure 0
  | fuel + 1, moment => do
    let sent : List OracleNotice :=
      (msgs.filter fun m => m.moment == moment).map fun m => ⟨m.shape, m.leafClass⟩
    nReqSend z.codes sent z.link.group z.batch.own.first 0 true
    nArm (A l) moment
    note (.scope .request)
    let more ← nMomentsA A z l msgs fuel (moment + 1)
    pure (sumT (sent.map (·.shape.answers)) + more)

/-- `nFrame`, over a table of arms. -/
def nFrameA (A : Nat → Arm) (z : ProofSized) :
    Nat → List ReqGroup → List ReqLink → List Nat → GroupSize → N Unit
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
      note (.scalars ((link.map (·.plain)).getD 0))
      note .reply
    nReqSend z.codes sent (if link.isSome then z.link.group else z.last.first) z.batch.own.first
      (if l == 0 then S.atStart.length else 0) (l == 0)
    let carried ← if 0 < l then do
        let t ← noteV (.loc before) (planLoc before)
        pure (1 + sumT ((keptOf g).map (·.shape.answers)) +
          t * (3 + sumT ((keptOf g).map (·.shape.mainRows))))
      else pure 0
    match link with
    | none => nIopp z.last.stages (carried + sampleRows) 0 S.choice.masksRide
    | some _ =>
      nArm (A l) 0
      note (.scope .request)
      let moments := (msgs.getLast?.map (·.moment + 1)).getD 0
      let more ← nMomentsA A z l msgs (moments - 1) 1
      let keptRows := sumT (((gs.head?.map keptOf).getD []).map (·.shape.mainRows))
      let closed : GroupSize :=
        { z.link.group with k := g.k, h := g.h, slots := 2 ^ clog2 (1 + keptRows) }
      note (.bat [closed] (open_.headD 0 + carried + sampleRows + more))
      note (.fold closed 0)
      nFrameA A z (l + 1) gs (links.drop 1) (open_.drop 1) closed

/-- `callsOf`'s text behind its planner and its reading of the shapes. -/
def callsFrom (c : Configured) (openRows : List Nat) (pendingRows : Nat) (A : Nat → Arm) :
    Except String (Setting × List Johnson.G.Chain) := do
  let z := c.sized
  let one (file : String) (ch : Nat) (scope : Scope) (x : N Unit) (truth : Planned) :
      Except String Johnson.G.Chain := do
    let (calls, P) ← noted z.set scope x
    unless sameAll P.rounds truth.rounds do
      throw s!"(k1) fails at {file} {ch}: the plan written while the calls were noted differs"
    let Q ← replay z.set scope calls
    unless sameAll Q.rounds truth.rounds do
      throw s!"(k2) fails at {file} {ch}: the list of calls, replayed alone, gives another plan"
    pure ⟨file, ch, scope, calls⟩
  let sc (x : LinSized) (other : Scope) : Scope := if x.lines.oneTime then .once else other
  match c.key, c.proof with
  | [k0, k1, k2], [p0, p1, p2] =>
    let l ← [
      one "key" 0 .once (do
        note (.record z.key.once.table)
        note (.send [⟨cubeBitsOf z.key.codes z.key.once.input.shape, [z.key.once.own.first]⟩] 1
          true)
        nRanges z.key.codes z.key.ranges
        nLinFirst z.key.codes z.key.once
        note .seal) k0,
      one "key" 1 (sc z.key.once .shared) (do nLinShared z.key.codes z.key.once; note .seal) k1,
      one "key" 2 (sc z.key.once .request) (nLinSecond z.key.once) k2,
      one "entry" 0 .once (nLinkPlan z.link) c.entry,
      one "proof" 0 .request (do
        nFrameA A z.proof 0 (reqGroups z.proof.request).toList z.proof.request.link openRows
          z.proof.link.group
        note (.scope .request)
        if 1 < pendingRows then note (.batt pendingRows z.proof.batch.shape.kCol)
        nLinFirst z.proof.codes z.proof.batch
        note .seal) p0,
      one "proof" 1 (sc z.proof.batch .shared)
        (do nLinShared z.proof.codes z.proof.batch; note .seal) p1,
      one "proof" 2 (sc z.proof.batch .request) (nLinSecond z.proof.batch) p2 ].mapM id
    pure (z.set, l)
  | _, _ => throw "the key or the proof has not three plans"

/-- The samples of the sendings that a call makes, one list for each sending. -/
def samplesOf : Call → List (List SampleSize)
  | .send o _ _ => [o]
  | .cs _ y cube _ _ _ => [[⟨cube, [y]⟩]]
  | .linFirst x => [x.w :: x.besideW]
  | .linShared _ x => [[x.u], x.omega :: x.besideOmega]
  | .link _ u => [[u]]
  | _ => []

/-- A code of a chain's list and a code as the planner sizes it agree in their three numbers. -/
def codeIs (c : Option Code) (x : CodeSize) : Bool := c == some ⟨x.logN, x.ell, x.r⟩

/-- The radius of a shape in a group, in positions. -/
def radiusAt (s : Setting) (sh : OracleShape) (g : GroupSize) : Nat :=
  let a := analysis s g
  if sh.mainRows != 0 then upperRadius a.mainAt.delta (2 ^ g.main.logN)
  else upperRadius a.maskAt.delta (2 ^ g.mask.logN)

/-- The code of a shape's main rows, and that of its mask rows. -/
def mainOf (cs : Codes) (s : OracleShape) : Code := cs.base.getD s.code default
def maskOf (cs : Codes) (s : OracleShape) : Code := cs.mask.getD s.maskCode default

/-- The logarithm of the number of long positions. -/
def lengthOf (cs : Codes) (s : OracleShape) : Nat := max (mainOf cs s).logN (maskOf cs s).logN

/-- The cube's bits. -/
def cubeOf (cs : Codes) (s : OracleShape) : Nat :=
  if 0 < s.mainRows ∧ 0 < s.maskRows then
    max (ceilLog2 s.mainRows + ceilLog2 (mainOf cs s).ell)
      (ceilLog2 s.maskRows + ceilLog2 (maskOf cs s).ell) + 1
  else (if 0 < s.mainRows then ceilLog2 s.mainRows + ceilLog2 (mainOf cs s).ell else 0) +
    (if 0 < s.maskRows then ceilLog2 s.maskRows + ceilLog2 (maskOf cs s).ell else 0)

/-- The largest cube's bits. -/
def cubeMax (cs : Codes) (l : List (OracleShape × Nat)) : Nat :=
  (l.map fun x => cubeOf cs x.1).foldr max 0

/-- The radius of one sampled message, from the groups that price its sample. -/
def radiusOf (s : Setting) (codes : Codes) (at_ : String) (sh : OracleShape) (sm : SampleSize) :
    Except String Nat := do
  if sm.groups.isEmpty then throw s!"{at_}: a sampled message whose sample has no group"
  unless cubeOf codes sh == sm.cubeBits do
    throw s!"{at_}: (p2) the shape's cube has not the sample's bits"
  sm.groups.foldlM (fun r g => do
    let main := sh.mainRows != 0
    unless (if main then codeIs codes.base[sh.code]? g.main
        else codeIs codes.mask[sh.maskCode]? g.mask) do
      throw s!"{at_}: (p1) the group's code is not the shape's"
    unless !(main && sh.maskRows != 0) || codeIs codes.mask[sh.maskCode]? g.mask do
      throw s!"{at_}: (p5) the group's mask code is not the shape's"
    let logN := if main then g.main.logN else g.mask.logN
    unless lengthOf codes sh == logN do
      throw s!"{at_}: the length at which the radius counts is not the code's own"
    pure (max r (radiusAt s sh g))) 0

/-- For every sending: its chain's codes and its sampled messages' shapes, each with a radius. -/
def packRun (c : Configured) (openRows : List Nat) (pendingRows : Nat) (A : Nat → Arm) :
    Except String (List (Codes × List (OracleShape × Nat))) := do
  let (s, chains) ← callsFrom c openRows pendingRows A
  let sends ← sendsFrom c
  let per ← (chains.zip sends).mapM fun (c, d) => do
    let smp := c.calls.flatMap samplesOf
    unless smp.length == d.sends.length do
      throw s!"{c.file} {c.chain}: the calls and the list have not as many sendings"
    (smp.zip d.sends).mapM fun (o, x) => do
      let at_ := s!"{c.file} {c.chain}, entry {x.entry} ({x.label})"
      let sampled := (x.sent.filter fun m => 0 < m.shape.answers).map (·.shape)
      let o' :=
        if o.length == sampled.length then o
        else if o.length == 1 then List.replicate sampled.length (o.headD ⟨0, []⟩) else []
      unless o'.length == sampled.length do
        throw s!"{at_}: the sampled messages and the samples are not as many"
      let l ← (sampled.zip o').mapM fun (sh, sm) => do
        pure (sh, ← radiusOf s d.codes at_ sh sm)
      unless x.behind.answers == l.length * s.samples do
        throw s!"{at_}: (p3) the entry behind takes in another number of answers"
      unless x.seed.drawE == s.samples * (cubeMax d.codes l + 1) do
        throw s!"{at_}: (p4) the entry draws another number of elements"
      pure (d.codes, l)
  pure per.flatten

/-- The sampled messages of the first proof chain's sendings, in order, each with its radius. -/
def firstRun (c : Configured) (openRows : List Nat) (pendingRows : Nat) (A : Nat → Arm) :
    Except String (List (OracleShape × Nat)) := do
  let sends ← sendsFrom c
  let pack ← packRun c openRows pendingRows A
  let flat := sends.flatMap fun c => c.sends.map fun s => (c, s)
  unless flat.length == pack.length do throw "the two lists have not as many sendings"
  pure (((flat.zip pack).filter fun x => x.1.1.file == "proof" && x.1.1.chain == 0).flatMap
    fun x => x.2.2)

/-- One shape has one radius. -/
def oneRadius (es : List (OracleShape × Nat)) : Bool :=
  es.all fun a => es.all fun b => a.1 != b.1 || a.2 == b.2

/-- **The test**: the rows can be made of what the public part holds, and in the first proof
chain's rows one shape has one radius. -/
def rowsMadeB (Z : ProofFile.Pub) : Bool :=
  match firstRun Z.made.p.chains.made
      (List.replicate Z.made.p.chains.made.sized.proof.request.link.length 1)
      (Z.made.p.X.NGr + 1) (armOf Z.made.p.X) with
  | .ok es => oneRadius es
  | .error _ => false

end VerifiableInference.Desc.LinkJoin
