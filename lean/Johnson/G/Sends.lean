-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/G/Sends.lean: every sending of oracle messages in the seven plans of the verifier on bytes,
with the codes of its chain, computed from the three public files.

For the statements on how oracle messages are packed (Johnson/Pack/). Definitions only.
Main names:
  `Sending`: a label, the oracle messages of one prover's message in the order of sending, and the
    plan's entry "SEND seed" of that sending with the entry behind it.
  `sendsOf`: for each chain, in the order key 0, 1, 2, entry 0, proof 0, 1, 2: its codes and its
    sendings. It refuses unless a chain's sendings are as many as its plan's entries "SEND seed",
    in order, and at each `treesOf codes sent` is that entry's hashed number of roots.
Where the lists come from: the frame's are the lists `sent` of `reqPlanFrom` and `reqMoments`
(OnBytes/Params/DeriveReq.lean), written once more; the key's first two are the index-mask message
and `Wf.messageOf`; W, the folded row and Omega are `linMessageW`, `linMessageU` and
`linMessageOmega`; the link's is `linkMessage`; a code switch's inside a proximity test follows
`ioppStagesVerify` (OnBytes/Iop/Prox.lean): the target, then, if masks ride, the next fold's fresh
mask or the masking word of the last step.
Limits: no theorem is stated. Which of the verifier's functions give a sending's list, and that the
target comes first at a code switch, is a reading of the verifier's text; the refusals above hold it
against the plan by two counts only, where `sendsOf` is evaluated. A sending here is an entry "SEND
seed" of a plan. An oracle message whose root goes in an entry of another name is not listed: at the
full-size example these are two, the fresh mask that a fold sends itself in its entry "FOLD
epsilon", in the shared chain of the key and in that of the proof.

-/
import Johnson.G.Calls

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.G

open OnBytes OnBytes.Params

/-- The oracle messages of one prover's message, under a label. -/
structure Listed where
  label : String
  sent : List OracleNotice

/-- The sendings of the code switches of a proximity test, from stage number i on. -/
def ioppSends (t : String) (answers : Nat) (ride : Bool) : Nat → List IoppStage → List Listed
  | i, _ :: next :: rest =>
    let T := switchTargetStage next.code next.maskCode next.k next.h answers
    let others : List OracleNotice :=
      if !ride then []
      else if rest.isEmpty then [baseMaskNotice next.code next.maskCode 1 0]
      else [foldMaskNotice (ioppFoldShape next {})]
    ⟨s!"{t}, the code switch of stage {i}", ⟨T.shape, T.leafClass⟩ :: others⟩ ::
      ioppSends t answers ride (i + 1) (next :: rest)
  | _, _ => []

/-- The sendings of a link's later moments. -/
def momentSends (l : Nat) (msgs : List ReqMessage) : Nat → Nat → List Listed
  | 0, _ => []
  | fuel + 1, moment =>
    ⟨s!"link {l}, moment {moment}",
      (msgs.filter fun m => m.moment == moment).map fun m => ⟨m.shape, m.leafClass⟩⟩ ::
      momentSends l msgs fuel (moment + 1)

/-- The sendings of the frame of a proof's first chain, from group number l on. -/
def frameSends (z : ProofSized) (answers : Nat) :
    Nat → List ReqGroup → List ReqLink → List Listed
  | _, [], _ => []
  | l, g :: gs, links =>
    let S := z.request
    let link := links.head?
    let msgs := (link.map (·.messages)).getD []
    let members : List OracleNotice :=
      (if 0 < l then [⟨g.target.shape, g.target.leafClass⟩] else []) ++
      (keptOf g).map (fun k => ⟨k.shape, k.leafClass⟩) ++
      (msgs.filter fun m => m.moment == 0).map (fun m => ⟨m.shape, m.leafClass⟩) ++
      [foldMaskNotice (ioppFoldShape ⟨S.code, S.maskCode, g.k, g.h⟩ {})]
    let sent := if l == 0 then members ++ S.atStart else members
    let here : Listed := ⟨s!"link {l}, moment 0", sent⟩
    match link with
    | none => here :: ioppSends "the last group's test" answers S.choice.masksRide 1 S.last
    | some _ =>
      here :: momentSends l msgs ((msgs.getLast?.map (·.moment + 1)).getD 0 - 1) 1 ++
        frameSends z answers (l + 1) gs (links.drop 1)

/-- The sendings of a shared chain. -/
def linSharedSends (S : LinShape) (answers : Nat) : Except String (List Listed) := do
  let u ← match linMessageU S with
    | some a => pure a.toList
    | none => throw "linMessageU gives nothing"
  pure ([⟨"the folded row", u⟩, ⟨"Omega", (linMessageOmega S).toList⟩] ++
    ioppSends "the folded row's test" answers S.choice.masksRide 1 S.testU ++
    (if S.sharedSplitNeeded then ioppSends "Omega's test" answers S.choice.masksRide 1 S.testOmega
     else []))

/-- The sending of W. -/
def wSend (S : LinShape) : Except String Listed :=
  match linMessageW S with
  | some a => pure ⟨"W", a.toList⟩
  | none => throw "linMessageW gives nothing"

/-- A sending with its place in the plan. -/
structure Sending where
  /-- the number of its entry "SEND seed", from 1 -/
  entry : Nat
  label : String
  sent : List OracleNotice
  /-- the entry "SEND seed" -/
  seed : Fmt.Entry
  /-- the entry behind it, which takes in the answers -/
  behind : Fmt.Entry

/-- A chain's codes and sendings. -/
structure ChainSends where
  file : String
  chain : Nat
  codes : Codes
  sends : List Sending

/-- The sendings of the seven chains, from policy.txt, layout.txt and KL.bin. -/
def sendsOf (pol lay KL : ByteArray) : Except String (List ChainSends) := do
  let p ← OnBytes.Model.Verify.planned pol KL (some lay)
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

end Johnson.G
