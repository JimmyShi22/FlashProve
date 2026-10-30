-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/HB/LLHARD/RadiiWritten.lean: the radii of the first proof chain's sampled oracle messages AT
THE WRITTEN VALUES OF THE FULL SIZE, by an evaluation in Lean's kernel. Definitions and statements
with their proofs.

Why. The radii are no fields: a maker outside the verifier (`packListOf`, Johnson/G/PackList.lean)
computes each from the setting, a group's sizes and the message's shape. That maker plans every
chain twice: Lean's kernel does not bear it whole. What a radius reads of it is little: the samples
of the sendings, which the planner's text lays off the sizes of a proof file.

  `reqSamples`, `momentSamples`, `stageSamples`, `frameSamples`, `samplesP0 z`: the samples of the
    first proof chain's sendings as a function of the sizes z: the text of `nFrame`, `nMoments`,
    `nStages`, `nReqSend`, `nLinFirst` (Johnson/G/Calls.lean) with the notes of sendings kept and
    all else dropped. THAT THE MAKER's OWN LIST OF CALLS HAS THESE SAMPLES IS NOT SHOWN HERE: OWED.

    (Where this and lean/THEOREM.md differ, the page holds.)
  `packChain s file chain smp d`: the text of `packListOf` at one chain.
  `radsFull`: the written radii: entries 24 to 105 of `packFullLit` (Johnson/G/PackLit.lean).
  `radii_written`: (W). `radii_rejects_short`, `radii_rejects_swapped`: (N). `radsFull_whole`: 82
    lists, 167 pairs, the shapes of the written sendings (Johnson/G/SendsWritten.lean).
All four by evaluations in Lean's kernel (`decide +kernel`).

THE ARGUMENTS, EACH WITH ITS WRITTEN TERM AND ITS TIE: the setting · `recordSet` · `made_in_scope` ·
the sizes · `proofSizedFull` · an accept of `madeIs` · the sendings · `proofSends0` · an accept of
`proofSendsIs`. None is called here. Limits. The first proof chain alone. Nothing on soundness.

-/
import Johnson.G.PackList
import Johnson.G.PackLit
import Johnson.G.SendsWritten
import Johnson.Desc.Ok.PlanWritten.SizedLit
import OnBytes.Params.EntryStagesRecord

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.G
open OnBytes OnBytes.Params
open VerifiableInference.PlanWritten (proofSizedFull)

/-! ## 1 The samples of the first proof chain's sendings, off the sizes of a proof file -/

/-- The samples that `nReqSend` (Johnson/G/Calls.lean) notes: its own text. -/
def reqSamples (codes : Codes) (sent : List OracleNotice) (group atStart : GroupSize)
    (riders : Nat) : List SampleSize :=
  let own := sent.length - riders
  (zipT (List.range sent.length) sent).filter (fun x => 0 < x.2.shape.answers) |>.map
    fun x => (⟨cubeBitsOf codes x.2.shape, [if x.1 < own then group else atStart]⟩ : SampleSize)

/-- `nMoments`' sendings. -/
def momentSamples (z : ProofSized) (msgs : List ReqMessage) : Nat → Nat → List (List SampleSize)
  | 0, _ => []
  | fuel + 1, moment =>
    reqSamples z.codes
        ((msgs.filter fun m => m.moment == moment).map fun m => ⟨m.shape, m.leafClass⟩)
        z.link.group z.batch.own.first 0 ::
      momentSamples z msgs fuel (moment + 1)

/-- `nStages`' sendings: one at each code switch. -/
def stageSamples : List StageSize → List (List SampleSize)
  | _ :: y :: rest => [⟨stageCubeBits y.g, [y.g]⟩] :: stageSamples (y :: rest)
  | _ => []

/-- `nFrame`'s sendings. -/
def frameSamples (z : ProofSized) : Nat → List ReqGroup → List ReqLink → List (List SampleSize)
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
    reqSamples z.codes sent (if link.isSome then z.link.group else z.last.first)
        z.batch.own.first (if l == 0 then S.atStart.length else 0) ::
      match link with
      | none => stageSamples z.last.stages
      | some _ =>
        momentSamples z msgs ((msgs.getLast?.map (·.moment + 1)).getD 0 - 1) 1 ++
          frameSamples z (l + 1) gs (links.drop 1)

/-- **The samples of the first proof chain's sendings**, one list a sending: the frame's, then
W's. -/
def samplesP0 (z : ProofSized) : List (List SampleSize) :=
  frameSamples z 0 (reqGroups z.request).toList z.request.link ++
    ((linSizeOf z.codes z.batch).map fun x => [x.w :: x.besideW]).getD []

/-! ## 2 One chain's share of `packListOf` -/

/-- The text of `packListOf` (Johnson/G/PackList.lean) at one chain. smp: the samples of its
sendings. -/
def packChain (s : Setting) (file : String) (chain : Nat) (smp : List (List SampleSize))
    (d : ChainSends) : Except String (List (Codes × List (OracleShape × Nat))) := do
  unless smp.length == d.sends.length do
    throw s!"{file} {chain}: the calls and the list have not as many sendings"
  (smp.zip d.sends).mapM fun (o, x) => do
    let at_ := s!"{file} {chain}, entry {x.entry} ({x.label})"
    let sampled := (x.sent.filter fun m => 0 < m.shape.answers).map (·.shape)
    let o' :=
      if o.length == sampled.length then o
      else if o.length == 1 then List.replicate sampled.length (o.headD ⟨0, []⟩) else []
    unless o'.length == sampled.length do
      throw s!"{at_}: the sampled messages and the samples are not as many"
    let l ← (sampled.zip o').mapM fun (sh, sm) => do
      pure (sh, ← radiusFor s d.codes at_ sh sm)
    unless x.behind.answers == l.length * s.samples do
      throw s!"{at_}: (p3) the entry behind takes in another number of answers"
    unless x.seed.drawE == s.samples * (Johnson.Pack.bMax d.codes l + 1) do
      throw s!"{at_}: (p4) the entry draws another number of elements"
    pure (d.codes, l)

/-! ## 3 At the written values -/

/-- **The written radii of the first proof chain**: one list a sending; in it, for each sampled
oracle message, its shape and its radius. -/
def radsFull : List (List (OracleShape × Nat)) := ((packFullLit.drop 24).take 82).map (·.2)

set_option maxRecDepth 1000000 in
/-- **(W)** At the written setting, sizes and sendings the text returns, and gives the written
radii. -/
theorem radii_written :
    (packChain recordSet "proof" 0 (samplesP0 proofSizedFull) proofSends0).toOption.map
      (·.map (·.2)) = some radsFull := by decide +kernel

set_option maxRecDepth 1000000 in
/-- **(N)** Without the first sending's samples the text refuses. -/
theorem radii_rejects_short :
    (packChain recordSet "proof" 0 ((samplesP0 proofSizedFull).drop 1) proofSends0).toOption =
      none := by decide +kernel

set_option maxRecDepth 1000000 in
/-- **(N)** With the first two sendings' samples exchanged it refuses too: the first sending has
four sampled oracle messages, the second one. -/
theorem radii_rejects_swapped :
    (packChain recordSet "proof" 0
      ((samplesP0 proofSizedFull).drop 1 |>.take 1 |>.append ((samplesP0 proofSizedFull).take 1)
        |>.append ((samplesP0 proofSizedFull).drop 2)) proofSends0).toOption = none := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- 82 lists, 167 pairs; sending by sending the shapes are those of the written sendings' sampled
oracle messages. -/
theorem radsFull_whole :
    (radsFull.length, (radsFull.map (·.length)).sum,
      decide (radsFull.map (·.map (·.1)) = proofSends0.sends.map fun x =>
        (x.sent.filter fun m => 0 < m.shape.answers).map (·.shape))) = (82, 167, true) := by
  decide +kernel

end Johnson.G

#print axioms Johnson.G.radii_written
#print axioms Johnson.G.radii_rejects_short
#print axioms Johnson.G.radii_rejects_swapped
#print axioms Johnson.G.radsFull_whole
