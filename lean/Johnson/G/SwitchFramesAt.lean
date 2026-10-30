-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/G/SwitchFramesAt.lean: the planner's records of the groups of a proof's first chain
(`OnBytes.Plan.framesOf`), at sizes whose links, links' group, last test's stages and codes are the
full size's written ones, HOLD AT EACH OF THE 25 SWITCHES WHAT THE WRITTEN RECORD OF THAT SWITCH
HOLDS (`tableFullLit`, Johnson/Top/H0/K2Caller/LitRows.lean): the group in front, the samples of the
sending, one tree, the rider.

Why. The law of the code switch at a seated place speaks of the record `rowOf z lo l kept f`
(Johnson/Top/H0/K2Caller/Table.lean) at the planner's own sizes z and record f. What is proved of
records is proved of the 25 written ones. That the two are one was held by evaluation alone. Of the
seven fields that `rowOf` computes, four read f: they are the four clauses here.
  `FrameLite`, `FrameN.lite`, `liteFrom`, `framesFrom_lite`: general in z: four fields of the
  records (the number, the group in front, the members, the group that prices the samples) are a
  function of two numbers of the request's shape, the links' group, the last test's first group, the
  groups and the links.
  `sent_of_mem`: behind the first record what is sent are the members, and nothing rides.
  `reqSampled_noRiders`: where nothing rides, the samples do not read the riders' group.
  `reqGroups_congr`: the groups read of a shape its links, its code's number and its answers alone.
  `liteFull`, `framesOkAt`, `framesOk_all`: at the written values Lean's kernel says yes to the four
  clauses at all 25.
  `lite_written`: at such sizes the four fields of the planner's records are `liteFull`'s.
  `frames_some`: at such sizes neither list is short: the law is idle at none of the 25.
  `frames_written`: the first sentence above.
Limits. A LAW WITH SEVEN PREMISES on z: that the planner's sizes in the goals' scope meet them is
not shown here. The full size alone. Numbers of the planner's record: nothing on the running text of
a block, nothing on the three fields of `rowOf` that read z alone, nothing on soundness or hiding.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Top.H0.K2Caller.Table
import Johnson.Top.H0.K2Caller.LitRows
import Johnson.Desc.K12.Law.Sizes.GroupsFull
import Johnson.Desc.K12.Law.Sizes.TurnsLFull
import Johnson.Desc.K12.Law.Sizes.StagesFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Plan
open OnBytes OnBytes.Params

/-! ## Four fields of the records, general in the sizes -/

/-- Four fields of a record. -/
structure FrameLite where
  l : Nat
  before : GroupSize
  members : List OracleNotice
  sendGroup : GroupSize
  deriving DecidableEq

/-- The four fields of a record. -/
def FrameN.lite (n : FrameN) : FrameLite := ⟨n.l, n.before, n.members, n.sendGroup⟩

/-- `closedGroup` at the links' group as a letter. -/
def closedLite (gL : GroupSize) (g : ReqGroup) (gs : List ReqGroup) : GroupSize :=
  { gL with
    k := g.k, h := g.h,
    slots := 2 ^ clog2 (1 + sumT (((gs.head?.map keptOf).getD []).map (·.shape.mainRows))) }

/-- `membersOf` at the two numbers of the codes as letters. -/
def membersLite (code maskCode l : Nat) (g : ReqGroup) (msgs : List ReqMessage) :
    List OracleNotice :=
  (if 0 < l then [⟨g.target.shape, g.target.leafClass⟩] else []) ++
    (keptOf g).map (fun k => ⟨k.shape, k.leafClass⟩) ++
    (msgs.filter fun m => m.moment == 0).map (fun m => ⟨m.shape, m.leafClass⟩) ++
    [foldMaskNotice (ioppFoldShape ⟨code, maskCode, g.k, g.h⟩ {})]

/-- The four fields from group number l on. -/
def liteFrom (code maskCode : Nat) (gL gLast : GroupSize) :
    Nat → List ReqGroup → List ReqLink → GroupSize → List FrameLite
  | _, [], _, _ => []
  | l, g :: gs, links, before =>
    ⟨l, before, membersLite code maskCode l g ((links.head?.map (·.messages)).getD []),
        if links.head?.isSome then gL else gLast⟩ ::
      (match links.head? with
      | none => []
      | some _ => liteFrom code maskCode gL gLast (l + 1) gs (links.drop 1) (closedLite gL g gs))

/-- The four fields of one record. -/
theorem frameAt_lite (z : ProofSized) (l : Nat) (g : ReqGroup) (gs : List ReqGroup)
    (links : List ReqLink) (open_ : List Nat) (before : GroupSize) :
    (frameAt z l g gs links open_ before).lite =
      ⟨l, before,
        membersLite z.request.code z.request.maskCode l g ((links.head?.map (·.messages)).getD []),
        if links.head?.isSome then z.link.group else z.last.first⟩ := rfl

/-- **The four fields of the planner's records are that function's values.** -/
theorem framesFrom_lite (z : ProofSized) :
    ∀ (gs : List ReqGroup) (l : Nat) (links : List ReqLink) (open_ : List Nat)
      (before : GroupSize),
      (framesFrom z l gs links open_ before).map FrameN.lite =
        liteFrom z.request.code z.request.maskCode z.link.group z.last.first l gs links before
  | [], _, _, _, _ => by
      unfold framesFrom liteFrom
      rfl
  | g :: gs, l, links, open_, before => by
      have ih := framesFrom_lite z gs (l + 1) (links.drop 1) (open_.drop 1) (closedGroup z g gs)
      unfold framesFrom liteFrom
      rw [List.map_cons, frameAt_lite]
      cases links.head? with
      | none => rfl
      | some v => exact congrArg (List.cons _) ih

/-- Behind the first record what is sent are the members, and nothing rides. -/
theorem sent_of_mem (z : ProofSized) :
    ∀ (gs : List ReqGroup) (l : Nat) (links : List ReqLink) (open_ : List Nat)
      (before : GroupSize) (n : FrameN),
      n ∈ framesFrom z l gs links open_ before → n.l ≠ 0 → n.sent = n.members ∧ n.riders = 0
  | [], _, _, _, _, _, h, _ => by
      unfold framesFrom at h
      exact absurd h (List.not_mem_nil)
  | g :: gs, l, links, open_, before, n, h, h0 => by
      unfold framesFrom at h
      rcases List.mem_cons.1 h with rfl | h
      · have hl : (l == 0) = false := beq_eq_false_iff_ne.2 h0
        unfold frameAt
        simp only [hl]
        exact ⟨rfl, rfl⟩
      · cases hk : links.head? with
        | none =>
          simp only [hk] at h
          exact absurd h (List.not_mem_nil)
        | some v =>
          simp only [hk] at h
          exact sent_of_mem z gs _ _ _ _ n h h0

/-- Where nothing rides, the samples do not read the riders' group. -/
theorem reqSampled_noRiders (codes : Codes) (sent : List OracleNotice) (g a a' : GroupSize) :
    reqSampled codes sent g a 0 = reqSampled codes sent g a' 0 := by
  unfold reqSampled
  refine List.map_congr_left fun x hx => ?_
  have hx' := (List.mem_filter.1 hx).1
  rw [zipT_eq] at hx'
  have h1 : x.1 < sent.length - 0 := by
    have := List.mem_range.1 (List.of_mem_zip hx').1
    omega
  simp only [h1, if_true]

end OnBytes.Plan

namespace OnBytes
open Params (ReqShape)

/-- One group reads of a shape its links, its code's number and its answers alone. -/
theorem reqGroupAt_congr {s s' : ReqShape} (h1 : s.link = s'.link) (h2 : s.code = s'.code)
    (h3 : s.answers = s'.answers) (l : Nat) (alive : List ReqAlive) :
    reqGroupAt s l alive = reqGroupAt s' l alive := by
  unfold reqGroupAt
  rw [h1, h2, h3]

theorem reqGroupsFrom_congr {s s' : ReqShape} (h1 : s.link = s'.link) (h2 : s.code = s'.code)
    (h3 : s.answers = s'.answers) :
    ∀ (count l : Nat) (alive : List ReqAlive),
      reqGroupsFrom s count l alive = reqGroupsFrom s' count l alive
  | 0, _, _ => rfl
  | count + 1, l, alive => by
    unfold reqGroupsFrom
    simp only [reqGroupAt_congr h1 h2 h3, reqGroupsFrom_congr h1 h2 h3 count]

/-- **The groups read of a shape its links, its code's number and its answers alone.** -/
theorem reqGroups_congr {s s' : ReqShape} (h1 : s.link = s'.link) (h2 : s.code = s'.code)
    (h3 : s.answers = s'.answers) : reqGroups s = reqGroups s' := by
  rw [reqGroups_eq, reqGroups_eq, h1, reqGroupsFrom_congr h1 h2 h3]

end OnBytes

namespace Johnson.G
open OnBytes OnBytes.Params OnBytes.Plan H2K.Sizes H2K.Member
open VerifiableInference.Desc.First.K2Caller (SwRow tableFullLit)

/-! ## At the written values -/

/- In this namespace, so that its name meets no other file's. -/
deriving instance DecidableEq for SampleSize

/-- The four fields at the written links, the written links' group and the written last stages. -/
def liteFull : List FrameLite :=
  liteFrom 0 0 gLink (szLFull.headD default).g 0 (reqGroups (shapeOfLinks linksFull 1)).toList
    linksFull gLink

theorem liteFull_eq : liteFull =
    liteFrom 0 0 gLink (szLFull.headD default).g 0 (reqGroups (shapeOfLinks linksFull 1)).toList
      linksFull gLink := rfl

/-- The four clauses at switch number i, as a test; and that the record is not the first. -/
def framesOkAt (i : Nat) : Bool :=
  match liteFull[i + 1]?, tableFullLit[i]? with
  | some f, some R =>
    decide (f.l ≠ 0) && decide (f.before = R.g) &&
      decide (reqSampled codesFull2 f.members f.sendGroup f.sendGroup 0 = R.o) &&
      decide (treesOf codesFull2 f.members.toArray = some 1) &&
      decide (((f.members.getLast?).map (·.shape)).getD {} =
        { maskRows := 1, maskCode := 0, answers := 0 })
  | _, _ => false

set_option maxRecDepth 1000000 in
/-- **Lean's kernel says yes at all 25.** -/
theorem framesOk_all : ((List.range 25).all framesOkAt) = true := by decide +kernel

/-- The written list of the last test's stages is not empty: its first group needs no stand-in. -/
theorem szL_first (d d' : StageSize) : (szLFull.headD d).g = (szLFull.headD d').g := rfl

/- Lean compares these names and does not open them. -/
attribute [local irreducible] linksFull gLink szLFull codesFull2 tableFullLit liteFull

set_option maxRecDepth 100000 in
/-- The four fields of the planner's records at such sizes. -/
theorem lite_written (z : ProofSized) (sub : Subproofs) (hlink : z.request.link = linksFull)
    (hcode : z.request.code = 0) (hmask : z.request.maskCode = 0) (hans : z.request.answers = 1)
    (hg : z.link.group = gLink) (hL : z.last.stages = szLFull) :
    (framesOf z sub).map FrameN.lite = liteFull := by
  have hfirst : z.last.first = (szLFull.headD default).g := by
    unfold TestSizes.first
    rw [hL]
    exact szL_first _ _
  have hgr : reqGroups z.request = reqGroups (shapeOfLinks linksFull 1) :=
    reqGroups_congr hlink hcode hans
  rw [liteFull_eq]
  unfold framesOf
  rw [framesFrom_lite, hcode, hmask, hg, hfirst, hgr, hlink]

/-- **Neither list is short**: at such sizes the planner has a record, and the written table one, at
each of the 25 switches: so the law below is idle at none. -/
theorem frames_some (z : ProofSized) (sub : Subproofs) (hlink : z.request.link = linksFull)
    (hcode : z.request.code = 0) (hmask : z.request.maskCode = 0) (hans : z.request.answers = 1)
    (hg : z.link.group = gLink) (hL : z.last.stages = szLFull) :
    ∀ i, i < 25 → ∃ f R, (framesOf z sub)[i + 1]? = some f ∧ tableFullLit[i]? = some R := by
  intro i hi
  have hk : framesOkAt i = true := List.all_eq_true.1 framesOk_all i (List.mem_range.2 hi)
  unfold framesOkAt at hk
  cases hA : liteFull[i + 1]? with
  | none => rw [hA] at hk; cases hk
  | some f' =>
    cases hB : tableFullLit[i]? with
    | none => rw [hA, hB] at hk; cases hk
    | some R =>
      rw [← lite_written z sub hlink hcode hmask hans hg hL, List.getElem?_map] at hA
      obtain ⟨f, hf, -⟩ := Option.map_eq_some_iff.1 hA
      exact ⟨f, R, hf, rfl⟩

set_option maxRecDepth 100000 in
/-- **THE PLANNER's RECORDS AT THE 25 SWITCHES HOLD WHAT THE WRITTEN RECORDS HOLD.** sub is free:
the four clauses read nothing of it. -/
theorem frames_written (z : ProofSized) (sub : Subproofs) (hlink : z.request.link = linksFull)
    (hcode : z.request.code = 0) (hmask : z.request.maskCode = 0) (hans : z.request.answers = 1)
    (hg : z.link.group = gLink) (hL : z.last.stages = szLFull) (hcs : z.codes = codesFull2) :
    ∀ i, i < 25 → ∀ f, (framesOf z sub)[i + 1]? = some f → ∀ R, tableFullLit[i]? = some R →
      f.before = R.g ∧
        reqSampled z.codes f.sent f.sendGroup z.batch.own.first f.riders = R.o ∧
        treesOf z.codes f.sent.toArray = some 1 ∧
        ((f.members.getLast?).map (·.shape)).getD {} =
          { maskRows := 1, maskCode := 0, answers := 0 } := by
  intro i hi f hf R hR
  have hf' : liteFull[i + 1]? = some f.lite := by
    rw [← lite_written z sub hlink hcode hmask hans hg hL, List.getElem?_map, hf]
    rfl
  have hk : framesOkAt i = true := List.all_eq_true.1 framesOk_all i (List.mem_range.2 hi)
  unfold framesOkAt at hk
  rw [hf', hR] at hk
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hk
  obtain ⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩ := hk
  obtain ⟨e1, e2⟩ := sent_of_mem z _ _ _ _ _ f (List.mem_of_getElem? hf) h0
  rw [e1, e2, hcs, reqSampled_noRiders _ _ _ _ f.sendGroup]
  exact ⟨h1, h2, h3, h4⟩

end Johnson.G

#print axioms OnBytes.Plan.frameAt_lite
#print axioms OnBytes.Plan.framesFrom_lite
#print axioms OnBytes.Plan.sent_of_mem
#print axioms OnBytes.Plan.reqSampled_noRiders
#print axioms OnBytes.reqGroupAt_congr
#print axioms OnBytes.reqGroupsFrom_congr
#print axioms OnBytes.reqGroups_congr
#print axioms Johnson.G.liteFull_eq
#print axioms Johnson.G.framesOk_all
#print axioms Johnson.G.szL_first
#print axioms Johnson.G.lite_written
#print axioms Johnson.G.frames_some
#print axioms Johnson.G.frames_written
