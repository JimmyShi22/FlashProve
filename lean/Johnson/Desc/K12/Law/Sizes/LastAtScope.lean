-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/Sizes/LastAtScope.lean: at every three public files in the scope of the goals,
the sized stages of the first chain's last proximity test in what the program computes are the typed
list szLFull, UNDER ONE CLOSED PREMISE on the layout file.

Params.proofSized sizes the links' group, and from it the last test, at the parameter file's first
32 lines and at seven numbers of a request's links. The links are made by Plan.reqFrame; by
LinksOfLayout.lean they are a function of the number of declared links, the number of answers and
the layout file's group lines. The scope (VerifierAndGoals.InScope) fixes the layout file. So the eight free
numbers and the scale file do not reach this list either.
Main names:
  `LayoutGroupsAre`: THE PREMISE: Plan.layoutRead at the stored full-size layout file
    (VerifierAndGoals.storedPublicFiles.lay) returns, and its group lines are the typed list groupsFull. It is one closed
    statement: no file Z occurs in it.
  `linkShapeIn`, `linkLoadIn`, `lastKIn`, `proofSized_last`: proofSized's text down to the last
    test's stages, every argument named.
  `last_sized`: at the written lines and the typed links the stages are szLFull.
  `last_of_public`: THE STATEMENT, from `PubFull X` (StageSizesAtScope.lean), configure's yes and
    reqFrame's yes at a file with the typed group lines: no planner's name, no maker of the public
    part, no scope occur in it. `last_of_configure`: at what publicOf returns at files in scope.
  `last_at_groups`: from `planned`, under the same test on Z's own layout file, which a program can
    run at Z.
  `last_at_scope`, `last_at_made`: from `planned` and from `madeOf`, under the closed premise.
Limits: THE PREMISE IS PROVED IN AtFullSide/LayoutRead/, in pieces. By one evaluation in Lean's
kernel it was not had: tried on the bytes of the first 100 lines of that text (4,016 of 224,975
bytes), the kernel stopped with "deep recursion" under the default stack; on shorter pieces, under a
larger stack, its time grew faster than the square of the length; the whole text was not tried. One
direction: from a program that returns; that Model.Verify.planned or madeOf returns at any file in
scope is not shown. Of a place of the kind K12 only the stages are pinned. Nothing on soundness.
Nothing on hiding.
-/
import Johnson.Desc.K12.Law.Sizes.StageSizesAtScope
import Johnson.Desc.K12.Law.Sizes.TurnsLFull
import Johnson.Desc.K12.Law.Sizes.GroupsFull
import OnBytes.Tie.Pv.Lookup.Ends.FoPlannedCut
import Johnson.Goal.Scope.ScopeLines

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K.Sizes
open OnBytes OnBytes.Params OnBytes.Model OnBytes.Model.Verify
open H2K.Member Lk6.AtPlan

/-- **The premise**: the group lines of the stored full-size layout file, as read, are the typed
lines. -/
def LayoutGroupsAre : Prop :=
  (Plan.layoutRead VerifierAndGoals.storedPublicFiles.lay).map (·.groups) = some groupsFull

/-! ## 1. proofSized's text down to the last test -/

/-- The load of the chain of links. links: as filled. -/
def loadIn (l : Lines) (links : List ReqLink) (openRows : List Nat) : ReqLoad :=
  reqLoad (shapeOfLinks links l.answers) l.link.logL l.link.maskLogL openRows

/-- The shape from which the links' group is solved. -/
def linkShapeIn (l : Lines) (links : List ReqLink) (openRows : List Nat) : GroupSize :=
  { shapeOf l.link (loadIn l links openRows).k false with slots := (loadIn l links openRows).slots }

/-- The load for which it is solved. -/
def linkLoadIn (l : Lines) (links : List ReqLink) (openRows : List Nat) : GroupLoad :=
  { cubeBits :=
      max (stageCubeBits (linkShapeIn l links openRows)) (loadIn l links openRows).cubeBits
    messages := links.foldl (fun m x => max m (2 * x.messages.length + 2)) 8
    batchedRows := (loadIn l links openRows).rows + (loadIn l links openRows).rowsADraw * 4096 }

/-- The row variables of the last group. -/
def lastKIn (l : Lines) (links : List ReqLink) : Nat :=
  ((reqGroups (shapeOfLinks links l.answers)).toList.getLast?.map (·.k)).getD 1

/-- **What proofSized returns holds the stages of the last test, every argument named.** -/
theorem proofSized_last {l : Lines} {sub : Subproofs} {z : ProofSized}
    (h : proofSized l sub = some z) :
    ∃ link : Solved,
      solveGroup (settingOf l) .request
        (linkLoadIn l (fillLinks sub.links) sub.openRows) id
        (linkShapeIn l (fillLinks sub.links) sub.openRows) = some link ∧
      solveStages (settingOf l) .request
        { link.group with k := lastKIn l (fillLinks sub.links), slots := 1,
                          main := { link.group.main with overE := true } }
        link.t l.link.stages = some z.last.stages := by
  unfold proofSized at h
  extract_lets at h
  replace h := opt_guard h
  obtain ⟨link, hl, h⟩ := opt_bind h
  obtain ⟨stages, hs, h⟩ := opt_bind h
  obtain ⟨T, _, h⟩ := opt_bind h
  split at h
  replace h := opt_guard h
  obtain ⟨⟨batch, codes2⟩, _, h⟩ := opt_bind h
  cases h
  exact ⟨link, hl, hs⟩

/-! ## 2. At the written lines and the typed links -/

theorem linkShape_full : linkShapeIn recordLines linksFull (List.replicate 25 1) =
    linkShapeFull := by
  unfold linkShapeIn loadIn
  rw [show recordLines.answers = 1 from rfl, show recordLines.link.logL = 22 from rfl,
    show recordLines.link.maskLogL = 13 from rfl, load_full]
  decide +kernel

theorem linkLoad_full : linkLoadIn recordLines linksFull (List.replicate 25 1) =
    linkLoadFull := by
  unfold linkLoadIn
  rw [linkShape_full, messages_full]
  unfold loadIn
  rw [show recordLines.answers = 1 from rfl, show recordLines.link.logL = 22 from rfl,
    show recordLines.link.maskLogL = 13 from rfl, load_full]
  decide +kernel

theorem lastK_at : lastKIn recordLines linksFull = 1 := lastK_full

/-- **At the written lines and the typed links the last test's stages are the typed list.** -/
theorem last_sized {sub : Subproofs} {z : ProofSized} (h : proofSized recordLines sub = some z)
    (h1 : fillLinks sub.links = linksFull) (h2 : sub.openRows = List.replicate 25 1) :
    z.last.stages = szLFull := by
  obtain ⟨link, hl, hs⟩ := proofSized_last h
  rw [h1, h2, linkShape_full, linkLoad_full] at hl
  obtain rfl : link = ⟨gLink, 219⟩ := Option.some.inj (hl.symm.trans link_solved)
  rw [h1, lastK_at] at hs
  exact Option.some.inj (hs.symm.trans L_stages)

/-! ## 3. At the scope -/

/-- **From configure's yes at a public part as at the full size**, where the links are what reqFrame
returns at a file whose group lines are the typed lines, and are as many as shapesWith asks. No
planner's name, no maker of the public part and no scope occur. -/
theorem last_of_public {X : Public} (hP0 : PubFull X) {shapes : Shapes}
    {cfg : ByteArray} {bits : Nat} {made : Configured}
    (hc : configure X.P.frame shapes cfg bits = .ok made) {rl : List ReqLink}
    (he : shapes.sub = subproofsWith X rl) {declared : Array Stages.FrameLink}
    {file : Plan.LayoutLines} {lay' : ReqLayout}
    (hr : Plan.reqFrame declared file X.P.frame.answers = some (rl, lay'))
    (hn0 : rl.length = (if X.p4 then 2 else 1) * X.NGr + 1) (hg : file.groups = groupsFull) :
    made.sized.proof.last.stages = szLFull := by
  obtain ⟨hfr, _, h4, hN⟩ := hP0
  have hn : rl.length = 25 := by simp [hn0, h4, hN]
  have e1 := reqFrame_links hr
  rw [hfr, hg] at e1
  have e2 : declared.size = 25 := by
    have := linksOfGroups_length declared.size recordLines.answers groupsFull
    rw [← e1, hn] at this
    exact this.symm
  rw [e2] at e1
  have hP := (configure_proof_sizes hc).1
  rw [hfr] at hP
  refine last_sized hP ?_ ?_
  · rw [he]
    exact congrArg (fun l => fillLinks (withReply l)) e1
  · rw [he]
    show List.replicate rl.length 1 = _
    rw [hn]

/-- The same where the public part is what publicOf returns at files in scope. -/
theorem last_of_configure {Z : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Z = true)
    {lay : Option ByteArray} {X : Public} (hX : publicOf Z.pol Z.KL lay = .ok X) {shapes : Shapes}
    {cfg : ByteArray} {bits : Nat} {made : Configured}
    (hc : configure X.P.frame shapes cfg bits = .ok made) {rl : List ReqLink}
    (he : shapes.sub = subproofsWith X rl) {declared : Array Stages.FrameLink}
    {file : Plan.LayoutLines} {lay' : ReqLayout}
    (hr : Plan.reqFrame declared file X.P.frame.answers = some (rl, lay'))
    (hn0 : rl.length = (if X.p4 then 2 else 1) * X.NGr + 1) (hg : file.groups = groupsFull) :
    made.sized.proof.last.stages = szLFull :=
  last_of_public (public_at_scope hZ hX) hc he hr hn0 hg

/-- **At three public files in the goals' scope whose layout file's group lines, as read, are the
typed lines, the stages of the first chain's last test are the typed list.** The premise hg0 is a
test on Z's own layout file, which a program can run. -/
theorem last_at_groups {Z : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Z = true)
    (hg0 : (Plan.layoutRead Z.lay).map (·.groups) = some groupsFull)
    {p : Verify.Planned} (hp : planned Z.pol Z.KL (some Z.lay) = .ok p) :
    p.chains.made.sized.proof.last.stages = szLFull := by
  obtain ⟨links, shapes, _, _, _, _, _, hX, _, hs, _, _, hc, _, _, _, _⟩ := planned_parts hp
  obtain ⟨rl, lay, _, declared, file, _, _, hf, hr, hw⟩ := Fo.shapesOf_cut hs
  obtain ⟨hn0, he⟩ := shapesWith_count hw
  have hg : file.groups = groupsFull := by
    have e : Plan.layoutRead Z.lay = some file := hf
    rw [e] at hg0
    exact Option.some.inj hg0
  exact last_of_configure hZ hX hc he hr hn0 hg

/-- **Under the closed premise: at every three public files in the goals' scope.** The scope fixes
the layout file, so the closed premise gives hg0 of last_at_groups at every Z. -/
theorem last_at_scope (hG : LayoutGroupsAre) {Z : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Z = true)
    {p : Verify.Planned} (hp : planned Z.pol Z.KL (some Z.lay) = .ok p) :
    p.chains.made.sized.proof.last.stages = szLFull := by
  refine last_at_groups hZ ?_ hp
  rw [(Johnson.G.ScopeLines.inScope_files hZ).2]
  exact hG

/-- The same from the record that Johnson.G.OfPlan.madeOf makes of the three files. -/
theorem last_at_made (hG : LayoutGroupsAre) {Z : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Z = true)
    {m : Johnson.G.OfPlan.Made} (h : Johnson.G.OfPlan.madeOf Z.pol Z.lay Z.KL = .ok m) :
    m.p.chains.made.sized.proof.last.stages = szLFull :=
  last_at_scope hG hZ (madeOf_planned h)

end H2K.Sizes

#print axioms H2K.Sizes.proofSized_last
#print axioms H2K.Sizes.last_sized
#print axioms H2K.Sizes.last_of_public
#print axioms H2K.Sizes.last_of_configure
#print axioms H2K.Sizes.last_at_groups
#print axioms H2K.Sizes.last_at_scope
#print axioms H2K.Sizes.last_at_made
