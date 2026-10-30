-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Numbers/ProofLinksAtScope.lean: at public files in the goals' scope, five further
fields of the sizes of a proof's chains are closed values: the links' group as solved, the
request's links, its two codes' numbers and its number of answers. UNDER THE PREMISE that the layout
file's group lines, as read, are the typed list. Statements and proofs; no definition.

Why. The half on the frames of the law of the kind "the code switch"
(Johnson/G/SwitchFramesAt.lean: `frames_written`) takes these five as premises, beside the three of
ProofSizesAtScope.lean.

How. `Params.proofSized` lays the request's shape outright: both codes' numbers are 0, the links are
the sub-proofs' links as filled, the number of answers is the lines'. It solves the links' group at
a load and a shape that are functions of the lines, the filled links and the open rows. In scope the
filled links are `linksFull`, a closed term computed from the typed group lines, and there are 25
open rows of 1: that is the first half
of the proof of `H2K.Sizes.last_of_public` (LastAtScope.lean), stated here by itself
(`links_of_public`). The solving at these values is `H2K.Sizes.link_solved`.

Main statements.
  `proofSized_request`, `proofSized_link`: the maker's text as far as these fields go.
  `links_of_public`: the filled links and the open rows, from `PubFull X` and reqFrame's yes at a
    file with the typed group lines.
  `five_sized`: the five fields at the written lines, at `linksFull` and the 25 open rows.
  `five_of_public`: from `PubFull X`, configure's yes and reqFrame's yes at such a file.
  `last_of_plain_groups`, `five_of_plain_groups`, `eight_of_made_groups`: in scope, at the proof
    file's plain road, UNDER A TEST ON Z's OWN LAYOUT FILE, which a program can run: its group
    lines, as read, are the typed list. The last: these five with the three of
    ProofSizesAtPlain.lean and the last test's stages.
  `groups_of_closed`: in scope that test follows from the closed premise
    `H2K.Sizes.LayoutGroupsAre`.
  `five_of_plain`, `five_of_made`, `eight_of_made`: so the same under that closed premise.

Limits. ALL FIVE STAND UNDER THE PREMISE ON THE LAYOUT FILE, whose closed form is proved nowhere.
Nothing on `request.atStart` or `request.last`. Nothing on the frames. Nothing on soundness.

-/
import Johnson.Goal.Numbers.ProofSizesAtPlain

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifierAndGoals.Sizes
open OnBytes OnBytes.Params OnBytes.Model OnBytes.Model.Verify OnBytes.Model.Stages OnBytes.Tie
open VerifiableInference.PlanWritten (publicOfO)
open H2K.Sizes H2K.Member Lk6.AtPlan Johnson.G

/-! ## 1. The maker's text -/

/-- `proofSized` lays four fields of the request's shape outright. -/
theorem proofSized_request {l : Lines} {sub : Subproofs} {z : ProofSized}
    (h : proofSized l sub = some z) :
    z.request.code = 0 ∧ z.request.maskCode = 0 ∧ z.request.link = fillLinks sub.links ∧
      z.request.answers = l.answers := by
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
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- The links' group in what `proofSized` returns is what `solveGroup` returns, every argument
named. -/
theorem proofSized_link {l : Lines} {sub : Subproofs} {z : ProofSized}
    (h : proofSized l sub = some z) :
    solveGroup (settingOf l) .request
      (linkLoadIn l (fillLinks sub.links) sub.openRows) id
      (linkShapeIn l (fillLinks sub.links) sub.openRows) = some z.link := by
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
  exact hl

/-! ## 2. At the written lines and the typed links -/

/-- **The five fields.** -/
theorem five_sized {sub : Subproofs} {z : ProofSized} (h : proofSized recordLines sub = some z)
    (h1 : fillLinks sub.links = linksFull) (h2 : sub.openRows = List.replicate 25 1) :
    z.link = ⟨gLink, 219⟩ ∧ z.request.link = linksFull ∧ z.request.code = 0 ∧
      z.request.maskCode = 0 ∧ z.request.answers = 1 := by
  obtain ⟨r1, r2, r3, r4⟩ := proofSized_request h
  have hl := proofSized_link h
  rw [h1, h2, linkShape_full, linkLoad_full] at hl
  exact ⟨Option.some.inj (hl.symm.trans link_solved), r3.trans h1, r1, r2, r4⟩

/-! ## 3. From configure's yes -/

section
variable {X : Public} (hP0 : PubFull X) {shapes : Shapes} {rl : List ReqLink}
  (he : shapes.sub = subproofsWith X rl) {declared : Array Stages.FrameLink}
  {file : Plan.LayoutLines} {lay' : ReqLayout}
  (hr : Plan.reqFrame declared file X.P.frame.answers = some (rl, lay'))
  (hn0 : rl.length = (if X.p4 then 2 else 1) * X.NGr + 1) (hg : file.groups = groupsFull)
include hP0 he hr hn0 hg

/-- **The filled links and the open rows.** -/
theorem links_of_public :
    fillLinks shapes.sub.links = linksFull ∧ shapes.sub.openRows = List.replicate 25 1 := by
  obtain ⟨hfr, _, h4, hN⟩ := hP0
  have hn : rl.length = 25 := by simp [hn0, h4, hN]
  have e1 := reqFrame_links hr
  rw [hfr, hg] at e1
  have e2 : declared.size = 25 := by
    have := linksOfGroups_length declared.size recordLines.answers groupsFull
    rw [← e1, hn] at this
    exact this.symm
  rw [e2] at e1
  refine ⟨?_, ?_⟩
  · rw [he]
    exact congrArg (fun l => fillLinks (withReply l)) e1
  · rw [he]
    show List.replicate rl.length 1 = _
    rw [hn]

/-- **The five fields, from configure's yes.** -/
theorem five_of_public {cfg : ByteArray} {bits : Nat} {made : Configured}
    (hc : configure X.P.frame shapes cfg bits = .ok made) :
    made.sized.proof.link = ⟨gLink, 219⟩ ∧ made.sized.proof.request.link = linksFull ∧
      made.sized.proof.request.code = 0 ∧ made.sized.proof.request.maskCode = 0 ∧
      made.sized.proof.request.answers = 1 := by
  obtain ⟨h1, h2⟩ := links_of_public hP0 he hr hn0 hg
  have hP := (configure_proof_sizes hc).1
  rw [hP0.frame] at hP
  exact five_sized hP h1 h2

end

/-! ## 4. At the scope, at the proof file's plain road -/

/-- In scope the test on Z's own layout file follows from the closed premise. -/
theorem groups_of_closed {Z : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Z = true) (hG : LayoutGroupsAre) :
    (Plan.layoutRead Z.lay).map (·.groups) = some groupsFull := by
  rw [(Johnson.G.ScopeLines.inScope_files hZ).2]
  exact hG

/-- **The last test's stages, under the test on Z's own layout file.** -/
theorem last_of_plain_groups {o : VerifierAndGoals.SecondHashFunctionType} {Z : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Z = true)
    {p : Verify.Planned} (hp : ProofFile.Plain.planned o Z.pol Z.KL (some Z.lay) = .ok p)
    (hg0 : (Plan.layoutRead Z.lay).map (·.groups) = some groupsFull) :
    p.chains.made.sized.proof.last.stages = szLFull := by
  obtain ⟨X, shapes, rl, lay', declared, file, hX, hc, he, hr, hn0, hf⟩ := plain_parts hp
  rw [hf] at hg0
  exact last_of_public (publicO_at_scope hZ hX) hc he hr hn0 (Option.some.inj hg0)

/-- **The five fields, under the test on Z's own layout file.** -/
theorem five_of_plain_groups {o : VerifierAndGoals.SecondHashFunctionType} {Z : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Z = true)
    {p : Verify.Planned} (hp : ProofFile.Plain.planned o Z.pol Z.KL (some Z.lay) = .ok p)
    (hg0 : (Plan.layoutRead Z.lay).map (·.groups) = some groupsFull) :
    p.chains.made.sized.proof.link = ⟨gLink, 219⟩ ∧
      p.chains.made.sized.proof.request.link = linksFull ∧
      p.chains.made.sized.proof.request.code = 0 ∧
      p.chains.made.sized.proof.request.maskCode = 0 ∧
      p.chains.made.sized.proof.request.answers = 1 := by
  obtain ⟨X, shapes, rl, lay', declared, file, hX, hc, he, hr, hn0, hf⟩ := plain_parts hp
  rw [hf] at hg0
  exact five_of_public (publicO_at_scope hZ hX) he hr hn0 (Option.some.inj hg0) hc

/-- **The five fields, under the closed premise.** -/
theorem five_of_plain {o : VerifierAndGoals.SecondHashFunctionType} {Z : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Z = true)
    {p : Verify.Planned} (hp : ProofFile.Plain.planned o Z.pol Z.KL (some Z.lay) = .ok p)
    (hG : LayoutGroupsAre) :
    p.chains.made.sized.proof.link = ⟨gLink, 219⟩ ∧
      p.chains.made.sized.proof.request.link = linksFull ∧
      p.chains.made.sized.proof.request.code = 0 ∧
      p.chains.made.sized.proof.request.maskCode = 0 ∧
      p.chains.made.sized.proof.request.answers = 1 :=
  five_of_plain_groups hZ hp (groups_of_closed hZ hG)

/-- **All that the two halves of the row ask of the sizes, under the test on Z's own layout
file.** -/
theorem eight_of_made_groups {o : VerifierAndGoals.SecondHashFunctionType} {Z : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Z = true)
    {m : Johnson.G.OfPlan.Made} (h : ProofFile.PlainG.madeOf o Z.pol Z.lay Z.KL = .ok m)
    (hg0 : (Plan.layoutRead Z.lay).map (·.groups) = some groupsFull) :
    m.p.chains.made.sized.proof.set = setLit ∧ m.p.chains.made.sized.proof.codes = codesFull2 ∧
      m.p.chains.made.sized.proof.batch.own.first =
        { main := ⟨22, 262144, 3571, true⟩, mask := ⟨13, 256, 55, true⟩, k := 5, h := 1,
          slots := 1, rule := .johnson, m := 159 } ∧
      m.p.chains.made.sized.proof.last.stages = szLFull ∧
      m.p.chains.made.sized.proof.link = ⟨gLink, 219⟩ ∧
      m.p.chains.made.sized.proof.request.link = linksFull ∧
      m.p.chains.made.sized.proof.request.code = 0 ∧
      m.p.chains.made.sized.proof.request.maskCode = 0 ∧
      m.p.chains.made.sized.proof.request.answers = 1 := by
  have hL := last_of_plain_groups hZ (made_planned h) hg0
  obtain ⟨a, b, c⟩ := sizes_of_made hZ h hL
  exact ⟨a, b, c, hL, five_of_plain_groups hZ (made_planned h) hg0⟩

section
variable {o : VerifierAndGoals.SecondHashFunctionType} {Z : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Z = true)
  {m : Johnson.G.OfPlan.Made} (h : ProofFile.PlainG.madeOf o Z.pol Z.lay Z.KL = .ok m)
  (hG : LayoutGroupsAre)
include hZ h hG

theorem five_of_made :
    m.p.chains.made.sized.proof.link = ⟨gLink, 219⟩ ∧
      m.p.chains.made.sized.proof.request.link = linksFull ∧
      m.p.chains.made.sized.proof.request.code = 0 ∧
      m.p.chains.made.sized.proof.request.maskCode = 0 ∧
      m.p.chains.made.sized.proof.request.answers = 1 :=
  five_of_plain hZ (made_planned h) hG

/-- **All that the two halves of the row ask of the sizes, under the one closed premise.** -/
theorem eight_of_made :
    m.p.chains.made.sized.proof.set = setLit ∧ m.p.chains.made.sized.proof.codes = codesFull2 ∧
      m.p.chains.made.sized.proof.batch.own.first =
        { main := ⟨22, 262144, 3571, true⟩, mask := ⟨13, 256, 55, true⟩, k := 5, h := 1,
          slots := 1, rule := .johnson, m := 159 } ∧
      m.p.chains.made.sized.proof.last.stages = szLFull ∧
      m.p.chains.made.sized.proof.link = ⟨gLink, 219⟩ ∧
      m.p.chains.made.sized.proof.request.link = linksFull ∧
      m.p.chains.made.sized.proof.request.code = 0 ∧
      m.p.chains.made.sized.proof.request.maskCode = 0 ∧
      m.p.chains.made.sized.proof.request.answers = 1 :=
  eight_of_made_groups hZ h (groups_of_closed hZ hG)

end

end VerifierAndGoals.Sizes

#print axioms VerifierAndGoals.Sizes.proofSized_request
#print axioms VerifierAndGoals.Sizes.proofSized_link
#print axioms VerifierAndGoals.Sizes.five_sized
#print axioms VerifierAndGoals.Sizes.links_of_public
#print axioms VerifierAndGoals.Sizes.five_of_public
#print axioms VerifierAndGoals.Sizes.groups_of_closed
#print axioms VerifierAndGoals.Sizes.last_of_plain_groups
#print axioms VerifierAndGoals.Sizes.five_of_plain_groups
#print axioms VerifierAndGoals.Sizes.eight_of_made_groups
#print axioms VerifierAndGoals.Sizes.five_of_plain
#print axioms VerifierAndGoals.Sizes.five_of_made
#print axioms VerifierAndGoals.Sizes.eight_of_made
