-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Entry/Makers/Binders.lean: TWENTY-EIGHT HYPOTHESES OF THE JOIN OF THE FIRST CHAIN'S
ROWS (`ProofFile.Sk.Full.decl_first_at_rows`, Johnson/Desc/ProofFile/Law/Skel/Full/FirstRows.lean), EACH
IN THAT THEOREM'S OWN LETTERS, from fewer and plainer ones. Calls alone.

That theorem says that the proof file's description returns at the full size and declares the
written rounds in its first chain, under some fifty hypotheses on the public part Z and the blank
ground G. Here twenty-eight of them are struck. What is left in their place:
  hS hR hZ hG   in the goals' scope, the files read, the public part Z at the second hash function,
                the blank ground G: the join's own first four
  hX hm         the public values X₀ and the planner's answer m are what their makers return
  hF hz hpl     of m: the first chain's parameters, the sized shapes and the proof file's three
                plans are the written ones
  u₃ u₄         of m: the declared rounds are the written ones; the trees are made
  h4 hN g0 a0   of X₀: attention is covered; twelve groups; twelve plans for layers; twelve for
                attention
  ha hw hK      of X₀: two closed tests accept: `armsB` (Johnson/LPFE1R/RowsAtArms.lean) and
                `k8AsksWB` (Johnson/AtFull/Desc/Lots/K8GroundOf.lean); the last number of columns
                that the head reads of the last group's plan is the border's

  `Struck Z G`: the twenty-eight, as one structure, under the join's names for them:
    cW e9 (the table of stretches; the declared rounds' entries) · l0 g0 a0 p0 d0 m0 (the links'
    frames) · c1 s1 l1 g1 (the commitments) · z2 u1 u2 t3 t4 t5 b2 (the switch) · m5 (attention) ·
    n8 t8 (the smallness test) · g9 t9 (the batching) · r13 c13 l13 g11 (the weights' opening).
  **`struck`**: the structure, from the hypotheses above.
How. Seventeen are projections of the value that the public part's maker returns
(`rows_of_written`, `fields_of_written`, Johnson/AtFull/Pub/FieldsOfWritten.lean) with ties between
written constants; the terms are those by which Johnson/AtFull/Rounds/SecondRowsPaid.lean shows the
same hypotheses of the second rows' join. The other eleven: four by this folder's laws (d0 m0 t9
g11) · two by joins of the smallness test's lot (n8 t8:
Johnson/AtFull/Desc/Lots/K8GroundPaid.lean) · one by a law in scope (l0: `views_in_scope`,
Johnson/AtFull/Desc/Lots/LinksInScope.lean) · FOUR ARE `struck`'S OWN PREMISES, CARRIED FROM X₀ TO
Z.p.X AND NOT SHOWN HERE (g0 a0 p0 b2). So `struck` shows twenty-four and moves four;
Johnson/AtFull/Entry/Makers/AtZFull.lean shows these four as well.

Limits. A JOINING: what is left is shown at no files here. n8 rests on hw, whose accept says little
(Johnson/AtFull/Entry/Makers/K8AsksAtMakers.lean, Limits). Whether the join's other hypotheses can
be met together with these is not shown here. At the second hash function alone. The full size
alone. Nothing on soundness.

-/
import Johnson.AtFull.Entry.Makers.TestsWhere
import Johnson.AtFull.Entry.Makers.SameAtBuilt
import Johnson.AtFull.Entry.Makers.FirstShape
import Johnson.AtFull.Desc.Lots.K8GroundPaid
import Johnson.AtFull.Pub.FieldsOfWritten
import Johnson.AtFull.Rounds.EntriesW
import Johnson.IMR.SendsPinned
import Johnson.Desc.Ok.PlanWritten.SizedTestLaws
import Johnson.Road.K4.K4PlanTied
import Johnson.Desc.K1.Law.FirstMakeFacts
import Johnson.Desc.ProofFile.Law.Skel.Full.Ask

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Entry

open OnBytes OnBytes.Model
open ProofFile (pubPlain blankBy pureRoad toldOf Root)
open ProofFile.Law (blankM)
open VerifiableInference.PlanWritten (publicOfO proofSizedFull FirstWritten)
open VerifiableInference.PlanWritten.Joined (writtenSized)
open VerifiableInference.Number.ByRuns (proofThree)
open VerifiableInference.Desc.Key (madeAt fixedDigest)
open Johnson.G.OfPlan (Made declPOf)
open Johnson.AtFull.ProofRows (declProofFull)
open Johnson.AtFull.Pub (rows_of_written fields_of_written)

/-- Twenty-eight hypotheses of the join of the first chain's rows, in its own letters. A list under
one name: no goal. -/
structure Struck (Z : ProofFile.Pub) (G : ProofFile.Ground) : Prop where
  cW : Z.cuts = Johnson.AtFull.Cut.cutWritten
  e9 : Z.D.1.map (·.entry) = Johnson.AtFull.Desc.Lots.esW
  l0 : Z.p.built.links.toList.map P1L20.Row.viewL = P1L20.Row.viewW
  g0 : Z.p.X.G.size = 12
  a0 : Z.p.X.A.size = 12
  p0 : Z.p.X.layers.y.h.p4 = true
  d0 : (Z.first.shape.link.map (·.plain)).take 24 = P1L20.Row.plainW
  m0 : ∀ l < 25, P1L20.Row.sameB Z.p.built.links Z.p.X l = true
  c1 : G.first.codes = Johnson.G.codesFull2
  s1 : G.first.shape = proofSizedFull.request
  l1 : G.first.layout = Johnson.G.layoutFull
  g1 : Z.P.samples = 1
  z2 : Z.p.chains.made.sized.proof = proofSizedFull
  u1 : proofSizedFull.request = Z.first.shape
  u2 : proofSizedFull.codes = Z.first.codes
  t3 : Z.s₀.st.codes = proofSizedFull.codes
  t4 : Z.s₀.check.frame.shape = proofSizedFull.request
  t5 : proofSizedFull.set.samples = Z.P.samples
  b2 : Z.p.X.owner.tl.kTX.back? = some (OnBytes.Model.Verify.borderOf Z.p.X.y).kxb
  m5 : Z.p.chains.made.proof = [proofThree.A.plan, proofThree.B.plan, proofThree.C.plan]
  n8 : P1K8L.k8GroundB G = true
  t8 : P1K8L.k8TritsB G = true
  g9 : Z.s₀.check.frame.groups = Johnson.AtFull.Desc.Lots.groupsW
  t9 : ∀ l ∈ ProofFile.Sk.Full.lsW, (VerifiableInference.Desc.K9.testsWhere Z.p.X l 0).isSome =
    Johnson.AtFull.Desc.Lots.twW l
  r13 : Z.first.pendingRows = 13
  c13 : Z.first.codes = proofSizedFull.codes
  l13 : Z.first.lin = proofSizedFull.batch.shape
  g11 : VerifiableInference.Desc.K1.ownGroup Z.first = 31

/-- **The twenty-eight, from the scope, the makers' returns, five facts on the planner's answer and
seven on the public values.** -/
theorem struck {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {Z : ProofFile.Pub}
    {G : ProofFile.Ground} {X₀ : Verify.Public} {m : Made} {told : List Root × List Root × List Root}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (hZ : pubPlain OnBytes.secondHashFunction P.pol lay P.KL = .ok Z)
    (hG : blankBy pureRoad.links Z = some G)
    (hX : publicOfO OnBytes.secondHashFunction P.pol P.KL (some lay) = .ok X₀)
    (hm : madeAt X₀ lay fixedDigest = .ok m)
    (hF : FirstWritten m.p.chains.proof.first)
    (hz : m.p.chains.made.sized = writtenSized)
    (hpl : m.p.chains.made.proof = [proofThree.A.plan, proofThree.B.plan, proofThree.C.plan])
    (u₃ : declPOf (blankM m) = .ok declProofFull) (u₄ : toldOf (blankM m) = .ok told)
    (h4 : X₀.p4 = true) (hN : X₀.NGr = 12) (g0 : X₀.G.size = 12) (a0 : X₀.A.size = 12)
    (ha : VerifiableInference.Desc.LinkJoin.armsB X₀ = true) (hw : P1K8L.k8AsksWB X₀ = true)
    (hK : X₀.owner.tl.kTX.back? = some (OnBytes.Model.Verify.borderOf X₀.y).kxb) :
    Struck Z G := by
  obtain ⟨⟨f1, f2, f3, f4, -, f6⟩, r2, -, r4, r5, r6, r7, r8, r9⟩ :=
    rows_of_written hX hm hF hz hpl u₃ u₄ hZ
  obtain ⟨-, eX, -, -, -, -, eD, -, -, -⟩ := fields_of_written hX hm hF hz hpl u₃ u₄ hZ
  have eF := ProofFile.Law.blankBy_first hG
  rw [← eX] at h4 hN g0 a0 ha hw hK
  exact
    { cW := r5
      e9 := Johnson.AtFull.Rounds.entries_at eD
      l0 := Johnson.AtFull.Lots.LinksScope.views_in_scope hS hR hZ
      g0 := g0
      a0 := a0
      p0 := h4
      d0 := plain_of_shape f3.symm
      m0 := fun l _ => same_of_pub hZ l
      c1 := by rw [eF, f1]; exact VerifiableInference.PlanWritten.codes_written
      s1 := by rw [eF]; exact f3
      l1 := by rw [eF]; exact f6
      g1 := r6.trans request_answers
      z2 := r4
      u1 := f3.symm
      u2 := f1.symm
      t3 := r7
      t4 := r8
      t5 := IM.samples_written.trans r6.symm
      b2 := hK
      m5 := r2
      n8 := P1K8L.k8GroundB_of_arms hS hR hZ hG h4 hN ha a0 hw
      t8 := P1K8L.k8TritsB_of_arms hS hR hZ hG h4 hN ha a0
      g9 := r9.trans (congrArg OnBytes.reqGroups OnBytes.Road.K4.shape_one.symm)
      t9 := fun l _ => tests_where_all h4 hN g0 a0 l
      r13 := f4
      c13 := f1
      l13 := f2
      g11 := ownGroup_of_shape f3.symm }

end Johnson.AtFull.Entry

#print axioms Johnson.AtFull.Entry.struck
