-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/SeatsNamed.lean: SEATS OF QUIET MEMBERS, STATED WITH EVERY STEP ON SHAPES NAMED
AND EVERY PARAMETER OF SUCH A STEP TIED TO A VALUE. Why so: a statement in which a step, or a
parameter of one, stands under "there is" and is tied to nothing is also met by a step that always
refuses, and nobody can evaluate it. Here each is a term in the head's own letters: the plan's entry
of the link (Zp.p.built.links[l]), the public record's plan of the group (Zp.p.X.A | Zp.p.X.G), and
the base that the proof file's seat makes (ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp)). A
joining of laws; nothing is evaluated.

  `attPar Y p l`, `layPar W Y hp l`: the frame's letters at an attention link and at a layers' link,
    as the library's framesOf lays them.
  **`row_att`**, **`row_lay`**: which row of the frame stands at a link of that sort: its "opened"
    and "cleared" as named texts at these letters; its test on the plan paid.
  **`cleared_att_named`**: the member "link l: cleared" at an attention link: carries and returns at
    clearAttG (pubOf Y) p.nLin.
  **`opened_att_named`**, **`opened_lay_named`**: the member at the first place of a link l (0 < l <
    24): its decision is "the lot's sub-protocol, then openAtt | openLay at these letters", both
    ways; and the test on the plan that openAtt_returns | openLay_returns ask is paid. (Link 0:
    another file's.)
  **`behind_named`**, **`layers_named`**: "behind the batching": "carries" and "returns", each
    stated apart. The smallness test's numbers are ProofFile.k8ParW Zp Bs.G₀ Xl m; the link's own tests
    behind the adding are the named tests gTw w (on the shape) and vTw w (on values) of
    Johnson/Desc/First/Batch/Shape/TestsNamed.lean at w := K9.testsWhere Zp.p.X m 0, tied by the
    library's IM.k9_of; at the layers' links the free slot's test is asked at the plan's own number
    of slots in use (hp.used, hp the plan of group g, written Bs.G₀.W.G[g]?).
  `link_named`: what the two above share: the link, its tests' text, its order, the seated K8.whole.
  `freeVH`, `freeRunH` (`freeV_eq`, `freeRun_eq`): the free slot's test and run at the plan alone.

Limits. In opened_…_named the lot's own sub-protocol b' stands under "there is", tied by its place
(1, l, 1, k) and by lying among the blocks that SOME lot of ProofFile.onlineFirstChainBlockTables Zp lays at Bs.G₀; that no
two such blocks share a place is not stated; its step on shapes is another kind's and is not here.
Their second half is the text openAtt | openLay, no step on shapes; the member is given by
L.hear[0]?, with no number in the flat list; neither has a caller (SwitchAtHead.lean states that
member anew).

In link_named the seated block's name and place stand under "there is" and are tied to nothing,
though the proof knows both: whether that member's decision is guarded (Block.guarded,
Johnson/Desc/SeatGuard.lean, decides by the place) does not follow from its last clause. So a yes of
that member does not give that the reply was kept.

Of "cleared" the twelve attention links alone stand here. The tests on values (vTw w, valsS, freeVH)
stay premises of the "returns" halves. That a step returns at a shape that the chain reaches is not
shown. The first place of link 0 and of the head's link (l = 24) is not here. UNDER THE HEAD: that
it has a member is shown in scope, where the reader returns and `protocolDataWellFormed` accepts (`head_of_live`,
Johnson/P5J/HeadOfLive.lean); that these three hold together, at two named sets of public files, in
a side library. At the earlier hash OnBytes.secondHashFunction. Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.OpenedAtHead
import Johnson.AtFull.Shape.BehindLayersAtHead
import Johnson.Desc.First.Batch.Shape.TestsNamed

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain Link Place KindName seatSame)
open VerifiableInference.Desc.First (S ModelPart kindsBeforeBatching K8.ParW)
open VerifiableInference.Desc.First.TailClaims
open VerifiableInference.Desc.First.TailClaims.Law.Tests
open VerifiableInference.Desc.First.Shape (ChainSh chainSh)
open VerifiableInference.Desc.LinkJoin (batchAt)
open Johnson.Desc.First.Walk
open Johnson.Desc.First.Walk.Shape
open Johnson.Desc.First.Walk.Seat (framesOf LinkFrame framesOf_arms rowOf pubOf)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc.K9 (testsWhere SegSort TWhere)
open VerifiableInference.Desc.K9.Shape (gTw vTw testsText tests_named k9Tests_is)
open IM (subAt)
open P5J (AtMgA F0T fullLinks)

/-- The frame's letters at an attention link. -/
def attPar (Y : Stages.LinkH) (p : Attention.Plan) (l : Nat) : AttPar :=
  ⟨pubOf Y, l, p.ns, p.seam.tl⟩

/-- The frame's letters at a layers' link. -/
def layPar (W : Verify.Public) (Y : Stages.LinkH) (hp : Layer.HPlan2) (l : Nat) : LayPar :=
  ⟨pubOf Y, l, W.layers.y.h.p4, Y.g, hp.Tp, hp.Fp, hp.ns, hp.tl⟩

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-! ## 1 Which row stands at which link, with its letters -/

theorem row_att (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l : Nat} (hl : l < 25)
    (hs : subAt l = .attention) {fs : List LinkFrame}
    (hfs : framesOf Zp.p.built.links Zp.first Zp.p.X = .ok fs) {f : LinkFrame}
    (hf : fs[l]? = some f) :
    ∃ Y p, Zp.p.built.links[l]? = some Y ∧ Zp.p.X.A[Y.g]? = some p ∧
      planAtt Zp.first.shape (attPar Y p l) = true ∧ f.opened = openAtt (attPar Y p l) ∧
      f.clear = clearWith (pubOf Y) (countsAtt p.nLin) (fun _ => none)
        (rowOf Zp.p.X Zp.first) := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hp := P1L20.plans_hold h.scope h.reads O (plans_at h) hfs hl hf
  rcases framesOf_arms hfs hf with ⟨Y, hY, hk, -⟩ | ⟨h0, Y, _, _, hY, hk, -⟩ |
    ⟨-, Y, p, P, hY, -, hA, rfl, e1, e2, e3⟩ | ⟨-, Y, _, _, hY, hk, -⟩
  · have e := sub_kind h hl hY
    rw [hk, hs] at e
    exact nomatch e
  · subst h0
    have e := sub_kind h hl hY
    rw [hk, hs] at e
    exact nomatch e
  · rw [e1] at hp
    exact ⟨Y, p, hY, hA, hp, e2, e3⟩
  · have e := sub_kind h hl hY
    rw [hk, hs] at e
    exact nomatch e

theorem row_lay (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l : Nat} (hl : l < 25) (h0 : l ≠ 0)
    (hs : subAt l = .layers) {fs : List LinkFrame}
    (hfs : framesOf Zp.p.built.links Zp.first Zp.p.X = .ok fs) {f : LinkFrame}
    (hf : fs[l]? = some f) :
    ∃ Y hp, Zp.p.built.links[l]? = some Y ∧ Zp.p.X.G[Y.g]? = some hp ∧
      planLay Zp.first.shape (layPar Zp.p.X Y hp l) = true ∧
      f.opened = openLay (layPar Zp.p.X Y hp l) ∧
      f.clear = clearWith (pubOf Y) (countsLay hp.tl.NM) leftLay (rowOf Zp.p.X Zp.first) := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hp := P1L20.plans_hold h.scope h.reads O (plans_at h) hfs hl hf
  rcases framesOf_arms hfs hf with ⟨Y, hY, hk, -⟩ | ⟨e0, -⟩ |
    ⟨-, Y, _, _, hY, hk, -⟩ | ⟨-, Y, q, P, hY, -, hG, rfl, e1, e2, e3⟩
  · have e := sub_kind h hl hY
    rw [hk, hs] at e
    exact nomatch e
  · exact absurd e0 h0
  · have e := sub_kind h hl hY
    rw [hk, hs] at e
    exact nomatch e
  · rw [e1] at hp
    exact ⟨Y, q, hY, hG, hp, e2, e3⟩

/-! ## 2 "cleared" at an attention link -/

theorem cleared_att_named (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (l : Nat) (hl : l < 25)
    (hs : subAt l = .attention) :
    ∃ (Y : Stages.LinkH) (p : Attention.Plan) (L : Link S ProofFile.Cl) (b : Block S ProofFile.Cl),
      Zp.p.built.links[l]? = some Y ∧ Zp.p.X.A[Y.g]? = some p ∧
      cF.links[l]? = some L ∧ cF.blocksInOrder[14 * l + L.hear.length + 7]? = some b ∧ b.rounds = [] ∧
      (∀ s rs gs t u, b.decide s rs gs = .ok t →
        clearAttG (pubOf Y) p.nLin (chainSh s) = .ok u → u = chainSh t) ∧
      ∀ s rs gs u, clearAttG (pubOf Y) p.nLin (chainSh s) = .ok u →
        ∃ t, b.decide s rs gs = .ok t := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨-, fs, hfs, hall⟩ := IM.frame_of h.scope h.reads O
  obtain ⟨Lk, f, -, -, bC, eL, -, hf, -, -, -, hC, -, -, -, -, -, -, hb, hr, hd⟩ := hall l hl
  obtain ⟨Y, p, hY, hA, hpl, -, hc⟩ := row_att h hl hs hfs hf
  have hv : (pubOf Y).fv = false := Props.planAtt_fv hpl
  refine ⟨Y, p, Lk, bC, hY, hA, eL, hb, hr, fun s rs gs t u hy hg => ?_,
    fun s rs gs u hg => ?_⟩
  · have hy' : Lk.clear s = .ok t := (hd s rs gs).symm.trans hy
    have hy2 := ((hC s t).1 hy').1
    rw [hc] at hy2
    exact clearAtt_carries (pubOf Y) p.nLin _ _ hv s t u hy2 hg
  · obtain ⟨t, ht⟩ := clearAtt_returns (pubOf Y) p.nLin (fun _ => none)
      (rowOf Zp.p.X Zp.first) hv s u hg
    have hB : clearAttB (pubOf Y) p.nLin (chainSh s) = true := by
      unfold clearAttG at hg
      by_cases hB : clearAttB (pubOf Y) p.nLin (chainSh s) = true
      · exact hB
      · rw [if_neg hB] at hg
        exact nomatch hg
    obtain ⟨hfail, ⟨a, ha, -⟩, -⟩ := (clearAttB_iff (pubOf Y) p.nLin s).1 hB
    obtain ⟨C, F, -, -, -, k, q, hbk, hq⟩ := Props.clearWith_iff.1 ht
    have hn : q = none := hbk.2.2.2.2.1 hv
    subst hn
    rcases hq with ⟨-, hl'⟩ | ⟨w, _, _, e, -⟩
    · obtain ⟨rfl, -⟩ := (leave_att ha t).1 hl'
      refine ⟨({ s with check := s.live, here := .between } : S),
        (hd s rs gs).trans ((hC s _).2 ⟨by rw [hc]; exact ht, hfail, ?_⟩)⟩
      unfold ProofFile.sameReply
      exact beq_self_eq_true _
    · exact nomatch e

/-! ## 3 The member at a link's first place -/

theorem opened_att_named (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (l : Nat) (hl : l < 24)
    (hs : subAt l = .attention) :
    ∃ (Bs : ProofFile.PureBase) (Y : Stages.LinkH) (p : Attention.Plan) (L : Link S ProofFile.Cl)
        (b b' : Block S ProofFile.Cl) (k : KindName),
      ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs ∧
      Zp.p.built.links[l]? = some Y ∧ Zp.p.X.A[Y.g]? = some p ∧
      cF.links[l]? = some L ∧ L.hear[0]? = some b ∧
      (kindsBeforeBatching (subAt l) (l == 0))[0]? = some k ∧
      (∃ Lt ∈ ProofFile.onlineFirstChainBlockTables Zp, b' ∈ Lt.blocks Bs.G₀) ∧
      b'.place = { chain := 1, link := some l, piece := 1, kind := k } ∧
      planAtt Zp.first.shape (attPar Y p l) = true ∧
      ∀ s t rs gs, b.decide s rs gs = .ok t ↔
        ∃ m, b'.decide s (rs.take b'.rounds.length) (gs.take b'.openings) = .ok m ∧
          m.failed = none ∧ ProofFile.sameReply s m = true ∧ openAtt (attPar Y p l) m = .ok t := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨k, hk, hk7⟩ := first_kind l hl
  obtain ⟨L, b, e1, e2, Lt, hLt, b', hb', hpc, fs, f, hfs, hf, e⟩ :=
    IM.first_sits h.scope h.reads O l (by omega) k hk
  obtain ⟨Y, p, hY, hA, hpl, eo, -⟩ := row_att h (by omega : l < 25) hs hfs hf
  refine ⟨Bs, Y, p, L, b, b', k, O.made, hY, hA, e1, e2, hk, ⟨Lt, hLt, hb'⟩, hpc, hpl,
    fun s t rs gs => ?_⟩
  rw [← eo]
  exact joined_iff e hk7 (by rw [eo]; exact keeps_att _) s t rs gs

theorem opened_lay_named (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (l : Nat) (hl : l < 24)
    (h0 : l ≠ 0) (hs : subAt l = .layers) :
    ∃ (Bs : ProofFile.PureBase) (Y : Stages.LinkH) (hp : Layer.HPlan2) (L : Link S ProofFile.Cl)
        (b b' : Block S ProofFile.Cl) (k : KindName),
      ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs ∧
      Zp.p.built.links[l]? = some Y ∧ Zp.p.X.G[Y.g]? = some hp ∧
      cF.links[l]? = some L ∧ L.hear[0]? = some b ∧
      (kindsBeforeBatching (subAt l) (l == 0))[0]? = some k ∧
      (∃ Lt ∈ ProofFile.onlineFirstChainBlockTables Zp, b' ∈ Lt.blocks Bs.G₀) ∧
      b'.place = { chain := 1, link := some l, piece := 1, kind := k } ∧
      planLay Zp.first.shape (layPar Zp.p.X Y hp l) = true ∧
      ∀ s t rs gs, b.decide s rs gs = .ok t ↔
        ∃ m, b'.decide s (rs.take b'.rounds.length) (gs.take b'.openings) = .ok m ∧
          m.failed = none ∧ ProofFile.sameReply s m = true ∧
          openLay (layPar Zp.p.X Y hp l) m = .ok t := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨k, hk, hk7⟩ := first_kind l hl
  obtain ⟨L, b, e1, e2, Lt, hLt, b', hb', hpc, fs, f, hfs, hf, e⟩ :=
    IM.first_sits h.scope h.reads O l (by omega) k hk
  obtain ⟨Y, hp, hY, hG, hpl, eo, -⟩ := row_lay h (by omega : l < 25) h0 hs hfs hf
  refine ⟨Bs, Y, hp, L, b, b', k, O.made, hY, hG, e1, e2, hk, ⟨Lt, hLt, hb'⟩, hpc, hpl,
    fun s t rs gs => ?_⟩
  rw [← eo]
  exact joined_iff e hk7 (by rw [eo]; exact keeps_lay _) s t rs gs

/-! ## 4 "behind the batching" -/

/-- What stands at link m, with the smallness test's numbers named. -/
theorem link_named (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (m : Nat) (hm : m < 25) :
    ∃ (Bs : ProofFile.PureBase) (Xl : Stages.LinkH) (w : SegSort × Nat × TWhere) (L : Link S ProofFile.Cl)
        (name : String) (a : Place),
      ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs ∧ Bs.G₀.built[m]? = some Xl ∧
      testsWhere Zp.p.X m 0 = some w ∧ cF.links[m]? = some L ∧ L.tests = testsText w ∧
      (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder[batchAt fullLinks P5J.At.ps m + 1]? =
        some L.behindB ∧
      L.orderAfter = VerifiableInference.Desc.First.orderAfterOf (subAt m) ∧
      L.hear[k8No (subAt m)]? = some (IM.seatedAs ProofFile.sameReply
        (VerifiableInference.Desc.First.K8.whole (ProofFile.k8ParW Zp Bs.G₀ Xl m)) name a) := by
  obtain ⟨L, -, -, hsort, hlk, hseg, -, hflat, -⟩ := LPFK9.fields_at_constant h m hm
  have hl : cF.links[m]? = some L := (h.laid.linkAt m).symm.trans hlk
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hsub : (ProofFile.subsOf Zp)[m]? = some (subAt m) := by
    rw [LPFK9.subs_full h.scope h.reads O]
    exact hsort
  have hi : 2 ≤ k8No (subAt m) + 1 ∧ k8No (subAt m) + 1 ≤ 9 := by
    cases subAt m <;> exact ⟨by decide, by decide⟩
  obtain ⟨Lk, b, Xl, e1, e2, hX, -, hla⟩ :=
    IM.k8_alone O m (subAt m) hsub (k8No (subAt m)) (k8_index _ _) hi
  obtain rfl : Lk = L := Option.some.inj (e1.symm.trans hl)
  obtain ⟨L9, -, w, T, l9, -, -, -, -, -, -, -, -, -, -, -, -, -, hw, -, -, hT, eT⟩ :=
    (IM.k9_of h.scope h.reads O).2 m hm
  obtain rfl : L9 = Lk := Option.some.inj (l9.symm.trans hl)
  have eT' : L9.tests = testsText w := by
    rw [eT]
    rw [k9Tests_is, hw] at hT
    exact (Option.some.inj hT).symm
  exact ⟨Bs, Xl, w, L9, _, _, O.made, hX, hw, hl, eT', hflat, hseg.orderAfter,
    e2.trans (congrArg some hla)⟩

/-- **"Behind the batching" at the thirteen links of the sorts attention and head.** -/
theorem behind_named (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (m : Nat) (hm : m < 25)
    (hs : subAt m ≠ .layers) :
    ∃ (Bs : ProofFile.PureBase) (Xl : Stages.LinkH) (w : SegSort × Nat × TWhere) (L : Link S ProofFile.Cl),
      ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs ∧ Bs.G₀.built[m]? = some Xl ∧
      testsWhere Zp.p.X m 0 = some w ∧ cF.links[m]? = some L ∧
      (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder[batchAt fullLinks P5J.At.ps m + 1]? =
        some L.behindB ∧
      (∀ (s s' : S) (t : ChainSh), L.runBehind s = .ok s' →
        behindG (gTw w) (ProofFile.k8ParW Zp Bs.G₀ Xl m).nU (chainSh s) = .ok t → t = chainSh s') ∧
      ∀ (s : S) (t : ChainSh),
        behindG (gTw w) (ProofFile.k8ParW Zp Bs.G₀ Xl m).nU (chainSh s) = .ok t → vTw w s = true →
        (∀ s₁, bareRun k8LsTail.2 s = .ok s₁ →
          valsS (ProofFile.k8ParW Zp Bs.G₀ Xl m).nU s₁ = true) →
        ∃ s', L.runBehind s = .ok s' := by
  obtain ⟨Bs, Xl, w, L, name, a, hB, hX, hw, hl, eT, hflat, ho, hh⟩ := link_named h m hm
  have ho' : L.orderAfter = [(k8No (subAt m), "K8.lsTail"), (k8No (subAt m), "K8.tests")] := by
    rw [ho]
    cases hq : subAt m with
    | layers => exact absurd hq hs
    | attention => rfl
    | head => rfl
  refine ⟨Bs, Xl, w, L, hB, hX, hw, hl, hflat,
    fun s s' t hr hg => behind_carries ho' (k8Runs_seated hh) s s' t hr hg,
    fun s t hg hv hv₂ => ?_⟩
  obtain ⟨s', hs', -⟩ := behind_seated ho' hh
    (fun s h1 h2 => by rw [eT]; exact tests_named w s h1 h2) s t hg hv hv₂
  exact ⟨s', hs'⟩

/-- The layers' test on the free slot, at a plan of a group: it reads the plan's number of slots in
use alone. -/
def freeVH (hp : Layer.HPlan2) (s : S) : Bool :=
  match s.here with
  | .lay a => (a.own.map fun o => OnBytes.Desc.First.K4.freeSlotOk hp.used o.wo.sFv a.F).getD false
  | _ => false

theorem freeV_eq (q : Par4) : freeV q = freeVH q.hp := rfl

/-- The layers' run "free-slot", at a plan of a group. -/
def freeRunH (hp : Layer.HPlan2) : S → Except String S := fun t =>
  (VerifiableInference.Desc.named "the part is not there" (OnBytes.Desc.First.K4.part? t)).bind
    fun q => (OnBytes.Desc.First.K4.freeSlot OnBytes.Desc.First.K4.seatOwn hp q).map
      (OnBytes.Desc.First.K4.setPart t)

theorem freeRun_eq (q : Par4) : freeRun q = freeRunH q.hp := rfl

/-- **"Behind the batching" at the twelve layers' links.** -/
theorem layers_named (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (g : Nat) (hg : g < 12) :
    ∃ (Bs : ProofFile.PureBase) (Xl : Stages.LinkH) (hp : Layer.HPlan2) (w : SegSort × Nat × TWhere)
        (L : Link S ProofFile.Cl),
      ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs ∧
      Bs.G₀.built[2 * g]? = some Xl ∧ Bs.G₀.W.G[g]? = some hp ∧
      testsWhere Zp.p.X (2 * g) 0 = some w ∧ cF.links[2 * g]? = some L ∧
      (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder[batchAt fullLinks P5J.At.ps (2 * g) + 1]? =
        some L.behindB ∧
      (∀ (s s' : S) (t : ChainSh), L.runBehind s = .ok s' →
        behindG₃ (gTw w) freeG (ProofFile.k8ParW Zp Bs.G₀ Xl (2 * g)).nU (chainSh s) = .ok t →
        t = chainSh s') ∧
      ∀ (s : S) (t : ChainSh),
        behindG₃ (gTw w) freeG (ProofFile.k8ParW Zp Bs.G₀ Xl (2 * g)).nU (chainSh s) = .ok t →
        vTw w s = true →
        (∀ s₁, bareRun k8LsTail.2 s = .ok s₁ → freeVH hp s₁ = true) →
        (∀ s₁ s₂, bareRun k8LsTail.2 s = .ok s₁ → freeRunH hp s₁ = .ok s₂ →
          valsS (ProofFile.k8ParW Zp Bs.G₀ Xl (2 * g)).nU s₂ = true) →
        ∃ s', L.runBehind s = .ok s' := by
  obtain ⟨Bs, Xl, w, L, n₈, a₈, hB, hX, hw, hl, eT, hflat, ho, h8⟩ :=
    link_named h (2 * g) (by omega)
  rw [sub_even g hg] at ho h8
  obtain ⟨Bs', base, O⟩ := h.laid.opened
  obtain rfl : Bs = Bs' := Except.ok.inj (hB.symm.trans O.made)
  obtain ⟨Lk, b, y, e1, e2, -, hla, -, -, -, hG, -⟩ := IM.k4_of h.scope h.reads O g hg
  obtain rfl : Lk = L := Option.some.inj (e1.symm.trans hl)
  have h4 : Lk.hear[2]? = some (IM.seatedAs ProofFile.sameReply (ProofFile.k4Block y) b.name (IM.k4Place g)) :=
    e2.trans (congrArg some hla)
  have K := k8Runs_seated h8
  have hF := free_seated h4
  have cF' : ∀ s s' t, (freeRun { y.2 with k3Runs := true } s).bind
      (seatSame ProofFile.sameReply s) = .ok s' → freeG (chainSh s) = .ok t → t = chainSh s' :=
    fun s s' t => freeS_carries _ s s' t
  refine ⟨Bs, Xl, y.2.hp, w, Lk, hB, hX, hG, hw, hl, hflat,
    fun s s' t hr hg' => behind₃_carries (oF := (2, "free-slot")) ho K hF cF' s s' t hr hg',
    fun s t hg' hv hvF hv₂ => ?_⟩
  exact behind₃_returns (oF := (2, "free-slot")) ho K hF cF'
    (vF := freeV { y.2 with k3Runs := true }) (fun s _ _ hv => freeS_returns _ s hv)
    (fun s h1 h2 => by rw [eT]; exact tests_named w s h1 h2)
    sameReply_k8set s t hg' hv
    (fun s₁ h₁ => hvF s₁ ((bind_seatSame_iff _ _ s s₁).1 h₁).1)
    (fun s₁ s₂ h₁ h₂ => hv₂ s₁ s₂ ((bind_seatSame_iff _ _ s s₁).1 h₁).1
      ((bind_seatSame_iff _ _ s₁ s₂).1 h₂).1)

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.layers_named
#print axioms Johnson.AtFull.Shape.row_att
#print axioms Johnson.AtFull.Shape.row_lay
#print axioms Johnson.AtFull.Shape.cleared_att_named
#print axioms Johnson.AtFull.Shape.opened_att_named
#print axioms Johnson.AtFull.Shape.opened_lay_named
#print axioms Johnson.AtFull.Shape.link_named
#print axioms Johnson.AtFull.Shape.behind_named
#print axioms Johnson.AtFull.Shape.attPar
#print axioms Johnson.AtFull.Shape.layPar
#print axioms Johnson.AtFull.Shape.freeVH
#print axioms Johnson.AtFull.Shape.freeV_eq
#print axioms Johnson.AtFull.Shape.freeRunH
#print axioms Johnson.AtFull.Shape.freeRun_eq
