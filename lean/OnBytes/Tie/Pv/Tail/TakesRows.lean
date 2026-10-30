-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Tail/TakesRows.lean: open steps on which entries of the plan the calls of a link use
up, each typed as a closed statement, with the lists of names that they speak of as written terms.

Definitions alone: nothing is proved here and nothing is assumed. Whoever proves a step states a
theorem of that very type in a file of its own.

The kit: OnBytes/Tie/Pv/Tail/EndTakes.lean (`Takes x N`: wherever the verifier's routine x returns
it has used up entries of the plan with just the names N; laws pure, bind, bindOn, after, before,
of_eq, lift, foldlM, must, get; the calls on the channel; masked sumchecks; `takes_pad` as a worked
example); EndTakesFrame.lean (the tactics qb, qs, ql, which pass a stretch of a text that closes no
round; sendings, the switch, the fold; `takes_getB`, `takes_mustB`, `takes_sub`, `takes_call`);
EndTakesPlan.lean and OnBytes/Tie/Pv/Req/Names.lean (`Says x N` for the planner's routines;
`says_forest` as a worked example). How a proof goes: unfold the routine; pass each call that closes
no round by `Takes.after (by qs) fun _ => ?_`; at a call that closes rounds `Takes.bind (its law)
fun _ => ?_`; take pairs apart by obtain and `dsimp only`; where the list is written otherwise,
`.of_eq (by simp [...])`. An «if» without «else» in a do-block doubles what follows it in both
branches: go by cases first.

Main names:
  `row_takes_first`, `row_takes_checkFirst`, `row_firstNames`, `row_takes_frameClose`,
    `row_takes_checkClose`, `row_takes_doorH`: a link's first call and its closing.
  `scoresNames`, `divideNames`, `attainNames`, `attOwnNames`; `row_takes_scores`,
    `row_takes_divide`, `row_takes_attain`, `row_says_attOwn`, `row_att_names`: the own rounds of an
    attention sub-proof.
  `headOwnNames`, `mergeNames`; `row_takes_tscIn`, `row_takes_hearSquares`,
    `row_takes_hearProducts`, `row_takes_hearStream`, `row_takes_hearLogits`, `row_takes_wsForkEnd`,
    `row_says_headOwn`, `row_says_headEnd`: the own rounds of the head's sub-proof, and the merge.
  `layerOwnNames`; `row_says_layerOwn`, `row_takes_hearOwn`: the own rounds of a layer sub-proof.

Limits: statements alone; whether they hold is not shown in this file. Names alone: nothing on an
entry's other fields.


-/
import OnBytes.Model.AttentionRounds
import OnBytes.Model.HeadRounds
import OnBytes.Model.VerifySubproofs
import OnBytes.Tie.Pv.Req.Link
import OnBytes.Tie.Pv.Tail.EndTakesFrame
import OnBytes.Tie.Pv.Tail.EndTakesPlan

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Tail.TakesRows
open OnBytes OnBytes.Model OnBytes.Tie.Pv.Tail.Used OnBytes.Tie.Pv.Tail.Lull OnBytes.Tie.Pv.Req

/-! ## The frame: a link's first call and its closing -/

/-- (F1) A link's first call. Text: OnBytes/Iop/Req.lean (ReqFrame.first). Laws at hand:
takes_closeEmpty, takes_sendVerify, takes_switch, beginLink_link, takes_getB. -/
def row_takes_first : Prop :=
  ∀ (f : ReqFrame) (L : Params.ReqLink), f.shape.link[f.link]? = some L →
    Takes f.first (firstNames L.plain f.link)

/-- (F2) The same one layer up. Text: OnBytes/Model/ReqChain.lean (ChainCheck.first). From (F1). -/
def row_takes_checkFirst : Prop :=
  ∀ (k : ChainCheck) (L : Params.ReqLink), k.frame.shape.link[k.frame.link]? = some L →
    Takes k.first (firstNames L.plain k.frame.link)

/-- (F3) The names of a link's first call are the planner's (OnBytes/Tie/Pv/Req/Link.lean:
headNames). -/
def row_firstNames : Prop :=
  ∀ (l : Nat) (links : List Params.ReqLink) (L : Params.ReqLink), links.head? = some L →
    firstNames L.plain l = headNames l links

/-- (F4) The closing of a link in the frame. Text: OnBytes/Iop/Req.lean (ReqFrame.close, foldShape;
ioppFoldShape). Laws at hand: takes_batVerify, takes_fold, takes_getB, takes_mustB. The one thing to
show beside the walk: (f.foldShape f.link layout).layout.k = layout.k. -/
def row_takes_frameClose : Prop :=
  ∀ (f : ReqFrame) (G : ReqGroup), f.groups[f.link]? = some G → Takes f.close (closeNames G.k)

/-- (F5) The same one layer up. Text: OnBytes/Model/ReqChain.lean (ChainCheck.close). From (F4). -/
def row_takes_checkClose : Prop :=
  ∀ (k : ChainCheck) (eq : ReqEquation) (G : ReqGroup), k.frame.groups[k.frame.link]? = some G →
    Takes (k.close eq) (closeNames G.k)

/-- (F6) The closing of a link as a sub-proof's check calls it. Text: OnBytes/Model/Trees.lean
(doorH). The link's state is read at the routine's beginning; LinkM.call tests that the chain is at
the link. From (F5), with a law like takes_call that lets f use the chain's state. -/
def row_takes_doorH : Prop :=
  ∀ (laid : Nat) (G : ReqGroup) (L L' : LinkCtx) (F F' : Fork) (c c' : Ctx),
    L.check.frame.groups[L.check.frame.link]? = some G →
    doorH laid L F c = .ok ((((), L'), F'), c') → TookN (closeNames G.k) c c'

/-! ## Attention: the own rounds -/

/-- The names of the rounds that Attention.scores closes. -/
def scoresNames (S : Attention.Shape) : List String :=
  (Attention.unitsOf S Attention.Table.kfd [Attention.Seg.fm, Attention.Seg.fd]).flatMap fun u =>
    pscNames (S.nvKF u.2.2) true

/-- The names of the rounds that Attention.divide closes. -/
def divideNames (S : Attention.Shape) : List String :=
  pscNames S.nvE true ++ ("BAT-sigma" :: (pscNames S.nvVM true ++ pscNames S.nvVD true))

/-- The names of the rounds that Attention.attain closes. -/
def attainNames (S : Attention.Shape) : List String :=
  "ZERO" :: ("BAT-sigma" :: (pscNames S.nvF true ++ ("BAT-sigma" ::
    (pscNames S.scdDegrees.length true ++ ("BAT-sigma" :: pscNames S.nvH true)))))

/-- The names of the rounds that the planner lays for an attention sub-proof's own rounds. -/
def attOwnNames (x : Params.AttentionRounds) : List String :=
  x.score.flatMap (fun s => pscNames s.1 true) ++ (pscNames x.e true ++ ("BAT-sigma" ::
    (pscNames x.valueM true ++ (pscNames x.valueD true ++ ("ZERO" :: ("BAT-sigma" ::
      (pscNames x.attained true ++ ("BAT-sigma" :: (pscNames (x.lt + x.lgk + x.lt) true ++
        ("BAT-sigma" :: pscNames x.bits true))))))))))

/-- (A1) Text: OnBytes/Model/AttentionSums.lean (sc3Rounds, sc3In, sc3Row), AttentionScores.lean. -/
def row_takes_scores : Prop :=
  ∀ (S : Attention.Shape) (zk : Array (Array E)), Takes (Attention.scores S zk) (scoresNames S)

/-- (A2) Text: OnBytes/Model/AttentionDivide.lean (productIn, valueBelowIn, valueOnIn, divide). -/
def row_takes_divide : Prop :=
  ∀ (S : Attention.Shape) (zk : Array (Array E)), Takes (Attention.divide S zk) (divideNames S)

/-- (A3) Text: OnBytes/Model/AttentionDivide.lean (coinsOm, scoreAtIndexIn, keyAtIndexIn, bitsIn,
attain), AttentionSums.lean (scdRounds, scdIn, scdRow). -/
def row_takes_attain : Prop :=
  ∀ (S : Attention.Shape), Takes (Attention.attain S) (attainNames S)

/-- (A4) The planner's half. Text: OnBytes/Params/SubRounds.lean (planAttentionOwn, attentionSc3,
attentionScd). Laws at hand: says_psc, says_batSigma, says_scalars, says_zero; a law for forEach is
wanted. -/
def row_says_attOwn : Prop :=
  ∀ x : Params.AttentionRounds, Says (Params.planAttentionOwn x) (attOwnNames x)

/-- (A5) The two lists are one at a plan that Attention.plan has made. Text:
OnBytes/Model/AttentionPlan.lean (plan :277-300: own; Counts.of, Counts.call :140-163: score),
AttentionShape.lean (unitsOf; scdDegrees :643). -/
def row_att_names : Prop :=
  ∀ (settings : Settings) (i : Attention.In) (cf : Attention.Cfg) (P : Attention.Plan),
    Attention.plan settings i cf = .ok P →
    scoresNames P.S ++ (divideNames P.S ++ attainNames P.S) = attOwnNames P.own

/-! ## The head: the own rounds and the merge -/

/-- The names of the rounds that the planner lays for the head sub-proof's own rounds. -/
def headOwnNames (x : Params.HeadRounds) : List String :=
  "ZERO" :: ("BAT-sigma" :: (levelNames (x.lPd + x.lt) ++ ("BAT-sigma" ::
    (pscNames x.lt (decide (0 < x.rowValues)) ++ (pscNames x.lt true ++
      pscNames (x.lt + x.lPd) true)))))

/-- The names of the rounds of the merge of the weight claims. -/
def mergeNames (lk : Nat) : List String := "BAT-sigma" :: pscNames lk true

/-- (H1) Text: OnBytes/Model/Tsc.lean. tscRounds tests lt ≤ P.size, and pscEnds
(OnBytes/Model/Psc.lean) tests 1 ≤ degreeInY and 1 ≤ shown: where one of the three fails tscIn never
returns, and the statement holds emptily. -/
def row_takes_tscIn : Prop :=
  ∀ (P : Array E) (lt shown degreeInY : Nat),
    Takes (tscIn P lt shown degreeInY) (pscNames lt (decide (0 < shown)))

/-- (H2) Text: OnBytes/Model/HeadHeard.lean (hearSquares). Laws at hand: takes_batch,
takes_levelIn. -/
def row_takes_hearSquares : Prop :=
  ∀ (h : Head.Shape) (PV : Array E),
    Takes (Head.hearSquares h PV) ("BAT-sigma" :: levelNames (h.lPd + h.lt))

/-- (H3) Text: OnBytes/Model/HeadHeard.lean (hearProducts, shownRun). From (H1). -/
def row_takes_hearProducts : Prop :=
  ∀ (h : Head.Shape) (PV : Array E), Takes (Head.hearProducts h PV)
    ("BAT-sigma" :: pscNames h.lt (decide (0 < Model.ledNO h.XL)))

/-- (H4) Text: OnBytes/Model/HeadHeard.lean (hearStream). From (H1). -/
def row_takes_hearStream : Prop :=
  ∀ (h : Head.Shape) (zt : Array E), Takes (Head.hearStream h zt) (pscNames h.lt true)

/-- (H5) Text: OnBytes/Model/HeadHeard.lean (channelRounds, hearLogits), Tsc.lean (tscRounds). -/
def row_takes_hearLogits : Prop :=
  ∀ (h : Head.Shape) (lam : Nat) (zt : Array E),
    Takes (Head.hearLogits h lam zt) (pscNames (h.lt + lam) true)

/-- (H6) The merge. Text: OnBytes/Model/Merge.lean (wsForkRounds, wsForkMerge, wsForkEnd). -/
def row_takes_wsForkEnd : Prop :=
  ∀ (lay : WsLay) (cl : Array WsClaim) (sv : Array Nat),
    Takes (wsForkEnd lay cl sv) (mergeNames lay.lk)

/-- (H7) The planner's half of the own rounds. Text: OnBytes/Params/SubRounds.lean (planHeadOwn,
planTokenSum). -/
def row_says_headOwn : Prop :=
  ∀ x : Params.HeadRounds, Says (Params.planHeadOwn x) (headOwnNames x)

/-- (H8) The planner's half of the merge and the batching element. -/
def row_says_headEnd : Prop :=
  ∀ x : Params.HeadRounds, Says (Params.planHeadEnd x) (mergeNames x.lkW ++ ["BAT-sigma"])

/-! ## A group of layers: the own rounds -/

/-- The names of the rounds that the planner lays for a layer sub-proof's own rounds. -/
def layerOwnNames (x : Params.LayerRounds) : List String :=
  "ZERO" :: ((if x.firstGroup = true then ["ZERO", "ZERO"] else []) ++ ("BAT-sigma" ::
    ((if (x.lNI != 0) = true then ["JOIN"] else []) ++ (levelNames (x.lNI + x.lPd + x.lt) ++
      ("BAT-sigma" :: (pscNames x.lt true ++
        ((if x.withTerms = true then pscNames x.lt true ++ ["BAT-sigma"] else []) ++
          (pscNames x.lamS true ++ (levelNames (x.ll + x.lPf + x.lt) ++
            ((if x.routed = true then (if 1 < x.ll then ["JOIN"] else []) ++
              levelNames (x.ll - 1 + x.lfe + x.lt) else []) ++ mergeNames x.lkW))))))))))

/-- (L1) The planner's half. Text: OnBytes/Params/SubRounds.lean (planLayerOwn, planProductLayer,
planTokenSumcheck). -/
def row_says_layerOwn : Prop :=
  ∀ x : Params.LayerRounds, Says (Params.planLayerOwn x) (layerOwnNames x)

/-- (L2) The port's half. Text: OnBytes/Model/Layer.lean (hearNorms, hearTerms, hearStack,
hearGated, hearOwn), Look.lean (stackRounds), Merge.lean. The three premises say of the record P.rd
what OnBytes/Model/LayerLayout.lean:719-721 computes. Cut it: one law for each of the five routines
first. -/
def row_takes_hearOwn : Prop :=
  ∀ (P : Layer.Pub) (hp : Layer.HPlan2) (g : Nat) (fo : Forest.Heard),
    P.rd.muV = P.rd.lNI + P.y.lPd + P.y.h.lt → P.rd.muH = P.y.h.ll + P.y.lPf + P.y.h.lt →
    P.rd.muH2 = P.y.h.ll - 1 + P.y.lfe + P.y.h.lt →
    Takes (Layer.hearOwn P hp g fo) (layerOwnNames (Verify.layerNumbers P hp g))

end OnBytes.Tie.Pv.Tail.TakesRows
