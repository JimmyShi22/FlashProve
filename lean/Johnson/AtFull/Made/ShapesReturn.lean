-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Made/ShapesReturn.lean: `Model.Verify.shapesWith`
(OnBytes/Model/VerifySubproofs.lean) RETURNS, FORWARD, AT EVERY PUBLIC PART; AND AT A PUBLIC PART AS
AT THE FULL SIZE THE SHAPES THAT IT RETURNS ARE SIZED AS WRITTEN. Joinings; nothing is evaluated
here. A law file; no running text imports it. Nothing on codes.

  `shapesWith_of`: **the forward law**: the range checks are there · as many links as sub-proofs ·
    no unit of the committed table's layout with four digits but the embedding's · what the key's
    proof of the ranges looks up is made ⊢ shapesWith X links layout ids = .ok ⟨subproofsWith X
    links, layout, ids, sh, rc⟩.
  `links_of_frame`: where `Plan.reqFrame` returns at 25 declared links, one answer and the typed
    group lines: its links, as the sizing fills them, are `linksFull`, and they are 25. By
    `reqFrame_links`, `linksOfGroups_length` (Johnson/Desc/K12/Law/Sizes/LinksOfLayout.lean).
  `shapes_and_sizes`: c₁ and c₂ of Johnson/AtFull/Made/Ledger.lean together.

WHAT IS READ OF THE PUBLIC PART X: P.frame · p4 · NGr · layers.wsLay · `rangeChecksOf X` (that the
plans of the twelve groups' layers and attention are there; of each sub-proof's smallness test: its
matrices' rows and columns, and tau). Nothing else: not the routine `linkRounds X`, which
`subproofsWith` hands on unread.

Limits. EVERY PREMISE IS A PREMISE. In the goals' scope four of them are had from a law that lies
(`H2K.Sizes.PubFull`: frame, wsLay, p4, groups); hU and hs at the layout of the ten written sizes
lie as closed facts elsewhere (`ws_parts`, Johnson/AtFull/Made/BuiltAtFull.lean;
`Lk6.AtPlan.shape_returns`). OWED BY OTHERS: that `rangeChecksOf X` returns (hc: it asks that
X.G[g]? and X.A[g]? are there at each g below 12); that `reqFrame` returns; that 25 links are
declared: THIS NUMBER MUST COME FROM `declareLinks`' RETURN, not from a yes of shapesWith, or the
run is a circle; that the layout file's group lines are the typed ones. IN c₁ NOTHING IS A WRITTEN
VALUE: later steps want more of its letters: the fit of the links wants lay = `layoutFull`, a gate
of `configure` reads rc, another the length of ids. The full size alone. Nothing on soundness.

-/
import Johnson.AtFull.Made.SizedReturns
import Johnson.Desc.K12.Law.Sizes.LinksOfLayout
import OnBytes.Model.VerifySubproofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Made
open OnBytes OnBytes.Params OnBytes.Model OnBytes.Model.Verify
open OnBytes.Tie (exc_step exc_go)
open H2K.Sizes VerifiableInference.PlanWritten.Joined
open Lk6.AtPlan (wsFull)

/-! ## 1 `shapesWith`, forward: at every public part -/

/-- **What the verifier's own plans hand to the sizing, forward.** -/
theorem shapesWith_of {X : Public} {links : List ReqLink} {layout : ReqLayout} {ids : List Nat}
    {rc : List RangeCheck} {sh : Plan.Shape} (g1 : rangeChecksOf X = some rc)
    (g2 : (links.length != (if X.p4 then 2 else 1) * X.NGr + 1) = false)
    (g3 : (X.layers.wsLay.U.any fun u => u.nlw == 4 && u.X != 12) = false)
    (g4 : Plan.shapeOfLayout X.layers.wsLay X.layers.wsLay.lk = some sh) :
    shapesWith X links layout ids =
      .ok { sub := subproofsWith X links, layout := layout, identifiers := ids, ranges := sh,
            rangeChecks := rc } := by
  unfold shapesWith
  extract_lets
  refine (exc_step _ (show orRefuse (rangeChecksOf X) "plan-link" = .ok rc by
    rw [g1]; rfl)).trans ?_
  refine (exc_go _ (not_true_of g2)).trans ?_
  refine (exc_go _ (not_true_of g3)).trans ?_
  refine (exc_step _ (show orRefuse (Plan.shapeOfLayout X.layers.wsLay X.layers.wsLay.lk)
    "internal-weight-limbs" = .ok sh by rw [g4]; rfl)).trans ?_
  rfl

/-! ## 2 The links that `reqFrame` returns, as the sizing fills them -/

/-- Where `reqFrame` returns at 25 declared links, one answer and the typed group lines, its links,
with the reply's scalar and as the sizing fills them, are the typed links; and they are 25. -/
theorem links_of_frame {declared : Array Stages.FrameLink} {file : Plan.LayoutLines}
    {rl : List ReqLink} {lay : ReqLayout} (hr : Plan.reqFrame declared file 1 = some (rl, lay))
    (hd : declared.size = 25) (hg : file.groups = groupsFull) :
    fillLinks (withReply rl) = linksFull ∧ rl.length = 25 := by
  have e := reqFrame_links hr
  rw [hd, hg] at e
  refine ⟨?_, ?_⟩
  · rw [e]
    rfl
  · rw [e]
    exact linksOfGroups_length 25 1 groupsFull

/-! ## 3 c₁ and c₂ together, at a public part as at the full size -/

/-- **THE SHAPES ARE MADE AND THE SIZES ARE THE WRITTEN ONES**: the premises c₁ and c₂ of
Johnson/AtFull/Made/Ledger.lean. c₂ ends in a written value. c₁ DOES NOT: the links rl, the layout
lay, the identifiers ids, the ranges sh and the range checks rc are all letters in it. -/
theorem shapes_and_sizes {X : Public} {declared : Array Stages.FrameLink}
    {file : Plan.LayoutLines} {rl : List ReqLink} {lay : ReqLayout} {ids : List Nat}
    {rc : List RangeCheck} {sh : Plan.Shape}
    (hf : X.P.frame = recordLines) (h4 : X.p4 = true) (hN : X.NGr = 12)
    (hY : wsLayOf wsFull true recordLines.blockLog = .ok X.layers.wsLay)
    (hU : (X.layers.wsLay.U.any fun u => u.nlw == 4 && u.X != 12) = false)
    (hs : Plan.shapeOfLayout X.layers.wsLay X.layers.wsLay.lk = some sh)
    (hc : rangeChecksOf X = some rc)
    (hr : Plan.reqFrame declared file X.P.frame.answers = some (rl, lay))
    (hd : declared.size = 25) (hg : file.groups = groupsFull) :
    shapesWith X rl lay ids =
        .ok { sub := subproofsWith X rl, layout := lay, identifiers := ids, ranges := sh,
              rangeChecks := rc } ∧
      sized X.P.frame { sub := subproofsWith X rl, layout := lay, identifiers := ids,
                        ranges := sh, rangeChecks := rc } = .ok writtenSized := by
  rw [hf] at hr
  obtain ⟨e1, e2⟩ := links_of_frame (show Plan.reqFrame declared file 1 = some (rl, lay) from hr)
    hd hg
  refine ⟨shapesWith_of hc (by rw [e2, h4, hN]; rfl) hU hs, ?_⟩
  rw [hf]
  refine sized_at_layout hY hs e1 ?_ ?_ rfl
  · show List.replicate rl.length 1 = List.replicate 25 1
    rw [e2]
  · show X.NGr + 1 = 13
    rw [hN]

end Johnson.AtFull.Made

#print axioms Johnson.AtFull.Made.shapesWith_of
#print axioms Johnson.AtFull.Made.links_of_frame
#print axioms Johnson.AtFull.Made.shapes_and_sizes
