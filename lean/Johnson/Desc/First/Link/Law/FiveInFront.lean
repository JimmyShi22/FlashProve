-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/FiveInFront.lean (kind K10): THE FIVE COMPARISONS OF PUBLIC NUMBERS (FiveNumbers.lean, FiveNumbersFull.lean beside this file) IN THE VERY FORMS IN WHICH THEIR SPENDERS ASK THEM, FROM
FACTS ON THE STATE IN FRONT ALONE: the begun statement is dealt with inside. A theorem: a join.

What is said. `five_in_front`: l < 25; cs = codesFull2 (cs a letter); at x := what K10's sub-protocol reads off the state (`rdK`): the frame's groups are reqGroups of its shape · its shape is shapeFull · its link
is l · the statement's codes are cs · the statement is in order (`InOrder`) · `ShapesAre` of the statement and the frame's group at the l-th written list ⊢
  (N1) (planOf es x).k = s.h + s.g and (N2) (planOf es x).h = s.h [hk, hh of `k10OnS_of_order`, Close/Law/OnOfOrder.lean]
  (N3) ∧ (N4) at every group G and layout lay of the BEGUN statement: 2 ^ lay.logEll = s.C.l ∧ 2 ^ lay.logEllZk = s.Z.l [hc of `ties_of_shapes` | `names_of_shapes`, Close/Law/ShapesBegun.lean]
  (N5) (x.2.2.codes.mask.getD (planOf es x).maskCode default).ell = s.Z.l [code of `k10OnS_of_order`]
at s := stageOf (gsAt l) 219.
How. The beginning of the group's test keeps the codes (`extends_begun`), the members, flags and shapes (`shapesAre_begun`) and the order (`InOrder.begun`); `layFacts` at the begun group; then `five_of_shapes`'
pieces.

Limits. The six premises on the state are shown of no state here: the frame's three are fields of `FoldFacts` (liveGroups · liveShape with the entry tests' first pin · frameIs); the codes and the order: `RowAsks`' codes |
inOrder; ShapesAre: the hinge. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.FiveNumbersFull
import Johnson.Desc.First.Close.Law.ShapesBegun
import Johnson.Desc.First.Close.Law.OnOfOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin

open OnBytes OnBytes.Slice OnBytes.Params OnBytes.Means Johnson.Pack Johnson.Top.H Johnson.G
open Cb
open VerifiableInference.Desc.First.Close
open VerifiableInference.Desc.ReqLit (shapeFull)

/-- **THE FIVE, IN THEIR SPENDERS' OWN FORMS, FROM THE STATE IN FRONT.** -/
theorem five_in_front {l : ℕ} (hl : l < 25) {cs : Codes} (hcs : cs = codesFull2)
    (hM : ∀ i, memMain (loAt l) i → ((loAt l).get i).1.mainRows ≠ 0 →
      cMain cs ((loAt l).get i).1 = (stageOf (gsAt l) 219).C)
    (hZ : ∀ i, memMain (loAt l) i → ((loAt l).get i).1.maskRows ≠ 0 →
      cMask cs ((loAt l).get i).1 = (stageOf (gsAt l) 219).Z)
    (es : List Fmt.Entry) (x : Option Nat × ReqFrame × Statement)
    (hg : x.2.1.groups = reqGroups x.2.1.shape) (hs : x.2.1.shape = shapeFull)
    (hk : x.2.1.link = l) (hx : x.2.2.codes = cs) (hI : InOrder x.2.2)
    {kb : Fin (loAt l).length → Bool} {no : Fin (loAt l).length → ℕ}
    (H : ∀ G, x.2.2.groups[x.2.1.group]? = some G → ShapesAre x.2.2 G (loAt l) kb no) :
    (planOf es x).k = (stageOf (gsAt l) 219).h + (stageOf (gsAt l) 219).g ∧
      (planOf es x).h = (stageOf (gsAt l) 219).h ∧
      (∀ G lay, x.2.2.groups[x.2.1.group]? = some G →
        (begun x.2.2 x.2.1.group G).layout x.2.1.group = some lay →
        2 ^ lay.logEll = (stageOf (gsAt l) 219).C.l ∧
          2 ^ lay.logEllZk = (stageOf (gsAt l) 219).Z.l) ∧
      (x.2.2.codes.mask.getD (planOf es x).maskCode default).ell =
        (stageOf (gsAt l) 219).Z.l := by
  obtain ⟨c1, c2, -, b, c4, -, c6⟩ := five_at hl
  obtain ⟨p1, p2, p3⟩ := plan_of_frame es x hg hs hk
  refine ⟨p1.trans c1, p2.trans c2, fun G lay hG hL => ?_,
    code_of_member hZ hx b c4 (p3.trans c6)⟩
  have hG' := begun_at x.2.1.group G hG
  have hOk := (hI.begun x.2.1.group G hG).groups x.2.1.group _ hG'
  have hc : (begun x.2.2 x.2.1.group G).codes = cs :=
    (extends_begun x.2.2 x.2.1.group G).codes.trans hx
  obtain ⟨-, -, n3, n4, -⟩ := five_of_shapes hl hcs hM hZ es x hg hs hk hx hc
    (layFacts hG' hL hOk) (shapesAre_begun x.2.1.group (H G hG))
  exact ⟨n3, n4⟩

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.five_in_front
