-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/FiveOfFacts.lean (kind K10): THE FIVE COMPARISONS OF PUBLIC NUMBERS IN THEIR SPENDERS' OWN FORMS (`five_in_front`, FiveInFront.lean beside this file) AT A STATE THAT IS «REACHED» AND BEARS NO
MARK, FROM THE FACTS THAT THE LAWS TAKE FROM «REACHED» (`FoldFacts`, Johnson/Desc/First/FoldFacts.lean) AND THE HINGE. A theorem: a join.

What is said.
  `frame_live`: where a link is open, the frame that K10's sub-protocol reads off the state is that link's own.
  `five_of_facts`: **FF : FoldFacts Rch at_ d reqW links ps · a reached at k, no mark · the place at number k is of link l, its piece's number at most 11 + 2 * shiftAt links l · a link L is open · the
    facts' codes are cs = codesFull2, their shape is shapeFull · l < 25 · `ShapesAre` of the state's statement and the frame's group at the l-th written list (THE HINGE) ⊢ hk ∧ hh of `k10OnS_of_order` ∧ hc of
    `ties_of_shapes` | `names_of_shapes` ∧ code of `k10OnS_of_order`**, at x := rdK (at_ a).2 and s := stageOf (gsAt l) 219. General in Rch, at_, d, links, ps: the letters of `rowAsks_whole`.
PAID INSIDE: hg (liveGroups) · hs (liveShape) · hk (frameIs' fourth clause) · hx (codes) · hI (tidy).

Limits. FoldFacts and the hinge are premises. The premises on the place are closed at a written list: not evaluated here. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.FiveInFront
import Johnson.Desc.First.FoldFacts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin

open OnBytes OnBytes.Slice OnBytes.Params OnBytes.Means Johnson.Pack Johnson.Top.H Johnson.G
open Cb
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.First (S ModelPart FoldFacts FoldData shiftAt)
open VerifiableInference.Desc.First.Close
open VerifiableInference.Desc.ReqLit (shapeFull)

/-- Where a link is open, the frame that K10's sub-protocol reads is that link's own. -/
theorem frame_live (s : S) (L : OnBytes.Model.LinkCtx) (h : s.link? = some L) :
    (rdK s).2.1 = L.check.frame := by
  show s.live.frame = _
  unfold S.live
  rw [h]

/-- **THE FIVE AT A REACHED STATE WITHOUT A MARK, FROM FoldFacts AND THE HINGE.** -/
theorem five_of_facts {X P : Type} {Rch : ℕ → X → Prop} {at_ : X → P × S} {d : FoldData}
    {reqW : P → Array UInt32} {links : List ModelPart} {ps : List Place}
    (FF : FoldFacts Rch at_ d reqW links ps) {k : ℕ} (a : X) (hr : Rch k a)
    (hu : (at_ a).2.failed = none) {l : ℕ} (hl : l < 25) (p : Place) (hp : ps[k]? = some p)
    (hpl : p.link = some l) (hpp : p.piece ≤ 11 + 2 * shiftAt links l)
    (L : OnBytes.Model.LinkCtx) (hL : (at_ a).2.link? = some L) {cs : Codes}
    (hcs : cs = codesFull2) (hdc : d.sent.codes = cs) (hds : d.sent.shape = shapeFull)
    (hM : ∀ i, memMain (loAt l) i → ((loAt l).get i).1.mainRows ≠ 0 →
      cMain cs ((loAt l).get i).1 = (stageOf (gsAt l) 219).C)
    (hZ : ∀ i, memMain (loAt l) i → ((loAt l).get i).1.maskRows ≠ 0 →
      cMask cs ((loAt l).get i).1 = (stageOf (gsAt l) 219).Z)
    (es : List Fmt.Entry) {kb : Fin (loAt l).length → Bool} {no : Fin (loAt l).length → ℕ}
    (H : ∀ G, (rdK (at_ a).2).2.2.groups[(rdK (at_ a).2).2.1.group]? = some G →
      ShapesAre (rdK (at_ a).2).2.2 G (loAt l) kb no) :
    (planOf es (rdK (at_ a).2)).k = (stageOf (gsAt l) 219).h + (stageOf (gsAt l) 219).g ∧
      (planOf es (rdK (at_ a).2)).h = (stageOf (gsAt l) 219).h ∧
      (∀ G lay, (rdK (at_ a).2).2.2.groups[(rdK (at_ a).2).2.1.group]? = some G →
        (begun (rdK (at_ a).2).2.2 (rdK (at_ a).2).2.1.group G).layout
          (rdK (at_ a).2).2.1.group = some lay →
        2 ^ lay.logEll = (stageOf (gsAt l) 219).C.l ∧
          2 ^ lay.logEllZk = (stageOf (gsAt l) 219).Z.l) ∧
      ((rdK (at_ a).2).2.2.codes.mask.getD (planOf es (rdK (at_ a).2)).maskCode default).ell =
        (stageOf (gsAt l) 219).Z.l := by
  refine five_in_front hl hcs hM hZ es (rdK (at_ a).2) (FF.liveGroups k a hr hu)
    ((FF.liveShape k a hr hu).trans hds) ?_ ((FF.codes k a hr hu).trans hdc)
    (tidy4B_iff.1 (FF.tidy k a hr hu)).inOrder H
  rw [frame_live _ L hL]
  exact ((FF.frameIs k a p l L hr hu hp hpl hL).2.2.2 hpp).1

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.frame_live
#print axioms VerifiableInference.Desc.LinkJoin.five_of_facts
