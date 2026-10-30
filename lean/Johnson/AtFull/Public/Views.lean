-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Public/Views.lean: WHAT headLast, linksCount AND declareLinks READ OF THE 24 LINKS
THAT ARE NOT THE HEAD's, AT THE FULL SIZE, BY LEAN's KERNEL: the views (LV,
Johnson/AtFull/Made/DeclView.lean) of the twelve layers' plans and of the twelve attention's plans,
as the public part's makers make them, are the written ones (viewsFull,
Johnson/AtFull/Made/LinksReturn.lean, its members 0 to 23). For the premise hV of links_return.

  `lvOf`: viewL's text, on a plan's parts in the place of a link. `viewL_link`: viewL of the link
    that SubPlanH.link makes is lvOf of the plan's parts: by definition.
  `lvG g hp`, `lvA g a`: the views of the links that listLinksH makes of the layers' plan hp and of
    the attention's plan a of group g. Name, kind, identifier, the flag fv and (for attention) the
    number 0 of claims on the weights are typed here after listLinksH's text; before_views ties
    them to that text.
  `viewsBefore G A`: the views of the links in front of the head's, in the chain's order, off the
    two arrays of plans.
  `before_views`: with twelve groups and attention, the views of TieK.beforeHead X cov are
    viewsBefore X.G X.A. A general law.
  **`hV_of_parts`**: links_return's premise hV, from: viewsBefore X.G X.A is viewsFull's first 24
    members; the head's link's view is its last. A general law.
  **`views24_W`**: [Lean's kernel; no free letter] behind Layer.plansG, the twelve groups' twins
    (Attention.groupS) and attentionOwners, at a layout of the form that layoutLook returns:
    viewsBefore of the layers' plans and of the attention's plans, these with the smallness tests
    that attentionOwners returns, is viewsFull's first 24 members.
A negative test stands beside it: Johnson/AtFull/Public/ViewsNo.lean.

Limits. At the makers' twins and the written scan, not at publicOf's value: that tie is the join's.
The head's link (member 24) is not here. viewsFull is the evaluator's print; here the kernel holds
24 of its 25 members against the makers. Nothing on soundness.

-/
import Johnson.AtFull.Public.Owners
import Johnson.AtFull.Made.LinksReturn

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace Johnson.AtFull.Public

open OnBytes OnBytes.Model OnBytes.Model.Stages
open Johnson.AtFull.Made.Decl (LV viewL viewsFull)
open OnBytes.Road.K4.Trial.AttK7Owners (onOk withPubC PW mqOf ttR)

/-- viewL's text, on a plan's parts. -/
def lvOf (name : String) (kind gid : Nat) (fv : Bool) (ns NCL : Nat) (tl : HTailF2) (Fp : Fork)
    (Tp : Tail2) : LV :=
  { name := name, kind := kind, gid := gid, fv := fv, ns := ns, NCL := NCL,
    pkMat := tl.pkMat, pxMat := tl.pxMat,
    plFor := tl.plFor.map fun p => (p.owner, p.rootIndex), PK := tl.ix.PK, TX := tl.ix.TX,
    FT := tl.ix.FT, U4 := tl.ix.U.toList.take 4, ZZ := tl.ix.ZZ, BZ := tl.ix.BZ,
    gtTree := tl.gtTree, nt := Tp.nt.map (·.ec), trees := Fp.trees.map fun t => (t.R, t.K) }

/-- The view of the link that SubPlanH.link makes. -/
theorem viewL_link (s : SubPlanH) (name : String) (gid kind g : Nat) (fv : Bool) :
    viewL (s.link name gid kind g fv) = lvOf name kind gid fv s.ns s.NCL s.tl s.Fp s.Tp := rfl

/-- The view of the link G_g (listLinksH, OnBytes/Model/StagesLinks.lean:164; layersPlanOf,
OnBytes/Model/VerifyLinks.lean:25). -/
def lvG (g : Nat) (hp : Layer.HPlan2) : LV :=
  lvOf ("G" ++ toString g) 0 (1 + g) true hp.ns hp.NCL hp.tl hp.Fp hp.Tp

/-- The view of the link A_g among twelve groups (:167; attentionPlanOf, :31). -/
def lvA (g : Nat) (a : Attention.Plan) : LV :=
  lvOf ("A" ++ toString g) 1 (2 + 12 + g) false a.ns 0 a.seam.tl a.seam.Fp a.seam.Tp

/-- The views of the links in front of the head's, in the chain's order. -/
def viewsBefore (G : Array Layer.HPlan2) (A : Array Attention.Plan) : List LV :=
  G.toList.zipIdx.flatMap fun x => lvG x.2 x.1 :: (A[x.2]?).toList.map (lvA x.2)

/-- **With twelve groups and attention, the views of the links in front of the head's are
viewsBefore of the public part's plans.** -/
theorem before_views {X : Verify.Public} (cov : Head.Covered) (hN : X.NGr = 12) (h4 : X.p4 = true) :
    (OnBytes.TieK.beforeHead X cov).map viewL = viewsBefore X.G X.A := by
  unfold OnBytes.TieK.beforeHead viewsBefore
  rw [List.map_flatMap]
  congr 1
  funext x
  unfold OnBytes.TieK.groupLinks
  rw [hN, h4, if_pos rfl, List.map_cons, Array.getElem?_map]
  generalize X.A[x.2]? = oa
  cases oa <;> rfl

/-- **links_return's premise hV, from its two parts.** -/
theorem hV_of_parts {X : Verify.Public} (hN : X.NGr = 12) (h4 : X.p4 = true)
    (hB : viewsBefore X.G X.A = viewsFull.take 24)
    (hH : [viewL ((Verify.headPlanOf X default).link "H" (1 + X.NGr) 2 0 true)] =
      viewsFull.drop 24) :
    (OnBytes.TieK.listedOf X default).map viewL = viewsFull := by
  unfold OnBytes.TieK.listedOf
  rw [List.map_append, before_views default hN h4, hB, List.map_cons, List.map_nil, hH,
    List.take_append_drop]

/-- The test at the plans as the public part's makers make them (publicOfO's lines 155-159, the
attention's groups by their twins). -/
def viewsAt (w : List LV) : Bool :=
  withPubC fun L => onOk (Layer.plansG L) fun G =>
    onOk (Attention.readLines PW.polCallsA) fun l =>
      onOk ((List.range L.y.NGr).mapM (Attention.groupS ttR PW L.y L.sc (mqOf L.y) l)) fun ps =>
        onOk (Verify.attentionOwners L.y.h.p4 L.y.NGr
            (G.map fun O => (⟨O.tl, O.Fp, O.Tp⟩ : Verify.SubPlan))
            (ps.toArray.map fun X => ⟨X.seam.tl, X.seam.Fp, X.seam.Tp⟩)) fun seenA =>
          decide (viewsBefore G
            (ps.toArray.zipWith (fun X s => { X with seam := { X.seam with tl := s.tl } })
              seenA) = w)

/-- **The 24 views are the written ones.** -/
theorem views24_W : viewsAt (viewsFull.take 24) = true := by decide +kernel

end Johnson.AtFull.Public

#print axioms Johnson.AtFull.Public.viewL_link
#print axioms Johnson.AtFull.Public.before_views
#print axioms Johnson.AtFull.Public.hV_of_parts
#print axioms Johnson.AtFull.Public.views24_W
