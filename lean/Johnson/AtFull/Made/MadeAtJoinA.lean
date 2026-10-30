-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Made/MadeAtJoinA.lean: the first half of the join of `Key.madeAt`'s ledger
(Johnson/AtFull/Made/Ledger.lean): the shapes are made, the sizes are the written ones, and the
planner `configure` returns the value made of the written plans. General in the public part X:
what is read of X stands as hypotheses by field.

What it says.
  `xOf X sh rc`      the shapes that the facts used here force: the sub-proofs of X at the
                     written links, the written layout and identifiers; the ranges sh and the range
                     checks rc are letters.
  `madeW x cfg`      the value that `configure` returns at the written sizes and the seven written
                     plans (`madeOfParts`).
  `shapes_join`      a₁ a₂ a₃ a₄ b₂ c₁ c₂ paid, under: X is as at the full size (`PubFull`) · twelve
                     plans of each kind · the segments' views are the written ones (hV) · the layout
                     file reads as the written value (b₁) · the range checks are rc (hc).
  `configure_join`   d₁ … d₄ · e₂ e₃ · f₁ … f₆ paid, under: the lines are the written ones (hf) ·
                     c₂ · e₁ (the proof file's first plan returns the written one) · `ShapesRead`
                     (five facts, Johnson/AtFull/Made/Gates.lean).

Where the facts used lie, all under Johnson/AtFull/Made/. links_return: LinksReturn.lean ·
reqFrame_of_pub: ReqFrameOfPub.lean · shapes_and_sizes: ShapesReturn.lean · gates_written_closed:
GatesClosed.lean · ws_parts: BuiltAtFull.lean · key_first_written: KeyFirstWritten.lean · the list
of premises: Ledger.lean. The other written plans: Johnson/Goal/Written/MadeOfSized.lean.

Limits. A joining: it pays none of its hypotheses. THAT ANY PUBLIC FILES MEET THEM IS SHOWN NOWHERE
HERE. Nothing on soundness.
-/
import Johnson.AtFull.Made.Ledger
import Johnson.AtFull.Made.LinksReturn
import Johnson.AtFull.Made.ReqFrameOfPub
import Johnson.AtFull.Made.ShapesReturn
import Johnson.AtFull.Made.KeyFirstWritten
import Johnson.AtFull.Made.GatesClosed
import Johnson.AtFull.Made.BuiltAtFull
import Johnson.AtFull.Made.Seams
import Johnson.AtFull.LayoutRead.GroupsAre
import Johnson.Goal.Written.MadeOfSized

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Made
open OnBytes OnBytes.Model OnBytes.Model.Verify OnBytes.Model.Stages OnBytes.Params
open VerifiableInference.PlanWritten (proofSizedFull)
open VerifiableInference.PlanWritten.Joined (writtenSized entry_written)
open VerifiableInference.Number.ByRuns (proofThree keyThree shared_written second_written
  proof_shared_written proof_second_written)
open Johnson.G (pricedEntryFull layoutFull)
open Johnson.AtFull.LayoutRead (LW)
open H2K.Sizes (PubFull)

/-- The shapes that the facts used here force. -/
def xOf (X : Public) (sh : Plan.Shape) (rc : List RangeCheck) : Shapes :=
  { sub := subproofsWith X reqLinksW, layout := layoutFull, identifiers := idsFull, ranges := sh,
    rangeChecks := rc }

/-- The `Configured` value of the written sizes and the seven written plans. -/
def madeW (x : Shapes) (cfg : ByteArray) : Configured :=
  madeOfParts recordLines x cfg writtenSized proofThree.A.plan proofThree.B.plan proofThree.C.plan
    keyThree.A.plan keyThree.B.plan keyThree.C.plan pricedEntryFull

/-- **The shapes are made and the sizes are the written ones.** -/
theorem shapes_join {X : Public} {lay : ByteArray} {rc : List RangeCheck} (P : PubFull X)
    (hG : X.G.size = 12) (hA : X.A.size = 12)
    (hV : (OnBytes.TieK.listedOf X default).map Decl.viewL = Decl.viewsFull)
    (b₁ : Plan.layoutRead lay = some LW) (hc : rangeChecksOf X = some rc) :
    ∃ (links₀ links : Array LinkH) (sh : Plan.Shape),
      linksOf X default = .ok links₀ ∧ headLast links₀ = .ok () ∧ linksCount links₀ = .ok () ∧
      declareLinks links₀ X.NGr X.p4 = .ok (links, declaredFull) ∧
      links.toList.map viewOf = viewFull ∧
      Plan.shapeOfLayout X.layers.wsLay X.layers.wsLay.lk = some sh ∧
      shapesOf X (some lay) = .ok (links, xOf X sh rc) ∧
      sized X.P.frame (xOf X sh rc) = .ok writtenSized := by
  obtain ⟨links₀, links, a₁, a₂, a₃, a₄, hv, hi⟩ := Decl.links_return P.groups P.p4 hG hA hV
  obtain ⟨Y, sh, hY, hs⟩ := Lk6.AtPlan.shape_returns
  obtain rfl : Y = X.layers.wsLay := Except.ok.inj (hY.symm.trans P.wsLay)
  have b₂ : Plan.reqFrame declaredFull LW X.P.frame.answers = some (reqLinksW, layoutFull) :=
    reqFrame_of_pub P moments_seam rfl
  obtain ⟨c₁, c₂⟩ := shapes_and_sizes (ids := idsFull) P.frame P.p4 P.groups P.wsLay
    (ws_parts P.wsLay).1 hs hc b₂ declared_size Johnson.AtFull.LayoutRead.groups_are
  refine ⟨links₀, links, sh, a₁, a₂, a₃, a₄, hv, hs, ?_, c₂⟩
  exact shapesOf_of_parts a₁ a₂ a₃ a₄ b₁ b₂ (by rw [hi]; exact c₁)

/-- **The planner returns the value made of the written plans.** -/
theorem configure_join {l : Lines} {x : Shapes} (cfg : ByteArray) (hf : l = recordLines)
    (c₂ : sized l x = .ok writtenSized)
    (e₁ : firstPlan proofSizedFull x.sub = .ok proofThree.A.plan)
    (R : ShapesRead x proofThree.A.plan) :
    configure l x cfg 0 = .ok (madeW x cfg) := by
  subst hf
  have d₁ : Plan.oneTimePlan writtenSized.key = .ok keyThree.A.plan := key_first_written
  obtain ⟨f₁, f₂, f₃, f₄, f₅, f₆⟩ := gates_written_closed x proofThree.A.plan R
  exact configure_of_parts c₂ e₁ proof_shared_written proof_second_written d₁ shared_written
    second_written entry_written f₁ f₂ f₃ f₄ f₅ f₆

#print axioms Johnson.AtFull.Made.shapes_join
#print axioms Johnson.AtFull.Made.configure_join

end Johnson.AtFull.Made
