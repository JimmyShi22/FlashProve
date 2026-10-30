-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Public/XShapeAt.lean: THE SHAPE PART OF A PUBLIC PART (xShapeOf,
Johnson/Desc/Ok/PlanWritten/XShape.lean) IS THE WRITTEN ONE (xShapeFull, Johnson/G/XShapeLit.lean),
FROM ITS 26 PARTS; and at a public part with the makers' plans. General laws, and one closed fact on
the written list.

  `tlAt_two`: Look.tlAt at profile 4, its two ifs written out.
  `written_range`: [Lean's kernel, through the library's comparison sameTails] xShapeFull's list of
    views is its own members 0 to 24, in order: so it has 25 members.
  **`m4_of_parts`**: profile 4 · twelve groups · at each g below 12 a layers' plan and an
    attention's plan whose smallness tests' views are xShapeFull's segments 2 g and 2 g + 1 ·
    the head's smallness test's view is segment 24 · the head's view is xShapeFull's second part ⊢
    xShapeOf X = xShapeFull.
  **`m4_at`**: the same at a public part X with the witnesses' plans (AtWitnesses.lean) and the
    head's plan HW, trimmed: from the closed fact on layersB and attB (a premise here:
    Johnson/AtFull/Public/ArmsAtMakers.lean pays it) and the two facts on HW
    (tailView_W, headView_W: Johnson/AtFull/Head/PlanAtFull.lean).

Limits. OpensAt and Makers are premises, as in AtWitnesses.lean. xShapeFull is an evaluator's print
(its file's head). The full size alone. Nothing on soundness.

-/
import Johnson.AtFull.Public.AtWitnesses
import Johnson.AtFull.Head.PlanAtFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Public

open OnBytes OnBytes.Model OnBytes.Model.Verify
open OnBytes.Road.K4.Trial.AttL2 (AOf)
open VerifiableInference.PlanWritten (tailView headView xShapeOf)
open VerifiableInference.Desc.First.Look (tlAt)
open Johnson.G (xShapeFull)
open _root_.AtFull.Head (HW tailView_W headView_W)

/-- Look.tlAt at profile 4. -/
theorem tlAt_two {X : Public} (h4 : X.p4 = true) (i : Nat) :
    tlAt X i =
      if i == 2 * X.NGr then some X.H.tl
      else if i % 2 == 0 then X.G[i / 2]?.map (·.tl) else X.A[i / 2]?.map (·.seam.tl) := by
  unfold tlAt
  rw [h4]
  rfl

set_option maxRecDepth 1000000 in
/-- The written list is its own members 0 to 24. -/
theorem written_range : (List.range 25).map (fun k => xShapeFull.1.getD k none) = xShapeFull.1 :=
  (VerifiableInference.PlanWritten.sameTails_iff _ _).1 (by decide +kernel)

/-- **The shape part, from its 26 parts**, at profile 4 and twelve groups. -/
theorem m4_of_parts {X : Public} (h4 : X.p4 = true) (hN : X.NGr = 12)
    (hE : ∀ g, g < 12 → ∃ hp, X.G[g]? = some hp ∧
      some (tailView hp.tl) = xShapeFull.1.getD (2 * g) none)
    (hO : ∀ g, g < 12 → ∃ a, X.A[g]? = some a ∧
      some (tailView a.seam.tl) = xShapeFull.1.getD (2 * g + 1) none)
    (hT : some (tailView X.H.tl) = xShapeFull.1.getD 24 none)
    (hH : headView X = xShapeFull.2) : xShapeOf X = xShapeFull := by
  have hl : (List.range 25).map (fun k => (tlAt X k).map tailView) = xShapeFull.1 := by
    rw [← written_range]
    refine List.map_congr_left fun k hk => ?_
    have hk' := List.mem_range.1 hk
    rw [tlAt_two h4, hN]
    by_cases e24 : k = 24
    · subst e24
      rw [if_pos (by decide)]
      exact hT
    · rw [if_neg fun h => e24 (by have := beq_iff_eq.1 h; omega)]
      by_cases ev : k % 2 = 0
      · rw [if_pos (beq_iff_eq.2 ev)]
        obtain ⟨hp, e0, v⟩ := hE (k / 2) (by omega)
        rw [e0]
        have e : 2 * (k / 2) = k := by omega
        rw [e] at v
        exact v
      · rw [if_neg fun h => ev (beq_iff_eq.1 h)]
        obtain ⟨a, e0, v⟩ := hO (k / 2) (by omega)
        rw [e0]
        have e : 2 * (k / 2) + 1 = k := by omega
        rw [e] at v
        exact v
  unfold xShapeOf
  rw [hl, hH]

variable {y : Layer.Lay} {sc : Layer.Scales} {wsLay : WsLay} {rope : Array Nat}
  {l : List Attention.Line} {ps : List Attention.Plan} {layers : Layer.Pub}
  {G : Array Layer.HPlan2} {seenA : Array SubPlan}

/-- **The shape part at a public part with twelve groups, profile 4, the witnesses' plans and the
head's plan HW, trimmed**: under OpensAt, Makers and the closed fact on layersB and attB. -/
theorem m4_at (O : OpensAt y) (M : Makers y sc wsLay rope l ps layers G seenA)
    (hW : atMakers (fun L G A => layersB L G && attB A) = true) {X : Public}
    (hN : X.NGr = 12) (h4 : X.p4 = true) (eG : X.G = G) (eA : X.A = AOf ps.toArray seenA)
    (eH : X.H = { HW with Fp := HW.Fp.trimL }) : xShapeOf X = xShapeFull := by
  obtain ⟨tE, tO⟩ := tails_at O M hW
  refine m4_of_parts h4 hN (by rw [eG]; exact tE) (by rw [eA]; exact tO) ?_ ?_
  · rw [eH]
    exact tailView_W
  · unfold headView
    rw [eH]
    exact headView_W

end Johnson.AtFull.Public

#print axioms Johnson.AtFull.Public.tlAt_two
#print axioms Johnson.AtFull.Public.written_range
#print axioms Johnson.AtFull.Public.m4_of_parts
#print axioms Johnson.AtFull.Public.m4_at
