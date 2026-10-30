-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Entry/Makers/SameAtBuilt.lean: A BUILT LINK FOR LAYERS BEARS ITS OWN PLAN'S LIST OF
ARRAYS AND PLANNED FORK, AS A GENERAL LAW. Nothing is evaluated here.

Why. The row of the links' frames in the proof file's first chain
(Johnson/AtFull/Desc/Lots/FramesRow.lean) stands under six hypotheses. The sixth, `sameB`, compares
each built link for layers with the entry of the public part's plans at the link's group: the number
of tables and the sizes of the planned fork. The links are made of these very plans
(`ProofFile.Plain.linksPlain`, Johnson/Desc/ProofFile/PlanPlain.lean), and the step that builds them
changes one other field alone (`OnBytes.TieK.buildLinksH_keeps`). So the comparison cannot fail.

  `kind0_of_listed`: a link of kind 0 in the list of all links was made of the plan that stands at
    the link's own group, and bears that plan's list of arrays and planned fork.
  `plan_of_built`: the same of a link as built, at the public part's own plans: THE PLAN IS THERE,
    and the two fields are its own.
  `same_of_built`: so `sameB` accepts at every number l.
  **`same_of_pub`**: wherever the public part Z of the proof file's description returns,
    `sameB Z.p.built.links Z.p.X l = true` at every l.

Limits. `sameB` also accepts where there is no link at l, where the link is of another kind and
where no plan stands at its group; that 25 links are there, of which kinds, and that twelve plans
are there, are other hypotheses of the same row and are not shown here. `plan_of_built` is the part
that says more than an accept. That the public part returns at any files is a premise. Nothing on
soundness.

-/
import Johnson.AtFull.Desc.Lots.FramesRow
import Johnson.AtFull.Desc.Lots.LinksInScope
import OnBytes.TieK.LinksEnd
import OnBytes.TieK.LinksAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Entry

open OnBytes OnBytes.Model
open OnBytes.Model.Stages (LinkH LinksH SubPlanH listLinksH buildLinksH)

/-- A link of kind 0 in the list of all links was made of the plan at its own group. -/
theorem kind0_of_listed {NGr : Nat} {p4 : Bool} {G A : Array SubPlanH} {H : SubPlanH} {Y : LinkH}
    (hY : Y ∈ OnBytes.TieK.listed NGr p4 G A H) (hk : Y.kind = 0) :
    ∃ s, G[Y.g]? = some s ∧ Y.Tp = s.Tp ∧ Y.Fp = s.Fp := by
  unfold OnBytes.TieK.listed OnBytes.TieK.listedBefore at hY
  rcases List.mem_append.1 hY with hY | hY
  · obtain ⟨⟨s, g⟩, hx, hY⟩ := List.mem_flatMap.1 hY
    have hg : G[g]? = some s := by
      rw [← Array.getElem?_toList]
      exact List.mem_zipIdx_iff_getElem?.1 hx
    unfold OnBytes.TieK.groupLinks at hY
    rcases List.mem_cons.1 hY with e | hY2
    · rw [e]
      exact ⟨s, hg, rfl, rfl⟩
    · by_cases h4 : p4 = true
      · rw [if_pos h4] at hY2
        obtain ⟨a, -, e⟩ := List.mem_map.1 hY2
        rw [← e] at hk
        have h1 : (1 : Nat) = 0 := hk
        omega
      · rw [if_neg h4] at hY2
        cases hY2
  · have e := List.mem_singleton.1 hY
    rw [e] at hk
    have h2 : (2 : Nat) = 0 := hk
    omega

variable {X : Verify.Public} {l₀ : Array LinkH} {p : Params.First} {B : LinksH}

/-- **A link for layers, as built: its plan is there, and it bears that plan's two fields.** -/
theorem plan_of_built (h₀ : ProofFile.Plain.linksPlain X = .ok l₀)
    (hB : buildLinksH l₀ X.NGr X.p4 X.layers.wsLay p = .ok B) {l : Nat} {Y : LinkH}
    (hY : B.links[l]? = some Y) (hk : Y.kind = 0) :
    ∃ hp, X.G[Y.g]? = some hp ∧ Y.Tp = hp.Tp ∧ Y.Fp = hp.Fp := by
  have K := OnBytes.TieK.buildLinksH_keeps (fun Z : LinkH => (Z.kind, Z.g, Z.Tp, Z.Fp))
    (fun _ _ => rfl) hB
  have hl : B.links.toList[l]? = some Y := by
    rw [Array.getElem?_toList]
    exact hY
  have hm : (Y.kind, Y.g, Y.Tp, Y.Fp) ∈
      B.links.toList.map fun Z : LinkH => (Z.kind, Z.g, Z.Tp, Z.Fp) :=
    List.mem_map.2 ⟨Y, List.mem_of_getElem? hl, rfl⟩
  rw [K] at hm
  obtain ⟨Y₀, hY₀, e⟩ := List.mem_map.1 hm
  simp only [Prod.mk.injEq] at e
  obtain ⟨ek, eg, eT, eF⟩ := e
  unfold ProofFile.Plain.linksPlain at h₀
  rw [OnBytes.TieK.listLinksH_listed h₀] at hY₀
  obtain ⟨s, hs, sT, sF⟩ := kind0_of_listed hY₀ (ek.trans hk)
  rw [Array.getElem?_map] at hs
  obtain ⟨hp, hhp, es⟩ := Option.map_eq_some_iff.1 hs
  refine ⟨hp, ?_, ?_, ?_⟩
  · rw [← eg]
    exact hhp
  · rw [← eT, sT, ← es]
  · rw [← eF, sF, ← es]

/-- So the comparison accepts at every number. -/
theorem same_of_built (h₀ : ProofFile.Plain.linksPlain X = .ok l₀)
    (hB : buildLinksH l₀ X.NGr X.p4 X.layers.wsLay p = .ok B) (l : Nat) :
    P1L20.Row.sameB B.links X l = true := by
  unfold P1L20.Row.sameB
  cases hY : B.links[l]? with
  | none => rfl
  | some Y =>
    dsimp only
    by_cases hk : Y.kind = 0
    · obtain ⟨hp, e, eT, eF⟩ := plan_of_built h₀ hB hY hk
      have c : (Y.kind == 0) = true := by simpa using hk
      rw [if_pos c, e]
      dsimp only
      rw [eT, eF, Bool.and_eq_true]
      exact ⟨beq_self_eq_true _, beq_self_eq_true _⟩
    · have c : ¬ (Y.kind == 0) = true := by simpa using hk
      rw [if_neg c]

/-- **Wherever the public part of the proof file's description returns, the frames' row's sixth
hypothesis holds, at every number.** -/
theorem same_of_pub {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {Z : ProofFile.Pub}
    (hZ : ProofFile.pubPlain o pol lay KL = .ok Z) (l : Nat) :
    P1L20.Row.sameB Z.p.built.links Z.p.X l = true := by
  have hB := IM.planned_built (ProofFile.Law.madeOf_planned (ProofFile.Law.pubBy_made
          (show ProofFile.pubBy (ProofFile.PlainG.madeOf o) ProofFile.plainStarts pol lay KL = .ok Z from hZ)))
  obtain ⟨l₀, h₀, hB⟩ := IM.plain_built hB
  exact same_of_built h₀ hB l

end Johnson.AtFull.Entry

#print axioms Johnson.AtFull.Entry.kind0_of_listed
#print axioms Johnson.AtFull.Entry.plan_of_built
#print axioms Johnson.AtFull.Entry.same_of_built
#print axioms Johnson.AtFull.Entry.same_of_pub
