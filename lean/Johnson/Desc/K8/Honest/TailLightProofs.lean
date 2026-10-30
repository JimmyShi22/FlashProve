-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/TailLightProofs.lean: THE SMALLNESS TEST: THE PROOFS OF THE TWO STATEMENTS OF
Johnson/Desc/K8/Honest/TailLight.lean, over `marks_of_tile`
(Johnson/Desc/K8/Honest/MarksOfTileProof.lean); with them: a yes of the lighter test gives the
seventeen premises. And lines on the library's example. Lemmas and tests; none of the library's
goals.

  `tailReady_of_light`, `tailReadyB_of_light`
  `tailReady_of_lightB`   a yes of the lighter test gives `TailReady`, at some marks and numbers
The lines. At the example behind the list's first four claims (`TailToy.behindFour`,
Johnson/Desc/K8/Honest/EqTailToy.lean) both tests say yes. With the table moved by one entry, a part
one entry too long, a third part, the batching element not drawn, or a table on no matrix of the
list, the lighter test says no. With a third part that is EMPTY the lighter test says no and the
test for the seventeen says yes: the lighter test goes one way.
Limits: those of the statements.
Nothing is claimed on completeness, soundness or hiding.

-/
import Johnson.Desc.K8.Honest.TailLight
import Johnson.Desc.K8.Honest.MarksOfTileProof

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2 VerifiableInference.Desc
open OnBytes.Tie.Pv.Tail.Port (readsList)

theorem tailReady_of_light : Spec.tailReady_of_light := by
  intro before front tl funs F cs s1 s3 h
  obtain ⟨rd, hm, ha, hc⟩ := marks_of_tile tl funs s1 s3 h.inList h.tile1 h.tile3 h.parts
  exact ⟨rd, h.four, h.drawn, h.plan, h.one, h.fresh, h.fits, h.table, h.reads, hm, ha, h.inList,
    h.tile1, h.tile3, h.kinds, h.sum, hc, h.apart⟩

theorem tailReadyB_of_light : Spec.tailReadyB_of_light := by
  intro before front tl funs F cs h
  unfold tailLightB at h
  cases h1 : tl.tablesTile funs 0 with
  | none => rw [h1] at h; cases h
  | some s1 =>
    cases h3 : tl.tablesTile funs 2 with
    | none => rw [h1, h3] at h; cases h
    | some s3 =>
      rw [h1, h3] at h
      simp only [Bool.and_eq_true] at h
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩, a7⟩, a8⟩, a10⟩, a11⟩, a12⟩, a14⟩, a15⟩ := h
      obtain ⟨rd, hm, ha, hc⟩ := marks_of_tile tl funs s1 s3 a10 h1 h3 (of_decide_eq_true a15)
      unfold tailReadyB
      rw [hm, h1, h3]
      simp only [Bool.and_eq_true]
      exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩, a7⟩, a8⟩, ha⟩, a10⟩, a11⟩, a12⟩,
        beq_iff_eq.2 hc⟩, a14⟩

/-- A yes of the lighter test gives the seventeen premises. -/
theorem tailReady_of_lightB {before front : Nat} {tl : HTailF2} {funs : Array HFun} {F : Fork}
    {cs : Array Claim} (h : tailLightB before front tl funs F cs = true) :
    ∃ rd s1 s3, TailReady before front tl funs F cs rd s1 s3 :=
  tailReady_of_B (tailReadyB_of_light before front tl funs F cs h)

namespace TailToy

/-- What the lighter test says at the example; turn: what is spoiled. -/
def light (turnT : HTailF2 → HTailF2) (turnF : Fork → Fork) (fs : Array HFun := funs) :
    Option Bool :=
  (behindFour turnT turnF).map fun y => tailLightB y.1 y.1 y.2.1 fs y.2.2.1 y.2.2.2

#guard light id id == some true && ready id id == some true
-- the table moved by one entry; a part one entry too long; a third part, with and without an entry
#guard light id id (funs.map fun f => { f with start := f.start + 1 }) == some false
#guard light (fun t => { t with tabLen := #[0, 5] }) id == some false
#guard light (fun t => { t with tabLen := t.tabLen.push 1 }) id == some false &&
  ready (fun t => { t with tabLen := t.tabLen.push 1 }) id == some false
#guard light (fun t => { t with tabLen := t.tabLen.push 0 }) id == some false &&
  ready (fun t => { t with tabLen := t.tabLen.push 0 }) id == some true
-- the batching element not drawn; a table on no matrix of the list
#guard light id (fun F => { F with thetaDrawnF := false }) == some false
#guard light id id (funs.push { mat := 7, len := 3, tree := 2 }) == some false

end TailToy

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.tailReady_of_light
#print axioms VerifiableInference.Desc.First.K8.Honest.tailReadyB_of_light
#print axioms VerifiableInference.Desc.First.K8.Honest.tailReady_of_lightB
