-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/PublicImplies.lean: the public tests and structures on an attention
segment's place that the files on the honest prover's side of its own rounds take as premises, each
drawn from the one structure `PublicAll` (Johnson/Desc/K5/Honest/Law/PublicAtPlan.lean). So at a
plan that the planner returns and that passes this library's one test (`public_at_plan`), and at the
library's head on the public input (`public_at_head`, Johnson/Desc/K5/Honest/Law/PublicAtHead.lean),
all of them hold. Statements with their proofs; arithmetic on lists of two members.

WHO IMPLIES WHOM. `PublicAll P fs` gives each of:
  `Sized P`, `Planned P`, `KeysFit fs`, `CallsFit P.S fs`, `UnitsAll`, `PairsAre`, `GeoFits P.g P.x`
                    its own fields
  `P.counted = true`  (Johnson/Desc/K5/Honest/Law/Lengths.lean)        `PublicAll.counted`
  `LiveFits P.g P.x`  (Johnson/Desc/K5/Honest/Law/LiveSecond.lean)     `PublicAll.liveFits`
  `LookFits P.D C`    (Johnson/Desc/K5/Honest/Law/LoneUnits.lean)      `PublicAll.lookFits`
  the public fields of `UnitPlace` (Johnson/Desc/K5/Honest/Law/TilesKit.lean): the unit at its
  number, its number of variables, its number of pieces               `PublicAll.unitsAt`
What `counted`, `LiveFits` and `GeoFits` say, side by side. All three have that the place's numbers
of a token's bits, of pairs and of layers are the planner's. `counted` has beside them: the
planner's list of softmax-table units is not empty; the number of bits of a head of keys; the
numbers of variables of "the score at the index" and of "the index's cells are bits"; and, for each
number below the length of the planner's list, that the place's unit of that number (none counting
as 0) has as many pieces as the planner's member says. It does not say that the two lists have one
length. `LiveFits` has beside the three: the two lists have one length and, member by member, the
planner's number is the unit's number of pieces. `GeoFits` has beside the three: each unit has at
most as many pieces as there are pairs, and each member of the planner's list says the number of
pairs. None of the three gives `Planned`: they say nothing of the other sumchecks' numbers of
variables.

Limits. `PublicAll` is a premise here. No property is claimed.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.K5.Honest.Law.PublicAtPlan
import Johnson.Desc.K5.Honest.Law.Lengths
import Johnson.Desc.K5.Honest.Law.LiveSecond
import Johnson.Desc.K5.Honest.Law.LoneUnits

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Honest
open OnBytes.Road.L5 (callsOf)
open VerifiableInference.Desc.First.Att.P (UnitG)
open Inst.Model.AttSeg (Step)

variable {P : Pub5} {fs : OnBytes.Model.Forest.Shape}

/-- **The two softmax-table units at their numbers**, the one below the diagonal first, each with
its number of pieces; and the two sumchecks' numbers of variables. -/
theorem PublicAll.unitsAt (A : PublicAll P fs) :
    ∃ u1 u2 : UnitG, P.g.scores = [u1, u2] ∧ u1.below = true ∧ u2.below = false ∧
      u1.pcs.length = P.D.nb ∧ u2.pcs.length = P.D.nb ∧
      (cut P.x).getD 0 3 - 3 = Step.s6b.g P.D ∧ (cut P.x).getD 1 3 - 3 = Step.s6d.g P.D := by
  obtain ⟨_, _, u1, u2, _, _, _, U, _, _, n1, n2⟩ := A.units
  exact ⟨u1, u2, U.sco, U.below, U.on, n1, n2, A.vKM, A.vKD⟩

/-- Each softmax-table unit has a piece for each pair that the planner counts. -/
theorem PublicAll.pieces (A : PublicAll P fs) : ∀ u ∈ P.g.scores, u.pcs.length = P.x.pairs := by
  obtain ⟨u1, u2, hs, _, _, n1, n2, _, _⟩ := A.unitsAt
  intro u hu
  rw [hs] at hu
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hu
  rw [A.planned.pairs]
  rcases hu with rfl | rfl
  · exact n1
  · exact n2

theorem PublicAll.liveFits (A : PublicAll P fs) : LiveFits P.g P.x := by
  obtain ⟨u1, u2, hs, _⟩ := A.unitsAt
  exact liveFits_of A.geo A.pieces (by rw [A.score2, hs]; rfl)

theorem PublicAll.lookFits (A : PublicAll P fs) : LookFits P.D (callsOf fs) := by
  obtain ⟨r1, _, _, _, _, _, _, U, _⟩ := A.units
  exact ⟨OnBytes.Road.L5.callsFit_a01 A.fit, U.m1.le, OnBytes.Road.L5.callsFit_deep A.fit .w3,
    (A.keys 2).1, (A.keys 3).1⟩

theorem PublicAll.counted (A : PublicAll P fs) : P.counted = true := by
  obtain ⟨u1, u2, hs, _, _, n1, n2, _, _⟩ := A.unitsAt
  have Pl := A.planned
  have H := A.sized
  have e6 : P.x.attained = P.g.lt + P.g.lgk + P.g.ldh := by
    have e := Pl.vSF
    rw [cut_iSF] at e
    rw [e, H.lt]
    rfl
  have e7 : P.x.bits = P.g.lt + P.g.lgk + 4 := by
    have e := Pl.vHB
    rw [cut_iHB] at e
    rw [e, H.lt]
    rfl
  have e8 : ∀ i < P.x.score.length,
      ((P.g.scores[i]?).map (·.pcs.length)).getD 0 = ((P.x.score[i]?).map (·.2)).getD 0 := by
    intro i hi
    have hx : P.x.score[i]? = some P.x.score[i] := List.getElem?_eq_getElem hi
    have h2 : (P.x.score[i]).2 = P.x.pairs := A.geo.score _ (List.getElem_mem hi)
    have hg : i < P.g.scores.length := by
      rw [hs]
      rw [A.score2] at hi
      exact hi
    have hy : P.g.scores[i]? = some P.g.scores[i] := List.getElem?_eq_getElem hg
    rw [hx, hy]
    show (P.g.scores[i]).pcs.length = (P.x.score[i]).2
    rw [h2]
    exact A.pieces _ (List.getElem_mem hg)
  unfold Pub5.counted
  simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq, List.all_eq_true, List.mem_range]
  exact ⟨⟨⟨⟨⟨⟨⟨A.score, Pl.pairs⟩, Pl.lt⟩, Pl.lgk⟩, Pl.Lam⟩, e6⟩, e7⟩, e8⟩

end H2K5.Honest

#print axioms H2K5.Honest.PublicAll.unitsAt
#print axioms H2K5.Honest.PublicAll.pieces
#print axioms H2K5.Honest.PublicAll.liveFits
#print axioms H2K5.Honest.PublicAll.lookFits
#print axioms H2K5.Honest.PublicAll.counted
