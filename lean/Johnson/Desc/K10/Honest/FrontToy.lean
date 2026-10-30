-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K10/Honest/FrontToy.lean: the propositions of Johnson/Desc/K10/Honest/YesFree.lean and
Front.lean ARE MET: members at made-up data, so that the theorems there are not empty.

The data are Johnson/Desc/First/Close/Law/CloseToys.lean's: a group of one member and two open rows;
k = 2, h = 0; four rounds.
  `toy_yes`        the kind's block's decision says yes on them: by `decide +kernel`: Lean's kernel
                   evaluates the decision itself; no compiled code is trusted
  `front_member`   so `CloseFront` holds at the element that the toy's "BAT" drew (`front_of_yes`)
  `back_yes`       and from that member the decision's yes comes back (`close_yes`, called)
  `shaped_member`, `shaped_other`   the toy's rounds, and rounds with other sent values and other later
                   challenges, have the kind's shape
  `other_yes`      so the decision says yes at these other rounds too: `kind_free`, called at premises
                   that are met together with a true side
  `other_yes'`     the same by Lean's kernel alone: a second road to that yes

Limits. One instance; no kept member; rows of single entries. Nothing on soundness, completeness or
hiding of the protocol.

-/
import Johnson.Desc.K10.Honest.Front
import Johnson.Desc.First.Close.Law.CloseToys

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10.YesFree.Toy
open OnBytes VerifiableInference.Desc VerifiableInference.Desc.First.Close
open VerifiableInference.Desc.First.Close.MeansToys (fr S0 rs0 rv el rB)

def P : Par := { link := 0, piece := 0, k := 2, h := 0, rows := 2, workField := 0, workClose := 0
                 sent := [] }
def s : Rec := ⟨none, fr, S0⟩

/-- The same "BAT"; other values sent, other challenges drawn behind it. -/
def rs1 : List Fmt.RoundView :=
  [rB, rv [el 90] [el 91], rv [el 92, el 93] [el 94], rv [el 95, el 96] [el 97]]

theorem toy_yes : (((kind (Cl := Unit)) P).decide s rs0 []).toOption.isSome = true := by
  decide +kernel

theorem toy_ok : ∃ s', ((kind (Cl := Unit)) P).decide s rs0 [] = .ok s' := by
  have h := toy_yes
  cases hd : ((kind (Cl := Unit)) P).decide s rs0 [] with
  | ok s' => exact ⟨s', rfl⟩
  | error e => rw [hd] at h; cases h

theorem front_member : ∃ t D, batDraw rs0 = [t] ∧ CloseFront P s (E.ofTriple t) D := by
  obtain ⟨s', h⟩ := toy_ok
  obtain ⟨t, D, a, b, _⟩ := front_of_yes h
  exact ⟨t, D, a, b⟩

theorem shaped_rv (xs : List E) (d : E) : Shaped xs.length (rv xs [d]) :=
  ⟨⟨xs.map (·.triple), by simp [rv], by simp⟩, ⟨d.triple, rfl⟩, rfl, rfl⟩

theorem shaped_member : ShapedAll rs0 :=
  ⟨shaped_rv [] _, shaped_rv [_] _, by
    intro r hr
    rcases List.mem_cons.1 hr with rfl | hr
    · exact shaped_rv [_, _] _
    · rcases List.mem_cons.1 hr with rfl | hr
      · exact shaped_rv [_, _] _
      · cases hr⟩

theorem shaped_other : ShapedAll rs1 :=
  ⟨shaped_rv [] _, shaped_rv [_] _, by
    intro r hr
    rcases List.mem_cons.1 hr with rfl | hr
    · exact shaped_rv [_, _] _
    · rcases List.mem_cons.1 hr with rfl | hr
      · exact shaped_rv [_, _] _
      · cases hr⟩

theorem back_yes : ∃ s', ((kind (Cl := Unit)) P).decide s rs0 [] = .ok s' := by
  obtain ⟨t, D, a, b⟩ := front_member
  exact close_yes b rs0 [] rfl shaped_member t a rfl

theorem other_yes : ∃ s', ((kind (Cl := Unit)) P).decide s rs1 [] = .ok s' :=
  (kind_free P s rs0 rs1 [] [] rfl shaped_member shaped_other rfl).1 toy_ok

theorem other_yes' : (((kind (Cl := Unit)) P).decide s rs1 []).toOption.isSome = true := by
  decide +kernel

end ProofFile.Honest.K10.YesFree.Toy

#print axioms ProofFile.Honest.K10.YesFree.Toy.toy_yes
#print axioms ProofFile.Honest.K10.YesFree.Toy.front_member
#print axioms ProofFile.Honest.K10.YesFree.Toy.shaped_member
#print axioms ProofFile.Honest.K10.YesFree.Toy.shaped_other
#print axioms ProofFile.Honest.K10.YesFree.Toy.back_yes
#print axioms ProofFile.Honest.K10.YesFree.Toy.other_yes
#print axioms ProofFile.Honest.K10.YesFree.Toy.other_yes'
