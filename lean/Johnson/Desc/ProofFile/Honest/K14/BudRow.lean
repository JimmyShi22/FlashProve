-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/BudRow.lean: kind K14: HOW MANY TREES THE SHARED CHAIN HAS SENT IN
FRONT OF "send o_omega", AS THE FRAME's RULE COUNTS THEM (the last argument of asksFrom in the field
bud₂ of BudDebts, Honest/Law/OwedRule.lean): as many as "send o_u" states. General in the plan, at
lists of the form FlatOf (Johnson/Desc/K14/Honest/FlatForm.lean). Statements with their proofs; no
definition.

  front_five      where a list of that form is cut at a member that stands at "send o_omega"'s
                  place, and no member behind the sixth stands there: what lies in front is the
                  list's first five members
  trees_before_omega   **there the rule's count is the number of oracle messages that "send o_u"
                  states in its first round**: "LIN point", "(rec_gamma)" and "LOC" state none

An oracle message, as a sub-protocol states it, is ONE TREE; it may hold several of the sending's
messages.
What is assumed. hno: no member of the list behind its sixth stands at "send o_omega"'s place:
FlatOf says nothing of what stands behind the ninth.
What is not claimed. That number at any plan (Honest/K14/BudAtRow.lean). Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K14.DataMade
import Johnson.Desc.ProofFile.Honest.Law.StratWords

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open VerifiableInference.Desc (Block)
open Desc.K14 (P14 St blocks)
open Desc.K14.Honest (FlatOf)

variable {Cl : Type} {c : OnBytes.Model.Verify.Chains} {P : P14}
  {b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit}

/-- Cut at a member that stands at "send o_omega"'s place: in front lie the first five. -/
theorem front_five {x0 x1 x2 x3 x4 x5 : Block St Cl} {rest pre t : List (Block St Cl)}
    {b : Block St Cl} (hx : x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: rest = pre ++ b :: t)
    (hp : b.place = sendPlace 5) (h0 : x0.place ≠ sendPlace 5) (h1 : x1.place ≠ sendPlace 5)
    (h2 : x2.place ≠ sendPlace 5) (h3 : x3.place ≠ sendPlace 5) (h4 : x4.place ≠ sendPlace 5)
    (hno : ∀ y ∈ rest, y.place ≠ sendPlace 5) : pre = [x0, x1, x2, x3, x4] := by
  match pre, hx with
  | [], hx => exact absurd ((List.cons.inj hx).1 ▸ hp) h0
  | [_], hx =>
    simp only [List.cons_append, List.nil_append, List.cons.injEq] at hx
    exact absurd (hx.2.1 ▸ hp) h1
  | [_, _], hx =>
    simp only [List.cons_append, List.nil_append, List.cons.injEq] at hx
    exact absurd (hx.2.2.1 ▸ hp) h2
  | [_, _, _], hx =>
    simp only [List.cons_append, List.nil_append, List.cons.injEq] at hx
    exact absurd (hx.2.2.2.1 ▸ hp) h3
  | [_, _, _, _], hx =>
    simp only [List.cons_append, List.nil_append, List.cons.injEq] at hx
    exact absurd (hx.2.2.2.2.1 ▸ hp) h4
  | [_, _, _, _, _], hx =>
    simp only [List.cons_append, List.nil_append, List.cons.injEq] at hx
    obtain ⟨rfl, rfl, rfl, rfl, rfl, -⟩ := hx
    rfl
  | _ :: _ :: _ :: _ :: _ :: _ :: pre', hx =>
    simp only [List.cons_append, List.cons.injEq] at hx
    exact absurd hp (hno b (by rw [hx.2.2.2.2.2.2]; simp))

/-- **The rule's count of the trees in front of "send o_omega" is the number of oracle messages that
"send o_u" states in its first round.** -/
theorem trees_before_omega {xs : List (Block St Cl)} (F : FlatOf xs c b1 b2 b3 b4 b5 b6 b7 b8)
    (hb : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8])
    (hno : ∀ y ∈ xs.drop 6, y.place ≠ sendPlace 5) (pre t : List (Block St Cl))
    (b : Block St Cl) (hx : xs = pre ++ b :: t) (hp : b.place = sendPlace 5) :
    ∃ os, b2.oracles = [os, []] ∧
      (((rowsOfChain xs).take (pre.flatMap (·.rounds)).length).map (·.2.length)).sum =
        os.length := by
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, tl, rfl, l0, l1, l2, l3, l4, l5, l6, l7, l8⟩ := F
  obtain ⟨p1, p4, -, -⟩ := places4 P b1 b2 b3 b4 b5 b6 b7 b8 hb
  obtain ⟨p3, -⟩ := places2 P b1 b2 b3 b4 b5 b6 b7 b8 hb
  obtain ⟨⟨d₀, d₁, os, rU, oU, -⟩, pU, -, -⟩ := send_declares P 0 b1 b2 b3 b4 b5 b6 b7 b8 hb
  obtain ⟨-, -, -, r1, o1, r4, o4, -, -⟩ := declares3 P b1 b2 b3 b4 b5 b6 b7 b8 hb
  obtain ⟨r3, -, -, -, -⟩ := declares_none P b1 b2 b3 b4 b5 b6 b7 b8 hb
  have q0 : x0.place = ⟨2, none, 0, .frame⟩ := l0.place
  have s0 : x0.rounds = [] := l0.rounds
  obtain rfl := front_five hx hp (by rw [q0]; decide) (by rw [l1.place, p1]; decide)
    (by rw [l2.place, pU]; decide) (by rw [l3.place, p3]; decide)
    (by rw [l4.place, p4]; decide) hno
  refine ⟨os, oU, ?_⟩
  simp [rowsOfChain, s0, l1.rounds, l1.oracles, l2.rounds, l2.oracles, l3.rounds, l4.rounds,
    l4.oracles, r1, o1, rU, oU, r3, r4, o4]

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.front_five
#print axioms ProofFile.Honest.K14.trees_before_omega
