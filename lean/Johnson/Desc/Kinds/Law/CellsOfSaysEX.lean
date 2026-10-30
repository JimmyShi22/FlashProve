--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Kinds/Law/CellsOfSaysEX.lean.
WHAT IT DOES NOT SHOW. A TOY: cells written out in Lean; no file in
scope; not what the prover's program lays. THAT THE VERIFIER's OWN ARRAY IS THE LIBRARY's EX is
another desk's (Law/LibTab.lean: tab_EX, on 16 bits): no tie to it is typed here. |Wh| <= 2^12 and
C < 2^40 stay premises. The example is Law/CellsOfSaysAt.lean's: made-up stream, weights, request
and policy. No soundness, no probability, nothing on hiding.
LETTERS. No top statement has a letter under "there is". sT is read by planOk alone.
WHAT IT IS. THE CONVERSE OF LEMMA 1, WHOLE, AT THE LIBRARY's OWN TABLE.
  tabEX, tabEX_cast   Inst/Model/Tables.lean's EX as natural numbers.
  steps_EX, steps_step   EX is a step table (by the library's tab9 and EX_step); so is stepTab.
  says_withTab, both_of_says_tab, both_of_says_EX   planOk, Request.ok, y < V, CellRelN c,
                    Says c.toCells, |Wh| <= 2^12, C < 2^40: CellRelN, CellRel AT THE TABLE and Says
                    hold of withTab tab c: at every step table; at EX.
  AtY.mar_Y1, AtY.row1_Y   in the example, at each of the 1022 positions that pay, every lifted
                    margin is 256: the middle digit is 1: ROW 1 IS HIT, and the value laid is 2.
  AtY.both_Y_EX     both relations and the claim, at EX, of the example's cells: no premise.

-/
import Mathlib
import Johnson.Desc.Kinds.Law.CellsOfSaysTab
import Johnson.Desc.Kinds.Law.CellsOfSaysAt
import Inst.Model.Head.PolicyHonest

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law

/-- The library's table EX (Inst/Model/Tables.lean), as natural numbers: 2^24, 2, 1, 1, ... -/
def tabEX (u : Nat) : Nat := (Inst.Model.exG u + (2 ^ 17 - 1)) / 2 ^ 17

theorem tabEX_cast (u : Nat) : (tabEX u : Int) = Inst.Model.EX u := rfl

section

variable [Sizes] [Policy] [Request] [Token]

/-- **The library's table is a step table.** -/
theorem steps_EX (hF : F = 24) : Steps tabEX := by
  obtain ⟨h0, h1⟩ := Inst.Model.TablesSanity.tab9
  refine ⟨⟨?_, fun u => ?_⟩, fun u hu => ?_⟩
  · rw [hF]
    rw [← tabEX_cast] at h0
    exact_mod_cast h0
  · have := h1 u
    rw [← tabEX_cast] at this
    rw [hF]
    exact ⟨by exact_mod_cast this.1, by exact_mod_cast this.2⟩
  · have := (Inst.Model.Head.Policy.Honest.EX_step hu).2
    rw [← tabEX_cast] at this
    exact_mod_cast this

/-- So is the table of two values. -/
theorem steps_step (hF : F = 24) : Steps stepTab :=
  ⟨tableOk_step hF, fun u hu => by
    unfold stepTab
    rw [if_neg (by omega)]
    norm_num⟩

/-- The claim speaks of the logits alone, and these are c's. -/
theorem says_withTab (tab : Nat → Nat) {c : NCells} (h : Says c.toCells) :
    Says (withTab tab c).toCells :=
  ⟨by
    have := h.a
    simpa only [cost_withTab] using this, by
    have := h.b
    simpa only [cost_withTab] using this, fun e1 => h.c e1⟩

/-- **THE CONVERSE OF LEMMA 1, WHOLE, AT EVERY STEP TABLE.** -/
theorem both_of_says_tab (tab : Nat → Nat) (hS : Steps tab) {sT : Nat}
    (hplan : planOk sT = true) (hreq : Request.ok = true) (hy : y < V) {c : NCells}
    (h : CellRelN c) (hs : Says c.toCells) (hw : ∀ k v, (c.Wh k v).natAbs ≤ 2 ^ 12)
    (hC : C < 2 ^ 40) :
    CellRelN (withTab tab c) ∧ CellRel (withTab tab c).toCells tab ∧
      Says (withTab tab c).toCells := by
  obtain ⟨a1, a2, _⟩ := both_withTab tab hS hplan hreq hy (fair_of hplan h hs hw hC) h
  exact ⟨a1, a2, says_withTab tab hs⟩

/-- **AT THE LIBRARY's OWN TABLE.** -/
theorem both_of_says_EX {sT : Nat} (hplan : planOk sT = true) (hreq : Request.ok = true)
    (hy : y < V) {c : NCells} (h : CellRelN c) (hs : Says c.toCells)
    (hw : ∀ k v, (c.Wh k v).natAbs ≤ 2 ^ 12) (hC : C < 2 ^ 40) :
    CellRelN (withTab tabEX c) ∧ CellRel (withTab tabEX c).toCells tabEX ∧
      Says (withTab tabEX c).toCells :=
  both_of_says_tab tabEX (steps_EX (planFacts hplan).hF) hplan hreq hy h hs hw hC

end

end VerifiableInference.Desc.Kinds.Head.Law

namespace VerifiableInference.Desc.Kinds.Head.Law.AtY

open Norm (lt ls d lPd T S2)
open AtX (sizesX requestX tokenX request_X token_X win_X costed_X rc_X checked_X)

attribute [local instance] sizesX policyY requestX tokenX

/-- At a position that pays every lifted margin is 256: all logits are 0 there. -/
theorem mar_Y1 {t x : Nat} (h1 : 1 ≤ t) (ht : t < 1023) (hx : x < V) : marA cY x t = 256 := by
  have hc := costed_X ht
  have h3 := checked_of_costed hc
  have hn : ¬ (checked t = true ∧ x < 0) := fun h => Nat.not_lt_zero x h.2
  have h0 : ¬ t = 0 := by omega
  unfold marA
  rw [if_pos ⟨hx, h3⟩, if_pos ⟨hx, hc⟩, paid_Y ht, over_Y ht, logit_Y (lt_T ht), logit_Y (lt_T ht),
    win_X, if_neg hn, if_neg h0, if_neg h0, if_neg (fun h => h0 h.1), if_neg (fun h => h0 h.1)]
  norm_num

/-- **SO ITS MIDDLE DIGIT IS 1: ROW 1 OF THE TABLE IS HIT, AND THE VALUE LAID IS THE LIBRARY's 2.**
-/
theorem row1_Y {t x : Nat} (h1 : 1 ≤ t) (ht : t < 1023) (hx : x < V) :
    midA cY x t = 1 ∧ tabEX (midA cY x t).toNat = 2 := by
  have e : midA cY x t = 1 := by
    unfold midA midD
    rw [mar_Y1 h1 ht hx]
    show (if (256 : Int) / 2 ^ 8 < 2 ^ 16 then (256 : Int) / 2 ^ 8 else _) = 1
    norm_num
  refine ⟨e, ?_⟩
  rw [e]
  have := Inst.Model.Head.Policy.Honest.EX_one
  rw [← tabEX_cast] at this
  exact_mod_cast this

/-- **BOTH RELATIONS ON CELLS, WHOLE, AT THE LIBRARY's OWN TABLE, OF Law/CellsOfSaysAt.lean's CELLS:
NO PREMISE IS LEFT.** -/
theorem both_Y_EX :
    CellRelN (withTab tabEX cY) ∧ CellRel (withTab tabEX cY).toCells tabEX ∧
      Says (withTab tabEX cY).toCells :=
  both_of_says_EX plan_Y request_X token_X cellRelN_Y fair_Y.claim fair_Y.wts fair_Y.clip

end VerifiableInference.Desc.Kinds.Head.Law.AtY
