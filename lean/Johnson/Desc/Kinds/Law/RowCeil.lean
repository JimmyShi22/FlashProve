-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/RowCeil.lean: THE TWO LISTS OF THE OUTPUT HEAD's ONE RULE ARE NEVER BOTH NON-EMPTY: so the rule's ceiling is the
one that each list has: at most the last message's scalars and one: STATED AND PROVED, at a ledger that is WellLaid.
WHAT IT DOES NOT SAY. Nothing on probabilities; nothing on the point pV (no rule of this shape carries it).
  normRule_behind   where the normalization's hearing returns on a front and LEAVES a round, the normalization's rule is empty
                    at that front.
  blockRule_none    where it does not return, the rule behind it is empty (by its text).
  blockRule_at_end  where it returns and leaves nothing, the rule behind it is "normed"'s at no round: empty.
  rowRule_length    the ceiling.
IMPORTED, NOT PROVED HERE: norm_parts, normRule_mid, level_length, drawPoint_one, batch_one (Law/NormHear.lean,
Law/NormRule.lean); midRule_back's lines stand inside its norm_block.

-/
import Mathlib
import Johnson.Desc.Kinds.Law.RowWhole

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law.Came

open OnBytes (E)
open OnBytes.Model (Fork World)
open Norm (lt ls d lPd S2 T)

variable [Sizes] [Policy] [Request] [Token]

/-- Behind the level's own rounds the middle rule is the back rule at the ledger behind the level. -/
theorem midRule_back (c : NCells) (mask : Nat → E) {pV : Point} {W : Array Hid} {gam : E}
    {Fa Fb : Fork} {tS : List Fmt.RoundView} {S : Sum}
    (h3 : level (zS pV) (Norm.squaresStart W gam #[]) Fa tS = some (S, Fb, []))
    {fr : List Fmt.RoundView} (hne : fr ≠ []) :
    midRule c mask pV W gam Fa (tS ++ fr) = backRule c mask pV Fb fr := by
  have lS : tS.length = nS pV := level_length h3
  have hpos : 0 < fr.length := List.length_pos_iff.mpr hne
  unfold midRule
  rw [if_neg (by rw [List.length_append, lS]; omega), ← lS, List.take_left, List.drop_left, h3]

/-- **Behind the normalization's own rounds its rule is empty.** -/
theorem normRule_behind (c : NCells) (mask : Nat → E) (F : Fork) (hW : WellLaid F)
    {h left : List Fmt.RoundView} {H : Norm.Heard} {G : Fork} (hh : Norm.hear F h = some (H, G, left))
    (hne : left ≠ []) : normRule c mask F h = [] := by
  obtain ⟨p0, p1, tS, p2, tP, Fa, Fb, Fc, rfl, h0, h1, _, h3, h4, h5, _⟩ := norm_parts hW hh
  obtain ⟨r0, rfl⟩ := drawPoint_one h0
  obtain ⟨r1, _, rfl, _, _, _⟩ := batch_one h1
  obtain ⟨r2, _, rfl, _, _, _⟩ := batch_one h4
  have lP : tP.length = H.pV.size + 3 := by
    obtain ⟨_, _, _, _, _, _, a1, _⟩ := sumcheck_spec h5
    exact a1
  show normRule c mask F (r0 :: r1 :: (tS ++ (r2 :: (tP ++ left)))) = []
  rw [normRule_mid c mask F h0 h1 (by simp), midRule_back c mask h3 (by simp)]
  obtain ⟨a, tl, e⟩ : ∃ a tl, tP ++ left = a :: tl := List.exists_cons_of_ne_nil (by simp [hne])
  have hlen : ¬ (a :: tl).length ≤ H.pV.size + 3 := by
    rw [← e, List.length_append, lP]
    have := List.length_pos_iff.mpr hne
    omega
  rw [e]
  show (match sendThenBatch 7 7 Fb [r2] with
    | none => []
    | some ((_, om), Fc, _) =>
      if (a :: tl).length ≤ H.pV.size + 3 then productsRule c mask Fc H.pV om (a :: tl)
      else []) = []
  rw [h4]
  exact if_neg hlen

section In
variable [FinalNorm.In]

theorem normedRule_nil (c : NCells) (mask : Nat → E) (F0 : Fork) : normedRule c mask F0 [] = [] := by
  simp [normedRule, badG, bad, raw]

variable [In]

theorem blockRule_none (c : NCells) (mask : Nat → E) (F : Fork) {h : List Fmt.RoundView}
    (hN : Norm.hear F h = none) : blockRule c mask F h = [] := by
  simp only [blockRule, tailRule, hN]

theorem blockRule_at_end (c : NCells) (mask : Nat → E) (F : Fork) {h : List Fmt.RoundView}
    {H : Norm.Heard} {G : Fork} (hN : Norm.hear F h = some (H, G, [])) :
    blockRule c mask F h = [] := by
  unfold blockRule tailRule
  rw [hN]
  dsimp only
  rw [if_pos (by simp)]
  exact normedRule_nil c mask G

/-- **THE CEILING OF THE BLOCK's ONE RULE.** -/
theorem rowRule_length (c : NCells) (mask : Nat → E) (F : Fork) (hW : WellLaid F)
    (h : List Fmt.RoundView) : (rowRule c mask F h).length
      ≤ ((h.getLast?.map fun r => r.vals.length).getD 0) + 1 := by
  unfold rowRule
  cases hN : Norm.hear F h with
  | none =>
    rw [blockRule_none c mask F hN, List.append_nil]
    exact normRule_length c mask F h
  | some v =>
    obtain ⟨H, G, left⟩ := v
    by_cases hl : left = []
    · subst hl
      rw [blockRule_at_end c mask F hN, List.append_nil]
      exact normRule_length c mask F h
    · rw [normRule_behind c mask F hW hN hl, List.nil_append]
      exact blockRule_length c mask F h

end In

end VerifiableInference.Desc.Kinds.Head.Law.Came

#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.normRule_behind
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.rowRule_length
