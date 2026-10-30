-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Ok/PlanWritten/PublicAtTwo.lean: what of the public part of a stage does not depend on
the second hash function (`publicOfO`, Johnson/Desc/Ok/PlanWritten/PublicAt.lean).

The statements are tools: they hold of all public files and all arguments o, and no description of
the protocol is named.

  `Attention.configO_plans`: where `Attention.configO` returns a value at two arguments o, o', the
    plans of the attention sub-proofs are the same.
  `publicOfO_two`: where `publicOfO` returns a value at two arguments o, o', the two records differ
    at most in the three digests of the lists of lookup calls. So o decides whether a value is
    returned, and these three fields, and nothing else.

How it is proved. Both computations are followed step by step; a step that does not name o returns
one value in both. At each of the text's two "if" the proof parts in two cases; what follows is done
once for all cases.

Limits. Nothing says at which o a value is returned. Nothing on soundness.
-/
import Johnson.Desc.Ok.PlanWritten.PublicAt
import OnBytes.Params.ConfigureLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.PlanWritten

open OnBytes OnBytes.Model OnBytes.Model.Verify
open OnBytes.Params (exc_bind)

/-- The plans of the attention sub-proofs do not depend on o. -/
theorem Attention.configO_plans {o o' : Nat → ByteArray → ByteArray} {P : PolScan} {y : Layer.Lay}
    {s : Layer.Scales} {midQ : Nat → Nat} {c c' : OnBytes.Attention.Config}
    (h : Attention.configO o P y s midQ = .ok c) (h' : Attention.configO o' P y s midQ = .ok c') :
    c.plans = c'.plans := by
  unfold Attention.configO at h h'
  dsimp only at h h'
  obtain ⟨l, e1, h⟩ := exc_bind h
  obtain ⟨l', e1', h'⟩ := exc_bind h'
  cases e1.symm.trans e1'
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨_, _, h'⟩ := exc_bind h'
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨_, _, h'⟩ := exc_bind h'
  obtain ⟨ps, e2, h⟩ := exc_bind h
  obtain ⟨ps', e2', h'⟩ := exc_bind h'
  cases e2.symm.trans e2'
  cases ps with
  | nil => cases h
  | cons X r =>
    dsimp only at h h'
    obtain ⟨_, _, h⟩ := exc_bind h
    obtain ⟨_, _, h'⟩ := exc_bind h'
    cases h
    cases h'
    rfl

/-- **What of the public part does not depend on o.** -/
theorem publicOfO_two {o o' : Nat → ByteArray → ByteArray} {pol KL : ByteArray}
    {layout : Option ByteArray} {X X' : Public} (h : publicOfO o pol KL layout = .ok X)
    (h' : publicOfO o' pol KL layout = .ok X') : X' = { X with digests := X'.digests } := by
  unfold publicOfO at h h'
  obtain ⟨⟨P, y⟩, e0, h⟩ := exc_bind h
  obtain ⟨⟨P', y'⟩, e0', h'⟩ := exc_bind h'
  cases e0.symm.trans e0'
  dsimp only at h h'
  -- the scales; the test on them; the gate's table
  obtain ⟨sc, esc, h⟩ := exc_bind h
  obtain ⟨sc', esc', h'⟩ := exc_bind h'
  cases esc.symm.trans esc'
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨_, _, h'⟩ := exc_bind h'
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨_, _, h'⟩ := exc_bind h'
  by_cases h3 : y.h.p3 = true <;> first
    | rw [if_pos h3] at h h'
    | rw [if_neg h3] at h h'
  all_goals
    -- the sigmoid's table, or nothing; no sum wraps; the three files' digest; the widths; the
    -- vocabulary
    obtain ⟨_, _, h⟩ := exc_bind h
    obtain ⟨_, _, h'⟩ := exc_bind h'
    obtain ⟨_, _, h⟩ := exc_bind h
    obtain ⟨_, _, h'⟩ := exc_bind h'
    obtain ⟨_, _, h⟩ := exc_bind h
    obtain ⟨_, _, h'⟩ := exc_bind h'
    obtain ⟨_, _, h⟩ := exc_bind h
    obtain ⟨_, _, h'⟩ := exc_bind h'
    obtain ⟨_, _, h⟩ := exc_bind h
    obtain ⟨_, _, h'⟩ := exc_bind h'
    -- the committed matrix; the rotary table and the test on it; the head's layout
    obtain ⟨ws, ews, h⟩ := exc_bind h
    obtain ⟨ws', ews', h'⟩ := exc_bind h'
    cases ews.symm.trans ews'
    obtain ⟨rope, erope, h⟩ := exc_bind h
    obtain ⟨rope', erope', h'⟩ := exc_bind h'
    cases erope.symm.trans erope'
    obtain ⟨_, _, h⟩ := exc_bind h
    obtain ⟨_, _, h'⟩ := exc_bind h'
    obtain ⟨HLy, eHLy, h⟩ := exc_bind h
    obtain ⟨HLy', eHLy', h'⟩ := exc_bind h'
    cases eHLy.symm.trans eHLy'
    by_cases h4 : y.h.p4 = true <;> first
      | (rw [if_pos h4] at h h'
         obtain ⟨c, hc, h⟩ := exc_bind h
         obtain ⟨c', hc', h'⟩ := exc_bind h'
         have ep := Attention.configO_plans hc hc'
         obtain ⟨pl, q⟩ := c
         obtain ⟨pl', q'⟩ := c'
         have ep' : pl = pl' := ep
         subst ep'
         obtain ⟨_, e14, h⟩ := exc_bind h
         obtain ⟨_, e14', h'⟩ := exc_bind h'
         cases e14
         cases e14')
      | (rw [if_neg h4] at h h'
         obtain ⟨_, e14, h⟩ := exc_bind h
         obtain ⟨_, e14', h'⟩ := exc_bind h'
         cases e14
         cases e14')
  all_goals
    dsimp only at h h'
    obtain ⟨lay, elay, h⟩ := exc_bind h
    obtain ⟨lay', elay', h'⟩ := exc_bind h'
    cases elay.symm.trans elay'
    obtain ⟨G, eG, h⟩ := exc_bind h
    obtain ⟨G', eG', h'⟩ := exc_bind h'
    cases eG.symm.trans eG'
    obtain ⟨sA, esA, h⟩ := exc_bind h
    obtain ⟨sA', esA', h'⟩ := exc_bind h'
    cases esA.symm.trans esA'
    obtain ⟨ow, eow, h⟩ := exc_bind h
    obtain ⟨ow', eow', h'⟩ := exc_bind h'
    cases eow.symm.trans eow'
    obtain ⟨H, eH, h⟩ := exc_bind h
    obtain ⟨H', eH', h'⟩ := exc_bind h'
    cases eH.symm.trans eH'
    obtain ⟨_, _, h⟩ := exc_bind h
    obtain ⟨_, _, h'⟩ := exc_bind h'
    cases h
    cases h'
    rfl

end VerifiableInference.PlanWritten

#print axioms VerifiableInference.PlanWritten.Attention.configO_plans
#print axioms VerifiableInference.PlanWritten.publicOfO_two
