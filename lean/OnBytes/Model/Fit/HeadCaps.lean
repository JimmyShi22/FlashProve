-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/Fit/HeadCaps.lean: the rounds that the planner lays for the output head's sub-proof
keep every entry of the plan small, at a setting within SetCap, for every public part that publicOf
returns.

Verify.linkRounds (OnBytes/Model/VerifySubproofs.lean) plans the head's link by
X.H.rounds X.hS X.HLy moment (OnBytes/Model/HeadRounds.lean), which is Params.headRounds at the
head's numbers. OnBytes/Params/Fit/FitSubHead.lean shows that headRounds keeps a property of entries
under two caps on these numbers. Here both caps are shown of what publicOf returns.

Statements.
  head_cap    the number of position bits is at most 2 ^ 40 (HeadWalk.lean: below 2 ^ 30).
  head_small  276 times the columns of all matrices of the head's smallness test is at most 2 ^ 45:
              the record has the matrices of a value of shapeF (HeadWalk.lean), whose own tests
              bound their number and their columns (ShapeFCaps.lean).
  head_keeps  for a setting s with SetCap s and every moment: Keeps s Small of the head's rounds.

Limits. Those of the files named. SetCap s is a premise. No toy: that publicOf returns at a
configuration is shown by no term here. Nothing on soundness or on hiding.
The program does not import this file.

-/
import OnBytes.Model.Fit.HeadWalk
import OnBytes.Model.Fit.ShapeFCaps
import OnBytes.Params.Fit.FitBase
import OnBytes.Params.Fit.FitSubHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Model.Verify
open OnBytes OnBytes.Model

variable {pol KL : ByteArray} {lay : Option ByteArray} {X : Public}

/-- The cap on the head's own numbers. -/
theorem head_cap (hX : publicOf pol KL lay = .ok X) : Params.HeadCap (X.H.own X.hS) :=
  ⟨Nat.le_of_lt (Nat.lt_of_lt_of_le (head_walk hX).2
    (Nat.pow_le_pow_right (by decide) (by decide)))⟩

/-- The cap on the head's smallness test. -/
theorem head_small (hX : publicOf pol KL lay = .ok X) : Params.SmallCap (smallSize X.H.tl) := by
  obtain ⟨_, _, tl1, hsh, hm, _⟩ := (head_walk hX).1
  have e : X.H.tl.foldColumns = tl1.foldColumns := by
    unfold HTailF2.foldColumns
    rw [hm]
  refine ⟨?_⟩
  show X.H.tl.foldColumns * 276 ≤ 2 ^ 45
  rw [e]
  exact small_cap hsh

/-- **The head's rounds keep every entry small.** -/
theorem head_keeps (hX : publicOf pol KL lay = .ok X) {s : Params.Setting} (S : Params.SetCap s)
    (moment : Nat) : Params.Keeps s Params.Small (X.H.rounds X.hS X.HLy moment) :=
  Params.keeps_headRounds (Params.subBase_small S) _ (head_cap hX) (head_small hX) moment

end OnBytes.Model.Verify

#print axioms OnBytes.Model.Verify.head_cap
#print axioms OnBytes.Model.Verify.head_small
#print axioms OnBytes.Model.Verify.head_keeps
