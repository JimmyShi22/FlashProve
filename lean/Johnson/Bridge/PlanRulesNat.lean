-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Bridge/PlanRulesNat.lean: Rules by name, for the rounds of a plan whose count is a function
of the entry's own numbers: a rule has a name, a guard and a slot, both as functions of the entry;
every entry of a list must have a name that is held elsewhere or a rule at which it passes. An entry
without a rule is refused: a form of round without a price shows as a no. Comparisons of
natural numbers; it imports Johnson/Bridge/PlanOkNat.lean alone: no Mathlib, no file on codes.
Johnson/Bridge/PlanRulesNatEq.lean [not in this library] has what a yes gives.

This file holds nothing on codes. It lies in this folder because it is part of one machine with
Johnson/Bridge/PlanOkNat.lean.
Like the files of Cb/Bridge/, this file was written by AI systems that had seen ArkLib's source
(https://github.com/Verified-zkEVM/ArkLib, a copy marked as
commit 2817d8c7d2f28d706b17f8de0f885880d0b2eb13; Copyright ArkLib Contributors, Apache-2.0), so it
does not count as written independently of it. It takes no text from ArkLib or from ThirdParty/ and
follows no file of theirs.

Main names:
  `Rule`: a name; a guard on the entry; the slot of an entry of that name.
  `ruleOf rules e`: the first rule of the entry's name.
  `ruleOk rules e`: the entry has a rule, passes its guard, and passes `slotOk` at its slot.
  `rulesOk held rules es`: every entry's name is among `held`, or the entry passes `ruleOk`.
  `nineNames`: the names that `planOk` reads.

Limits: this file proves nothing and writes no rule. A rule's slot is made of the entry itself: what
it takes off the entry it does not test; that a rule's count bounds the number of bad challenges of
a block's round is the law of whoever gives the rule. A name among `held` is passed over here: that
every entry of that name is held by another test is said for `nineNames` and `planOk` in
Johnson/Bridge/PlanRulesNatEq.lean [not in this library] (`nine_held`), for no other list. Where an
entry stands is not
asked. The cost: a rule's guard and the slot's equalities stand in front of the comparison; what a
rule takes off the entry reaches a power unheld. No sum over rounds.

-/
import Johnson.Bridge.PlanOkNat

set_option autoImplicit false

namespace Johnson.Bridge.OkNat
open OnBytes OnBytes.Params

/-- A rule: a name; a guard on the entry; the slot of an entry of that name. -/
structure Rule where
  name : String
  guard : Fmt.Entry → Bool
  slot : Fmt.Entry → Slot

/-- The first rule of the entry's name. -/
def ruleOf (rules : List Rule) (e : Fmt.Entry) : Option Rule :=
  rules.find? fun r => r.name == e.name

/-- The entry has a rule, passes its guard, and passes at its slot. No rule: no. -/
def ruleOk (rules : List Rule) (e : Fmt.Entry) : Bool :=
  match ruleOf rules e with
  | none => false
  | some r => r.guard e && slotOk e (r.slot e)

/-- Every entry's name is held elsewhere, or the entry passes at its rule. -/
def rulesOk (held : List String) (rules : List Rule) (es : List Fmt.Entry) : Bool :=
  es.all fun e => held.contains e.name || ruleOk rules e

/-- The names that `planOk` reads. -/
def nineNames : List String :=
  ["BAT", "FOLD epsilon", "FOLD round", "CS", "BASE lambda", "BASE", "SEND seed", "LOC",
    "LIN point"]

end Johnson.Bridge.OkNat

#print axioms Johnson.Bridge.OkNat.rulesOk
