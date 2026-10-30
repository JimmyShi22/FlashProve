-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K3/Term/LookupOpenItemsWritten.lean: the kind "lookup" (K3): at each of
the fifty borders in front of a lookup, the open set that the first chain's `Thread` reads, the
forward rows' `fwdOpen`, is the library's table `openSets`. One closed fact, evaluated by the kernel,
with a control at which the same comparison says no.

What is shown.
  `forwardOpenIsTheTablesAt`: the comparison at one border, a test with code.
  `forwardOpenIsTheTablesAtTheLookups`: the comparison at the fifty borders, a test with code.
  `forwardOpenIsTheTablesAtTheLookups_holds`: it says yes.
  `forwardOpenDiffersAtTheChainsEnd`: the control: at the chain's last border it says no.
  `lookupOpenItemsAreTheTables`: at link l < 25, on the calls and on the digits: `fwdOpen` is the
    table's open set.
  `forwardOpenIsTheTablesBehindTheDigits`, `…_holds`: the comparison one border behind each lookup
    on the digits, and its yes.
  `lookupOpenItemsBehindTheDigitsAreTheTables`: the same equation there.

Hypotheses that remain. `linkBelow`: l < 25. Nothing else: the lists are the written ones.

How the proof goes. As at the kind K5 (Honest/K5/Law/Opened.lean): `opens` reads all borders in one
pass, `opens_get` ties it to `fwdOpen`, the kernel compares it with the table.

Limits. Lists alone: nothing is said of what an item means. At the full size's written list alone.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.Opened
import Johnson.Desc.Sound.MgAt.K3RidesRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Term
open VerifiableInference.Desc.First (openSets start)
open VerifiableInference.Desc.Sound.MgAt (borderOf)
open ProofFile.Honest.FirstRows (rows opens)

/-- The comparison at one border: the forward open set in one pass is the table's own. -/
def forwardOpenIsTheTablesAt (border : Nat) : Bool :=
  (opens P5J.At.links P5J.At.ps (start P5J.At.links))[border]? ==
    (openSets P5J.At.links P5J.At.ps (start P5J.At.links))[border]?

/-- The comparison at the fifty borders in front of a lookup. -/
def forwardOpenIsTheTablesAtTheLookups : Bool :=
  (List.range 25).all fun l =>
    forwardOpenIsTheTablesAt (borderOf l false) && forwardOpenIsTheTablesAt (borderOf l true)

/-- The comparison one border behind each lookup on the digits. -/
def forwardOpenIsTheTablesBehindTheDigits : Bool :=
  (List.range 25).all fun l => forwardOpenIsTheTablesAt (borderOf l true + 1)

set_option maxRecDepth 1000000 in
/-- **The test says yes.** No premise: a closed fact, by the kernel. -/
theorem forwardOpenIsTheTablesAtTheLookups_holds : forwardOpenIsTheTablesAtTheLookups = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- **The test behind the digits says yes.** No premise: a closed fact, by the kernel. -/
theorem forwardOpenIsTheTablesBehindTheDigits_holds :
    forwardOpenIsTheTablesBehindTheDigits = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A control: at the chain's last border the same comparison says no. No premise: a closed fact, by
the kernel. -/
theorem forwardOpenDiffersAtTheChainsEnd :
    forwardOpenIsTheTablesAt P5J.At.ps.length = false := by
  decide +kernel

/-- **At each border in front of a lookup `fwdOpen` is the table's open set.** Conditional on the
link's being below 25. -/
theorem lookupOpenItemsAreTheTables {l : Nat} (linkBelow : l < 25) (digits : Bool) :
    fwdOpen (start P5J.At.links) (rows P5J.At.links P5J.At.ps) (borderOf l digits) =
      ((openSets P5J.At.links P5J.At.ps (start P5J.At.links))[borderOf l digits]?).getD [] := by
  have both := List.all_eq_true.1 forwardOpenIsTheTablesAtTheLookups_holds l
    (List.mem_range.2 linkBelow)
  obtain ⟨onCalls, onDigits⟩ := Bool.and_eq_true_iff.1 both
  have compared : forwardOpenIsTheTablesAt (borderOf l digits) = true := by
    cases digits
    · exact onCalls
    · exact onDigits
  have place : P5J.At.ps[borderOf l digits]? = some (IM.k3Place l digits) :=
    K3Lot.k03_at_full l linkBelow digits
  have within : borderOf l digits ≤ P5J.At.ps.length :=
    Nat.le_of_lt (List.getElem?_eq_some_iff.1 place).1
  rw [← beq_iff_eq.1 compared, ProofFile.Honest.K5.opens_get _ _ _ _ within]
  rfl

/-- **One border behind a lookup on the digits `fwdOpen` is the table's open set too.** Conditional on
the link's being below 25. -/
theorem lookupOpenItemsBehindTheDigitsAreTheTables {l : Nat} (linkBelow : l < 25) :
    fwdOpen (start P5J.At.links) (rows P5J.At.links P5J.At.ps) (borderOf l true + 1) =
      ((openSets P5J.At.links P5J.At.ps (start P5J.At.links))[borderOf l true + 1]?).getD [] := by
  have compared := List.all_eq_true.1 forwardOpenIsTheTablesBehindTheDigits_holds l
    (List.mem_range.2 linkBelow)
  have place : P5J.At.ps[borderOf l true]? = some (IM.k3Place l true) :=
    K3Lot.k03_at_full l linkBelow true
  have within : borderOf l true + 1 ≤ P5J.At.ps.length :=
    (List.getElem?_eq_some_iff.1 place).1
  rw [← beq_iff_eq.1 compared, ProofFile.Honest.K5.opens_get _ _ _ _ within]
  rfl

end ProofFile.Honest.K3.Term

#print axioms ProofFile.Honest.K3.Term.forwardOpenIsTheTablesAtTheLookups_holds
#print axioms ProofFile.Honest.K3.Term.forwardOpenDiffersAtTheChainsEnd
#print axioms ProofFile.Honest.K3.Term.lookupOpenItemsAreTheTables
#print axioms ProofFile.Honest.K3.Term.forwardOpenIsTheTablesBehindTheDigits_holds
#print axioms ProofFile.Honest.K3.Term.lookupOpenItemsBehindTheDigitsAreTheTables
