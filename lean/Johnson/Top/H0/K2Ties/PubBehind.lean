-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Ties/PubBehind.lean: BEHIND A CODE SWITCH NO OPEN PUBLIC ITEM HAS A SENTENCE BESIDE
ITS
TEST, at the composed meaning of the open claims over its closed base (`mgAll D mgBase`,
Johnson/Desc/Sound/MgBase.lean). One definition, four theorems. A law file: no sub-protocol imports
it.

Why. The table's promise at a border ends in: what each open public item says beside its test holds
(`Meaning.pubP`). Whoever shows the promise behind a code switch (the second tie) owes that clause.
Over the closed base the composed meaning's `pubP` says something at three sorts of item alone
(left,
leftOn, hasRow); at every item to which the table `First.saysNone` (Johnson/Desc/First/AllSaid.lean)
gives "no sentence is meant" it holds outright (`mgAll_pubP_said`).

What is said.
  `saidBehindB links ps k`: every public item that is open behind sub-protocol number k, by the
  closed
    list of extra public tests (`mgMore`, Johnson/Desc/Sound/MgAllAt.lean), is one to which that
    table
    gives "no sentence is meant".
  `pubP_behind`: where the test accepts, the clause holds behind k, AT EVERY STATE.
  `said_small`, `said_full`: BY LEAN's KERNEL the test accepts at all 5 | 25 code switches of the
  two
    written lists of segments.
  `said_can_fail`: a negative test: behind sub-protocol number 3 of the small list the test refuses.

Limits. At the base `mgBase` alone. The two lists of segments are the written ones. No soundness is
claimed.

Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.Sound.MgBase
import Johnson.Top.H0.K2Ties.Table

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Ties
open VerifiableInference.Desc (Place Wit)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (ModelPart Pub pubSets saysNone flatPlacesOf)

/-- Every public item that is open behind sub-protocol number k is one without a sentence. -/
def saidBehindB (links : List ModelPart) (ps : List Place) (k : ℕ) : Bool :=
  ((pubSets mgMore links ps)[k + 1]?.getD []).all fun q => (saysNone q).isSome

/-- **Where the test accepts, what the open public items say beside their tests holds behind k.** -/
theorem pubP_behind {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
    (D : MgData Xi P Tok rows cols nR X) (links : List ModelPart) (ps : List Place) (k : ℕ)
    (h : saidBehindB links ps k = true) (a : P × First.S) :
    ∀ q ∈ (pubSets (mgAll D mgBase).more links ps)[k + 1]?.getD [], (mgAll D mgBase).pubP q a := by
  rw [mgAll_more_base]
  intro q hq
  exact mgAll_pubP_said D q a (List.all_eq_true.1 h q hq)

theorem said_small : (switches 4).all (fun x =>
    saidBehindB linksSmall (flatPlacesOf linksSmall true) x.1) = true := by decide +kernel

theorem said_full : (switches 24).all (fun x =>
    saidBehindB linksFull (flatPlacesOf linksFull true) x.1) = true := by decide +kernel

/-- A negative test: behind sub-protocol number 3 of the small list an open public item is none of
those to which the table gives "no sentence is meant": the test refuses. -/
theorem said_can_fail :
    saidBehindB linksSmall (flatPlacesOf linksSmall true) 3 = false := by decide +kernel

end VerifiableInference.Desc.First.K2Ties

#print axioms VerifiableInference.Desc.First.K2Ties.said_can_fail
#print axioms VerifiableInference.Desc.First.K2Ties.pubP_behind
#print axioms VerifiableInference.Desc.First.K2Ties.said_small
#print axioms VerifiableInference.Desc.First.K2Ties.said_full
