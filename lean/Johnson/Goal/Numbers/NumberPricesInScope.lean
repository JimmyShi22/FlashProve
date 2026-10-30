-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Goal/Numbers/NumberPricesInScope.lean: the error bounds of the rounds of all three files, at
the lists of rounds that the planner itself made: in the public part that the IOP as written in Lean
for the proof file computes (`pureRoad.pub`, Johnson/Desc/ProofFile/OnlineDescriptionPublicPart.lean), at all public
files in the goals' scope. For the proof file's three lists under the yes of the test on what the
planner configured (`madePinnedAt`, Johnson/Desc/Ok/PlanWritten/MadeTestLaws.lean); for the key
file's three and a copy's file's one with no test. For every o in the second hash function's place.

What it says of a round. `PricedAt d r` (Johnson/Desc/Ok/NumberPrices/AtData.lean), of a written
round's data d and the planner's round r at its place: d bears r's entry, and r's error bound, after
the round's proof of work, is a share of 2 ^ -128 in the three forms that the laws on counts call.
`PricedRounds D P₁ P₂ P₃`: so place by place along a file's three chains. `EntryPricedAt P`
(Johnson/Desc/Ok/NumberPrices/EntryAtWritten.lean): the like for a copy's file's one chain.
`Desc.chainAll w P` (Johnson/Desc/MadeOk.lean): the public test on one list, at w bits of proof of
work at most.

How. Three closed statements at written values (`proofPricesWritten`,
Johnson/Desc/Ok/NumberPrices/ProofAtWritten.lean; `keyPricesWritten`, KeyAtWritten.lean;
`entryPricesWritten`, EntryAtWritten.lean) are carried to the planner's own lists by equations:
`made_in_scope` (Johnson/Goal/Numbers/MadeInScope.lean); `keyPlans_at_pure`
(Johnson/Goal/Numbers/KeyPlansAtPure.lean); `entry_in_scope`, here.

Statements.
  `PricesAtMade c`: a definition: the three parts, at what the planner configured.
  `prices_of_free`: where the four fields that do not hang on the digest are the written value,
    `PricesAtMade` holds.
  **`number_prices_in_scope`**: in scope, under the test's yes.
  `entry_in_scope`: in scope the planner's list for a copy's file is the written one; no test is
    asked. `entryPriced_in_scope`, `keyPricedAll_in_scope`: so the parts for a copy's file and for
    the key file hold with no test.
No evaluation is made here.

FOUR OF THE 67383 ROUNDS OF THE SEVEN LISTS ARE NOT SPOKEN OF BY `PricedAt`. Two are the last round,
under the name "SEAL", of the proof file's first list and of the key file's first list: the first
clause of `PricedRounds` runs against the list without its last, and the written data have no round
for it. Two are the entry of the out-of-domain (OOD) sample on the committed table (these files call
it the record; its name in a list is "RECORD"): one in the key file's first list, one at the head of
a copy's file's list: `chainRounds` leaves every entry of that name out. `Desc.chainAll` says yes at
all seven whole lists; what it asks at these four was not read for this file.

Limits. `PricedRounds` is the first premise of a call of the laws that end in a bound on a sum of
counts (`errBelow_F`, `errBelow_sum`,
Johnson/Desc/Ok/NumberPrices/CoversStretch.lean [not in this library]), not the call: whoever calls
still owes that the round's error bound covers its own count (`Covers`). That the data of the IOP as
written in Lean are `writtenPFull`, `writtenKFull` and `frD.ds` is not said here. That a verifier
asks the test is not said here. Each statement has a member only where the public part is computed,
and the first two only where the test says yes: the reference run's to show. Nothing on soundness.

-/
import Johnson.Goal.Numbers.MadeInScope
import Johnson.Desc.Ok.NumberPrices.EntryAtWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.PlanWritten.Joined
open VerifiableInference VerifiableInference.Number VerifiableInference.PlanWritten
open VerifiableInference.Number.ByRuns
open OnBytes OnBytes.Params OnBytes.Flat.Held Johnson.G Johnson.G.MadeFree Lk6.AtPlan

/-- **The error bounds of all three files' rounds, at what the planner configured.** -/
def PricesAtMade (c : Configured) : Prop :=
  (∃ F₁ F₂ F₃, c.proof = [F₁, F₂, F₃] ∧ PricedRounds writtenPFull F₁ F₂ F₃ ∧
      Desc.chainAll 20 F₁ = true ∧ Desc.chainAll 28 F₂ = true ∧ Desc.chainAll 20 F₃ = true) ∧
    (∃ K₁ K₂ K₃, c.key = [K₁, K₂, K₃] ∧ PricedRounds writtenKFull K₁ K₂ K₃ ∧
      Desc.chainAll 32 K₁ = true ∧ Desc.chainAll 32 K₂ = true ∧ Desc.chainAll 32 K₃ = true) ∧
    EntryPricedAt c.entry ∧ Desc.chainAll 32 c.entry = true

/-- Where the four fields are the written value. -/
theorem prices_of_free {c : Configured} (h : freeOf c = writtenMade) : PricesAtMade c := by
  have hp : c.proof = [proofThree.A.plan, proofThree.B.plan, proofThree.C.plan] :=
    congrArg Free.proof h
  have hk : c.key = [keyThree.A.plan, keyThree.B.plan, keyThree.C.plan] := congrArg Free.key h
  have he : c.entry = pricedEntryFull := congrArg Free.entry h
  refine ⟨⟨_, _, _, hp, proofPricedFull, proofAll_full⟩, ⟨_, _, _, hk, keyPricedFull, keyAll_full⟩,
    ?_⟩
  rw [he]
  exact entryPricesWritten

section
variable {o : ProofFile.SecondHashFunctionArgument} {W : VerifierAndGoals.PublicFiles} {Z : ProofFile.Pub}

/-- **IN SCOPE, UNDER THE TEST's YES: THE ERROR BOUNDS HOLD AT THE PLANNER's OWN SEVEN LISTS.** -/
theorem number_prices_in_scope (hW : VerifierAndGoals.InScope W = true)
    (h : ProofFile.pureRoad.pub o W.pol W.lay W.KL = .ok Z)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true) :
    PricesAtMade Z.p.chains.made :=
  prices_of_free (made_in_scope hW h hy)

/-- **In scope the planner's list for a copy's file is the written one.** No test is asked. -/
theorem entry_in_scope (hW : VerifierAndGoals.InScope W = true)
    (h : ProofFile.pureRoad.pub o W.pol W.lay W.KL = .ok Z) :
    Z.p.chains.made.entry = pricedEntryFull := by
  obtain ⟨v, hv⟩ := inScope_policy hW
  rw [hv] at h
  obtain ⟨ls, _, hc, _, _⟩ := ProofFile.Law.pub_configure h
  obtain ⟨hf, _⟩ := args_of_steps (publicSteps_of_O (ProofFile.Law.pub_public h))
  rw [hf] at hc
  obtain ⟨hz, _, _, _, _, _, _, _, _, ae⟩ := configure_plans hc
  obtain ⟨e2, T, hT, hL⟩ := sized_link hz
  obtain rfl : T = recordTable := Option.some.inj (hT.symm.trans record_table)
  have e56 : (Z.p.chains.made.sized.link, Z.p.chains.made.sized.entryCodes) =
      (writtenLink, recordCodes) := Option.some.inj (hL.symm.trans writtenLink_sized)
  have e5 : Z.p.chains.made.sized.link = writtenLink := congrArg Prod.fst e56
  have e2' : Z.p.chains.made.sized.set = recordSet := e2
  rw [e2', e5] at ae
  exact Except.ok.inj (ae.symm.trans entry_written)

theorem entryPriced_in_scope (hW : VerifierAndGoals.InScope W = true)
    (h : ProofFile.pureRoad.pub o W.pol W.lay W.KL = .ok Z) :
    EntryPricedAt Z.p.chains.made.entry ∧ Desc.chainAll 32 Z.p.chains.made.entry = true := by
  rw [entry_in_scope hW h]
  exact entryPricesWritten

theorem keyPricedAll_in_scope (hW : VerifierAndGoals.InScope W = true)
    (h : ProofFile.pureRoad.pub o W.pol W.lay W.KL = .ok Z) :
    ∃ K₁ K₂ K₃, Z.p.chains.made.key = [K₁, K₂, K₃] ∧ PricedRounds writtenKFull K₁ K₂ K₃ ∧
      Desc.chainAll 32 K₁ = true ∧ Desc.chainAll 32 K₂ = true ∧ Desc.chainAll 32 K₃ = true :=
  ⟨_, _, _, keyPlans_at_pure hW h, keyPricedFull, keyAll_full⟩

end

end VerifiableInference.PlanWritten.Joined

#print axioms VerifiableInference.PlanWritten.Joined.prices_of_free
#print axioms VerifiableInference.PlanWritten.Joined.number_prices_in_scope
#print axioms VerifiableInference.PlanWritten.Joined.entry_in_scope
#print axioms VerifiableInference.PlanWritten.Joined.entryPriced_in_scope
#print axioms VerifiableInference.PlanWritten.Joined.keyPricedAll_in_scope
