-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Conditions/BindsTold.lean: THE LAW OF BINDING FOR A TOLD RECORD (`told_binds_written`,
Johnson/Goal/Conditions/BindsLaw.lean) APPLIED: at a description's honest terms; then over the told
record of `descriptionOfDataOnBytes flashProveData`. Statements and proofs.

Why. `bindsWith_plain` (Johnson/Goal/Conditions/BindsPlain.lean) is reached by a long road: a
description with terms laid in, re-bound, with a coins' algorithm, at enumerations by digits; then
back. None of that stands in its statement. By the law the same is had at once, and the law's
fourteen premises are seen to be met together.

Main names.
  **`bindsWith_of_laws`** (namespace `VerifierAndGoals.Fit`): at a description's honest terms: from `BindLaws
    Q Z s tP q` alone: D's system of record with any type Coins for the committer's randomness and
    the written committer
    (written in Lean beside the IOP: a placeholder that corresponds to no program of the release)
    has opening-form binding at `epsBind honestBudget`. It overtakes `bindsWith_written`
    (BindsPlain.lean), which asks three premises more (binds, reach, fill).
  `epsBind_budget_at_70`: in numbers: at most 2^-114 up to 2^70 queries.
  **`bindsWith_plain_law`** (namespace `FlashProve`): `BindsWith (plainSystem …) ((T₀ Z).extractorOn
    (phiThe Z s)) (epsBind honestBudget)` at every Z whose files are read: SO THE LAW'S PREMISES ARE
    MET TOGETHER: it is not empty.
  **`bindsWith_plain_at_70`**: THE NUMBER IN THE STATEMENT: the same at the error "2^-114 while t ≤
    2^70; beyond: nothing".
  `never_does_not_bind`: A CONTROL: at an extractor that never gives some weights w, `plainSystem`
    has opening-form binding at no error below 1 at `count₀ Z`.

Every "there is": none, in premises or conclusions.
Limits. (1) Those of BindsLaw.lean: the fence; the verifier is idle; values, not algorithms. (2) The
eleven laws at `descriptionOfDataOnBytes flashProveData` are `bindLaws_the`'s; at another description they are owed anew.
(3) The limits of BindsPlain.lean on `plainSystem` (THE WRITTEN COMMITTER IS LAID BESIDE `descriptionOfDataOnBytes
flashProveData`, whose own honest side is hollow), on the hash function's names (THE CLOSED TERMS HERE
REACH CONCRETE HASH FUNCTIONS BY NAME: the same with the second hash function's place a letter:
Johnson/Goal/Conditions/BindsAtSecondHashFunction.lean) and on the numbers hold for `bindsWith_plain_law`.
Nothing on soundness, completeness or hiding; no program's commitment is spoken of.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Goal.Conditions.BindsPlain
import Johnson.Goal.Conditions.BindsLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section
open scoped ENNReal

namespace VerifierAndGoals.Fit
open VerifiableInference VerifiableInference.OnPublicFiles

variable {D : Description} (Q : HonestTerms D)

/-- **The law at a description's honest terms**: from `BindLaws` alone (of it, neither what it says
of the coins' algorithm nor Q's two enumerations, filling and prover are read). The system is D's
own system of record but for the committer's side. -/
theorem bindsWith_of_laws {Z : PublicFiles} {s : IntegerTransformer.Settings} {tP q : ℕ}
    (h : BindLaws Q Z s tP q) (b : (D.input Z (Q.c₀ Z) (Q.m₀ Z)).LeafBody) (Coins : Type)
    (rOf : Coins → (D.input Z (Q.c₀ Z) (Q.m₀ Z)).protocol.EncodingRandomness) (σOf : Coins → ℕ → Rom.Bits) (len : ℕ)
    (fence : ∀ x k, k < 2 ^ (D.input Z (Q.c₀ Z) (Q.m₀ Z)).queryLayout.depth → (σOf x k).length = len)
    (sample : RandomizedAlgorithm Coins)
    (prove : ModelWeights s → Coins → List Token → List Token → RandomizedAlgorithm D.Form) :
    BindsWith ((systemOfRecord D Z s).withRandomness Coins sample
      (fun w x => (Q.T Z).commitAtCoins b (Q.back Z s w) (rOf x) (σOf x)) prove)
      ((Q.T Z).extractorOn (Q.φ Z s)) (epsBind honestBudget) :=
  told_binds_written (Q.T Z)
    ((systemOfRecord D Z s).withRandomness Coins sample
      (fun w x => (Q.T Z).commitAtCoins b (Q.back Z s w) (rOf x) (σOf x)) prove)
    (Q.back Z s) (Q.φ Z s) b rOf σOf (fun _ _ _ => rfl) len fence h.wire h.section_ h.decodes
    h.noCoin h.asks h.once h.spare h.word h.code h.total tP h.reading honestBudget
    (le_trans (Nat.le_succ _) (le_trans (Nat.le_add_left _ q) h.number))

/-- In numbers: up to 2^70 queries that error is at most 2^-114. -/
theorem epsBind_budget_at_70 (t : ℕ) (ht : t ≤ 2 ^ 70) :
    epsBind honestBudget t ≤ (2 : ℝ≥0∞)⁻¹ ^ 114 :=
  le_trans (epsBind_mono honestBudget (Nat.le_add_right t 2)) (epsBind_at_70 t ht)

end VerifierAndGoals.Fit

namespace FlashProve
open VerifierAndGoals VerifierAndGoals.Fit FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles

/- Lean compares these by their names. -/
attribute [local irreducible] theCoding theKeyData theProofData protocolDataWellFormed theDeadPlan theKeyGate
  theProofGate theLinkGate theProvers theNamed LPFD.Full.GF riDigits fieldRows descriptionOfDataOnBytes T₀
  FlashProve.thePlan FlashProve.theItem

/-- **BINDING OVER THE DESCRIPTION's TOLD RECORD, BY THE LAW**: at every Z whose files are read (in
scope or not). The statement names no K, no W, no digits. On the proof's road: no W, no digits, no
re-bound description; one K (`placeHolderNumberCoins`) as the carrier of `bindLaws_the`, of which
the law reads nothing that hangs on K. The error has two queries less than `bindsWith_plain`'s
(Johnson/Goal/Conditions/BindsPlain.lean): no coins' algorithm is run. -/
theorem bindsWith_plain_law (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy) (hr : readFiles Z = .ok pp)
    (b : (R₀ Z).LeafBody) (sample : RandomizedAlgorithm (Coins₀ Z))
    (prove : ModelWeights (settingsOfRead pp) → Coins₀ Z → List Token → List Token →
      RandomizedAlgorithm flashProveDescription.Form) :
    BindsWith (plainSystem Z (settingsOfRead pp) b sample prove)
      ((T₀ Z).extractorOn (phiThe Z (settingsOfRead pp))) (epsBind honestBudget) := by
  unfold plainSystem
  rw [← T_the placeHolderNumberCoins Z]
  exact bindsWith_of_laws (theTerms placeHolderNumberCoins)
    (bindLaws_the placeHolderNumberCoins hE_the Z pp hr) b (Coins₀ Z) (fun x => x.1.1)
    (fun x => x.1.2) (R₀ Z).compilerParameters.sMT (fun x => x.2) sample prove

/-- **THE SAME WITH THE NUMBER IN THE STATEMENT**: while the bounds on the committer's and the
opener's queries add up to at most 2^70, the probability is at most 2^-114. (Beyond: nothing.) -/
theorem bindsWith_plain_at_70 (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy) (hr : readFiles Z = .ok pp)
    (b : (R₀ Z).LeafBody) (sample : RandomizedAlgorithm (Coins₀ Z))
    (prove : ModelWeights (settingsOfRead pp) → Coins₀ Z → List Token → List Token →
      RandomizedAlgorithm flashProveDescription.Form) :
    BindsWith (plainSystem Z (settingsOfRead pp) b sample prove)
      ((T₀ Z).extractorOn (phiThe Z (settingsOfRead pp)))
      fun t => if t ≤ 2 ^ 70 then (2 : ℝ≥0∞)⁻¹ ^ 114 else ⊤ :=
  (bindsWith_plain_law Z pp hr b sample prove).mono fun t => by
    by_cases ht : t ≤ 2 ^ 70
    · rw [if_pos ht]
      exact epsBind_budget_at_70 t ht
    · rw [if_neg ht]
      exact le_top

/-- **A CONTROL: AN EXTRACTOR THAT NEVER GIVES SOME WEIGHTS DOES NOT MEET IT**: at such an extractor
opening-form binding of `plainSystem` holds at no error below 1 at the written committer's count. By
`BindsWith.one_le_of_never` (Johnson/Top/FrontBinds.lean). -/
theorem never_does_not_bind (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy) (hr : readFiles Z = .ok pp)
    (b : (R₀ Z).LeafBody) (sample : RandomizedAlgorithm (Coins₀ Z))
    (prove : ModelWeights (settingsOfRead pp) → Coins₀ Z → List Token → List Token →
      RandomizedAlgorithm flashProveDescription.Form)
    (extractor : Commitment → QueryLog → Option (ModelWeights (settingsOfRead pp)))
    (ε : ℕ → ℝ≥0∞)
    (h : BindsWith (plainSystem Z (settingsOfRead pp) b sample prove) extractor ε)
    (w : ModelWeights (settingsOfRead pp)) (hn : ∀ c l, extractor c l ≠ some w) :
    1 ≤ ε (count₀ Z) :=
  h.one_le_of_never w hn (coins₀_nonempty Z).some
    (plain_count Z pp hr b w (coins₀_nonempty Z).some.1.1 (coins₀_nonempty Z).some.1.2)

end FlashProve

#print axioms VerifierAndGoals.Fit.bindsWith_of_laws
#print axioms VerifierAndGoals.Fit.epsBind_budget_at_70
#print axioms FlashProve.bindsWith_plain_law
#print axioms FlashProve.bindsWith_plain_at_70
#print axioms FlashProve.never_does_not_bind
