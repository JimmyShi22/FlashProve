-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Conditions/BindsOwn.lean: THE COMMITTER OF `theWide K W` (the committer that this
folder's files lay into the description): ITS COUNT, AND WHAT THE EXTRACTOR GIVES FROM ITS LOG.
Statements and proofs: general in D and Q, then at `theWide K W` at every K and W, then at the
closed `theWideDigits`.

Why. `coins_enumerated_own` (Johnson/Goal/Conditions/WideDigits.lean) and `fixedCommit_theWide`
(Johnson/Goal/Conditions/BindsPlain.lean) tie `theWide`'s committer to the written one BY VALUES:
`theWide`'s asks up to two queries more (its coins' algorithm): enough for binding,
not for a count or a log. `extracts_at_coins` and `extracts_plain` speak of the written committer's
log. Here the same is said of `theWide`'s.

Main names.
  `commitCount_withTerms` (namespace `VerifierAndGoals.Fit`): the committer of `D.withTerms Q` asks at most q
    + (Q.tCommit Z tP + 1) queries: the coins' algorithm's, the told committer's, one for the key's
    code. (`commitWithin_withTerms`, Johnson/Goal/Conditions/DescribeTerms.lean, rounds this up to
    the honest side's budget.)
  `commitCount_of`: the same, the count a letter. `epsBind_value`: THE NAMED ERROR, WRITTEN OUT:
    `epsBind honestBudget (t + 2)` = 3 (t + 2^49 + 4)² / 2^256. `two_epsBind_at_70`: twice it (two
    openings) is at most 2^-113 up to 2^70 queries.
  `extracts_own_of`: where `D.withTerms Q` binds at ε: from a commitment of the committer of
    `D.withTerms Q` at any weights and randomness, and the queries of that run, its extractor gives
    the weights back, but with probability ε at that count. By `BindsWith.atRandomness`.
  `extractor_written`: the extractor over the re-bound description IS `(Q.T Z).extractorOn (Q.φ Z
    s)`.
  `extractor_theWide` (namespace `FlashProve`, as all below): the extractor of `theWide K W` IS `(T₀
    Z).extractorOn (phiThe Z s)`, at every K and W.
  `commitCount_theWide`: its committer asks at most 2 + `count₀ Z` queries.
  **`extracts_own`**: at every K and W, every Z in scope whose files are read, all weights and every
    randomness ρ: at every o: from `(theWide K W o).commit Z s w ρ` and that run's log the extractor
    gives w back, but with probability `epsBind honestBudget (2 + count₀ Z + 2)`.
    `extracts_own_digits`: at the closed term.

Limits. Those of BindsPlain.lean, but (2). `theWide K W` IS `descriptionOfDataOnBytes flashProveData` re-bound, with this
folder's committer and extractor laid in. THE HONEST SIDE OF `descriptionOfDataOnBytes flashProveData` ITSELF IS HOLLOW
(`theHonest := fixedCommitterAndProver`, Johnson/Goal/Description/Honest.lean: no randomness, a commitment of
zeros). `theWide K W` does not read its argument o. ρ is K's randomness: at `digitCoins` a number;
how far ρ reaches is `coins_enumerated_own`'s matter. The honest side at the closed term is hollow
but for the committer. Nothing on completeness or hiding.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Goal.Conditions.BindsPlain

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section
open scoped ENNReal

namespace VerifierAndGoals.Fit
open VerifiableInference VerifiableInference.OnPublicFiles

variable {D : Description} {Q : HonestTerms D}

/-- **The count of the committer of `D.withTerms Q`.** -/
theorem commitCount_withTerms {Z : PublicFiles} {s : IntegerTransformer.Settings} {tP q : ℕ}
    (h : BindLaws Q Z s tP q) (w : ModelWeights s) (ρ : Q.Rand) :
    ((D.withTerms Q).commit Z s w ρ).toRandomized.QueryBound (q + (Q.tCommit Z tP + 1)) :=
  queryBound_andThen (Q.coins Z ρ) _ q (Q.tCommit Z tP + 1) (h.coinsWithin ρ) fun n =>
    queryBound_commit_systemOn (Q.T Z) (Q.ri Z) (Q.sl Z) (Q.b₀ Z) (Q.proveT Z) (Q.back Z s)
      (modelNextToken s) tP h.reading w n

/-- The same, the count a letter. -/
theorem commitCount_of {Z : PublicFiles} {s : IntegerTransformer.Settings} {tP q : ℕ}
    (h : BindLaws Q Z s tP q) (c : ℕ) (hc : q + (Q.tCommit Z tP + 1) = c) (w : ModelWeights s)
    (ρ : Q.Rand) : ((D.withTerms Q).commit Z s w ρ).toRandomized.QueryBound c :=
  hc ▸ commitCount_withTerms h w ρ

/-- The named error, written out. -/
theorem epsBind_value (t : ℕ) :
    epsBind honestBudget (t + 2) = ((3 * (t + 2 ^ 49 + 4) ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  unfold epsBind honestBudget
  have e : t + 2 + 2 * 2 ^ 48 + 2 = t + 2 ^ 49 + 4 := by
    have e1 : (2 : ℕ) ^ 49 = 2 * 2 ^ 48 := by norm_num
    omega
  rw [e]

/-- In numbers: up to 2^70 queries twice the named error (two openings) is at most 2^-113. -/
theorem two_epsBind_at_70 (t : ℕ) (ht : t ≤ 2 ^ 70) :
    2 * epsBind honestBudget (t + 2) ≤ (2 : ℝ≥0∞)⁻¹ ^ 113 := by
  refine le_trans (mul_le_mul_right (epsBind_at_70 t ht) 2) (le_of_eq ?_)
  rw [show (114 : ℕ) = 113 + 1 from rfl, pow_succ, mul_left_comm,
    ENNReal.mul_inv_cancel (by norm_num) (by norm_num), mul_one]

/-- **From that committer's commitment and log the extractor gives the weights back**, but with
probability ε at that count. -/
theorem extracts_own_of {Z : PublicFiles} {s : IntegerTransformer.Settings} {tP q : ℕ}
    (h : BindLaws Q Z s tP q) (ε : ℕ → ℝ≥0∞)
    (binds : BindsWith (systemOfRecord (D.withTerms Q) Z s) ((D.withTerms Q).extractor Z s) ε)
    (w : ModelWeights s) (ρ : Q.Rand) :
    Prob ((D.withTerms Q).commit Z s w ρ).toRandomized.withQueryLog
        {c | (D.withTerms Q).extractor Z s c.1 c.2 ≠ some w}
      ≤ ε (q + (Q.tCommit Z tP + 1)) :=
  binds.atRandomness w ρ (q + (Q.tCommit Z tP + 1)) (commitCount_withTerms h w ρ)

/-- **The extractor over the re-bound description, written out.** -/
theorem extractor_written (Q : HonestTerms D) (n : PublicFiles → ℕ)
    (coins' : (Z : PublicFiles) → Q.Rand → DeterministicAlgorithm (Fin (n Z + 1))) (Z : PublicFiles)
    (s : IntegerTransformer.Settings) :
    ((D.reBound n).withTerms (Q.reBound n coins')).extractor Z s =
      (Q.T Z).extractorOn (Q.φ Z s) := by
  rw [LayoutsByPublicReading.extractorOn_eq]
  rfl

end VerifierAndGoals.Fit

namespace FlashProve
open VerifierAndGoals VerifierAndGoals.Fit FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles

/- Lean compares these by their names. -/
attribute [local irreducible] theCoding theKeyData theProofData protocolDataWellFormed theDeadPlan theKeyGate
  theProofGate theLinkGate theProvers theNamed LPFD.Full.GF riDigits fieldRows descriptionOfDataOnBytes T₀
  FlashProve.thePlan FlashProve.theItem

variable (K : TheCoins) (W : WideCoins K)

/-- **`theWide`'s extractor, written out**: at every K and W. -/
theorem extractor_theWide (o : SecondHashFunctionType) (Z : PublicFiles) (s : IntegerTransformer.Settings) :
    (theWide K W o).extractor Z s = (T₀ Z).extractorOn (phiThe Z s) := by
  rw [← T_the K Z]
  exact extractor_written (theTerms K) W.bound (fun Z => coinsAnchor Z (K.shape Z) (W.gen Z)) Z s

/-- The count of the honest side's terms over the re-bound description is `count₀`. -/
theorem count_theWide (Z : PublicFiles) : (theWideTerms K W).tCommit Z 8 + 1 = count₀ Z := rfl

/- From here on Lean compares that number by its name. -/
attribute [local irreducible] count₀

/-- `theWide`'s committer asks at most 2 + `count₀ Z` queries: two above the bound on the written
one. -/
theorem commitCount_theWide (o : SecondHashFunctionType) (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy)
    (hr : readFiles Z = .ok pp) (w : ModelWeights (settingsOfRead pp)) (ρ : K.Rand) :
    ((theWide K W o).commit Z (settingsOfRead pp) w ρ).toRandomized.QueryBound
      (2 + count₀ Z) :=
  commitCount_of (bindLaws_wide K W Z pp hr) (2 + count₀ Z)
    (congrArg (fun c => 2 + c) (count_theWide K W Z)) w ρ

/-- **FROM THE COMMITMENT AND THE LOG OF `theWide`'s COMMITTER THE EXTRACTOR GIVES THE WEIGHTS
BACK**,
but with probability the named error at that run's count: at every K and W. -/
theorem extracts_own (o : SecondHashFunctionType) (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy) (hs : InScope Z = true)
    (hr : readFiles Z = .ok pp) (w : ModelWeights (settingsOfRead pp)) (ρ : K.Rand) :
    Prob ((theWide K W o).commit Z (settingsOfRead pp) w ρ).toRandomized.withQueryLog
        {c | (T₀ Z).extractorOn (phiThe Z (settingsOfRead pp)) c.1 c.2 ≠ some w}
      ≤ epsBind honestBudget (2 + count₀ Z + 2) := by
  have h := extracts_own_of (bindLaws_wide K W Z pp hr) (fun t => epsBind honestBudget (t + 2))
    (bindsAt_withTerms (theWideTerms K W) 8 2 (fun Z pp _ h₂ => bindLaws_wide K W Z pp h₂) Z pp hs
      hr).2 w ρ
  rw [count_theWide K W Z] at h
  rw [← extractor_theWide K W o Z (settingsOfRead pp)]
  exact h

/-- At the closed term. -/
theorem extracts_own_digits (o : SecondHashFunctionType) (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy) (hs : InScope Z = true)
    (hr : readFiles Z = .ok pp) (w : ModelWeights (settingsOfRead pp)) (ρ : ℕ) :
    Prob ((theWideDigits o).commit Z (settingsOfRead pp) w
        ρ).toRandomized.withQueryLog
        {c | (T₀ Z).extractorOn (phiThe Z (settingsOfRead pp)) c.1 c.2 ≠ some w}
      ≤ epsBind honestBudget (2 + count₀ Z + 2) :=
  extracts_own digitCoins digitWide o Z pp hs hr w ρ

end FlashProve

#print axioms VerifierAndGoals.Fit.commitCount_withTerms
#print axioms VerifierAndGoals.Fit.commitCount_of
#print axioms VerifierAndGoals.Fit.epsBind_value
#print axioms VerifierAndGoals.Fit.two_epsBind_at_70
#print axioms VerifierAndGoals.Fit.extracts_own_of
#print axioms VerifierAndGoals.Fit.extractor_written
#print axioms FlashProve.extractor_theWide
#print axioms FlashProve.count_theWide
#print axioms FlashProve.commitCount_theWide
#print axioms FlashProve.extracts_own
#print axioms FlashProve.extracts_own_digits
