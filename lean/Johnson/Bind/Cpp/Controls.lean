-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Bind/Cpp/Controls.lean: NEGATIVE TESTS AT THE CONCLUSIONS: a committer that does not feel
the weights, laid into the commit field of the description theCpp (Johnson/Bind/Cpp/Defs.lean),
FAILS the conclusions that follow from the tie: the opening form of binding (BindsWith), "nobody
opens one commitment to two different weights" (NoTwoOpenings) and correctness of extraction
(ExtractsCommittedWeights: all three in VerifiableInference/MoreStatements.lean), the last also in
its form at every randomness. So these conclusions are not had for nothing, and the tie, from which
they follow, buys something.
"Binding", "binds" in this file: the opening form, BindsWith: nobody opens a commitment, by naming
weights and randomness from which the committer gives it, to weights that the extractor does not
give.

Why. Johnson/Bind/Cpp/Guards.lean shows that a constant committer fails THE TIE (constant_fails) and
states two further negative tests as definitions of propositions: BlindDoesNotBind (at the
conclusion) and BlindFails (at the tie). Both are proved here, to their letter.

Main names.
  General in the argument system (namespace Bind.Control):
  `one_le_of_blindValue`: the library's negative test `BindsWith.one_le_of_blind`
    (Johnson/Top/FrontBinds.lean) asks that the committer is ONE ALGORITHM at two different weights.
    Here it is asked only that its VALUE is one at every hash function. The proof is that theorem's
    own, with its tools.
  `one_le_add_of_two`, `one_le_add_of_blind`, `one_le_add_of_blind_at`: where the committer is one
    algorithm at two different weights, correctness of extraction holds at no error below 1/2: with
    the randomness sampled, and at one fixed randomness.
  Beside them (the same namespace): `two_weights`: at valid settings there are two different weights
    (the all-zero ones, and weights whose embedding has an entry that is not 0);
    `not_one_le_quarter`, `not_one_le_two_quarters`.
  At theCpp (namespace Bind.Cpp):
  `BlindAt T sh p l K`: at this shape and these files the committer T.id does not read the table's
    plain entries. `Blind T`: at every shape and all files.
  `blindTwin g`, `blind_blindTwin`, `count_blindTwin`: A MEMBER: the running committer of
    Johnson/Bind/Twin.lean, run at the table whose plain entries are all 0.
  `id_blind`, `commitAt_blind`, `commit_blind`: so the commit field is one algorithm at all weights.
  `bitsBinding_le_quarter`, `not_one_le_bitsBinding`, `not_one_le_two_bitsBinding`: the errors of
    the conclusions are small.
  `exists_prove`: a prover to lay into theCpp where a statement names none.
  **`blindDoesNotBind` : BlindDoesNotBind** · `blindAt_fails` · **`blindFails` : BlindFails**.
  `blind_twoOpenings`, `blind_extracts`, `blind_extracts_at`: the other conclusions, at a committer
    that is blind at the full size's shape and Z's files.
  `blindTwin_fails`: at the member, each conclusion at its own error.

Limits. Negative tests alone: they say where the notions fail, and nothing on where they hold. The
errors at which the notions fail: every error below 1 at the committer's number of queries
(BindsWith, NoTwoOpenings), every error below 1/2 (ExtractsCommittedWeights). The adversary of the
first negative test computes the extractor's answer from its own commitment and log: that costs no
query, and the game bounds queries alone. That these negative tests part a blind committer from the
running one is shown only where the running one meets the tie (SaltAt Z:
Johnson/Bind/Cpp/TheTie.lean). blindAt_fails, blindFails, blindDoesNotBind and blind_twoOpenings ask
the count (CountAt: at most 2^35 queries): a blind committer that asks more is not reached by them;
blind_extracts and blind_extracts_at do not ask it. BlindAt is sameness of ALGORITHMS; sameness of
VALUES alone is reached for BindsWith (blindDoesNotBind, one_le_of_blindValue), not for the tie or
for correctness of extraction. Nothing on any program. No cheating prover, proof or transcript is
made here.
Terms: lean/GLOSSARY.md, and "Words" in the head of Johnson/Bind/Cpp/Defs.lean.

-/
import Johnson.Bind.Cpp.Guards
import Johnson.Bind.Cpp.AtTwin
import Johnson.Top.FrontBinds
import IntegerModel.Arrays.SameTensors
import VerifiableInference.ProbabilityGuards
import VerifiableInference.StatementsNonEmpty
import Ladder.BitsTies
import Ladder.Ties

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

open scoped ENNReal

noncomputable section

/-! ## 1. General in the argument system -/

namespace Bind.Control
open VerifiableInference VerifiableInference.RandomizedAlgorithm

/-- **A negative test.** A committer whose value is one and the same at two different weights, under
the randomness ρ and at every hash function, with at most tS queries at the first: then binding
holds at no error below 1 at tS, whatever the extractor. The adversary runs the committer at the
first weights, computes the extractor's answer from its own commitment and log, which costs no
query, and opens to whichever of the two the extractor does not give. -/
theorem one_le_of_blindValue {system : ArgumentSystem}
    {extractor : Commitment → QueryLog → Option system.Weights} {ε : ℕ → ℝ≥0∞}
    (h : BindsWith system extractor ε) {w w' : system.Weights} (hne : w ≠ w')
    (ρ : system.CommitmentRandomness)
    (hc : ∀ hash, (system.commit w ρ).evaluate hash = (system.commit w' ρ).evaluate hash) {tS : ℕ}
    (hS : (system.commit w ρ).toRandomized.QueryBound tS) : 1 ≤ ε tS := by
  classical
  let pick : Commitment → QueryLog → system.Weights :=
    fun c l => if extractor c l = some w then w' else w
  have key := h tS 0 system.Weights ((system.commit w ρ).picking pick []).toRandomized
    (DeterministicAlgorithm.queryBound_picking pick _ [] tS hS)
    (fun state => RandomizedAlgorithm.done (state, ρ)) fun _ => trivial
  refine le_trans (le_of_eq (Eq.symm ?_)) key
  refine Prob_eq_one _ _ fun hash => ?_
  show ZKCP.prob ((((system.commit w ρ).picking pick []).toRandomized.withQueryLog.bind fun c =>
      (RandomizedAlgorithm.done (c.1.2, ρ)).bind fun y =>
        (system.commit y.1 y.2).toRandomized.bind fun recomputed =>
          RandomizedAlgorithm.done (extractor c.1.1 c.2, c.1.1, y.1, recomputed)).run hash) _ = 1
  rw [run_bind, run_withQueryLog_toRandomized, PMF.pure_bind,
    DeterministicAlgorithm.evaluate_picking, DeterministicAlgorithm.logUnder_picking, run_bind,
    run_done, PMF.pure_bind, run_bind, DeterministicAlgorithm.run_toRandomized, PMF.pure_bind,
    run_done, ZKCP.prob_pure]
  refine if_pos ⟨?_, ?_⟩
  · show (system.commit (pick _ _) ρ).evaluate hash = (system.commit w ρ).evaluate hash
    by_cases e : extractor ((system.commit w ρ).evaluate hash)
        ([].reverse ++ (system.commit w ρ).logUnder hash) = some w
    · rw [show pick _ _ = w' from if_pos e]
      exact (hc hash).symm
    · rw [show pick _ _ = w from if_neg e]
  · show extractor ((system.commit w ρ).evaluate hash) ((system.commit w ρ).logUnder hash) ≠
      some (pick _ _)
    by_cases e : extractor ((system.commit w ρ).evaluate hash)
        ([].reverse ++ (system.commit w ρ).logUnder hash) = some w
    · rw [show pick _ _ = w' from if_pos e]
      intro e'
      exact hne (Option.some.inj (e.symm.trans e'))
    · rw [show pick _ _ = w from if_neg e]
      exact e

/-- In one experiment, "the answer read off the outcome is not a" and "… is not b", for two
different a and b, cannot both have a probability below 1/2: no answer is both. -/
theorem one_le_add_of_two {γ β : Type} (experiment : RandomizedAlgorithm γ) (f : γ → Option β)
    {a b : β} (hne : a ≠ b) {α : ℝ≥0∞} (ha : Prob experiment {x | f x ≠ some a} ≤ α)
    (hb : Prob experiment {x | f x ≠ some b} ≤ α) : 1 ≤ α + α := by
  rw [← Prob_add_compl experiment {x | f x ≠ some a}]
  refine add_le_add ha (le_trans (Prob_mono experiment fun x hx => ?_) hb)
  have hx' : ¬ f x ≠ some a := hx
  show f x ≠ some b
  intro e
  exact hne (Option.some.inj ((not_not.1 hx').symm.trans e))

/-- **A negative test.** A committer that is one and the same algorithm at two different weights, at
all randomness: then correctness of extraction holds at no error below 1/2, whatever the extractor:
the two experiments are one, and no answer of the extractor is both weights. -/
theorem one_le_add_of_blind {system : ArgumentSystem}
    {extractor : Commitment → QueryLog → Option system.Weights} {α : ℝ≥0∞}
    (h : ExtractsCommittedWeights system extractor α) {w w' : system.Weights} (hne : w ≠ w')
    (hc : ∀ ρ, system.commit w ρ = system.commit w' ρ) : 1 ≤ α + α := by
  have hw := h w
  have hw' := h w'
  rw [show (fun randomness => (system.commit w' randomness).toRandomized) =
    fun randomness => (system.commit w randomness).toRandomized from
      funext fun ρ => by rw [hc ρ]] at hw'
  exact one_le_add_of_two _ id hne hw hw'

/-- **A negative test.** The same at one fixed randomness ρ: a committer that is one algorithm at
two different weights under ρ: "from the commitment and that run's queries the extractor gives the
committer's own weights back" holds at both at no error below 1/2. -/
theorem one_le_add_of_blind_at {system : ArgumentSystem}
    {extractor : Commitment → QueryLog → Option system.Weights} {α : ℝ≥0∞}
    (ρ : system.CommitmentRandomness) {w w' : system.Weights} (hne : w ≠ w')
    (hc : system.commit w ρ = system.commit w' ρ)
    (hw : Prob (system.commit w ρ).toRandomized.withQueryLog
      {o | extractor o.1 o.2 ≠ some w} ≤ α)
    (hw' : Prob (system.commit w' ρ).toRandomized.withQueryLog
      {o | extractor o.1 o.2 ≠ some w'} ≤ α) : 1 ≤ α + α := by
  rw [← hc] at hw'
  exact one_le_add_of_two _ (fun o : Commitment × QueryLog => extractor o.1 o.2) hne hw hw'

/-- **At valid settings there are two different weights**: those of the all-zero index, and those of
an index whose embedding has the entry 2^20 at (0, 0). -/
theorem two_weights {settings : IntegerTransformer.Settings}
    (valid : settingsAreValid settings = true) : ∃ w w' : ModelWeights settings, w ≠ w' := by
  refine ⟨weightsOfIndex valid (Cm.Idx.ofIndex Inst.Model.ScalesSanity.iZero),
    weightsOfIndex valid (Cm.Idx.ofIndex (Inst.Model.ScalesSanity.iAt 0 (by decide))), fun h => ?_⟩
  have e := (weightsOfIndex_eq_iff valid _ _).1 h
  rw [Cm.index_ofIndex, Cm.index_ofIndex] at e
  have e2 := congrArg (fun i : Inst.Model.Index Inst.Model.ppref => i.val.Emb 0 0) e
  norm_num [Inst.Model.ScalesSanity.iZero, Inst.Model.ScalesSanity.iAt,
    Inst.Model.ScalesSanity.iW, Inst.Model.SanityAtt.embA] at e2

/-- 1 is not at most a quarter. -/
theorem not_one_le_quarter : ¬ (1 : ℝ≥0∞) ≤ 4⁻¹ :=
  not_le.2 (ENNReal.inv_lt_one.2 (by exact_mod_cast (by norm_num : (1 : ℕ) < 4)))

/-- Nor at most two quarters. -/
theorem not_one_le_two_quarters : ¬ (1 : ℝ≥0∞) ≤ 4⁻¹ + 4⁻¹ := by
  have h : (4 : ℝ≥0∞)⁻¹ + 4⁻¹ < 2⁻¹ + 2⁻¹ :=
    ENNReal.add_lt_add
      (ENNReal.inv_lt_inv.2 (by exact_mod_cast (by norm_num : (2 : ℕ) < 4)))
      (ENNReal.inv_lt_inv.2 (by exact_mod_cast (by norm_num : (2 : ℕ) < 4)))
  rw [ENNReal.inv_two_add_inv_two] at h
  exact not_le.2 h

end Bind.Control

/-! ## 2. At the description theCpp -/

namespace Bind.Cpp
open VerifierAndGoals VerifierAndGoals.Fit FlashProve FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles
open Bind.Twin (Shape Table)
open Bind.Control

/-- **At this shape and these files the committer does not read the table's plain entries**: at two
tables with the same encoding randomness, pads and salts it is one algorithm. -/
def BlindAt (T : Letters) (sh : Shape) (p l K : ByteArray) : Prop :=
  ∀ t t' : Table, t.tail = t'.tail → t.pad = t'.pad → t.salt = t'.salt →
    T.id sh p l K t = T.id sh p l K t'

/-- The same at every shape and all files. -/
def Blind (T : Letters) : Prop := ∀ sh p l K, BlindAt T sh p l K

/-- **A member**: the running committer, run at the table whose plain entries are all 0. -/
def blindTwin (g : Shape → Seed → Digest → Digest → Coins) : Letters :=
  ⟨fun sh p l K t => Bind.Twin.twinID sh p l K ⟨fun _ _ => 0, t.tail, t.pad, t.salt⟩, g⟩

theorem blind_blindTwin (g : Shape → Seed → Digest → Digest → Coins) : Blind (blindTwin g) := by
  intro sh p l K t t' h1 h2 h3
  show Bind.Twin.twinID sh p l K ⟨fun _ _ => 0, t.tail, t.pad, t.salt⟩ =
    Bind.Twin.twinID sh p l K ⟨fun _ _ => 0, t'.tail, t'.pad, t'.salt⟩
  rw [h1, h2, h3]

/-- A blind committer at given coins is one algorithm at all plain entries. -/
theorem id_blind {T : Letters} {sh : Shape} {p l K : ByteArray} (hT : BlindAt T sh p l K)
    (x : Coins) (e e' : ℕ → ℕ → UInt64) :
    T.id sh p l K (x.table e) = T.id sh p l K (x.table e') :=
  hT (x.table e) (x.table e') rfl rfl rfl

/-- So is the committer of the commit field, general in the shape and the entries. -/
theorem commitAt_blind {T : Letters} {sh : Shape} {Z : PublicFiles} (hT : BlindAt T sh Z.pol Z.lay Z.KL)
    (e e' : ℕ → ℕ → UInt64) (ρ : Rand) : T.commitAt sh Z e ρ = T.commitAt sh Z e' ρ := by
  cases ρ with
  | inl seed =>
    show DeterministicAlgorithm.query _ _ = DeterministicAlgorithm.query _ _
    refine congrArg (DeterministicAlgorithm.query _) (funext fun c =>
      congrArg (DeterministicAlgorithm.query _) (funext fun I => ?_))
    exact id_blind hT _ e e'
  | inr x => exact id_blind hT x e e'

/-- **At a committer that is blind at the full size's shape and Z's files the commit field is one
algorithm at all weights.** -/
theorem commit_blind {T : Letters} {Z : PublicFiles} (hT : BlindAt T shapeFull Z.pol Z.lay Z.KL)
    (s : IntegerTransformer.Settings) (w w' : ModelWeights s) (ρ : Rand) :
    cppCommit T Z s w ρ = cppCommit T Z s w' ρ :=
  commitAt_blind hT (entryOf s w) (entryOf s w') ρ

/- From here on Lean compares these by their names. -/
attribute [local irreducible] Bind.Twin.twinID Bind.Twin.calls shapeFull twinBudget
  theCoding theKeyData theProofData protocolDataWellFormed theDeadPlan theKeyGate theProofGate theLinkGate
  theProvers theNamed LPFD.Full.GF riDigits fieldRows descriptionOfDataOnBytes T₀ FlashProve.thePlan
  FlashProve.theItem LayoutsByPublicReading.commitAtCoins

/-- Its count is the running committer's. -/
theorem count_blindTwin (g : Shape → Seed → Digest → Digest → Coins) : Count (blindTwin g) :=
  fun Z t => Bind.Twin.queryBound_twinID_of shapeFull twinBudget count_le Z.pol Z.lay Z.KL
    ⟨fun _ _ => 0, t.tail, t.pad, t.salt⟩

/-- bindingErrorInQueries at the committer's count is at most a quarter. -/
theorem bitsBinding_le_quarter : bindingErrorInQueries (twinBudget + 2) ≤ 4⁻¹ :=
  bitsBinding_le_ceiling _ (by
    unfold twinBudget queryBudget
    norm_num)

/-- So it is below 1. -/
theorem not_one_le_bitsBinding : ¬ 1 ≤ bindingErrorInQueries (twinBudget + 2) := fun h =>
  not_one_le_quarter (le_trans h bitsBinding_le_quarter)

/-- And so is twice it. -/
theorem not_one_le_two_bitsBinding :
    ¬ 1 ≤ bindingErrorInQueries (twinBudget + 2) + bindingErrorInQueries (twinBudget + 2) := fun h =>
  not_one_le_two_quarters (le_trans h (add_le_add bitsBinding_le_quarter bitsBinding_le_quarter))

/-- **A NEGATIVE TEST AT THE CONCLUSION: a committer whose value does not feel the weights does not
bind**, at a Z that is read. -/
theorem blindDoesNotBind : BlindDoesNotBind := by
  intro T prove Z pp hr cnt hv hb
  obtain ⟨w, w', hne⟩ := two_weights (valid_of_read hr)
  exact not_one_le_bitsBinding (one_le_of_blindValue hb hne (Sum.inl 0 : Rand)
    (hv w w' (Sum.inl 0 : Rand)) (commit_count T Z cnt (settingsOfRead pp) w (Sum.inl 0 : Rand)))

/-- There is a prover to lay into theCpp: one that returns a constant form. A form exists: the
description's own prover returns one. -/
theorem exists_prove (Z₀ : PublicFiles) (pp : Inst.Model.ScalesAndPolicy) (hr : readFiles Z₀ = .ok pp) :
    Nonempty (PublicFiles → (s : IntegerTransformer.Settings) → ModelWeights s → Rand → List Token →
      List Token → RandomizedAlgorithm flashProveDescription.Form) :=
  ⟨fun _ _ _ _ _ _ => .done (firstResult (flashProveDescription.prove Z₀ (settingsOfRead pp)
    (nonempty_modelWeights (valid_of_read hr)).some (firstResult flashProveDescription.sample) [] []))⟩

/-- **A negative test at the tie**: a committer that is blind at the full size's shape and Z's files
does not meet the tie together with the count, at a Z that is read: else it would bind. -/
theorem blindAt_fails {T : Letters} {Z : PublicFiles} (hT : BlindAt T shapeFull Z.pol Z.lay Z.KL)
    (pp : Inst.Model.ScalesAndPolicy) (hr : readFiles Z = .ok pp) (cnt : CountAt T Z) : ¬ TieAt T Z := by
  intro tie
  obtain ⟨prove⟩ := exists_prove Z pp hr
  exact blindDoesNotBind T prove Z pp hr cnt
    (fun w w' ρ hash => by rw [commit_blind hT (settingsOfRead pp) w w' ρ])
    (bindsAtZ_cpp T prove Z pp hr tie cnt).2

/-- **A NEGATIVE TEST AT THE TIE: a committer that does not read the table's entries does not meet
the tie together with the count**, at a Z that is read. -/
theorem blindFails : BlindFails :=
  fun _ hT Z pp hr cnt => blindAt_fails (hT shapeFull Z.pol Z.lay Z.KL) pp hr cnt

variable (prove : PublicFiles → (s : IntegerTransformer.Settings) → ModelWeights s → Rand → List Token →
    List Token → RandomizedAlgorithm flashProveDescription.Form)

/-- **At a blind committer somebody opens one commitment to two different weights**: the notion
holds at no error below 1 at the committer's count. -/
theorem blind_twoOpenings {T : Letters} {Z : PublicFiles} (hT : BlindAt T shapeFull Z.pol Z.lay Z.KL)
    (pp : Inst.Model.ScalesAndPolicy) (hr : readFiles Z = .ok pp) (cnt : CountAt T Z) {ε : ℕ → ℝ≥0∞}
    (h : NoTwoOpenings (systemOfRecord (atSecondHashFunction (theCpp T prove)) Z (settingsOfRead pp)) ε) :
    1 ≤ ε (twinBudget + 2) := by
  obtain ⟨w, w', hne⟩ := two_weights (valid_of_read hr)
  exact h.one_le_of_blind hne (Sum.inl 0 : Rand)
    (commit_blind hT (settingsOfRead pp) w w' (Sum.inl 0 : Rand))
    (commit_count T Z cnt (settingsOfRead pp) w (Sum.inl 0 : Rand))

/-- **At a blind committer correctness of extraction holds at no error below 1/2**, whatever the
extractor. -/
theorem blind_extracts {T : Letters} {Z : PublicFiles} (hT : BlindAt T shapeFull Z.pol Z.lay Z.KL)
    (pp : Inst.Model.ScalesAndPolicy) (hr : readFiles Z = .ok pp)
    {extractor : Commitment → QueryLog → Option (ModelWeights (settingsOfRead pp))} {α : ℝ≥0∞}
    (h : ExtractsCommittedWeights
      (systemOfRecord (atSecondHashFunction (theCpp T prove)) Z (settingsOfRead pp)) extractor α) :
    1 ≤ α + α := by
  obtain ⟨w, w', hne⟩ := two_weights (valid_of_read hr)
  exact one_le_add_of_blind h hne fun ρ => commit_blind hT (settingsOfRead pp) w w' ρ

/-- **Nor at one fixed randomness**, a seed or coins, whatever the extractor. -/
theorem blind_extracts_at {T : Letters} {Z : PublicFiles} (hT : BlindAt T shapeFull Z.pol Z.lay Z.KL)
    (pp : Inst.Model.ScalesAndPolicy) (hr : readFiles Z = .ok pp) (ρ : Rand)
    {extractor : Commitment → QueryLog → Option (ModelWeights (settingsOfRead pp))} {α : ℝ≥0∞}
    (h : ∀ w : ModelWeights (settingsOfRead pp),
      Prob ((atSecondHashFunction (theCpp T prove)).commit Z (settingsOfRead pp) w ρ).toRandomized.withQueryLog
        {o | extractor o.1 o.2 ≠ some w} ≤ α) : 1 ≤ α + α := by
  obtain ⟨w, w', hne⟩ := two_weights (valid_of_read hr)
  exact one_le_add_of_blind_at
    (system := systemOfRecord (atSecondHashFunction (theCpp T prove)) Z (settingsOfRead pp)) ρ hne
    (commit_blind hT (settingsOfRead pp) w w' ρ) (h w) (h w')

/-- **At the member**: the running committer at entries of 0, at a Z that is read: it does not meet
the tie; it does not bind at bindingErrorInQueries; NoTwoOpenings fails at the error 2 · bindingErrorInQueries t;
correctness of extraction fails at bindingErrorInQueries (twinBudget + 2), with the randomness sampled and at
every fixed randomness. These are the errors of bindsAt_salt, noTwoOpenings_salt,
extractsCommitted_salt and extracts_salt (Johnson/Bind/Cpp/TheTie.lean). -/
theorem blindTwin_fails (g : Shape → Seed → Digest → Digest → Coins) (Z : PublicFiles)
    (pp : Inst.Model.ScalesAndPolicy) (hr : readFiles Z = .ok pp) :
    ¬ TieAt (blindTwin g) Z ∧
      ¬ BindsWith (systemOfRecord (atSecondHashFunction (theCpp (blindTwin g) prove)) Z (settingsOfRead pp))
        ((atSecondHashFunction (theCpp (blindTwin g) prove)).extractor Z (settingsOfRead pp)) bindingErrorInQueries ∧
      ¬ NoTwoOpenings
        (systemOfRecord (atSecondHashFunction (theCpp (blindTwin g) prove)) Z (settingsOfRead pp))
        (fun t => 2 * bindingErrorInQueries t) ∧
      ¬ ExtractsCommittedWeights
        (systemOfRecord (atSecondHashFunction (theCpp (blindTwin g) prove)) Z (settingsOfRead pp))
        ((atSecondHashFunction (theCpp (blindTwin g) prove)).extractor Z (settingsOfRead pp))
        (bindingErrorInQueries (twinBudget + 2)) ∧
      ∀ ρ : Rand, ¬ ∀ w : ModelWeights (settingsOfRead pp),
        Prob ((atSecondHashFunction (theCpp (blindTwin g) prove)).commit Z (settingsOfRead pp) w
            ρ).toRandomized.withQueryLog
          {o | (atSecondHashFunction (theCpp (blindTwin g) prove)).extractor Z (settingsOfRead pp) o.1 o.2 ≠
            some w} ≤ bindingErrorInQueries (twinBudget + 2) := by
  have hB : BlindAt (blindTwin g) shapeFull Z.pol Z.lay Z.KL :=
    blind_blindTwin g shapeFull Z.pol Z.lay Z.KL
  refine ⟨blindAt_fails hB pp hr (count_blindTwin g Z),
    blindDoesNotBind (blindTwin g) prove Z pp hr (count_blindTwin g Z)
      (fun w w' ρ hash => by rw [commit_blind hB (settingsOfRead pp) w w' ρ]),
    fun h => ?_, fun h => not_one_le_two_bitsBinding (blind_extracts prove hB pp hr h),
    fun ρ h => not_one_le_two_bitsBinding (blind_extracts_at prove hB pp hr ρ h)⟩
  have h1 := blind_twoOpenings prove hB pp hr (count_blindTwin g Z) h
  rw [two_mul] at h1
  exact not_one_le_two_bitsBinding h1

end Bind.Cpp

end

#print axioms Bind.Control.one_le_of_blindValue
#print axioms Bind.Control.one_le_add_of_two
#print axioms Bind.Control.one_le_add_of_blind
#print axioms Bind.Control.one_le_add_of_blind_at
#print axioms Bind.Control.two_weights
#print axioms Bind.Control.not_one_le_quarter
#print axioms Bind.Control.not_one_le_two_quarters
#print axioms Bind.Cpp.blind_blindTwin
#print axioms Bind.Cpp.id_blind
#print axioms Bind.Cpp.commitAt_blind
#print axioms Bind.Cpp.commit_blind
#print axioms Bind.Cpp.count_blindTwin
#print axioms Bind.Cpp.bitsBinding_le_quarter
#print axioms Bind.Cpp.not_one_le_bitsBinding
#print axioms Bind.Cpp.not_one_le_two_bitsBinding
#print axioms Bind.Cpp.blindDoesNotBind
#print axioms Bind.Cpp.exists_prove
#print axioms Bind.Cpp.blindAt_fails
#print axioms Bind.Cpp.blindFails
#print axioms Bind.Cpp.blind_twoOpenings
#print axioms Bind.Cpp.blind_extracts
#print axioms Bind.Cpp.blind_extracts_at
#print axioms Bind.Cpp.blindTwin_fails
