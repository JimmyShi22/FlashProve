-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Ok/NumberPrices/KeyAtWrittenTeeth.lean: where the closed fact on the key file's prices
(`KeyPricesWritten`, Johnson/Desc/Ok/NumberPrices/KeyAtWritten.lean) and its test bite, and where
they do not.

`chainOk_false_of_run`, `chainOk_false_of_idx`, `f2_right`, `half_ofReal`, `two_ofReal`,
`not_pricedAt_of_above`, `above_of_test`, `mem_chain_of_idx` are tools; `not_keyPriced_of_above` is
a tool at the written lists. All else are facts on written files that are bent here.

Definitions.
  `scaleAt i f recs`: the records with the error of the record i turned by f. `twice`, `finer`,
    `halved`: an error times 2, times 1025 / 1024, times 1 / 2, each exact. `struck`: the error 0.
  `withSecond recs`: `keyThree` with other records in the second plan.
  `bentKey`, `fineKey`, `halvedKey`: so with the record 45 of the second plan turned: the round
    "BASE lambda" whose price stands nearest to the bound among the three plans' 106 records (0.0011
    of a bit, by programs outside Lean; not shown here). `struckKey`: all errors of all three plans
    struck to 0.
  `aboveB j r`: a test with code: r's error is at least (2 ^ j + 1) * 2 ^ (work - 128 - j), which is
    above the bound 2 ^ (work - 128).
Statements.
  Where the test and the statement bite. `bent_walk`: at `bentKey` the walk still says yes: the
    entries are untouched. `bent_lit_no`, `bent_no`: the test says no. `bent_plan_no`: `Desc.chainOk
    32` says no at the whole bent plan. `not_keyPriced_bent`: ¬ KeyPricedAt bentKey: the statement
    is false there, not only untested. `fine_lit_no`, `not_keyPriced_fine`: the like with the error
    raised by one part in 1024.
  `not_pricedAt_of_above`: a priced round whose error is above 2 ^ (work - 128) has `PricedAt` with
    no round's data: the clause `share` fails, at every kind, because the factor for the sampler's
    bias is at least 1. `above_of_test`: a yes of `aboveB` gives that.
  Where the walk bites. At the second chain: `walk_dropped_no`: with the last run dropped;
    `walk_longer_no`: with one more round in front. At the first chain: `walk_record_no`: with the
    entry "RECORD" not passed over. Each time the walk says no.
  Where they do not bite, and must not. `halved_ok`, `halved_priced`: with that error halved the
    test says yes and the statement holds. `struck_ok`, `struck_priced`: with every error struck to
    0 the test says yes and the statement holds. A smaller error passes every clause here: the price
    is still within the bound. Only a law from below, on a count, can catch it, and there is none
    yet.
By evaluations in Lean's kernel (`decide +kernel`): `bent_walk`, `bent_lit_no`, `fine_lit_no`,
`walk_dropped_no`, `walk_longer_no`, `walk_record_no`, `halved_lit`, `struck_lit0`, `1`, `2`, and
the premises inside `bent_plan_no`, `not_keyPriced_bent`, `not_keyPriced_fine`. All else is by
proof.

What of OnBytes/Model/ is used: nothing by name.

Limits. The plants stand at one record. A doubled error is caught only where the price has less than
one bit of room. No tooth here bends `why`, `group`, `rests`, `scope`, `wordFault`, the work or the
target (for all plans: Johnson/Desc/Ok/NumberPrices/Teeth.lean). Nothing on soundness.
-/
import Johnson.Desc.Ok.NumberPrices.KeyAtWritten
import Johnson.Desc.Ok.NumberPrices.Teeth

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Number.ByRuns
open VerifiableInference VerifiableInference.Number
open _root_.Iop Prob _root_.Run OnBytes.Params OnBytes.Slice OnBytes.Flat OnBytes.Flat.Held
open OnBytes.Maker Johnson.G Johnson.G.Runs
open scoped ENNReal

/-! ## Tools -/

/-- A record that does not hold and that a run names, not 0 times: the plan is refused. -/
theorem chainOk_false_of_run {w : ℕ} {s : Setting} {recs : List PlanRound}
    {runs : List (Nat × Nat)} {n i : ℕ} {r : PlanRound} (hm : (n + 1, i) ∈ runs)
    (hr : recs[i]? = some r) (hf : roundHolds s (capped s) r = false) :
    Desc.chainOk w ⟨s, unrunG recs runs⟩ = false :=
  chainOk_false_of_round w _ r (mem_unrunG_of hm hr) hf

/-- The like with the record given by its index alone. -/
theorem chainOk_false_of_idx {w : ℕ} {s : Setting} {recs : List PlanRound}
    {runs : List (Nat × Nat)} {n i : ℕ} (hm : (n + 1, i) ∈ runs)
    (hf : (recs[i]?).any (fun r => !roundHolds s (capped s) r) = true) :
    Desc.chainOk w ⟨s, unrunG recs runs⟩ = false := by
  cases h : recs[i]? with
  | none => simp [h] at hf
  | some r =>
    have hr : roundHolds s (capped s) r = false := by simpa [h] using hf
    exact chainOk_false_of_run hm h hr

/-- A member on the right of a relation place by place has a partner on the left. -/
theorem f2_right {α β : Type} {R : α → β → Prop} : ∀ {l : List α} {m : List β},
    List.Forall₂ R l m → ∀ b ∈ m, ∃ a ∈ l, R a b
  | _, _, .nil, _, hb => by simp at hb
  | _, _, .cons h t, b, hb => by
    rcases List.mem_cons.1 hb with e | hb
    · rw [e]
      exact ⟨_, List.mem_cons.2 (Or.inl rfl), h⟩
    · obtain ⟨a, ha, hr⟩ := f2_right t b hb
      exact ⟨a, List.mem_cons_of_mem _ ha, hr⟩

theorem half_ofReal (T : ℕ) : (2 : ℝ≥0∞)⁻¹ ^ T = ENNReal.ofReal ((2⁻¹ : ℝ) ^ T) := by
  rw [ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_inv_of_pos (by norm_num)]
  norm_num

theorem two_ofReal (W : ℕ) : (2 : ℝ≥0∞) ^ W = ENNReal.ofReal ((2 : ℝ) ^ W) := by
  rw [ENNReal.ofReal_pow (by norm_num)]
  norm_num

/-- **An error above the bound has `PricedAt` with no round's data.** -/
theorem not_pricedAt_of_above {d : RDT} {r : PlanRound}
    (hb : (2⁻¹ : ℚ) ^ 128 * 2 ^ r.entry.work < r.error.val) : ¬ Number.PricedAt d r := by
  intro P
  have s := P.share
  rw [P.entry] at s
  have one_le : (1 : ℝ≥0∞) ≤ kapSl 128 ^ exAll (Fmt.dsOf r.entry d.kind) :=
    one_le_pow₀ (one_le_kapSl 128)
  have s1 : ENNReal.ofReal (r.error.val : ℝ) / 2 ^ r.entry.work ≤ (2 : ℝ≥0∞)⁻¹ ^ 128 :=
    calc ENNReal.ofReal (r.error.val : ℝ) / 2 ^ r.entry.work
        = 1 * (ENNReal.ofReal (r.error.val : ℝ) / 2 ^ r.entry.work) := (one_mul _).symm
      _ ≤ kapSl 128 ^ exAll (Fmt.dsOf r.entry d.kind) *
          (ENNReal.ofReal (r.error.val : ℝ) / 2 ^ r.entry.work) := mul_le_mul' one_le le_rfl
      _ ≤ (2 : ℝ≥0∞)⁻¹ ^ 128 := s
  rw [two_ofReal, half_ofReal, ← ENNReal.ofReal_div_of_pos (by positivity)] at s1
  have s2 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 s1
  have s3 := (div_le_iff₀ (by positivity)).1 s2
  have hbR : (2⁻¹ : ℝ) ^ 128 * 2 ^ r.entry.work < (r.error.val : ℝ) := by
    have h := (Rat.cast_lt (K := ℝ)).2 hb
    simpa only [Rat.cast_mul, Rat.cast_pow, Rat.cast_inv, Rat.cast_ofNat] using h
  exact absurd s3 (not_le.2 hbR)

/-- The error is at least (2 ^ j + 1) * 2 ^ (work - 128 - j). -/
def aboveB (j : ℕ) (r : PlanRound) : Bool :=
  (⟨2 ^ j + 1, (r.entry.work : ℤ) - ((128 + j : ℕ) : ℤ)⟩ : Binary).le r.error

theorem above_of_test {j : ℕ} {r : PlanRound} (h : aboveB j r = true) :
    (2⁻¹ : ℚ) ^ 128 * 2 ^ r.entry.work < r.error.val := by
  have h1 := Binary.le_sound _ _ h
  have h2 : (⟨2 ^ j + 1, (r.entry.work : ℤ) - ((128 + j : ℕ) : ℤ)⟩ : Binary).val =
      ((2 : ℚ) ^ j + 1) * ((2 : ℚ) ^ r.entry.work * (2⁻¹ : ℚ) ^ (128 + j)) := by
    show ((2 ^ j + 1 : ℕ) : ℚ) * (2 : ℚ) ^ ((r.entry.work : ℤ) - ((128 + j : ℕ) : ℤ)) = _
    rw [two_zpow_sub]
    push_cast
    rfl
  rw [h2] at h1
  have x0 : (0 : ℚ) < (2 : ℚ) ^ r.entry.work * (2⁻¹ : ℚ) ^ (128 + j) := by positivity
  have hj : (2 : ℚ) ^ j * (2⁻¹ : ℚ) ^ j = 1 := by
    rw [← mul_pow]
    norm_num
  have e : (2⁻¹ : ℚ) ^ 128 * 2 ^ r.entry.work =
      (2 : ℚ) ^ j * ((2 : ℚ) ^ r.entry.work * (2⁻¹ : ℚ) ^ (128 + j)) :=
    calc (2⁻¹ : ℚ) ^ 128 * 2 ^ r.entry.work
        = (2⁻¹ : ℚ) ^ 128 * 2 ^ r.entry.work * ((2 : ℚ) ^ j * (2⁻¹ : ℚ) ^ j) := by
          rw [hj, mul_one]
      _ = (2 : ℚ) ^ j * ((2 : ℚ) ^ r.entry.work * (2⁻¹ : ℚ) ^ (128 + j)) := by
          rw [pow_add]
          ring
  rw [e]
  have e2 : ((2 : ℚ) ^ j + 1) * ((2 : ℚ) ^ r.entry.work * (2⁻¹ : ℚ) ^ (128 + j)) =
      (2 : ℚ) ^ j * ((2 : ℚ) ^ r.entry.work * (2⁻¹ : ℚ) ^ (128 + j)) +
        (2 : ℚ) ^ r.entry.work * (2⁻¹ : ℚ) ^ (128 + j) := by ring
  rw [e2] at h1
  linarith

/-- A record that a run names, not 0 times, and that has not the name "RECORD" is a round of
the chain. -/
theorem mem_chain_of_idx {s : Setting} {recs : List PlanRound} {runs : List (Nat × Nat)} {n i : ℕ}
    {q : PlanRound → Bool} (hm : (n + 1, i) ∈ runs)
    (hq : (recs[i]?).any (fun r => q r && (r.entry.name != Fmt.recordName)) = true) :
    ∃ r ∈ chainRounds ⟨s, unrunG recs runs⟩, q r = true := by
  cases h : recs[i]? with
  | none => simp [h] at hq
  | some r =>
    rw [h] at hq
    have c : (q r && (r.entry.name != Fmt.recordName)) = true := hq
    have c' := Bool.and_eq_true_iff.1 c
    exact ⟨r, List.mem_filter.2 ⟨mem_unrunG_of hm h, c'.2⟩, c'.1⟩

/-! ## The bent plans -/

/-- The records with the error of the record i turned by f. -/
def scaleAt : ℕ → (Binary → Binary) → List PlanRound → List PlanRound
  | _, _, [] => []
  | 0, f, r :: rs => { r with error := f r.error } :: rs
  | i + 1, f, r :: rs => r :: scaleAt i f rs

/-- An error times 2. -/
def twice (b : Binary) : Binary := ⟨2 * b.m, b.e⟩

/-- An error times 1025 / 1024. -/
def finer (b : Binary) : Binary := ⟨1025 * b.m, b.e - 10⟩

/-- An error times 1 / 2. -/
def halved (b : Binary) : Binary := ⟨b.m, b.e - 1⟩

/-- The priced round with the error 0. -/
def struck (r : PlanRound) : PlanRound := { r with error := ⟨0, 0⟩ }

/-- The three written priced plans with other records in the second. -/
def withSecond (recs : List PlanRound) : Three :=
  { keyThree with B := ⟨pricedKeySetFull, recs, pricedKeyRunsFull1⟩ }

def bentKey : Three := withSecond (scaleAt 45 twice pricedKeyRecsFull1)
def fineKey : Three := withSecond (scaleAt 45 finer pricedKeyRecsFull1)
def halvedKey : Three := withSecond (scaleAt 45 halved pricedKeyRecsFull1)

/-- All errors of all three plans struck to 0. -/
def struckKey : Three :=
  ⟨⟨pricedKeySetFull, pricedKeyRecsFull0.map struck, pricedKeyRunsFull0⟩,
    ⟨pricedKeySetFull, pricedKeyRecsFull1.map struck, pricedKeyRunsFull1⟩,
    ⟨pricedKeySetFull, pricedKeyRecsFull2.map struck, pricedKeyRunsFull2⟩⟩

/-! ## Where the test and the statement bite -/

/-- At the bent plan the walk still says yes: the entries are untouched. -/
theorem bent_walk :
    sameBy (fun x r => decide (x.1.entry = r.entry)) 10000 (valRuns dryKeyRecsFull dryKeyRunsFull1)
      (chainRuns (scaleAt 45 twice pricedKeyRecsFull1) pricedKeyRunsFull1) = true := by
  decide +kernel

/-- **The test on the bent plan says no.** -/
theorem bent_lit_no : litOk 32 10000 dryKeyRecsFull dryKeyRunsFull1 bentKey.B = false := by
  decide +kernel

/-- **So the test on the three says no.** -/
theorem bent_no : keyLitOk 10000 bentKey = false := by
  simp [keyLitOk, bent_lit_no]

/-- **The whole bent plan is refused too.** -/
theorem bent_plan_no : Desc.chainOk 32 bentKey.B.plan = false :=
  chainOk_false_of_idx (n := 0) (i := 45) (by decide +kernel) (by decide +kernel)

/-- A plan of the second chain with a round above the bound: the statement is false. -/
theorem not_keyPriced_of_above {T : Three}
    (h : ∃ r ∈ chainRounds T.B.plan, aboveB 20 r = true) : ¬ KeyPricedAt T := by
  intro H
  have H2 : List.Forall₂ Number.PricedAt writtenKFull.ds₂ (chainRounds T.B.plan) := H.2.1
  obtain ⟨r, hr, hb⟩ := h
  obtain ⟨d, _, P⟩ := f2_right H2 r hr
  exact not_pricedAt_of_above (above_of_test hb) P

/-- **At the three plans with one price doubled the statement is false.** -/
theorem not_keyPriced_bent : ¬ KeyPricedAt bentKey :=
  not_keyPriced_of_above
    (mem_chain_of_idx (n := 0) (i := 45) (by decide +kernel) (by decide +kernel))

/-- **With that price raised by one part in 1024 the test says no.** -/
theorem fine_lit_no : litOk 32 10000 dryKeyRecsFull dryKeyRunsFull1 fineKey.B = false := by
  decide +kernel

/-- **And the statement is false.** -/
theorem not_keyPriced_fine : ¬ KeyPricedAt fineKey :=
  not_keyPriced_of_above
    (mem_chain_of_idx (n := 0) (i := 45) (by decide +kernel) (by decide +kernel))

/-! ## Where the walk bites -/

/-- With the priced plan's last run dropped the walk says no. -/
theorem walk_dropped_no :
    sameBy (fun x r => decide (x.1.entry = r.entry)) 10000 (valRuns dryKeyRecsFull dryKeyRunsFull1)
      (chainRuns pricedKeyRecsFull1 pricedKeyRunsFull1.dropLast) = false := by
  decide +kernel

/-- With a run of one more round in front it says no. -/
theorem walk_longer_no :
    sameBy (fun x r => decide (x.1.entry = r.entry)) 10000 (valRuns dryKeyRecsFull dryKeyRunsFull1)
      (chainRuns pricedKeyRecsFull1 ((1, 0) :: pricedKeyRunsFull1)) = false := by
  decide +kernel

/-- With the entry "RECORD" not passed over it says no. -/
theorem walk_record_no :
    sameBy (fun x r => decide (x.1.entry = r.entry)) 10000 (valRuns dryKeyRecsFull dryKeyRunsFull0)
      (valRuns pricedKeyRecsFull0 pricedKeyRunsFull0) = false := by
  decide +kernel

/-! ## Where they do not bite, and must not -/

theorem halved_lit : litOk 32 10000 dryKeyRecsFull dryKeyRunsFull1 halvedKey.B = true := by
  decide +kernel

/-- With that price halved the test says yes. -/
theorem halved_ok : keyLitOk 10000 halvedKey = true :=
  Bool.and_eq_true_iff.2 ⟨Bool.and_eq_true_iff.2
    ⟨Bool.and_eq_true_iff.2 ⟨key_recs0, key_walk0⟩, halved_lit⟩,
    Bool.and_eq_true_iff.2 ⟨key_recs2, key_walk2⟩⟩

/-- **And the statement holds.** -/
theorem halved_priced : KeyPricedAt halvedKey := (pricedOfThree 10000 halvedKey).1 halved_ok

set_option maxRecDepth 1000000 in
theorem struck_lit0 : litOk 32 10000 dryKeyRecsFull dryKeyRunsFull0 struckKey.A = true := by
  decide +kernel

theorem struck_lit1 : litOk 32 10000 dryKeyRecsFull dryKeyRunsFull1 struckKey.B = true := by
  decide +kernel

theorem struck_lit2 : litOk 32 10000 dryKeyRecsFull dryKeyRunsFull2 struckKey.C = true := by
  decide +kernel

/-- With every error struck to 0 the test says yes. -/
theorem struck_ok : keyLitOk 10000 struckKey = true :=
  Bool.and_eq_true_iff.2 ⟨Bool.and_eq_true_iff.2 ⟨struck_lit0, struck_lit1⟩, struck_lit2⟩

/-- **And the statement holds**: it then serves the count 0 alone. -/
theorem struck_priced : KeyPricedAt struckKey := (pricedOfThree 10000 struckKey).1 struck_ok

end VerifiableInference.Number.ByRuns

#print axioms VerifiableInference.Number.ByRuns.chainOk_false_of_run
#print axioms VerifiableInference.Number.ByRuns.chainOk_false_of_idx
#print axioms VerifiableInference.Number.ByRuns.f2_right
#print axioms VerifiableInference.Number.ByRuns.half_ofReal
#print axioms VerifiableInference.Number.ByRuns.two_ofReal
#print axioms VerifiableInference.Number.ByRuns.not_pricedAt_of_above
#print axioms VerifiableInference.Number.ByRuns.above_of_test
#print axioms VerifiableInference.Number.ByRuns.mem_chain_of_idx
#print axioms VerifiableInference.Number.ByRuns.bent_walk
#print axioms VerifiableInference.Number.ByRuns.bent_lit_no
#print axioms VerifiableInference.Number.ByRuns.bent_no
#print axioms VerifiableInference.Number.ByRuns.bent_plan_no
#print axioms VerifiableInference.Number.ByRuns.not_keyPriced_of_above
#print axioms VerifiableInference.Number.ByRuns.not_keyPriced_bent
#print axioms VerifiableInference.Number.ByRuns.fine_lit_no
#print axioms VerifiableInference.Number.ByRuns.not_keyPriced_fine
#print axioms VerifiableInference.Number.ByRuns.walk_dropped_no
#print axioms VerifiableInference.Number.ByRuns.walk_longer_no
#print axioms VerifiableInference.Number.ByRuns.walk_record_no
#print axioms VerifiableInference.Number.ByRuns.halved_lit
#print axioms VerifiableInference.Number.ByRuns.halved_ok
#print axioms VerifiableInference.Number.ByRuns.halved_priced
#print axioms VerifiableInference.Number.ByRuns.struck_lit0
#print axioms VerifiableInference.Number.ByRuns.struck_lit1
#print axioms VerifiableInference.Number.ByRuns.struck_lit2
#print axioms VerifiableInference.Number.ByRuns.struck_ok
#print axioms VerifiableInference.Number.ByRuns.struck_priced
