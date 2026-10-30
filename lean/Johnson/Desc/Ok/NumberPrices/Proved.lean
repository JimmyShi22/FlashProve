-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Ok/NumberPrices/Proved.lean: the proof of `PricesGeneral`
(Johnson/Desc/Ok/NumberPrices/Stated.lean), and `PricesRungs` in literals: two of the three parts of
`PricesNamed` (Johnson/Goal/Numbers/NumberPricesAt.lean [not in this library]).

WHERE THINGS STAND. No file under this folder imports a file under Ladder/: where the three public
files occur they are the letters pol, lay, KL; where a bound on a round's error occurs it is a
literal. `PricesAtRelease`, `PricesAtGap`, `PricesRungs`, `pricesRungs`, `PricesNamed`,
`pricesNamed_of`, `prices_at_release`, `below_step`, `pricedAt_of_release`, wherever a head under
this folder names them, stand in Johnson/Goal/Numbers/NumberPricesAt.lean [not in this library].
There `PricesAtRelease` and `PricesAtGap` are stated, not proved, and `PricesNamed` is not proved.

THE THEOREMS HERE ARE TOOLS. No line under Owed/ [not in this library] is to be laid on them.

Statements and proofs, with no evaluation of any plan: from `Binary.le_sound`, `Binary.val_twoTo`
(OnBytes/Params/RealLaws.lean), `whole_ge`, `held_num`, `held_round`, `capped_two`, `cappedTwo_ge`
(OnBytes/Slice/HeldRound.lean), `held_list`, `all_filter` (OnBytes/Flat/HeldAll.lean) and
`inv_pow_split` (Johnson/Thin/K/Level/Arith.lean).

Main names:
  `chainOk_parts`: what a yes of `Desc.chainOk w P` says, part by part.
  `price_le`: in a plan that holds, price P r ≤ 2^(work - target).
  `pricesOf_of_parts`: PricesOf w P from: P holds; `sideB P`; 128 ≤ the target; no round has more
    than w bits of work. So a target above 128 serves as well; `Desc.chainOk` asks 128 itself.
  `pricesGeneral : PricesGeneral`. `rungsLit`: `PricesRungs` in literals.
  `pricesNamed_of` (Johnson/Goal/Numbers/NumberPricesAt.lean [not in this library]):
    `PricesAtRelease` gives
    `PricesNamed`.
  `keyOk_parts`, `proofOk_parts`: what a yes of `Desc.keyOk c`, `Desc.proofOk c` says, part by part.
  `prices_at`: from `PricesAt pol lay KL` (Johnson/Desc/Ok/NumberPrices/AtRelease.lean): at the
    public files pol lay KL the plan is made, the key has three plans and the proof three, PricesOf
    holds of each of the seven plans at its own w (32, 32, 32; 32; 20, 28, 20), and the line on
    slots says `Desc.slots`. `prices_at_release`
    (Johnson/Goal/Numbers/NumberPricesAt.lean [not in this library]): the
    same at the stored full-size files, from `PricesAtRelease`.
  `below_step` (Johnson/Goal/Numbers/NumberPricesAt.lean [not in this library]): a list of error
    counts that is below 2 ^
    -128 (`Err.Below`, Iop/InteractiveOracleProof.lean) is, with its shared rounds' counts multiplied by `Desc.slots`
    (`Err.timesShared`, Iop/BatchSound.lean), below 2 ^ -122: by `below_timesShared`
    (OnBytes/Slice/TimesSharedBelow.lean). No part of `PricesNamed`; no list is shown to be below 2
    ^ -128.
  `rungs_90`: 2^32 (1/2)^128, 64 · 2^28 (1/2)^128 and 2^20 (1/2)^128 are at most (1/2)^90: with (G3)
    at the seven values of w in `Desc.madeOk`: the prices with the work not counted, times 64 in the
    proof's second plan. No part of `PricesNamed`.

What of OnBytes/Model/ is used: `prices_at` bears `madeOf` and `m.p.chains.made`, as `PricesAt`
does: see the head of Johnson/Desc/Ok/NumberPrices/AtRelease.lean. No further file is reached.

Limits: `PricesAtRelease` is not proved, and so `PricesNamed` is not. Else those of
Johnson/Desc/Ok/NumberPrices/Stated.lean.


-/
import Johnson.Desc.Ok.NumberPrices.Stated
import OnBytes.Slice.TimesSharedBelow
import Johnson.Thin.K.Level.Arith

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Number
open _root_.Iop Prob _root_.Run OnBytes.Params OnBytes.Slice OnBytes.Flat.Held
open _root_.TopC
open scoped ENNReal

/-- What the test's yes says. -/
theorem chainOk_parts {w : ℕ} {P : Planned} (h : Desc.chainOk w P = true) :
    P.holds = true ∧ sideB P = true ∧ P.set.target = 128 ∧ ∀ r ∈ P.rounds, r.entry.work ≤ w := by
  have c1 := Bool.and_eq_true_iff.1 h
  have c2 := Bool.and_eq_true_iff.1 c1.1
  have c3 := Bool.and_eq_true_iff.1 c2.1
  exact ⟨c3.1, c3.2, of_decide_eq_true c2.2,
    fun r hr => of_decide_eq_true (List.all_eq_true.1 c1.2 r hr)⟩

/-- In a plan that holds every round holds. -/
theorem rounds_hold {P : Planned} (h : P.holds = true) :
    P.rounds.all (roundHolds P.set (capped P.set)) = true :=
  (Bool.and_eq_true_iff.1 (Bool.and_eq_true_iff.1 h).1).1

/-- What the side conditions say of the setting and of the rounds together. -/
theorem sideB_parts {P : Planned} (h : sideB P = true) :
    P.set.p = 2 ^ 64 - 2 ^ 32 + 1 ∧ P.set.degree = 3 ∧
      P.rounds.all (sideR P.set.target) = true := by
  have c1 := Bool.and_eq_true_iff.1 h
  have c2 := Bool.and_eq_true_iff.1 c1.1
  exact ⟨of_decide_eq_true c2.1, of_decide_eq_true c2.2, c1.2⟩

/-- Of one round's side conditions: the one on work. -/
theorem sideR_work {T : ℕ} {r : PlanRound} (h : sideR T r = true) :
    r.entry.drawE ≠ 0 → r.entry.work + 66 ≤ T := by
  intro hne
  rcases Bool.or_eq_true_iff.1 (Bool.and_eq_true_iff.1 h).2 with h0 | h0
  · exact absurd (by simpa using h0) hne
  · exact of_decide_eq_true h0

/-- In a plan that holds a round's price is at most 2^(work - target). -/
theorem price_le {P : Planned} (h : P.holds = true) {r : PlanRound} (hr : r ∈ P.rounds) :
    price P r ≤ (2 : ℚ) ^ ((r.entry.work : ℤ) - (P.set.target : ℤ)) := by
  have h1 := Binary.le_sound _ _ (List.all_eq_true.1 (rounds_hold h) r hr)
  rw [Binary.val_twoTo] at h1
  exact h1

/-- 2^(W - T) as a product. -/
theorem two_zpow_sub (W T : ℕ) : (2 : ℚ) ^ ((W : ℤ) - (T : ℤ)) = 2 ^ W * (2⁻¹ : ℚ) ^ T := by
  rw [zpow_sub₀ (by norm_num : (2 : ℚ) ≠ 0), zpow_natCast, zpow_natCast, inv_pow, div_eq_mul_inv]

/-- Powers of a half fall, in rational numbers. -/
theorem half_pow_anti_rat {a b : ℕ} (h : a ≤ b) : (2⁻¹ : ℚ) ^ b ≤ (2⁻¹ : ℚ) ^ a := by
  rw [inv_pow, inv_pow]
  exact inv_anti₀ (by positivity) (pow_le_pow_right₀ (by norm_num) h)

/-- Powers of a half fall, in the extended non-negative reals. -/
theorem half_pow_anti {a b : ℕ} (h : a ≤ b) : (2 : ℝ≥0∞)⁻¹ ^ b ≤ (2 : ℝ≥0∞)⁻¹ ^ a := by
  rw [← ENNReal.inv_pow, ← ENNReal.inv_pow]
  exact ENNReal.inv_le_inv.2 (pow_le_pow_right₀ (by norm_num) h)

/-- `PricesOf` from the test's parts, with "at least 128" for the target. -/
theorem pricesOf_of_parts {w : ℕ} {P : Planned} (hh : P.holds = true) (hs : sideB P = true)
    (hT : 128 ≤ P.set.target) (hw : ∀ r ∈ P.rounds, r.entry.work ≤ w) : PricesOf w P := by
  obtain ⟨hp, hd, hside⟩ := sideB_parts hs
  refine ⟨fun r hr => ?_, fun ds ha => ?_⟩
  · have hpr := price_le hh hr
    rw [two_zpow_sub] at hpr
    have hW : (0 : ℚ) < 2 ^ r.entry.work := by positivity
    have hhalf := half_pow_anti_rat hT
    refine ⟨?_, ?_, ?_⟩
    · rw [div_le_iff₀ hW, mul_comm]
      exact le_trans hpr (mul_le_mul_of_nonneg_left hhalf hW.le)
    · have H := (whole_ge P.set (capped P.set) r).trans
        (Binary.le_sound _ _ (List.all_eq_true.1 (rounds_hold hh) r hr))
      rw [Binary.val_twoTo] at H
      have hu : (3 : ℚ) * (2 : ℚ) ^ (-193 : ℤ) ≤ (capped P.set).val := by
        rw [capped_two P.set hp hd]
        exact cappedTwo_ge
      exact le_trans
        (held_num r.error.val (capped P.set).val r.entry.drawE r.entry.drawNZ r.entry.work
          P.set.target (Binary.val_nonneg _) hu (sideR_work (List.all_eq_true.1 hside r hr)) H)
        hhalf
    · exact le_trans hpr (mul_le_mul (pow_le_pow_right₀ (by norm_num) (hw r hr)) hhalf
        (by positivity) (by positivity))
  · refine (held_list P.set hp hd ds (chainRounds P) ha (all_filter _ _ _ hside)
      (all_filter _ _ _ (rounds_hold hh))).imp fun d r H count hc => ?_
    exact le_trans
      (held_round P.set H.p H.degree r d H.entry H.log H.nz H.work H.holds count hc)
      (mul_le_mul' (half_pow_anti hT) le_rfl)

/-- `PricesGeneral`: a tool. -/
theorem pricesGeneral : PricesGeneral := fun _ _ h =>
  pricesOf_of_parts (chainOk_parts h).1 (chainOk_parts h).2.1
    (le_of_eq (chainOk_parts h).2.2.1.symm) (chainOk_parts h).2.2.2

/-- The slots' factor on 2 ^ -128, in literals. -/
theorem rungsLit :
    (Desc.slots : ℚ) * (2⁻¹ : ℚ) ^ 128 ≤ (2⁻¹ : ℚ) ^ 122 ∧
      (Desc.slots : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹ ^ 128) ≤ ((2 : ℝ≥0∞)⁻¹ ^ 122) := by
  refine ⟨by unfold Desc.slots; norm_num, ?_⟩
  have h64 : ((Desc.slots : ℕ) : ℝ≥0∞) = 2 ^ 6 := by
    unfold Desc.slots
    norm_num
  rw [h64, ← ENNReal.inv_pow, ← ENNReal.inv_pow, inv_pow_split 122 6]

/-- The test on a chain with the test on its rounds of matrix entries: its first conjunct. -/
theorem chainOk_of_all {w : ℕ} {P : Planned} (h : Desc.chainAll w P = true) :
    Desc.chainOk w P = true := by
  simp only [Desc.chainAll, Bool.and_eq_true] at h
  tauto

/-- What a yes of the test at the key file's chains says. -/
theorem keyOk_parts {c : Configured} (h : Desc.keyOk c = true) :
    ∃ K₁ K₂ K₃, c.key = [K₁, K₂, K₃] ∧ Desc.chainOk 32 K₁ = true ∧ Desc.chainOk 32 K₂ = true ∧
      Desc.chainOk 32 K₃ = true := by
  unfold Desc.keyOk at h
  split at h
  · rename_i K₁ K₂ K₃ hk
    simp only [Desc.chainAll, Bool.and_eq_true] at h
    exact ⟨K₁, K₂, K₃, hk, by tauto, by tauto, by tauto⟩
  · cases h

/-- What a yes of the test at the proof file's chains says. -/
theorem proofOk_parts {c : Configured} (h : Desc.proofOk c = true) :
    ∃ F₁ F₂ F₃, c.proof = [F₁, F₂, F₃] ∧ Desc.chainOk 20 F₁ = true ∧ Desc.chainOk 28 F₂ = true ∧
      Desc.chainOk 20 F₃ = true ∧ c.sized.lines.slots = Desc.slots := by
  unfold Desc.proofOk at h
  split at h
  · rename_i F₁ F₂ F₃ hk
    simp only [Desc.chainAll, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨F₁, F₂, F₃, hk, by tauto, by tauto, by tauto, by tauto⟩
  · cases h

/-- `PricesOf` at the seven plans that are made of the public files pol lay KL. -/
theorem prices_at {pol lay KL : ByteArray} (h : PricesAt pol lay KL) :
    ∃ m K₁ K₂ K₃ F₁ F₂ F₃,
      Johnson.G.OfPlan.madeOf pol lay KL = .ok m ∧
      m.p.chains.made.key = [K₁, K₂, K₃] ∧ m.p.chains.made.proof = [F₁, F₂, F₃] ∧
      PricesOf 32 K₁ ∧ PricesOf 32 K₂ ∧ PricesOf 32 K₃ ∧ PricesOf 32 m.p.chains.made.entry ∧
      PricesOf 20 F₁ ∧ PricesOf 28 F₂ ∧ PricesOf 20 F₃ ∧
      m.p.chains.made.sized.lines.slots = Desc.slots := by
  obtain ⟨m, _, _, hm, hok, _⟩ := h
  obtain ⟨hk, he, hp⟩ := (Desc.madeOk_iff _).1 hok
  obtain ⟨K₁, K₂, K₃, ek, k1, k2, k3⟩ := keyOk_parts hk
  obtain ⟨F₁, F₂, F₃, ef, f1, f2, f3, hs⟩ := proofOk_parts hp
  exact ⟨m, K₁, K₂, K₃, F₁, F₂, F₃, hm, ek, ef, pricesGeneral _ _ k1, pricesGeneral _ _ k2,
    pricesGeneral _ _ k3, pricesGeneral _ _ (chainOk_of_all he), pricesGeneral _ _ f1,
    pricesGeneral _ _ f2, pricesGeneral _ _ f3, hs⟩

/-- The three pairs of work and slots in `Desc.madeOk`, with the work not counted, against
(1/2)^90. -/
theorem rungs_90 :
    (2 : ℚ) ^ 32 * (2⁻¹ : ℚ) ^ 128 ≤ (2⁻¹ : ℚ) ^ 90 ∧
      (Desc.slots : ℚ) * ((2 : ℚ) ^ 28 * (2⁻¹ : ℚ) ^ 128) ≤ (2⁻¹ : ℚ) ^ 90 ∧
      (2 : ℚ) ^ 20 * (2⁻¹ : ℚ) ^ 128 ≤ (2⁻¹ : ℚ) ^ 90 := by
  refine ⟨by norm_num, by unfold Desc.slots; norm_num, by norm_num⟩

end VerifiableInference.Number

#print axioms VerifiableInference.Number.chainOk_parts
#print axioms VerifiableInference.Number.rounds_hold
#print axioms VerifiableInference.Number.sideB_parts
#print axioms VerifiableInference.Number.sideR_work
#print axioms VerifiableInference.Number.price_le
#print axioms VerifiableInference.Number.two_zpow_sub
#print axioms VerifiableInference.Number.half_pow_anti_rat
#print axioms VerifiableInference.Number.half_pow_anti
#print axioms VerifiableInference.Number.pricesOf_of_parts
#print axioms VerifiableInference.Number.pricesGeneral
#print axioms VerifiableInference.Number.rungsLit
#print axioms VerifiableInference.Number.chainOk_of_all
#print axioms VerifiableInference.Number.keyOk_parts
#print axioms VerifiableInference.Number.proofOk_parts
#print axioms VerifiableInference.Number.prices_at
#print axioms VerifiableInference.Number.rungs_90
