-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Ok/NumberPrices/AtData.lean: the laws on a plan's prices at the rounds' data that are
made of the three public files: each round of the data, against the planner's priced round at its
place.

WHERE THINGS STAND. No file under this folder imports a file under Ladder/: where the three public
files occur they are the letters pol, lay, KL; where a bound on a round's error occurs it is a
literal. `PricesAtRelease`, `PricesAtGap`, `PricesRungs`, `pricesRungs`, `PricesNamed`,
`pricesNamed_of`, `prices_at_release`, `below_step`, `pricedAt_of_release`, wherever a head under
this folder names them, stand in Johnson/Goal/Numbers/NumberPricesAt.lean [not in this library].

ALL THEOREMS HERE ARE TOOLS: they hold at all public files, and name no description of the protocol
and no value of the release. No line under Owed/ [not in this library] is to be laid on any of them.

Why. `PricesGeneral` (Johnson/Desc/Ok/NumberPrices/Stated.lean) speaks of any record of the planner
and of any written rounds that are aligned with it. Here it is brought to the data of the key file's
and of the proof file's rounds (`dataKAt`, `dataPAt`, Johnson/G/RoundsOfPlan.lean).

Definitions, statements and proofs.
  `PricedAt d r`, of a round's data d and a round r of the planner's record: `entry`: d bears r's
    entry; `share`: kapSl 128 ^ exAll (dsOf d.entry d.kind) * (r.error / 2^work) ≤ 2 ^ -128; `held`:
    for every number e that is at most r.error times the number of the round's typed values there is
    a c with e ≤ c * (the number of typed values) and kapSl 128 ^ exAll (dsOf d.entry d.kind) * (c /
    2^work) ≤ 2 ^ -128; `count`: every such e is, times the sampler's weight, at most 2 ^ -128 times
    the number of the written round's verifier messages (`wT d`, OnBytes/Flat/RoundsT.lean): the
    clause of `Err.Below` (Iop/InteractiveOracleProof.lean) for that round at 2 ^ -128.
  `held_share`: the clause `share` for one round, under what `held_round` asks. Its proof is the
    second half of `held_round`'s (OnBytes/Slice/HeldRound.lean).
  `pricedAt_list`: if `Desc.chainOk w P` says yes, rs are rounds of P, and the data ds bear the
    entries of rs one by one, then PricedAt holds of ds and rs place by place.
  `pricedAt_aligned`, `pricedAt_cut`: the same from `Aligned (ds.map toRD) P`, against the plan's
    rounds of the chain, and from `AlignedCut (ds.map toRD) P`, against these without the last.
  `PricedAt.held_times`: the clause `held` with the number e multiplied by `Desc.slots`, at 2 ^
    -122.
  `PricedRounds D P₁ P₂ P₃`: PricedAt holds place by place of D.ds₁ and the first record's rounds of
    the chain without the last, of D.ds₂ and the second's, of D.ds₃ and the third's.
  `PricedData D P₁ P₂ P₃`: D is the data of three empty lists, or PricedRounds D P₁ P₂ P₃.
  `pricedRounds_of_data`: the second case, where D's third list has a round.
  `key_pricedAt`, `proof_pricedAt`: if `dataKAt m` (`dataPAt m`) returns D, the test says yes of the
    three records, and THE NAMED PREMISE holds, then PricedData of D and the three records.
  `key_pricedAt_of_tests`, `proof_pricedAt_of_tests`: the same from public tests alone: `madeOf`
    returns m; `Desc.keyOk` and `Desc.keyFit` (`Desc.proofOk`, `Desc.proofFit`) say yes of
    m.p.chains.made. The three records are then those of m.p.chains.made.
  `pricedAt_of_pricesAt`: from `PricesAt pol lay KL` (Johnson/Desc/Ok/NumberPrices/AtRelease.lean):
    at the public files pol lay KL the plan is made, the data of the key file's and of the proof
    file's rounds are made of it, and PricedRounds holds of each with the three records of the made
    plan.
  `pricedAt_of_release` (Johnson/Goal/Numbers/NumberPricesAt.lean [not in this library]): the same
    at the stored full-size
    files, from `PricesAtRelease`.

THE NAMED PREMISE is `KeyPlansPriced m K₁ K₂ K₃` (`ProofPlansPriced m F₁ F₂ F₃`,
Johnson/G/PlansPriced.lean): three equations between plans, chain by chain:
  m.p.chains.key.oneTime.given.plan = K₁.plan, m.p.chains.key.shared.given.plan = K₂.plan,
  m.p.chains.key.second.given.plan = K₃.plan; for the proof file .proof.first, .shared, .second.
Of each equation only the plans' rounds are used, that is their entries but for every one under the
name RECORD. It follows there from a yes of the test `Desc.keyFit` (`Desc.proofFit`).

What ties the kind. `Fmt.dsOf d.entry d.kind` reads the round's kind, of which the planner's record
has nothing. Every round of these data has the kind of its entry's name: `dataKAt_kinds`,
`dataPAt_kinds` (Johnson/G/DataAligned.lean). It is not used here: the four clauses hold at every
kind.

What of OnBytes/Model/ is used. The statements bear `m.p.chains.made`: `m.p` is a
`Model.Verify.Planned` (OnBytes/Model/Verify.lean), `.chains` a `Model.Verify.Chains`
(OnBytes/Model/VerifyChains.lean), and `dataKAt`, `dataPAt`, `madeOf` (Johnson/G/RoundsOfPlan.lean)
are made of them. All of it is a function of the public files alone. No further file under
OnBytes/Model/ is reached than Johnson/G/PlansPriced.lean lists in its head.

Limits. WHERE A THEOREM HERE NAMES `madeOf` IT SPEAKS OF THE PLAN AT THE FORMAT's OWN DIGEST OF THE
THREE FILES; the like at every digest of 32 bytes: `pricedAt_of_digest`, `pricedAt_one`
(Johnson/Desc/Ok/NumberPrices/AtDigest.lean). That a number e of bad typed values is at most r.error
times the number of typed values is a premise of `held` and `count`: no count is bounded here. Which
of the two cases holds at given public files is not shown. The first chain's last round, and the
entry under the name RECORD, are passed over. In `PricedAt` the bound is 2 ^ -128 in all three
lists; the factor for the slots of a batch is in `PricedAt.held_times` alone, and nothing says at
which list it is to be laid. The work is counted as the written round counts it. Nothing on the
entry file's data: the library makes none (its plan's tie: `entryPlanPriced_of_fit`,
Johnson/G/PlansPriced.lean). Nothing says that a description's data are these data. Nothing on
soundness.


-/
import Johnson.Desc.Ok.NumberPrices.Proved
import Johnson.G.DataAligned

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Number
open _root_.Iop Prob _root_.Run OnBytes.Params OnBytes.Slice OnBytes.Flat OnBytes.Flat.Held
open OnBytes.Maker Johnson.G.OfPlan
open scoped ENNReal

/-- `PricedAt`: four clauses on a round's data d and the planner's round r at its place. -/
structure PricedAt (d : RDT) (r : PlanRound) : Prop where
  entry : d.entry = r.entry
  share : kapSl 128 ^ exAll (Fmt.dsOf d.entry d.kind) *
    (ENNReal.ofReal (r.error.val : ℝ) / 2 ^ d.entry.work) ≤ ((2 : ℝ≥0∞)⁻¹ ^ 128)
  held : ∀ e : ℕ, (e : ℚ) ≤ r.error.val * (nVals (Fmt.dsOf d.entry d.kind) : ℚ) →
    ∃ c : ℝ≥0∞, (e : ℝ≥0∞) ≤ c * (Nat.card (Vals .two (Fmt.dsOf d.entry d.kind)) : ℝ≥0∞) ∧
      kapSl 128 ^ exAll (Fmt.dsOf d.entry d.kind) * (c / 2 ^ d.entry.work) ≤ ((2 : ℝ≥0∞)⁻¹ ^ 128)
  count : ∀ e : ℕ, (e : ℚ) ≤ r.error.val * (nVals (Fmt.dsOf d.entry d.kind) : ℚ) →
    ((e * (bsRound .two d.entry d.kind).w : ℕ) : ℝ≥0∞) ≤
      ((2 : ℝ≥0∞)⁻¹ ^ 128) * (Fintype.card (wT d).Chal : ℝ≥0∞)

/-- One round: the planner's number for the round's error, work counted, with the sampler's bias by
what the round draws, is at most 2 ^ -target. -/
theorem held_share (s : Setting) (hp : s.p = 2 ^ 64 - 2 ^ 32 + 1) (hdeg : s.degree = 3)
    (r : PlanRound) (d : PQ.RD) (hd : d.entry = r.entry) (hnz : r.entry.drawNZ ≤ r.entry.drawE)
    (hw : r.entry.drawE ≠ 0 → r.entry.work + 66 ≤ s.target)
    (hold : roundHolds s (capped s) r = true) :
    kapSl 128 ^ exAll (Fmt.dsOf d.entry d.kind) *
      (ENNReal.ofReal (r.error.val : ℝ) / 2 ^ d.entry.work) ≤ (2 : ℝ≥0∞)⁻¹ ^ s.target := by
  have hc0 : 0 ≤ r.error.val := Binary.val_nonneg _
  have H := (whole_ge s (capped s) r).trans (Binary.le_sound _ _ hold)
  rw [Binary.val_twoTo] at H
  have hu : (3 : ℚ) * (2 : ℚ) ^ (-193 : ℤ) ≤ (capped s).val := by
    rw [capped_two s hp hdeg]
    exact cappedTwo_ge
  have hnum := held_num r.error.val (capped s).val r.entry.drawE r.entry.drawNZ r.entry.work
    s.target hc0 hu hw H
  have hnumR : (((1 + (2 : ℚ) ^ (-128 : ℤ) : ℚ)) : ℝ) ^ (3 * r.entry.drawE) *
      ((r.error.val : ℝ) / 2 ^ r.entry.work) ≤ (2⁻¹ : ℝ) ^ s.target := by
    have h := (Rat.cast_le (K := ℝ)).2 hnum
    simpa only [Rat.cast_mul, Rat.cast_pow, Rat.cast_div, Rat.cast_inv, Rat.cast_ofNat] using h
  rw [exAll_dsOf, hd, Nat.sub_add_cancel hnz, kapSl_ofReal]
  have h2 : (2 : ℝ≥0∞) ^ r.entry.work = ENNReal.ofReal ((2 : ℝ) ^ r.entry.work) := by
    rw [ENNReal.ofReal_pow (by norm_num)]
    norm_num
  have h3 : (2 : ℝ≥0∞)⁻¹ ^ s.target = ENNReal.ofReal ((2⁻¹ : ℝ) ^ s.target) := by
    rw [ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_inv_of_pos (by norm_num)]
    norm_num
  rw [h2, h3, ← ENNReal.ofReal_div_of_pos (by positivity),
    ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal hnumR

/-- A number that is at most the planner's number times the number of typed values, in the extended
non-negative reals. -/
theorem count_le_ofReal (r : PlanRound) (ds : List Fmt.Draw) (e : ℕ)
    (hc : (e : ℚ) ≤ r.error.val * (nVals ds : ℚ)) :
    (e : ℝ≥0∞) ≤ ENNReal.ofReal (r.error.val : ℝ) * (Nat.card (Vals .two ds) : ℝ≥0∞) := by
  have hc0R : (0 : ℝ) ≤ (r.error.val : ℝ) := by exact_mod_cast Binary.val_nonneg r.error
  have hcR : (e : ℝ) ≤ (r.error.val : ℝ) * (nVals ds : ℝ) := by exact_mod_cast hc
  rw [card_vals_all, ← ENNReal.ofReal_natCast (nVals _), ← ENNReal.ofReal_mul hc0R,
    ← ENNReal.ofReal_natCast e]
  exact ENNReal.ofReal_le_ofReal hcR

/-- Place by place, against any rounds of a plan that passes the test. -/
theorem pricedAt_list {w : ℕ} {P : Planned} (h : Desc.chainOk w P = true) (rs : List PlanRound)
    (hrs : ∀ r ∈ rs, r ∈ P.rounds) (ds : List RDT)
    (ha : (ds.map toRD).map (·.entry) = rs.map (·.entry)) : List.Forall₂ PricedAt ds rs := by
  obtain ⟨hh, hs, hT, _⟩ := chainOk_parts h
  obtain ⟨hp, hd, hside⟩ := sideB_parts hs
  have hle : (2 : ℝ≥0∞)⁻¹ ^ P.set.target ≤ ((2 : ℝ≥0∞)⁻¹ ^ 128) := half_pow_anti (le_of_eq hT.symm)
  have a1 : rs.all (sideR P.set.target) = true :=
    List.all_eq_true.2 fun r hr => List.all_eq_true.1 hside r (hrs r hr)
  have a2 : rs.all (roundHolds P.set (capped P.set)) = true :=
    List.all_eq_true.2 fun r hr => List.all_eq_true.1 (rounds_hold hh) r (hrs r hr)
  have H := held_list P.set hp hd (ds.map toRD) rs ha a1 a2
  rw [List.forall₂_map_left_iff] at H
  refine H.imp fun d r Hd => ?_
  have hsh := le_trans
    (held_share P.set Hd.p Hd.degree r (toRD d) Hd.entry Hd.nz Hd.work Hd.holds) hle
  exact ⟨Hd.entry, hsh, fun e he => ⟨_, count_le_ofReal r _ e he, hsh⟩, fun e he => le_trans
    (held_round P.set Hd.p Hd.degree r (toRD d) Hd.entry Hd.log Hd.nz Hd.work Hd.holds e he)
    (mul_le_mul' hle le_rfl)⟩

/-- Against the plan's rounds of the chain. -/
theorem pricedAt_aligned {w : ℕ} {P : Planned} (h : Desc.chainOk w P = true) (ds : List RDT)
    (ha : Aligned (ds.map toRD) P) : List.Forall₂ PricedAt ds (chainRounds P) :=
  pricedAt_list h _ (fun _ hr => List.mem_of_mem_filter hr) ds ha

/-- Against the plan's rounds of the chain without the last. -/
theorem pricedAt_cut {w : ℕ} {P : Planned} (h : Desc.chainOk w P = true) (ds : List RDT)
    (ha : AlignedCut (ds.map toRD) P) : List.Forall₂ PricedAt ds (chainRounds P).dropLast :=
  pricedAt_list h _ (fun _ hr => List.mem_of_mem_filter (List.mem_of_mem_dropLast hr)) ds ha

/-- The clause `held` with the number multiplied by the slots of a batch, at 2 ^ -122. -/
theorem PricedAt.held_times {d : RDT} {r : PlanRound} (h : PricedAt d r) (e : ℕ)
    (he : (e : ℚ) ≤ r.error.val * (nVals (Fmt.dsOf d.entry d.kind) : ℚ)) :
    ∃ c : ℝ≥0∞, ((Desc.slots * e : ℕ) : ℝ≥0∞) ≤
        c * (Nat.card (Vals .two (Fmt.dsOf d.entry d.kind)) : ℝ≥0∞) ∧
      kapSl 128 ^ exAll (Fmt.dsOf d.entry d.kind) * (c / 2 ^ d.entry.work) ≤ ((2 : ℝ≥0∞)⁻¹ ^ 122) :=
          by
  obtain ⟨c, h1, h2⟩ := h.held e he
  refine ⟨(Desc.slots : ℝ≥0∞) * c, ?_, ?_⟩
  · rw [Nat.cast_mul, mul_assoc]
    exact mul_le_mul' le_rfl h1
  · calc kapSl 128 ^ exAll (Fmt.dsOf d.entry d.kind) *
          ((Desc.slots : ℝ≥0∞) * c / 2 ^ d.entry.work)
        = (Desc.slots : ℝ≥0∞) *
          (kapSl 128 ^ exAll (Fmt.dsOf d.entry d.kind) * (c / 2 ^ d.entry.work)) := by
          rw [div_eq_mul_inv, div_eq_mul_inv]
          ring
      _ ≤ (Desc.slots : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹ ^ 128) := mul_le_mul' le_rfl h2
      _ ≤ ((2 : ℝ≥0∞)⁻¹ ^ 122) := rungsLit.2

/-- Each round of a file's data D, against three records of the planner, place by place. -/
def PricedRounds (D : WholeD) (P₁ P₂ P₃ : Planned) : Prop :=
  List.Forall₂ PricedAt D.ds₁ (chainRounds P₁).dropLast ∧
    List.Forall₂ PricedAt D.ds₂ (chainRounds P₂) ∧ List.Forall₂ PricedAt D.ds₃ (chainRounds P₃)

/-- The same, or D is the data of three empty lists. -/
def PricedData (D : WholeD) (P₁ P₂ P₃ : Planned) : Prop :=
  (∃ a, D = WholeD.of a (OnBytes.Three.Whole.of [] [] [])) ∨ PricedRounds D P₁ P₂ P₃

/-- Where the third list has a round, D is not the data of three empty lists. -/
theorem pricedRounds_of_data {D : WholeD} {P₁ P₂ P₃ : Planned} (h : PricedData D P₁ P₂ P₃)
    (hne : D.ds₃ ≠ []) : PricedRounds D P₁ P₂ P₃ := by
  rcases h with ⟨a, rfl⟩ | h
  · exact absurd rfl hne
  · exact h

/-- **The key file's data, under the named premise.** -/
theorem key_pricedAt {m : Made} {D : WholeD} {K₁ K₂ K₃ : Planned} {w₁ w₂ w₃ : ℕ}
    (hD : dataKAt m = .ok D) (hp : KeyPlansPriced m K₁ K₂ K₃) (h₁ : Desc.chainOk w₁ K₁ = true)
    (h₂ : Desc.chainOk w₂ K₂ = true) (h₃ : Desc.chainOk w₃ K₃ = true) :
    PricedData D K₁ K₂ K₃ := by
  rcases key_aligned hD hp with h | ⟨a1, a2, a3⟩
  · exact Or.inl h
  · exact Or.inr ⟨pricedAt_cut h₁ _ a1, pricedAt_aligned h₂ _ a2, pricedAt_aligned h₃ _ a3⟩

/-- **The proof file's data, under the named premise.** -/
theorem proof_pricedAt {m : Made} {D : WholeD} {F₁ F₂ F₃ : Planned} {w₁ w₂ w₃ : ℕ}
    (hD : dataPAt m = .ok D) (hp : ProofPlansPriced m F₁ F₂ F₃) (h₁ : Desc.chainOk w₁ F₁ = true)
    (h₂ : Desc.chainOk w₂ F₂ = true) (h₃ : Desc.chainOk w₃ F₃ = true) :
    PricedData D F₁ F₂ F₃ := by
  rcases proof_aligned hD hp with h | ⟨a1, a2, a3⟩
  · exact Or.inl h
  · exact Or.inr ⟨pricedAt_cut h₁ _ a1, pricedAt_aligned h₂ _ a2, pricedAt_aligned h₃ _ a3⟩

/-- **The key file's data, from public tests alone.** -/
theorem key_pricedAt_of_tests {pol lay KL : ByteArray} {m : Made} {D : WholeD}
    (h : madeOf pol lay KL = .ok m) (hok : Desc.keyOk m.p.chains.made = true)
    (hf : Desc.keyFit m.p.chains.made = true) (hD : dataKAt m = .ok D) :
    ∃ K₁ K₂ K₃, m.p.chains.made.key = [K₁, K₂, K₃] ∧ PricedData D K₁ K₂ K₃ := by
  obtain ⟨K₁, K₂, K₃, hk, h₁, h₂, h₃⟩ := keyOk_parts hok
  exact ⟨K₁, K₂, K₃, hk, key_pricedAt hD (keyPlansPriced_of_fit h hk hf) h₁ h₂ h₃⟩

/-- **The proof file's data, from public tests alone.** -/
theorem proof_pricedAt_of_tests {pol lay KL : ByteArray} {m : Made} {D : WholeD}
    (h : madeOf pol lay KL = .ok m) (hok : Desc.proofOk m.p.chains.made = true)
    (hf : Desc.proofFit m.p.chains.made = true) (hD : dataPAt m = .ok D) :
    ∃ F₁ F₂ F₃, m.p.chains.made.proof = [F₁, F₂, F₃] ∧ PricedData D F₁ F₂ F₃ := by
  obtain ⟨F₁, F₂, F₃, hk, h₁, h₂, h₃, _⟩ := proofOk_parts hok
  exact ⟨F₁, F₂, F₃, hk, proof_pricedAt hD (proofPlansPriced_of_fit h hk hf) h₁ h₂ h₃⟩

/-- **From `PricesAt pol lay KL`: `PricedAt` holds of every round of the two files' data.** -/
theorem pricedAt_of_pricesAt {pol lay KL : ByteArray} (h : PricesAt pol lay KL) :
    ∃ m DK DP K₁ K₂ K₃ F₁ F₂ F₃,
      madeOf pol lay KL = .ok m ∧
      dataKAt m = .ok DK ∧ dataPAt m = .ok DP ∧
      m.p.chains.made.key = [K₁, K₂, K₃] ∧ m.p.chains.made.proof = [F₁, F₂, F₃] ∧
      PricedRounds DK K₁ K₂ K₃ ∧ PricedRounds DP F₁ F₂ F₃ := by
  obtain ⟨m, DK, DP, hm, hok, hfit, hK, hP, nK, nP⟩ := h
  obtain ⟨hk, _, hp⟩ := (Desc.madeOk_iff _).1 hok
  simp only [Desc.fitOk, Bool.and_eq_true] at hfit
  obtain ⟨K₁, K₂, K₃, ek, dK⟩ := key_pricedAt_of_tests hm hk hfit.1.1 hK
  obtain ⟨F₁, F₂, F₃, ef, dP⟩ := proof_pricedAt_of_tests hm hp hfit.2 hP
  exact ⟨m, DK, DP, K₁, K₂, K₃, F₁, F₂, F₃, hm, hK, hP, ek, ef, pricedRounds_of_data dK nK,
    pricedRounds_of_data dP nP⟩

end VerifiableInference.Number

#print axioms VerifiableInference.Number.held_share
#print axioms VerifiableInference.Number.count_le_ofReal
#print axioms VerifiableInference.Number.pricedAt_list
#print axioms VerifiableInference.Number.pricedAt_aligned
#print axioms VerifiableInference.Number.pricedAt_cut
#print axioms VerifiableInference.Number.PricedAt.held_times
#print axioms VerifiableInference.Number.pricedRounds_of_data
#print axioms VerifiableInference.Number.key_pricedAt
#print axioms VerifiableInference.Number.proof_pricedAt
#print axioms VerifiableInference.Number.key_pricedAt_of_tests
#print axioms VerifiableInference.Number.proof_pricedAt_of_tests
#print axioms VerifiableInference.Number.pricedAt_of_pricesAt
