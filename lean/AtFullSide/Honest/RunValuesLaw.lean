-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/Honest/RunValuesLaw.lean: the law of the four run values under the provers' coins.

  runValueBytes_injective, runValueBytes_size   the bytes of a run value
  coinRuns_rarely_zero     at a coin of the frame's product form, each value is 32 zero bytes with
                           chance at most 2^-256
  onlineRuns_rarely_zero, offlineRuns_rarely_zero   the same at the provers, where the maker and the
                           offline description return

Limits.
  * The law is stated where the public files make a prover. In the fall-back arm the provers send
    the fixed messages.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import E2E.TheHonestProverStatements

set_option autoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.AtFiles.HonestTerm
open Iop Prob
open scoped ENNReal
open AtPublicFiles.Bridge AtPublicFiles.Cut
open ProofFile.Honest (Purse)
open ProofFile.Honest.Term (OnlineReturn onlineMaker)
open VerifiableInference.Desc (Chain)
open VerifierAndGoals (PublicFiles)
open P5J (TS)

theorem runValueBytes_size (value : RunValue) : (runValueBytes value).size = 32 := by
  simp [runValueBytes, ByteArray.size]

theorem runValueBytes_injective : Function.Injective runValueBytes := by
  intro a b h
  funext i
  have e : (Array.ofFn fun i => (a i).val.toUInt8) = Array.ofFn fun i => (b i).val.toUInt8 :=
    congrArg ByteArray.data h
  have f : (a i).val.toUInt8 = (b i).val.toUInt8 := by
    have := congrArg (fun array : Array UInt8 => array[i.val]?) e
    simpa [Array.getElem?_ofFn, i.isLt] using this
  have g := congrArg UInt8.toNat f
  first
    | simp only [Nat.toUInt8, UInt8.toNat_ofNat'] at g
    | simp only [Nat.toUInt8, UInt8.toNat_ofNat] at g
    | simp at g
  have ha := (a i).isLt
  have hb := (b i).isLt
  apply Fin.ext
  omega

set_option synthInstance.maxHeartbeats 400000 in
theorem card_runValue : Fintype.card RunValue = 2 ^ 256 := by
  show Fintype.card (Fin 32 → Fin 256) = 2 ^ 256
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
  norm_num

/-- **One value of a set of 2^256 has chance at most 2^-256.** -/
theorem chance_of_one_value {R : Type} [Fintype R] [Nonempty R] (card : Fintype.card R = 2 ^ 256)
    (bad : R → Prop) (once : ∀ a b, bad a → bad b → a = b) :
    pr (unif R) {value | bad value} ≤ (2⁻¹ : ℝ≥0∞) ^ 256 := by
  classical
  have h : cnt bad ≤ 1 := by
    unfold cnt
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_le_one_iff.mpr fun a b => Subtype.ext (once a.1 b.1 a.2 b.2)
  refine (pr_unif_le_of_cnt_le h).trans (le_of_eq ?_)
  rw [card, Nat.cast_one, one_div, Nat.cast_pow, Nat.cast_ofNat, ENNReal.inv_pow]

theorem pr_snd {C D : Type} [Fintype C] [Nonempty C] [Fintype D] [Nonempty D] (P : D → Prop) :
    pr (unif (C × D)) {c | P c.2} = pr (unif D) {d | P d} := by
  show (unif (C × D)).toOuterMeasure _ = (unif D).toOuterMeasure _
  conv_rhs => rw [← map_snd_unif (C := C) (D := D)]
  rw [PMF.toOuterMeasure_map_apply]
  rfl

theorem pr_fst {C D : Type} [Fintype C] [Nonempty C] [Fintype D] [Nonempty D] (P : C → Prop) :
    pr (unif (C × D)) {c | P c.1} = pr (unif C) {d | P d} := by
  show (unif (C × D)).toOuterMeasure _ = (unif C).toOuterMeasure _
  conv_rhs => rw [← map_fst_unif (C := C) (D := D)]
  rw [PMF.toOuterMeasure_map_apply]
  rfl

theorem runOk_false_once (a b : RunValue) (ha : Fmt.runOk (runValueBytes a) = false)
    (hb : Fmt.runOk (runValueBytes b) = false) : a = b := by
  simp only [Fmt.runOk, decide_eq_false_iff_not, not_not] at ha hb
  exact runValueBytes_injective (ha.trans hb.symm)

/-- **Each of two values of a set of 2^256 has chance at most 2^-256 of being the one refused.** -/
theorem pairRuns_rarely_zero {A B R : Type} [Fintype A] [Nonempty A] [Fintype B] [Nonempty B]
    [Fintype R] [Nonempty R] (card : Fintype.card R = 2 ^ 256) (read : R → ByteArray)
    (once : ∀ a b, Fmt.runOk (read a) = false → Fmt.runOk (read b) = false → a = b)
    (fin : Fintype ((A × R) × (B × R))) (ne : Nonempty ((A × R) × (B × R))) :
    @RunsRarelyZero _ fin ne fun coin => (read coin.1.2, read coin.2.2) := by
  obtain rfl : fin = instFintypeProd _ _ := Subsingleton.elim _ _
  constructor
  · show pr _ {coin : (A × R) × (B × R) | Fmt.runOk (read coin.1.2) = false} ≤ _
    rw [pr_fst (P := fun c : A × R => Fmt.runOk (read c.2) = false),
      pr_snd (P := fun v : R => Fmt.runOk (read v) = false)]
    exact chance_of_one_value card _ once
  · show pr _ {coin : (A × R) × (B × R) | Fmt.runOk (read coin.2.2) = false} ≤ _
    rw [pr_snd (P := fun c : B × R => Fmt.runOk (read c.2) = false),
      pr_snd (P := fun v : R => Fmt.runOk (read v) = false)]
    exact chance_of_one_value card _ once

local instance (priority := high) nonemptyRunValueAtLaw : Nonempty RunValue := ⟨fun _ => 0⟩

local instance (priority := high) purseNonempty (rows : List (ProofFile.Honest.Addr × ProofFile.Honest.Due)) :
    Nonempty (Purse rows) := ⟨default⟩

set_option synthInstance.maxHeartbeats 400000 in
/-- **Each run value of a coin of the frame's form is 32 zero bytes with chance at most 2^-256.** -/
theorem coinRuns_rarely_zero {A B : Type} [Fintype A] [Nonempty A] [Fintype B] [Nonempty B]
    (fin : Fintype ((A × RunValue) × (B × RunValue)))
    (ne : Nonempty ((A × RunValue) × (B × RunValue))) :
    @RunsRarelyZero _ fin ne (coinRuns (A := A) (B := B)) :=
  pairRuns_rarely_zero card_runValue runValueBytes runOk_false_once fin ne

variable {files : PublicFiles}

/-- A map of coins carried along an equation of families. -/
theorem runs_along_family {Y : Type} {E : ExtSpec} {Q : InteractiveOracleProof Y E} {Wt : Type} {F G : Family Q Wt}
    (e : F = G) (runs : F.Coin → RunPair)
    (h : @RunsRarelyZero F.Coin F.finCoin F.neCoin runs) :
    @RunsRarelyZero G.Coin G.finCoin G.neCoin (e ▸ runs) := by
  subst e
  exact h

/-- A map of coins carried along an equation of provers. -/
theorem runs_along_prover {Y : Type} {E : ExtSpec} {Q : InteractiveOracleProof Y E} {Wt : Type} {F G : Honest Q Wt}
    (e : F = G) (runs : F.Coin → RunPair)
    (h : @RunsRarelyZero F.Coin F.finCoin F.neCoin runs) :
    @RunsRarelyZero G.Coin G.finCoin G.neCoin (e ▸ runs) := by
  subst e
  exact h

/-- **The online prover's two run values**, where the maker, the places and the first chain return.
-/
theorem onlineRuns_rarely_zero {returned : OnlineReturn files} {places : H2U.Places4}
    {firstChain : Chain TS ProofFile.Cl} (made : onlineMaker files = .ok returned)
    (hp : H2U.placesOfMade returned.Z.made = .ok places)
    (hc : ProofFile.onlineFirstChainAt returned.Z = .ok firstChain) :
    @RunsRarelyZero (onlineProver files).Coin (onlineProver files).finCoin
      (onlineProver files).neCoin (onlineRuns files) := by
  apply runs_along_family (onlineWithRuns_family files)
  have e : onlineWithRuns files =
      ⟨onlineProverAt returned places firstChain, onlineRunsAt returned places firstChain⟩ := by
    simp only [onlineWithRuns, made, hp, hc]
  rw [e]
  exact coinRuns_rarely_zero (A := Purse returned.B.shared)
    (B := Purse returned.B.first × Purse returned.B.second) _ _

/-- **The offline prover's two run values**, where the public files make the offline description. -/
theorem offlineRuns_rarely_zero (parts : Parts files) {description : OfflineDescription}
    (h : offlineDescription files = .ok description) :
    @RunsRarelyZero (offlineProver parts).Coin (offlineProver parts).finCoin
      (offlineProver parts).neCoin (offlineRuns parts) := by
  apply runs_along_prover (offlineWithRuns_prover parts)
  have e : offlineWithRuns parts =
      ⟨offlineProverWithEncodedTable files (keyFileDescription description.source description.numbers description.later) parts.book
        (parts.prover description) runValueBytes runValueBytes (offlineStart description),
        offlineRunsAt parts description⟩ := by
    simp only [offlineWithRuns, h]
  rw [e]
  exact coinRuns_rarely_zero (A := Purse parts.book.shared)
    (B := Purse parts.book.first × Purse parts.book.second) _ _

/-- A coin fixes two strings of 32 bytes. -/
def RunsHaveTheirSize {Coin : Type} (runs : Coin → RunPair) : Prop :=
  ∀ coin, (runs coin).1.size = 32 ∧ (runs coin).2.size = 32

theorem coinRuns_sizes {A B : Type} : RunsHaveTheirSize (coinRuns (A := A) (B := B)) :=
  fun _ => ⟨runValueBytes_size _, runValueBytes_size _⟩

/-- **The online prover's coins fix strings of 32 bytes**, where the three functions return. -/
theorem onlineRuns_sizes {returned : OnlineReturn files} {places : H2U.Places4}
    {firstChain : Chain TS ProofFile.Cl} (made : onlineMaker files = .ok returned)
    (hp : H2U.placesOfMade returned.Z.made = .ok places)
    (hc : ProofFile.onlineFirstChainAt returned.Z = .ok firstChain) : RunsHaveTheirSize (onlineRuns files) := by
  have along : ∀ {F G : Family (protocolAtFiles files).onlineBatch.loc (FullSizeMatrix × (protocolAtFiles files).EncodingRandomness × (protocolAtFiles files).OutOfDomainSeed)}
      (e : F = G) (runs : F.Coin → RunPair), RunsHaveTheirSize runs →
      RunsHaveTheirSize (e ▸ runs : G.Coin → RunPair) := by
    intro F G e runs h
    subst e
    exact h
  apply along (onlineWithRuns_family files)
  have e : onlineWithRuns files =
      ⟨onlineProverAt returned places firstChain, onlineRunsAt returned places firstChain⟩ := by
    simp only [onlineWithRuns, made, hp, hc]
  rw [e]
  exact coinRuns_sizes (A := Purse returned.B.shared)
    (B := Purse returned.B.first × Purse returned.B.second)

/-- **The offline prover's coins fix strings of 32 bytes**, where the description returns. -/
theorem offlineRuns_sizes (parts : Parts files) {description : OfflineDescription}
    (h : offlineDescription files = .ok description) : RunsHaveTheirSize (offlineRuns parts) := by
  have along : ∀ {F G : Honest (protocolAtFiles files).offline (FullSizeMatrix × (protocolAtFiles files).EncodingRandomness × (protocolAtFiles files).OutOfDomainSeed)}
      (e : F = G) (runs : F.Coin → RunPair), RunsHaveTheirSize runs →
      RunsHaveTheirSize (e ▸ runs : G.Coin → RunPair) := by
    intro F G e runs h
    subst e
    exact h
  apply along (offlineWithRuns_prover parts)
  have e : offlineWithRuns parts =
      ⟨offlineProverWithEncodedTable files (keyFileDescription description.source description.numbers description.later) parts.book
        (parts.prover description) runValueBytes runValueBytes (offlineStart description),
        offlineRunsAt parts description⟩ := by
    simp only [offlineWithRuns, h]
  rw [e]
  exact coinRuns_sizes (A := Purse parts.book.shared)
    (B := Purse parts.book.first × Purse parts.book.second)

end AtPublicFiles.AtFiles.HonestTerm

#print axioms AtPublicFiles.AtFiles.HonestTerm.onlineRuns_sizes
#print axioms AtPublicFiles.AtFiles.HonestTerm.offlineRuns_sizes
#print axioms AtPublicFiles.AtFiles.HonestTerm.onlineRuns_rarely_zero
#print axioms AtPublicFiles.AtFiles.HonestTerm.offlineRuns_rarely_zero
#print axioms AtPublicFiles.AtFiles.HonestTerm.coinRuns_rarely_zero
#print axioms AtPublicFiles.AtFiles.HonestTerm.runValueBytes_size
#print axioms AtPublicFiles.AtFiles.HonestTerm.runValueBytes_injective
#print axioms AtPublicFiles.AtFiles.HonestTerm.chance_of_one_value
#print axioms AtPublicFiles.AtFiles.HonestTerm.pr_snd
#print axioms AtPublicFiles.AtFiles.HonestTerm.runOk_false_once
