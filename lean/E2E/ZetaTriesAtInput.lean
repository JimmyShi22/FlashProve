-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/ZetaTriesAtInput.lean: the proof-of-work tests at the verifier's parameters at Z, and a number
for the three searches' failures.

Summary. For every Z in scope this file counts the rounds with a proof-of-work test and bounds their
bits. With at least 2 ^ 40 tries in every search, the library's expression for the failure of a
request's three searches is then at most 71 · 2 ^ -256. Eight closed facts are evaluated by Lean's
kernel.

Main results.
  `tries_description`: `Tries` holds at the verifier's parameters at Z, for every Z in scope. `Tries
    r` states: at most 19, 6 and 46 rounds of the three protocols have a test, each of at most 32
    bits.
  `alpha_of_tries`: under `Tries r`, if 2 ^ 40 ≤ cap i + 1 in all three protocols, then `alphaAll
    r.queryLayout capT capL capB 0 0 0 0 0 ≤ 71 · 2 ^ -256` (`alphaAll`: Johnson/Prover/All/Law.lean).

Terms: E2E/HidingTerms.lean.

Limits.
- A bound on a written expression. That `alphaAll` bounds the probability that one of a request's
  three searches runs out is `allY_law` (Johnson/Prover/All/Law.lean), under its own premises. It is
  not used here: E2E/StringsShown.lean applies it for arbitrary parameters, and
  E2E/StringsAtInput.lean has the statement at the verifier's parameters.
- Such a bound says that a proof is produced, not that the verifier accepts it.
- One link, one request: `alphaAll` has no factor for the number of copies.
- Out of scope nothing is proved. No security property is stated.

Definitions and helper lemmas.
  `tests_keyFull`, `tests_proofFull`, `tests_link`, `work_keyFull`, `work_proofFull`, `work_link`,
    `tests_dead`, `work_dead`: at the library's written data, 19 rounds of the key file, 46 of the
    proof file and 6 of the link name bits of proof of work, none more than 32; three empty lists
    have none.
  `testsE`, `workE`, `testsE_eq`, `testsE_whole`, `workE_le`, `workLe_of_E`: a sum and a maximum
    over a chain's rounds, in the form in which the kernel evaluates them round by round (`force`,
    Johnson/G/Eager.lean), and that they are the counts.
  `cnt_fullD`, `bits_fullD`: at the full-size wiring, for arbitrary rounds' data.
  `tests_atFiles`: for Z in scope, whether or not the description is live.
  `tries_atFiles`, `tries_built`: `Tries` at the structure of parameters from which the verifier is
    compiled and at the parameters of the value that the library builds.


-/
import E2E.ZetaTriesWires
import E2E.ZetaAtInput
import Johnson.Prover.All.Law

set_option autoImplicit false
set_option maxRecDepth 1000000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

open scoped ENNReal

namespace AtPublicFiles.ZetaAt
open OnBytes.Prover
open TypedOracleCompiler.Iop TypedOracleCompiler.Joined OnBytes.Maker TypedOracleCompiler.Compile.Batch
open TypedOracleCompiler.Compile.Batch.Cms (batTC batLC wTC wLC wBC)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open OnBytes.Flat (RecFull)
open OnBytes.Slice (frS frZ)
open _root_.Run.PQ (CK View XO Dn)
open _root_.Run (ckP chalP)
open VerifiableInference.OnPublicFiles (threeProtocolsAtFullSize wireOfFullD InnerCompilerInput innerCompilerInputAtFullSize)
open Johnson.G
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles)
open FlashProve (dataAtFiles)
open FlashProve (protocolDataWellFormed flashProveData)
open LPFD.Full (sBG sTG saltG)

/-! ## 1. Two sums, evaluated round by round -/

/-- a plus the number of rounds that name bits of proof of work. -/
def testsE : ℕ → List RDT → ℕ
  | a, [] => a
  | a, d :: ds => force (a + (d.entry.work != 0).toNat) fun v => testsE v ds

theorem testsE_eq : ∀ (ds : List RDT) (a : ℕ), testsE a ds = a + testsT ds
  | [], _ => rfl
  | d :: ds, a => by
    show force (a + (d.entry.work != 0).toNat) (fun v => testsE v ds) =
      a + ((d.entry.work != 0).toNat + testsT ds)
    rw [force_eq, testsE_eq ds, Nat.add_assoc]

theorem testsE_whole (D : WholeD) :
    testsE (testsE (testsE 0 D.ds₁) D.ds₂) D.ds₃ = testsW D := by
  rw [testsE_eq, testsE_eq, testsE_eq]
  unfold testsW
  omega

/-- The greatest of a and the rounds' bits of proof of work. -/
def workE : ℕ → List RDT → ℕ
  | a, [] => a
  | a, d :: ds => force (max a d.entry.work) fun v => workE v ds

theorem workE_le : ∀ (ds : List RDT) (a : ℕ), a ≤ workE a ds ∧ ∀ d ∈ ds, d.entry.work ≤ workE a ds
  | [], a => ⟨Nat.le_refl _, fun _ h => absurd h List.not_mem_nil⟩
  | d :: ds, a => by
    have e : workE a (d :: ds) = workE (max a d.entry.work) ds := force_eq _ _
    obtain ⟨h1, h2⟩ := workE_le ds (max a d.entry.work)
    rw [e]
    refine ⟨(le_max_left _ _).trans h1, fun x hx => ?_⟩
    rcases List.mem_cons.1 hx with rfl | hx
    · exact (le_max_right _ _).trans h1
    · exact h2 x hx

theorem workLe_of_E {β : ℕ} {D : WholeD} (h : workE (workE (workE 0 D.ds₁) D.ds₂) D.ds₃ ≤ β) :
    WorkLe β D := by
  obtain ⟨a1, b1⟩ := workE_le D.ds₁ 0
  obtain ⟨a2, b2⟩ := workE_le D.ds₂ (workE 0 D.ds₁)
  obtain ⟨a3, b3⟩ := workE_le D.ds₃ (workE (workE 0 D.ds₁) D.ds₂)
  exact ⟨fun d hd => (b1 d hd).trans (a2.trans (a3.trans h)),
    fun d hd => (b2 d hd).trans (a3.trans h), fun d hd => (b3 d hd).trans h⟩

/-! ## 2. Closed numbers, by Lean's kernel -/

theorem tests_keyFull : testsW dKeyFull = 19 :=
  testsE_whole dKeyFull ▸ (by decide +kernel :
    testsE (testsE (testsE 0 dKeyFull.ds₁) dKeyFull.ds₂) dKeyFull.ds₃ = 19)

theorem tests_proofFull : testsW dProofFull = 46 :=
  testsE_whole dProofFull ▸ (by decide +kernel :
    testsE (testsE (testsE 0 dProofFull.ds₁) dProofFull.ds₂) dProofFull.ds₃ = 46)

theorem work_keyFull : WorkLe 32 dKeyFull :=
  workLe_of_E (by decide +kernel)

theorem work_proofFull : WorkLe 32 dProofFull :=
  workLe_of_E (by decide +kernel)

theorem tests_link : testsR PV.EntryFive.dsF = 6 := by decide +kernel

theorem work_link : ∀ d ∈ PV.EntryFive.dsF, d.entry.work ≤ 32 := by decide +kernel

theorem tests_dead : testsW FlashProve.emptyRoundsData = 0 := by decide +kernel

theorem work_dead : WorkLe 32 FlashProve.emptyRoundsData :=
  workLe_of_E (by decide +kernel)

/-! ## 3. At the full-size wiring, for arbitrary rounds' data -/

section
variable {X : Type} (A : (frS.toDecR frZ 402653181).Claims X)
  (R : (frS.toDecR frZ 402653181).RelationsAndEncoding A) (DK DP : WholeD)
  (runK : RecFull → View → View → View → Bool) (runP : X × RecFull → View → View → View → Bool)
  (ds : List TypedOracleCompiler.Run.PQ.RD) (xs : List XO) (dec : RecFull × RecFull → View → Bool)
  (rK rP : RecFull) (depthReq : ℕ) (early : X → X) (salt : ℕ)
  (P : (threeProtocolsAtFullSize A R DK DP runK runP ds xs dec rK rP depthReq early salt).Provers)
  (K depthReqT : ℕ)

local notation "Ff" => threeProtocolsAtFullSize A R DK DP runK runP ds xs dec rK rP depthReq early salt
local notation "Lo" => OnBytes.Flat.Files.withProvers Ff P
local notation "Ww" =>
  wireOfFullD A R DK DP runK runP ds xs dec rK rP depthReq early salt P K depthReqT

include A R DK DP runK runP ds xs dec rK rP depthReq early salt P K depthReqT

/-- **The tests of the three wirings**, as computable functions of the rounds' data. -/
theorem cnt_fullD : cnt (Lo).offline.shape (Ff).annT (wTC Ww).sh = testsW DK ∧
    cnt (Lo).link.shape (Ff).annL (wLC Ww).sh = testsR ds ∧
    cnt (Lo).onlineBatch.loc.shape (Lo).onlineBatch.ann (wBC Ww).sh = testsW DP :=
  ⟨cnt_wqWhole (ckP .two) K (chalP .two K) (DK.at frS.P.T.a) (OnBytes.Flat.front₀ rK)
      (OnBytes.Flat.join₀ rK) ByteArray.empty OnBytes.Flat.silK runK,
    cnt_wqW (ckP .two) K (chalP .two K) ds frS.P.T.a xs dec,
    cnt_wqWhole (ckP .two) K (chalP .two K) (DP.at frS.P.T.a) (OnBytes.Flat.front₀ rP)
      (OnBytes.Flat.join₀ rP) ByteArray.empty OnBytes.Flat.silP runP⟩

/-- **Their bits.** -/
theorem bits_fullD {β : ℕ} (hK : WorkLe β DK) (hL : ∀ d ∈ ds, d.entry.work ≤ β)
    (hP : WorkLe β DP) : BitsLe β (Lo).offline.shape (Ff).annT (wTC Ww).sh ∧
    BitsLe β (Lo).link.shape (Ff).annL (wLC Ww).sh ∧
    BitsLe β (Lo).onlineBatch.loc.shape (Lo).onlineBatch.ann (wBC Ww).sh :=
  ⟨bits_wqWhole (ckP .two) K (chalP .two K) (DK.at frS.P.T.a) (OnBytes.Flat.front₀ rK)
      (OnBytes.Flat.join₀ rK) ByteArray.empty OnBytes.Flat.silK runK hK,
    bits_wqW (ckP .two) K (chalP .two K) ds frS.P.T.a xs dec hL,
    bits_wqWhole (ckP .two) K (chalP .two K) (DP.at frS.P.T.a) (OnBytes.Flat.front₀ rP)
      (OnBytes.Flat.join₀ rP) ByteArray.empty OnBytes.Flat.silP runP hP⟩

end

/-! ## 4. In scope -/

/-- **For Z in scope, whether or not the description is live: the two files' rounds with a test, and
their bits.** -/
theorem tests_atFiles (Z : PublicFiles) (scope : InScope Z = true) :
    testsW (dataAtFiles flashProveData Z).DK ≤ 19 ∧ testsW (dataAtFiles flashProveData Z).DP ≤ 46 ∧
      WorkLe 32 (dataAtFiles flashProveData Z).DK ∧ WorkLe 32 (dataAtFiles flashProveData Z).DP := by
  cases live : protocolDataWellFormed (asDescriptionFiles Z) with
  | true =>
    have eK := (AtPublicFiles.Reads.key_data Z scope live).trans writtenKFull_eq
    have eP := (AtPublicFiles.Reads.proof_data Z scope live).trans writtenPFull_eq
    refine ⟨?_, ?_, ?_, ?_⟩
    · show testsW ((dataAtFiles flashProveData Z).DK.at frS.P.T.a) ≤ _
      rw [eK, tests_keyFull]
    · show testsW ((dataAtFiles flashProveData Z).DP.at frS.P.T.a) ≤ _
      rw [eP, tests_proofFull]
    · show WorkLe 32 ((dataAtFiles flashProveData Z).DK.at frS.P.T.a)
      rw [eK]
      exact work_keyFull
    · show WorkLe 32 ((dataAtFiles flashProveData Z).DP.at frS.P.T.a)
      rw [eP]
      exact work_proofFull
  | false =>
    rw [(AtPublicFiles.Reads.data_shut Z live).1, (AtPublicFiles.Reads.data_shut Z live).2, tests_dead]
    exact ⟨Nat.zero_le _, Nat.zero_le _, work_dead, work_dead⟩

/-- **Six facts on the tests**: at most 19, 6 and 46 rounds of the three protocols have a
proof-of-work test, each of at most 32 bits. -/
structure Tries (r : InnerCompilerInput) : Prop where
  nT : cnt r.protocol.offline.shape r.offlineRoundSplits (wTC r.queryLayout).sh ≤ 19
  nL : cnt r.protocol.link.shape r.linkRoundSplits (wLC r.queryLayout).sh ≤ 6
  nB : cnt r.protocol.onlineBatch.loc.shape r.protocol.onlineBatch.ann (wBC r.queryLayout).sh ≤ 46
  bT : BitsLe 32 r.protocol.offline.shape r.offlineRoundSplits (wTC r.queryLayout).sh
  bL : BitsLe 32 r.protocol.link.shape r.linkRoundSplits (wLC r.queryLayout).sh
  bB : BitsLe 32 r.protocol.onlineBatch.loc.shape r.protocol.onlineBatch.ann (wBC r.queryLayout).sh

theorem tries_atFiles (Z : PublicFiles) (scope : InScope Z = true)
    (c₀ : VerifiableInference.Digest) (m₀ : List (Dig 256)) :
    Tries (innerCompilerInputAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings c₀ m₀)) := by
  obtain ⟨h1, h2, h3, h4⟩ := tests_atFiles Z scope
  have c3 := cnt_fullD (dataAtFiles flashProveData Z).A
    (OnBytes.Flat.relationsAndEncodingOfClaims (dataAtFiles flashProveData Z).A (dataAtFiles flashProveData Z).E)
    (dataAtFiles flashProveData Z).DK (dataAtFiles flashProveData Z).DP (dataAtFiles flashProveData Z).runK (dataAtFiles flashProveData Z).runP
    PV.EntryFive.dsF PV.EntryFive.xsF (dataAtFiles flashProveData Z).dec (dataAtFiles flashProveData Z).G.rec₀
    (dataAtFiles flashProveData Z).G.z₀.2 (sBG (dataAtFiles flashProveData Z).G).logLeaves (dataAtFiles flashProveData Z).G.early
    (saltG (dataAtFiles flashProveData Z).G) (dataAtFiles flashProveData Z).P
    (LPFD.Full.KF (dataAtFiles flashProveData Z).DK (dataAtFiles flashProveData Z).DP) (sTG (dataAtFiles flashProveData Z).G).logLeaves
  have b3 := bits_fullD (dataAtFiles flashProveData Z).A
    (OnBytes.Flat.relationsAndEncodingOfClaims (dataAtFiles flashProveData Z).A (dataAtFiles flashProveData Z).E)
    (dataAtFiles flashProveData Z).DK (dataAtFiles flashProveData Z).DP (dataAtFiles flashProveData Z).runK (dataAtFiles flashProveData Z).runP
    PV.EntryFive.dsF PV.EntryFive.xsF (dataAtFiles flashProveData Z).dec (dataAtFiles flashProveData Z).G.rec₀
    (dataAtFiles flashProveData Z).G.z₀.2 (sBG (dataAtFiles flashProveData Z).G).logLeaves (dataAtFiles flashProveData Z).G.early
    (saltG (dataAtFiles flashProveData Z).G) (dataAtFiles flashProveData Z).P
    (LPFD.Full.KF (dataAtFiles flashProveData Z).DK (dataAtFiles flashProveData Z).DP) (sTG (dataAtFiles flashProveData Z).G).logLeaves
    h3 work_link h4
  exact
    { nT := le_of_eq_of_le c3.1 h1
      nL := le_of_eq (c3.2.1.trans tests_link)
      nB := le_of_eq_of_le c3.2.2 h2
      bT := b3.1
      bL := b3.2.1
      bB := b3.2.2 }

theorem tries_built (Z : PublicFiles) (scope : InScope Z = true) (c : VerifiableInference.Digest)
    (m : (FlashProve.descriptionOfDataOnBytes flashProveData).More) :
    Tries ((FlashProve.descriptionOfDataOnBytes flashProveData).input Z c m) := tries_atFiles Z scope c m

/-- **At the verifier's parameters at Z**, for every Z in scope. -/
theorem tries_description (Z : PublicFiles) (scope : InScope Z = true) :
    ∀ (c : VerifiableInference.Digest) (m : (VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).More),
      Tries ((VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).input Z c m) :=
  VerifierAndGoals.ofBuilt
    (Q := fun D => ∀ (c : VerifiableInference.Digest) (m : D.More), Tries (D.input Z c m))
    fun c m => tries_built Z scope c m

/-! ## 5. The three searches' failures -/

/-- **With at least 2 ^ 40 tries in every search the three searches' failures are together at most
71 · 2 ^ -256.** -/
theorem alpha_of_tries (r : InnerCompilerInput) (h : Tries r) (capT capL capB : ℕ → ℕ)
    (hT : ∀ i, 2 ^ 40 ≤ capT i + 1) (hL : ∀ i, 2 ^ 40 ≤ capL i + 1)
    (hB : ∀ i, 2 ^ 40 ≤ capB i + 1) :
    alphaAll r.queryLayout capT capL capB 0 0 0 0 0 ≤ 71 * (2⁻¹ : ℝ≥0∞) ^ 256 := by
  have e : (2 : ℕ) ^ 32 * 256 = 2 ^ 40 := by norm_num
  have a1 := capFail_le_cnt 32 256 capT (fun i => e ▸ hT i) _ _ _ 0 h.bT
  have a2 := capFail_le_cnt 32 256 capL (fun i => e ▸ hL i) _ _ _ 0 h.bL
  have a3 := capFail_le_cnt 32 256 capB (fun i => e ▸ hB i) _ _ _ 0 h.bB
  have n1 : (cnt r.protocol.offline.shape r.offlineRoundSplits (wTC r.queryLayout).sh : ℝ≥0∞) ≤ 19 := by exact_mod_cast h.nT
  have n2 : (cnt r.protocol.link.shape r.linkRoundSplits (wLC r.queryLayout).sh : ℝ≥0∞) ≤ 6 := by exact_mod_cast h.nL
  have n3 : (cnt r.protocol.onlineBatch.loc.shape r.protocol.onlineBatch.ann (wBC r.queryLayout).sh : ℝ≥0∞) ≤ 46 := by exact_mod_cast h.nB
  unfold alphaAll
  simp only [add_zero]
  calc _ ≤ 19 * (2⁻¹ : ℝ≥0∞) ^ 256 + 6 * (2⁻¹ : ℝ≥0∞) ^ 256 + 46 * (2⁻¹ : ℝ≥0∞) ^ 256 :=
        add_le_add (add_le_add (a1.trans (mul_le_mul' n1 le_rfl))
          (a2.trans (mul_le_mul' n2 le_rfl))) (a3.trans (mul_le_mul' n3 le_rfl))
    _ = 71 * (2⁻¹ : ℝ≥0∞) ^ 256 := by
        rw [← add_mul, ← add_mul]
        norm_num

end AtPublicFiles.ZetaAt

/- Each command below is expected to print a subset of [propext, Classical.choice, Quot.sound]. -/
#print axioms AtPublicFiles.ZetaAt.tries_description
#print axioms AtPublicFiles.ZetaAt.alpha_of_tries
#print axioms AtPublicFiles.ZetaAt.tests_keyFull
#print axioms AtPublicFiles.ZetaAt.tests_proofFull
#print axioms AtPublicFiles.ZetaAt.work_keyFull
#print axioms AtPublicFiles.ZetaAt.work_proofFull
#print axioms AtPublicFiles.ZetaAt.tests_link
#print axioms AtPublicFiles.ZetaAt.work_link
#print axioms AtPublicFiles.ZetaAt.testsE_eq
#print axioms AtPublicFiles.ZetaAt.testsE_whole
#print axioms AtPublicFiles.ZetaAt.workE_le
#print axioms AtPublicFiles.ZetaAt.workLe_of_E
#print axioms AtPublicFiles.ZetaAt.tests_dead
#print axioms AtPublicFiles.ZetaAt.work_dead
#print axioms AtPublicFiles.ZetaAt.cnt_fullD
#print axioms AtPublicFiles.ZetaAt.bits_fullD
#print axioms AtPublicFiles.ZetaAt.tests_atFiles
#print axioms AtPublicFiles.ZetaAt.tries_atFiles
#print axioms AtPublicFiles.ZetaAt.tries_built
