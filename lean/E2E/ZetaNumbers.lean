-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/ZetaNumbers.lean: bounds on the numbers of E2E/ZetaAtWiring.lean at the rounds' data from which
`VerifierAndGoals.verify` is compiled.

Summary. The bound on `zetaW` needs upper bounds on the protocols' rounds, on the depths of their
request trees and on the leaves of all their trees. The first two hold for all public files Z, the
third for every Z in scope, whether or not the description is live. Five closed facts are evaluated
by Lean's kernel.

Main results.
  `rounds_atFiles`: for every Z, the key file's and the proof file's rounds and the depths of their
    request trees are together at most 2 ^ 20. The library's one test on numbers counts them
    (`fit_theLay`, Johnson/Goal/Conditions/NumbersAtThe.lean; `cntWhole`,
    Johnson/Top/Pub/CountsTop.lean).
  `leaves_atFiles`: for every Z in scope, the key file's trees have fewer than 2 ^ 37 leaves in all
    and the proof file's fewer than 2 ^ 39. If the description is live, the rounds' data are the
    library's written data; if not, three empty lists each (E2E/ReadsAtFiles.lean).

Terms: E2E/HidingTerms.lean.

Limits. Bounds, not the numbers themselves. Out of scope nothing is proved about the leaves. No
security property is stated.

Definitions and helper lemmas.
  `leaves_keyFull`, `leaves_proofFull`, `leaves_link`, `rounds_link`, `leaves_dead`: at the
    library's written data: the two bounds above; the link's trees have 19,030,016 leaves, in 41
    rounds; three empty lists have none.
  `leavesE`, `leavesE_eq`, `leavesE_whole`: the two long sums are evaluated round by round (`force`,
    Johnson/G/Eager.lean).
  `rounds_le_cnt`: a file's rounds and a depth are together at most the library's count `cntWhole`.


-/
import E2E.ZetaAtWiring
import E2E.ReadsAtFiles
import Johnson.Goal.Conditions.NumbersAtThe

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace AtPublicFiles.ZetaAt
open OnBytes.Maker Johnson.G
open OnBytes.Slice (frS frZ)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles)
open FlashProve (dataAtFiles)
open FlashProve (protocolDataWellFormed flashProveData)
open LPFD.Full (sBG sTG)

/-! ## 1. Closed numbers, by Lean's kernel -/

/-- a plus the leaves of all trees that a chain of rounds sends: each sum is evaluated before the
next round is looked at (`force`, Johnson/G/Eager.lean). -/
def leavesE : ℕ → List RDT → ℕ
  | a, [] => a
  | a, d :: ds => force (a + treesSum d.trees) fun v => leavesE v ds

theorem leavesE_eq : ∀ (ds : List RDT) (a : ℕ), leavesE a ds = a + leavesT ds
  | [], _ => rfl
  | d :: ds, a => by
    show force (a + treesSum d.trees) (fun v => leavesE v ds) = a + (treesSum d.trees + leavesT ds)
    rw [force_eq, leavesE_eq ds, Nat.add_assoc]

theorem leavesE_whole (D : WholeD) :
    leavesE (leavesE (leavesE 0 D.ds₁) D.ds₂) D.ds₃ = leavesW D := by
  rw [leavesE_eq, leavesE_eq, leavesE_eq]
  unfold leavesW
  omega

theorem leaves_keyFull : leavesW dKeyFull < 2 ^ 37 :=
  leavesE_whole dKeyFull ▸ (by decide +kernel :
    leavesE (leavesE (leavesE 0 dKeyFull.ds₁) dKeyFull.ds₂) dKeyFull.ds₃ < 2 ^ 37)

theorem leaves_proofFull : leavesW dProofFull < 2 ^ 39 :=
  leavesE_whole dProofFull ▸ (by decide +kernel :
    leavesE (leavesE (leavesE 0 dProofFull.ds₁) dProofFull.ds₂) dProofFull.ds₃ < 2 ^ 39)
theorem leaves_link : leavesR PV.EntryFive.dsF = 19030016 := by decide +kernel
theorem rounds_link : PV.EntryFive.dsF.length = 41 := by decide +kernel
theorem leaves_dead : leavesW FlashProve.emptyRoundsData = 0 := by decide +kernel

/-! ## 2. At every Z: rounds and request trees -/

/-- A file's rounds and the depth of its request tree are counted in the library's bound on typed
queries. -/
theorem rounds_le_cnt (D : WholeD) (dep : ℕ) :
    roundsW D + dep ≤ OnBytes.K.Arm.cntWhole D dep := by
  unfold roundsW OnBytes.K.Arm.cntWhole
  omega

/-- **At every Z: the key file's and the proof file's rounds and the depths of their request trees
are together at most 2 ^ 20**: the library's one test on numbers. -/
theorem rounds_atFiles (Z : PublicFiles) :
    roundsW (dataAtFiles flashProveData Z).DK + (sTG (dataAtFiles flashProveData Z).G).logLeaves +
      (roundsW (dataAtFiles flashProveData Z).DP + (sBG (dataAtFiles flashProveData Z).G).logLeaves) ≤ 2 ^ 20 := by
  have h := (VerifiableInference.OnPublicFiles.frameFitFullD_parts (FlashProve.fit_theLay Z)).hcnt
  unfold VerifiableInference.OnPublicFiles.cntFrameFullD at h
  have a := rounds_le_cnt ((dataAtFiles flashProveData Z).DK.at frS.P.T.a)
    (dataAtFiles flashProveData Z).G.k.oneTime.binding.logLeaves
  have b := rounds_le_cnt ((dataAtFiles flashProveData Z).DP.at frS.P.T.a)
    (dataAtFiles flashProveData Z).G.c.first.binding.logLeaves
  have a' : roundsW (dataAtFiles flashProveData Z).DK + (sTG (dataAtFiles flashProveData Z).G).logLeaves ≤ _ := a
  have b' : roundsW (dataAtFiles flashProveData Z).DP + (sBG (dataAtFiles flashProveData Z).G).logLeaves ≤ _ := b
  have q : FlashProve.theQueries = 2 ^ 20 := rfl
  omega

/-! ## 3. In scope: the leaves -/

/-- **For Z in scope, whether or not the description is live: the leaves of all trees of the key
file and of the proof file.** -/
theorem leaves_atFiles (Z : PublicFiles) (scope : InScope Z = true) :
    leavesW (dataAtFiles flashProveData Z).DK < 2 ^ 37 ∧ leavesW (dataAtFiles flashProveData Z).DP < 2 ^ 39 := by
  cases live : protocolDataWellFormed (asDescriptionFiles Z) with
  | true =>
    constructor
    · show leavesW ((dataAtFiles flashProveData Z).DK.at frS.P.T.a) < _
      rw [AtPublicFiles.Reads.key_data Z scope live, writtenKFull_eq]
      exact leaves_keyFull
    · show leavesW ((dataAtFiles flashProveData Z).DP.at frS.P.T.a) < _
      rw [AtPublicFiles.Reads.proof_data Z scope live, writtenPFull_eq]
      exact leaves_proofFull
  | false =>
    rw [(AtPublicFiles.Reads.data_shut Z live).1, (AtPublicFiles.Reads.data_shut Z live).2, leaves_dead]
    exact ⟨by norm_num, by norm_num⟩

end AtPublicFiles.ZetaAt

/- Each command below is expected to print a subset of [propext, Classical.choice, Quot.sound]. -/
#print axioms AtPublicFiles.ZetaAt.leaves_keyFull
#print axioms AtPublicFiles.ZetaAt.leaves_proofFull
#print axioms AtPublicFiles.ZetaAt.leaves_link
#print axioms AtPublicFiles.ZetaAt.rounds_atFiles
#print axioms AtPublicFiles.ZetaAt.leaves_atFiles
#print axioms AtPublicFiles.ZetaAt.leavesE_eq
#print axioms AtPublicFiles.ZetaAt.leavesE_whole
#print axioms AtPublicFiles.ZetaAt.rounds_link
#print axioms AtPublicFiles.ZetaAt.leaves_dead
#print axioms AtPublicFiles.ZetaAt.rounds_le_cnt
