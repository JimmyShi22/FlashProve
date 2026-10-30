-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
E2E/PlaysAtLetters.lean

Three small turns of PlaysAtNine.lean's and PlaysAtTen.lean's statements, and a law for a stand at 10. No
file is bent.

  `quiet_guarded`, `quiet_job`   behind the guard a half stops as it did: needsField leaves a part's
                 stops as they are: a stand's premise at the half at 10
  `plays_at_ten_thr`   `plays_at_ten` with hop from the pair: ThrS … → isSome: a letter ∀ E, Hand → Field
                 pays that with Thr's own E
  `plays_nine_real`, `plays_ten_real`   the two at wts := K₁.weights, rnd := randKey K₁, the readers
                 that `tableKey` lays: so that «at the real halves» is said at the real table

Limits. As in the two files. A YES AT «SOME» IS A YES AT ANY COLUMNS. tt stays a letter: the filled table
is TableFilled.lean's. Nothing on completeness, on soundness or on what is hidden.

NOT IN FRONT OF A LAW OVER COINS: `plays_at_ten_thr`, `plays_nine_real`, `plays_ten_real` bear this
label; the rule is at its home, the head of Johnson/Bind/ForProver/FiveFieldsAt.lean. Their ground:
as the two laws they call. None: the bar is flat.
-/
import E2E.PlaysAtTen
import E2E.KeyNoStop
import Johnson.Desc.ProofFile.Honest.K12.HalfReturns

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace AtPublicFiles.PlaysAtNine
open ProofFile.Honest ProofFile.Honest.K14 ProofFile.Honest.K12
open OnBytes (TableKey)
open VerifiableInference.Desc (Place Block)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open VerifiableInference.Desc.Key (Source)
open AtPublicFiles.KeyFile (KeyParts)
open AtPublicFiles.KeySharedThread (parKey randKey)
open _root_.Desc.K14 (St)
open _root_.Desc.K14.Honest (Eight)
open AtPublicFiles.AtFiles.Full (QK PF)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub)
open AtPublicFiles.KeyLay (withTestsOnUAndOmega)
open AtPublicFiles.TreesAtNine (JN TN)
open AtPublicFiles.HalvesAreJobs (pU pO JO)
open AtPublicFiles.Stops (QuietHalf)

/-- **Behind the guard a half stops as it did.** -/
theorem quiet_guarded {V W X : Type} (h : Placed V W X) (H : QuietHalf h) :
    QuietHalf h.needsField := by
  intro p hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
  exact H q hq

/-- **A test's half behind the guard is quiet.** -/
theorem quiet_job {V W X : Type} (J : TestJob W X) :
    QuietHalf (proverSideOfProximityTest J : Placed V W X).needsField := by
  refine quiet_guarded _ fun p hp => ?_
  rcases List.mem_cons.1 hp with rfl | hp
  · exact first_quiet J
  · rcases List.mem_cons.1 hp with rfl | hp
    · exact rest_quiet J
    · cases hp

section
variable
  (K₀ : KeyPub) (hK₀ : fullPub = some K₀) {W₀ Rc X₀ X Wk P₁ Wt : Type}
  (Xs : Source) (Nr : H2U.PlaceNums) (K₁ : KeyParts W₀ Rc X₀ X Wk)
  (ℓ : WitLens Wt) (Nm : NumbersS) (Mg₀ : Common W₀ Rc TableKey → MeaningS St P₁ Wt)
  (tk : Nat → Nat → Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table)
  (tt : Nat → Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table)
  (rest : Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Wt)
  (Kp : Nat → St → St → Prop) (Vd : Common W₀ Rc TableKey → Prop) (w : Common W₀ Rc TableKey)

include hK₀ in
/-- **`plays_at_ten` with hop from the pair.**
NOT IN FRONT OF A LAW OVER COINS (the rule, and this statement's ground: this file's head). -/
theorem plays_at_ten_thr (wts : W₀ → Weights) (rnd : Rc → TableRand) (e : parKey Xs PF = QK)
    (B : Eight (parKey Xs PF)) (hs : K₁.send = ⟨parKey Xs PF, 0⟩)
    (hsp : K₁.lin.S.sharedSplitNeeded = true) (own₀ : X₀)
    (h7 : tt 7 = ownTbl 1 (JO Xs K₁ B) own₀ 43 (fun _ _ _ => true))
    (htt : ∀ τ, τ < 3 → tt (8 + τ) = testTbl 1 (JO Xs K₁ B) own₀ 43 (fun _ _ _ => true) τ)
    (Said : Nat → Coins (keyBook K₀) → Mid (Common W₀ Rc TableKey) X₀ → Prop)
    (hop : ∀ k s m E, ThrS (TN Xs Nr (withTestsOnUAndOmega K₁ pU pO) ℓ Nm Mg₀ wts rnd tk tt rest Kp Vd w) Said 10
      k s m E → m.opened.isSome = true) :
    PlaysS (TN Xs Nr (withTestsOnUAndOmega K₁ pU pO) ℓ Nm Mg₀ wts rnd tk tt rest Kp Vd w) Said 10 :=
  fun blk hblk k s m E ds l hS =>
    plays_at_ten K₀ hK₀ Xs Nr K₁ ℓ Nm Mg₀ wts rnd tk tt rest Kp Vd w e B hs hsp own₀ h7 htt
      (fun _ _ m => m.opened.isSome = true) (fun _ _ h => h) blk hblk k s m E ds l
      ⟨hS.1, hop _ _ _ _ hS⟩

include hK₀ in
/-- **`plays_at_nine` at the readers that the parts hold.**
NOT IN FRONT OF A LAW OVER COINS (the rule, and this statement's ground: this file's head). -/
theorem plays_nine_real (e : parKey Xs PF = QK) (B : Eight (parKey Xs PF))
    (hs : K₁.send = ⟨parKey Xs PF, 0⟩) (hsp : K₁.lin.S.sharedSplitNeeded = true) (own₀ : X₀)
    (htt : ∀ τ, τ < 4 → tt (3 + τ) = testTbl 1 (JN Xs K₁ B) own₀ 8 (fun _ _ _ => true) τ) :
    Plays (TN Xs Nr (withTestsOnUAndOmega K₁ pU pO) ℓ Nm Mg₀ K₁.weights (randKey K₁) tk tt rest Kp Vd w) 9 :=
  plays_at_nine K₀ hK₀ Xs Nr K₁ ℓ Nm Mg₀ K₁.weights (randKey K₁) tk tt rest Kp Vd w e B hs hsp own₀ htt

include hK₀ in
/-- **`plays_at_ten_thr` at the readers that the parts hold.**
NOT IN FRONT OF A LAW OVER COINS (the rule, and this statement's ground: this file's head). -/
theorem plays_ten_real (e : parKey Xs PF = QK) (B : Eight (parKey Xs PF))
    (hs : K₁.send = ⟨parKey Xs PF, 0⟩) (hsp : K₁.lin.S.sharedSplitNeeded = true) (own₀ : X₀)
    (h7 : tt 7 = ownTbl 1 (JO Xs K₁ B) own₀ 43 (fun _ _ _ => true))
    (htt : ∀ τ, τ < 3 → tt (8 + τ) = testTbl 1 (JO Xs K₁ B) own₀ 43 (fun _ _ _ => true) τ)
    (Said : Nat → Coins (keyBook K₀) → Mid (Common W₀ Rc TableKey) X₀ → Prop)
    (hop : ∀ k s m E, ThrS (TN Xs Nr (withTestsOnUAndOmega K₁ pU pO) ℓ Nm Mg₀ K₁.weights (randKey K₁) tk tt rest
      Kp Vd w) Said 10 k s m E → m.opened.isSome = true) :
    PlaysS (TN Xs Nr (withTestsOnUAndOmega K₁ pU pO) ℓ Nm Mg₀ K₁.weights (randKey K₁) tk tt rest Kp Vd w) Said 10 :=
  plays_at_ten_thr K₀ hK₀ Xs Nr K₁ ℓ Nm Mg₀ tk tt rest Kp Vd w K₁.weights (randKey K₁) e B hs hsp own₀
    h7 htt Said hop

end

end AtPublicFiles.PlaysAtNine

#print axioms AtPublicFiles.PlaysAtNine.quiet_guarded
#print axioms AtPublicFiles.PlaysAtNine.quiet_job
#print axioms AtPublicFiles.PlaysAtNine.plays_at_ten_thr
#print axioms AtPublicFiles.PlaysAtNine.plays_nine_real
#print axioms AtPublicFiles.PlaysAtNine.plays_ten_real
