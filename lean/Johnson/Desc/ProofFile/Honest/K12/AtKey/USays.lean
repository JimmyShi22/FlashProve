-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtKey/USays.lean: the key file's test on G_u: «the rows that the test takes in hold at the
words of the job's plain rows, in front of the test» (`SaysInFront`, E2E/OfflineSayAtRun.lean), at every state at which
the thread's invariant holds at border 9 and at every coin that the book lends the test's two parts.

  `says_in_front_of_says`   `SaysAt` (K12/AsksWhole.lean) is `SaysInFront` at the job's own test and plain rows: one text
  `says_in_front_at_key`    the sentence, from the invariant alone
  `say_at_stand_at_laid`    the same over every stand of the thread's pair, at a caller's thread and second condition
                            (`laidThread`, `laidLetter`, ULaid.lean), at the test's place by its name
  `job_is_written`          the job is `jobKU` (E2E/KeyHalves.lean) at the senders' own data and readers
  `say_at_stand_written`    the sentence in that job's letters, at `laidThread`, whose table's letter tt is `ttF`
  `say_at_stand_any_table`  the same at every letter tt of the table and every second condition

Limits.
- NOT IN FRONT OF A LAW OVER COINS (the rule: the head of Johnson/Bind/ForProver/FiveFieldsAt.lean): the thread's
  invariant is a premise.
- The job is `AN` (E2E/SaysAtNine.lean) at the senders' own readers.
- Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtKey.ULaid
import E2E.OfflineSayAtRun

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace ProofFile.Honest.K12.AtKey
open ProofFile.Honest ProofFile.Honest.K14 ProofFile.Honest.K12
open ProofFile.Honest.K12.Light (SaysAt ManyJob plainMany)
open ProofFile.Honest.K12.Light.ItemLaws (AN)
open AtPublicFiles.OfflineRows (SaysInFront)
open OnBytes (TableKey)
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open VerifiableInference.Desc.Key (Source Xi)
open AtPublicFiles.KeyFile (KeyParts)
open AtPublicFiles.KeySharedThread (threadKey parKey sentKey)
open AtPublicFiles.KeyAsksKey (tableKey)
open AtPublicFiles.KeyStandOne (inK)
open AtPublicFiles.KeyStandMember (keyOf)
open AtPublicFiles.KeyFiveFields (pubKey)
open AtPublicFiles.KeyLay (withTestsOnUAndOmega)
open AtPublicFiles.HalvesAreJobs (pO)
open _root_.Desc.K14 (St)
open _root_.Desc.K14.Honest (Eight)
open AtPublicFiles.AtFiles (KeySourced)
open AtPublicFiles.AtFiles.Full (QK PF par_sourced)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub foldedTestPlace)
open AtPublicFiles.TreesAtNine (JN)
open AtPublicFiles.TableFilled (TU)
open AtPublicFiles.StandAtNine (K1)
open AtPublicFiles.HalvesAreJobs (pU)
open AtPublicFiles.KeyLay (jobKU bsOf stOf wtOf rdOf)

/-- **One text.** -/
theorem says_in_front_of_says {W X : Type} (A : ManyJob W X) (w : W) (fr : Front X) (C : TestCoins)
    (h : SaysAt A w fr C) : SaysInFront A.toRun.toTest w fr (plainMany A w fr C) := h

section
variable (K₀ : KeyPub) (hK₀ : fullPub = some K₀) {W₀ Rc X₀ X Wk P₁ Wt : Type}
  (Xs : Source) (Nr : H2U.PlaceNums) (K₁ : KeyParts W₀ Rc X₀ X Wk)
  (ℓ : WitLens Wt) (Nm : NumbersS) (Mg₀ : Common W₀ Rc TableKey → MeaningS St P₁ Wt)
  (tk : Nat → Nat → Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table)
  (rest : Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Wt)
  (Kp : Nat → St → St → Prop) (Vd : Common W₀ Rc TableKey → Prop) (w : Common W₀ Rc TableKey)
  (B : Eight (parKey Xs PF))
  (tt : Nat → Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table)

include hK₀ in
/-- **The rows that the test takes in hold, in front of the test.** -/
theorem says_in_front_at_key (e : parKey Xs PF = QK) {layO : OnBytes.TreeLay}
    (hQ : Plan2 (parKey Xs PF) (sentKey Xs PF) layO) {k : Coins (keyBook K₀)} {s : St}
    {m : ProofFile.Honest.Mid (Common W₀ Rc TableKey) X₀} {E : Env}
    (u : Thr (TU K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w tt) 9 k s m E)
    (c : RowCoins [(firstPart (JN Xs K₁ B) : Part Empty _ _), restPart (JN Xs K₁ B)])
    (hc : lendRow (keyBook K₀) ((keyBook K₀).rowsOf 1) (k.look 1) (JN Xs K₁ B).p.place
      [(firstPart (JN Xs K₁ B) : Part Empty _ _), restPart (JN Xs K₁ B)] 0 = .ok c) :
    SaysInFront (JN Xs K₁ B) m.st.input (frontOf m)
      (plainMany (AN (X₀ := X₀) Xs K₁ B) m.st.input (frontOf m) (restCoins (JN Xs K₁ B) c.2.1)) :=
  says_in_front_of_says _ _ _ _ (says_at_key K₀ hK₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B tt e hQ u c hc)

end

variable {W₀ Rc X₀ X Wk P₁ Wt : Type}
  (Xs : Source) (Nr : H2U.PlaceNums) (K₀ : KeyPub) (K' : KeyParts W₀ Rc X₀ X Wk)
  (ℓ : WitLens Wt) (Nm : NumbersS) (Mg₀ : Common W₀ Rc TableKey → MeaningS St P₁ Wt)
  (tk : Nat → Nat → Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table)
  (rest : Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Wt)
  (Kp : ℕ → St → St → Prop) (Vd : Common W₀ Rc TableKey → Prop)
  (f : W₀ → Weights) (g : Rc → ℕ → TableRand) (Z₀ : ProofFile.Pub)
  (w₀ : W₀) (rc : Rc) (x : Xi) (B : Eight (parKey Xs PF)) (own₀ : X₀)
  (r o : Placed (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) X)

/-- **Over every stand of the thread's pair at border 9, at a caller's letters.** -/
theorem say_at_stand_at_laid {Z : VerifierAndGoals.PublicFiles} (hs : KeySourced Z Xs Nr PF)
    (scope : VerifierAndGoals.InScope Z = true) (hK₀ : fullPub = some K₀) :
    ∀ k st m₀ E₀ (c : RowCoins [(firstPart (JN Xs (K1 Xs K' f g Z₀) B) : Part Empty _ _), restPart (JN Xs (K1 Xs K' f g Z₀) B)]),
      ThrS (laidThread Xs Nr K₀ K' ℓ Nm Mg₀ tk rest Kp Vd f g Z₀ w₀ rc x B own₀ r o)
        (laidLetter Xs Nr K₀ K' ℓ Nm Mg₀ tk rest Kp Vd f g Z₀ w₀ rc x B own₀ r o) 9 k st m₀ E₀ →
      lendRow (keyBook K₀) ((keyBook K₀).rowsOf 1) (k.look 1) foldedTestPlace
        [(firstPart (JN Xs (K1 Xs K' f g Z₀) B) : Part Empty _ _), restPart (JN Xs (K1 Xs K' f g Z₀) B)] 0 = .ok c →
      SaysInFront (JN Xs (K1 Xs K' f g Z₀) B) m₀.st.input (frontOf m₀)
        (plainMany (AN (X₀ := X₀) Xs (K1 Xs K' f g Z₀) B) m₀.st.input (frontOf m₀) (restCoins (JN Xs (K1 Xs K' f g Z₀) B) c.2.1)) := by
  intro k st m₀ E₀ c hA hc
  obtain ⟨layO, hQ⟩ := AtPublicFiles.KeySharedThread.plan_key hs scope
  exact says_in_front_at_key K₀ hK₀ Xs Nr (K1 Xs K' f g Z₀) ℓ Nm Mg₀ tk rest Kp Vd _ B _ (par_sourced hs scope) hQ hA.1 c hc

/-- **The job is the written job at the senders' own readers**: the eight as the senders' public data give them. -/
theorem job_is_written : (AN (X₀ := X₀) Xs (K1 Xs K' f g Z₀) B) = (jobKU (X := X₀) (K1 Xs K' f g Z₀).send pU (bsOf (K1 Xs K' f g Z₀)) (stOf (K1 Xs K' f g Z₀)) (wtOf (K1 Xs K' f g Z₀)) (rdOf (K1 Xs K' f g Z₀))) := by
  have hb : bsOf (K1 Xs K' f g Z₀) = [B.b1, B.b2, B.b3, B.b4, B.b5, B.b6, B.b7, B.b8] := by
    show (_root_.Desc.K14.blocks (parKey Xs PF)).getD [] = _
    rw [B.made]
    rfl
  rw [hb]
  rfl

/-- **The same in the written job's letters.** -/
theorem say_at_stand_written {Z : VerifierAndGoals.PublicFiles} (hs : KeySourced Z Xs Nr PF)
    (scope : VerifierAndGoals.InScope Z = true) (hK₀ : fullPub = some K₀) :
    ∀ k st m₀ E₀ (c : RowCoins [(firstPart (jobKU (X := X₀) (K1 Xs K' f g Z₀).send pU (bsOf (K1 Xs K' f g Z₀)) (stOf (K1 Xs K' f g Z₀)) (wtOf (K1 Xs K' f g Z₀)) (rdOf (K1 Xs K' f g Z₀))).toRun.toTest : Part Empty _ _),
        restPart (jobKU (X := X₀) (K1 Xs K' f g Z₀).send pU (bsOf (K1 Xs K' f g Z₀)) (stOf (K1 Xs K' f g Z₀)) (wtOf (K1 Xs K' f g Z₀)) (rdOf (K1 Xs K' f g Z₀))).toRun.toTest]),
      ThrS (laidThread Xs Nr K₀ K' ℓ Nm Mg₀ tk rest Kp Vd f g Z₀ w₀ rc x B own₀ r o)
        (laidLetter Xs Nr K₀ K' ℓ Nm Mg₀ tk rest Kp Vd f g Z₀ w₀ rc x B own₀ r o) 9 k st m₀ E₀ →
      lendRow (keyBook K₀) ((keyBook K₀).rowsOf 1) (k.look 1) foldedTestPlace
        [(firstPart (jobKU (X := X₀) (K1 Xs K' f g Z₀).send pU (bsOf (K1 Xs K' f g Z₀)) (stOf (K1 Xs K' f g Z₀)) (wtOf (K1 Xs K' f g Z₀)) (rdOf (K1 Xs K' f g Z₀))).toRun.toTest : Part Empty _ _),
          restPart (jobKU (X := X₀) (K1 Xs K' f g Z₀).send pU (bsOf (K1 Xs K' f g Z₀)) (stOf (K1 Xs K' f g Z₀)) (wtOf (K1 Xs K' f g Z₀)) (rdOf (K1 Xs K' f g Z₀))).toRun.toTest] 0 = .ok c →
      SaysInFront (jobKU (X := X₀) (K1 Xs K' f g Z₀).send pU (bsOf (K1 Xs K' f g Z₀)) (stOf (K1 Xs K' f g Z₀)) (wtOf (K1 Xs K' f g Z₀)) (rdOf (K1 Xs K' f g Z₀))).toRun.toTest m₀.st.input (frontOf m₀)
        (plainMany (jobKU (X := X₀) (K1 Xs K' f g Z₀).send pU (bsOf (K1 Xs K' f g Z₀)) (stOf (K1 Xs K' f g Z₀)) (wtOf (K1 Xs K' f g Z₀)) (rdOf (K1 Xs K' f g Z₀))) m₀.st.input (frontOf m₀)
          (restCoins (jobKU (X := X₀) (K1 Xs K' f g Z₀).send pU (bsOf (K1 Xs K' f g Z₀)) (stOf (K1 Xs K' f g Z₀)) (wtOf (K1 Xs K' f g Z₀)) (rdOf (K1 Xs K' f g Z₀))).toRun.toTest c.2.1)) := by
  rw [← job_is_written Xs K' f g Z₀ B]
  exact say_at_stand_at_laid Xs Nr K₀ K' ℓ Nm Mg₀ tk rest Kp Vd f g Z₀ w₀ rc x B own₀ r o hs scope hK₀

/-- **The same at every letter of the table and every second condition**: the sentence spends the invariant alone. -/
theorem say_at_stand_any_table {Z : VerifierAndGoals.PublicFiles} (hs : KeySourced Z Xs Nr PF)
    (scope : VerifierAndGoals.InScope Z = true) (hK₀ : fullPub = some K₀)
    (tt : Nat → Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table)
    (Said : ℕ → Coins (keyBook K₀) → ProofFile.Honest.Mid (Common W₀ Rc TableKey) X₀ → Prop) :
    ∀ k st m₀ E₀ (c : RowCoins [(firstPart (jobKU (X := X₀) (K1 Xs K' f g Z₀).send pU (bsOf (K1 Xs K' f g Z₀)) (stOf (K1 Xs K' f g Z₀)) (wtOf (K1 Xs K' f g Z₀)) (rdOf (K1 Xs K' f g Z₀))).toRun.toTest : Part Empty _ _),
        restPart (jobKU (X := X₀) (K1 Xs K' f g Z₀).send pU (bsOf (K1 Xs K' f g Z₀)) (stOf (K1 Xs K' f g Z₀)) (wtOf (K1 Xs K' f g Z₀)) (rdOf (K1 Xs K' f g Z₀))).toRun.toTest]),
      ThrS (threadKey Xs Nr PF (keyOf (pubKey Z₀ Xs.chains) Xs PF { withTestsOnUAndOmega (K1 Xs K' f g Z₀) pU pO with rng := r, own := o } f g) ℓ Nm Mg₀
          (tableKey Xs PF K₀ (keyOf (pubKey Z₀ Xs.chains) Xs PF { withTestsOnUAndOmega (K1 Xs K' f g Z₀) pU pO with rng := r, own := o } f g) tk tt) rest Kp Vd (inK w₀ rc x)) Said 9 k st m₀ E₀ →
      lendRow (keyBook K₀) ((keyBook K₀).rowsOf 1) (k.look 1) foldedTestPlace
        [(firstPart (jobKU (X := X₀) (K1 Xs K' f g Z₀).send pU (bsOf (K1 Xs K' f g Z₀)) (stOf (K1 Xs K' f g Z₀)) (wtOf (K1 Xs K' f g Z₀)) (rdOf (K1 Xs K' f g Z₀))).toRun.toTest : Part Empty _ _),
          restPart (jobKU (X := X₀) (K1 Xs K' f g Z₀).send pU (bsOf (K1 Xs K' f g Z₀)) (stOf (K1 Xs K' f g Z₀)) (wtOf (K1 Xs K' f g Z₀)) (rdOf (K1 Xs K' f g Z₀))).toRun.toTest] 0 = .ok c →
      SaysInFront (jobKU (X := X₀) (K1 Xs K' f g Z₀).send pU (bsOf (K1 Xs K' f g Z₀)) (stOf (K1 Xs K' f g Z₀)) (wtOf (K1 Xs K' f g Z₀)) (rdOf (K1 Xs K' f g Z₀))).toRun.toTest m₀.st.input (frontOf m₀)
        (plainMany (jobKU (X := X₀) (K1 Xs K' f g Z₀).send pU (bsOf (K1 Xs K' f g Z₀)) (stOf (K1 Xs K' f g Z₀)) (wtOf (K1 Xs K' f g Z₀)) (rdOf (K1 Xs K' f g Z₀))) m₀.st.input (frontOf m₀)
          (restCoins (jobKU (X := X₀) (K1 Xs K' f g Z₀).send pU (bsOf (K1 Xs K' f g Z₀)) (stOf (K1 Xs K' f g Z₀)) (wtOf (K1 Xs K' f g Z₀)) (rdOf (K1 Xs K' f g Z₀))).toRun.toTest c.2.1)) := by
  obtain ⟨layO, hQ⟩ := AtPublicFiles.KeySharedThread.plan_key hs scope
  obtain ⟨B⟩ := hQ.eight
  rw [← job_is_written Xs K' f g Z₀ B]
  intro k st m₀ E₀ c hA hc
  exact says_in_front_at_key K₀ hK₀ Xs Nr (K1 Xs K' f g Z₀) ℓ Nm Mg₀ tk rest Kp Vd _ B tt (par_sourced hs scope) hQ hA.1 c hc

end ProofFile.Honest.K12.AtKey

end

#print axioms ProofFile.Honest.K12.AtKey.says_in_front_of_says
#print axioms ProofFile.Honest.K12.AtKey.says_in_front_at_key
#print axioms ProofFile.Honest.K12.AtKey.say_at_stand_at_laid
#print axioms ProofFile.Honest.K12.AtKey.job_is_written
#print axioms ProofFile.Honest.K12.AtKey.say_at_stand_written
#print axioms ProofFile.Honest.K12.AtKey.say_at_stand_any_table
