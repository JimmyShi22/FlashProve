-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/OwnSayAtStand.lean: THE ROWS THAT THE KEY FILE'S OWN TEST TAKES IN HOLD, AT A STAND OF THE LAST THREAD.

  `own_says_at_stand`: SaysInFront at the own test's job, at every stand at border 2 at the lent coins: say_stand at
  the state where the own test begins, from the tie of the chain's words to the job's rows (htie, with the coins bound by lendRow).

What stays a premise: htie, and what say_stand and third_shaped ask. No stand is shown to exist here. lendRow's return is a premise.
The statement speaks of answers, which depend on the pads.
This file says nothing on completeness, soundness or hiding.
Limit: NOT IN FRONT OF A LAW OVER COINS (the rule: Johnson/Bind/ForProver/FiveFieldsAt.lean's head). The premises of this theorem read two kinds of coins: k (a run's coins) and, through the input, rc (the committer's randomness).
The stand ThrS reads k and the input, and under it stand the thread's invariants and what is said. The lending reads k and ties c.
htie reads k through the witness and through c. So this theorem may not be used as a step toward a statement about distributions over these coins.
-/
import E2E.KeyLastDone
import E2E.OfflineSayAtRun

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

noncomputable section

namespace AtPublicFiles.KeyLastChain
open ProofFile.Honest ProofFile.Honest.K12
open ProofFile.Honest.K14 (jobOmega WitLens)
open ProofFile.Honest.K12.Light (plainMany)
open OnBytes (TableKey Oracle)
open OnBytes.Means (Words Says tableSize layoutOf)
open OnBytes.Slice (GE rdE readE begun)
open VerifiableInference.Desc (Block Place Wit)
open VerifiableInference.Desc.K12 (T12 proximityTestKind guardedProximityTestParts)
open VerifiableInference.Desc.K12.Seat (enterOwn)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open VerifiableInference.Desc.Third (S₃ Border)
open VerifiableInference.Desc.Third.Law (dotI)
open VerifiableInference.Desc.Key (Xi FirstState Source LaterPlaces descriptionFromSource thirdPar)
open VerifiableInference.Desc.Own (keyFits)
open _root_.Desc.K14 (St)
open AtPublicFiles.KeyFile (KeyParts)
open AtPublicFiles.KeySharedThread (threadKey)
open AtPublicFiles.KeyThread (KeyFill)
open AtPublicFiles.KeyLay (pWK jobKWAt parIK parWK shapeOK)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub)
open AtPublicFiles.KeyTest (jobOwn)
open AtPublicFiles.AtFiles (KeySourced ThirdShaped sh₃ SF CF)
open AtPublicFiles.AtFiles.Full (A0 QK)
open H2K.Member (piKWFull)
open Johnson.RunOne.KeyRows1 (plan₁)

open AtPublicFiles.OfflineRows (SaysInFront)

section
variable {W₀ Rc X₀ X Wk Cells M Smp Rec P₂ Wt₂ Wd : Type} {Z : VerifierAndGoals.PublicFiles}
  (K₀ : KeyPub)
  (Xs : Source) (Nr : H2U.PlaceNums) (Pl : LaterPlaces) (K : KeyParts W₀ Rc X₀ X Wk)
  (L : KeyFill (keyBook K₀) W₀ Rc Cells M Smp Rec)
  (ℓ₂ : WitLens Wt₂) (Nm : NumbersS)
  (Mg₂ : Common W₀ Rc TableKey → MeaningS St P₂ Wt₂)
  (tb₂ : Fmt.TreeSource → Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table)
  (rest₂ : Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Wt₂)
  (Kp₂ : Nat → St → St → Prop) (Vd₂ : Common W₀ Rc TableKey → Prop)
  (w₂ : Common W₀ Rc TableKey) (w₀ : W₀) (rc : Rc) (x : Xi)
  (hs₁ : List (Placed (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) X))
  (tb₁ : Fmt.TreeSource → Coins (keyBook K₀) → Local W₀ Rc Xi Unit → List Fmt.Drawn → Place × Table)
  (Said₁ : Nat → Coins (keyBook K₀) → Mid (Local W₀ Rc Xi Unit) X → Prop)
  (Said₂ : Nat → Coins (keyBook K₀) → Mid (Common W₀ Rc TableKey) X₀ → Prop)
  (d : (Xi × FirstState) × St)
  (Dt : Local W₀ Rc Xi Unit → MeaningS St (Xi × FirstState) (Wit Cells Unit M × Words Cb.Gl.E))
  (n₁ n₂ : Nat) (Vd : Local W₀ Rc Xi Unit → Prop) (w : Local W₀ Rc Xi Unit)
  (dfltT : Place × Table) (dfltM : Mid (Local W₀ Rc Xi Unit) X)
  (JI JW : ProofFile.Honest.K1.SendJob Wd X) (A : ProofFile.Honest.K14.SendPub)
  (lift : Local W₀ Rc Xi Unit → Wd) (ask : Local W₀ Rc Xi Unit → ProofFile.Honest.K14.Ask)

set_option maxHeartbeats 4000000 in
/-- **The own test's rows**: the rows that the own test takes in hold, at a stand at border 2, at the coins that the book lends. -/
theorem own_says_at_stand (hs : KeySourced Z Xs Nr Pl) (scope : VerifierAndGoals.InScope Z = true)
    (hfit : ∀ v, (threadKey Xs Nr Pl K ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂).valid v →
      keyFits v.key QK.par.S.fold.index = true)
    (hd : d.1.2.lin = none)
    (hsame : L.R.same = fun a b => readE a = readE b)
    (ho₀ : (plan₁ (AtPublicFiles.KeyThread.one₀ Xs)).orc 0 = some 0) (ho₂ : (plan₁ (AtPublicFiles.KeyThread.one₀ Xs)).orc 2 = some 9)
    (htie : ∀ k st m E
      (c : RowCoins [(firstPart (jobKWAt Xs Nr Pl JI JW A lift ask).toRun.toTest : Part (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) X),
        restPart (jobKWAt Xs Nr Pl JI JW A lift ask).toRun.toTest]), ThrS (threadOwn Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt (mlKey (val₁Key Xs L)) n₁ n₂ Vd w dfltT dfltM) (saidOwn Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt (mlKey (val₁Key Xs L)) n₁ n₂ Vd w dfltT dfltM) 2 k st m E →
      lendRow (keyBook K₀) ((keyBook K₀).rowsOf 2) (k.look 2) (jobKWAt Xs Nr Pl JI JW A lift ask).toRun.toTest.p.place
        [(firstPart (jobKWAt Xs Nr Pl JI JW A lift ask).toRun.toTest : Part (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) X),
          restPart (jobKWAt Xs Nr Pl JI JW A lift ask).toRun.toTest] 0 = .ok c → ∀ G, st.st.groups[st.loc.own]? = some G →
      ∀ o ∈ G.members.toList, ∀ pt, ∀ i < tableSize st.st o pt,
        wordsKey (val₁Key Xs L) st ((threadOwn Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt (mlKey (val₁Key Xs L)) n₁ n₂ Vd w dfltT dfltM).wit k m.st.input (m.st.heard ++ [])) o pt i =
          wordsAt (begun st.st st.loc.own G) (layoutOf st.st G)
            (plainMany (jobKWAt Xs Nr Pl JI JW A lift ask) m.st.input (frontOf m) (restCoins (jobKWAt Xs Nr Pl JI JW A lift ask).toRun.toTest c.2.1)) o pt i ) :
    ∀ k st m E (c : RowCoins [(firstPart (jobKWAt Xs Nr Pl JI JW A lift ask).toRun.toTest : Part (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) X),
        restPart (jobKWAt Xs Nr Pl JI JW A lift ask).toRun.toTest]),
      ThrS (threadOwn Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt (mlKey (val₁Key Xs L)) n₁ n₂ Vd w dfltT dfltM) (saidOwn Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt (mlKey (val₁Key Xs L)) n₁ n₂ Vd w dfltT dfltM) 2 k st m E →
      lendRow (keyBook K₀) ((keyBook K₀).rowsOf 2) (k.look 2) (jobKWAt Xs Nr Pl JI JW A lift ask).toRun.toTest.p.place
        [(firstPart (jobKWAt Xs Nr Pl JI JW A lift ask).toRun.toTest : Part (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) X),
          restPart (jobKWAt Xs Nr Pl JI JW A lift ask).toRun.toTest] 0 = .ok c →
      SaysInFront (jobKWAt Xs Nr Pl JI JW A lift ask).toRun.toTest m.st.input (frontOf m)
        (plainMany (jobKWAt Xs Nr Pl JI JW A lift ask) m.st.input (frontOf m) (restCoins (jobKWAt Xs Nr Pl JI JW A lift ask).toRun.toTest c.2.1)) := by
  have hZ := third_shaped Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt (mlKey (val₁Key Xs L))
    (tableKey Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt (mlKey (val₁Key Xs L)) n₁ n₂ Vd
      (fun _ _ _ => True) keptOwn w dfltT dfltM) n₁ n₂ Vd (fun _ _ _ => True) keptOwn w hs scope hfit hd (fun _ _ _ => true)
  have hfun : ∀ k v h s s', (threadOwn Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt (mlKey (val₁Key Xs L)) n₁ n₂ Vd w dfltT dfltM).begun k v h s → (threadOwn Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt (mlKey (val₁Key Xs L)) n₁ n₂ Vd w dfltT dfltM).begun k v h s' → s = s' := fun k v h s s' a b =>
    Except.ok.inj ((show (descriptionFromSource Xs Nr Pl).start₃ _ _ _ = .ok s from a).symm.trans b)
  intro k st m E c hT hc
  have hen := enters_own Xs Nr Pl JI JW A lift ask rfl rfl hfun hT.1 (hT.2.1)
  exact say_stand Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt n₁ n₂ Vd w dfltT dfltM hs scope hZ hsame
    ho₀ ho₂ [] hT.1 hen _ (htie k st m E c hT hc)

end

end AtPublicFiles.KeyLastChain

#print axioms AtPublicFiles.KeyLastChain.own_says_at_stand
