-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
E2E/KeyLastLaid.lean: `last_done` with four premises paid, where the last chain's one half is `proverSideOfGuardedSending` and it is laid: the half at the job's place (`half_own`), the count of trees in front of
the test, `Listed` of the chain's members, and the chain's steps at every coin (`chain_of_rows`).

  `last_laid`.

Left: what `last_done` leaves but these; `hown`; `hrow`: `offline_second_laid` at the value.
Nothing on soundness, completeness, hiding or binding.
-/
import E2E.KeyLastDone
import E2E.KeyOwnHalf
import E2E.OfflineReady

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

set_option maxHeartbeats 1000000 in
/-- **The last chain's part, with four more premises paid.** -/
theorem last_laid (hs : KeySourced Z Xs Nr Pl) (scope : VerifierAndGoals.InScope Z = true) (hK₀ : fullPub = some K₀)
    (hfit : ∀ v, (threadKey Xs Nr Pl K ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂).valid v →
      keyFits v.key QK.par.S.fold.index = true)
    (hd : d.1.2.lin = none) (hdM : dfltM.opened.isSome = true)
    (hI : JI.P.sent = parIK.sent) (hW : JW.P.sent = parWK.sent)
    (hO : ∀ n, ((jobOmega ⟨A.P, n + A.atPoint⟩).Q.sent.getD 0 default).shape = shapeOK)
    (hsame : L.R.same = fun a b => readE a = readE b)
    (ho₀ : (plan₁ (AtPublicFiles.KeyThread.one₀ Xs)).orc 0 = some 0) (ho₂ : (plan₁ (AtPublicFiles.KeyThread.one₀ Xs)).orc 2 = some 9)
    (hDt : ∀ v, (Dt v).dot = dotI (thirdPar Xs.chains).S gKey (fun _ u => u.2)
      (fun _ => wvK (val₁Key Xs L) (thirdPar Xs.chains).S CF A0.2.w))
    (htie : ∀ k st m E
      (c : RowCoins [(firstPart (jobKWAt Xs Nr Pl JI JW A lift ask).toRun.toTest : Part (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) X),
        restPart (jobKWAt Xs Nr Pl JI JW A lift ask).toRun.toTest]), ThrS (threadOwn Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt (mlKey (val₁Key Xs L)) n₁ n₂ Vd w dfltT dfltM) (saidOwn Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt (mlKey (val₁Key Xs L)) n₁ n₂ Vd w dfltT dfltM) 2 k st m E →
      lendRow (keyBook K₀) ((keyBook K₀).rowsOf 2) (k.look 2) (jobKWAt Xs Nr Pl JI JW A lift ask).toRun.toTest.p.place
        [(firstPart (jobKWAt Xs Nr Pl JI JW A lift ask).toRun.toTest : Part (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) X),
          restPart (jobKWAt Xs Nr Pl JI JW A lift ask).toRun.toTest] 0 = .ok c → ∀ G, st.st.groups[st.loc.own]? = some G →
      ∀ o ∈ G.members.toList, ∀ pt, ∀ i < tableSize st.st o pt,
        wordsKey (val₁Key Xs L) st ((threadOwn Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt (mlKey (val₁Key Xs L)) n₁ n₂ Vd w dfltT dfltM).wit k m.st.input (m.st.heard ++ [])) o pt i =
          wordsAt (begun st.st st.loc.own G) (layoutOf st.st G)
            (plainMany (jobKWAt Xs Nr Pl JI JW A lift ask) m.st.input (frontOf m) (restCoins (jobKWAt Xs Nr Pl JI JW A lift ask).toRun.toTest c.2.1)) o pt i)
    (hold : ∀ k st m E
      (c : RowCoins [(firstPart (jobKWAt Xs Nr Pl JI JW A lift ask).toRun.toTest : Part (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) X),
        restPart (jobKWAt Xs Nr Pl JI JW A lift ask).toRun.toTest]), ThrS (threadOwn Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt (mlKey (val₁Key Xs L)) n₁ n₂ Vd w dfltT dfltM) (saidOwn Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt (mlKey (val₁Key Xs L)) n₁ n₂ Vd w dfltT dfltM) 2 k st m E →
      lendRow (keyBook K₀) ((keyBook K₀).rowsOf 2) (k.look 2) (jobKWAt Xs Nr Pl JI JW A lift ask).toRun.toTest.p.place
        [(firstPart (jobKWAt Xs Nr Pl JI JW A lift ask).toRun.toTest : Part (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) X),
          restPart (jobKWAt Xs Nr Pl JI JW A lift ask).toRun.toTest] 0 = .ok c →
      OldAt E ((jobKWAt Xs Nr Pl JI JW A lift ask).toRun.toTest.trees₀ m.st.input (frontOf m) (restCoins (jobKWAt Xs Nr Pl JI JW A lift ask).toRun.toTest c.2.1).mem
        ((jobKWAt Xs Nr Pl JI JW A lift ask).toRun.toTest.first m.st.input (frontOf m) (restCoins (jobKWAt Xs Nr Pl JI JW A lift ask).toRun.toTest c.2.1)))
        (fun k => [Fmt.TreeSource.taken 0 0, .taken 0 5, .taken 1 1].getD k (.own 0)))
    (hwide : ∀ (k : Coins (keyBook K₀)) (m : Mid (Local W₀ Rc Xi Unit) X), ∀ d' ∈ (proximityTestKind guardedProximityTestParts (jobKWAt Xs Nr Pl JI JW A lift ask).toRun.toTest.p : Block VerifiableInference.Desc.K12.T12 Unit).rounds,
      ∀ o ∈ d'.opens, ProofFile.Honest.K12.oldSrc 0 o.2 = true →
        o.2 ∈ (threadOwn Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt (mlKey (val₁Key Xs L)) n₁ n₂ Vd w dfltT dfltM).hand 2 ∧ ((threadOwn Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt (mlKey (val₁Key Xs L)) n₁ n₂ Vd w dfltT dfltM).tableAt o.2 k m).2.words = o.1.W)
    (hown : K.own = AtPublicFiles.KeyLay.proverSideOfGuardedSending Xs Nr Pl JI JW A lift ask)
    (hrow : ∀ h ∈ (AtPublicFiles.KeyFile.keyProver K).second, AtPublicFiles.OfflineRows.RowLaid (keyBook K₀) 2 h)
    (fl : Nat → S₃ → List Fmt.Drawn → Option String) :
    OwesS (threadOwn Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt (mlKey (val₁Key Xs L)) n₁ n₂ Vd w dfltT dfltM) (saidOwn Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt (mlKey (val₁Key Xs L)) n₁ n₂ Vd w dfltT dfltM) ∧ (∀ b, SaidNext (threadOwn Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt (mlKey (val₁Key Xs L)) n₁ n₂ Vd w dfltT dfltM) (saidOwn Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt (mlKey (val₁Key Xs L)) n₁ n₂ Vd w dfltT dfltM) b) ∧ YesS (threadOwn Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt (mlKey (val₁Key Xs L)) n₁ n₂ Vd w dfltT dfltM) (saidOwn Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt (mlKey (val₁Key Xs L)) n₁ n₂ Vd w dfltT dfltM) fl := by
  have hsrc := hs
  refine last_done K₀ Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt n₁ n₂ Vd w dfltT dfltM JI JW A lift ask
    hs scope hK₀ hfit hd hdM hI hW hO
    (half_own Xs Nr Pl JI JW A lift ask _ (by show [K.own] = _; rw [hown])) hsame ho₀ ho₂ hDt htie hold hwide rfl
    (fun b hb => AtPublicFiles.KeyThread.lists_of_shaped ((planOk_all hsrc.named.plan).2.2 b hb).2)
    (fun k v => ?_) fl
  obtain ⟨r1, r2, r3⟩ := AtPublicFiles.KeyBook.places_named scope hs.named
  exact AtPublicFiles.OfflineRows.chain_of_rows hK₀ _ _ _ k hrow
    (fun b hb => (AtPublicFiles.KeyThread.lists_of_shaped ((planOk_all hsrc.named.plan).2.2 b hb).2).1.symm)
    (fun b hb => List.mem_append_right _ (r3 ▸ List.mem_map.2 ⟨b, hb, rfl⟩))

end

end AtPublicFiles.KeyLastChain

#print axioms AtPublicFiles.KeyLastChain.last_laid
