-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
E2E/KeyLastDone.lean: the last chain's part of the debts at the members, at the thread of this work with the letter `mlKey`, with what is paid laid in: the exchange
(`exchange_own`, `rows_stand`, `dot_stand`), the riders (`rides_own`), the marks (`mark_stand`), the plays' frame (`playsS_own`, `run_own`), the words' frame
(`say_stand`), the coins (`own_asks`).

  `last_done`.

Left as premises, each named, and no other: `hfit`, `hd`, `hdM` · value ties: `hI`, `hW`, `hO`, `hhalf`, `ht0` · `hsame`, 'ho₀', `ho₂`, `hDt` ·
`htie`: the words on the members' tables · `hold`, `hwide`: the tables at hand and their widths · `hlisted`, `hlaid`.
Nothing on soundness, completeness, hiding or binding.
-/
import E2E.KeyOwnAsks
import E2E.KeyOwnMarkStand
import E2E.KeyOwnSayThread
import E2E.KeyOwnRun
import E2E.KeyOwnJob
import E2E.KeyLastEvOwn
import E2E.KeyLastRidesOwn
import E2E.KeyLastEnd

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

set_option maxHeartbeats 4000000 in
/-- **The last chain's part of the debts, with what is paid laid in.** -/
theorem last_done (hs : KeySourced Z Xs Nr Pl) (scope : VerifierAndGoals.InScope Z = true) (hK₀ : fullPub = some K₀)
    (hfit : ∀ v, (threadKey Xs Nr Pl K ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂).valid v →
      keyFits v.key QK.par.S.fold.index = true)
    (hd : d.1.2.lin = none) (hdM : dfltM.opened.isSome = true)
    (hI : JI.P.sent = parIK.sent) (hW : JW.P.sent = parWK.sent)
    (hO : ∀ n, ((jobOmega ⟨A.P, n + A.atPoint⟩).Q.sent.getD 0 default).shape = shapeOK)
    (hhalf : ((threadOwn Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt (mlKey (val₁Key Xs L)) n₁ n₂ Vd w dfltT dfltM).hs.find? fun g => g.place == (jobKWAt Xs Nr Pl JI JW A lift ask).toRun.toTest.p.place) =
      some (proverSideOfProximityTest (jobKWAt Xs Nr Pl JI JW A lift ask).toRun.toTest : Placed (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) X).needsField)
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
    (ht0 : treesTo (threadOwn Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt (mlKey (val₁Key Xs L)) n₁ n₂ Vd w dfltT dfltM).bs 2 = 0)
    (hlisted : ∀ b ∈ (descriptionFromSource Xs Nr Pl).second.blocksInOrder, ProofFile.Honest.Small.Listed b)
    (hlaid : ∀ (k : Coins (keyBook K₀)) (v : Local W₀ Rc Xi Unit), ∃ Lall,
      chainSteps (keyBook K₀) ((keyBook K₀).rowsOf 2) (k.look 2) (Face.own.sees v) (descriptionFromSource Xs Nr Pl).second.blocksInOrder (threadOwn Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt (mlKey (val₁Key Xs L)) n₁ n₂ Vd w dfltT dfltM).hs = .ok Lall)
    (fl : Nat → S₃ → List Fmt.Drawn → Option String) :
    OwesS (threadOwn Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt (mlKey (val₁Key Xs L)) n₁ n₂ Vd w dfltT dfltM) (saidOwn Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt (mlKey (val₁Key Xs L)) n₁ n₂ Vd w dfltT dfltM) ∧ (∀ b, SaidNext (threadOwn Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt (mlKey (val₁Key Xs L)) n₁ n₂ Vd w dfltT dfltM) (saidOwn Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt (mlKey (val₁Key Xs L)) n₁ n₂ Vd w dfltT dfltM) b) ∧ YesS (threadOwn Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt (mlKey (val₁Key Xs L)) n₁ n₂ Vd w dfltT dfltM) (saidOwn Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt (mlKey (val₁Key Xs L)) n₁ n₂ Vd w dfltT dfltM) fl := by
  have hpl := place_own hs scope
  have hp : (jobKWAt Xs Nr Pl JI JW A lift ask).toRun.toTest.p = piKWFull := hpl
  have hms := mems_own Xs Nr Pl JI JW A lift ask hI hW hO
  have htr := trees_own Xs Nr Pl JI JW A lift ask hpl
  have hZ := third_shaped Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt (mlKey (val₁Key Xs L))
    (tableKey Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt (mlKey (val₁Key Xs L)) n₁ n₂ Vd
      (fun _ _ _ => True) keptOwn w dfltT dfltM) n₁ n₂ Vd (fun _ _ _ => True) keptOwn w hs scope hfit hd (fun _ _ _ => true)
  have hfun : ∀ k v h s s', (threadOwn Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt (mlKey (val₁Key Xs L)) n₁ n₂ Vd w dfltT dfltM).begun k v h s → (threadOwn Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt (mlKey (val₁Key Xs L)) n₁ n₂ Vd w dfltT dfltM).begun k v h s' → s = s' := fun k v h s s' a b =>
    Except.ok.inj ((show (descriptionFromSource Xs Nr Pl).start₃ _ _ _ = .ok s from a).symm.trans b)
  have hpS : (thirdPar Xs.chains).S = SF := by
    obtain ⟨-, -, hlin, -⟩ := AtPublicFiles.AtFiles.Full.first_of_sourced hs scope fun _ _ _ _ => true
    exact hlin.symm.trans (AtPublicFiles.AtFiles.Full.six_sourced hs scope).lin
  refine last_members Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt (mlKey (val₁Key Xs L))
    n₁ n₂ Vd w dfltT dfltM JI JW A lift ask hs scope hfit hd hdM hpl hms htr hhalf ?_ ?_
    (fun b hb => rides_own Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt _ n₁ n₂ Vd w dfltT dfltM b hb)
    ?_ fl
  · exact playsS_own Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt _ n₁ n₂ Vd _ _ w dfltT dfltM
      JI JW A lift ask hpl hdM rfl hhalf
      (fun k st m E ds c hT _ hc => run_own _ _ c hT.1 ht0
        (agree_at_W K₀ hK₀ _ hp (members_own Xs Nr Pl JI JW A lift ask) _
          (fresh_own Xs Nr Pl JI JW A lift ask) _ _ c hc _ _) (hwide k m))
      hlisted hlaid
  · exact exchange_own Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt (val₁Key Xs L) n₁ n₂ Vd w dfltT dfltM
      hs scope hZ hpS
      (fun k s m E ds hT => rows_stand Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt n₁ n₂ Vd w dfltT
        dfltM hs scope hZ hsame ds hT.1)
      (fun k s m E ds hT => dot_stand Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt (val₁Key Xs L) n₁ n₂ Vd w
        dfltT dfltM hDt
        (fun k s m E hT' => end_stand Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt _ n₁ n₂ Vd w dfltT dfltM hs scope hZ hT'.1) ds hT)
  · intro k st m E c hT hc
    have hen := enters_own Xs Nr Pl JI JW A lift ask rfl rfl hfun hT.1 (hT.2.1)
    have hsh := shape_own hs scope rfl hZ hT.1
    have hmark := mark_stand hs scope rfl hZ hfun hT.1 hT.2.1
    exact own_asks _ K₀ hK₀ hp (members_own Xs Nr Pl JI JW A lift ask) _ (fresh_own Xs Nr Pl JI JW A lift ask) _ _ m E c hc st hen
      hsh hmark (depths_own Xs Nr Pl JI JW A lift ask hpl _ _ _ _) (hT.1.2.2.2.2.1.2.2.1.trans ht0) (hold k st m E c hT hc)
      (say_stand Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt n₁ n₂ Vd w dfltT dfltM hs scope hZ hsame
        ho₀ ho₂ [] hT.1 hen _ (htie k st m E c hT hc))

end

end AtPublicFiles.KeyLastChain

#print axioms AtPublicFiles.KeyLastChain.last_done
