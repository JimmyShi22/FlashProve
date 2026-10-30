-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/OfflineOwnFolds.lean: AT THE KEY FILE's OWN PROXIMITY TEST, WHAT IS ASKED IN FRONT OF THE TEST (`AsksInFront`,
E2E/OfflineTestAsks.lean), AT A VERIFIER's STATE THAT ACCEPTED FOLDS REACH: with no thread, no stand and no truth of the
witness, but for one named premise, the clause `allSay`. In scope, at the written sizes.

  `shape19_of_fold`, `shape12_of_fold`   the two earlier chains' ends have the runs' last shapes: by `shape_of_fold`
                     (E2E/OfflineShapeOfFold.lean)
  `ReachedOwn`         a state in front of the own test: the description folds the two earlier chains (`DoorAt`,
                     E2E/KeyLastSaid.lean), starts the last chain, and folds its first two sub-protocols
  `fits_door`, `mark_door`   the marks at the last chain's first state: the text of E2E/KeyOwnMarkStand.lean's two, which read
                     no thread, laid here because that file stands over E2E/KeyOwnSayStand.lean
  `start_reached`, `shape_reached`, `mark_reached`   the written shapes `A0`, `A2`; the marks `OwnMark`
  `SayInFront`         THE NAMED PREMISE: the rows that the test takes in hold at the job's words: the clause `allSay` of
                     `DataFront` (K12/ShapeAll.lean) at `plainMany`
  `asks_reached`       `AsksInFront` at the job `jobKWAt`, at every input, front and family of coins at which the job's state
                     on entry is the seat's way in at a reached state

What each clause stands on. The seven clauses on the shape, and the number of trees: kernel lines at the written shape
(`five_KW`, `tidy_A2`, `tsLen_KW`, `planB_KW_full`). `denseRows`, `claims`: the marks, which accepted folds keep
(`mark_door`, `second_mark`, `entry_marks`). `cols`, `state`, `trees`: of form, at every family of coins (`dataThree_of_frontD` at
`many_KW`). `allSay`: the premise.

Premises. hkey: the instance's key has the written sizes (`keyFits`): the shared chain's first shape reads it. hI, hW, hO:
what the three sendings send, at the written public data.

Limits. In scope (`KeySourced`, `InScope`). That a state is reached, and that the job's state on entry is the way in there,
are premises here. `SayInFront` reads the input and the coins; nothing is shown of it. Nothing on completeness, on
soundness or on what is hidden.
-/
import E2E.OfflineTestAsks
import E2E.OfflineShapeOfFold
import E2E.KeyOwnFront
import E2E.KeyFirstMarks
import E2E.LotSamplesDense
import Johnson.Desc.Third.Law.AtDoor
import E2E.KeyOwnEntry
import E2E.KeyOwnJob

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace AtPublicFiles.OfflineRows
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun OnBytes.Means Cb
open VerifiableInference.Desc.Ground.Sh
open H2K.Sw H2K.JointK H2K.First
open Johnson.Prover.Link
open ProofFile.Honest ProofFile.Honest.K12
open ProofFile.Honest.K12.Light (ManyJob colsMany plainMany dataThree_of_frontD ts_of_frontD tsLenOf)
open ProofFile.Honest.K14 (SendPub jobOmega)
open ProofFile.Honest.Sh (testSh thinOf claimsB)
open VerifiableInference.Desc (Block OpenedColumn foldBlocks foldBlocks_cons_ok step_iff)
open VerifiableInference.Desc.Own (keyFits)
open VerifiableInference.Desc.K12 (T12 proximityTestKind guardedProximityTestParts)
open VerifiableInference.Desc.K12.Seat (enterOwn leaveOwn)
open VerifiableInference.Desc.Third (S₃ batchLinearConstraintsSecondPart takenSources)
open VerifiableInference.Desc.Third.Law (takenSources_same ok_of_bind some_of_named start₃E_inv start₃_inv)
open AtPublicFiles.KeyLastThread (start_key handOf)
open VerifiableInference.Desc.Key (Xi FirstState Source LaterPlaces descriptionFromSource ownTest thirdPar)
open _root_.Desc.K14 (St)
open AtPublicFiles.KeyShape AtPublicFiles.KeyLink
open AtPublicFiles.KeyLay (pWK jobKWAt parIK parWK shapeOK)
open AtPublicFiles.AtFiles
open AtPublicFiles.AtFiles.Full
open AtPublicFiles.KeyLastChain
open H2K.Member (piKWFull codesKeyFull)

/-! ## 1 The two earlier chains' ends -/

section Key
variable {Z : VerifierAndGoals.PublicFiles} {X : Source} {N : H2U.PlaceNums} {P : LaterPlaces}

/-- The first chain's end has the run's last shape. -/
theorem shape19_of_fold (hs : KeySourced Z X N P) (scope : VerifierAndGoals.InScope Z = true)
    (x : (keyFileDescription X N P).XiPub) {e₁ : (keyFileDescription X N P).S₁} {rs r : List Fmt.RoundView} {cols c : List OpenedColumn}
    (hf : foldBlocks 0 (keyFileDescription X N P).first.blocksInOrder ((keyFileDescription X N P).start₁ x) rs cols =
      .ok (e₁, r, c)) : sh₁B (pubOf X) CF e₁ = T19 := by
  obtain ⟨-, -, -, hlen, hsh0, hrun, hyes, -⟩ := first_of_sourced hs scope fun _ _ _ _ => true
  obtain ⟨bw, hw, he, ha, -⟩ := public_first_sourced hs scope
  have ht : (keyFileDescription X N P).first.blocksInOrder.take 19 = (keyFileDescription X N P).first.blocksInOrder := by
    rw [← hlen]
    exact List.take_length
  have hf' : foldBlocks 0 ((keyFileDescription X N P).first.blocksInOrder.take 19) ((keyFileDescription X N P).start₁ x) rs cols =
      .ok (e₁, r, c) := by
    rw [ht]
    exact hf
  have h19 := shape_of_fold (Z₁W (pubOf X) CF X.Y.D.1 X.Y.told.1 N fun _ _ _ _ => true) (ft := 0)
    (bs := (keyFileDescription X N P).first.blocksInOrder)
    (fun j => carries_whole₁ (pubOf X) CF X.Y.D.1 X.Y.told.1 N 0 _ bw hw he ha j) (a₀ := T0)
    (n := 19) (b := 19) (le_of_eq hlen.symm) (Nat.le_refl _) hyes
    ((start₁_shape (cs := CF) (N := N) (X := X) (P := P) _ x).trans hsh0) hf'
  exact Except.ok.inj (h19.symm.trans hrun)

/-- The shared chain's end has the run's last shape, at an instance whose key's sizes fit. -/
theorem shape12_of_fold (hs : KeySourced Z X N P) (scope : VerifierAndGoals.InScope Z = true)
    (x : (keyFileDescription X N P).XiPub) (hk : keyFits x.key QK.par.S.fold.index = true)
    {e₂ : (keyFileDescription X N P).S₂} {rs r : List Fmt.RoundView} {cols c : List OpenedColumn}
    (hf : foldBlocks 0 (keyFileDescription X N P).shared.blocksInOrder ((keyFileDescription X N P).start₂ x) rs cols =
      .ok (e₂, r, c)) : sh₂ e₂ = V12 := by
  have hlen : (keyFileDescription X N P).shared.blocksInOrder.length = 12 := len₂_sourced hs scope
  have ht : (keyFileDescription X N P).shared.blocksInOrder.take 12 = (keyFileDescription X N P).shared.blocksInOrder := by
    rw [← hlen]
    exact List.take_length
  have hf' : foldBlocks 0 ((keyFileDescription X N P).shared.blocksInOrder.take 12) ((keyFileDescription X N P).start₂ x) rs cols =
      .ok (e₂, r, c) := by
    rw [ht]
    exact hf
  have h12 := shape_of_fold (Z₂At X.chains P gK₂ fun _ _ _ _ => true) (ft := 0)
    (bs := (keyFileDescription X N P).shared.blocksInOrder) (fun j => carries₂_sourced hs scope 0 _ j) (a₀ := V0)
    (n := 12) (b := 12) (le_of_eq hlen.symm) (Nat.le_refl _) (yes₂_sourced hs scope _)
    (first₂_shape hs scope x hk) hf'
  exact Except.ok.inj (h12.symm.trans (run₂_sourced hs scope _))

/-! ## 2 The marks at the last chain's first state -/

/-- The samples' rows are dense at the state that the door names. Statement and proof are those of
`fits_door` (E2E/KeyOwnMarkStand.lean); two of its implicit letters are this section's. -/
theorem fits_door {Xs : Source} {Pl : LaterPlaces}
    (hs : KeySourced Z Xs N Pl) (scope : VerifierAndGoals.InScope Z = true) (x : Xi)
    (r₁ r₂ : List Fmt.RoundView) (c₁ c₂ : List OpenedColumn) (e₁ : (descriptionFromSource Xs N Pl).S₁) (e₂ : (descriptionFromSource Xs N Pl).S₂)
    (v₀ : (descriptionFromSource Xs N Pl).S₃) (D : DoorAt (descriptionFromSource Xs N Pl) x r₁ r₂ c₁ c₂ e₁ e₂ v₀) :
    SamplesDense (v₀ : S₃).st ∧ ∀ b, (v₀ : S₃).loc.border = some b → SamplesDense b.shared.st := by
  have h1 := (AtPublicFiles.KeyLastChain.Lots.lotSamplesDense Xs N Pl hs scope x r₁ c₁).1 _ _ _ D.fold₁
  have h2 := (AtPublicFiles.KeyLastChain.Lots.lotSamplesDense Xs N Pl hs scope x r₂ c₂).2 _ _ _ D.fold₂
  have hst := D.start
  obtain ⟨l, _, hst⟩ := ok_of_bind hst
  obtain ⟨e, he, hst⟩ := ok_of_bind hst
  obtain ⟨f, hf, h3⟩ := start₃E_inv _ _ _ _ _ _ _ _ _ _ _ hst
  obtain ⟨_, _, rfl⟩ := start₃_inv _ _ _ _ h3
  have he' := some_of_named he
  have hfs : f.st = (e₁ : VerifiableInference.Desc.Key.FirstState).d.st := by
    unfold VerifiableInference.Desc.Third.firstOutFrom at hf
    split at hf
    · dsimp only at hf
      split at hf
      · split at hf
        · cases hf; rfl
        · cases hf
      · cases hf
    · cases hf
  have hes : e.st = (e₂ : _root_.Desc.K14.St).st := by
    unfold _root_.Desc.K14.ended at he'
    dsimp only at he'
    split at he'
    · cases he'; rfl
    · cases he'
  refine ⟨?_, ?_⟩
  · show SamplesDense f.st
    rw [hfs]; exact h1
  · intro b hb
    obtain rfl := Option.some.inj hb
    show SamplesDense e.st
    rw [hes]; exact h2

/-- **The marks at the state that the door names.** Statement and proof are those of `mark_door`
(E2E/KeyOwnMarkStand.lean); two of its implicit letters are this section's. -/
theorem mark_door {Xs : Source} {Pl : LaterPlaces}
    (hs : KeySourced Z Xs N Pl) (scope : VerifierAndGoals.InScope Z = true) (x : Xi)
    (r₁ r₂ : List Fmt.RoundView) (c₁ c₂ : List OpenedColumn) (e₁ : (descriptionFromSource Xs N Pl).S₁) (e₂ : (descriptionFromSource Xs N Pl).S₂)
    (v₀ : (descriptionFromSource Xs N Pl).S₃) (D : DoorAt (descriptionFromSource Xs N Pl) x r₁ r₂ c₁ c₂ e₁ e₂ v₀) : OwnMark v₀ := by
  obtain ⟨s₁, s₂⟩ := fits_door hs scope x r₁ r₂ c₁ c₂ e₁ e₂ v₀ D
  obtain ⟨bw, hw, -, -, -⟩ := public_first_sourced hs scope
  obtain ⟨l, hl, hc⟩ := claims_of_fold _ Xs.Y.D.1 Xs.Y.told.1 N bw hw D.fold₁
  obtain ⟨h, o, hh, -, hst⟩ := (start_key Xs N Pl _ _ _ v₀).1 D.start
  have hh' : (e₁ : VerifiableInference.Desc.Key.FirstState).lin.map (handOf e₁) = some h := hh
  rw [hl] at hh'
  obtain rfl := Option.some.inj hh'
  obtain ⟨-, -, -, -, est, -, -, eown, -⟩ := K14.start_gives (thirdPar Xs.chains) _ o v₀ hst
  refine ⟨?_, s₁, s₂⟩
  rw [est, eown]
  exact hc

/-! ## 3 A state in front of the own test -/

/-- **A state that the description's own accepted folds reach in front of the own test**, at the instance x. -/
def ReachedOwn (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces) (x : Xi) (s : S₃) : Prop :=
  ∃ (r₁ r₂ : List Fmt.RoundView) (c₁ c₂ : List OpenedColumn) (e₁ : (descriptionFromSource X N P).S₁) (e₂ : (descriptionFromSource X N P).S₂)
    (v₀ : (descriptionFromSource X N P).S₃) (rs : List Fmt.RoundView) (cols : List OpenedColumn),
    DoorAt (descriptionFromSource X N P) x r₁ r₂ c₁ c₂ e₁ e₂ v₀ ∧
      foldBlocks (descriptionFromSource X N P).lastChainFirstTreeNumber ((descriptionFromSource X N P).second.blocksInOrder.take 2) v₀ rs cols =
        .ok (s, [], [])

/-- In scope the description's shape of the linear claim is the written one. -/
theorem linShape_written (hs : KeySourced Z X N P) (scope : VerifierAndGoals.InScope Z = true) :
    X.chains.made.sized.key.once.shape = SF := by
  obtain ⟨-, -, hlin, -⟩ := first_of_sourced hs scope fun _ _ _ _ => true
  exact hlin.symm.trans (six_sourced hs scope).lin

/-- **The last chain's first state has the written shape.** -/
theorem start_reached (hs : KeySourced Z X N P) (scope : VerifierAndGoals.InScope Z = true) {x : Xi}
    (hk : keyFits ((descriptionFromSource X N P).pub x).key QK.par.S.fold.index = true)
    {r₁ r₂ : List Fmt.RoundView} {c₁ c₂ : List OpenedColumn} {e₁ : (descriptionFromSource X N P).S₁} {e₂ : (descriptionFromSource X N P).S₂}
    {v₀ : (descriptionFromSource X N P).S₃} (D : DoorAt (descriptionFromSource X N P) x r₁ r₂ c₁ c₂ e₁ e₂ v₀) :
    sh₃ SF (v₀ : S₃) = A0 := by
  have h1 := shape19_of_fold hs scope ((descriptionFromSource X N P).pub x) D.fold₁
  have h2 := shape12_of_fold hs scope ((descriptionFromSource X N P).pub x) hk D.fold₂
  have q : sh₃ X.chains.made.sized.key.once.shape (v₀ : S₃) = A0 :=
    first₃_shape hs scope (fun _ _ _ => true) _ e₁ e₂ h1 h2 v₀ D.start
  rw [linShape_written hs scope] at q
  exact q

/-- **A reached state has the written shape.** -/
theorem shape_reached (hs : KeySourced Z X N P) (scope : VerifierAndGoals.InScope Z = true) {x : Xi}
    (hk : keyFits ((descriptionFromSource X N P).pub x).key QK.par.S.fold.index = true) {s : S₃}
    (h : ReachedOwn X N P x s) : sh₃ SF s = A2 := by
  obtain ⟨r₁, r₂, c₁, c₂, e₁, e₂, v₀, rs, cols, D, hf⟩ := h
  have h0 := start_reached hs scope hk D
  have hS := linShape_written hs scope
  have hr := shape_of_fold (Z₃Own X P fun _ _ _ => true) (ft := (descriptionFromSource X N P).lastChainFirstTreeNumber)
    (bs := (keyFileDescription X N P).second.blocksInOrder)
    (fun j => carries_all_in_scope hs scope _ _ j) (a₀ := A0) (n := 4) (b := 2)
    (Nat.le_of_eq (AtPublicFiles.KeyThread.lengths scope hs.named).2.2.symm) (by decide)
    (yes₃_sourced hs scope _) (s₀ := (v₀ : S₃)) (by
      show sh₃ X.chains.made.sized.key.once.shape (v₀ : S₃) = A0
      rw [hS]
      exact h0) hf
  obtain rfl := later_sourced hs scope
  have hr₁ : (Z₃ X.chains.made.sized.key.once.shape (ownTest PF).rounds
      (gOwn (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ PF.W)) fun _ _ _ => true).run 2 A0 =
      .ok (sh₃ X.chains.made.sized.key.once.shape s) := hr
  rw [hS] at hr₁
  unfold A2
  rw [hr₁]
  rfl

/-- **A reached state bears the marks.** -/
theorem mark_reached (hs : KeySourced Z X N P) (scope : VerifierAndGoals.InScope Z = true) {x : Xi}
    (hk : keyFits ((descriptionFromSource X N P).pub x).key QK.par.S.fold.index = true) {s : S₃}
    (h : ReachedOwn X N P x s) : OwnMark s := by
  obtain ⟨r₁, r₂, c₁, c₂, e₁, e₂, v₀, rs, cols, D, hf⟩ := h
  have h0 := start_reached hs scope hk D
  obtain ⟨b₀, b₁, e, d₀, d₁⟩ : ∃ b₀ b₁, (descriptionFromSource X N P).second.blocksInOrder.take 2 = [b₀, b₁] ∧
      b₀.decide = (batchLinearConstraintsSecondPart (Cl := Unit) (thirdPar X.chains)).decide ∧
      b₁.decide = (takenSources (ownTest P) : Block S₃ Unit).decide :=
    ⟨_, _, rfl, rfl, rfl⟩
  rw [e] at hf
  obtain ⟨-, s₁, _, hs₁, h₁⟩ := foldBlocks_cons_ok.1 hf
  obtain ⟨-, s₂, _, hs₂, h₂⟩ := foldBlocks_cons_ok.1 h₁
  have hy₁ := ((step_iff _ b₀ v₀ s₁ _ _ _).1 hs₁).2.1
  have hy₂ := ((step_iff _ b₁ s₁ s₂ _ _ _).1 hs₂).2.1
  rw [d₀] at hy₁
  rw [d₁] at hy₂
  have e₂' : s₂ = s₁ := takenSources_same _ s₁ s₂ _ _ hy₂
  have q : (Except.ok (s₂, _, _) : Except String (S₃ × List Fmt.RoundView × List OpenedColumn)) = .ok (s, [], []) :=
    h₂
  have e₃ : s₂ = s := (Prod.mk.inj (Except.ok.inj q)).1
  have e₄ : s₁ = s := e₂'.symm.trans e₃
  rw [e₄] at hy₁
  exact second_mark (Cl := Unit) _ v₀ s _ _ hy₁ (fresh_of_shape h0)
    (mark_door hs scope _ _ _ _ _ _ _ _ D)

end Key

/-! ## 4 What is asked in front of the test -/

section Asks
variable {Z : VerifierAndGoals.PublicFiles} {Xs : Source} {Nr : H2U.PlaceNums} {Pl : LaterPlaces}
  {W₀ Rc Tr Y Wd : Type} (JI JW : ProofFile.Honest.K1.SendJob Wd Y) (A : SendPub)
  (lift : Local W₀ Rc Xi Tr → Wd) (ask : Local W₀ Rc Xi Tr → ProofFile.Honest.K14.Ask)

/-- **THE NAMED PREMISE: the rows that the test takes in hold at the job's words.** The clause `allSay` of
`DataFront`, at the job's own plain rows. It reads the input and the coins. -/
def SayInFront {W X : Type} (B : ManyJob W X) (w : W) (fr : Front X) (C : TestCoins) : Prop :=
  ∀ G, (B.toRun.toTest.rec₀ w fr).st.groups[(B.toRun.toTest.rec₀ w fr).g]? = some G →
    AllSay rdE (begun (B.toRun.toTest.rec₀ w fr).st (B.toRun.toTest.rec₀ w fr).g G)
      (runRows (B.toRun.toTest.rec₀ w fr).st G).toList
      (wordsAt (begun (B.toRun.toTest.rec₀ w fr).st (B.toRun.toTest.rec₀ w fr).g G)
        (layoutOf (B.toRun.toTest.rec₀ w fr).st G) (plainMany B w fr C))

/-- **What is asked in front of the own test, where the job's state on entry is the way in at a reached
state.** -/
theorem asks_reached (hs : KeySourced Z Xs Nr Pl) (scope : VerifierAndGoals.InScope Z = true) {x : Xi}
    (hk : keyFits ((descriptionFromSource Xs Nr Pl).pub x).key QK.par.S.fold.index = true)
    (hI : JI.P.sent = parIK.sent) (hW : JW.P.sent = parWK.sent)
    (hO : ∀ n, ((jobOmega ⟨A.P, n + A.atPoint⟩).Q.sent.getD 0 default).shape = shapeOK)
    {s : S₃} (hr : ReachedOwn Xs Nr Pl x s) (w : Local W₀ Rc Xi Tr) (fr : Front Y)
    (hen : enterOwn s = .ok ((jobKWAt Xs Nr Pl JI JW A lift ask).toRun.toTest.rec₀ w fr))
    (C : TestCoins) (hsay : SayInFront (jobKWAt Xs Nr Pl JI JW A lift ask) w fr C) :
    AsksInFront (jobKWAt Xs Nr Pl JI JW A lift ask).toRun.toTest codesKeyFull 3 w fr C := by
  have hpl := place_own hs scope
  have hms := mems_own Xs Nr Pl JI JW A lift ask hI hW hO
  have htr := trees_own Xs Nr Pl JI JW A lift ask hpl
  have hsh := shape_reached hs scope hk hr
  have hmk := mark_reached hs scope hk hr
  have hN := entry_shape hen hsh
  obtain ⟨hcl, hden⟩ := entry_marks hen hsh hmk
  have hp : (jobKWAt Xs Nr Pl JI JW A lift ask).toRun.toTest.p = piKWFull := hpl
  have he : (jobKWAt Xs Nr Pl JI JW A lift ask).toRun.toTest.p.early = true :=
    (own_place_in_scope hs scope).1
  have five : frontFiveB (jobKWAt Xs Nr Pl JI JW A lift ask).toRun.toTest.p CF
      (testSh ((jobKWAt Xs Nr Pl JI JW A lift ask).toRun.toTest.rec₀ w fr)) = true := by
    rw [hN, hp]
    exact five_KW
  have tid : stTidyB ((jobKWAt Xs Nr Pl JI JW A lift ask).toRun.toTest.rec₀ w fr).st = true := by
    have e : ((jobKWAt Xs Nr Pl JI JW A lift ask).toRun.toTest.rec₀ w fr).st = s.st := by
      have q := Except.ok.inj hen
      rw [← q]
    rw [e]
    have q : (sh₃ SF s).2.tidy = true := by
      rw [hsh]
      exact tidy_A2
    exact q
  obtain ⟨Dp, S⟩ := frontAsksD_of_five (jobKWAt Xs Nr Pl JI JW A lift ask).toRun.toTest w fr CF he
    five tid hden hcl
  have hmany : ProofFile.Honest.K12.Light.manyFitsS (jobKWAt Xs Nr Pl JI JW A lift ask).p
      ((jobKWAt Xs Nr Pl JI JW A lift ask).mems.map (·.shape))
      (jobKWAt Xs Nr Pl JI JW A lift ask).trees
      (thinOf (testSh ((jobKWAt Xs Nr Pl JI JW A lift ask).rec₀ w fr))) = true := by
    have hN' : testSh ((jobKWAt Xs Nr Pl JI JW A lift ask).rec₀ w fr) = testOf A2 := hN
    have hp' : (jobKWAt Xs Nr Pl JI JW A lift ask).p = piKWFull := hpl
    rw [hN', hp', hms, htr]
    exact many_KW
  obtain ⟨d1, d2, d3⟩ := dataThree_of_frontD (jobKWAt Xs Nr Pl JI JW A lift ask) w fr CF Dp he five
    S hmany C
  have hts : Dp.ts.length = 3 := by
    have q := ts_of_frontD (jobKWAt Xs Nr Pl JI JW A lift ask).toRun.toTest w fr CF Dp he five S
    rw [hN, hp] at q
    exact q.trans tsLen_KW
  rw [← codes_KW]
  refine ⟨Dp, _, _, hts, ?_, S, ⟨d1, d2, d3, hsay⟩⟩
  rw [hp, codes_KW]
  exact planB_KW_full

end Asks

end AtPublicFiles.OfflineRows

#print axioms AtPublicFiles.OfflineRows.shape19_of_fold
#print axioms AtPublicFiles.OfflineRows.shape12_of_fold
#print axioms AtPublicFiles.OfflineRows.fits_door
#print axioms AtPublicFiles.OfflineRows.mark_door
#print axioms AtPublicFiles.OfflineRows.start_reached
#print axioms AtPublicFiles.OfflineRows.shape_reached
#print axioms AtPublicFiles.OfflineRows.mark_reached
#print axioms AtPublicFiles.OfflineRows.asks_reached
