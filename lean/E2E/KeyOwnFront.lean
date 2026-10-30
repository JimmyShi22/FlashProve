-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
E2E/KeyOwnFront.lean: what the key file's own test asks where the pair stands at border 2 (`OwnFrontDense`), from the closed
lines at that test and five named premises.

Main names.
  `shape_own`: at border 2 the verifier's state has the written shape `A2`.
  `entry_shape`: so the test's state on entry has the shape 'testOf A2'.
  `front_own`: `OwnFrontDense` at the job `jobKWAt`.

Paid here: the way in (`enters_own`); the plan, the form, the count (closed lines); the leaving; `FrontAsksD` but for two
premises, by `frontAsksD_of_five` at `five_KW`; three of `DataFront`'s four fields, by `dataThree_of_frontD` at `many_KW`.
Left as premises, each named: `hag` (the two parts' coins agree) · `hop` (the depths, the sources, the old tables) · `hden`
(the rows taken in are dense) · `hcl` (the rows pass the ground's tests) · `hsay` (they hold at the prover's words).
Also: `hms`, `htr`: the job's members and trees have the written shapes; `hpl`: the place is the written one.
What stays open beyond these: that a pair stands.
Nothing on soundness, completeness, hiding or binding.
-/
import E2E.KeyOwnSeat
import E2E.KeyOwnLines
import E2E.KeyOwnDense
import E2E.KeyQuietThird
import Johnson.Desc.ProofFile.Honest.K12.AsksAtHeadDense
import Johnson.Desc.ProofFile.Honest.K12.Sim.TreesPlanAt

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace AtPublicFiles.KeyLastChain
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun OnBytes.Means Cb
open VerifiableInference.Desc.Ground.Sh
open H2K.Sw H2K.JointK H2K.First
open Johnson.Prover.Link
open ProofFile.Honest ProofFile.Honest.K12
open ProofFile.Honest.K12.Light (ManyJob colsMany plainMany dataThree_of_frontD ts_of_frontD tsLenOf)
open ProofFile.Honest.K14 (SendPub)
open ProofFile.Honest.Sh (testSh thinOf claimsB)
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.K12 (T12 proximityTestKind guardedProximityTestParts)
open VerifiableInference.Desc.K12.Seat (enterOwn leaveOwn)
open VerifiableInference.Desc.Third (S₃)
open VerifiableInference.Desc.Key (Xi Source LaterPlaces descriptionFromSource)
open AtPublicFiles.KeyLay (pWK jobKWAt)
open AtPublicFiles.AtFiles (KeySourced ThirdShaped Z₃Own sh₃ SF CF gOwn Z₃ own_place_in_scope carries_all_in_scope)
open AtPublicFiles.AtFiles.Full (A0 PF later_sourced six_sourced first_of_sourced)
open H2K.Member (piKWFull codesKeyFull)

/-- The mark at the written shape. -/
theorem tidy_A2 : A2.2.tidy = true := by decide +kernel

/-- The number of trees at the written shape. -/
theorem tsLen_KW : tsLenOf piKWFull (thinOf (testOf A2)) = 3 := by decide +kernel

theorem codes_KW : CF = codesKeyFull := by decide +kernel

section
variable {Z : VerifierAndGoals.PublicFiles} {Xs : Source} {Nr : H2U.PlaceNums} {Pl : LaterPlaces} {Bk : ProverCoinCounts}
  {W₀ Rc Tr Y Wd : Type}
  {T₃ : Thread Bk (descriptionFromSource Xs Nr Pl).S₃ (descriptionFromSource Xs Nr Pl).Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Y Xi}
  {v : S₃ → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool}

/-- **At border 2 the state has the written shape.** -/
theorem shape_own (hs : KeySourced Z Xs Nr Pl) (scope : VerifierAndGoals.InScope Z = true)
    (hbs : T₃.bs = (descriptionFromSource Xs Nr Pl).second.blocksInOrder) (hZ : ThirdShaped T₃ v A0) {k : Coins Bk} {st : S₃}
    {m : Mid (Local W₀ Rc Xi Tr) Y} {E : Env} (hT : Thr T₃ 2 k st m E) :
    sh₃ SF st = A2 := by
  obtain ⟨-, -, hlin, -⟩ := first_of_sourced hs scope fun _ _ _ _ => true
  have hS : Xs.chains.made.sized.key.once.shape = SF := hlin.symm.trans (six_sourced hs scope).lin
  have hr := shape_at T₃ (Z₃Own Xs Pl v) (n := 4) (b := 2) (a₀ := A0)
    (by rw [hbs]; exact Nat.le_of_eq (AtPublicFiles.KeyThread.lengths scope hs.named).2.2.symm) (by decide) hZ.yes hZ.first
    (fun j => by rw [hbs]; exact carries_all_in_scope hs scope v T₃.ft j) hT
  obtain rfl := later_sourced hs scope
  have hr₁ : (Z₃ Xs.chains.made.sized.key.once.shape (VerifiableInference.Desc.Key.ownTest PF).rounds
      (gOwn (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ PF.W)) v).run 2 A0 =
      .ok (sh₃ Xs.chains.made.sized.key.once.shape st) := hr
  rw [hS] at hr₁
  have hr₂ : (Z₃ SF (VerifiableInference.Desc.Key.ownTest PF).rounds
      (gOwn (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ PF.W)) fun _ _ _ => true).run 2 A0 = .ok (sh₃ SF st) := hr₁
  unfold A2
  rw [hr₂]
  rfl

/-- **The test's state on entry has the written shape.** -/
theorem entry_shape {st : S₃} {t : T12} (he : enterOwn st = .ok t) (hsh : sh₃ SF st = A2) :
    testSh t = testOf A2 := by
  have e : t = { st := st.st, book := st.book, roots := st.roots, g := st.loc.own, pass := .nothing
                 mask := st.loc.mask } := (Except.ok.inj he).symm
  subst e
  rw [← hsh]
  rfl

variable (JI JW : ProofFile.Honest.K1.SendJob Wd Y) (A : SendPub) (lift : Local W₀ Rc Xi Tr → Wd)
  (ask : Local W₀ Rc Xi Tr → ProofFile.Honest.K14.Ask)

/-- **What the job's test asks at a stand of the pair**, from the closed lines and the five named premises. -/
theorem front_own (hs : KeySourced Z Xs Nr Pl) (scope : VerifierAndGoals.InScope Z = true)
    (hbs : T₃.bs = (descriptionFromSource Xs Nr Pl).second.blocksInOrder) (hft : T₃.ft = (descriptionFromSource Xs Nr Pl).lastChainFirstTreeNumber)
    (hfun : ∀ k w h s s', T₃.begun k w h s → T₃.begun k w h s' → s = s')
    (hZ : ThirdShaped T₃ v A0) (hpl : pWK Pl = piKWFull)
    (hms : (jobKWAt Xs Nr Pl JI JW A lift ask).mems.map (·.shape) = msKW)
    (htr : (jobKWAt Xs Nr Pl JI JW A lift ask).trees = ProofFile.Honest.K12.AtProof.treesW piKWFull)
    {k : Coins Bk} {st : S₃} {m : Mid (Local W₀ Rc Xi Tr) Y} {E : Env} {V : Type}
    (c : RowCoins [(firstPart (jobKWAt Xs Nr Pl JI JW A lift ask).toRun.toTest : Part V (Local W₀ Rc Xi Tr) Y),
      restPart (jobKWAt Xs Nr Pl JI JW A lift ask).toRun.toTest])
    (hT : Thr T₃ 2 k st m E) (hS : saidLast (descriptionFromSource Xs Nr Pl) T₃ 2 k m)
    (hag : Agree (jobKWAt Xs Nr Pl JI JW A lift ask).toRun.toTest m.st.input (frontOf m)
      (jobKWAt Xs Nr Pl JI JW A lift ask).toRun.toTest.s₀
      (firstRd (jobKWAt Xs Nr Pl JI JW A lift ask).toRun.toTest c.1)
      (restCoins (jobKWAt Xs Nr Pl JI JW A lift ask).toRun.toTest c.2.1))
    (hop : ∃ depths src₀,
      ((jobKWAt Xs Nr Pl JI JW A lift ask).toRun.toTest.trees₀ m.st.input (frontOf m)
        (restCoins (jobKWAt Xs Nr Pl JI JW A lift ask).toRun.toTest c.2.1).mem
        ((jobKWAt Xs Nr Pl JI JW A lift ask).toRun.toTest.first m.st.input (frontOf m)
          (restCoins (jobKWAt Xs Nr Pl JI JW A lift ask).toRun.toTest c.2.1))).map (·.1) = depths ∧
      OpensFit (jobKWAt Xs Nr Pl JI JW A lift ask).toRun.toTest
        (proximityTestKind guardedProximityTestParts (jobKWAt Xs Nr Pl JI JW A lift ask).toRun.toTest.p : Block T12 Unit).rounds depths src₀
        E.sent ∧
      OldAt E ((jobKWAt Xs Nr Pl JI JW A lift ask).toRun.toTest.trees₀ m.st.input (frontOf m)
        (restCoins (jobKWAt Xs Nr Pl JI JW A lift ask).toRun.toTest c.2.1).mem
        ((jobKWAt Xs Nr Pl JI JW A lift ask).toRun.toTest.first m.st.input (frontOf m)
          (restCoins (jobKWAt Xs Nr Pl JI JW A lift ask).toRun.toTest c.2.1))) src₀)
    (hden : ∀ G, ((jobKWAt Xs Nr Pl JI JW A lift ask).toRun.toTest.rec₀ m.st.input (frontOf m)).st.groups[
        ((jobKWAt Xs Nr Pl JI JW A lift ask).toRun.toTest.rec₀ m.st.input (frontOf m)).g]? = some G →
      ∀ r ∈ (runRows ((jobKWAt Xs Nr Pl JI JW A lift ask).toRun.toTest.rec₀ m.st.input (frontOf m)).st
        G).toList, DenseRow r)
    (hcl : claimsB ((jobKWAt Xs Nr Pl JI JW A lift ask).toRun.toTest.rec₀ m.st.input (frontOf m)) = true)
    (hsay : ∀ G, ((jobKWAt Xs Nr Pl JI JW A lift ask).toRun.toTest.rec₀ m.st.input (frontOf m)).st.groups[
        ((jobKWAt Xs Nr Pl JI JW A lift ask).toRun.toTest.rec₀ m.st.input (frontOf m)).g]? = some G →
      AllSay rdE (begun ((jobKWAt Xs Nr Pl JI JW A lift ask).toRun.toTest.rec₀ m.st.input (frontOf m)).st
          ((jobKWAt Xs Nr Pl JI JW A lift ask).toRun.toTest.rec₀ m.st.input (frontOf m)).g G)
        (runRows ((jobKWAt Xs Nr Pl JI JW A lift ask).toRun.toTest.rec₀ m.st.input (frontOf m)).st G).toList
        (wordsAt (begun ((jobKWAt Xs Nr Pl JI JW A lift ask).toRun.toTest.rec₀ m.st.input (frontOf m)).st
            ((jobKWAt Xs Nr Pl JI JW A lift ask).toRun.toTest.rec₀ m.st.input (frontOf m)).g G)
          (layoutOf ((jobKWAt Xs Nr Pl JI JW A lift ask).toRun.toTest.rec₀ m.st.input (frontOf m)).st G)
          (plainMany (jobKWAt Xs Nr Pl JI JW A lift ask) m.st.input (frontOf m)
            (restCoins (jobKWAt Xs Nr Pl JI JW A lift ask).toRun.toTest c.2.1)))) :
    OwnFrontDense (jobKWAt Xs Nr Pl JI JW A lift ask).toRun.toTest enterOwn leaveOwn st m E c := by
  have hen := enters_own Xs Nr Pl JI JW A lift ask hbs hft hfun hT hS
  have hsh := shape_own hs scope hbs hZ hT
  have hN := entry_shape hen hsh
  have hp : (jobKWAt Xs Nr Pl JI JW A lift ask).toRun.toTest.p = piKWFull := hpl
  have he : (jobKWAt Xs Nr Pl JI JW A lift ask).toRun.toTest.p.early = true :=
    (own_place_in_scope hs scope).1
  have five : frontFiveB (jobKWAt Xs Nr Pl JI JW A lift ask).toRun.toTest.p CF
      (testSh ((jobKWAt Xs Nr Pl JI JW A lift ask).toRun.toTest.rec₀ m.st.input (frontOf m))) = true := by
    rw [hN, hp]
    exact five_KW
  have tid : stTidyB ((jobKWAt Xs Nr Pl JI JW A lift ask).toRun.toTest.rec₀ m.st.input (frontOf m)).st = true := by
    have e : ((jobKWAt Xs Nr Pl JI JW A lift ask).toRun.toTest.rec₀ m.st.input (frontOf m)).st = st.st := by
      have q := Except.ok.inj hen
      rw [← q]
    rw [e]
    have q : (sh₃ SF st).2.tidy = true := by
      rw [hsh]
      exact tidy_A2
    exact q
  obtain ⟨Dp, S⟩ := frontAsksD_of_five (jobKWAt Xs Nr Pl JI JW A lift ask).toRun.toTest m.st.input (frontOf m) CF he
    five tid hden hcl
  have hmany : ProofFile.Honest.K12.Light.manyFitsS (jobKWAt Xs Nr Pl JI JW A lift ask).p
      ((jobKWAt Xs Nr Pl JI JW A lift ask).mems.map (·.shape)) (jobKWAt Xs Nr Pl JI JW A lift ask).trees
      (thinOf (testSh ((jobKWAt Xs Nr Pl JI JW A lift ask).rec₀ m.st.input (frontOf m)))) = true := by
    have hN' : testSh ((jobKWAt Xs Nr Pl JI JW A lift ask).rec₀ m.st.input (frontOf m)) = testOf A2 := hN
    have hp' : (jobKWAt Xs Nr Pl JI JW A lift ask).p = piKWFull := hpl
    rw [hN', hp', hms, htr]
    exact many_KW
  obtain ⟨d1, d2, d3⟩ := dataThree_of_frontD (jobKWAt Xs Nr Pl JI JW A lift ask) m.st.input (frontOf m) CF Dp he five S
    hmany (restCoins (jobKWAt Xs Nr Pl JI JW A lift ask).toRun.toTest c.2.1)
  have hts : Dp.ts.length = 3 := by
    have q := ts_of_frontD (jobKWAt Xs Nr Pl JI JW A lift ask).toRun.toTest m.st.input (frontOf m) CF Dp he five S
    rw [hN, hp] at q
    exact q.trans tsLen_KW
  refine ⟨hag, hop, hen, ?_, ?_, ?_, ⟨CF, Dp, _, _, ?_, S, ⟨d1, d2, d3, hsay⟩⟩, fun t' rs gs _ => ⟨_, rfl⟩⟩
  · rw [hp]
    exact H2K.Pub.piKWFull_planOk
  · rw [hp]
    exact formPub_KW
  · rw [hp]
    exact termLen_KW
  · rw [hp, hts, codes_KW]
    exact planB_KW_full

end

end AtPublicFiles.KeyLastChain

#print axioms AtPublicFiles.KeyLastChain.tidy_A2
#print axioms AtPublicFiles.KeyLastChain.tsLen_KW
#print axioms AtPublicFiles.KeyLastChain.codes_KW
#print axioms AtPublicFiles.KeyLastChain.shape_own
#print axioms AtPublicFiles.KeyLastChain.entry_shape
#print axioms AtPublicFiles.KeyLastChain.front_own
