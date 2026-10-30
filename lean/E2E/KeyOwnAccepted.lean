-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
E2E/KeyOwnAccepted.lean: the key file's own proximity test is accepted from the pair, at every letter for a fall, where the
five named premises of `front_own` hold at each stand.

  `OwnAsks`: the five, as one structure: the coins agree; the depths, sources and old tables; the rows are dense; they pass
    the ground's tests; they hold at the prover's words.
  `stages_KW`: the place's first two stages, by the kernel.
  `acceptedS_own`: `AcceptedS` at member 2.

What stays open. `OwnAsks` at each stand; that the half stands at the place (`hhalf`); the written place and job's shapes.
Nothing on soundness, completeness, hiding or binding.
-/
import E2E.KeyOwnFront
import E2E.KeyOwnGuarded

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace AtPublicFiles.KeyLastChain
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun OnBytes.Means Cb
open VerifiableInference.Desc.Ground.Sh
open H2K.Sw H2K.JointK H2K.First
open Johnson.Prover.Link
open ProofFile.Honest ProofFile.Honest.K12
open ProofFile.Honest.K12.Light (ManyJob plainMany)
open ProofFile.Honest.K14 (SendPub)
open ProofFile.Honest.Sh (claimsB)
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.K12 (T12 proximityTestKind guardedProximityTestParts)
open VerifiableInference.Desc.K12.Seat (enterOwn leaveOwn)
open VerifiableInference.Desc.Third (S₃)
open VerifiableInference.Desc.Key (Xi Source LaterPlaces descriptionFromSource)
open AtPublicFiles.KeyLay (pWK jobKWAt)
open AtPublicFiles.AtFiles (KeySourced ThirdShaped)
open AtPublicFiles.AtFiles.Full (A0)
open H2K.Member (piKWFull)
open H2K.Pub (sgOf)

theorem stages_KW : ∃ s t rest, piKWFull.nums.stages = s :: t :: rest ∧ s.k = (sgOf s).h + (sgOf s).g :=
  ⟨_, _, _, rfl, by decide +kernel⟩

section
variable {W Y V : Type}

/-- **The five premises, at a job, a state of the run, the available tables and the two parts' coins.** -/
structure OwnAsks (A : ManyJob W Y) (m : Mid W Y) (E : Env)
    (c : RowCoins [(firstPart A.toRun.toTest : Part V W Y), restPart A.toRun.toTest]) : Prop where
  agree : Agree A.toRun.toTest m.st.input (frontOf m) A.toRun.toTest.s₀ (firstRd A.toRun.toTest c.1)
    (restCoins A.toRun.toTest c.2.1)
  opens : ∃ depths src₀,
    (A.toRun.toTest.trees₀ m.st.input (frontOf m) (restCoins A.toRun.toTest c.2.1).mem
      (A.toRun.toTest.first m.st.input (frontOf m) (restCoins A.toRun.toTest c.2.1))).map (·.1) = depths ∧
    OpensFit A.toRun.toTest (proximityTestKind guardedProximityTestParts A.toRun.toTest.p : Block T12 Unit).rounds depths src₀ E.sent ∧
    OldAt E (A.toRun.toTest.trees₀ m.st.input (frontOf m) (restCoins A.toRun.toTest c.2.1).mem
      (A.toRun.toTest.first m.st.input (frontOf m) (restCoins A.toRun.toTest c.2.1))) src₀
  dense : ∀ G, (A.toRun.toTest.rec₀ m.st.input (frontOf m)).st.groups[
      (A.toRun.toTest.rec₀ m.st.input (frontOf m)).g]? = some G →
    ∀ r ∈ (runRows (A.toRun.toTest.rec₀ m.st.input (frontOf m)).st G).toList, DenseRow r
  claims : claimsB (A.toRun.toTest.rec₀ m.st.input (frontOf m)) = true
  say : ∀ G, (A.toRun.toTest.rec₀ m.st.input (frontOf m)).st.groups[
      (A.toRun.toTest.rec₀ m.st.input (frontOf m)).g]? = some G →
    AllSay rdE (begun (A.toRun.toTest.rec₀ m.st.input (frontOf m)).st
        (A.toRun.toTest.rec₀ m.st.input (frontOf m)).g G)
      (runRows (A.toRun.toTest.rec₀ m.st.input (frontOf m)).st G).toList
      (wordsAt (begun (A.toRun.toTest.rec₀ m.st.input (frontOf m)).st
          (A.toRun.toTest.rec₀ m.st.input (frontOf m)).g G)
        (layoutOf (A.toRun.toTest.rec₀ m.st.input (frontOf m)).st G)
        (plainMany A m.st.input (frontOf m) (restCoins A.toRun.toTest c.2.1)))

end

section
variable {Z : VerifierAndGoals.PublicFiles} {Xs : Source} {Nr : H2U.PlaceNums} {Pl : LaterPlaces} {Bk : ProverCoinCounts}
  {W₀ Rc Tr Y Wd : Type}
  {T₃ : Thread Bk (descriptionFromSource Xs Nr Pl).S₃ (descriptionFromSource Xs Nr Pl).Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Y Xi}
  {v : S₃ → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool}
  {Said : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) Y → Prop}
  (JI JW : ProofFile.Honest.K1.SendJob Wd Y) (A : SendPub) (lift : Local W₀ Rc Xi Tr → Wd)
  (ask : Local W₀ Rc Xi Tr → ProofFile.Honest.K14.Ask)

/-- **Member 2 is accepted, from the pair, at every letter for a fall.** -/
theorem acceptedS_own (hs : KeySourced Z Xs Nr Pl) (scope : VerifierAndGoals.InScope Z = true)
    (hbs : T₃.bs = (descriptionFromSource Xs Nr Pl).second.blocksInOrder) (hft : T₃.ft = (descriptionFromSource Xs Nr Pl).lastChainFirstTreeNumber)
    (hfun : ∀ k w h s s', T₃.begun k w h s → T₃.begun k w h s' → s = s')
    (hZ : ThirdShaped T₃ v A0) (hpl : pWK Pl = piKWFull)
    (hms : (jobKWAt Xs Nr Pl JI JW A lift ask).mems.map (·.shape) = msKW)
    (htr : (jobKWAt Xs Nr Pl JI JW A lift ask).trees = ProofFile.Honest.K12.AtProof.treesW piKWFull)
    (hhalf : (T₃.hs.find? fun g => g.place == (jobKWAt Xs Nr Pl JI JW A lift ask).toRun.toTest.p.place) =
      some (proverSideOfProximityTest (jobKWAt Xs Nr Pl JI JW A lift ask).toRun.toTest :
        Placed (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Y).needsField)
    (hlast : ∀ k m, Said 2 k m → saidLast (descriptionFromSource Xs Nr Pl) T₃ 2 k m)
    (hopen : ∀ k st m E, ThrS T₃ Said 2 k st m E → m.opened.isSome = true)
    (hasks : ∀ k st m E
      (c : RowCoins [(firstPart (jobKWAt Xs Nr Pl JI JW A lift ask).toRun.toTest :
          Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Y),
        restPart (jobKWAt Xs Nr Pl JI JW A lift ask).toRun.toTest]),
      ThrS T₃ Said 2 k st m E →
      lendRow Bk (Bk.rowsOf T₃.chain) (k.look T₃.chain) (jobKWAt Xs Nr Pl JI JW A lift ask).toRun.toTest.p.place
        [(firstPart (jobKWAt Xs Nr Pl JI JW A lift ask).toRun.toTest :
          Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Y),
        restPart (jobKWAt Xs Nr Pl JI JW A lift ask).toRun.toTest] 0 = .ok c →
      OwnAsks (jobKWAt Xs Nr Pl JI JW A lift ask) m E c)
    (fall : Nat → S₃ → List Fmt.Drawn → Option String) : AcceptedS T₃ Said fall 2 := by
  refine acceptedS_guarded T₃ Said 2 (jobKWAt Xs Nr Pl JI JW A lift ask).toRun.toTest enterOwn leaveOwn
    ⟨?_, hhalf, ?_, hopen, fun k st m E c hT hc => ?_⟩ fall
  · obtain ⟨blk, hb, hseat⟩ := seat_own Xs Nr Pl JI JW A lift ask
    exact ⟨blk, by rw [hbs]; exact hb, hseat⟩
  · have hp : (jobKWAt Xs Nr Pl JI JW A lift ask).toRun.toTest.p = piKWFull := hpl
    rw [hp]
    exact stages_KW
  · obtain ⟨a, o, d, cl, sy⟩ := hasks k st m E c hT hc
    exact front_own JI JW A lift ask hs scope hbs hft hfun hZ hpl hms htr c hT.1 (hlast k m hT.2) a o d cl sy

end

end AtPublicFiles.KeyLastChain

#print axioms AtPublicFiles.KeyLastChain.stages_KW
#print axioms AtPublicFiles.KeyLastChain.acceptedS_own
