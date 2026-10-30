-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- K12's simulator: the offline row of the test on G_u, at a run.
/-
Johnson/Desc/ProofFile/Honest/K12/Sim2/RowFoldedAtRun.lean: OnAtRun₂ (Law/OwedAtRun.lean) at the list of
the test on G_u, at the key file's shared chain.

  LeftAtFolded       what is left at a stand: the two clauses on the asks
  onAtRun_folded     the statement

Paid at every stand: the door (door_clause_any), FiveAt, TreesAt (trees_at_run_U). Left: hleft; on the
filling hg, hgU, hgO; on the book hT, hb; public: the rest.

Limits. The rule moves the debt and pays none of it. The condition reads the input and the carried
values: no later law may take it as a hypothesis on a run and then speak of the random values as sampled
anew. Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim2.RowFolded
import Johnson.Desc.ProofFile.Honest.K12.Sim2.RowRangesAtRun
import Johnson.Desc.ProofFile.Honest.K12.Sim2.SharedChainAtRun
import Johnson.Desc.ProofFile.Honest.K12.Sim.TreesAtRunU
import Johnson.Desc.ProofFile.Honest.K12.Sim.FrameAtRun

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace ProofFile.Honest.K12.Sim2
open VerifiableInference.Desc (Block FileDescription Oracle Place)
open VerifiableInference.Desc.K12 (proximityTestKind guardedProximityTestParts T12)
open ProofFile.Honest ProofFile.Honest.K12 ProofFile.Honest.K12.Light

/-! ## On at a run -/

section Run
open VerifiableInference.Desc.Key (Xi LaterPlaces Source)
open H2K.Member (piKUFull codesKeyFull)
open AtPublicFiles.AtFiles (keyFileDescription KeySourced)
open OnBytes (TableKey)
open ProofFile.Honest.K14 (SendPub sendPlace jobU jobOmega sendingPart liftSend sendingsFit SendDeclared)
open Desc.K14.Honest (ReadsNone)
open Johnson.G.OfPlan (rootsOf)
open AtPublicFiles.KeyLay (jobKU)

variable {Z : VerifierAndGoals.PublicFiles} {Xs : Source} {N : H2U.PlaceNums} {Pl : LaterPlaces} {W₀ Rc X₀ Y : Type}

theorem rest_KU : restLen piKUFull.nums.stages ≠ 0 := by decide +kernel

/-- **What is left at a stand**: the two clauses on the asks, at the job. -/
def LeftAtFolded (J : TestJob (Common W₀ Rc TableKey) X₀) (K : OnBytes.Codes)
    (os : List (Fmt.Shape × Fmt.TreeSource)) (mem : ℕ → Stretch)
    (m : ProofFile.Honest.Mid (Common W₀ Rc TableKey) X₀) : Prop :=
  ∃ Dp cc Rw, Dp.ts.length = os.length ∧
    ShapeAsksD J m.st.input (restFront J m) (carriedCoins J mem) (heardIn J m) K Dp ∧
    DataAsks J m.st.input (restFront J m) (carriedCoins J mem) (heardIn J m) Dp cc Rw

/-- **The clause of the rule at the list of the test on G_u.** -/
theorem onAtRun_folded (scope : VerifierAndGoals.InScope Z = true) (hS : KeySourced Z Xs N Pl) {Bk : ProverCoinCounts}
    {H : Prover W₀ Rc Xi TableKey Unit X₀ Y}
    {G : Sides (keyFileDescription Xs N Pl) Bk W₀ Rc TableKey Unit X₀ Y} {w₀ : W₀} {rc : Rc} {x : Xi}
    {k : Coins Bk} {ρ : Draws} {R : Ready W₀ Rc Xi TableKey Unit X₀ Y} {r : RunC (keyFileDescription Xs N Pl)}
    (T : ThreadsP (keyFileDescription Xs N Pl) Bk (G.prover H) w₀ rc x k R)
    (hρ : ρ.due (keyFileDescription Xs N Pl) = true)
    (hR : ready (keyFileDescription Xs N Pl) Bk (G.prover H) w₀ rc x k = .ok R)
    (hrun : runC (keyFileDescription Xs N Pl) Bk (G.prover H) w₀ rc x k ρ = .ok r)
    (Ap : SendPub) (bs : List (Block Desc.K14.St Unit))
    (wt : Common W₀ Rc TableKey → Weights) (rd : Common W₀ Rc TableKey → TableRand)
    (L : Lettered Bk (keyFileDescription Xs N Pl).S₂ (keyFileDescription Xs N Pl).Cl Empty (Common W₀ Rc TableKey) X₀
      TableKey)
    (hplace : L.place = (pKU Pl).place)
    (hrow : L.row = testPairs (jobKU (X := X₀) Ap (pKU Pl) bs (G.prover H).storedWords wt rd).toRun.toTest
      (simLocU Ap.P (sentOf Ap.P.S) bs (pKU Pl) 1))
    (hOn : L.On = OnEntry Face.shared
      (jobKU (X := X₀) Ap (pKU Pl) bs (G.prover H).storedWords wt rd).toRun.toTest
      (simLocU Ap.P (sentOf Ap.P.S) bs (pKU Pl) 1) codesKeyFull 1 (pKU Pl).nums.first)
    (hg : ((G.prover H).shared.find? fun g => g.place == (pKU Pl).place) =
      some (proverSideOfProximityTest (jobKU (X := X₀) Ap (pKU Pl) bs (G.prover H).storedWords wt rd).toRun.toTest))
    (hT : tiesB Bk (pKU Pl).place 2 = true)
    -- the rounds in front of the test
    (d0 d1 d2 : Fmt.DeclaredRound) (e : Fmt.Entry) (post : List Fmt.DeclaredRound)
    (h0 : ReadsNone d0) (h1 : ReadsNone d1) (h2 : ReadsNone d2)
    (hpre : (H2K.JointK.keySharedPre Xs.chains Pl).flatMap (·.rounds) =
      d0 :: d1 :: d2 :: { entry := e, stored := [Desc.K14.readsAtLoc Ap.P.S.fold Ap.P.item] } :: post)
    -- the two sendings
    (preU tU preO tO : List (Block (keyFileDescription Xs N Pl).S₂ (keyFileDescription Xs N Pl).Cl))
    (bU bO : Block (keyFileDescription Xs N Pl).S₂ (keyFileDescription Xs N Pl).Cl)
    (hcutU : (keyFileDescription Xs N Pl).shared.blocksInOrder = preU ++ bU :: tU)
    (hcutO : (keyFileDescription Xs N Pl).shared.blocksInOrder = preO ++ bO :: tO)
    (hpU : bU.place = sendPlace 2) (hpO : bO.place = sendPlace 5)
    (hgU : ((G.prover H).shared.find? fun g => g.place == bU.place) = some ⟨bU.place,
      [(liftSend (askOf Ap wt rd) (sendingPart (jobU Ap)) :
        Part Empty (Common W₀ Rc TableKey) X₀)]⟩)
    (hgO : ((G.prover H).shared.find? fun g => g.place == bO.place) = some ⟨bO.place,
      [(liftSend (askOf Ap wt rd) (sendingPart (jobOmega Ap)) :
        Part Empty (Common W₀ Rc TableKey) X₀)]⟩)
    (hdU : SendDeclared bU (jobU Ap)) (hdO : SendDeclared bO (jobOmega Ap))
    (hinU : (preU.flatMap (·.rounds)).length + 2 ≤
      ((H2K.JointK.keySharedPre Xs.chains Pl).flatMap (·.rounds)).length)
    (hinO : (preO.flatMap (·.rounds)).length + 2 ≤
      ((H2K.JointK.keySharedPre Xs.chains Pl).flatMap (·.rounds)).length)
    (hb : bookCutsU Bk Ap (pKU Pl) = true)
    (hQ : sendingsFit Ap.P = true) (hcf : colFitsU Ap (pKU Pl) = true)
    (hfr : freshFitsU Ap (pKU Pl) = true)
    (hroom : 2 * (stage₀ (pKU Pl)).k + 1 ≤ (stage₀ (pKU Pl)).h + (stage₀ (pKU Pl)).Z.l)
    (hwU : widthFits (jobU Ap) 0 = true) (hwO : widthFits (jobOmega Ap) 1 = true)
    (hat : Ap.atPoint < (preU.flatMap (·.rounds)).length)
    (hsrc : (pKU Pl).nums.first.map (fun o => ProofFile.Honest.srcOf 1 o.2) =
      [(1, rootsOf (preU.flatMap (·.rounds)) + 0), (1, rootsOf (preO.flatMap (·.rounds)) + 1)])
    (hleft : ∀ (m : ProofFile.Honest.Mid (Common W₀ Rc TableKey) X₀)
      (ca : CsAll (restMember (V := Empty)
        (jobKU (X := X₀) Ap (pKU Pl) bs (G.prover H).storedWords wt rd).toRun.toTest
        (simLocU Ap.P (sentOf Ap.P.S) bs (pKU Pl) 1)).part.carries)
      (σ : Side (keyFileDescription Xs N Pl).S₂ (keyFileDescription Xs N Pl).Cl Empty (Common W₀ Rc TableKey) X₀ TableKey)
      (t' : List (Block (keyFileDescription Xs N Pl).S₂ (keyFileDescription Xs N Pl).Cl)),
      testSide (keyFileDescription Xs N Pl).shared.blocksInOrder
        (jobKU (X := X₀) Ap (pKU Pl) bs (G.prover H).storedWords wt rd).toRun.toTest
        (simLocU Ap.P (sentOf Ap.P.S) bs (pKU Pl) 1) [] = some σ →
      StandsAt (keyFileDescription Xs N Pl).shared.blocksInOrder R.shared σ (restMember (V := Empty)
                            (jobKU (X := X₀) Ap (pKU Pl) bs (G.prover H).storedWords wt rd).toRun.toTest
                            (simLocU Ap.P (sentOf Ap.P.S) bs (pKU Pl) 1)) (H2K.JointK.keySharedPre Xs.chains Pl) t'
        (firstLen (pKU Pl).nums.stages) →
      InsideOf .shared Bk 1 (G.prover H).shared σ.block
        (T.I₂ (H2K.JointK.keySharedPre Xs.chains Pl).length) (σ.roundsTo 1) k m
        (envOf (H.storedWords w₀ rc) (fun _ _ => none) (r.run.played.2.1.take
          (((H2K.JointK.keySharedPre Xs.chains Pl).flatMap (·.rounds)).length + σ.roundsTo 1))) →
      m.seen = roundsOf (r.run.played.2.1.take
        (((H2K.JointK.keySharedPre Xs.chains Pl).flatMap (·.rounds)).length + σ.roundsTo 1)) →
      r.called ⟨L.place, 1⟩ = true →
      midSharedAtW (keyFileDescription Xs N Pl) Bk (G.prover H) w₀ rc x k ρ ⟨L.place, 1⟩ = .ok (some m) →
      carriedAt Bk k 1 ⟨L.place, 1⟩ (restMember (V := Empty)
        (jobKU (X := X₀) Ap (pKU Pl) bs (G.prover H).storedWords wt rd).toRun.toTest
        (simLocU Ap.P (sentOf Ap.P.S) bs (pKU Pl) 1)).part = .ok ca →
      (laidOf (keyFileDescription Xs N Pl) ρ [] (r.run.played.2.1.take
                     (((H2K.JointK.keySharedPre Xs.chains Pl).flatMap (·.rounds)).length + σ.roundsTo 1)) []).front 1
          (storedShown (H.storedWords w₀ rc) (storedAsks (keyFileDescription Xs N Pl) ρ)) =
        r.run.beforeAt (storedShown (H.storedWords w₀ rc) r.run.storedAsked) ⟨L.place, 1⟩ →
      LeftAtFolded (jobKU (X := X₀) Ap (pKU Pl) bs (G.prover H).storedWords wt rd).toRun.toTest codesKeyFull
        (pKU Pl).nums.first (stretches _ ca) m) :
    OnAtRun₂ T ρ r L := by
  intro σ hσ u hu pre' t' hcut m ca hin hseen hca hc hmid hfrt
  have hpl : σ.block.place = L.place := side_place hσ
  obtain ⟨pk, Al⟩ := alike_KU scope hS
  have hJp : (jobKU (X := X₀) Ap (pKU Pl) bs (G.prover H).storedWords wt rd).toRun.toTest.p =
      pKU Pl := rfl
  have hσ' : testSide (keyFileDescription Xs N Pl).shared.blocksInOrder
      (jobKU (X := X₀) Ap (pKU Pl) bs (G.prover H).storedWords wt rd).toRun.toTest
      (simLocU Ap.P (sentOf Ap.P.S) bs (pKU Pl) 1) [] = some σ := by
    unfold testSide
    rw [hJp, ← hplace, ← hrow]
    exact hσ
  obtain ⟨b, hf, hbp, hr, hor⟩ := find_folded scope hS.named
    (jobKU (X := X₀) Ap (pKU Pl) bs (G.prover H).storedWords wt rd).toRun.toTest rfl
  have F : PlaceFacts (jobKU (X := X₀) Ap (pKU Pl) bs (G.prover H).storedWords wt rd).toRun.toTest.p
      dsKU := facts_KU facts_KUFull _ pk Al
  obtain ⟨-, -, hall⟩ := any_at_place (V := Empty)
    (jobKU (X := X₀) Ap (pKU Pl) bs (G.prover H).storedWords wt rd).toRun.toTest
    (simLocU Ap.P (sentOf Ap.P.S) bs (pKU Pl) 1) F _ b hf hbp hr hor rfl rfl rfl
  obtain ⟨-, hmem, -⟩ := hall [] σ hσ'
  rw [hOn, hfrt]
  rw [hmem] at hu
  rcases List.mem_cons.1 hu with rfl | hu'
  · intro hn
    cases hn
  obtain rfl := List.mem_singleton.1 hu'
  have hpos : restLen (jobKU (X := X₀) Ap (pKU Pl) bs (G.prover H).storedWords wt rd).toRun.toTest.p.nums.stages ≠ 0 := by
    show restLen (pKU Pl).nums.stages ≠ 0
    rw [congrArg (·.stages) Al.nums]
    exact rest_KU
  have hg' : ((G.prover H).shared.find? fun g => g.place == σ.block.place) =
      some (proverSideOfProximityTest (jobKU (X := X₀) Ap (pKU Pl) bs (G.prover H).storedWords wt rd).toRun.toTest) := by
    rw [hpl, hplace]
    exact hg
  have hc' : r.called ⟨σ.block.place, 1⟩ = true := by
    rw [hpl]
    exact hc
  obtain ⟨pre, t, c, m₁, S, hm₁, hca₁, hin₁, F5⟩ := five_at_test₂ hS.named.plan hρ hR
    (jobKU (X := X₀) Ap (pKU Pl) bs (G.prover H).storedWords wt rd).toRun.toTest F _ rfl
    (fun s w fr mem mem' hh => rowsMu_many _ s w fr mem mem' hh)
    (simLocU Ap.P (sentOf Ap.P.S) bs (pKU Pl) 1) rfl rfl [] σ hσ' b hf hbp hr hor hg' hT hrun hc' hpos
    (storedShown (H.storedWords w₀ rc) r.run.storedAsked)
  -- what stands in front
  have Q := ((keyFileDescription Xs N Pl).planOk_ok).1 hS.named.plan
  have hnd := (places_nodup Q.places).2.1
  have hcutK := H2K.JointK.keyShared_cut Xs.chains Pl
  have hkp : (H2K.JointK.keyGu Pl).place = (pKU Pl).place := H2K.JointK.k12_place guardedProximityTestParts (pKU Pl)
  have key := find_after_nodup (fun b : Block Desc.K14.St VerifiableInference.Desc.Key.Claim => b.place)
    (H2K.JointK.keySharedPre Xs.chains Pl) (H2K.JointK.keyGu Pl)
    ((Pl.O.toList.map H2K.JointK.keyOmega) ++ [H2K.JointK.keySharedEnd Xs.chains Pl])
    (by rw [← hcutK]; exact hnd) (pKU Pl).place hkp
  have hbK : b = H2K.JointK.keyGu Pl := by
    have hf' : (((VerifiableInference.Desc.Key.sharedChain Xs.chains Pl).retype
        (Cl' := VerifiableInference.Desc.Key.Claim)).blocksInOrder.find? fun b => b.place == (pKU Pl).place) =
        some b := hf
    rw [hcutK, key] at hf'
    exact (Option.some.inj hf').symm
  have hblk : σ.block = b := by
    have h₁ := hσ'
    unfold testSide Side.seated at h₁
    obtain ⟨b', hb', e'⟩ := Option.map_eq_some_iff.1 h₁
    have : b' = b := Option.some.inj (hb'.symm.trans hf)
    rw [← e', this]
  have epre : pre = H2K.JointK.keySharedPre Xs.chains Pl := by
    have c1 := S.cut
    rw [hblk, hbK] at c1
    exact pre_of_cut (fun b : Block Desc.K14.St VerifiableInference.Desc.Key.Claim => b.place) _ _ _ _ _ _
      c1 hcutK hnd
  subst epre
  have ec := S.cut
  obtain ⟨rfl, rfl⟩ := both_of_cut (fun b : Block Desc.K14.St VerifiableInference.Desc.Key.Claim => b.place)
    _ _ _ _ _ _ hcut ec hnd
  -- the clause door
  obtain ⟨m', hm', -, hdoor⟩ := door_clause_any (F := keyFileDescription Xs N Pl) hS.named.plan Ap (pKU Pl)
    (sentOf Ap.P.S) bs wt rd none 1 hR σ
    (restMember (jobKU (X := X₀) Ap (pKU Pl) bs (G.prover H).storedWords wt rd).toRun.toTest
      (simLocU Ap.P (sentOf Ap.P.S) bs (pKU Pl) 1)) _ _ S d0 d1 d2 e post h0 h1 h2 hpre hrun hc'
  obtain rfl : m₁ = m' := Option.some.inj (Except.ok.inj (hm₁.symm.trans hm'))
  -- the clause trees
  have hTr := trees_at_run_U hS.named.plan hR hrun Ap (pKU Pl) _ wt rd
    (jobKU (X := X₀) Ap (pKU Pl) bs (G.prover H).storedWords wt rd).toRun.toTest rfl
    (simLocU Ap.P (sentOf Ap.P.S) bs (pKU Pl) 1) σ (hpl.trans hplace) _ _ S hc' preU tU preO tO bU bO
    hcutU hcutO hpU hpO hgU hgO hdU hdO hinU hinO hb hQ hcf hfr hroom hwU hwO hat hsrc
    (storedShown (H.storedWords w₀ rc) r.run.storedAsked) m₁ c.2.1.2.2 hm₁ hca₁
  rw [hpl] at hm₁ hca₁ F5 hTr hdoor
  have hmid' : orRefused (midSharedAtW (keyFileDescription Xs N Pl) Bk (G.prover H) w₀ rc x k ρ ⟨L.place, 1⟩) =
      .ok m := hmid
  rw [hm₁] at hmid'
  obtain rfl : m₁ = m := Except.ok.inj (show (Except.ok m₁ : Except Refusal _) = .ok m from hmid')
  obtain rfl : c.2.1.2.2 = ca := Except.ok.inj (hca₁.symm.trans hca)
  refine onEntry_of_free Face.shared _ _ _ 1 _ _ _ m₁ _ ?_
  exact ⟨F5.le, F5.leS, F5.heardFit, F5.heard, hdoor, F5.fold,
    hleft m₁ _ σ _ hσ' S hin hseen hc hm₁ hca hfrt, hTr⟩

end Run

end ProofFile.Honest.K12.Sim2

#print axioms ProofFile.Honest.K12.Sim2.onAtRun_folded
