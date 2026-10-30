-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- K12's simulator: the public premises of the row of the test on G_u.
/-
Johnson/Desc/ProofFile/Honest/K12/Sim2/RowFoldedPub.lean: what onAtRun_folded asks of the numbers and the
book, at the written plan and at keyBook, by Lean's kernel, and the statement with these paid.

  planK, fold_pub_full, fold_book_full, room_KU   at the written plan, by the kernel
  bookCutsU_plan, bookCutsU_place, fold_pub_at, fold_book_at   carried to a plan and a place alike
  chains_of_source, plan_sourced   in scope the plan's codes and shape are the written ones
  onAtRun_folded_key   onAtRun_folded at keyBook and the plan's eight sub-protocols

Limits. onAtRun_folded_key keeps hb8, hr0, hr1 (the eight are made; the roots in front of the two
sendings), the filling's hg, hgU, hgO and hleft as premises. Nothing on completeness, soundness or
hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim2.RowFoldedAtRun
import Johnson.Desc.ProofFile.Honest.K12.Sim2.RowRangesPub
import E2E.KeyLayFits
import Johnson.Desc.ProofFile.Honest.K12.DoorAtWalk
import Johnson.Desc.ProofFile.Honest.K12.Sim.ShownAtRun
import Johnson.Desc.ProofFile.Honest.K12.NearAtHead
import Johnson.Desc.ProofFile.Honest.K12.FitAtHead
import Johnson.Desc.ProofFile.Honest.K12.TreeIsColumnAtHead
import Johnson.Desc.ProofFile.Honest.K12.TableIsColumn
import Johnson.Desc.ProofFile.Honest.K12.SendFitAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace ProofFile.Honest.K12.Sim2
open H2K.Member (piKUFull)
open AtPublicFiles.KeyBook (keyBook fullPub KeyPub foldedTestPlace)
open AtPublicFiles.KeyLay (AK)
open ProofFile.Honest ProofFile.Honest.K12 ProofFile.Honest.K12.Light
open ProofFile.Honest.K14 (jobU jobOmega sendingsFit)
open Lk6.AtPlan (keyFull)

/-- The plan at the written codes and shape. -/
abbrev planK : ProofFile.Honest.K14.SendPub := ProofFile.Honest.K12.Light.planOf keyFull.codes keyFull.once.shape

theorem fold_pub_full : (sendingsFit planK.P && colFitsU planK piKUFull && freshFitsU planK piKUFull &&
    widthFits (jobU planK) 0 && widthFits (jobOmega planK) 1) = true := by decide +kernel

theorem fold_book_full : (fullPub.map fun K => bookCutsU (keyBook K) planK piKUFull &&
    tiesB (keyBook K) foldedTestPlace 2) = some true := by decide +kernel

theorem room_KU : 2 * (stage₀ piKUFull).k + 1 ≤ (stage₀ piKUFull).h + (stage₀ piKUFull).Z.l := by
  decide +kernel

theorem bookCutsU_plan (Bk : ProverCoinCounts) (A : ProofFile.Honest.K14.SendPub) (p : VerifiableInference.Desc.K12.P12) :
    bookCutsU Bk A p = bookCutsU Bk (ProofFile.Honest.K12.Light.planOf A.P.codes A.P.S) p := rfl

theorem bookCutsU_place (Bk : ProverCoinCounts) (A : ProofFile.Honest.K14.SendPub)
    {p q : VerifiableInference.Desc.K12.P12} (h : p.place = q.place) :
    bookCutsU Bk A p = bookCutsU Bk A q := by
  unfold bookCutsU
  rw [h]

/-- **The numbers of the test on G_u, at every plan at the written codes and shape and every place alike
the written one.** -/
theorem fold_pub_at (A : ProofFile.Honest.K14.SendPub) (hc : A.P.codes = keyFull.codes)
    (hS : A.P.S = keyFull.once.shape) {p : VerifiableInference.Desc.K12.P12} (Al : Alike p piKUFull) :
    sendingsFit A.P = true ∧ colFitsU A p = true ∧ freshFitsU A p = true ∧
      2 * (stage₀ p).k + 1 ≤ (stage₀ p).h + (stage₀ p).Z.l ∧
      widthFits (jobU A) 0 = true ∧ widthFits (jobOmega A) 1 = true := by
  have k := fold_pub_full
  simp only [Bool.and_eq_true] at k
  obtain ⟨⟨⟨⟨k1, k2⟩, k3⟩, k4⟩, k5⟩ := k
  have hs : p.nums.stages = piKUFull.nums.stages := congrArg (·.stages) Al.nums
  have ho : p.nums.ownMask = piKUFull.nums.ownMask := congrArg (·.ownMask) Al.nums
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [sendingsFit_plan, hc, hS]
    exact k1
  · rw [colFitsU_plan, hc, hS, colFitsU_stages _ hs]
    exact k2
  · rw [freshFitsU_plan, hc, hS, freshFitsU_stages _ hs ho]
    exact k3
  · have e : stage₀ p = stage₀ piKUFull := by
      unfold stage₀
      rw [hs]
    rw [e]
    exact room_KU
  · rw [(widthFits_plan _ 0).1, hc, hS]
    exact k4
  · rw [(widthFits_plan _ 1).2, hc, hS]
    exact k5

/-- **The book's tests at the test on G_u.** -/
theorem fold_book_at {K : KeyPub} (hK : fullPub = some K) (A : ProofFile.Honest.K14.SendPub)
    (hc : A.P.codes = keyFull.codes) (hS : A.P.S = keyFull.once.shape)
    {p : VerifiableInference.Desc.K12.P12} (hp : p.place = piKUFull.place) :
    bookCutsU (keyBook K) A p = true ∧ tiesB (keyBook K) foldedTestPlace 2 = true := by
  have k := fold_book_full
  rw [hK] at k
  have k' : (bookCutsU (keyBook K) planK piKUFull && tiesB (keyBook K) foldedTestPlace 2) = true :=
    Option.some.inj k
  simp only [Bool.and_eq_true] at k'
  refine ⟨?_, k'.2⟩
  rw [bookCutsU_plan, hc, hS, bookCutsU_place _ _ hp]
  exact k'.1

section Join
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.Key (Xi LaterPlaces Source Claim sharedPar beforeSharedPoint sourceOf)
open H2K.Member (codesKeyFull)
open AtPublicFiles.AtFiles (keyFileDescription KeySourced)
open OnBytes (TableKey)
open ProofFile.Honest.K14 (SendPub sendingPart liftSend sendPlace)
open AtPublicFiles.KeyLay (jobKU)
open Johnson.G.OfPlan (rootsOf)

variable {Z : VerifierAndGoals.PublicFiles} {Xs : Source} {N : H2U.PlaceNums} {Pl : LaterPlaces} {W₀ Rc X₀ Y : Type}

theorem chains_of_source {m : Johnson.G.OfPlan.Made} {X : Source} (h : sourceOf m = .ok X) :
    X.chains = m.p.chains := by
  unfold sourceOf at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  · split at h
    · cases h
    · exact (congrArg Source.chains (Except.ok.inj h)).symm

/-- In scope the plan's codes and shape are the written ones. -/
theorem plan_sourced (scope : VerifierAndGoals.InScope Z = true) (hS : KeySourced Z Xs N Pl)
    (bp : List (ℕ × ℕ)) :
    (sharedPar Xs.chains bp).codes = keyFull.codes ∧ (sharedPar Xs.chains bp).S = keyFull.once.shape := by
  obtain ⟨X₀, m, h0, hm, hX, -, -⟩ := hS.source
  have hk := Johnson.RunOne.Law.KeyInScope.key_in_scope scope
    (Johnson.RunOne.Law.ReadAtO.readOf_publicOfO h0) hm
  have hc := chains_of_source hX
  refine ⟨?_, ?_⟩
  · show Xs.chains.made.sized.key.codes = _
    rw [hc, hk]
  · show Xs.chains.made.sized.key.once.shape = _
    rw [hc, hk]

/-- **The clause of the rule at the list of the test on G_u, at the key's book and the plan's eight
sub-protocols.** What stays: hb8 with hr0, hr1 (the eight, and the roots in front of the two sendings);
the filling's hg, hgU, hgO; hleft. -/
theorem onAtRun_folded_key (scope : VerifierAndGoals.InScope Z = true) (hS : KeySourced Z Xs N Pl) {K : KeyPub}
    (hK : fullPub = some K) {H : Prover W₀ Rc Xi TableKey Unit X₀ Y}
    {G : Sides (keyFileDescription Xs N Pl) (keyBook K) W₀ Rc TableKey Unit X₀ Y} {w₀ : W₀} {rc : Rc} {x : Xi}
    {k : Coins (keyBook K)} {ρ : Draws} {R : Ready W₀ Rc Xi TableKey Unit X₀ Y}
    {r : RunC (keyFileDescription Xs N Pl)}
    (T : ThreadsP (keyFileDescription Xs N Pl) (keyBook K) (G.prover H) w₀ rc x k R)
    (hρ : ρ.due (keyFileDescription Xs N Pl) = true)
    (hR : ready (keyFileDescription Xs N Pl) (keyBook K) (G.prover H) w₀ rc x k = .ok R)
    (hrun : runC (keyFileDescription Xs N Pl) (keyBook K) (G.prover H) w₀ rc x k ρ = .ok r)
    (b1 b2 b3 b4 b5 b6 b7 b8 : Block Desc.K14.St Unit)
    (hb8 : Desc.K14.blocks (sharedPar Xs.chains (VerifiableInference.Desc.Key.beforeSharedPoint Pl)) =
      some [b1, b2, b3, b4, b5, b6, b7, b8])
    (hr0 : rootsOf b1.rounds = 0)
    (hr1 : rootsOf ([b1, b2, b3, b4].flatMap (·.rounds)) = 1)
    (wt : Common W₀ Rc TableKey → Weights) (rd : Common W₀ Rc TableKey → TableRand)
    (L : Lettered (keyBook K) (keyFileDescription Xs N Pl).S₂ (keyFileDescription Xs N Pl).Cl Empty (Common W₀ Rc TableKey) X₀
      TableKey)
    (hplace : L.place = (pKU Pl).place)
    (hrow : L.row = testPairs (jobKU (X := X₀)
        ⟨sharedPar Xs.chains (VerifiableInference.Desc.Key.beforeSharedPoint Pl), 0⟩ (pKU Pl)
        [b1, b2, b3, b4, b5, b6, b7, b8] (G.prover H).storedWords wt rd).toRun.toTest
      (simLocU (sharedPar Xs.chains (VerifiableInference.Desc.Key.beforeSharedPoint Pl))
        (sentOf (sharedPar Xs.chains (VerifiableInference.Desc.Key.beforeSharedPoint Pl)).S)
        [b1, b2, b3, b4, b5, b6, b7, b8] (pKU Pl) 1))
    (hOn : L.On = OnEntry Face.shared (jobKU (X := X₀)
        ⟨sharedPar Xs.chains (VerifiableInference.Desc.Key.beforeSharedPoint Pl), 0⟩ (pKU Pl)
        [b1, b2, b3, b4, b5, b6, b7, b8] (G.prover H).storedWords wt rd).toRun.toTest
      (simLocU (sharedPar Xs.chains (VerifiableInference.Desc.Key.beforeSharedPoint Pl))
        (sentOf (sharedPar Xs.chains (VerifiableInference.Desc.Key.beforeSharedPoint Pl)).S)
        [b1, b2, b3, b4, b5, b6, b7, b8] (pKU Pl) 1) codesKeyFull 1 (pKU Pl).nums.first)
    (hg : ((G.prover H).shared.find? fun g => g.place == (pKU Pl).place) =
      some (proverSideOfProximityTest (jobKU (X := X₀)
                         ⟨sharedPar Xs.chains (VerifiableInference.Desc.Key.beforeSharedPoint Pl), 0⟩ (pKU Pl)
                         [b1, b2, b3, b4, b5, b6, b7, b8] (G.prover H).storedWords wt rd).toRun.toTest))
    (hgU : ((G.prover H).shared.find? fun g => g.place == sendPlace 2) = some ⟨sendPlace 2,
      [(liftSend (askOf ⟨sharedPar Xs.chains (VerifiableInference.Desc.Key.beforeSharedPoint Pl), 0⟩ wt rd)
        (sendingPart (jobU ⟨sharedPar Xs.chains (VerifiableInference.Desc.Key.beforeSharedPoint Pl), 0⟩)) :
        Part Empty (Common W₀ Rc TableKey) X₀)]⟩)
    (hgO : ((G.prover H).shared.find? fun g => g.place == sendPlace 5) = some ⟨sendPlace 5,
      [(liftSend (askOf ⟨sharedPar Xs.chains (VerifiableInference.Desc.Key.beforeSharedPoint Pl), 0⟩ wt rd)
        (sendingPart (jobOmega ⟨sharedPar Xs.chains (VerifiableInference.Desc.Key.beforeSharedPoint Pl), 0⟩)) :
        Part Empty (Common W₀ Rc TableKey) X₀)]⟩)
    (hleft : ∀ (m : ProofFile.Honest.Mid (Common W₀ Rc TableKey) X₀)
      (ca : CsAll (restMember (V := Empty)
        (jobKU (X := X₀) ⟨sharedPar Xs.chains (VerifiableInference.Desc.Key.beforeSharedPoint Pl), 0⟩ (pKU Pl) [b1, b2, b3, b4, b5, b6, b7, b8] (G.prover H).storedWords wt rd).toRun.toTest
        (simLocU (sharedPar Xs.chains (VerifiableInference.Desc.Key.beforeSharedPoint Pl)) (sentOf (sharedPar Xs.chains (VerifiableInference.Desc.Key.beforeSharedPoint Pl)).S) [b1, b2, b3, b4, b5, b6, b7, b8] (pKU Pl) 1)).part.carries)
      (σ : Side (keyFileDescription Xs N Pl).S₂ (keyFileDescription Xs N Pl).Cl Empty (Common W₀ Rc TableKey) X₀ TableKey)
      (t' : List (Block (keyFileDescription Xs N Pl).S₂ (keyFileDescription Xs N Pl).Cl)),
      testSide (keyFileDescription Xs N Pl).shared.blocksInOrder
        (jobKU (X := X₀) ⟨sharedPar Xs.chains (VerifiableInference.Desc.Key.beforeSharedPoint Pl), 0⟩ (pKU Pl) [b1, b2, b3, b4, b5, b6, b7, b8] (G.prover H).storedWords wt rd).toRun.toTest
        (simLocU (sharedPar Xs.chains (VerifiableInference.Desc.Key.beforeSharedPoint Pl)) (sentOf (sharedPar Xs.chains (VerifiableInference.Desc.Key.beforeSharedPoint Pl)).S) [b1, b2, b3, b4, b5, b6, b7, b8] (pKU Pl) 1) [] = some σ →
      StandsAt (keyFileDescription Xs N Pl).shared.blocksInOrder R.shared σ (restMember (V := Empty)
                            (jobKU (X := X₀) ⟨sharedPar Xs.chains (VerifiableInference.Desc.Key.beforeSharedPoint Pl), 0⟩ (pKU Pl) [b1, b2, b3, b4, b5, b6, b7, b8] (G.prover H).storedWords wt rd).toRun.toTest
                            (simLocU (sharedPar Xs.chains (VerifiableInference.Desc.Key.beforeSharedPoint Pl)) (sentOf (sharedPar Xs.chains (VerifiableInference.Desc.Key.beforeSharedPoint Pl)).S) [b1, b2, b3, b4, b5, b6, b7, b8] (pKU Pl) 1)) (H2K.JointK.keySharedPre Xs.chains Pl) t'
        (firstLen (pKU Pl).nums.stages) →
      InsideOf .shared (keyBook K) 1 (G.prover H).shared σ.block
        (T.I₂ (H2K.JointK.keySharedPre Xs.chains Pl).length) (σ.roundsTo 1) k m
        (envOf (H.storedWords w₀ rc) (fun _ _ => none) (r.run.played.2.1.take
          (((H2K.JointK.keySharedPre Xs.chains Pl).flatMap (·.rounds)).length + σ.roundsTo 1))) →
      m.seen = roundsOf (r.run.played.2.1.take
        (((H2K.JointK.keySharedPre Xs.chains Pl).flatMap (·.rounds)).length + σ.roundsTo 1)) →
      r.called ⟨L.place, 1⟩ = true →
      midSharedAtW (keyFileDescription Xs N Pl) (keyBook K) (G.prover H) w₀ rc x k ρ ⟨L.place, 1⟩ = .ok (some m) →
      carriedAt (keyBook K) k 1 ⟨L.place, 1⟩ (restMember (V := Empty)
        (jobKU (X := X₀) ⟨sharedPar Xs.chains (VerifiableInference.Desc.Key.beforeSharedPoint Pl), 0⟩ (pKU Pl) [b1, b2, b3, b4, b5, b6, b7, b8] (G.prover H).storedWords wt rd).toRun.toTest
        (simLocU (sharedPar Xs.chains (VerifiableInference.Desc.Key.beforeSharedPoint Pl)) (sentOf (sharedPar Xs.chains (VerifiableInference.Desc.Key.beforeSharedPoint Pl)).S) [b1, b2, b3, b4, b5, b6, b7, b8] (pKU Pl) 1)).part = .ok ca →
      (laidOf (keyFileDescription Xs N Pl) ρ [] (r.run.played.2.1.take
                     (((H2K.JointK.keySharedPre Xs.chains Pl).flatMap (·.rounds)).length + σ.roundsTo 1)) []).front 1
          (storedShown (H.storedWords w₀ rc) (storedAsks (keyFileDescription Xs N Pl) ρ)) =
        r.run.beforeAt (storedShown (H.storedWords w₀ rc) r.run.storedAsked) ⟨L.place, 1⟩ →
      LeftAtFolded (jobKU (X := X₀) ⟨sharedPar Xs.chains (VerifiableInference.Desc.Key.beforeSharedPoint Pl), 0⟩ (pKU Pl) [b1, b2, b3, b4, b5, b6, b7, b8] (G.prover H).storedWords wt rd).toRun.toTest codesKeyFull
        (pKU Pl).nums.first (stretches _ ca) m) :
    OnAtRun₂ T ρ r L := by
  obtain ⟨hc, hSh⟩ := plan_sourced scope hS (VerifiableInference.Desc.Key.beforeSharedPoint Pl)
  obtain ⟨pk, Al⟩ := alike_KU scope hS
  have hpp : (pKU Pl).place = piKUFull.place := by
    show _ = _
    rw [show (pKU Pl).place = ⟨2, none, 9, .K12⟩ from H2K.JointK.place_of_p12At _ _]
    decide +kernel
  obtain ⟨hQ, hcf, hfr, hroom, hwU, hwO⟩ :=
    fold_pub_at ⟨sharedPar Xs.chains (VerifiableInference.Desc.Key.beforeSharedPoint Pl), 0⟩ hc hSh Al
  obtain ⟨hbk, hties⟩ := fold_book_at hK
    ⟨sharedPar Xs.chains (VerifiableInference.Desc.Key.beforeSharedPoint Pl), 0⟩ hc hSh hpp
  have hU : Desc.K14.withU (sharedPar Xs.chains (VerifiableInference.Desc.Key.beforeSharedPoint Pl)).S =
      some (sentOf (sharedPar Xs.chains (VerifiableInference.Desc.Key.beforeSharedPoint Pl)).S) := by
    rw [hSh]
    exact withU_sentOf (by decide +kernel)
  have hSN : (sharedPar Xs.chains (VerifiableInference.Desc.Key.beforeSharedPoint Pl)).S.sharedSplitNeeded =
      true := by
    rw [hSh]
    decide +kernel
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8⟩ := lengths_eight _ _ b1 b2 b3 b4 b5 b6 b7 b8 hb8 hU hSN
  obtain ⟨dU, pU, dO, pO⟩ := ProofFile.Honest.K14.send_declares _ 0 b1 b2 b3 b4 b5 b6 b7 b8 hb8
  obtain ⟨d0, d1, d2, e, post, q0, q1, q2, eq⟩ := rounds_eight _ _ b1 b2 b3 b4 b5 b6 b7 b8 hb8 hU
  have hP : H2K.JointK.keySharedPre Xs.chains Pl =
      ((VerifiableInference.Desc.Key.sharedChain Xs.chains Pl).retype (Cl' := Claim)).first.asBare ::
        [b1, b2, b3, b4, b5, b6, b7, b8].map fun b => (b.retype (Cl' := Claim)).asBare := by
    unfold H2K.JointK.keySharedPre Desc.K14.blocksOr
    rw [hb8]
    rfl
  have hcutK := H2K.JointK.keyShared_cut Xs.chains Pl
  rw [hP] at hcutK
  have eU : (keyFileDescription Xs N Pl).shared.blocksInOrder = [((VerifiableInference.Desc.Key.sharedChain Xs.chains Pl).retype
                          (Cl' := Claim)).first.asBare, (b1.retype (Cl' := Claim)).asBare] ++ (b2.retype (Cl' := Claim)).asBare ::
      _ := hcutK
  have eO : (keyFileDescription Xs N Pl).shared.blocksInOrder = [((VerifiableInference.Desc.Key.sharedChain Xs.chains Pl).retype
                          (Cl' := Claim)).first.asBare, (b1.retype (Cl' := Claim)).asBare, (b2.retype (Cl' := Claim)).asBare,
                          (b3.retype (Cl' := Claim)).asBare, (b4.retype (Cl' := Claim)).asBare] ++
      (b5.retype (Cl' := Claim)).asBare :: _ := hcutK
  have hRounds : (H2K.JointK.keySharedPre Xs.chains Pl).flatMap (·.rounds) =
      [b1, b2, b3, b4, b5, b6, b7, b8].flatMap (·.rounds) := by
    rw [hP]
    rfl
  have L8 : ([b1, b2, b3, b4, b5, b6, b7, b8].flatMap (·.rounds)).length = 8 := by
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_append, n1, n2, n3, n4,
      n5, n6, n7, n8]
  have L4 : ([b1, b2, b3, b4].flatMap (·.rounds)).length = 4 := by
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_append, n1, n2, n3, n4]
  have L1 : ([b1].flatMap (·.rounds)).length = 1 := by
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, n1]
  have hsF : piKUFull.nums.first.map (fun o => ProofFile.Honest.srcOf 1 o.2) = [(1, 0), (1, 2)] := by
    decide +kernel
  have hpt : (pKU Pl).place = foldedTestPlace := H2K.JointK.place_of_p12At _ _
  refine onAtRun_folded scope hS T hρ hR hrun
    ⟨sharedPar Xs.chains (VerifiableInference.Desc.Key.beforeSharedPoint Pl), 0⟩
    [b1, b2, b3, b4, b5, b6, b7, b8] wt rd L hplace hrow hOn hg (by rw [hpt]; exact hties) d0 d1 d2 e post
    q0 q1 q2 (hRounds.trans eq) _ _ _ _ (b2.retype (Cl' := Claim)).asBare
    (b5.retype (Cl' := Claim)).asBare eU eO pU pO
    (by
      have e' : (b2.retype (Cl' := Claim)).asBare.place = sendPlace 2 := pU
      rw [e']
      exact hgU)
    (by
      have e' : (b5.retype (Cl' := Claim)).asBare.place = sendPlace 5 := pO
      rw [e']
      exact hgO)
    (ProofFile.Honest.K14.sendDeclared_like (c := b2) rfl rfl dU)
    (ProofFile.Honest.K14.sendDeclared_like (c := b5) rfl rfl dO)
    ?_ ?_ hbk hQ hcf hfr hroom hwU hwO ?_ ?_ hleft
  · rw [hRounds, L8]
    show ([b1].flatMap (·.rounds)).length + 2 ≤ 8
    rw [L1]
    decide
  · rw [hRounds, L8]
    show ([b1, b2, b3, b4].flatMap (·.rounds)).length + 2 ≤ 8
    rw [L4]
    decide
  · show 0 < ([b1].flatMap (·.rounds)).length
    rw [L1]
    exact Nat.zero_lt_one
  · rw [Al.nums, hsF]
    show [(1, 0), (1, 2)] = [(1, rootsOf ([b1].flatMap (·.rounds)) + 0),
      (1, rootsOf ([b1, b2, b3, b4].flatMap (·.rounds)) + 1)]
    have e0 : [b1].flatMap (·.rounds) = b1.rounds := by simp
    rw [e0, hr0, hr1]

end Join

end ProofFile.Honest.K12.Sim2

#print axioms ProofFile.Honest.K12.Sim2.fold_pub_full
#print axioms ProofFile.Honest.K12.Sim2.fold_book_full
#print axioms ProofFile.Honest.K12.Sim2.fold_pub_at
#print axioms ProofFile.Honest.K12.Sim2.fold_book_at
#print axioms ProofFile.Honest.K12.Sim2.plan_sourced
#print axioms ProofFile.Honest.K12.Sim2.onAtRun_folded_key
