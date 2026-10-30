-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/OfflineRangesLeftAtRun.lean: AT A RUN THAT HAS RETURNED, WHERE THE SECOND PART OF THE KEY FILE's PROXIMITY TEST ON
THE RANGES WAS CALLED: what is left of the condition at that part's entry (`LeftAtRanges`,
Johnson/Desc/ProofFile/Honest/K12/Sim2/RowRangesAtRun.lean: the two clauses on the asks) follows from ONE of its
clauses, said in front of the test: the rows taken in hold at the job's words. No thread, no stand, no truth of
the witness beyond that premise.

  `ReachedRanges`          a verifier's state in front of the test: the description's own fold over the first
                          chain's first fifteen sub-protocols, which read no column, accepts and ends in it
  `shape15_of_fold`        a reached state has the written shape `T15`
  `marks_of_fold`          a reached state bears the two marks on the open rows
  `SayInFrontOfRanges`     THE NAMED PREMISE: the clause `allSay` of `DataFront` (K12/ShapeAll.lean) at the job's own
                          plain rows
  `asks_reached_ranges`    `AsksInFront` (E2E/OfflineTestAsks.lean) at every input, front and family of coins at
                          which the job's state on entry is the seat's structure at a reached state
  `reached_ranges_at_run`  at the called second part the job's state on entry, at the input and the front as that
                          part lays it, is the seat's structure at a reached state
  `left_ranges_at_run`     the statement

What each clause stands on. The number of trees, `planB`, the eight clauses on the state on entry and the three on
the form of the prover's data: the written shape, which accepted folds keep (`shape_of_fold`), the two marks, which
accepted folds keep (`marks_of_pre`, E2E/KeyMarksThr.lean), and kernel lines at the written sizes
(`front_data_KR`, K12/FrontAtKey.lean). `allSay`: the premise.

Premises of `left_ranges_at_run`. In scope. hρ, hR, hrun: the challenges fit, `ready` and `runC` have returned. hg:
the prover's side at the place is the test's pair. hT: the book's ties. hc: the second part was called. hm: m is
the walk's state there. hsay. The stretches mem are free.

Limits. It moves all clauses but one off the debt and leaves that one. `SayInFrontOfRanges` reads the input and the
carried coins: it says that the multiplicities' words are true; no later law may take it as a hypothesis on a run and
then speak of the coins as sampled anew. The clause trees of the same condition is not treated here. Nothing on
completeness, on soundness or on what is hidden.
-/
import E2E.OfflineShapeOfFold
import E2E.OfflineTestAsks
import E2E.KeyRangesSeated
import Johnson.Desc.ProofFile.Honest.K12.CalledAtFirst
import Johnson.Desc.ProofFile.Honest.K12.Sim2.RowRangesAtRun

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

noncomputable section

namespace AtPublicFiles.OfflineRows
open ProofFile.Honest ProofFile.Honest.K12 ProofFile.Honest.K12.Light
open ProofFile.Honest.K12.Sim2 (LeftAtRanges simRanges five_at_test find_ranges facts_KRFull rest_KR
  first_KR_length dsKR)
open VerifiableInference.Desc (Block OpenedColumn Place foldBlocks)
open VerifiableInference.Desc.Key (Xi Source LaterPlaces FirstState descriptionFromSource)
open OnBytes.Means (AllSay layoutOf)
open OnBytes.Slice (GF rdE begun runRows)
open H2K.Member (piKRFull codesKeyFull nKRFull)
open H2K.JointK (keyFirstPre)
open AtPublicFiles.KeyBook (rngPlace fullFirst places_named)
open AtPublicFiles.KeyThread (rangesTestJob recRanges sentRanges place_sourced take15 pre_dry readsOf_dry
  length_of_cut take_of_cut sent_codes sent_msgs stages_KRJ)
open AtPublicFiles.KeyShape
open AtPublicFiles.AtFiles
open AtPublicFiles.AtFiles.Full
open VerifierAndGoals (PublicFiles InScope)

section Reached
variable {Z : PublicFiles} {Xs : Source} {N : H2U.PlaceNums} {Pl : LaterPlaces}

/-- **A state that the description's own accepted fold reaches in front of the test on the ranges**, at the
instance x. The fifteen sub-protocols in front read no column. -/
def ReachedRanges (Xs : Source) (N : H2U.PlaceNums) (Pl : LaterPlaces) (x : Xi) (rs : List Fmt.RoundView)
    (s : FirstState) : Prop :=
  foldBlocks 0 ((descriptionFromSource Xs N Pl).first.blocksInOrder.take 15) ((descriptionFromSource Xs N Pl).start₁ ((descriptionFromSource Xs N Pl).pub x)) rs
    [] = .ok (s, [], [])

/-- **A reached state has the written shape.** -/
theorem shape15_of_fold (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true) {x : Xi}
    {rs : List Fmt.RoundView} {s : FirstState} (h : ReachedRanges Xs N Pl x rs s) :
    sh₁B (pubOf Xs) CF s = T15 := by
  obtain ⟨hN, -, -, hlen, hsh0, -, hyes, -⟩ := first_of_sourced hs scope fun _ _ _ _ => true
  obtain ⟨bw, hw, he, ha, -⟩ := public_first_sourced hs scope
  have h6 := six_sourced hs scope
  have h15 := shape_of_fold (Z₁W (pubOf Xs) CF Xs.Y.D.1 Xs.Y.told.1 N fun _ _ _ _ => true) (ft := 0)
    (bs := (keyFileDescription Xs N Pl).first.blocksInOrder)
    (fun j => carries_whole₁ (pubOf Xs) CF Xs.Y.D.1 Xs.Y.told.1 N 0 _ bw hw he ha j) (a₀ := T0)
    (n := 19) (b := 15) (le_of_eq hlen.symm) (by decide) hyes
    ((start₁_shape (cs := CF) (N := N) (X := Xs) (P := Pl) _ ((descriptionFromSource Xs N Pl).pub x)).trans hsh0) h
  subst hN
  have q0 := entries_six Xs nKRFull Pl hs.named.plan h6 0 (by decide)
  have q1 := entries_six Xs nKRFull Pl hs.named.plan h6 1 (by decide)
  exact Except.ok.inj (h15.symm.trans (run15_six h6 _ _ _ q0 q1))

/-- **A reached state bears the two marks.** -/
theorem marks_of_fold (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true) {x : Xi}
    {rs : List Fmt.RoundView} {s : FirstState} (h : ReachedRanges Xs N Pl x rs s) : MarksAt s := by
  unfold ReachedRanges at h
  have e15 : (descriptionFromSource Xs N Pl).first.blocksInOrder.take 15 =
      keyFirstPre Xs.Y.k.oneTime Xs.Y.D.1 Xs.Y.told.1 Xs.set N := take15 scope hs.named
  rw [e15] at h
  exact marks_of_pre _ _ _ _ _ 0 h (plainAll_start _)

end Reached

section Asks
variable {Z : PublicFiles} {W₀ Rc : Type} (Xs : Source) (N : H2U.PlaceNums) (Pl : LaterPlaces)
  (entry : Local W₀ Rc Xi Unit → Nat → Nat → GF) (groups : List (List Nat)) (first : Nat)

/-- **THE NAMED PREMISE: the rows that the test takes in hold at the job's words.** The clause `allSay` of
`DataFront`, at the job's own plain rows. It reads the input and the coins. -/
def SayInFrontOfRanges (w : Local W₀ Rc Xi Unit) (fr : Front Unit) (C : TestCoins) : Prop :=
  ∀ G, ((rangesTestJob (X' := Unit) Xs N Pl entry groups first).rec₀ w fr).st.groups[
             ((rangesTestJob (X' := Unit) Xs N Pl entry groups first).rec₀ w fr).g]? = some G →
    AllSay rdE (begun ((rangesTestJob (X' := Unit) Xs N Pl entry groups first).rec₀ w fr).st
        ((rangesTestJob (X' := Unit) Xs N Pl entry groups first).rec₀ w fr).g G)
      (runRows ((rangesTestJob (X' := Unit) Xs N Pl entry groups first).rec₀ w fr).st G).toList
      (wordsAt (begun ((rangesTestJob (X' := Unit) Xs N Pl entry groups first).rec₀ w fr).st
          ((rangesTestJob (X' := Unit) Xs N Pl entry groups first).rec₀ w fr).g G)
        (layoutOf ((rangesTestJob (X' := Unit) Xs N Pl entry groups first).rec₀ w fr).st G)
        (plainOne (sentRanges Xs entry groups first) w (C.mem 0)
          ((rangesTestJob (X' := Unit) Xs N Pl entry groups first).first w fr C)))

/-- **What is asked in front of the test, where the job's state on entry is the seat's structure at a reached
state.** -/
theorem asks_reached_ranges (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true) {x : Xi}
    {rs : List Fmt.RoundView} {s : FirstState} (hr : ReachedRanges Xs N Pl x rs s)
    (w : Local W₀ Rc Xi Unit) (fr : Front Unit)
    (hen : recRanges (X' := Unit) Xs N Pl w fr = rangesState s) (C : TestCoins)
    (hsay : SayInFrontOfRanges Xs N Pl entry groups first w fr C) :
    AsksInFront (rangesTestJob (X' := Unit) Xs N Pl entry groups first) codesKeyFull 1 w fr C := by
  have hsh := shape15_of_fold hs scope hr
  have hM := marks_of_fold hs scope hr
  obtain rfl := nums_sourced hs scope
  have hTidy : VerifiableInference.Desc.Ground.Sh.stTidyB s.d.st = true :=
    (congrArg (·.2.tidy) hsh).trans loc15.2.2
  have hCl : ProofFile.Honest.Sh.claimsB (rangesState s) = true :=
    claims_of_gRng (pubOf Xs) Lk6.AtPlan.keyFull.codes nKRFull
      (by rw [hsh]; exact gRng_six (six_sourced hs scope)) hM
  have hcd := sent_codes Xs nKRFull Pl entry groups first hs scope
  have hms := sent_msgs Xs nKRFull Pl entry groups first hs scope
  obtain ⟨Dp, h1, F, a1, a2, a3⟩ := front_data_KR (X := Unit) (sentRanges Xs entry groups first)
    (recRanges Xs nKRFull Pl) w fr C hcd hms
    (by rw [hen]; exact thinSh_15 s hsh) (by rw [hen]; exact hTidy)
    (by rw [hen]; exact hM.1) (by rw [hen]; exact hCl)
  exact ⟨Dp, _, _, h1, planB_KR, frontAsksD_of _ _ _ F, a1, a2, a3, hsay⟩

end Asks

section Run
variable {Z : PublicFiles} {Xs : Source} {N : H2U.PlaceNums} {Pl : LaterPlaces} {W₀ Rc Ky X₀ : Type}
  {Bk : ProverCoinCounts} {P : Prover W₀ Rc Xi Ky Unit X₀ Unit} {w₀ : W₀} {rc : Rc} {x : Xi} {k : Coins Bk}
  {ρ : Draws} {R : Ready W₀ Rc Xi Ky Unit X₀ Unit} {r : RunC (keyFileDescription Xs N Pl)}

/-- **At a called part at the test's place, behind the first part's rounds, the job's state on entry is the
seat's structure at a reached state.** -/
theorem reached_ranges_at_run {V Pb : Type} (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true)
    (hR : ready (keyFileDescription Xs N Pl) Bk P w₀ rc x k = .ok R)
    (hrun : runC (keyFileDescription Xs N Pl) Bk P w₀ rc x k ρ = .ok r)
    (J : TestJob (Local W₀ Rc Xi Unit) Unit)
    (σ : Side (keyFileDescription Xs N Pl).S₁ (keyFileDescription Xs N Pl).Cl V (Local W₀ Rc Xi Unit) Unit Pb)
    (u : Member V (Local W₀ Rc Xi Unit) Unit Pb)
    (pre t : List (Block (keyFileDescription Xs N Pl).S₁ (keyFileDescription Xs N Pl).Cl))
    (S : StandsAt (keyFileDescription Xs N Pl).first.blocksInOrder R.first σ u pre t (firstLen J.p.nums.stages))
    (hc : r.called ⟨σ.block.place, u.number⟩ = true) (ha : σ.block.place = rngPlace) :
    ∃ (m : Mid (Local W₀ Rc Xi Unit) Unit) (s : FirstState) (rs : List Fmt.RoundView),
      midAtW (keyFileDescription Xs N Pl) Bk P w₀ rc x k ρ ⟨σ.block.place, u.number⟩ = .ok (some m) ∧
      ReachedRanges Xs N Pl x rs s ∧
      recRanges (X' := Unit) Xs N Pl m.st.input (restFront J m) = rangesState s := by
  obtain ⟨m, s, cols, more, rest, tr, hm, -, hin, -, hlen, -, hfold, hfill⟩ :=
    called_at_first hs.named.plan hR σ u pre t _ S hrun hc
  obtain ⟨r1, -, -⟩ := places_named scope hs.named
  have hplaces : (keyFileDescription Xs N Pl).first.blocksInOrder.map (·.place) = fullFirst.map (·.1) := by
    rw [← r1]
    unfold Johnson.RunOne.Sound.rowsOf
    rw [List.map_map]
    rfl
  have hpl15 : pre.length = 15 :=
    length_of_cut (fun b : Block (keyFileDescription Xs N Pl).S₁ (keyFileDescription Xs N Pl).Cl => b.place)
      (keyFileDescription Xs N Pl).first.blocksInOrder pre t σ.block (fullFirst.map (·.1)) rngPlace 15 S.cut
      hplaces (by decide) ha (by decide)
  have hpre : (keyFileDescription Xs N Pl).first.blocksInOrder.take 15 = pre := take_of_cut _ _ _ _ 15 S.cut hpl15
  have hdry : ∀ d ∈ pre.flatMap (·.rounds), AtPublicFiles.KeyThread.Dry d := by
    intro d hd
    rw [← hpre, take15 scope hs.named] at hd
    exact pre_dry _ _ _ _ _ d hd
  rw [readsOf_dry _ _ _ _ _ _ hdry] at hfill
  obtain rfl : ([] : List OpenedColumn) = cols := Except.ok.inj hfill
  have hseen : (restFront J m).seen.rounds = m.seen.take (pre.flatMap (·.rounds)).length := by
    show m.seen.take (m.seen.length - firstLen J.p.nums.stages) = _
    rw [hlen, Nat.add_sub_cancel]
  have hx : m.st.input.x = x := by rw [hin]
  have hreach : ReachedRanges Xs N Pl x (m.seen.take (pre.flatMap (·.rounds)).length) s := by
    unfold ReachedRanges
    show foldBlocks 0 ((keyFileDescription Xs N Pl).first.blocksInOrder.take 15) _ _ [] = _
    rw [hpre]
    exact hfold
  refine ⟨m, s, _, hm, hreach, ?_⟩
  unfold recRanges
  rw [hseen, hx]
  have hreach' : foldBlocks 0 ((AtPublicFiles.KeyThread.D Xs N Pl).first.blocksInOrder.take 15)
      ((AtPublicFiles.KeyThread.D Xs N Pl).start₁ ((AtPublicFiles.KeyThread.D Xs N Pl).pub x))
      (m.seen.take (pre.flatMap (·.rounds)).length) [] = .ok (s, [], []) := hreach
  rw [hreach']

/-- **What is left at the second part's entry, from the one clause on the words.** -/
theorem left_ranges_at_run (scope : InScope Z = true) (hs : KeySourced Z Xs N Pl)
    (hρ : ρ.due (keyFileDescription Xs N Pl) = true)
    (hR : ready (keyFileDescription Xs N Pl) Bk P w₀ rc x k = .ok R)
    (hrun : runC (keyFileDescription Xs N Pl) Bk P w₀ rc x k ρ = .ok r)
    (entry : Local W₀ Rc Xi Unit → Nat → Nat → GF) (groups : List (List Nat)) (first : Nat)
    (hg : (P.first.find? fun g => g.place == rngPlace) =
      some (proverSideOfProximityTest (rangesTestJob (X' := Unit) Xs N Pl entry groups first)))
    (hT : tiesB Bk rngPlace 1 = true) (hc : r.called ⟨rngPlace, 1⟩ = true)
    (m : Mid (Local W₀ Rc Xi Unit) Unit)
    (hm : midAtW (keyFileDescription Xs N Pl) Bk P w₀ rc x k ρ ⟨rngPlace, 1⟩ = .ok (some m))
    (mem : ℕ → K12.Stretch)
    (hsay : SayInFrontOfRanges Xs N Pl entry groups first m.st.input
      (restFront (rangesTestJob (X' := Unit) Xs N Pl entry groups first) m)
      (carriedCoins (rangesTestJob (X' := Unit) Xs N Pl entry groups first) mem)) :
    LeftAtRanges (rangesTestJob (X' := Unit) Xs N Pl entry groups first) codesKeyFull piKRFull.nums.first
      mem m := by
  have hJ : (rangesTestJob (X' := Unit) Xs N Pl entry groups first).p = piKRFull := place_sourced hs scope
  have hPR : (rangesTestJob (X' := Unit) Xs N Pl entry groups first).p.place = rngPlace := by
    rw [hJ]
    exact ProofFile.Honest.K12.Sim2.place_KR
  obtain ⟨b, hf, hbp, hr, hor⟩ := find_ranges scope hs.named
    (rangesTestJob (X' := Unit) Xs N Pl entry groups first) rfl
  have F : PlaceFacts (rangesTestJob (X' := Unit) Xs N Pl entry groups first).p dsKR := by
    rw [hJ]
    exact facts_KRFull
  have hpos : restLen (rangesTestJob (X' := Unit) Xs N Pl entry groups first).p.nums.stages ≠ 0 := by
    rw [hJ]
    exact rest_KR
  obtain ⟨σ, hσ, hσb⟩ : ∃ σ : Side (keyFileDescription Xs N Pl).S₁ (keyFileDescription Xs N Pl).Cl (Local W₀ Rc Xi Unit)
      (Local W₀ Rc Xi Unit) Unit Xi,
      testSide (keyFileDescription Xs N Pl).first.blocksInOrder (rangesTestJob (X' := Unit) Xs N Pl entry groups first)
        (simRanges Xs N Pl) [] = some σ ∧ σ.block = b := by
    refine ⟨⟨b, testPairs (rangesTestJob (X' := Unit) Xs N Pl entry groups first) (simRanges Xs N Pl),
      fallOf [] (rangesTestJob (X' := Unit) Xs N Pl entry groups first).p.place⟩, ?_, rfl⟩
    unfold testSide Side.seated
    show Option.map _ ((keyFileDescription Xs N Pl).first.blocksInOrder.find? fun b => b.place == _) = _
    rw [hf]
    rfl
  have hpl : σ.block.place = rngPlace := by rw [hσb, hbp, hPR]
  have hg' : (P.first.find? fun g => g.place == σ.block.place) =
      some (proverSideOfProximityTest (rangesTestJob (X' := Unit) Xs N Pl entry groups first)) := by
    rw [hpl]
    exact hg
  have hc₁ : r.called ⟨σ.block.place, 1⟩ = true := by
    rw [hpl]
    exact hc
  obtain ⟨pre, t, c, m₁, S, hm₁, -, -, F5⟩ := five_at_test hs.named.plan hρ hR
    (rangesTestJob (X' := Unit) Xs N Pl entry groups first) F (AtPublicFiles.KeyTest.sMsg, 1) rfl
    (fun w fr mem mem' hh => ProofFile.Honest.K12.rows_one _ _ _ w fr mem mem' hh) (simRanges Xs N Pl)
    hJ.symm rfl [] σ hσ b hf hbp hr hor hg' (by rw [hPR]; exact hT) hrun hc₁ hpos []
  obtain ⟨m₂, s, rs, hm₂, hreach, hen⟩ := reached_ranges_at_run hs scope hR hrun
    (rangesTestJob (X' := Unit) Xs N Pl entry groups first) σ _ pre t S hc₁ hpl
  obtain rfl : m₁ = m₂ := Option.some.inj (Except.ok.inj (hm₁.symm.trans hm₂))
  rw [hpl] at hm₁
  obtain rfl : m₁ = m := Option.some.inj (Except.ok.inj (hm₁.symm.trans hm))
  have hasks := asks_reached_ranges Xs N Pl entry groups first hs scope hreach m₁.st.input
    (restFront (rangesTestJob (X' := Unit) Xs N Pl entry groups first) m₁) hen
    (carriedCoins (rangesTestJob (X' := Unit) Xs N Pl entry groups first) mem) hsay
  obtain ⟨a, next, rest, hst, -⟩ :=
    stages_KRJ (rangesTestJob (X' := Unit) Xs N Pl entry groups first) hJ
  have hleft := left_of_front (rangesTestJob (X' := Unit) Xs N Pl entry groups first) codesKeyFull 1 mem m₁
    a next rest hst (by rw [hJ]; exact formPubB_KR) F5.heardFit hasks
  obtain ⟨Dp, cc, Rw, h1, hA, hD⟩ := hleft
  exact ⟨Dp, cc, Rw, h1.trans first_KR_length.symm, hA, hD⟩

end Run

end AtPublicFiles.OfflineRows

#print axioms AtPublicFiles.OfflineRows.shape15_of_fold
#print axioms AtPublicFiles.OfflineRows.marks_of_fold
#print axioms AtPublicFiles.OfflineRows.asks_reached_ranges
#print axioms AtPublicFiles.OfflineRows.reached_ranges_at_run
#print axioms AtPublicFiles.OfflineRows.left_ranges_at_run
