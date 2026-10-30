-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- K12's simulator: the request's own test at a run, from a stand of the last chain's thread.
/-
Johnson/Desc/ProofFile/Honest/K12/Sim2/ListWAtThread.lean: CONDITIONAL. Statements with their
proofs; no
definition.

Can the hypotheses be met together at a real run? NOT KNOWN: as at Sim2/ListWAtReturn.lean; and no
value
of the thread and its companion is laid here: they are letters.

What is here. `onAtRun_W_lines_at_return` (Sim2/ListWAtReturn.lean) WITH hlines GIVEN UP FOR WHAT
THE RULE
HANDS ITS PAYER: the invariant at the border in front of the test. Where the rule's invariant at
border
2 of the last chain is a thread's (hI₃), what is left at a called stand of the run follows from
sentences AT A STAND OF THAT THREAD, in the forms in which other files state them there (at the
stand's own front `frontOf m₀` and the coins `restCoins` of what the frame lends the unguarded
pair).

  `entry_is_the_stand`   THE STEP: a play of as many rounds as the test's first part has, from m₀:
  the
      second part's front at its end is `frontOf m₀`, field and all, and the input is m₀'s. General
      in
      the job.
  `says_at_carried`   `SaysAt` at `restCoins` of a lent part's coins is `SaysAt` at `carriedCoins`
  of its
      carried blocks: the two differ in a field that `SaysAt` does not read.
  `pair_lent_at_run`   where ready returns, the frame lends the UNGUARDED pair its coins at the
  test's
      place: no premise on the book beyond ready's yes.
  `lines_of_thread`   `LeftAtOwnLines` at the rule's own m and ca, from hI₃, hsix and hsays.
  `onAtRun_W_at_thread`   **the statement**, at the wide filling's return.

THE END IS `OnAtRun₃` ITSELF.

THE THREE NEW PREMISES. Th, Said: LETTERS, until the file of the letters lies.
  hI₃   T.I₃ 2 = ThrS Th Said 2: the rule's invariant at the border in front of the test is the
      thread's with its companion. That, at a
      value of `ThreadsP` that is made of named threads, it holds by rfl is not shown here.
  hsix   at every stand of the thread at border 2, at the run's coins: the three tests on the shape
  of
      the state on entry (`frontFiveB` · `manyFitsS` · `tsLenOf` = 3) and `FrontAsksD` at some plain
      data. TO THE LETTER THE END OF `lines_front_narrow` (K12/AtFile/WLine.lean, its `linesB`
      written
      out; read; not in this ground), which has it from the stronger head, the job's numbers, shapes
      and trees, `FieldAtW` and "the way in at the stand's state returns the job's state on entry".
  hsays   at every such stand and whatever the frame lends the pair: `SaysAt` at `frontOf m₀` and
      `restCoins`: the field saysAt of `OwnStand` (K12/AtFile/WStand.lean). A premise here; at
      the letters' names (the thread `thread₃`, the companion `said₃`, the job P.ownMany) it is
      `rowsSay_at_the_letters` (AtFullSide/K12/RowsSayAtTheLetters.lean), from the head at the
      return, the maker's return and the last chain's open letters P, WHICH ARE A PREMISE THERE
      (`openLast`, Honest/K12/AtFile/WAtTheLetters.lean, is a value of them); whether a stand of
      that thread is there is not said. `StandRest`.saysAt (WTable.lean) asks its like as a
      premise.
BOTH ARE ASKED AT THE RUN's OWN k ALONE, at every state, stand and environment of the thread there.

ALL THE PREMISES: h · hAr · hL · hP · T · hρ · hR · hrun · hM · hq · hT and the book's five · hI₃ ·
hsix ·
hsays.

Limits. Those of Sim2/ListWAtReturn.lean. K12/AtFile/WLine.lean and K12/AtFile/WStand.lean bear
"NOT IN FRONT OF A LAW OVER COINS": whoever
pays hsix or hsays by them and keeps their letters takes that label. That a stand is reached is the
rule's own hypothesis here (`InsideOf`), not a claim. Nothing on completeness, soundness or hiding.
No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim2.ListWAtReturn
import Johnson.Desc.ProofFile.Honest.K12.Sim2.ListWCame
import Johnson.Desc.ProofFile.Honest.K12.FirstPlayAtSecond
import Johnson.Desc.ProofFile.Honest.K12.PlayedTerm
import Johnson.Desc.ProofFile.Honest.Small.PlayRow
import Johnson.Desc.ProofFile.Honest.Gap
import Johnson.Desc.ProofFile.Honest.Thread.PaysLaw
import Johnson.Desc.ProofFile.Honest.Thread.Said

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

noncomputable section

namespace ProofFile.Honest.K12.Sim2
open VerifiableInference.Desc (Block Chain FileDescription Oracle Place KindName)
open VerifiableInference.Desc.K12 (T12)
open VerifiableInference.Desc.K12.Seat (enterOwn)
open H2K.Member (codesFull piWFull)
open ProofFile.Honest ProofFile.Honest.K12 ProofFile.Honest.K12.AtProof ProofFile.Honest.K12.Light
open ProofFile.Honest.K14 (jobOmega)

attribute [local irreducible] P2Law.ProofPlan.WP

/-- **THE STEP FROM A STAND TO THE SECOND PART's ENTRY.** ss, ds: the steps and the challenges of a
play from m₀ that returns y. hn: as many challenges as the test's first part has rounds. -/
theorem entry_is_the_stand {W : Type} (J : TestJob W Unit) (m₀ : Mid W Unit)
    (ss : List (Step W Unit)) (ds : List Fmt.Drawn) (y : List Played × Mid W Unit)
    (hp : play ss ds [] m₀ = .ok y) (hn : ds.length = firstLen J.p.nums.stages) :
    restFront J y.2 = frontOf m₀ ∧ y.2.st.input = m₀.st.input := by
  have a := play_mid ss ds [] m₀ y hp
  have b := play_heard ss ds [] m₀ y hp
  have c := play_opened ss ds [] m₀ y hp
  have l1 : y.1.length = ss.length := yields_length _ _ _ _ (play_yields _ _ _ _ _ hp)
  have l2 : ds.length = ss.length := Small.play_lengths ss ds [] m₀ y hp
  refine ⟨?_, a.1⟩
  have e1 : y.2.st.heard.take (y.2.st.heard.length - firstLen J.p.nums.stages) =
      m₀.st.heard := by
    rw [b, List.length_append, hn]
    simp
  have e2 : y.2.shown.front (firstLen J.p.nums.stages) = m₀.shown := by
    show (⟨y.2.seen.take (y.2.seen.length - firstLen J.p.nums.stages), y.2.opened⟩ : Seen) =
      ⟨m₀.seen, m₀.opened⟩
    rw [a.2.2, c, List.length_append, roundsOf_length, l1, ← l2, hn]
    simp
  show (⟨y.2.st.heard.take (y.2.st.heard.length - firstLen J.p.nums.stages), y.2.st.own,
    y.2.shown.front (firstLen J.p.nums.stages)⟩ : Front Unit) = ⟨m₀.st.heard, m₀.st.own, m₀.shown⟩
  rw [e1, e2]

/-- **`SaysAt` does not read the second part's own coins.** -/
theorem says_at_carried {W X : Type} (M : ManyJob W X) (w : W) (fr : Front X)
    (c : Handed ⟨0, dueRest M.toRun.toTest.p.nums.stages⟩ []
      (memberRuns M.toRun.toTest ⟨M.toRun.toTest.p.place, 1⟩ ++ [freshRun M.toRun.toTest]))
    (h : SaysAt M w fr (restCoins M.toRun.toTest c)) :
    SaysAt M w fr (carriedCoins M.toRun.toTest (stretches _ c.2.2)) := h

variable {W₀ : Type} {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl}

/-- CONDITIONAL on ready, the cut and hg. **Where ready returns the frame lends the unguarded
pair.** -/
theorem pair_lent_at_run {Rc Tr Ky X₀ Y : Type} {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : ProofFile.Inst} {k : Coins Bk}
    {R : Ready W₀ Rc ProofFile.Inst Ky Tr X₀ Y}
    (hR : ready (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Bk P w₀ rc x k = .ok R)
    (J : TestJob (Local W₀ Rc ProofFile.Inst Tr) Y)
    (pre t : List (Block (P5J.F0T OnBytes.secondHashFunction Zp Np cF).S₃ (P5J.F0T OnBytes.secondHashFunction Zp Np cF).Cl))
    (b : Block (P5J.F0T OnBytes.secondHashFunction Zp Np cF).S₃ (P5J.F0T OnBytes.secondHashFunction Zp Np cF).Cl)
    (hcut : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = pre ++ b :: t)
    (hg : (P.second.find? fun g => g.place == b.place) =
      some ((proverSideOfProximityTest J : Placed (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) Y).needsField))
          :
    ∃ c : RowCoins [(firstPart J : Part (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) Y),
        restPart J],
      lendRow Bk (Bk.rowsOf 2) (k.look 2) b.place
        [(firstPart J : Part (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) Y), restPart J] 0 =
        .ok c := by
  obtain ⟨c, -, -, hl, -, -, -⟩ := block_steps_at_second hR pre b t hcut _ hg
  have hl' : lendRow Bk (Bk.rowsOf 2) (k.look 2) b.place
      [(firstPart J : Part (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) Y).needsField,
        (restPart J : Part (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) Y).needsField] 0 =
      .ok c := hl
  rw [lend_guarded] at hl'
  exact ⟨c, hl'⟩

/-- CONDITIONAL on all its premises. **What is left at a called stand of the run, from a stand of
the
thread.** The letters are those that `onAtRun_W_lines_at_lot` hands its payer. -/
theorem lines_of_thread {Ky X₀ : Type} {Bk : ProverCoinCounts}
    {P : Prover W₀ IndexCommitterCoins ProofFile.Inst Ky Cells X₀ Unit} {w₀ : W₀} {rc : IndexCommitterCoins} {x : ProofFile.Inst}
    {k : Coins Bk} {R : Ready W₀ IndexCommitterCoins ProofFile.Inst Ky Cells X₀ Unit}
    (hR : ready (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Bk P w₀ rc x k = .ok R)
    (M : ManyJob (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit) (Js : SimJob ProofFile.Inst)
    (hg : (P.second.find? fun g => g.place == placeW) =
      some ((proverSideOfProximityTest M.toRun.toTest : Placed (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) (Local W₀ IndexCommitterCoins
                                 ProofFile.Inst Cells) Unit).needsField))
    (A₃ : ℕ → Coins Bk → (P5J.F0T OnBytes.secondHashFunction Zp Np cF).S₃ → Mid (Local W₀ IndexCommitterCoins ProofFile.Inst Cells)
        Unit → Env → Prop)
    (Th : Thread Bk (P5J.F0T OnBytes.secondHashFunction Zp Np cF).S₃ (P5J.F0T OnBytes.secondHashFunction Zp Np cF).Cl (Local
                                W₀ IndexCommitterCoins ProofFile.Inst Cells) (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit ProofFile.Inst)
    (Said : ℕ → Coins Bk → Mid (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit → Prop)
    (hI₃ : A₃ 2 = ThrS Th Said 2)
    (hsix : ∀ (st : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).S₃) (m₀ : Mid (Local W₀ IndexCommitterCoins ProofFile.Inst Cells)
                    Unit) (E₀ : Env), ThrS Th Said 2 k st m₀ E₀ →
      frontFiveB M.toRun.toTest.p codesFull (ProofFile.Honest.Sh.testSh (M.toRun.toTest.rec₀ m₀.st.input
                (frontOf m₀))) = true ∧
      manyFitsS M.p (M.mems.map (·.shape)) M.trees
        (ProofFile.Honest.Sh.thinOf (ProofFile.Honest.Sh.testSh (M.toRun.toTest.rec₀ m₀.st.input (frontOf m₀))))
            = true ∧
      tsLenOf M.toRun.toTest.p (ProofFile.Honest.Sh.thinOf (ProofFile.Honest.Sh.testSh (M.toRun.toTest.rec₀
                      m₀.st.input (frontOf m₀)))) = 3 ∧
      ∃ Dp, FrontAsksD M.toRun.toTest m₀.st.input (frontOf m₀) codesFull Dp)
    (hsays : ∀ (st : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).S₃) (m₀ : Mid (Local W₀ IndexCommitterCoins ProofFile.Inst Cells)
                    Unit) (E₀ : Env)
      (c : RowCoins [(firstPart M.toRun.toTest : Part (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) (Local W₀
                IndexCommitterCoins ProofFile.Inst Cells) Unit), restPart M.toRun.toTest]),
      ThrS Th Said 2 k st m₀ E₀ →
      lendRow Bk (Bk.rowsOf 2) (k.look 2) placeW
        [(firstPart M.toRun.toTest : Part (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) (Local W₀ IndexCommitterCoins ProofFile.Inst
                  Cells) Unit), restPart M.toRun.toTest] 0 = .ok c →
      SaysAt M m₀.st.input (frontOf m₀) (restCoins M.toRun.toTest c.2.1))
    (m : Mid (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit)
    (ca : CsAll (restMember (V := Local W₀ IndexCommitterCoins ProofFile.Inst Cells) M.toRun.toTest Js).part.carries)
    (σ : Side (P5J.F0T OnBytes.secondHashFunction Zp Np cF).S₃ (P5J.F0T OnBytes.secondHashFunction Zp Np cF).Cl (Local W₀
                                IndexCommitterCoins ProofFile.Inst Cells) (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit ProofFile.Inst)
    (pre' t' pre t : List (Block (P5J.F0T OnBytes.secondHashFunction Zp Np cF).S₃ (P5J.F0T OnBytes.secondHashFunction Zp Np
                    cF).Cl))
    (hcut : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = pre' ++ σ.block :: t')
    (hσ₀ : Side.seated (P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder placeW (guardRow (testPairs
                             M.toRun.toTest Js)) [] = some σ)
    (S : StandsAt (P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder R.second σ (restMember
                             M.toRun.toTest Js).guarded pre t
      (firstLen M.toRun.toTest.p.nums.stages)) (E : Env)
    (hin : InsideOf .own Bk 2 P.second σ.block (A₃ pre'.length) (σ.roundsTo 1) k m E)
    (hca : carriedAt Bk k 2 ⟨placeW, 1⟩ (restMember (V := Local W₀ IndexCommitterCoins ProofFile.Inst Cells)
        M.toRun.toTest Js).part = .ok ca) :
    LeftAtOwnLines M codesFull (stretches _ ca) m := by
  have hσp : σ.block.place = placeW := by
    obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.1 hσ₀
    simpa using List.find?_some hb
  have h2 : pre'.length = 2 := by
    rw [front_of_own_test_is_two hcut hσp]
    rfl
  rw [h2, hI₃] at hin
  obtain ⟨st, m₀, E₀, l, ds, y, hA, -, hd, hp', em, -⟩ := hin
  have hrow : σ.row = guardRow (testPairs M.toRun.toTest Js) := by
    obtain ⟨b, -, e⟩ := Option.map_eq_some_iff.1 hσ₀
    rw [← e]
  have hn : σ.roundsTo 1 = firstLen M.toRun.toTest.p.nums.stages := by
    unfold Side.roundsTo
    rw [hrow]
    show (firstPart M.toRun.toTest : Part (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) (Local W₀ IndexCommitterCoins ProofFile.Inst
              Cells) Unit).needsField.moves.length + 0 = _
    rw [Nat.add_zero, needsField_length, first_moves_len]
  have hdl : ds.length = firstLen M.toRun.toTest.p.nums.stages := by
    have e := drawsFit_length _ _ hd
    rw [e, List.length_take, hn]
    have := S.le
    omega
  obtain ⟨eF, eI⟩ := entry_is_the_stand M.toRun.toTest m₀ _ ds y hp' hdl
  subst em
  obtain ⟨c, hl⟩ := pair_lent_at_run hR M.toRun.toTest pre' t' σ.block hcut (by rw [hσp]; exact hg)
  rw [hσp] at hl
  have h1 := (lendRow_cons_ok (lendRow_cons_ok hl).2).1
  have eca : ca = c.2.1.2.2 := by
    unfold carriedAt at hca
    have h1' : lendPart Bk (Bk.rowsOf 2) (k.look 2) ⟨placeW, 1⟩
        (restMember (V := Local W₀ IndexCommitterCoins ProofFile.Inst Cells) M.toRun.toTest Js).part = .ok c.2.1 := h1
    rw [h1'] at hca
    exact (Except.ok.inj hca).symm
  subst eca
  obtain ⟨s5, sF, sC, Dp, sFr⟩ := hsix st m₀ E₀ hA
  have sS := says_at_carried M _ _ _ (hsays st m₀ E₀ c hA hl)
  exact ⟨by rw [eI, eF]; exact s5, by rw [eI, eF]; exact sF, by rw [eI, eF]; exact sC,
    by rw [eI, eF]; exact sFr.tidy, by rw [eI, eF]; exact sFr.denseRows,
    by rw [eI, eF]; exact sFr.claims, by rw [eI, eF]; exact sS⟩

/-- CONDITIONAL on all its premises. **The clause of the rule at the list that bears the lot's row,
at
the wide filling's return, from a stand of the last chain's thread.** -/
theorem onAtRun_W_at_thread {x₀ : VerifiableInference.Desc.First.Look.Place}
    (h : P5J.AtMgA OnBytes.secondHashFunction Z D₀ r₀ Zp Np cF x₀) (I : WiderIn W₀)
    (S' : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) {Ar : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
    (hAr : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction S' O) =
      .ok Ar)
    (hL : secondW (X := Unit) I OnBytes.secondHashFunction S' O Ar.Z Ar.G ≠ []) {Bk : ProverCoinCounts}
    {H : Prover W₀ IndexCommitterCoins ProofFile.Inst OnBytes.TableKey Cells Unit Unit}
    {G : Sides (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Bk W₀ IndexCommitterCoins OnBytes.TableKey Cells Unit Unit}
    (hP : G.prover H = Ar.H) {w₀ : W₀} {rc : IndexCommitterCoins}
    {x : ProofFile.Inst} {k : Coins Bk} {ρ : Draws}
    {R : Ready W₀ IndexCommitterCoins ProofFile.Inst OnBytes.TableKey Cells Unit Unit}
    {r : RunC (P5J.F0T OnBytes.secondHashFunction Zp Np cF)}
    (T : ThreadsP (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Bk (G.prover H) w₀ rc x k R)
    (hρ : ρ.due (P5J.F0T OnBytes.secondHashFunction Zp Np cF) = true)
    (hR : ready (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Bk (G.prover H) w₀ rc x k = .ok R)
    (hrun : runC (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Bk (G.prover H) w₀ rc x k ρ = .ok r)
    (M : ManyJob (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit)
    (hM : jobRealW S' (P5J.F0T OnBytes.secondHashFunction Zp Np cF) enterOwn O.pile (K1.lotNo OnBytes.secondHashFunction Zp)
      (fun w => ⟨w.trace, I.weights Zp w.w₀, w.rc⟩) (fun w => I.weights Zp w.w₀)
      (fun P w => randAt P w.rc) Zp Ar.G = some M)
    (L : Lettered Bk (P5J.F0T OnBytes.secondHashFunction Zp Np cF).S₃ (P5J.F0T OnBytes.secondHashFunction Zp Np cF).Cl
      (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit ProofFile.Inst)
    (hq : L.bare = rowAtW Face.own OnBytes.secondHashFunction Zp Np cF M.toRun.toTest)
    -- on the book
    (hT : tiesB Bk placeW M.toRun.toTest.members.length = true)
    (hbkI : k1CutFits Bk ⟨placeW, 1⟩ 0 senderI PIw rideIw 4 = true)
    (hbkW : k1CutFits Bk ⟨placeW, 1⟩ 1 senderW PWw rideWw 0 = true)
    (hbkF : k1CutFits Bk ⟨placeW, 1⟩ 3 senderW PWw rideWw 1 = true)
    (hbkO : Light.cutFits Bk ⟨placeW, 1⟩ 2 senderO (jobOmega (⟨VerifiableInference.Desc.K1.qAt Zp
        Np, 0⟩ : K14.SendPub)) 0 = true)
    (hnotO : ∀ r ∈ Bk.first, r.1 ≠ senderO)
    -- the rule's invariant in front of the test is a thread's; two sentences at its stands
    (Th : Thread Bk (P5J.F0T OnBytes.secondHashFunction Zp Np cF).S₃ (P5J.F0T OnBytes.secondHashFunction Zp Np cF).Cl (Local
                                W₀ IndexCommitterCoins ProofFile.Inst Cells) (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit ProofFile.Inst)
    (Said : ℕ → Coins Bk → Mid (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit → Prop)
    (hI₃ : T.I₃ 2 = ThrS Th Said 2)
    (hsix : ∀ (st : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).S₃) (m₀ : Mid (Local W₀ IndexCommitterCoins ProofFile.Inst Cells)
                    Unit) (E₀ : Env), ThrS Th Said 2 k st m₀ E₀ →
      frontFiveB M.toRun.toTest.p codesFull (ProofFile.Honest.Sh.testSh (M.toRun.toTest.rec₀ m₀.st.input
                (frontOf m₀))) = true ∧
      manyFitsS M.p (M.mems.map (·.shape)) M.trees
        (ProofFile.Honest.Sh.thinOf (ProofFile.Honest.Sh.testSh (M.toRun.toTest.rec₀ m₀.st.input (frontOf m₀))))
            = true ∧
      tsLenOf M.toRun.toTest.p (ProofFile.Honest.Sh.thinOf (ProofFile.Honest.Sh.testSh (M.toRun.toTest.rec₀
                      m₀.st.input (frontOf m₀)))) = 3 ∧
      ∃ Dp, FrontAsksD M.toRun.toTest m₀.st.input (frontOf m₀) codesFull Dp)
    (hsays : ∀ (st : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).S₃) (m₀ : Mid (Local W₀ IndexCommitterCoins ProofFile.Inst Cells)
                    Unit) (E₀ : Env)
      (c : RowCoins [(firstPart M.toRun.toTest : Part (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) (Local W₀
                IndexCommitterCoins ProofFile.Inst Cells) Unit), restPart M.toRun.toTest]),
      ThrS Th Said 2 k st m₀ E₀ →
      lendRow Bk (Bk.rowsOf 2) (k.look 2) placeW
        [(firstPart M.toRun.toTest : Part (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) (Local W₀ IndexCommitterCoins ProofFile.Inst
                  Cells) Unit), restPart M.toRun.toTest] 0 = .ok c →
      SaysAt M m₀.st.input (frontOf m₀) (restCoins M.toRun.toTest c.2.1)) :
    OnAtRun₃ T ρ r L := by
  have h' := h.toAtMg
  -- the test's own half, as the search finds it
  have hg : ((G.prover H).second.find? fun g => g.place == placeW) =
      some ((proverSideOfProximityTest M.toRun.toTest : Placed (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) (Local W₀ IndexCommitterCoins
                                 ProofFile.Inst Cells) Unit).needsField) := by
    obtain ⟨hZ0, -, -⟩ := atPure_ok hAr
    have eZ : Ar.Z = Zp := Except.ok.inj (hZ0.symm.trans h'.laid.pub)
    obtain ⟨N, c, M', hN', hc', hM', -, -, -, hg⟩ :=
      own_test_found_of_laid I OnBytes.secondHashFunction S' O hAr hL
    rw [eZ] at hN' hc' hM'
    obtain rfl : N = Np := Except.ok.inj (hN'.symm.trans h'.laid.places)
    obtain rfl : c = cF := Except.ok.inj (hc'.symm.trans h'.laid.chain)
    have eMM : M' = M := Option.some.inj (hM'.symm.trans hM)
    rw [eMM] at hg
    rw [hP]
    exact hg
  have hLp : L.place = placeW := by
    obtain ⟨⟨Fo, hF, hp⟩, -, -⟩ := real_job_letters _ _ _ _ _ _ _ _ _ _ hM
    obtain rfl : Fo = fourOf Np := Option.some.inj (hF.symm.trans (four_at_head h'))
    exact (isListAtW_of_row L _ hp hq).place
  refine onAtRun_W_lines_at_return h I S' O hAr hL hP T hρ hR hrun M hM L hq hT hbkI hbkW hbkF hbkO
    hnotO ?_
  intro m ca σ pre' t' pre t hcut hσ₀ S hin hseen hc hca hmid hown F5 hdr hfr'
  rw [hLp] at hca
  exact lines_of_thread hR M (simAtW OnBytes.secondHashFunction Zp Np cF) hg T.I₃ Th Said hI₃ hsix hsays m ca σ
      pre' t' pre t hcut hσ₀ S _
    hin hca

end ProofFile.Honest.K12.Sim2

#print axioms ProofFile.Honest.K12.Sim2.entry_is_the_stand
#print axioms ProofFile.Honest.K12.Sim2.says_at_carried
#print axioms ProofFile.Honest.K12.Sim2.pair_lent_at_run
#print axioms ProofFile.Honest.K12.Sim2.lines_of_thread
#print axioms ProofFile.Honest.K12.Sim2.onAtRun_W_at_thread
