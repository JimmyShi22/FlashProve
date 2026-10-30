-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/OfflineFoldedLeft.lean: at the key file's proximity test on G_u (place ⟨2, –, 9⟩): what is left of the condition at the entry of the second part (LeftAtFolded,
Johnson/Desc/ProofFile/Honest/K12/Sim2/RowFoldedAtRun.lean: the two clauses on the asks) FROM ONE NAMED SENTENCE ON HIDDEN DATA, SaysInFront
(E2E/OfflineSayAtRun.lean); and so the row's owedAt at a returned run from SayAtRun.

Why no fact of a run on the verifier's state is spent. The job's state on entry is doorUF (Johnson/Desc/ProofFile/Honest/K12/DoorsByShape.lean), whose fall-back is
made of the plan's shape: its shape is one public term and the three tests that read its rows hold AT EVERY INPUT AND FRONT (shape_doorUF, three_doorUF),
whether the fold of the sub-protocols in front has returned or not. Of a run the form of the challenges heard alone is read.

  folded_asks            AsksInFront (E2E/OfflineTestAsks.lean) at the job at the written values, at every eight that the written parameters make, every reader,
                         input, front and family of coins, from SaysInFront at the job's own plain rows
  folded_left            LeftAtFolded at every state whose last challenges the first part's rounds can draw; the job's letters are tied to the written values
                         by equations
  letters_written        in scope the senders' own letters K.send, pKU Pl, bsOf K are the written values
  heard_at_run           at the called second part the state that the frame returns has heard challenges of the declared form
  left_of_say            LeftAtRun (E2E/OfflineFoldedAtRows.lean) from SayAtRun
  owed_folded_of_say     THE STATEMENT: at every row of the muted offline rows' shared list at the place: owedAt, from SayAtRun

The closed lines on the shape (front_U, many_U, ts_U, three_U) stand in E2E/KeyDoorUClosedKernel.lean; planB_KU in …/K12/Sim2/RowFolded.lean.

WHAT STAYS: SayAtRun: that the rows which the group under test has taken in say true things of the members' words, at the run's own input, front and carried coins.
Where the state on entry is the fall-back nothing says that it can be met. Beside it: T : ThreadsP, a letter; FoldedLetters; H.storedWords = stOf K; four
equations on K; KeySourced, InScope, fullPub = some K₀, ready, due, silent, the run has returned.
Limits. At the written sizes. SayAtRun reads the input and the carried coins: no later law may take it as a hypothesis on a run and then speak of the coins as
sampled anew. Nothing on soundness, completeness, hiding or binding.
-/
import E2E.OfflineFoldedAtRows
import E2E.OfflineSayAtRun
import E2E.OfflineTestAsks
import E2E.KeyDoorUClosedKernel
import E2E.KeyNineClosed
import Johnson.Desc.ProofFile.Honest.K12.ManyFitsAt

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace AtPublicFiles.OfflineRows.Folded
open ProofFile.Honest ProofFile.Honest.K12 ProofFile.Honest.K12.Light ProofFile.Honest.K12.Sim2
open ProofFile.Honest.K12.Light.KeyDoorUClosed (shapeU fallUK threeL front_U many_U ts_U three_U)
open ProofFile.Honest.K14 (SendPub)
open OnBytes (TableKey)
open VerifiableInference.Desc (Block Place)
open VerifiableInference.Desc.K12 (P12 T12)
open VerifiableInference.Desc.Key (Xi Source LaterPlaces)
open _root_.Desc.K14 (St blocks blocksOr withU)
open H2K.Member (codesKeyFull piKUFull)
open AtPublicFiles.AtFiles (KeySourced keyFileDescription)
open AtPublicFiles.AtFiles.Full (QK PF par_sourced later_sourced plan_eight)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub foldedTestPlace omegaTestPlace)
open AtPublicFiles.KeyFile (KeyInst KeyParts keyProver)
open AtPublicFiles.KeySharedThread (parKey)
open AtPublicFiles.KeyLay (jobKU proverSideOfTestOnU bsOf stOf wtOf rdOf)
open AtPublicFiles.KeyValueHolds (place_p12At)

/-! ## 1 In front of the test, at every input and front -/

section Front
variable {W₀ Rc X₀ : Type}

/-- **What is asked in front of the test on G_u, from the one sentence on hidden data.** -/
theorem folded_asks (bs : List (Block St Unit)) (hb : blocks QK = some bs)
    (st : W₀ → Rc → ℕ → ℕ → Option (List UInt64)) (wt : Common W₀ Rc TableKey → Weights)
    (rd : Common W₀ Rc TableKey → TableRand) (w : Common W₀ Rc TableKey) (fr : Front X₀)
    (C : TestCoins)
    (say : SaysInFront (jobKU (X := X₀) ⟨QK, 0⟩ piKUFull bs st wt rd).toRun.toTest w fr
      (plainMany (jobKU (X := X₀) ⟨QK, 0⟩ piKUFull bs st wt rd) w fr C)) :
    AsksInFront (jobKU (X := X₀) ⟨QK, 0⟩ piKUFull bs st wt rd).toRun.toTest codesKeyFull 2 w fr C := by
  have hS : QK.S.sharedSplitNeeded = true := by decide +kernel
  have hw : withU QK.S = some (sentOf QK.S) := withU_sentOf (by decide +kernel)
  have hcd : QK.codes = codesKeyFull := by decide +kernel
  have hp : ∀ b ∈ bs, b.planOk = true := by
    have e : blocksOr QK = bs := by
      unfold blocksOr
      rw [hb]
      rfl
    rw [← e]
    exact plan_eight
  have hN : ProofFile.Honest.Sh.testSh ((jobKU (X := X₀) ⟨QK, 0⟩ piKUFull bs st wt rd).rec₀ w fr) = shapeU :=
    shape_doorUF QK bs hb hS (sentOf QK.S) hw (fun w : Common W₀ Rc TableKey => w.key)
      (fun (w : Common W₀ Rc TableKey) (fr : Front X₀) => colsLoc QK (st w.w₀ w.rc) fr.seen.rounds) w fr
  have h3 := three_U
  simp only [threeL, List.cons.injEq, and_true] at h3
  have hT : Three ((jobKU (X := X₀) ⟨QK, 0⟩ piKUFull bs st wt rd).rec₀ w fr) :=
    three_doorUF QK bs hb hp hS (sentOf QK.S) hw ⟨h3.1, h3.2.1, h3.2.2⟩
      (fun w : Common W₀ Rc TableKey => w.key)
      (fun (w : Common W₀ Rc TableKey) (fr : Front X₀) => colsLoc QK (st w.w₀ w.rc) fr.seen.rounds) w fr
  have h5 : frontFiveB piKUFull codesKeyFull
      (ProofFile.Honest.Sh.testSh ((jobKU (X := X₀) ⟨QK, 0⟩ piKUFull bs st wt rd).rec₀ w fr)) = true := by
    rw [hN, ← hcd]
    exact front_U
  obtain ⟨Dp, S⟩ := frontAsks_of_five (jobKU (X := X₀) ⟨QK, 0⟩ piKUFull bs st wt rd).toRun.toTest w fr
    codesKeyFull rfl h5 hT.tidy hT.plain hT.claims
  have hn : Dp.ts.length = 2 := by
    rw [ts_of_front (jobKU (X := X₀) ⟨QK, 0⟩ piKUFull bs st wt rd).toRun.toTest w fr codesKeyFull Dp rfl
      h5 S]
    show tsLenOf piKUFull (ProofFile.Honest.Sh.thinOf
      (ProofFile.Honest.Sh.testSh ((jobKU (X := X₀) ⟨QK, 0⟩ piKUFull bs st wt rd).rec₀ w fr))) = 2
    rw [hN]
    exact ts_U
  obtain ⟨d1, d2, d3⟩ := dataThree_of_front (jobKU (X := X₀) ⟨QK, 0⟩ piKUFull bs st wt rd) w fr
    codesKeyFull Dp rfl h5 S (by rw [hN]; exact many_U) C
  exact ⟨Dp, _, _, hn, planB_KU, frontAsksD_of _ _ _ S, ⟨d1, d2, d3, say⟩⟩

/-- **What is left at a state behind the first part**, the job's letters tied to the written values by equations. -/
theorem folded_left (A : SendPub) (hA : A = ⟨QK, 0⟩) (p : P12) (hp : p = piKUFull)
    (bs : List (Block St Unit)) (hb : blocks QK = some bs)
    (st : W₀ → Rc → ℕ → ℕ → Option (List UInt64)) (wt : Common W₀ Rc TableKey → Weights)
    (rd : Common W₀ Rc TableKey → TableRand) (mem : ℕ → ProofFile.Honest.K12.Stretch)
    (m : Mid (Common W₀ Rc TableKey) X₀)
    (hfit : drawsFit (((H2K.JointK.laidOf p).take (firstLen p.nums.stages)).map (·.1))
      (m.st.lately (firstLen p.nums.stages)) = true)
    (say : SaysInFront (jobKU (X := X₀) A p bs st wt rd).toRun.toTest m.st.input
      (restFront (jobKU (X := X₀) A p bs st wt rd).toRun.toTest m)
      (plainMany (jobKU (X := X₀) A p bs st wt rd) m.st.input
        (restFront (jobKU (X := X₀) A p bs st wt rd).toRun.toTest m)
        (carriedCoins (jobKU (X := X₀) A p bs st wt rd).toRun.toTest mem))) :
    LeftAtFolded (jobKU (X := X₀) A p bs st wt rd).toRun.toTest codesKeyFull p.nums.first mem m := by
  subst hA
  subst hp
  obtain ⟨a, next, rest, hst⟩ : ∃ a next rest, piKUFull.nums.stages = a :: next :: rest := by
    have h2 : 2 ≤ piKUFull.nums.stages.length := by decide +kernel
    match piKUFull.nums.stages, h2 with
    | a :: b :: r, _ => exact ⟨a, b, r, rfl⟩
  have hF : formPubB piKUFull = true := by decide +kernel
  exact left_of_front (jobKU (X := X₀) ⟨QK, 0⟩ piKUFull bs st wt rd).toRun.toTest codesKeyFull 2 mem m a
    next rest hst hF hfit (folded_asks bs hb st wt rd _ _ _ say)

end Front

/-! ## 2 At a run -/

section Run
variable {Z : VerifierAndGoals.PublicFiles} {Xs : Source} {N : H2U.PlaceNums} {Pl : LaterPlaces} {W₀ Rc X₀ Y Wk : Type}

/-- In scope the senders' own letters are the written values. -/
theorem letters_written (scope : VerifierAndGoals.InScope Z = true) (hS : KeySourced Z Xs N Pl)
    (K : KeyParts W₀ Rc X₀ Y Wk) (hsend : K.send = ⟨parKey Xs Pl, 0⟩) :
    K.send = ⟨QK, 0⟩ ∧ pKU Pl = piKUFull ∧ blocks QK = some (bsOf K) := by
  have e : parKey Xs Pl = QK := par_sourced hS scope
  have hA : K.send = ⟨QK, 0⟩ := by rw [hsend, e]
  refine ⟨hA, ?_, ?_⟩
  · rw [later_sourced hS scope]
    exact AtPublicFiles.KeyNineClosed.place_full
  · obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, hb8⟩ := eight_sourced scope hS
    have hb8' : blocks (parKey Xs Pl) = some [b1, b2, b3, b4, b5, b6, b7, b8] := hb8
    rw [e] at hb8'
    unfold bsOf
    rw [hA]
    show blocks QK = some ((blocks QK).getD [])
    rw [hb8']
    rfl

/-- **At the called second part the state that the frame returns has heard challenges of the declared form.** -/
theorem heard_at_run (scope : VerifierAndGoals.InScope Z = true) (hS : KeySourced Z Xs N Pl) {K₀ : KeyPub}
    (hK : fullPub = some K₀) (K : KeyParts W₀ Rc X₀ Y Wk)
    (hsp : K.lin.S.sharedSplitNeeded = true)
    (hU : K.onU = proverSideOfTestOnU K.send (pKU Pl) (bsOf K) (stOf K) (wtOf K) (rdOf K))
    (hOp : K.onOmega.place = omegaTestPlace) {P : Prover W₀ Rc Xi TableKey Unit X₀ Y}
    (hsh : P.shared = (keyProver K).shared)
    {w₀ : W₀} {rc : Rc} {x : Xi} {k : Coins (keyBook K₀)} {ρ : Draws}
    {R : Ready W₀ Rc Xi TableKey Unit X₀ Y} {r : RunC (keyFileDescription Xs N Pl)}
    (hρ : ρ.due (keyFileDescription Xs N Pl) = true)
    (hR : ready (keyFileDescription Xs N Pl) (keyBook K₀) P w₀ rc x k = .ok R)
    (hrun : runC (keyFileDescription Xs N Pl) (keyBook K₀) P w₀ rc x k ρ = .ok r)
    (hc : r.called ⟨foldedTestPlace, 1⟩ = true) (m : ProofFile.Honest.Mid (Common W₀ Rc TableKey) X₀)
    (hm : midSharedAtW (keyFileDescription Xs N Pl) (keyBook K₀) P w₀ rc x k ρ ⟨foldedTestPlace, 1⟩ = .ok (some m)) :
    drawsFit (((H2K.JointK.laidOf (pKU Pl)).take (firstLen (pKU Pl).nums.stages)).map (·.1))
      (m.st.lately (firstLen (pKU Pl).nums.stages)) = true := by
  obtain ⟨pk, Al⟩ := alike_KU scope hS
  obtain ⟨b, hf, hbp, hr, hor⟩ := find_folded scope hS.named (foldedJob K Pl) rfl
  have hpt : (pKU Pl).place = foldedTestPlace := H2K.JointK.place_of_p12At _ _
  have hUp : K.onU.place = foldedTestPlace := by
    rw [hU]
    exact place_p12At _ _
  obtain ⟨σ, hσ⟩ : ∃ σ : Side (keyFileDescription Xs N Pl).S₂ (keyFileDescription Xs N Pl).Cl Empty (Common W₀ Rc TableKey) X₀ TableKey,
      testSide (keyFileDescription Xs N Pl).shared.blocksInOrder (foldedJob K Pl) (foldedSim K Pl) [] = some σ := by
    unfold testSide Side.seated
    rw [hf]
    exact ⟨_, rfl⟩
  have hblk : σ.block = b := by
    have h₁ := hσ
    unfold testSide Side.seated at h₁
    obtain ⟨b', hb', e'⟩ := Option.map_eq_some_iff.1 h₁
    have : b' = b := Option.some.inj (hb'.symm.trans hf)
    rw [← e', this]
  have hσp : σ.block.place = foldedTestPlace := by
    rw [hblk, hbp]
    exact hpt
  have hg : (P.shared.find? fun g => g.place == σ.block.place) = some (proverSideOfProximityTest (foldedJob K Pl)) := by
    rw [hσp, hsh, folded_found K hsp hUp hOp, hU]
    rfl
  obtain ⟨hcd, hSh⟩ := plan_sourced scope hS (VerifiableInference.Desc.Key.beforeSharedPoint Pl)
  have hpp : (pKU Pl).place = piKUFull.place := by
    rw [hpt]
    decide +kernel
  have hT : tiesB (keyBook K₀) (pKU Pl).place 2 = true := by
    rw [hpt]
    exact (fold_book_at hK ⟨parKey Xs Pl, 0⟩ hcd hSh hpp).2
  have hpos : restLen (foldedJob K Pl).p.nums.stages ≠ 0 := by
    show restLen (pKU Pl).nums.stages ≠ 0
    rw [congrArg (·.stages) Al.nums]
    exact rest_KU
  obtain ⟨pre, t, c, m₁, -, hm₁, -, -, F5⟩ := five_at_test₂ hS.named.plan hρ hR (foldedJob K Pl)
    (facts_KU facts_KUFull _ pk Al) _ rfl
    (fun s w fr mem mem' hh => rowsMu_many _ s w fr mem mem' hh) (foldedSim K Pl) rfl rfl [] σ hσ b hf hbp
    hr hor hg hT hrun (by rw [hσp]; exact hc) hpos []
  rw [hσp] at hm₁
  obtain rfl : m₁ = m := Option.some.inj (Except.ok.inj (hm₁.symm.trans hm))
  exact F5.heardFit

/-- **What is left at one run, from the one sentence on hidden data at that run.** -/
theorem left_of_say (scope : VerifierAndGoals.InScope Z = true) (hS : KeySourced Z Xs N Pl) {K₀ : KeyPub}
    (hK : fullPub = some K₀) (K : KeyParts W₀ Rc X₀ Y Wk) (hsend : K.send = ⟨parKey Xs Pl, 0⟩)
    (hsp : K.lin.S.sharedSplitNeeded = true)
    (hU : K.onU = proverSideOfTestOnU K.send (pKU Pl) (bsOf K) (stOf K) (wtOf K) (rdOf K))
    (hOp : K.onOmega.place = omegaTestPlace) {P : Prover W₀ Rc Xi TableKey Unit X₀ Y}
    (hsh : P.shared = (keyProver K).shared)
    {w₀ : W₀} {rc : Rc} {x : Xi} {k : Coins (keyBook K₀)} {ρ : Draws}
    {R : Ready W₀ Rc Xi TableKey Unit X₀ Y} {r : RunC (keyFileDescription Xs N Pl)}
    (hρ : ρ.due (keyFileDescription Xs N Pl) = true)
    (hR : ready (keyFileDescription Xs N Pl) (keyBook K₀) P w₀ rc x k = .ok R)
    (hrun : runC (keyFileDescription Xs N Pl) (keyBook K₀) P w₀ rc x k ρ = .ok r)
    (say : SayAtRun Empty (foldedJob K Pl)
      (plainMany (jobKU (X := X₀) K.send (pKU Pl) (bsOf K) (stOf K) (wtOf K) (rdOf K))) k 1
      foldedTestPlace r.called (midSharedAtW (keyFileDescription Xs N Pl) (keyBook K₀) P w₀ rc x k ρ)) :
    LeftAtRun (Xs := Xs) (N := N) (Pl := Pl) K P w₀ rc x k ρ r.called := by
  obtain ⟨hA, hpw, hb⟩ := letters_written scope hS K hsend
  intro hcl m ca hm hca
  exact folded_left K.send hA (pKU Pl) hpw (bsOf K) hb (stOf K) (wtOf K) (rdOf K) (stretches _ ca) m
    (heard_at_run scope hS hK K hsp hU hOp hsh hρ hR hrun hcl m hm) (say hcl m ca hm hca)

/-- **owedAt at the row of the test on G_u, at the muted offline rows, from the one sentence on hidden data at the run.** -/
theorem owed_folded_of_say (scope : VerifierAndGoals.InScope Z = true) (hS : KeySourced Z Xs N Pl) {K₀ : KeyPub}
    (hK : fullPub = some K₀) {Bk : ProverCoinCounts} (hB : Bk = keyBook K₀) (K : KeyParts W₀ Rc X₀ Y Wk)
    (hsend : K.send = ⟨parKey Xs Pl, 0⟩) (hsp : K.lin.S.sharedSplitNeeded = true)
    (hU : K.onU = proverSideOfTestOnU K.send (pKU Pl) (bsOf K) (stOf K) (wtOf K) (rdOf K))
    (hOp : K.onOmega.place = omegaTestPlace) (S : OfflineSimulators)
    (c : ConditionsByChain (keyFileDescription Xs N Pl) Bk W₀ Rc TableKey Unit X₀ Y)
    (hc : FoldedLetters (Xs := Xs) (N := N) (Pl := Pl) K S c)
    (H : Prover W₀ Rc KeyInst TableKey Unit X₀ Y) (hst : H.storedWords = stOf K)
    {w₀ : W₀} {rc : Rc} {x : Xi} {k : Coins Bk} {ρ : Draws}
    {R : Ready W₀ Rc Xi TableKey Unit X₀ Y} {r : RunC (keyFileDescription Xs N Pl)}
    (T : ThreadsP (keyFileDescription Xs N Pl) Bk
      ((offlineRows (keyFileDescription Xs N Pl) Bk K S c).mute.prover H) w₀ rc x k R)
    (hρ : ρ.due (keyFileDescription Xs N Pl) = true)
    (hsil : silentAt (keyFileDescription Xs N Pl)
      ((offlineRows (keyFileDescription Xs N Pl) Bk K S c).mute.prover H) w₀ rc x ρ = none)
    (hR : ready (keyFileDescription Xs N Pl) Bk
      ((offlineRows (keyFileDescription Xs N Pl) Bk K S c).mute.prover H) w₀ rc x k = .ok R)
    (hrun : runC (keyFileDescription Xs N Pl) Bk
      ((offlineRows (keyFileDescription Xs N Pl) Bk K S c).mute.prover H) w₀ rc x k ρ = .ok r)
    (say : SayAtRun Empty (foldedJob K Pl)
      (plainMany (jobKU (X := X₀) K.send (pKU Pl) (bsOf K) (stOf K) (wtOf K) (rdOf K))) k 1
      foldedTestPlace r.called
      (midSharedAtW (keyFileDescription Xs N Pl) Bk ((offlineRows (keyFileDescription Xs N Pl) Bk K S c).mute.prover H) w₀ rc x
        k ρ)) :
    ∀ L ∈ (offlineRows (keyFileDescription Xs N Pl) Bk K S c).mute.shared, L.place = foldedTestPlace →
      L.owedAt (keyFileDescription Xs N Pl).shared.blocksInOrder k 1
        (fun a => orRefused (midSharedAtW (keyFileDescription Xs N Pl) Bk
          ((offlineRows (keyFileDescription Xs N Pl) Bk K S c).mute.prover H) w₀ rc x k ρ a)) r.run
        (storedShown (H.storedWords w₀ rc) r.run.storedAsked) r.called := by
  subst hB
  have hsh : ((offlineRows (keyFileDescription Xs N Pl) (keyBook K₀) K S c).mute.prover H).shared =
      (keyProver K).shared := by
    rw [prover_mute, offlineRows_prover_at]
  exact owed_folded_at_rows scope hS hK rfl K hsend hsp hU hOp S c hc H hst T hρ hsil hR hrun
    (left_of_say scope hS hK K hsend hsp hU hOp hsh hρ hR hrun say)

end Run

end AtPublicFiles.OfflineRows.Folded

#print axioms AtPublicFiles.OfflineRows.Folded.folded_asks
#print axioms AtPublicFiles.OfflineRows.Folded.folded_left
#print axioms AtPublicFiles.OfflineRows.Folded.letters_written
#print axioms AtPublicFiles.OfflineRows.Folded.heard_at_run
#print axioms AtPublicFiles.OfflineRows.Folded.left_of_say
#print axioms AtPublicFiles.OfflineRows.Folded.owed_folded_of_say
