-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/OfflineOmegaLeft.lean: AT THE KEY FILE's TEST ON G_omega (⟨2, –, 10⟩): THE CLAUSE asks OF THE CONDITION AT THE ENTRY OF THE SECOND
PART (∃ Dp cc R, Dp.ts.length = 3 ∧ `ShapeAsksO` ∧ `DataAsks`, at the written codes), FROM ONE NAMED SENTENCE ON HIDDEN DATA.

Why no run's fact on the verifier's state is spent. The job's state on entry is `doorOmegaF`
(Johnson/Desc/ProofFile/Honest/K12/DoorsByShape.lean), whose fall-back is made of the plan's shape: its shape is one public term, and
the three tests that read its rows hold, AT EVERY INPUT AND FRONT (`shape_doorOmegaF`, `three_doorOmegaF`), whether the
fold of the sub-protocols in front has returned or not. Of a run the form of the challenges heard alone is read.

  `writtenCodes`, `omegaForm_written`, `omegaBat_written`, `omegaEarly_written`, `omegaTail_written`   closed lines, by the kernel
  `laterDraw`            a written challenge for a round
  `omega_shape`          `OwnTestShape` (E2E/OfflineTestLeftOwn.lean) at the job `jobKO` at the written values, at every eight that the
                         written parameters make, every reader, input and front
  `omega_left`           the clause asks at every input, front, coins and list heard that the first part's rounds can draw
  `omega_left_at_run`    the same AT A RUN's OWN VALUES, in the form in which `owedAt_shared_at` (E2E/OfflineOwedChains.lean) asks
                         On: at every carried block that the book gives the part and every state that the frame
                         returns at its address

WHAT STAYS: `RowsSayInFront` (E2E/OfflineTestLeftOwn.lean) at the run's own input, front and carried coins: that the rows which
the group under test has taken in say true things of the members' words. It is a premise here, inside the form: asked
at the same carried block and state at which the clause is given. Where the state on entry is the fall-back nothing
says that it can be met.

The closed lines on the shape (`five_O`, `three_O`, `ts_O`, `many_O`, `plan_U`) stand in E2E/KeyTenLinesKernel.lean and
E2E/KeyTenPubKernel.lean.

Limits. At the written sizes. It pays neither the clause door nor the clause trees. The state on entry is the job's own
letter: that it is the verifier's is the clause door's. Nothing on any property.
-/
import E2E.OfflineOmegaFive
import E2E.OfflineTestLeftOwn
import E2E.KeyTenLinesKernel
import E2E.KeyTenPubKernel
import Johnson.Desc.ProofFile.Honest.K12.DoorsByShape
import Johnson.Desc.ProofFile.Honest.K12.FitSharedAt
import Johnson.Desc.ProofFile.Honest.K12.Own.PlanOwn

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

noncomputable section

namespace AtPublicFiles.OfflineRows
open ProofFile.Honest ProofFile.Honest.K12 ProofFile.Honest.K12.Own
open ProofFile.Honest.K12.Light (ManyJob shape_doorOmegaF three_doorOmegaF Three sentOf shapes_atOmega)
open ProofFile.Honest.K12.Light.KeyDoorUClosed (shapeOm fallOm bareO msO planU threeL five_O three_O ts_O many_O
  plan_U)
open ProofFile.Honest.K14 (SendPub)
open OnBytes (TableKey)
open VerifiableInference.Desc (Place Block)
open VerifiableInference.Desc.K12 (P12 T12 proximityTestKind guardedProximityTestParts)
open VerifiableInference.Desc.Key (Source LaterPlaces)
open _root_.Desc.K14 (St blocks blocksOr withU)
open H2K.Pub (sgOf)
open H2K.Member (piKUFull piKOFull codesKeyFull)
open H2K.JointK (laidOf)
open Johnson.Prover.Link (batCut)
open AtPublicFiles.AtFiles (KeySourced keyFileDescription)
open AtPublicFiles.AtFiles.Full (QK PF plan_eight)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub foldedTestPlace omegaTestPlace)
open AtPublicFiles.KeyFile (KeyInst KeyParts keyProver)
open AtPublicFiles.KeyLay (jobKO proverSideOfTestOnOmega)
open AtPublicFiles.KeyNineClosed (place_full)
open VerifierAndGoals (PublicFiles InScope)

/-! ## Closed lines -/

theorem writtenCodes : QK.codes = codesKeyFull := by decide +kernel

theorem omegaForm_written : formPubB piKOFull = true := by decide +kernel

theorem omegaBat_written : batCut (((laidOf piKOFull).take 1).map (·.1)) = true := by decide +kernel

theorem omegaEarly_written : piKOFull.early = true := by decide +kernel

/-- A written challenge for a round. -/
def laterDraw (d : Fmt.DeclaredRound) : Fmt.Drawn :=
  { elems := List.replicate d.entry.drawE (1, 0, 0), poss := List.replicate d.entry.poss 0,
    trits := List.replicate d.entry.trits 0, digest := none }

/-- The rounds behind the first fold can draw the written challenges. -/
theorem omegaTail_written :
    drawsFit (((laidOf piKOFull).drop (firstLen piKOFull.nums.stages)).map (·.1))
      ((((laidOf piKOFull).drop (firstLen piKOFull.nums.stages)).map (·.1)).map laterDraw) = true := by
  decide +kernel

theorem some_getD {α : Type} {o : Option α} (h : o.isSome = true) (d : α) : o = some (o.getD d) := by
  cases o with
  | none => cases h
  | some a => rfl

/-! ## The shape, at every input and front -/

section Shape
variable {W₀ Rc X₀ : Type}

/-- **The tests on the shape of the state on entry and on the plan, at the key file's test on G_omega.** -/
theorem omega_shape (bs : List (Block St Unit)) (hb : blocks QK = some bs)
    (weights : Common W₀ Rc TableKey → Weights) (rand : Common W₀ Rc TableKey → TableRand)
    (w : Common W₀ Rc TableKey) (fr : Front X₀) :
    ∃ a next rest, OwnTestShape (jobKO (X := X₀) ⟨QK, 0⟩ piKUFull piKOFull bs weights rand) w fr codesKeyFull 3
      a next rest := by
  have hall : ∀ x ∈ planU, x = true := fun x hx => List.all_eq_true.1 plan_U x hx
  have hS : QK.S.sharedSplitNeeded = true := writtenShape_splits
  have hwS : (withU QK.S).isSome = true := hall _ (by unfold planU; simp)
  have hM : QK.S.masksAhead = true := hall _ (by unfold planU; simp)
  have hl : QK.codes.lengthsOk = true := hall _ (by unfold planU; simp)
  have hpU : (proximityTestKind guardedProximityTestParts piKUFull : Block T12 Unit).planOk = true := hall _ (by unfold planU; simp)
  have hw : withU QK.S = some (sentOf QK.S) := some_getD hwS _
  have hp : ∀ b ∈ bs, b.planOk = true := by
    have e : blocksOr QK = bs := by
      unfold blocksOr
      rw [hb]
      rfl
    rw [← e]
    exact plan_eight
  have hN : ProofFile.Honest.Sh.testSh ((jobKO (X := X₀) ⟨QK, 0⟩ piKUFull piKOFull bs weights rand).rec₀ w fr) =
      shapeOm :=
    shape_doorOmegaF QK bs hb hS (sentOf QK.S) hw piKUFull hpU
      (fun w : Common W₀ Rc TableKey => w.key) Light.colsOpened w fr
  have h3 := three_O
  simp only [threeL, List.cons.injEq, and_true] at h3
  have hT : Three ((jobKO (X := X₀) ⟨QK, 0⟩ piKUFull piKOFull bs weights rand).rec₀ w fr) :=
    three_doorOmegaF QK bs hb hp hS hM (sentOf QK.S) hw hl piKUFull hpU ⟨h3.1, h3.2.1, h3.2.2⟩
      (fun w : Common W₀ Rc TableKey => w.key) Light.colsOpened w fr
  obtain ⟨a, next, rest, hst⟩ := two_in_front (l := piKOFull.nums.stages) omegaStages_two
  have hfl : firstLen piKOFull.nums.stages = 2 + a.k := by
    rw [hst]
    rfl
  refine ⟨a, next, rest, ⟨hst, omegaEarly_written, formPub_of_B _ _ _ _ hst omegaForm_written,
    planOB_KO_full, omegaBat_written, ?_, ?_, ?_, ?_, hT.tidy, hT.plain, hT.claims⟩⟩
  · rw [← hfl]
    exact omegaEnough_written
  · rw [hN, ← writtenCodes]
    exact five_O
  · rw [hN]
    exact ts_O
  · rw [hN]
    exact many_O

/-- **The clause asks at every input, front and coins, at every list heard that the first part's rounds can
draw**, from the one sentence on hidden data. -/
theorem omega_left (bs : List (Block St Unit)) (hb : blocks QK = some bs)
    (weights : Common W₀ Rc TableKey → Weights) (rand : Common W₀ Rc TableKey → TableRand)
    (w : Common W₀ Rc TableKey) (fr : Front X₀) (C : TestCoins) (hs : List Fmt.Drawn)
    (hd : drawsFit (((laidOf piKOFull).take (firstLen piKOFull.nums.stages)).map (·.1)) hs = true)
    (say : RowsSayInFront (jobKO (X := X₀) ⟨QK, 0⟩ piKUFull piKOFull bs weights rand) w fr C) :
    ∃ Dp cc R, Dp.ts.length = 3 ∧
      ShapeAsksO (jobKO (X := X₀) ⟨QK, 0⟩ piKUFull piKOFull bs weights rand).toRun.toTest w fr C (byNo hs)
        codesKeyFull Dp ∧
      DataAsks (jobKO (X := X₀) ⟨QK, 0⟩ piKUFull piKOFull bs weights rand).toRun.toTest w fr C (byNo hs) Dp cc
        R := by
  obtain ⟨a, next, rest, T⟩ := omega_shape (X₀ := X₀) bs hb weights rand w fr
  have hfl : firstLen piKOFull.nums.stages = 2 + a.k := by
    rw [show piKOFull.nums.stages = a :: next :: rest from T.stages]
    rfl
  exact left_of_shape_own _ w fr C codesKeyFull 3 a next rest T hs _ (by rw [← hfl]; exact hd)
    (by rw [← hfl]; exact omegaTail_written) say

end Shape

/-! ## At a run -/

section Run
variable {W₀ Rc Wk : Type} {Z : PublicFiles} {Xs : Source} {N : H2U.PlaceNums} {Pl : LaterPlaces}

/-- **THE CLAUSE asks AT A RUN, at the second part of the test on G_omega**: at every carried block and every
state that the frame returns at the part's address, where the part is called: from the one sentence on hidden
data at that block and state. Js: any simulators' job: nothing is read of it. -/
theorem omega_left_at_run (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true) {K₀ : KeyPub}
    (hK : fullPub = some K₀) {Bk : ProverCoinCounts} (hB : Bk = keyBook K₀) (K : KeyParts W₀ Rc Unit Unit Wk)
    (hsp : K.lin.S.sharedSplitNeeded = true) (hU : K.onU.place = foldedTestPlace) (A : SendPub)
    (hA : A = ⟨QK, 0⟩) (pU pO : P12) (hpU : pU = H2U.proximityTestParametersAt foldedTestPlace PF.U)
    (hpO : pO = H2U.proximityTestParametersAt omegaTestPlace (PF.O.getD PF.U)) (bs : List (Block St Unit))
    (hb : blocks QK = some bs) (weights : Common W₀ Rc TableKey → Weights)
    (rand : Common W₀ Rc TableKey → TableRand) (hO : K.onOmega = proverSideOfTestOnOmega A pU pO bs weights rand)
    (S : OfflineSimulators)
    (c : ConditionsByChain (keyFileDescription Xs N Pl) Bk W₀ Rc TableKey Unit Unit Unit)
    (H : Prover W₀ Rc KeyInst TableKey Unit Unit Unit) (Js : SimJob TableKey) {w₀ : W₀} {rc : Rc}
    {x : KeyInst} {k : Coins Bk} {ρ : Draws} {r : RunC (keyFileDescription Xs N Pl)}
    (due : ρ.due (keyFileDescription Xs N Pl) = true)
    (h : runC (keyFileDescription Xs N Pl) Bk ((offlineRows (keyFileDescription Xs N Pl) Bk K S c).prover H) w₀ rc x k ρ =
      .ok r) :
    ∀ L ∈ (offlineRows (keyFileDescription Xs N Pl) Bk K S c).shared, L.place = omegaTestPlace →
      ∀ σ, L.side (keyFileDescription Xs N Pl).shared.blocksInOrder = some σ → ∀ u ∈ σ.members, u.number = 1 →
      r.called ⟨L.place, u.number⟩ = true → ∀ ca m,
      carriedAt Bk k 1 ⟨L.place, u.number⟩ u.part = .ok ca →
      orRefused (midSharedAtW (keyFileDescription Xs N Pl) Bk ((offlineRows (keyFileDescription Xs N Pl) Bk K S c).prover H)
        w₀ rc x k ρ ⟨L.place, u.number⟩) = .ok m →
      RowsSayInFront (jobKO (X := Unit) A pU pO bs weights rand) m.st.input
        (restFront (jobKO (X := Unit) A pU pO bs weights rand).toRun.toTest m)
        (carriedCoins (jobKO (X := Unit) A pU pO bs weights rand).toRun.toTest (stretches _ ca)) →
      ∃ Dp cc R, Dp.ts.length = 3 ∧
        ShapeAsksO (jobKO (X := Unit) A pU pO bs weights rand).toRun.toTest m.st.input
          (restFront (jobKO (X := Unit) A pU pO bs weights rand).toRun.toTest m)
          (carriedCoins (jobKO (X := Unit) A pU pO bs weights rand).toRun.toTest (stretches _ ca))
          (heardIn (jobKO (X := Unit) A pU pO bs weights rand).toRun.toTest m) codesKeyFull Dp ∧
        DataAsks (jobKO (X := Unit) A pU pO bs weights rand).toRun.toTest m.st.input
          (restFront (jobKO (X := Unit) A pU pO bs weights rand).toRun.toTest m)
          (carriedCoins (jobKO (X := Unit) A pU pO bs weights rand).toRun.toTest (stretches _ ca))
          (heardIn (jobKO (X := Unit) A pU pO bs weights rand).toRun.toTest m) Dp cc R := by
  intro L hL hp σ hσ u hu hn hc ca m hca hm say
  have five := omega_five_at_run_own hs scope hK hB K hsp hU A hA pU pO hpO bs weights rand hO S c H Js due h
    [] L hL hp σ hσ u hu hn hc ca m hca hm
  have hfit := five.heardFit
  have e1 : pU = piKUFull := hpU.trans place_full
  have e2 : pO = piKOFull := hpO.trans omegaNumbers_written
  subst hA
  subst e1
  subst e2
  exact omega_left bs hb weights rand _ _ _ _ hfit say

end Run

end AtPublicFiles.OfflineRows

#print axioms AtPublicFiles.OfflineRows.writtenCodes
#print axioms AtPublicFiles.OfflineRows.omegaForm_written
#print axioms AtPublicFiles.OfflineRows.omegaBat_written
#print axioms AtPublicFiles.OfflineRows.omegaEarly_written
#print axioms AtPublicFiles.OfflineRows.omegaTail_written
#print axioms AtPublicFiles.OfflineRows.omega_shape
#print axioms AtPublicFiles.OfflineRows.omega_left
#print axioms AtPublicFiles.OfflineRows.omega_left_at_run
