-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/Part4/ColumnsOfJobW.lean: THE LAST CHAIN's PROXIMITY TEST (the
kind K12, the place W): AT ANY JOB ON THREE MEMBERS OF WHICH THE FIRST TWO ARE MESSAGES OF TWO
SENDINGS, UNDER PUBLIC PREMISES, WHERE THE TEST's CARRIED COINS ARE THE TWO SENDERS' OWN, NUMBER BY
NUMBER, THE COLUMNS OF THE JOB's TREES 0 AND 1 ARE THE TWO SENDERS' OWN WRITTEN SYMBOLS AT THE
SENDERS' OWN COINS; AND THE PUBLIC PREMISES HOLD AT THE JOB jobW AT THE WRITTEN SENDINGS AND THE
WRITTEN PLACE's STAGES.

WHAT IT IS NOT.
  * THAT THE COINS ARE THE SAME IS A PREMISE, five times (heldIndexF, heldIndexE, heldWF, heldWE,
    heldFresh), each in the form in which another author's laws have it at the maker's book
    (members_held, fresh_held, AtFullSide/K12/HeldAtHeadW.lean). No book, no lending, no run and no
    thread stands here.
  * It does not say what a sender's table is, nor that a thread's table shows these symbols: that
    is the sendings' authors' half. So it is not yet "the job's trees are the tables taken over".
  * The senders' data is read at the test's own front (fr): that it is the data which the sender
    read when it sent is not said here.
  * The public premises are shown at the written sendings parGF and parWF, W's written ride and the
    written place's stages: that a job at a public part has these is a premise (four equations).
  * The closed test is an evaluation in Lean's kernel at the typed sizes; it is public.
  * It is no statement on a tree's depth.
  * Nothing on completeness, soundness or what a proof hides.

WHAT IT IS. Five definitions; eight theorems.

  blocksApartB, sentFitsAtB, sentFitsB   closed tests: two blocks of rows do not overlap; all public
                            premises of ColumnsOfSentMembers.lean and FreshTableOfASending.lean at
                            two sendings and the written place's first stage; the same at the
                            written sendings
  writtenRideOfW            W's sending's ride at the written parameters (the term that another
                            author's AtFullSide/K12/HeldAtHeadW.lean calls rideWF)
  SentMembersFit            these premises, as propositions
  blocksApart               what blocksApartB says
  sentFitsAtTheTypedSizes   the test says yes at the typed sizes: an evaluation in Lean's kernel
  sentFitsRefusesASwap      a control: with the two sendings swapped it says no at some typed size.
                            It shows that the conjunction can say no, not that each of its
                            seventeen clauses can
  sentFitsReadsThePlan      the test reads the shared plan's codes and shape alone
  sentMembersFitOfTheTest   from the test's yes to the propositions
  membersOfJobW             the job's three members, written out
  columnsOfTwoSentMembers   **the statement**, at any job on three members of that make, under the
                            public premises
  sentMembersFitAtJobW      the public premises at jobW, from the test's yes and four equations

CALLED. firstTreeIsTheSenders, secondTreeIsTheSenders (ColumnsOfSentMembers.lean);
freshTableIsTheSendersRows, freshTailsAreTheSenders (FreshTableOfASending.lean); rowsR_csAt
(K12/AtProof/JobW.lean); code_of_same (K12/TreeIsColumn.lean).
-/
import Johnson.Desc.ProofFile.Honest.K12.Part4.ColumnsOfSentMembers
import Johnson.Desc.ProofFile.Honest.K12.Part4.FreshTableOfASending

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Part4
open OnBytes.Slice (GE codeOf)
open Johnson.Prover.Send (Rows shapeAt mainSyms maskSyms)
open Fmt.M1 (Stage)
open VerifiableInference.Desc (K1.Par)
open VerifiableInference.Desc.K1 (parGF parWF qFull)
open VerifiableInference.Desc.K12 (P12 T12)
open H2K.Member (piWFull)
open ProofFile.Honest.K14 (SendPub jobOmega Ask)
open ProofFile.Honest.K12.Light (ManyJob Mem firstsOf sameCode code_of_same memOfSending)
open ProofFile.Honest.K12.AtProof (shapesW jobW memK1 csAt rowsR_csAt senderI senderW senderO)

/-! ## 1 The closed test -/

/-- Two blocks of rows do not overlap: the first is empty, or one ends where the other begins. -/
def blocksApartB (aFirst aRows bFirst bRows : ℕ) : Bool :=
  aRows == 0 || decide (aFirst + aRows ≤ bFirst) || decide (bFirst + bRows ≤ aFirst)

/-- What blocksApartB says. -/
theorem blocksApart {aFirst aRows bFirst bRows : ℕ}
    (apart : blocksApartB aFirst aRows bFirst bRows = true) :
    ∀ r < bRows, ¬ (aFirst ≤ bFirst + r ∧ bFirst + r < aFirst + aRows) := by
  intro r below ⟨from_, to_⟩
  unfold blocksApartB at apart
  simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at apart
  omega

/-- W's sending's ride at the written parameters. -/
abbrev writtenRideOfW : ℕ → Option K1.Ride := K1.rideOf (K1.wFold qFull.lin)

/-- **The public premises, as propositions.** s: the stage. PI, PW: the two sendings. rideW: W's
ride. f0, f1: the first rows of the two members' blocks. -/
structure SentMembersFit (s : Stage) (PI PW : K1.Par) (rideW : ℕ → Option K1.Ride)
    (f0 f1 : Option ℕ × Option ℕ) : Prop where
  indexMessage : PI.sent.size - 1 < PI.sent.size
  wMessages : 1 < PW.sent.size
  indexMasks : MaskBlockFits s PI (PI.sent.size - 1) (f0.2.getD 0)
  wMain : MainBlockFits s PW 0 (f1.1.getD 0)
  wMask : MaskBlockFits s PW 0 (f1.2.getD 0)
  clearMain : ∀ r < (shapeAt PW 0).mainRows, ¬ (f0.1.getD 0 ≤ f1.1.getD 0 + r ∧
    f1.1.getD 0 + r < f0.1.getD 0 + (shapeAt PI (PI.sent.size - 1)).mainRows)
  clearMask : ∀ r < (shapeAt PW 0).maskRows, ¬ (f0.2.getD 0 ≤ f1.2.getD 0 + r ∧
    f1.2.getD 0 + r < f0.2.getD 0 + (shapeAt PI (PI.sent.size - 1)).maskRows)
  fresh : RidesAtTheStage s PW rideW 1

/-- **The test**, at two sendings and the written place's first stage. A: the shared sendings'
public data, of which Omega's shape is read. -/
def sentFitsAtB (PI PW : K1.Par) (A : SendPub) : Bool :=
  let fs := firstsOf (shapesW PI PW ((jobOmega A).Q.sent.getD 0 default).shape)
  let s := piWFull.nums.stages.headD default
  let f0 := fs.getD 0 (none, none)
  let f1 := fs.getD 1 (none, none)
  let sI := shapeAt PI (PI.sent.size - 1)
  decide (PI.sent.size - 1 < PI.sent.size) && decide (1 < PW.sent.size) &&
    decide (f0.2.getD 0 + sI.maskRows ≤ 2 ^ s.h) &&
    sameCode (PI.codes.mask.getD sI.maskCode default) s.Z &&
    decide (s.h ≤ s.k) && decide (f1.1.getD 0 + (shapeAt PW 0).mainRows ≤ 2 ^ s.k) &&
    sameCode (PW.codes.base.getD (shapeAt PW 0).code default) s.C &&
    ((shapeAt PW 0).mainDeg == 1 || (shapeAt PW 0).mainDeg == 3) &&
    decide (f1.2.getD 0 + (shapeAt PW 0).maskRows ≤ 2 ^ s.h) &&
    sameCode (PW.codes.mask.getD (shapeAt PW 0).maskCode default) s.Z &&
    blocksApartB (f0.1.getD 0) sI.mainRows (f1.1.getD 0) (shapeAt PW 0).mainRows &&
    blocksApartB (f0.2.getD 0) sI.maskRows (f1.2.getD 0) (shapeAt PW 0).maskRows &&
    (writtenRideOfW 1 == some ⟨s.k, s.h⟩) && decide (2 * s.k + 1 ≤ s.h + s.Z.l) &&
    ((shapeAt PW 1).mainRows == 0) && ((shapeAt PW 1).maskRows == 2 ^ s.h) &&
    sameCode (PW.codes.mask.getD (shapeAt PW 1).maskCode default) s.Z

/-- The test at the written sendings. -/
def sentFitsB (A : SendPub) : Bool := sentFitsAtB parGF parWF A

set_option maxRecDepth 1000000 in
/-- **The test says yes at the typed sizes.** An evaluation in Lean's kernel. -/
theorem sentFitsAtTheTypedSizes : (VerifiableInference.Desc.K1.realSized.all fun y =>
    sentFitsB (ProofFile.Honest.K12.Light.planOf y.2 y.1.shape)) = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- A control. **With the two sendings swapped the test says no at some typed size.** Stated as
"= false": so it also shows that there is a typed size at which the test is evaluated. An evaluation
in Lean's kernel. -/
theorem sentFitsRefusesASwap : (VerifiableInference.Desc.K1.realSized.all fun y =>
    sentFitsAtB parWF parGF (ProofFile.Honest.K12.Light.planOf y.2 y.1.shape)) = false := by
  decide +kernel

/-- The test reads the shared plan's codes and shape alone. -/
theorem sentFitsReadsThePlan (A : SendPub) :
    sentFitsB A = sentFitsB (ProofFile.Honest.K12.Light.planOf A.P.codes A.P.S) := rfl

/-- **From the test's yes to the propositions.** -/
theorem sentMembersFitOfTheTest (A : SendPub) (yes : sentFitsB A = true) :
    SentMembersFit (piWFull.nums.stages.headD default) parGF parWF writtenRideOfW
      ((firstsOf (shapesW parGF parWF ((jobOmega A).Q.sent.getD 0 default).shape)).getD 0
        (none, none))
      ((firstsOf (shapesW parGF parWF ((jobOmega A).Q.sent.getD 0 default).shape)).getD 1
        (none, none)) := by
  unfold sentFitsB sentFitsAtB at yes
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at yes
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩, a7⟩, a8⟩, a9⟩, a10⟩, a11⟩, a12⟩, a13⟩, a14⟩,
    a15⟩, a16⟩, a17⟩ := yes
  exact ⟨a1, a2, ⟨a3, code_of_same a4⟩, ⟨a5, a6, code_of_same a7, a8⟩, ⟨a9, code_of_same a10⟩,
    blocksApart a11, blocksApart a12, ⟨a13, a5, a14, a15, a16, code_of_same a17⟩⟩

/-! ## 2 At the job -/

variable {W X Xi : Type}

/-- The job's three members, with the first rows of their blocks written out. -/
theorem membersOfJobW (q : P12) (door : W → Front X → T12) (JI : K1.SendJob Readers X)
    (JW : K1.SendJob (K1.PlaceIn Xi) X) (A : SendPub) (readers : W → Readers)
    (wit : W → K1.PlaceIn Xi) (ask : W → Ask) (n₁ : ℕ) :
    (jobW q door JI JW A readers wit ask n₁).mems =
      [memK1 JI readers senderI (JI.P.sent.size - 1)
          ((firstsOf (shapesW JI.P JW.P ((jobOmega A).Q.sent.getD 0 default).shape)).getD 0
            (none, none)),
        memK1 JW wit senderW 0
          ((firstsOf (shapesW JI.P JW.P ((jobOmega A).Q.sent.getD 0 default).shape)).getD 1
            (none, none)),
        memOfSending (jobOmega ⟨A.P, n₁ + A.atPoint⟩) senderO 0
          ((firstsOf (shapesW JI.P JW.P ((jobOmega A).Q.sent.getD 0 default).shape)).getD 2
            (none, none)) ask none] := rfl

/-- **The columns of trees 0 and 1 of a job on three members, of which the first two are messages
of two sendings, are the two senders' own written symbols at the senders' own coins.** f0, f1: the
first rows of the two members' blocks. fits: the public premises. tails: the test's coins for the
fresh table's tails follow its coefficients. The five premises "held": the carried coins are the
senders' own, number by number. -/
theorem columnsOfTwoSentMembers (B : ManyJob W X) {WI WW : Type} (JI : K1.SendJob WI X)
    (JW : K1.SendJob WW X) (liftI : W → WI) (liftW : W → WW) (addressI addressW : Addr)
    (f0 f1 : Option ℕ × Option ℕ) (mC : Mem W X)
    (members : B.mems = [memK1 JI liftI addressI (JI.P.sent.size - 1) f0,
      memK1 JW liftW addressW 0 f1, mC]) {depth0 depth1 : ℕ}
    (tree0 : B.trees[0]? = some (depth0, [.mask 0]))
    (tree1 : B.trees[1]? = some (depth1, [.main 1, .mask 1, .fresh]))
    (fits : SentMembersFit B.s₀ JI.P JW.P JW.ride f0 f1) (w : W) (fr : Front X) (C : TestCoins)
    (tails : C.tails = tailsIn B.s₀ C.hide)
    (cI : Cs (K1.dueR JI.P JI.ride)) (cW : Cs (K1.dueR JW.P JW.ride))
    (heldIndexF : ∀ i, i < (K1.dueMsg JI.P.codes (shapeAt JI.P (JI.P.sent.size - 1))
        (JI.ride (JI.P.sent.size - 1))).f →
      K1.cf cI ((K1.startR JI.P JI.ride (JI.P.sent.size - 1)).f + i) = (C.mem 0).f i)
    (heldIndexE : ∀ i, i < (K1.dueMsg JI.P.codes (shapeAt JI.P (JI.P.sent.size - 1))
        (JI.ride (JI.P.sent.size - 1))).e →
      K1.ce cI ((K1.startR JI.P JI.ride (JI.P.sent.size - 1)).e + i) = (C.mem 0).e i)
    (heldWF : ∀ i, i < (K1.dueMsg JW.P.codes (shapeAt JW.P 0) (JW.ride 0)).f →
      K1.cf cW ((K1.startR JW.P JW.ride 0).f + i) = (C.mem 1).f i)
    (heldWE : ∀ i, i < (K1.dueMsg JW.P.codes (shapeAt JW.P 0) (JW.ride 0)).e →
      K1.ce cW ((K1.startR JW.P JW.ride 0).e + i) = (C.mem 1).e i)
    (heldFresh : ∀ i < dueFresh B.s₀, K1.ce cW ((K1.startR JW.P JW.ride 1).e + i) = C.hide i)
    (x : ℕ) :
    ((B.toRun.toTest.trees₀ w fr C.mem (B.toRun.toTest.first w fr C)).getD 0
        (0, fun _ => [])).2 x =
      maskSyms JI.P (K1.rowsR JI.P JI.ride (JI.data (liftI w) fr) cI) (JI.P.sent.size - 1) x ∧
    ((B.toRun.toTest.trees₀ w fr C.mem (B.toRun.toTest.first w fr C)).getD 1
        (0, fun _ => [])).2 x =
      mainSyms JW.P (K1.rowsR JW.P JW.ride (JW.data (liftW w) fr) cW) 0 x ++
        maskSyms JW.P (K1.rowsR JW.P JW.ride (JW.data (liftW w) fr) cW) 0 x ++
        maskSyms JW.P (K1.rowsR JW.P JW.ride (JW.data (liftW w) fr) cW) 1 x := by
  refine ⟨?_, ?_⟩
  · exact firstTreeIsTheSenders B _ mC w fr C JI liftI addressI (JI.P.sent.size - 1) f0 members
      tree0 fits.indexMasks _
      (rowsR_csAt JI.P JI.ride _ _ fits.indexMessage (C.mem 0) cI heldIndexF heldIndexE) x
  · exact secondTreeIsTheSenders B _ mC w fr C JW liftW addressW f1 members tree1 fits.wMain
      fits.wMask fits.clearMain fits.clearMask 1 fits.fresh.maskRows fits.fresh.code _
      (rowsR_csAt JW.P JW.ride _ _ (Nat.lt_trans Nat.zero_lt_one fits.wMessages) (C.mem 1) cW
        heldWF heldWE)
      (freshTableIsTheSendersRows fits.fresh _ cW C.hide fun i below =>
        heldFresh i (Nat.lt_of_lt_of_le below (Nat.le_add_right _ _)))
      (fun r isRow t isPlace => by
        show C.tails r t = _
        rw [tails]
        exact freshTailsAreTheSenders fits.fresh _ cW C.hide heldFresh r isRow t isPlace) x

/-- **The public premises hold at jobW**, at the written sendings, W's written ride and the written
place's stages (four equations), where the closed test says yes. -/
theorem sentMembersFitAtJobW (q : P12) (door : W → Front X → T12) (JI : K1.SendJob Readers X)
    (JW : K1.SendJob (K1.PlaceIn Xi) X) (A : SendPub) (readers : W → Readers)
    (wit : W → K1.PlaceIn Xi) (ask : W → Ask) (n₁ : ℕ) (hPI : JI.P = parGF) (hPW : JW.P = parWF)
    (hRW : JW.ride = writtenRideOfW) (hst : q.nums.stages = piWFull.nums.stages)
    (yes : sentFitsB A = true) :
    SentMembersFit (jobW q door JI JW A readers wit ask n₁).s₀ JI.P JW.P JW.ride
      ((firstsOf (shapesW JI.P JW.P ((jobOmega A).Q.sent.getD 0 default).shape)).getD 0
        (none, none))
      ((firstsOf (shapesW JI.P JW.P ((jobOmega A).Q.sent.getD 0 default).shape)).getD 1
        (none, none)) := by
  have fits := sentMembersFitOfTheTest A yes
  rw [← hst, ← hPI, ← hPW, ← hRW] at fits
  exact fits

end ProofFile.Honest.K12.Part4

#print axioms ProofFile.Honest.K12.Part4.blocksApart
#print axioms ProofFile.Honest.K12.Part4.sentFitsAtTheTypedSizes
#print axioms ProofFile.Honest.K12.Part4.sentFitsRefusesASwap
#print axioms ProofFile.Honest.K12.Part4.sentFitsReadsThePlan
#print axioms ProofFile.Honest.K12.Part4.sentMembersFitOfTheTest
#print axioms ProofFile.Honest.K12.Part4.membersOfJobW
#print axioms ProofFile.Honest.K12.Part4.columnsOfTwoSentMembers
#print axioms ProofFile.Honest.K12.Part4.sentMembersFitAtJobW
