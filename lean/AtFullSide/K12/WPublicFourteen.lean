-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K12/WPublicFourteen.lean: THE FOURTEEN PUBLIC PREMISES of saysAt_rest (AtFullSide/K12/WSaysRest.lean) and saysAt_at_letters (WSaysAtLetters.lean), at the filling's job, UNDER THE HEAD AT A
RETURN ALONE: no stand, no run, no coin's value.

  PublicFourteen hd M layO   the fourteen as one structure; each field bears the premise's text to the letter and names its binder there
  dueOmega_written, point_written, omegaShape_written, sharedShape_written   four closed lines at the written sizes, put to Lean's kernel: each can say no
  dueOmega_bent              a control: at the first sending's address the count is another
  book_written_at_return     the return's book is what the maker of books returns at the written description
  publicFourteen_at_head     THE STATEMENT: ∃ layO, PublicFourteen hd M layO

BY WHAT. hAp sharedTenantsApart · hpl the job's text, stages_at_head · hP plan2_sentWithU · hcov, n5 covers_head, cut_of_cover · hdS book_made_written, dueOmega_written · htf, hte written_O with hdS ·
ht₁ first_trees_83 · hten shNums_tenant, tenants_written, the head's count of trees · hpoint planAlike_at_head, alike₂_rounds, point_written · hx199 omegaShape_written · hso sharedShape_written ·
ha sendPub_at_head.

Limits. The full size and the format's second hash function alone. hx199 is put to the kernel here by a line of this file's own, in the premise's own form; narrow_shapes' third clause
(AtFullSide/K12/WNumbersAtHead.lean) says the like in another form: on a ground that holds that file one of the two can go. Public numbers: nothing on a stand, a run or a coin. Nothing on completeness,
soundness or hiding.
-/
import AtFullSide.K12.LettersAtHead
import AtFullSide.K12.HeldAtHeadW
import AtFullSide.K14.SixSidesLent
import Johnson.Desc.ProofFile.Honest.K12.AtFile.BookLines
import Johnson.Desc.ProofFile.Honest.K12.AtFile.TreesSentBeforeTestAtU
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WNarrowAtW
import Johnson.Desc.ProofFile.Honest.K12.AtProof.HalfAtPure
import Johnson.Desc.ProofFile.Honest.K12.StagesAtHead
import Johnson.Desc.ProofFile.Honest.K14.ArrAtHead
import Johnson.Desc.ProofFile.Honest.K14.AsksAtShared
import Johnson.Desc.ProofFile.Honest.K14.TenantAtHead
import Johnson.Desc.ProofFile.Honest.K14.WordsAtLastWitness
import Johnson.Desc.ProofFile.Honest.K14.WrittenAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

noncomputable section

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K12
open ProofFile.Honest ProofFile.Honest.K12 ProofFile.Honest.K12.AtProof
open VerifiableInference.Desc.K1 (qAt realSized)
open OnBytes.Slice (frS)
open ProofFile.Honest.K12.AtFile (narrowW covers_head cut_of_cover)
open ProofFile.Honest.FirstThread (HeadAtReturn sharedShape)
open ProofFile.Honest.K12.Light (ManyJob planOf written_at_head qAt_written stages_at_head)
open ProofFile.Honest.K14
open VerifierAndGoals.AtTheName (dpZ)
open P2Law.ProofPlan (WP)
open Johnson.G (proofSendsFull)
open AtFullSide.K14 (rawRowsSharedW book_made_written bookRaw_returns_written bookWhole_returns_raw)

/-! ## 1 Closed lines -/

/-- What the written book's shared rows hold for Omega's sender is what its part takes. -/
theorem dueOmega_written : (realSized.all fun q =>
    decide (dueAt rawRowsSharedW senderO = (sendingPart (jobOmega (planOf q.2 q.1.shape))).takes)) = true := by
  decide +kernel

/-- A control: at the first sending's address the count is another. -/
theorem dueOmega_bent : (realSized.all fun q =>
    decide (dueAt rawRowsSharedW senderU = (sendingPart (jobOmega (planOf q.2 q.1.shape))).takes)) = false := by
  decide +kernel

/-- The written shared chain's first round draws as many elements as the shape has column variables. -/
theorem point_written : (realSized.all fun q =>
    decide (((declsTo WP.shared.blocksInOrder WP.shared.blocksInOrder.length).head?).map (·.entry.drawE) =
      some (planOf q.2 q.1.shape).P.par.S.kCol)) = true := by
  decide +kernel

/-- The closed shape's message 199 has Omega's shape. -/
theorem omegaShape_written : (realSized.all fun q =>
    decide ((narrowW.st.oracles[199]?).map (·.shape) = some (planOf q.2 q.1.shape).P.par.S.omega)) = true := by
  decide +kernel

/-- What goes out with Omega has, first, Omega's shape. -/
theorem sharedShape_written : (realSized.all fun q =>
    decide (((_root_.Desc.K14.withOmega (planOf q.2 q.1.shape).P.S).getD 0 default).shape =
      (planOf q.2 q.1.shape).P.par.S.omega)) = true := by
  decide +kernel

/-! ## 2 The fourteen -/

variable {W₀ : Type} {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}

/-- **The fourteen public premises of saysAt_rest**, each in its own text. -/
structure PublicFourteen (hd : HeadAtReturn files A) (M : ManyJob (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit)
    (layO : OnBytes.TreeLay) : Prop where
  /-- hAp -/
  tenantsApart : ProofFile.Honest.FirstThread.SharedTenantsApart hd
  /-- hpl -/
  place : M.toRun.toTest.p.place = placeW
  /-- hP -/
  plan : Plan2 (qAt A.Z hd.places) (ProofFile.Honest.K12.Light.sentOf (qAt A.Z hd.places).S) layO
  /-- hcov -/
  covers : ∀ k : Coins A.B, ∃ own, (k.look 1 ⟨sendPlace 5, 0⟩).2.cut ⟨0, 0⟩
    (sendingPart (jobOmega ⟨qAt A.Z hd.places, 0⟩)).takes = some own
  /-- n5 -/
  countAtFive : (dueAt (A.B.rowsOf 1) ⟨sendPlace 5, 0⟩).e =
    (sendingPart (jobOmega ⟨qAt A.Z hd.places, 0⟩)).takes.e
  /-- hdS -/
  dueShared : dueAt A.B.shared senderO = (sendingPart (jobOmega ⟨qAt A.Z hd.places, 0⟩)).takes
  /-- htf -/
  rowBase : rowOF.2.2.f ≤ (sendingPart (jobOmega ⟨qAt A.Z hd.places, 0⟩)).takes.f
  /-- hte -/
  rowExtension : rowOF.2.2.e ≤ (sendingPart (jobOmega ⟨qAt A.Z hd.places, 0⟩)).takes.e
  /-- ht₁ -/
  firstTrees : 83 ≤ hd.description.t₁
  /-- hten -/
  tenantOmega : hd.sharedNumbers.tenant .oOmega = (((dpZ files).at frS.P.T.a).t₁ + 1, 0)
  /-- hpoint -/
  point : ((declsTo hd.description.shared.blocksInOrder hd.description.shared.blocksInOrder.length).head?).map
    (·.entry.drawE) = some (qAt A.Z hd.places).par.S.kCol
  /-- hx199 -/
  shapeAt199 : (narrowW.st.oracles[199]?).map (·.shape) = some (qAt A.Z hd.places).par.S.omega
  /-- hso -/
  sharedShapeOmega : sharedShape A.Z hd.places .oOmega = (qAt A.Z hd.places).par.S.omega
  /-- ha -/
  pointInFront : ∀ a, sendPub A.Z = some ⟨qAt A.Z hd.places, a⟩ → a = 0

/-- The return's book is what the maker of books returns at the written description. -/
theorem book_written_at_return (hd : HeadAtReturn files A) {P : OnlineProverParts W₀ IndexCommitterCoins Cells Unit Unit}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL P = .ok A) :
    bookWhole WP proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2 (mergesByName WP.first.blocksInOrder) =
      .ok A.B := by
  obtain ⟨W, hW⟩ := bookRaw_returns_written
  obtain rfl : W = A.B :=
    Except.ok.inj ((bookWhole_same_at_made (bookWhole_returns_raw W hW) hd.head).symm.trans
      (atPure_book_at_head hd.head hA))
  exact bookWhole_returns_raw _ hW

/-- **THE FOURTEEN AT THE FILLING's JOB, UNDER THE HEAD.** -/
theorem publicFourteen_at_head (hd : HeadAtReturn files A) (I : WiderIn W₀) (S : OnBytes.HonestTrace.Sz)
    (O : OnlineProverArguments)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL
      (onlineProverPartsInUse I OnBytes.secondHashFunction S O) = .ok A)
    {M : ManyJob (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit}
    (hM : jobAtFill A.Z hd.places hd.firstChain I S O A.G = some M) :
    ∃ layO, PublicFourteen hd M layO := by
  have h := hd.head
  obtain ⟨x, hx, Wr⟩ := written_at_head h.toAtMg
  obtain ⟨layO, hQ⟩ := plan2_sentWithU h
  obtain ⟨B⟩ := hQ.eight
  have hB := book_written_at_return hd hA
  obtain ⟨-, c5, -, n5⟩ := covers_head h.toAtMg hB
  have eS : A.B.shared = rawRowsSharedW := (book_made_written h hA).2.1
  have l1 := dueOmega_written
  have l2 := point_written
  have l3 := omegaShape_written
  have l4 := sharedShape_written
  rw [hx] at l1 l2 l3 l4
  simp only [Option.all_some, decide_eq_true_eq] at l1 l2 l3 l4
  have hdS : dueAt A.B.shared senderO = (sendingPart (jobOmega ⟨qAt A.Z hd.places, 0⟩)).takes := by
    rw [eS, qAt_written Wr hd.places]
    exact l1
  obtain ⟨-, -, -, wf, we⟩ := written_O
  have t83 : hd.description.t₁ = 83 := first_trees_83 h.toAtMg
  refine ⟨layO, ⟨sharedTenantsApart hd, ?_, hQ, ?_, n5, hdS, ?_, ?_, le_of_eq t83.symm, ?_, ?_, ?_, ?_, ?_⟩⟩
  · -- hpl
    unfold jobAtFill jobRealW at hM
    obtain ⟨F, hF, hM⟩ := Option.bind_eq_some_iff.1 hM
    obtain ⟨An, -, hM⟩ := Option.bind_eq_some_iff.1 hM
    obtain ⟨msg, -, rfl⟩ := Option.map_eq_some_iff.1 hM
    obtain rfl : F = fourOf hd.places := Option.some.inj (hF.symm.trans (stages_at_head h.toAtMg).1)
    show (H2U.proximityTestParametersAt placeW hd.places.W).place = placeW
    exact H2K.JointK.place_of_p12At _ _
  · -- hcov
    intro k
    exact Option.isSome_iff_exists.1 (cut_of_cover k (sendPlace 5) _ c5)
  · -- htf
    rw [← hdS, eS]
    exact wf
  · -- hte
    rw [← hdS, eS]
    exact we
  · -- hten
    have e : hd.sharedNumbers.tenant = _root_.Desc.K14.Law.Fence.tenantSh 83 _root_.Desc.K14.Law.layUFull
        _root_.Desc.K14.Law.layOFull :=
      shNums_tenant h.toAtMg _
    have t : ((dpZ files).at frS.P.T.a).t₁ = 83 := h.toAtMg.trees.1
    rw [e, t]
    exact tenants_written.2.1
  · -- hpoint
    have e : declsTo hd.description.shared.blocksInOrder hd.description.shared.blocksInOrder.length =
        declsTo WP.shared.blocksInOrder WP.shared.blocksInOrder.length := by
      unfold declsTo
      rw [List.take_length, List.take_length]
      exact (VerifiableInference.Desc.alike₂_rounds _ _ (planAlike_at_head h).shared).symm
    rw [e, qAt_written Wr hd.places]
    exact l2
  · -- hx199
    rw [qAt_written Wr hd.places]
    exact l3
  · -- hso
    show ((_root_.Desc.K14.withOmega (qAt A.Z hd.places).S).getD 0 default).shape = _
    rw [qAt_written Wr hd.places]
    exact l4
  · -- ha
    intro a ha
    have e := Option.some.inj ((sendPub_at_head h.toAtMg B.b1 B.b2 B.b3 B.b4 B.b5 B.b6 B.b7 B.b8 B.made).symm.trans ha)
    exact (congrArg (·.atPoint) e).symm

end AtFullSide.K12

#print axioms AtFullSide.K12.dueOmega_written
#print axioms AtFullSide.K12.dueOmega_bent
#print axioms AtFullSide.K12.point_written
#print axioms AtFullSide.K12.omegaShape_written
#print axioms AtFullSide.K12.sharedShape_written
#print axioms AtFullSide.K12.book_written_at_return
#print axioms AtFullSide.K12.publicFourteen_at_head
