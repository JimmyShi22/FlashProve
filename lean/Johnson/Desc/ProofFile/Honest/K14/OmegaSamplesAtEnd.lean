-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K14/OmegaSamplesAtEnd.lean: kind K14: at the full size, where the
shared chain's honest thread (sharedThread, Honest/Thread/TheFirstThread.lean) stands at that
chain's last border: Omega's sample rows at that state say their claims of the words that the
library's reading takes off the SECOND chain's honest witness (lastWitness, the same file), read
through the shared chain's book behind the plan's count of the first chain's trees. Statements with
their proofs; no definition.

It is omega_samples_of_thread (Honest/K14/OmegaSamplesOfThread.lean) with its three premises on the
state shown by omega_written_at_shared_end (Honest/K14/OmegaSeatAtEnd.lean): the state notes Omega
as the message number 2, with the plan's shape, and its book seats it at the table's tenant.

  shared_has_twelve   at the full size the shared chain has twelve sub-protocols
  omega_shape_is      the shape that lastWitness's tables are laid at for Omega is the plan's
  trees_one_number    three names of the first chain's count of trees are the number 83: the one at
                      the plan's data, the description's, and the shared table's plan's
  omega_samples_at_end   **the statement**: its conclusion is, to the letter, what is asked of Omega
                      in front of the second chain's proximity test

Premises of omega_samples_at_end beside the thread u.
  hin     the input of the thread's run is ⟨w.w₀, w.rc, A.H.key w.x⟩: the shared chain's input made
          from w, the input of the second chain's run
  hd      the first challenge that the thread's run has heard is the first behind the first chain's
          in the list that lastWitness is handed
Both can be met at a run, by the frame's text (Honest/Frame.lean): ready lays the two inputs in just
this form, and Ready.start₃ hands the second chain the first chain's challenges followed by the
shared chain's; hd then needs that the first chain's run has heard as many challenges as that chain
declares rounds, and the shared chain's at least one.
NEITHER IS SHOWN HERE, NOR THAT THE THREAD STANDS AT ANY RUN. The coins k are one run's.

Limits. h : HeadAtReturn is a hypothesis (Honest/K14/WordsAtLastWitness.lean says what it holds).
The second chain's thread names the shared chain's last state through a free field of what it takes
from outside: a caller owes u at that value. Omega alone. Where Desc.K14.ended returns nothing the
statement says nothing; under u it does return (ended_at_shared_end, Honest/K14/SharedEnds.lean).

This file proves nothing about soundness, completeness, hiding or any other property of the
protocol.
-/
import Johnson.Desc.ProofFile.Honest.K14.OmegaSamplesOfThread
import Johnson.Desc.ProofFile.Honest.K14.OmegaSeatAtEnd

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open OnBytes.Slice (rdE frS)
open OnBytes.Means (SampleSays)
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.Shared (Msg2)
open VerifiableInference.Desc.Sound (wordsShared)
open VerifiableInference.Desc.Third (sharedOfEnd)
open VerifiableInference.Desc.K1 (qAt)
open VerifierAndGoals.AtTheName (dpZ)
open Desc.K14 (St)
open ProofFile.Honest.FirstThread

/-- At the full size the shared chain has twelve sub-protocols. -/
theorem shared_has_twelve {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
    {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl}
    {x₀ : VerifiableInference.Desc.First.Look.Place}
    (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) :
    (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder.length = 12 := by
  obtain ⟨sentU, layO, hQ⟩ := plan2_at_head h
  obtain ⟨nO, hO⟩ := H2K.JointK.omega_some_in_scope h.scope Zp ProofFile.pureRoad.links Np cF
    h.laid.planOk (LPFD.asks_written h.laid.asks)
  obtain ⟨B⟩ := hQ.eight
  exact shared_twelve Zp Np cF B.b1 B.b2 B.b3 B.b4 B.b5 B.b6 B.b7 B.b8 nO hO B.made

variable {W₀ Rc Tr X₀ X Wt : Type} {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}

/-- The shape at which lastWitness's table for Omega is laid is the plan's shape of Omega. -/
theorem omega_shape_is (h : HeadAtReturn files A) :
    sharedShape A.Z h.places .oOmega = (qAt A.Z h.places).S.omega := by
  show ((Desc.K14.withOmega (qAt A.Z h.places).S).getD 0 default).shape = _
  rw [Desc.K14.Law.withOmega_split (sendings_at_head h.head).2.1]
  rfl

/-- **Three names of the first chain's count of trees are the number 83.** -/
theorem trees_one_number (h : HeadAtReturn files A) :
    ((dpZ files).at frS.P.T.a).t₁ = 83 ∧ h.description.t₁ = 83 ∧
      Desc.K14.Law.Sh.t₁ h.head.toAtMg.shPlan = 83 :=
  ⟨h.head.toAtMg.trees_at.1, first_trees_83 h.head.toAtMg, h.head.toAtMg.first_told⟩

/-- **FROM THE SHARED CHAIN's THREAD AT ITS LAST BORDER: OMEGA's SAMPLE ROWS SAY THEIR CLAIMS OF
lastWitness's WORDS**, read through the shared chain's book behind the plan's count of the first
chain's trees. -/
theorem omega_samples_at_end (h : HeadAtReturn files A) (first : FirstThreadParts A)
    (reads : IndexReaders W₀ Rc) (sh : SharedThreadParts A Wt)
    (w₂ : Common W₀ Rc OnBytes.TableKey) {k : Coins A.B} {e₂ : St}
    {m₂ : Mid (Common W₀ Rc OnBytes.TableKey) X₀} {E₂ : Env}
    (u : Thr (sharedThread h reads sh w₂) h.description.shared.blocksInOrder.length k e₂ m₂ E₂)
    (w : Local W₀ Rc ProofFile.Inst Tr) (heard : List Fmt.Drawn)
    (hin : m₂.st.input = ⟨w.w₀, w.rc, A.H.key w.x⟩)
    (hd : firstRv m₂.st.heard = firstRv (heard.drop
      (declsTo h.description.first.blocksInOrder h.description.first.blocksInOrder.length).length)) :
    ∀ e, Desc.K14.ended e₂ = some e →
      SampleSays rdE (sharedOfEnd e).st (sharedOfEnd e).omega
        (wordsShared (P5J.At.arr A.Z) ((dpZ files).at frS.P.T.a).t₁ (sharedOfEnd e).st
          (sharedOfEnd e).book (lastWitness h first reads k w heard)) := by
  obtain ⟨ho, -, hx, hseat⟩ :=
    omega_written_at_shared_end _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h.head u
  have u12 : Thr (sharedThread h reads sh w₂) 12 k e₂ m₂ E₂ := shared_has_twelve h.head ▸ u
  refine omega_samples_of_thread h first reads sh w₂ u12 w heard hin hd _ ho ?_ ?_
  · rw [(trees_one_number h).1, hseat 83]
    exact congrArg some (congrFun (shNums_tenant h.head.toAtMg _) .oOmega).symm
  · rw [omega_shape_is h]
    exact hx

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.shared_has_twelve
#print axioms ProofFile.Honest.K14.omega_shape_is
#print axioms ProofFile.Honest.K14.trees_one_number
#print axioms ProofFile.Honest.K14.omega_samples_at_end
