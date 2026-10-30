-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/FiveAtLaid.lean: the five sentences at member 9 at the shared chain's
thread as ProofFile lays it at a return of the maker: `sharedThread` (Honest/Thread/TheFirstThread.lean). The book is
the return's: `makers_book_one` (AtFullSide/K14/MakersBookOne.lean) closes what `five_nine` asks of it.

  `book_written`   the return's book is the maker's book at the written description
  `five_at_sharedThread`   the statement

What stays, all of it on the parts that `sharedThread` takes from outside its file. htb, hfx: the trees' tables
and counts are `tableShared`'s, `sentIn`'s. hf: the prover's list finds the test's half: `half_found` at the base
list. hrd, hoth, hkp: the riders and the form at 10 and what the test's place keeps, behind a step at a stand.
hku: what the test's place keeps is a yes of the test, at a stand. hO: the second test's place. hb: the eight.

Limits.
- NOT IN FRONT OF A LAW OVER COINS: all five have `ThrS` as a premise. That a stand at 9 is reached is not said.
- At the return's own prover: read through, the half is no `proverSideOfProximityTest`.
- Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.LaidAtShared
import Johnson.Desc.ProofFile.Honest.Thread.TheFirstThread
import AtFullSide.K14.MakersBookOne

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace ProofFile.Honest.K12.AtFile
open OnBytes (TableKey)
open VerifiableInference.Desc (Block Place)
open VerifiableInference.Desc (K1.qAt)
open VerifiableInference.Desc.K12 (T12 proximityTestKind guardedProximityTestParts)
open Desc.K14 (St blocks)
open ProofFile.Honest
open ProofFile.Honest.K12
open ProofFile.Honest.FirstThread
open ProofFile.Honest.K12.Light (sentOf)
open ProofFile.Honest.K12.AtProof (fourOf placeU)
open P2Law.ProofPlan (WP declProofFull)
open Johnson.G (proofSendsFull)

variable {W₀ Rc Tr X₀ X Wt : Type} {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}

/-- **The return's book is the maker's book at the written description.** -/
theorem book_written (h : HeadAtReturn files A) :
    bookWhole WP proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName WP.first.blocksInOrder) = .ok A.B := by
  obtain ⟨B, hW, -, -, -, hall⟩ := AtFullSide.K14.makers_book_one h.head
  obtain ⟨P, hP⟩ := h.returned
  obtain ⟨eB, -⟩ := hall _ _ _ _ _ P A hP
  rw [eB]
  exact hW

/-- **The five sentences at member 9, at ProofFile's shared thread.** -/
theorem five_at_sharedThread (h : HeadAtReturn files A) (reads : IndexReaders W₀ Rc)
    (parts : SharedThreadParts A Wt) (w : Common W₀ Rc TableKey)
    (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks (K1.qAt A.Z h.places) = some [b1, b2, b3, b4, b5, b6, b7, b8])
    (JO : TestJob (Common W₀ Rc TableKey) X₀) (own₀ : X₀)
    (htb : parts.table = tableShared (K1.qAt A.Z h.places) reads.weights reads.rand
      (jobDoorU (X₀ := X₀) A.Z h.places [b1, b2, b3, b4, b5, b6, b7, b8] A.H.storedWords reads.weights
        reads.rand).toRun.toTest JO own₀)
    (hfx : ∀ i, parts.fixed (.own i) = ProofFile.Honest.Small.sentIn declProofFull.2.1 i)
    (nO : H2U.PlaceNums) (hO : h.places.O = some nO)
    (hf : (A.H.shared.find? fun g => g.place == (fourOf h.places).U.place) =
      some (proverSideOfProximityTest (jobDoorU (X₀ := X₀) A.Z h.places [b1, b2, b3, b4, b5, b6, b7, b8]
                         A.H.storedWords reads.weights reads.rand).toRun.toTest))
    (Said : ℕ → Coins A.B → Mid (Common W₀ Rc TableKey) X₀ → Prop)
    (fall : ℕ → St → List Fmt.Drawn → Option String)
    (hrd : ∀ blk, (sharedThread h reads parts w).bs[9]? = some blk →
      ∀ k s m E ds y cols s', ThrS (sharedThread h reads parts w) Said 9 k s m E →
        (sharedThread h reads parts w).Stepped blk k s m E ds y cols s' →
        (sharedThread h reads parts w).rides 10 y.2.st.input s')
    (hoth : ∀ blk, (sharedThread h reads parts w).bs[9]? = some blk →
      ∀ k s m E ds y cols s', ThrS (sharedThread h reads parts w) Said 9 k s m E →
        (sharedThread h reads parts w).Stepped blk k s m E ds y cols s' → parts.shape 10 s' = true)
    (hkp : ∀ blk, (sharedThread h reads parts w).bs[9]? = some blk →
      ∀ k s m E ds y cols s', ThrS (sharedThread h reads parts w) Said 9 k s m E →
        (sharedThread h reads parts w).Stepped blk k s m E ds y cols s' → parts.keeps placeU s s')
    (hku : ∀ k s m E s', ThrS (sharedThread h reads parts w) Said 9 k s m E →
      parts.keeps placeU s s' → keepsU (fourOf h.places).U s s') :
    PlaysS (sharedThread h reads parts w) Said 9 ∧ BehindS (sharedThread h reads parts w) Said 9 ∧
      ExchangeS (sharedThread h reads parts w) Said 9 ∧
      RidesPastS (sharedThread h reads parts w) Said 9 ∧
      AcceptedS (sharedThread h reads parts w) Said fall 9 := by
  obtain ⟨blk, G⟩ := laidU_head h.head.toAtMg A.H h.sharedNumbers parts.lens parts.meaning parts.shape
    (fun d => (_root_.Desc.K14.ended d).isSome) reads.weights reads.rand parts.rest
    b1 b2 b3 b4 b5 b6 b7 b8 hb JO own₀ parts.table htb parts.fixed hfx h.description.t₁
    h.description.t₂ (fun v => A.H.inRange v.w₀ = true) parts.rides parts.keeps w nO hO hf
  exact five_nine h.head.toAtMg h.head (book_written h) _ parts.lens parts.meaning parts.shape
    reads.weights reads.rand (fun k v hd => parts.lens.get (parts.rest k v hd)) A.H.storedWords _
    b1 b2 b3 b4 b5 b6 b7 b8 JO own₀ blk G Said (hrd blk G.member) (hoth blk G.member)
    (fun k s m E ds y cols s' u hS => (keeps_nine _ _ _ s s').2 (hkp blk G.member k s m E ds y cols s' u hS))
    (fun k s m E s' u hk => hku k s m E s' u ((keeps_nine _ _ _ s s').1 hk)) fall

end ProofFile.Honest.K12.AtFile

end

#print axioms ProofFile.Honest.K12.AtFile.book_written
#print axioms ProofFile.Honest.K12.AtFile.five_at_sharedThread
