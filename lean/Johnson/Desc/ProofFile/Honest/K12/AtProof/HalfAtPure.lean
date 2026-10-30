-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/AtProof/HalfAtPure.lean: the pair at the proximity test on G_u
(`halfU`, HalfU.lean in this folder) at a filling of the honest prover (`onlineProverFromPublicFiles`,
Johnson/Desc/ProofFile/Honest/AtPure.lean) and under the library's head: three hypotheses of our
laws at that test, as lemmas; and that under the head the job which is handed is the job of which
these laws speak. No definition; ten theorems.

  `key_at_pure`   the key of `onlineProverFromPublicFiles`'s prover is the instance's: the hypothesis hα of `door_at_run`
                 (K12/DoorAtRun.lean) and `atHandU_at_run` (AtHandU.lean). At every filling
  `storedWords_at_pure`   its stored words are the filling's columns as words: the hypothesis hst of
                 `atHandAtU_at_run`. At every filling
  `withHalfU_shared`, `withHalfU_enc`, `shared_at_pure`   what `withHalfU` lays, and what
                 `onlineProverFromPublicFiles`'s prover then holds in the shared chain
  `inFront_at_head`   under the head, where the eight are made: the frame's count of the rounds in
                 front of "LIN point" is 0: the hypothesis ha of `atHandAtU_at_run`
  `sendPub_at_head`   so the sendings' public data, off the public part, are the head's
  `realU_at_head`, `halfU_at_head`   so the real job is `jobHeadU` (K12/OnFreeTAtHeadU.lean) at the
                 filling's columns as words, the reader wt at the input's index, the plan's item's
                 pad and tail, and no vector of its own; and `halfU` is its pair
  `atHandAtU_at_run'`   `atHandAtU_at_run` with ha paid

By what. The frame's authors' `atPure_ok` (Honest/AtPureLaw.lean), and the texts of
`Prover.storedWords` and `pureKey` (Honest/Frame.lean) and of `sharedInFront`
(Honest/SharedChainProverSides.lean). Of the authors of the honest side of the linear claim's shared rounds
(K14): `readers_at`, `flatOf_plain` (Honest/K14/AtFilling.lean), `dataOf_flat`
(Honest/K14/DataMade.lean), the text of `dataOf` (Honest/K14/Parts.lean). Ours: `stages_at_head`
(K12/StagesAtHead.lean): under the head the places' numbers, off the public part, are the head's.

Limits.
- The join with `onFreeT_head_U` (K12/OnFreeTAtHeadU.lean) is begun here, not made. Its job is the
  term of `realU_at_head` where the prover's stored words are the filling's columns as words. Not
  typed: that none of the chain's six other sides stands at the test's place, so that the prover's
  list is found to hold the pair there; that `onlineProverFromPublicFiles`'s description and public part are the head's;
  and its other hypotheses stay as they are.
- `p14At_at_head` (AtHandU.lean) says what the first half of `readers_at` says. A neighbour of
  `storedWords_at_pure`, in its authors' letters: `storedWords_encW`
  (Johnson/Bind/ForProver/TabCols.lean).
- `onlineProverFromPublicFiles` refuses where a side stands at no place of its chain: so the hypothesis of
  `shared_at_pure` already says that the pair's place, if there is a pair, lies in the shared chain.
- hb, that the library makes the eight at the head's parameters, stays a hypothesis.
- Nothing on whether `onlineProverFromPublicFiles`, `ready` or `runC` returns. Nothing is evaluated here.
- wt is a free letter in all of it: see HalfU.lean's limits.
- The job reads the stored table's columns at "LOC"'s positions; these are computed from the index.
- The stand is the state that `midSharedAtW` (Honest/MidW.lean) returns. That `runC`'s own walk goes
  through that state is not said here.
- It moves no count. Nothing on completeness, soundness or hiding.
Over what it stands. HalfU.lean, Bare.lean, Members.lean, Doors.lean in this folder,
K12/OnFreeTAtHeadU.lean and those named under "By what".
Also beneath this file: AtHandU.lean in this folder, K12/LiveField.lean and, of the
frame's authors (Johnson/Desc/ProofFile/Honest/): Blind, Field, FieldFree, FieldGood, FieldLaw,
FieldOwed, FieldWalk, Gap, GapAt, GapSame, MidW, StepsFront, Tie2File, TieChain, TiePlace, Ties,
WalkHeard, WalkLive, WalkOpened, WalkTake, Law/Rule/FaithOwnFile, Law/Rule/OpenedAt,
Law/Rule/OpenedFile, Law/Rule/OpenedRun, Law/Rule/OpenedStart, Law/Rule/OpenedStep,
Law/Rule/OpenedWalk, Law/WalkMid.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.AtPureLaw
import Johnson.Desc.ProofFile.Honest.K14.AtFilling
import Johnson.Desc.ProofFile.Honest.K14.DataMade
import Johnson.Desc.ProofFile.Honest.K12.StagesAtHead
import Johnson.Desc.ProofFile.Honest.K12.OnFreeTAtHeadU
import Johnson.Desc.ProofFile.Honest.K12.AtProof.AtHandU

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtProof
open OnBytes (TableKey)
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc (K1.qAt)
open Desc.K14 (St blocks)
open ProofFile.Honest.K12.Light (jobHeadU)
open ProofFile.Honest (ProverCoinCounts Prover Coins Draws Ready RunC Side Member Common StandsAt ready runC
  midSharedAtW)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}

section
variable {W₀ Rc Tr X₀ X : Type} {o' : SecondHashFunctionArgument} {pol lay KL : ByteArray}

/-- **The key of `onlineProverFromPublicFiles`'s prover is the instance's**, at every filling. -/
theorem key_at_pure {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (h : onlineProverFromPublicFiles o' pol lay KL P = .ok A) : ∀ x, A.H.key x = x.pub.key := by
  obtain ⟨-, -, -, -, -, -, hk, -⟩ := atPure_ok h
  intro x
  rw [hk]
  rfl

/-- **The stored words of `onlineProverFromPublicFiles`'s prover are the filling's columns as words**, at every
filling. -/
theorem storedWords_at_pure {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (h : onlineProverFromPublicFiles o' pol lay KL P = .ok A) : ∀ w₀ rc i x,
    A.H.storedWords w₀ rc i x = (P.enc A.Z w₀ rc i x).map (·.map OnBytes.Slice.ofF) := by
  obtain ⟨-, -, -, -, hs, -⟩ := atPure_ok h
  intro w₀ rc i x
  unfold Prover.storedWords
  rw [hs]

/-- What `withHalfU` lays in the shared chain. -/
theorem withHalfU_shared (P : OnlineProverParts W₀ IndexCommitterCoins Tr Unit X) (wt : Pub → W₀ → Weights) (Z : Pub)
    (G : Ground) :
    (withHalfU P wt).shared Z G = P.shared Z G ++ halfU (wt Z) (P.enc Z) Z := rfl

/-- It leaves the columns as they are. -/
theorem withHalfU_enc (P : OnlineProverParts W₀ IndexCommitterCoins Tr Unit X) (wt : Pub → W₀ → Weights) :
    (withHalfU P wt).enc = P.enc := rfl

/-- **What `onlineProverFromPublicFiles`'s prover holds in the shared chain at a filling with the pair.** -/
theorem shared_at_pure {P : OnlineProverParts W₀ IndexCommitterCoins Tr Unit X} {wt : Pub → W₀ → Weights}
    {A : OnlineProverWithDescription W₀ IndexCommitterCoins Tr Unit X} (h : onlineProverFromPublicFiles o' pol lay KL (withHalfU P wt) = .ok A) :
    A.H.shared = P.shared A.Z A.G ++ halfU (wt A.Z) (P.enc A.Z) A.Z := by
  obtain ⟨-, -, -, -, -, -, -, -, hs, -⟩ := atPure_ok h
  rw [hs]
  rfl

end

/-- **Under the head, where the eight are made: the frame's count of the rounds in front of
"LIN point" is 0.** -/
theorem inFront_at_head (h : P5J.AtMg o Z D r₀ Zp Np cF) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks (K1.qAt Zp Np) = some [b1, b2, b3, b4, b5, b6, b7, b8]) :
    sharedInFront Zp (K14.place 1) = some 0 := by
  have hr := ProofFile.Honest.K14.readers_at Zp Np h.laid.places
  unfold sharedInFront
  rw [hr.2]
  have F : Desc.K14.Honest.FlatOf (Desc.K14.Law.seatN Zp Np).chain.blocksInOrder Zp.p.chains
      b1 b2 b3 b4 b5 b6 b7 b8 :=
    ProofFile.Honest.K14.flatOf_plain Zp.p.chains (K1.qAt Zp Np) b1 b2 b3 b4 b5 b6 b7 b8
      (VerifiableInference.Desc.K12.Seat.tests Np) VerifiableInference.Desc.K12.Seat.last hb
  have d := ProofFile.Honest.K14.dataOf_flat F hb (K1.qAt Zp Np).S
  unfold ProofFile.Honest.K14.dataOf at d
  obtain ⟨a, ha, d⟩ := Option.bind_eq_some_iff.1 d
  obtain ⟨z, -, e⟩ := Option.map_eq_some_iff.1 d
  have e0 : a = 0 := congrArg (·.atPoint) e
  subst e0
  exact ha

/-- So the sendings' public data, off the public part, are the head's. -/
theorem sendPub_at_head (h : P5J.AtMg o Z D r₀ Zp Np cF) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks (K1.qAt Zp Np) = some [b1, b2, b3, b4, b5, b6, b7, b8]) :
    sendPub Zp = some ⟨K1.qAt Zp Np, 0⟩ := by
  have hr := ProofFile.Honest.K14.readers_at Zp Np h.laid.places
  unfold sendPub
  rw [hr.1, inFront_at_head h b1 b2 b3 b4 b5 b6 b7 b8 hb]
  rfl

/-- **Under the head the real job is the head's job.** -/
theorem realU_at_head {W₀ : Type} (h : P5J.AtMg o Z D r₀ Zp Np cF)
    (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks (K1.qAt Zp Np) = some [b1, b2, b3, b4, b5, b6, b7, b8])
    (wt : W₀ → Weights) (enc : W₀ → IndexCommitterCoins → ℕ → ℕ → Option (List Cb.Gl.F)) :
    realU wt enc Zp = some (jobHeadU Zp Np [b1, b2, b3, b4, b5, b6, b7, b8]
        (fun w rc i x => (enc w rc i x).map (·.map OnBytes.Slice.ofF))
        (fun w => wt w.w₀) (fun w => randAt (K1.qAt Zp Np) w.rc) none).toRun.toTest := by
  unfold realU jobRealU
  rw [(Light.stages_at_head h).1, sendPub_at_head h b1 b2 b3 b4 b5 b6 b7 b8 hb]
  show ((Desc.K14.blocks (K1.qAt Zp Np)).map _).map _ = _
  rw [hb]
  rfl

/-- So `halfU` is that job's pair. -/
theorem halfU_at_head {W₀ : Type} (h : P5J.AtMg o Z D r₀ Zp Np cF)
    (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks (K1.qAt Zp Np) = some [b1, b2, b3, b4, b5, b6, b7, b8])
    (wt : W₀ → Weights) (enc : W₀ → IndexCommitterCoins → ℕ → ℕ → Option (List Cb.Gl.F)) :
    halfU wt enc Zp = [proverSideOfProximityTest (jobHeadU Zp Np [b1, b2, b3, b4, b5, b6, b7, b8]
                         (fun w rc i x => (enc w rc i x).map (·.map OnBytes.Slice.ofF))
                         (fun w => wt w.w₀) (fun w => randAt (K1.qAt Zp Np) w.rc) none).toRun.toTest] := by
  unfold halfU
  rw [realU_at_head h b1 b2 b3 b4 b5 b6 b7 b8 hb]
  rfl

/-- **`atHandAtU_at_run` with ha paid.** The front fr is any that shows just the eight's rounds, as
the stand has seen them: at every value of the field `opened`. -/
theorem atHandAtU_at_run' {W₀ Tr X₀ Y V Pb X : Type} (h : P5J.AtMg o Z D r₀ Zp Np cF)
    (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks (K1.qAt Zp Np) = some [b1, b2, b3, b4, b5, b6, b7, b8]) {Bk : ProverCoinCounts}
    {P : Prover W₀ IndexCommitterCoins ProofFile.Inst TableKey Tr X₀ Y} (hα : ∀ x, P.key x = x.pub.key) {w₀ : W₀}
    {rc : IndexCommitterCoins} {x : ProofFile.Inst} {k : Coins Bk} {ρ : Draws}
    {R : Ready W₀ IndexCommitterCoins ProofFile.Inst TableKey Tr X₀ Y} {r : RunC (P5J.F0T o Zp Np cF)}
    (hR : ready (P5J.F0T o Zp Np cF) Bk P w₀ rc x k = .ok R)
    (σ : Side St ProofFile.Cl V (Common W₀ IndexCommitterCoins TableKey) X₀ Pb)
    (u : Member V (Common W₀ IndexCommitterCoins TableKey) X₀ Pb) (pre t : List (Block St ProofFile.Cl)) (i : ℕ)
    (S : StandsAt (P5J.F0T o Zp Np cF).shared.blocksInOrder R.shared σ u pre t i)
    (h9 : pre = (P5J.F0T o Zp Np cF).shared.blocksInOrder.take 9)
    (hrun : runC (P5J.F0T o Zp Np cF) Bk P w₀ rc x k ρ = .ok r)
    (hc : r.called ⟨σ.block.place, u.number⟩ = true)
    (enc : W₀ → IndexCommitterCoins → ℕ → ℕ → Option (List Cb.Gl.F))
    (hst : ∀ w₀ rc i x, P.storedWords w₀ rc i x = (enc w₀ rc i x).map (·.map OnBytes.Slice.ofF)) :
    ∃ m : ProofFile.Honest.Mid (Common W₀ IndexCommitterCoins TableKey) X₀,
      midSharedAtW (P5J.F0T o Zp Np cF) Bk P w₀ rc x k ρ ⟨σ.block.place, u.number⟩ = .ok (some m) ∧
      ∀ fr : Front X, fr.seen.rounds =
          m.seen.take ([b1, b2, b3, b4, b5, b6, b7, b8].flatMap (·.rounds)).length →
        atHandAtU enc Zp m.st.input fr = true :=
  atHandAtU_at_run h b1 b2 b3 b4 b5 b6 b7 b8 hb hα hR σ u pre t i S h9 hrun hc enc hst 0
    (inFront_at_head h b1 b2 b3 b4 b5 b6 b7 b8 hb)

end ProofFile.Honest.K12.AtProof

#print axioms ProofFile.Honest.K12.AtProof.key_at_pure
#print axioms ProofFile.Honest.K12.AtProof.storedWords_at_pure
#print axioms ProofFile.Honest.K12.AtProof.withHalfU_shared
#print axioms ProofFile.Honest.K12.AtProof.withHalfU_enc
#print axioms ProofFile.Honest.K12.AtProof.shared_at_pure
#print axioms ProofFile.Honest.K12.AtProof.inFront_at_head
#print axioms ProofFile.Honest.K12.AtProof.sendPub_at_head
#print axioms ProofFile.Honest.K12.AtProof.realU_at_head
#print axioms ProofFile.Honest.K12.AtProof.halfU_at_head
#print axioms ProofFile.Honest.K12.AtProof.atHandAtU_at_run'
