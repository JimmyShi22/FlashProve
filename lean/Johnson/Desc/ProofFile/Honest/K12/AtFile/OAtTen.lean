-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/OAtTen.lean: the five sentences of the frame at member 10 of the proof
file's shared thread, the proximity test on G_omega, at one set of letters.

  `five_at_ten`  `PlaysS`, `BehindS`, `ExchangeS`, `RidesPastS`, `AcceptedS`

The premises. h, hO, hA, hB: the head; the seated place; the stronger head; the book is the maker's. L, ℓ, Mg₀, hl, hMg,
hwit, hfirst: a shared thread's letters, whose meaning is `mgWords` and whose witness is `witAll` at the holdings
`holds2`. H: `StandO` (OAccepted.lean). Fx: `FixedO` (OPlays.lean). K: `LettersTen` (OStep.lean). c2, n5: the book's rows
at the two sendings.

Limits.
- NOT IN FRONT OF A LAW OVER COINS: the pair is a premise of all five sentences.
- Any letters, no filling: W₀ and Rc are free; the half at the place is `proverSideOfProximityTest`'s behind the guard, a premise. The
  crossing to the term is another law's. No thread is shown to meet the premises here. A theorem with a false premise says nothing.
- That a stand is reached is not said: the fold of the five sentences over the chain is the thread's.
- Nothing on completeness of the whole chain, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.OStep
import Johnson.Desc.ProofFile.Honest.K12.AtFile.OPlays

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace ProofFile.Honest.K12.AtFile
open OnBytes (TableKey)
open VerifiableInference.Desc (Block Alike₂)
open VerifiableInference.Desc (K1.qAt)
open VerifiableInference.Desc.K12 (P12)
open VerifiableInference.Desc.Shared (MeaningS)
open Desc.K14 (St blocks first)
open ProofFile.Honest
open ProofFile.Honest.K14 (jobU jobOmega sendPlace sendingPart mgWords WitLens holds2 witAll)
open OnBytes.Means (Words)
open ProofFile.Honest.K12
open ProofFile.Honest.K12.Light (sentOf)
open ProofFile.Honest.K12.AtProof (fourOf)
open ProofFile.Honest.SharedThread (Letters)
open P2Law.ProofPlan (WP)
open Johnson.G (proofSendsFull)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl} {pO : P12}
  {W₀ Rc X₀ Cl P₁ Wt : Type} {Bk : ProverCoinCounts}

set_option maxHeartbeats 1000000 in
/-- **The five sentences at member 10.** -/
theorem five_at_ten (h : P5J.AtMg o Z D r Zp Np cF) (hO : (fourOf Np).O = some pO)
    {x₀ : VerifiableInference.Desc.First.Look.Place} (hA : P5J.AtMgA o Z D r Zp Np cF x₀)
    (hB : bookWhole (P5J.F0T o Zp Np cF) proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName (P5J.F0T o Zp Np cF).first.blocksInOrder) = .ok Bk)
    (L : ProofFile.Honest.SharedThread.Letters Bk St Cl W₀ Rc TableKey X₀ P₁ Wt) (ℓ : WitLens Wt)
    (Mg₀ : Common W₀ Rc TableKey → MeaningS St P₁ Wt)
    (hl : List.Forall₂ Alike₂ WP.shared.blocksInOrder L.bs)
    (hMg : L.Mg = fun w => mgWords ℓ (K1.qAt Zp Np) L.N (Mg₀ w))
    (Said : ℕ → Coins Bk → Mid (Common W₀ Rc TableKey) X₀ → Prop)
    (wts : W₀ → Weights) (rnd : Rc → TableRand)
    (rest : Coins Bk → Common W₀ Rc TableKey → List Fmt.Drawn → Words Cb.Gl.E)
    (hwit : ∀ k w hd, ℓ.get (L.wit k w hd) = witAll (K1.qAt Zp Np) (sentOf (K1.qAt Zp Np).S)
      (holds2 (K1.qAt Zp Np) wts rnd) rest k w hd)
    (hfirst : ∀ key, L.first key = first (K1.qAt Zp Np).codes key)
    (JU : TestJob (Common W₀ Rc TableKey) X₀) (own₀ : X₀) (c₀ : OnBytes.Model.Verify.Chains)
    (bs : List (Block St Unit)) (hb : blocks (K1.qAt Zp Np) = some bs) {blk : Block St Cl}
    (H : StandO Zp Np pO L.thread Said wts rnd JU own₀ c₀ bs blk) (Fx : FixedO L.thread)
    (K : LettersTen L Said)
    (c2 : takesCover Bk ⟨sendPlace 2, 0⟩ (jobU ⟨K1.qAt Zp Np, 0⟩) = true)
    (n5 : (dueAt (Bk.rowsOf 1) ⟨sendPlace 5, 0⟩).e =
      (sendingPart (jobOmega ⟨K1.qAt Zp Np, 0⟩)).takes.e)
    (fall : ℕ → St → List Fmt.Drawn → Option String) :
    PlaysS L.thread Said 10 ∧ BehindS L.thread Said 10 ∧ ExchangeS L.thread Said 10 ∧
      RidesPastS L.thread Said 10 ∧ AcceptedS L.thread Said fall 10 :=
  ⟨playsS_head_O h hO hB L.thread Said wts rnd JU own₀ c₀ bs H Fx c2,
    behindS_head_O h hO L Said wts rnd JU own₀ c₀ bs hb H K,
    exchangeS_head_O h hO L Said wts rnd JU own₀ c₀ bs hb H K ℓ Mg₀ hMg,
    ridesPastS_ten L K.split Said,
    acceptedS_head_O h hO hB L.thread Said wts rnd JU own₀ c₀ bs hb H fall
      fun k s m E c u hc => says_head_O h hO hA hB L ℓ Mg₀ hl K.split hMg (fun s => (K.order s).1) wts
        rnd rest hwit hfirst c₀ bs hb H.front H.cover n5 u.1 (H.field k s m E u) c hc⟩

end ProofFile.Honest.K12.AtFile

end

#print axioms ProofFile.Honest.K12.AtFile.five_at_ten
