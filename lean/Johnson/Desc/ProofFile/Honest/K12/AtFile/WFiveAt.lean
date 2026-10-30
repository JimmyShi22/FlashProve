-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/WFiveAt.lean: the five statements at the last chain's proximity
test, at number 2 of the thread of `lettersLast`, in one: `PlaysS`, `BehindS`, `ExchangeS`, `RidesPastS`,
`AcceptedS` (Thread/PaysS.lean).

  `FiveAt`         the five, at one number
  `five_at_W`      they hold at the letters, where `LetterAtW`'s three letters, `StandAtW` and the
                   letters' order, rides and keeps hold

What stays a premise. hPL: the thread's promise is `fillAt`. H₀: the letters (`letter_at_filling`,
WFilling.lean, at the base prover). S: what a stand owes (`StandAtW`, WAccepted.lean).
hnext: the letters' order, rides and keeps behind the block. hB: the book is the maker's.

Limits.
- NOT IN FRONT OF A LAW OVER COINS: the thread's pair is a premise, the five its ends.
- AT THE FILLING, NOT READ THROUGH: the half is `proverSideOfProximityTest` behind the guard at the base prover.
- That a stand is reached is not said. If no stand exists the five say nothing.
- Nothing on completeness of the whole chain, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WFive
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WLetter

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtFile
open ProofFile.Honest
open ProofFile.Honest.K12
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.K12 (T12)
open VerifiableInference.Desc.K12.Seat (enterOwn leaveOwn)
open VerifiableInference.Desc.Third (S₃ P₁₄ SharedOut)
open VerifiableInference.Desc.Last (fillAt)
open Johnson.G (proofSendsFull)
open ProofFile.Honest.K12.AtProof (fourOf idleT12)
open ProofFile.Honest.K12.Light (ManyJob)
open ProofFile.Honest.LastThread (lettersLast)
open ToldDesc (ownAt)
open P5J (F0T TS)

/-- **The five statements at one number.** -/
structure FiveAt {S Cl V W X Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk S Cl V W X Pb)
    (Said : ℕ → Coins Bk → Mid W X → Prop) (fall : ℕ → S → List Fmt.Drawn → Option String)
    (b : ℕ) : Prop where
  plays : PlaysS T Said b
  behind : BehindS T Said b
  exchange : ExchangeS T Said b
  rides : RidesPastS T Said b
  accepted : AcceptedS T Said fall b

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {Bk : ProverCoinCounts} {W₀ Rc Tr X₀ X Wt : Type}
  (H : Prover W₀ Rc ProofFile.Inst OnBytes.TableKey Tr X₀ X)
  (N : VerifiableInference.Desc.Shared.NumbersS)
  (Mg : Local W₀ Rc ProofFile.Inst Tr →
    VerifiableInference.Desc.Shared.MeaningS Desc.K14.St (ProofFile.InstPub × TS) Wt)
  (ML : VerifiableInference.Desc.Last.MeaningL S₃ Wt)
  (PL : VerifiableInference.Desc.Last.PromMeaningL Desc.K14.St S₃ (ProofFile.InstPub × TS))
  (order : S₃ → Prop) (taken : List Fmt.TreeSource)
  (ends : Coins Bk → Local W₀ Rc ProofFile.Inst Tr → List Fmt.Drawn →
    (ProofFile.InstPub × TS) × Desc.K14.St)
  (wit : Coins Bk → Local W₀ Rc ProofFile.Inst Tr → List Fmt.Drawn → Wt)
  (table : Fmt.TreeSource → Coins Bk → Local W₀ Rc ProofFile.Inst Tr → List Fmt.Drawn →
    VerifiableInference.Desc.Place × Table)
  (fixed : Fmt.TreeSource → ℕ) (item n₁ n₂ : ℕ) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : ℕ → Local W₀ Rc ProofFile.Inst Tr → S₃ → Prop)
  (Kp : VerifiableInference.Desc.Place → S₃ → S₃ → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)

/-- **The five at the last chain's test.** -/
theorem five_at_W (h : P5J.AtMg OnBytes.secondHashFunction Z D r Zp Np cF)
    (hB : bookWhole (F0T OnBytes.secondHashFunction Zp Np cF) proofSendsFull.1 proofSendsFull.2.1
      proofSendsFull.2.2 (mergesByName (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder) = .ok Bk)
    (Said : ℕ → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (A : ManyJob (Local W₀ Rc ProofFile.Inst Tr) X) (hp : A.p = (fourOf Np).W) (f : Addr × ℕ)
    (hfr : A.fresh = some f) (hl : A.mems.length = 3) (hd : A.trees.map (·.1) = [13, 22, 22])
    {p : P₁₄} {R : List Fmt.DeclaredRound} {hand : ProofFile.InstPub × TS → Option VerifiableInference.Desc.Last.Handed}
    {ended : Desc.K14.St → Option SharedOut} (hPL : PL = fillAt p R hand ended)
    (H₀ : LetterAtW (F0T OnBytes.secondHashFunction Zp Np cF)
      (lettersLast Zp Np cF H N Mg ML PL order taken ends wit table fixed item n₁ n₂ Vd Rd Kp w).thread
      2 A enterOwn leaveOwn ((ownAt Np).retype : Block S₃ ProofFile.Cl) idleT12)
    (S : StandAtW (F0T OnBytes.secondHashFunction Zp Np cF)
      (lettersLast Zp Np cF H N Mg ML PL order taken ends wit table fixed item n₁ n₂ Vd Rd Kp
        w).thread Said 2 A)
    (hnext : ∀ k s m E ds y cols s',
      ThrS (lettersLast Zp Np cF H N Mg ML PL order taken ends wit table fixed item n₁ n₂ Vd Rd Kp
        w).thread Said 2 k s m E →
      drawsFit ((ownAt Np).retype : Block S₃ ProofFile.Cl).rounds ds = true →
      (lettersLast Zp Np cF H N Mg ML PL order taken ends wit table fixed item n₁ n₂ Vd Rd Kp
        w).thread.Stepped ((ownAt Np).retype : Block S₃ ProofFile.Cl) k s m E ds y cols s' →
      order s' ∧ Rd 3 y.2.st.input s' ∧ ∀ q, VerifiableInference.Desc.Last.lastPlaces[2]? = some q →
        Kp q s s')
    (fl : ℕ → S₃ → List Fmt.Drawn → Option String) :
    FiveAt (lettersLast Zp Np cF H N Mg ML PL order taken ends wit table fixed item n₁ n₂ Vd Rd Kp
      w).thread Said fl 2 := by
  have hplan : (VerifiableInference.Desc.K12.proximityTestKind VerifiableInference.Desc.K12.guardedProximityTestParts
      A.toRun.toTest.p : Block T12 Unit).planOk = true :=
    (public_head_W h A hp (by rw [hfr]; rfl)).2.2.1
  exact
    { plays := playsS_at_W h H₀ S.field hB hp f hfr hl S.old S.trees
      behind := behindS_at_W _ Said hPL H₀.member A.toRun.toTest H₀.seat hplan hnext
      exchange := exchangeS_at_W _ Said
      rides := ridesPastS_at_W _ Said
      accepted := acceptedS_at_W h H₀ S hB hp f hfr hl hd fl }

end ProofFile.Honest.K12.AtFile

#print axioms ProofFile.Honest.K12.AtFile.FiveAt
#print axioms ProofFile.Honest.K12.AtFile.five_at_W
