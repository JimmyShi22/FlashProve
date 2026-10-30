-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/FHeadI.lean: one more layer of the condition `keeps` of the
first chain's invariant at the full size. `fHeadI` is `fHeadH` (FHeadH.lean) with one relation
beside it at the kind K7 (the next token's sub-protocol, number 338): the state after the step is
the one that the sub-protocol's own decision returns (`H1Keeps`, Honest/K7/Keeps.lean).

Why. The clause of `fHead` at K7 (`K7KeepsAt`, Honest/K7/KeepsAt.lean) has a state `m` between:
`H1Keeps` from the state before the step to `m`, then `keepsOpened`
(Honest/Law/NoHouse/OpenedKeeps.lean) from `m` to the state after. `keepsOpened` is a disjunction.
Its first arm says that the two states are equal. Its second arm does not say in which segment the
chain is after the step. It does not say which arm holds at the output head's segment. The item
`carry 23` is read through the library's `doorZ` (Johnson/Top/H0/K2Caller/CarryClosed.lean), which
looks at just that. With the relation the item passes over number 338 (K7CarryCell.lean). Every
statement at `fHeadH` stays as it is. `cellI_of_H` carries a cell of the column `hR` of the
gathering from `fHeadH` to `fHeadI`.

  1  `relsReply`, `fHeadI`   two definitions
  2  `kpBy_fHeadI`   `fHeadI` implies `fHeadH`
  3  `cellI_of_H`   a cell of the column `hR` at `fHeadH` is one at `fHeadI`

Limits.
  * That `keeps` := `fHeadI` holds after a sub-protocol's accepting step is not proved here. For the
    new relation it is proved in ReplyKeptPaid.lean.
  * Full size only, under the library's hypothesis `AtMgA` at the hash function `secondHashFunction`
    (FirstAt.lean says which that is).
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.FHeadH

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Strs Wit Place KindName)
open VerifiableInference.Desc.First (Item)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)

/-! ## 1 The definitions -/

/-- What the item `carry` needs of `keeps` beyond `fHeadH`: at K7 the state after the step is the
one that the sub-protocol's own decision returns (`H1Keeps`, Honest/K7/Keeps.lean). Everywhere else
it is "True". It is a definition: a part of a clause of `keeps`. -/
def relsReply (G : ProofFile.Ground) : KindName → TS → TS → Prop
  | .K7 => H1Keeps G.W.H.tl G.W.hS.V
  | _ => fun _ _ => True

/-- `fHeadH` with this relation beside it. It is a definition: it fills an argument of the
invariant. -/
def fHeadI (Zp : ProofFile.Pub) (cF : Chain TS ProofFile.Cl) (G : ProofFile.Ground) (take : Nat → Bool)
    (P11 : Johnson.Desc.First.ForkMerge.HeadMergeP) (p12 : VerifiableInference.Desc.K12.P12)
    (P13 : VerifiableInference.Desc.K13.Where) (D : VerifiableInference.Desc.First.PubData) :
    KindName → Place → TS → TS → Prop :=
  fun κ p s s' => fHeadH Zp cF G take P11 p12 P13 D κ p s s' ∧ relsReply G κ s s'

/-- `fHeadI` implies `fHeadH`. -/
theorem kpBy_fHeadI {Zp : ProofFile.Pub} {cF : Chain TS ProofFile.Cl} (G : ProofFile.Ground) (take : Nat → Bool)
    (P11 : Johnson.Desc.First.ForkMerge.HeadMergeP) (p12 : VerifiableInference.Desc.K12.P12)
    (P13 : VerifiableInference.Desc.K13.Where) (Dp : VerifiableInference.Desc.First.PubData) :
    ∀ p s s', kpBy (fHeadI Zp cF G take P11 p12 P13 Dp) p s s' →
      kpBy (fHeadH Zp cF G take P11 p12 P13 Dp) p s s' :=
  fun _ _ _ hk => hk.1

/-! ## 2 At the invariant -/

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)
  (G : ProofFile.Ground) (take : Nat → Bool)
  (P11 : Johnson.Desc.First.ForkMerge.HeadMergeP) (p12 : VerifiableInference.Desc.K12.P12)
  (P13 : VerifiableInference.Desc.K13.Where)
  (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)

/-- A cell of the column `hR` at `fHeadH` is one at `fHeadI`. -/
theorem cellI_of_H {b : Nat} {i : Item}
    (hc : RidesPastAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHeadH Zp cF G take P11 p12 P13 h.𝔇.pubD)) w).thread Said
      b i) :
    RidesPastAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHeadI Zp cF G take P11 p12 P13 h.𝔇.pubD)) w).thread Said
      b i :=
  head_ridesPastAtS_mono h H Q test carryX item n₁ n₂ b₀ Vd Rd
    (kpBy (fHeadH Zp cF G take P11 p12 P13 h.𝔇.pubD)) w
    (kpBy (fHeadI Zp cF G take P11 p12 P13 h.𝔇.pubD))
    (kpBy_fHeadI G take P11 p12 P13 h.𝔇.pubD) Said hc

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.kpBy_fHeadI
#print axioms ProofFile.Honest.FirstThread.cellI_of_H
