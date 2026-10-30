-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/KeepsFree.lean: four hypotheses of the gathering at the first
chain's invariant at the full size do not depend on the condition `keeps`. `lettersHead`
(FirstHead.lean) takes `keeps` through its argument `Kp`. `PlaysS` and `ExchangeS` (PaysS.lean),
`ExchangeAtS` and `LaysAtS` (SharesS.lean) do not read it. So a proof of one of them at one `Kp` is
a proof at every other. KeepsMono.lean has the two hypotheses that do read `keeps`, and
FormShare.lean has `FormBehindAtS`. With these lemmas, what is proved at `fHead` (FHead.lean) can be
used at `fHeadF` (FHeadF.lean). Each proof is the hypothesis itself: the two statements unfold to
the same term. No definition.

  1  `head_playsS_kp`, `head_exchangeS_kp`, `head_exchangeAtS_kp`, `head_laysAtS_kp`   the four
     lemmas

Limits.
  * Full size only, and only under the library's hypothesis `AtMgA` at the hash function `secondHashFunction`
    (FirstAt.lean says which that is).
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.SharesS
import Johnson.Desc.ProofFile.Honest.Thread.FirstHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Strs Wit Place)
open VerifiableInference.Desc.First (Item)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)
  (Kp' : Place → TS → TS → Prop)
  (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)

/-- `PlaysS` does not depend on `Kp`. -/
theorem head_playsS_kp {b : Nat}
    (hc : PlaysS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said b) :
    PlaysS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp' w).thread Said b := hc

/-- `ExchangeS` does not depend on `Kp`. -/
theorem head_exchangeS_kp {b : Nat}
    (hc : ExchangeS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said b) :
    ExchangeS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp' w).thread Said b := hc

/-- `ExchangeAtS` does not depend on `Kp`. -/
theorem head_exchangeAtS_kp {b : Nat} {i : Item}
    (hc : ExchangeAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said b i) :
    ExchangeAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp' w).thread Said b i := hc

/-- `LaysAtS` does not depend on `Kp`. -/
theorem head_laysAtS_kp {b : Nat} {c : RiderCl (Local W₀ Rc ProofFile.Inst Tr) TS}
    (hc : LaysAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said b c) :
    LaysAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp' w).thread Said b c := hc

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.head_playsS_kp
#print axioms ProofFile.Honest.FirstThread.head_exchangeS_kp
#print axioms ProofFile.Honest.FirstThread.head_exchangeAtS_kp
#print axioms ProofFile.Honest.FirstThread.head_laysAtS_kp
