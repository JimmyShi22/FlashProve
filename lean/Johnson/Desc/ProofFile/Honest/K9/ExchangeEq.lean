-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/ExchangeEq.lean: THE STATEMENT "EXCHANGE" (`ExchangeS`, Honest/Thread/PaysS.lean) AT THE SUB-PROTOCOL "THE ONE
EQUATION" OF EACH OF THE 25 SEGMENTS OF THE FIRST CHAIN: where the sub-protocol's step accepts, every item that the table's row owes there
holds behind it. At the first chain's thread under the library's hypothesis `AtMgA`, every parameter of the thread free; and at the first
chain's thread of the online part as a named term (`firstThread`, Honest/Thread/TheFirstThread.lean).

The row owes one item there, "row l equation": the row that the sub-protocol has laid on the segment's group holds of the witness
(`eq_owes`, Honest/K9/ExchangeByKind.lean: a closed fact on the written lists, by Lean's kernel). That item's share is
`exchange_rowEq_head` (Honest/K9/EqExchangeHead.lean). This file joins the two by `exchangeS_iff` (Honest/Thread/SharesS.lean) and passes from
`SaidOk` to a variable `Said` by `exchangeAtS_mono` (Honest/Thread/SaidMono.lean). No definition is made.

  **`k9_exchangeS_eq`**         l < 25, `Said` gives `SaidOk`: `ExchangeS` of the thread of `lettersHead …` at 14 l + `IM.nAt l` + 4
  **`k9_exchangeS_eq_first`**   the same at `firstThread h parts w`: the thread's parameters are passed as they stand in that file

THE PREMISES: the library's hypothesis h (at `firstThread`: the head at the return) · l < 25 · `hSaid`: what is said at a border gives `SaidOk` there.
WHAT IS SPENT OF THE INVARIANT IN FRONT (inside `exchange_rowEq_head`): the open item "total l", whose sentence says that the batched form holds of
the witness; the public tests that are open at that border; that the state is reached.

Limits. The step's yes is a premise of `ExchangeS` itself. That the thread's invariant and `Said` hold together in front of this sub-protocol at
any run is not proved here: where they never do, the theorems say nothing. Who makes the item "total l" hold one border in front is not treated
here. The full size and the hash function `secondHashFunction` alone: the hypothesis's. This file proves no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K9.ExchangeByKind
import Johnson.Desc.ProofFile.Honest.Thread.TheFirstThread

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- **"Exchange" at "the one equation" of each of the 25 segments.** -/
theorem k9_exchangeS_eq (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (hSaid : ∀ b k m, Said b k m → SaidOk b k m) (l : Nat) (hl : l < 25) :
    ExchangeS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said (14 * l + IM.nAt l + 4) := by
  refine (exchangeS_iff _ _).2 fun i hi => ?_
  have hi' : i ∈ (FirstRows.rows P5J.At.links P5J.At.ps (14 * l + IM.nAt l + 4)).owes := hi
  rw [eq_owes l hl] at hi'
  obtain rfl := List.mem_singleton.1 hi'
  exact exchangeAtS_mono _ hSaid (exchange_rowEq_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hl)

end

variable {W₀ Rc Tr X₀ X : Type} {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}

/-- **The same at the first thread.** -/
theorem k9_exchangeS_eq_first (h : HeadAtReturn files A) (parts : FirstThreadParts A) (w : Local W₀ Rc ProofFile.Inst Tr)
    (Said : Nat → Coins A.B → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (hSaid : ∀ b k m, Said b k m → SaidOk b k m) (l : Nat) (hl : l < 25) :
    ExchangeS (firstThread h parts w) Said (14 * l + IM.nAt l + 4) :=
  k9_exchangeS_eq h.head A.H parts.script _ _ _ _ _ _ _ _ _ w Said hSaid l hl

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.k9_exchangeS_eq
#print axioms ProofFile.Honest.K9.k9_exchangeS_eq_first
