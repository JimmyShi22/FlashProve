-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K13/SeatedM4S.lean: kind K13 (the members' batching) at the place
"M:4", the member at which the prover sends the vector W: what follows from the structure
`K13SeatedM4` (SeatedM4.lean of this folder), said over again in the form that starts from the pair
"the thread and what is said" (`ThrS`, Honest/Thread/Said.lean). Two statements with their proofs;
no definition.

Why. `k13_seated_m4` and `k13_seated_m4_exchange` start from the thread alone (`Thr`). The debts at
a border are stated from the pair (`ExchangeS`, Honest/Thread/PaysS.lean; `ExchangeAtS`,
Honest/Thread/SharesS.lean). The pair holds the thread as its first half, so each form from the
pair follows from the form from the thread, at every Said.

Main names.
  `k13_seated_m4S`: the shares at "wrow", "pileOne" and "pinW", from the structure, at every Said.
  `k13_seated_m4_exchangeS`: `ExchangeS` at the member, from the structure and the share at the
    fourth item that the member's row owes, "pinV".

Limits. General in the thread's parameters L, as SeatedM4.lean is. The fields `pub` and `witness` of
the structure still ask their sentences wherever the thread stands, whatever is said: a caller who
has them under Said alone cannot use these statements. Nothing of Said is read. That the structure
holds at any L is not shown here.

What is not claimed. Neither is one of the library's goals. Nothing on soundness, completeness or
hiding.
-/
import Johnson.Desc.ProofFile.Honest.K13.SeatedM4
import Johnson.Desc.ProofFile.Honest.Thread.SharesS

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K13
open OnBytes OnBytes.Slice
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First (S Item)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.K13 (whereOf)

variable {Bk : ProverCoinCounts} {W₀ Rc Xi Tr X P Cells Tok : Type} {nR : ℕ}
  {L : FirstThread.Letters Bk Cl W₀ Rc Xi Tr X P Cells Tok MsgT} {b : Nat} {Z : Pub}
  {c : Chain S Cl} {arr : ℕ → ℕ → ℕ}
  {mat : Cells → Fin nR → (Fin (whereOf Z).lin.kCol → Bool) → GE} {asked : Xi → E}

/-- **From the structure, from the pair "the thread and what is said", at every Said**: behind the
member's accepted step the items "wrow", "pileOne" and "pinW" hold. -/
theorem k13_seated_m4S (h : K13SeatedM4 L b Z c arr mat asked)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop) :
    ExchangeAtS L.thread Said b Item.wrow ∧ ExchangeAtS L.thread Said b Item.pileOne ∧
      ExchangeAtS L.thread Said b Item.pinW := by
  have e := (exchangeOf_mem L.thread b _).1 (k13_seated_m4 h)
  exact ⟨exchangeAtS_of L.thread Said (e Item.wrow (by simp)),
    exchangeAtS_of L.thread Said (e Item.pileOne (by simp)),
    exchangeAtS_of L.thread Said (e Item.pinW (by simp))⟩

/-- **`ExchangeS` at the member**, from the structure and the share at "pinV", at every Said. -/
theorem k13_seated_m4_exchangeS (h : K13SeatedM4 L b Z c arr mat asked)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop)
    (hV : ExchangeAtS L.thread Said b Item.pinV) : ExchangeS L.thread Said b := by
  refine (exchangeS_iff L.thread Said).2 fun i hi => ?_
  rw [owes_tied h.tied] at hi
  rcases List.mem_cons.1 hi with rfl | hi
  · exact hV
  rcases List.mem_cons.1 hi with rfl | hi
  · exact (k13_seated_m4S h Said).2.1
  rcases List.mem_cons.1 hi with rfl | hi
  · exact (k13_seated_m4S h Said).2.2
  rcases List.mem_cons.1 hi with rfl | hi
  · exact (k13_seated_m4S h Said).1
  exact absurd hi List.not_mem_nil

end ProofFile.Honest.K13

#print axioms ProofFile.Honest.K13.k13_seated_m4S
#print axioms ProofFile.Honest.K13.k13_seated_m4_exchangeS
