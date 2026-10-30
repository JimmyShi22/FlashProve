-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/GatherSilentK9.lean: the gathering `owesS_framesI`
(GatherAboveT.lean) for a prover that has no side at a place of the kind K9, with fewer hypotheses
on what is played and exchanged. No definition.

  1  `owesNil_full`, `owesNil_control`, `rows_owe_nil_354`, `rows_owe_nil_back`   a closed test by
     Lean's kernel on the written table of items: the row of number 354 and the rows of the 25
     numbers 14 l + nAt l + 6 owe no item. The negative test: with 5 for 6 the test fails
  2  `owesS_framesJ`   `owesS_framesI` with these changes in its hypotheses:
     * `hno` comes: the prover's list has no side at a place of the kind K9
     * `hPback` is asked at the 25 numbers 14 l + nAt l + 5 (kind K10) and no longer at the 75
       numbers 14 l + nAt l + 2, + 4, + 6 (kind K9): there `playsS_k9_silent` (K9Silent.lean) proves
       `PlaysS`
     * `hXback` is asked at c = 2, 4, 5 and no longer at c = 6, and `hX354` goes: these rows owe
       nothing, so the hypotheses asked nothing
     One call of `owesS_framesI`, whose statement is not changed.

The statement of `owesS_framesJ` is that of `owesS_framesI`, changed by a program at these four
places.

Limits.
  * Those of GatherAboveT.lean and K9Silent.lean. `hno` and a hypothesis that the prover's list has
    a side at a place of the kind K9 exclude each other at one prover.
  * "It plays" is not "it is accepted": `OwesS` does not say that a side stands at a place, nor that
    a step accepts what was played.
  * What is exchanged at the 50 numbers 14 l + nAt l + 2 and + 4 stays a hypothesis (`hXback`).
  * The end and the hypotheses on what is played, exchanged and laid are implications from the
    invariant. Nothing here shows that the invariant holds at any state of a run.
  * The shares of the item `pinW` are proved beneath this file through `cell_pinW`
    (Honest/Thread/CellsByKindC.lean), which is `ridesPastAt_pinW` (Honest/Thread/HeadPinW.lean) and
    holds because the item reads neither the state nor the oracles: at these parameters the decoder
    of the stored table is a constant, so the item says nothing about the stored table.
  * Full size only, under the library's hypothesis `AtMgA` at the hash function `secondHashFunction`
    (FirstAt.lean says which that is).
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.GatherAboveT
import Johnson.Desc.ProofFile.Honest.Thread.K9Silent

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Strs Wit Place KindName)
open VerifiableInference.Desc.First (Item)
open VerifiableInference.Desc.K2.Honest (carryExact)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T parts4)

/-! ## 1 The rows that owe nothing -/

set_option maxRecDepth 1000000 in
/-- The rows of number 354 and of the numbers 14 l + nAt l + 6 owe no item. -/
theorem owesNil_full : ((354 :: (List.range 25).map fun l => 14 * l + IM.nAt l + 6).all fun b =>
    (FirstRows.rows P5J.At.links P5J.At.ps b).owes.isEmpty) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A negative test: with 5 in the place of 6 the same test fails. -/
theorem owesNil_control : ((354 :: (List.range 25).map fun l => 14 * l + IM.nAt l + 5).all fun b =>
    (FirstRows.rows P5J.At.links P5J.At.ps b).owes.isEmpty) = false := by
  decide +kernel

/-- The test at number 354. -/
theorem rows_owe_nil_354 : (FirstRows.rows P5J.At.links P5J.At.ps 354).owes = [] :=
  List.isEmpty_iff.1 (List.all_eq_true.1 owesNil_full 354 List.mem_cons_self)

/-- The test at the third sub-protocol behind a segment's batching. -/
theorem rows_owe_nil_back {l : Nat} (hl : l < 25) :
    (FirstRows.rows P5J.At.links P5J.At.ps (14 * l + IM.nAt l + 6)).owes = [] :=
  List.isEmpty_iff.1 (List.all_eq_true.1 owesNil_full _
    (List.mem_cons_of_mem _ (List.mem_map.2 ⟨l, List.mem_range.2 hl, rfl⟩)))

/-! ## 2 The gathering -/

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **`owesS_framesI` for a prover without a side at K9.** -/
theorem owesS_framesJ (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (w : Local W₀ Rc ProofFile.Inst Tr) {ν : Nat}
    {st : Nat → TS → Prop} {R : Nat → Option OnBytes.Model.Forest.Heard → Prop}
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (hSaid : ∀ b k m, Said b k m → SaidOk b k m)
    {Bs : ProofFile.PureBase} (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs)
    (hσ : ∀ s s', Johnson.Desc.First.ForkMerge.Returns.K11Keeps (K11.parOf Zp Bs.G₀) s s' →
      st 24 s → st 24 s')
    (hb₀ : b₀ = 339) (noHalf : ∀ g ∈ H.first, g.place.kind ≠ KindName.frame) {Vh : Nat}
    (hno : ∀ g ∈ H.first, g.place.kind ≠ KindName.K9)
    (hhalf : H.first.find? (fun g => g.place == IM.k7Place) = some (replyHalf 24 1 Vh))
    {L : Letters Bk ProofFile.Cl W₀ Rc ProofFile.Inst Tr X ProofFile.InstPub (CellsM OnBytes.Flat.numsFull)
      P5J.At.Tok MsgT}
    (hL : L = lettersHead h H Q test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ b₀ Vd
      (ridersOf (csHead ν st R))
      (kpBy (fHeadI Zp cF Bs.G₀ P1L20.bearing (K11.parOf Zp Bs.G₀) (H2U.p12OfMade Zp.made)
        (VerifiableInference.Desc.K13.whereOf Zp) h.𝔇.pubD)) w)
    (htst : ∀ l, l < 25 → ∀ blk, cF.blocksInOrder[14 * l + IM.nAt l + 3]? = some blk → ∀ s rs cols s' n,
      blk.step 0 s rs cols = .ok (s', n) → test l s = none)
    (hPhear : ∀ l, l < 25 → ∀ i, i < IM.nAt l → PlaysS L.thread Said (14 * l + i + 2))
    (hPback : ∀ l, l < 25 → PlaysS L.thread Said (14 * l + IM.nAt l + 5))
    (hP353 : PlaysS L.thread Said 353) (hP354 : PlaysS L.thread Said 354)
    (hP355 : PlaysS L.thread Said 355) (hP356 : PlaysS L.thread Said 356)
    (hXhear : ∀ l, l < 25 → ∀ i, i < IM.nAt l →
      ∀ j : Item, j ∈ (L.thread.row (14 * l + i + 2)).owes →
      (j ∈ L.thread.opened (14 * l + i + 2) →
        (∀ m t, j ≠ Item.pin m t) ∧ j ≠ Item.pinI ∧ j ≠ Item.pinW ∧
        ∀ m q, q ∈ parts4 → j ≠ Item.constr m q) →
      ExchangeAtS L.thread Said (14 * l + i + 2) j)
    (hXback : ∀ l, l < 25 → ∀ c, c = 2 ∨ c = 4 ∨ c = 5 →
      ∀ j : Item, j ∈ (L.thread.row (14 * l + IM.nAt l + c)).owes →
      (j ∈ L.thread.opened (14 * l + IM.nAt l + c) →
        (∀ m t, j ≠ Item.pin m t) ∧ j ≠ Item.pinI ∧ j ≠ Item.pinW ∧
        ∀ m q, q ∈ parts4 → j ≠ Item.constr m q) →
      ExchangeAtS L.thread Said (14 * l + IM.nAt l + c) j)
    (hX353 : ∀ j : Item, j ∈ (L.thread.row (353)).owes →
      (j ∈ L.thread.opened (353) →
        (∀ m t, j ≠ Item.pin m t) ∧ j ≠ Item.pinI ∧ j ≠ Item.pinW ∧
        ∀ m q, q ∈ parts4 → j ≠ Item.constr m q) →
      ExchangeAtS L.thread Said (353) j)
    (hX355 : ∀ j : Item, j ∈ (L.thread.row (355)).owes →
      (j ∈ L.thread.opened (355) →
        (∀ m t, j ≠ Item.pin m t) ∧ j ≠ Item.pinI ∧ j ≠ Item.pinW ∧
        ∀ m q, q ∈ parts4 → j ≠ Item.constr m q) →
      ExchangeAtS L.thread Said (355) j)
    (hX356 : ∀ j : Item, j ∈ (L.thread.row (356)).owes →
      (j ∈ L.thread.opened (356) →
        (∀ m t, j ≠ Item.pin m t) ∧ j ≠ Item.pinI ∧ j ≠ Item.pinW ∧
        ∀ m q, q ∈ parts4 → j ≠ Item.constr m q) →
      ExchangeAtS L.thread Said (356) j)
    (hnx : LaysAtS L.thread Said 345 (riderHead 346 346 fun a => a.F.next = ν))
    (hs : LaysAtS L.thread Said 345 ⟨346, 347, fun _ _ s => st 24 s⟩)
    (hstl : ∀ l, l < 24 →
      LaysAtS L.thread Said (14 * l + 8) ⟨14 * l + 9, 14 * l + 9, fun _ _ s => st l s⟩)
    (hatt : ∀ g, g < 12 → LaysAtS L.thread Said (14 * (2 * g + 1) + 3)
      (riderAtt (14 * (2 * g + 1) + 4) (14 * (2 * g + 1) + 9) fun a => R g a.g)) :
    OwesS L.thread Said := by
  subst hL
  exact owesS_framesI h H Q test item n₁ n₂ b₀ Vd w Said hSaid hB hσ hb₀ noHalf hhalf rfl htst
    hPhear
    (fun l hl j hj => by
      rcases hj with rfl | rfl | rfl | rfl
      · exact playsS_k9_silent h H Q test _ item n₁ n₂ b₀ Vd _ _ w Said hno hl (Or.inl rfl)
      · exact playsS_k9_silent h H Q test _ item n₁ n₂ b₀ Vd _ _ w Said hno hl
          (Or.inr (Or.inl rfl))
      · exact hPback l hl
      · exact playsS_k9_silent h H Q test _ item n₁ n₂ b₀ Vd _ _ w Said hno hl
          (Or.inr (Or.inr rfl)))
    hP353 hP354 hP355 hP356 hXhear
    (fun l hl c hc j hj hi => by
      rcases hc with rfl | rfl | rfl | rfl
      · exact hXback l hl 2 (Or.inl rfl) j hj hi
      · exact hXback l hl 4 (Or.inr (Or.inl rfl)) j hj hi
      · exact hXback l hl 5 (Or.inr (Or.inr rfl)) j hj hi
      · exact absurd
          (show j ∈ (FirstRows.rows P5J.At.links P5J.At.ps (14 * l + IM.nAt l + 6)).owes from hj)
          (by rw [rows_owe_nil_back hl]; exact List.not_mem_nil))
    hX353
    (fun j hj _ => absurd
      (show j ∈ (FirstRows.rows P5J.At.links P5J.At.ps 354).owes from hj)
      (by rw [rows_owe_nil_354]; exact List.not_mem_nil))
    hX355 hX356 hnx hs hstl hatt

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.owesNil_full
#print axioms ProofFile.Honest.FirstThread.owesNil_control
#print axioms ProofFile.Honest.FirstThread.rows_owe_nil_354
#print axioms ProofFile.Honest.FirstThread.rows_owe_nil_back
#print axioms ProofFile.Honest.FirstThread.owesS_framesJ
