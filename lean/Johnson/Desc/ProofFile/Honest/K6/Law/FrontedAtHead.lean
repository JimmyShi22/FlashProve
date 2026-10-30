-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K6/Law/FrontedAtHead.lean.
WHAT IT IS NOT. EVERY STATEMENT IS CONDITIONAL ON THE HYPOTHESIS P5J.AtMgA. (The library has a
member of it under four premises on the three public files: P5J.head_exists_at_name,
Johnson/P5J/HeadExistsAtName.lean; nothing here calls that.) That the thread holds at any run is
shown nowhere. At the format's second hash function OnBytes.secondHashFunction, the full size, the goals' scope alone.
K6Fronted is a structure of premises: to meet it is no property of the protocol. Nothing on
soundness, on completeness or on hiding.
WHAT IT IS. WHO PAYS THE STRUCTURE K6Fronted (Honest/K6/Law/Accepted.lean) AT THE FIRST CHAIN's
THREAD AT THE LIBRARY's OWN LETTERS (lettersHead, Honest/Thread/FirstHead.lean), at all its
arguments. This file alone of the sub-protocol's laws stands over these letters; the laws stay
general in the thread. Calls and ties: no new mathematics.
  digitsPlace_at_head     the place of the lookup on the digits, and its shape: public data.
  k6Front_at_head    wherever the thread holds at border 341 the verifier's state is ready
                     (K6Front), with just the room behind the hearing that the lookup on the digits
                     takes.
  k6Fronted_at_head  number 341 of the first chain's flat list, with K6Fronted at it, at every
                     sentence Said: nothing of Said is spent.
BY WHICH ROADS. No mark, where the chain stands, "what the lookup on the calls left" and "a token is
heard": the thread's clause on the promise, by headFrontItems_of_thr (Honest/K6/Law/FrontAt.lean).
The state's own test on the request: the thread gives the library's Reach (thr_reach,
Honest/Thread/ReachFacts.lean), and startOk_reached (Kinds/Law/K6WayUpAtSeat.lean) reads it there.
The two tests on public numbers: theorems in the goals' scope.
CALLED: digits_place, k6Pub_in_scope (Kinds/Law/K6PubInScope.lean), headKeysFit_at_place
(Kinds/Law/K6KeysInScope.lean), k6_member_at_mg, startOk_reached, P5J.flat_ok (P5J/FoldJ1.lean),
headFrontItems_of_thr, thr_reach, stand_at_k6, k6Front_of_items.

-/
import Johnson.Desc.ProofFile.Honest.K6.Law.Accepted
import Johnson.Desc.ProofFile.Honest.K6.Law.FrontAt
import Johnson.Desc.K6.Honest.Law.FrontOfItems
import Johnson.Desc.Kinds.Law.K6KeysInScope
import Johnson.Desc.ProofFile.Honest.Thread.ReachFacts
import Johnson.P5J.FoldJ1

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K6
open VerifiableInference.Desc (Chain Place Strs Block Claim)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.Kinds.Head (startOk)
open VerifiableInference.Desc.Kinds.Head.Law (K6Front k6Front_of_items stand_at_k6)
open VerifiableInference.Desc.First.Look (placeAt)
open OnBytes.Model.Forest (elems)
open ProofFile.Honest.FirstThread (Script WtF lettersHead)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- The place of the lookup on the digits of the head's smallness test, and its shape: public data.
CONDITIONAL on the same hypothesis as all of this file. (The library's digits_place,
Kinds/Law/K6PubInScope.lean, which is called, says more: the shape is the plan's own, and the
place's first slot is 2,168.) -/
theorem digitsPlace_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    ∃ p8 h8, placeAt (P5J.At.X Zp) 24 true = some p8 ∧ p8.shape = some h8 := by
  obtain ⟨p, e, s, _⟩ :=
    VerifiableInference.Desc.Kinds.Head.Law.InScope.digits_place h.scope h.reads h.pubOne
  exact ⟨p, _, e, s⟩

/-- **WHEREVER THE FIRST CHAIN's THREAD HOLDS AT BORDER 341, AT THE LIBRARY's OWN LETTERS, THE
VERIFIER's STATE IS READY.** CONDITIONAL on the one hypothesis that ties the table's letters to the
proof file's description. p8, h8: pinned by the two equations; one pair serves all states. -/
theorem k6Front_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr) :
    ∃ p8 h8, placeAt (P5J.At.X Zp) 24 true = some p8 ∧ p8.shape = some h8 ∧
      ∀ (k : Coins Bk) (s : TS) (μ : Mid (Local W₀ Rc ProofFile.Inst Tr) X) (E : Env),
        Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread 341 k s μ E →
        K6Front (P5J.At.X Zp) (elems h8) s := by
  obtain ⟨p8, h8, e8, s8⟩ := digitsPlace_at_head h
  refine ⟨p8, h8, e8, s8, fun k s μ E hT => ?_⟩
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have eW : Bs.G₀.W = P5J.At.X Zp := O.W
  obtain ⟨blk, hblk, _⟩ := P4.k6_member_at_mg h.toAtMg
  obtain ⟨hlt, _⟩ := List.getElem?_eq_some_iff.mp hblk
  obtain ⟨hm, R⟩ := headFrontItems_of_thr
    (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) h.𝔇 rfl rfl rfl rfl hT
  have hr := FirstThread.thr_reach h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w
    (Nat.le_of_lt hlt) hT
  have hst : startOk (P5J.At.X Zp) s = true :=
    eW ▸ P4.startOk_reached h.scope h.reads O (P5J.flat_ok h.toAtMg) hr hm
  obtain ⟨p8', h8', e8', s8', F⟩ := k6Front_of_items (P5J.At.X Zp) hm (stand_at_k6 R.shape) R.left
    R.tokenSmall hst
    (VerifiableInference.Desc.Kinds.Head.Law.InScope.k6Pub_in_scope h.scope h.reads h.pubOne)
    (VerifiableInference.Desc.Kinds.Head.Law.InScope.headKeysFit_at_place h.scope h.reads
      h.pubOne)
  obtain rfl : p8' = p8 := Option.some.inj (e8'.symm.trans e8)
  obtain rfl : h8' = h8 := Option.some.inj (s8'.symm.trans s8)
  exact F

/-- **THE STRUCTURE K6Fronted AT THE LIBRARY's OWN LETTERS**, at every letter Said: nothing of Said
is spent here. CONDITIONAL on the same hypothesis. blk, p8, h8: each pinned by an equation in the
end. -/
theorem k6Fronted_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop) :
    ∃ (blk : Block TS ProofFile.Cl) (p8 : VerifiableInference.Desc.First.Look.P)
      (h8 : OnBytes.Model.Forest.Shape), cF.blocksInOrder[341]? = some blk ∧
      placeAt (P5J.At.X Zp) 24 true = some p8 ∧ p8.shape = some h8 ∧
      K6Fronted (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 341
        (P5J.At.X Zp) (elems h8) blk := by
  obtain ⟨blk, hblk, M⟩ := P4.k6_member_at_mg h.toAtMg
  obtain ⟨p8, h8, e8, s8, F⟩ := k6Front_at_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w
  exact ⟨blk, p8, h8, hblk, e8, s8, M, fun k s r E hT => F k s r E hT.1⟩

end ProofFile.Honest.K6

#print axioms ProofFile.Honest.K6.digitsPlace_at_head
#print axioms ProofFile.Honest.K6.k6Front_at_head
#print axioms ProofFile.Honest.K6.k6Fronted_at_head
