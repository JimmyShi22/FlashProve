-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/NoStopOfSenders.lean: no stop at a member of the first chain that
sends a new tree. Only the kinds K1, K2 and K12 send there, by a closed test on the written cut of the
first chain, and the head ties the chain to that cut. So it is enough that the halves of these three
kinds have no stop.

  `RowQuiet`   no part of a list has a stop
  `rowStop_none`, `chainStop_none`   a quiet row does not stop
  `senders_first`, `sender_kind_first`   the closed test, and the kind of a sending sub-protocol
  `noStop_first`   no stop at a member with a new tree, at the thread of `lettersHead`

This file proves nothing about soundness, completeness, hiding or any other property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.K7.AtSeat
import Johnson.Desc.ProofFile.Honest.Thread.FirstHead
import Johnson.Road.K4.K4HeadWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Block Chain Strs Place KindName)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.PlanWritten (cutOf cutFirstFull toldRounds)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)

/-- **No part of the list has a stop.** -/
def RowQuiet {V W X : Type} (ps : List (Part V W X)) : Prop :=
  ∀ p ∈ ps, (∀ a b, p.bad a b = none) ∧ ∀ v a b, p.hid v a b = none

theorem part_stop_none {V W X : Type} {p : Part V W X} (h1 : ∀ a b, p.bad a b = none)
    (h2 : ∀ v a b, p.hid v a b = none) (v : Option V) (loc ds : List Fmt.Drawn) :
    p.stopAt v loc ds = none := by
  unfold Part.stopAt
  cases v with
  | none => simp [h1]
  | some x => simp [h1, h2]

/-- **A quiet row does not stop.** -/
theorem rowStop_none {V W X : Type} (v : Option V) : ∀ (ps : List (Part V W X))
    (loc ds : List Fmt.Drawn), RowQuiet ps → rowStopAt v ps loc ds = none
  | [], _, _, _ => rfl
  | p :: ps, loc, ds, h => by
    obtain ⟨h1, h2⟩ := h p List.mem_cons_self
    unfold rowStopAt
    rw [part_stop_none h1 h2, rowStop_none v ps _ _ fun q hq => h q (List.mem_cons_of_mem _ hq)]
    rfl

/-- **Where the halves at the place are quiet, the chain of one sub-protocol does not stop.** -/
theorem chainStop_none {S Cl V W Y : Type} {v : Option V} {blk : Block S Cl} {hs : List (Placed V W Y)}
    (h : ∀ x ∈ hs, x.place = blk.place → RowQuiet x.parts) (loc ds : List Fmt.Drawn) :
    chainStopAt v [blk] hs loc ds = none := by
  unfold chainStopAt
  dsimp only
  cases hf : hs.find? (fun x => x.place == blk.place) with
  | none => rfl
  | some x =>
    have hx := List.mem_of_find?_eq_some hf
    have hp0 : (x.place == blk.place) = true := (List.find?_eq_some_iff_append.1 hf).1
    have hp : x.place = blk.place := beq_iff_eq.1 hp0
    rw [Option.bind_some, rowStop_none v x.parts _ _ (h x hx hp)]
    rfl

set_option maxRecDepth 1000000 in
/-- **Of the written cut of the first chain, only the kinds K1, K2 and K12 send.** -/
theorem senders_first : (cutFirstFull.all fun e =>
    e.2.2.2.2.1.isEmpty || [KindName.K1, .K2, .K12].contains e.2.1.kind) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A control: without K12 the test fails. -/
theorem senders_first_control : (cutFirstFull.all fun e =>
    e.2.2.2.2.1.isEmpty || [KindName.K1, .K2].contains e.2.1.kind) = false := by
  decide +kernel

theorem told_of_sends {S Cl : Type} {b : Block S Cl} (h : b.oracles.flatMap id ≠ []) :
    (toldRounds b).isEmpty = false := by
  unfold toldRounds
  cases h0 : b.oracles.zipIdx.filter (fun x => !x.1.isEmpty) with
  | cons a t => rfl
  | nil =>
    exfalso
    apply h
    rw [List.flatMap_eq_nil_iff]
    intro l hl
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hl
    have hm : (l, i) ∈ b.oracles.zipIdx := by
      have e := ProofFile.Honest.mem_zipIdx_of _ 0 i l hi
      rw [Nat.zero_add] at e
      exact e
    have h1 := List.filter_eq_nil_iff.1 h0 (l, i) hm
    cases l with
    | nil => rfl
    | cons a t => exact absurd rfl h1

/-- **A sending sub-protocol of the first chain is of one of the three kinds.** -/
theorem sender_kind_first {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
    {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} (h : P5J.AtMg o Z D r Zp Np cF)
    {b : Nat} {blk : Block TS ProofFile.Cl} (hb : cF.blocksInOrder[b]? = some blk)
    (hs : blk.oracles.flatMap id ≠ []) :
    [KindName.K1, .K2, .K12].contains blk.place.kind = true := by
  have e := OnBytes.Road.K4.cut_of_head h
  have hrow : cutFirstFull[b]? = some (blk.name, blk.place, blk.rounds.length, blk.oracles.length,
      toldRounds blk, blk.before) := by
    rw [← e]
    unfold cutOf
    rw [List.getElem?_map, hb]
    rfl
  have h1 := List.all_eq_true.1 senders_first _ (List.mem_of_getElem? hrow)
  have h2 := told_of_sends hs
  simpa [h2] using h1

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- **NO STOP AT A MEMBER WITH A NEW TREE**, from the quiet of the three kinds' halves. -/
theorem noStop_first
    (hq : ∀ y ∈ H.first, [KindName.K1, .K2, .K12].contains y.place.kind = true →
      RowQuiet y.parts) :
    ∀ b, b < (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.bs.length → (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.fresh b ≠ [] →
      ∀ blk, (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.bs[b]? = some blk → ∀ (m : Mid (Local W₀ Rc ProofFile.Inst Tr) X) (ds : List Fmt.Drawn),
        chainStopAt ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.φ.sees m.st.input) [blk] (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.hs m.loc ds = none := by
  intro b _ hf blk hblk m ds
  have hs : blk.oracles.flatMap id ≠ [] := fun e => hf (fresh_nil_of_oracles _ hblk e)
  have hk := sender_kind_first h.toAtMg hblk hs
  exact chainStop_none (fun y hy hp => hq y hy (by rw [hp]; exact hk)) _ _

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.RowQuiet
#print axioms ProofFile.Honest.FirstThread.rowStop_none
#print axioms ProofFile.Honest.FirstThread.chainStop_none
#print axioms ProofFile.Honest.FirstThread.senders_first
#print axioms ProofFile.Honest.FirstThread.senders_first_control
#print axioms ProofFile.Honest.FirstThread.told_of_sends
#print axioms ProofFile.Honest.FirstThread.sender_kind_first
#print axioms ProofFile.Honest.FirstThread.noStop_first
