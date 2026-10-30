-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K13/ExchangeM4At.lean: kind K13's share of the debt `Exchange` at
"M:4", AT THE LIBRARY's OWN PARAMETERS (`FirstThread.lettersAt`,
Johnson/Desc/ProofFile/Honest/Thread/FirstAt.lean): the full size, at the hash `OnBytes.secondHashFunction`.
Statements with their proofs: two evaluations by Lean's kernel on the written lists, unfoldings, and
uses of `pileOne_at_m4`, `exchange_at_m4` and `exchange_of_m4`.

Why. `TiedAtM4` (Honest/K13/ExchangeM4.lean) is a premise of the conditional statements. Here it is
shown at the library's own parameters, UNDER THE HYPOTHESIS h UNDER WHICH THESE ARE LAID
(`P5J.AtMgA`): so that premise can be met if h can; and the statements are used there. The
statements' premises together are met at no parameters here.
Main names:
  `m4_place`: number 356 of the written list of places is the place "M:4".
  `m4_pileOne_open`: the item `pileOne` is open at the border number 356.
  `tied_at_letters`: **under h, `TiedAtM4` holds at the library's own parameters**, at b = 356, the
    reader's numbers and the matrix of the library's data.
  `pileOne_at_letters`: `pileOne_at_m4` there: what is left of its premises is `PublicAtM4` from the
    thread in front.
  `exchange_at_letters`: `exchange_at_m4` there: what is left: `PublicAtM4` from the thread, and,
    for `wrow` alone, `ReplyRides` and `WitnessHasW`.
  `exchange_whole_at_letters`: `Exchange` at the border number 356, from these and the share at
    `pinV`; the share at `pinW` holds by unfolding of these parameters: no work of the kind's.

What is not claimed. That the hypothesis h can be met. `PublicAtM4` from the thread; `ReplyRides`;
`WitnessHasW`; the share at `pinV`: premises still. That the thread holds at any run. Nothing on
soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K13.ExchangeM4Proof
import Johnson.Desc.ProofFile.Honest.K13.FromThreadAt
import Johnson.Desc.ProofFile.Honest.Thread.FirstAt
import Johnson.P5J.PlacesPaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K13
open VerifiableInference.Desc (Chain Strs)
open VerifiableInference.Desc.First (Item start)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.K13 (whereOf)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (lettersAt Script WtF)

set_option maxRecDepth 100000 in
/-- Number 356 of the written list of places is the place "M:4". -/
theorem m4_place : P5J.At.ps[356]? = some ⟨1, none, 4, .K1⟩ := by decide +kernel

set_option maxRecDepth 100000 in
/-- The item `pileOne` is open at the border number 356. -/
theorem m4_pileOne_open :
    Item.pileOne ∈ fwdOpen (start P5J.At.links) (FirstRows.rows P5J.At.links P5J.At.ps) 356 := by
  decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **Under h, `TiedAtM4` holds at the library's own parameters.** -/
theorem tied_at_letters (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Tr X : Type}
    (hs : List (Placed (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X))
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (stored : Local W₀ Rc ProofFile.Inst Tr → Nat → Nat → Option (List UInt64))
    (ans : Nat → Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ : Nat)
    (valid : Local W₀ Rc ProofFile.Inst Tr → Prop) (rides : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (keeps : Nat → TS → TS → Prop) :
    TiedAtM4 (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps) 356 Zp cF
      h.𝔇.arr h.𝔇.mat13 := by
  refine ⟨rfl, fun blk hb => ?_, m4_place, fun _ => rfl, fun _ => rfl, m4_pileOne_open⟩
  have hp := P5J.At.places_paid h.scope h.reads h.laid
  have hb' : cF.blocksInOrder[356]? = some blk := hb
  have e : (VerifiableInference.Desc.First.blockPlaces cF.blocksInOrder)[356]? = some blk.place := by
    unfold VerifiableInference.Desc.First.blockPlaces
    rw [List.getElem?_map, hb']
    rfl
  rw [hp, m4_place] at e
  exact (Option.some.inj e).symm

/-- **`pileOne_at_m4` at these parameters**: what is left of its premises is `PublicAtM4` from the
thread in front. -/
theorem pileOne_at_letters (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Tr X : Type}
    (hs : List (Placed (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X))
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (stored : Local W₀ Rc ProofFile.Inst Tr → Nat → Nat → Option (List UInt64))
    (ans : Nat → Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ : Nat)
    (valid : Local W₀ Rc ProofFile.Inst Tr → Prop) (rides : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (keeps : Nat → TS → TS → Prop)
    (hpub : ∀ k s m En,
      Thr (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).thread 356 k s m
        En → PublicAtM4 (whereOf Zp) s) :
    ExchangeOf (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).thread 356
      [Item.pileOne] := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  exact pileOne_at_m4 _ 356 _ _ _ _ _ Zp Bs base cF _ _ h.𝔇.arr h.𝔇.mat13 O
    (tied_at_letters h hs Q stored ans test carryX item n₁ n₂ valid rides keeps) hpub

/-- **`exchange_at_m4` at these parameters.** -/
theorem exchange_at_letters (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Tr X : Type}
    (hs : List (Placed (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X))
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (stored : Local W₀ Rc ProofFile.Inst Tr → Nat → Nat → Option (List UInt64))
    (ans : Nat → Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ : Nat)
    (valid : Local W₀ Rc ProofFile.Inst Tr → Prop) (rides : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (keeps : Nat → TS → TS → Prop)
    (hpub : ∀ k s m En,
      Thr (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).thread 356 k s m
        En → PublicAtM4 (whereOf Zp) s)
    (hY : ReplyRides (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps) 356
      ProofFile.Inst.asked)
    (hW : WitnessHasW (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps) 356 Zp
      h.𝔇.arr h.𝔇.mat13 ProofFile.Inst.asked) :
    ExchangeOf (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).thread 356
      [Item.wrow, Item.pileOne] := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  exact exchange_at_m4 _ 356 _ _ _ _ _ Zp Bs base cF _ _ h.𝔇.arr h.𝔇.mat13 ProofFile.Inst.asked O
    (tied_at_letters h hs Q stored ans test carryX item n₁ n₂ valid rides keeps) hpub hY hW

/-- **`Exchange` at the border number 356**, at these parameters: from the premises of
`exchange_at_letters` and the share at `pinV`. The share at `pinW` holds by unfolding of these
parameters (`k13_pinW_at`, FromThreadAt.lean). -/
theorem exchange_whole_at_letters (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Tr X : Type}
    (hs : List (Placed (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X))
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (stored : Local W₀ Rc ProofFile.Inst Tr → Nat → Nat → Option (List UInt64))
    (ans : Nat → Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ : Nat)
    (valid : Local W₀ Rc ProofFile.Inst Tr → Prop) (rides : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (keeps : Nat → TS → TS → Prop)
    (hpub : ∀ k s m En,
      Thr (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).thread 356 k s m
        En → PublicAtM4 (whereOf Zp) s)
    (hY : ReplyRides (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps) 356
      ProofFile.Inst.asked)
    (hW : WitnessHasW (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps) 356 Zp
      h.𝔇.arr h.𝔇.mat13 ProofFile.Inst.asked)
    (hV : ExchangeOf (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).thread
      356 [Item.pinV]) :
    Exchange (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).thread 356 :=
  exchange_of_m4 (tied_at_letters h hs Q stored ans test carryX item n₁ n₂ valid rides keeps)
    (exchange_at_letters h hs Q stored ans test carryX item n₁ n₂ valid rides keeps hpub hY hW)
    (k13_pinW_at h hs Q stored ans test carryX item n₁ n₂ valid rides keeps 356) hV

end ProofFile.Honest.K13

#print axioms ProofFile.Honest.K13.m4_place
#print axioms ProofFile.Honest.K13.m4_pileOne_open
#print axioms ProofFile.Honest.K13.tied_at_letters
#print axioms ProofFile.Honest.K13.pileOne_at_letters
#print axioms ProofFile.Honest.K13.exchange_at_letters
#print axioms ProofFile.Honest.K13.exchange_whole_at_letters
