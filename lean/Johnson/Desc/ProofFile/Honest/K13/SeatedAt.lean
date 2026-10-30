-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K13/SeatedAt.lean: kind K13, the members' batching: WHICH FIELDS OF
`K13Seated` (Seated.lean of this folder) HOLD AT THE LIBRARY's OWN PARAMETERS
(`FirstThread.lettersAt`, Honest/Thread/FirstAt.lean), AT NUMBER 355, under the hypothesis h under
which these parameters are laid. Statements with their proofs: calls alone.

OF THE FIFTEEN FIELDS NINE ARE SHOWN: three by evaluation, with no use of h; six from h, one of them
but for a premise on the thread's halves:
  place, opened, passes: evaluations by Lean's kernel on the written lists (`m3_place`,
    `m3_pile_open`, FromThreadAt.lean; `m3_passBy`, RidesAtM3.lean).
  isAtM3: `k13_memberIs_at` (FromThreadAt.lean).
  table, pub, noPub: `m3_rowM3`, `pubM3_at`, `m3_noPub_at` (BehindAtM3At.lean).
  reads: `k13_reads_at` (ExchangeAtM3.lean), at the library's reader through the book of commitment
    trees (`k13ReaderAt`).
  member: `k13_atK13_at` (ExchangeAtM3.lean): its rounds and oracle messages from h; THAT THE KIND's
    HALF STANDS AT THE MEMBER's PLACE AMONG THE THREAD's HALVES IS A PREMISE (hH): the halves are a
    parameter.
SIX STAY PREMISES, in the fields' own words: mat, coins, rows (the three ties of ExchangeAtM3.lean);
keepsIs, ridesIs (pointwise, on the parameters `keeps` and `rides`, which have no text at
`lettersAt`); others (on the variable R).
Main names:
  `k13_seated_at`: **the structure at these parameters**, from h, hH and the six.
  `k13_seated_four_at`: **so `Plays`, `Behind`, the share of `Exchange` at "pileOne" and `RidesPast`
    at number 355**, from the same.

What is not claimed. That h can be met. hH, and the six premises that stay: ridesIs SPEAKS OF ONE
VALUE THAT IS SENT IN THE CLEAR. `Accepted` at these parameters. That the thread holds at any run.
Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K13.Seated
import Johnson.Desc.ProofFile.Honest.K13.BehindAtM3At

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K13
open OnBytes
open VerifiableInference.Desc (Chain Strs)
open VerifiableInference.Desc.First (Item)
open VerifiableInference.Desc.Ground (takeMasksP)
open VerifiableInference.Desc.K13.Law (dOf)
open VerifiableInference.Desc.K13.Honest (withClaim K13KeepsAll)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (lettersAt Script WtF)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Tr X : Type}
  (hs : List (Placed (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X))
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (stored : Local W₀ Rc ProofFile.Inst Tr → Nat → Nat → Option (List UInt64))
  (ans : Nat → Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (test : Nat → TS → Option String)
  (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ : Nat)
  (valid : Local W₀ Rc ProofFile.Inst Tr → Prop) (rides : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
  (keeps : Nat → TS → TS → Prop)

/-- **`K13Seated` at the library's own parameters, at number 355.** hH: the kind's half stands at
the member's place among the thread's halves. hM, hC, hW: the three ties. hK, hR: what is asked,
pointwise, of `keeps` and `rides`. hO: the other clauses of `rides` go over the kind's step. -/
theorem k13_seated_at {weights : W₀ → Weights} {pile : PileOf ProofFile.Inst}
    {R : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop}
    (hH : ∀ blk, cF.blocksInOrder[355]? = some blk →
      (hs.find? fun g => g.place == blk.place) = some (proverSideOfClaimCombination weights pile h.𝔇.P13))
    (hM : MatTie (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps) weights
      pile h.𝔇.P13 (k13ReaderAt h))
    (hC : CoinsTie (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps) 355
      weights pile h.𝔇.P13 (k13ReaderAt h))
    (hW : RowsTie (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps) 355
      pile ProofFile.Inst.asked)
    (hK : ∀ s s', keeps 355 s s' ↔ K13KeepsAll h.𝔇.P13 s s')
    (hR : ∀ c, c = 355 ∨ c = 355 + 1 → ∀ w s,
      rides c w s ↔ ReplyIs ProofFile.Inst.asked w.x s ∧ R c w s)
    (hO : ∀ w s t msg row,
      takeMasksP (dOf s) s.out.indexMasks (Batt.masksOf h.𝔇.P13.lin.kCol) = some t →
      linMessageW h.𝔇.P13.lin = some msg → R 355 w s →
      R (355 + 1) w (withClaim s t.2.st msg row)) :
    K13Seated (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps) 355
      weights pile h.𝔇.P13 Unit (k13ReaderAt h) ProofFile.Inst.asked R where
  place := m3_place
  opened := m3_pile_open
  passes := m3_passBy
  member := k13_atK13_at h hs Q stored ans test carryX item n₁ n₂ valid rides keeps hH
  isAtM3 := k13_memberIs_at h
  table := m3_rowM3 h
  pub := pubM3_at h
  noPub := m3_noPub_at h
  reads := k13_reads_at h hs Q stored ans test carryX item n₁ n₂ valid rides keeps
  mat := hM
  coins := hC
  rows := hW
  keepsIs := hK
  ridesIs := hR
  others := hO

/-- **The four statements at number 355 of the thread at the library's own parameters.** -/
theorem k13_seated_four_at {weights : W₀ → Weights} {pile : PileOf ProofFile.Inst}
    {R : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop}
    (hH : ∀ blk, cF.blocksInOrder[355]? = some blk →
      (hs.find? fun g => g.place == blk.place) = some (proverSideOfClaimCombination weights pile h.𝔇.P13))
    (hM : MatTie (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps) weights
      pile h.𝔇.P13 (k13ReaderAt h))
    (hC : CoinsTie (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps) 355
      weights pile h.𝔇.P13 (k13ReaderAt h))
    (hW : RowsTie (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps) 355
      pile ProofFile.Inst.asked)
    (hK : ∀ s s', keeps 355 s s' ↔ K13KeepsAll h.𝔇.P13 s s')
    (hR : ∀ c, c = 355 ∨ c = 355 + 1 → ∀ w s,
      rides c w s ↔ ReplyIs ProofFile.Inst.asked w.x s ∧ R c w s)
    (hO : ∀ w s t msg row,
      takeMasksP (dOf s) s.out.indexMasks (Batt.masksOf h.𝔇.P13.lin.kCol) = some t →
      linMessageW h.𝔇.P13.lin = some msg → R 355 w s →
      R (355 + 1) w (withClaim s t.2.st msg row)) :
    Plays (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).thread 355 ∧
      Behind (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).thread 355 ∧
      ExchangeOf (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).thread 355
        [Item.pileOne] ∧
      RidesPast (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).thread 355 :=
  k13_seated
    (k13_seated_at h hs Q stored ans test carryX item n₁ n₂ valid rides keeps hH hM hC hW hK hR hO)

end ProofFile.Honest.K13

#print axioms ProofFile.Honest.K13.k13_seated_at
#print axioms ProofFile.Honest.K13.k13_seated_four_at
