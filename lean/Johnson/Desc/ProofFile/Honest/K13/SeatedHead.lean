-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K13/SeatedHead.lean: kind K13, the members' batching: THE STRUCTURES
`K13Riders` (SeatedRiders.lean of this folder) AND `K13Seated` (Seated.lean) HELD AGAINST THE
FRAME's OWN LAYING OF THE FIRST CHAIN's THREAD AT THE LIBRARY's HYPOTHESIS
(`FirstThread.lettersHead`, Honest/Thread/FirstHead.lean), AT NUMBER 355. Two statements with their
proofs: calls and unfoldings alone.

`lettersHead` lays `rides` as "from the border b₀ on the reply that the state holds is the one
asked", beside other clauses Rd, and `keeps` by the member's place, through a parameter Kp. So the
fields on `rides` and `keeps` hold there, where b₀ is at most 355 and Kp at the kind's place is
`K13KeepsAll`.
WHAT IS LEFT AT `lettersHead`, BY NAME:
  hb: b₀ ≤ 355.
  hH: the kind's half stands at the member's place among the prover's halves of the first chain.
  hM, hC, hW: the three ties `MatTie`, `CoinsTie`, `RowsTie`.
  hK: Kp at the kind's place is `K13KeepsAll`.
  for `K13Riders`, with Rd a list of clauses: hN: none of them begins at the border behind the
    member. For `K13Seated`: hO: Rd goes over the kind's step.
Main names:
  `k13_riders_head`: **`K13Riders` at `lettersHead`.**
  `k13_seated_head`: `K13Seated` there.

What is not claimed. That the hypothesis h can be met. That h holds together with the thread's
sentence anywhere. Any of the premises that are left. That the thread holds at any run. Nothing on
any property.
-/
import Johnson.Desc.ProofFile.Honest.K13.SeatedAt
import Johnson.Desc.ProofFile.Honest.K13.SeatedRiders
import Johnson.Desc.ProofFile.Honest.Thread.FirstHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K13
open OnBytes
open VerifiableInference.Desc (Chain Strs Place)
open VerifiableInference.Desc.Ground (takeMasksP)
open VerifiableInference.Desc.K13.Law (dOf)
open VerifiableInference.Desc.K13.Honest (withClaim K13KeepsAll)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (lettersHead head_keeps Script WtF)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- **`K13Seated` at the frame's own laying of the thread, at number 355.** -/
theorem k13_seated_head {weights : W₀ → Weights} {pile : PileOf ProofFile.Inst} (hb : b₀ ≤ 355)
    (hH : ∀ blk, cF.blocksInOrder[355]? = some blk →
      (H.first.find? fun g => g.place == blk.place) = some (proverSideOfClaimCombination weights pile h.𝔇.P13))
    (hM : MatTie (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) weights pile h.𝔇.P13
      (k13ReaderAt h))
    (hC : CoinsTie (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) 355 weights pile
      h.𝔇.P13 (k13ReaderAt h))
    (hW : RowsTie (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) 355 pile
      ProofFile.Inst.asked)
    (hK : ∀ s s', Kp ⟨1, none, 3, .K13⟩ s s' ↔ K13KeepsAll h.𝔇.P13 s s')
    (hO : ∀ v s t msg row,
      takeMasksP (dOf s) s.out.indexMasks (Batt.masksOf h.𝔇.P13.lin.kCol) = some t →
      linMessageW h.𝔇.P13.lin = some msg → Rd 355 v s →
      Rd (355 + 1) v (withClaim s t.2.st msg row)) :
    K13Seated (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) 355 weights pile h.𝔇.P13
      Unit (k13ReaderAt h) ProofFile.Inst.asked Rd :=
  k13_seated_at h H.first Q _ _ test carryX item n₁ n₂ _ _ _ hH hM hC hW
    (fun s s' =>
      (head_keeps h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w m3_place s s').trans (hK s s'))
    (fun c hc _ _ =>
      have hc' : b₀ ≤ c := by
        rcases hc with rfl | rfl <;> omega
      ⟨fun q => ⟨q.1 hc', q.2⟩, fun q => ⟨fun _ => q.1, q.2⟩⟩)
    hO

/-- **`K13Riders` at the frame's own laying of the thread, with its other clauses a list, at number
355.** hN: no clause of the list begins at the border behind the member. -/
theorem k13_riders_head {weights : W₀ → Weights} {pile : PileOf ProofFile.Inst}
    (cs : List (RiderCl (Local W₀ Rc ProofFile.Inst Tr) TS)) (hb : b₀ ≤ 355)
    (hH : ∀ blk, cF.blocksInOrder[355]? = some blk →
      (H.first.find? fun g => g.place == blk.place) = some (proverSideOfClaimCombination weights pile h.𝔇.P13))
    (hM : MatTie (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf cs) Kp w) weights pile
      h.𝔇.P13 (k13ReaderAt h))
    (hC : CoinsTie (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf cs) Kp w) 355 weights
      pile h.𝔇.P13 (k13ReaderAt h))
    (hW : RowsTie (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf cs) Kp w) 355 pile
      ProofFile.Inst.asked)
    (hK : ∀ s s', Kp ⟨1, none, 3, .K13⟩ s s' ↔ K13KeepsAll h.𝔇.P13 s s')
    (hN : ∀ c ∈ cs, c.lo ≠ 355 + 1) :
    K13Riders (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf cs) Kp w) 355 weights pile
      h.𝔇.P13 Unit (k13ReaderAt h) ProofFile.Inst.asked cs b₀ where
  place := m3_place
  opened := m3_pile_open
  passes := m3_passBy
  member := k13_atK13_at h H.first Q _ _ test carryX item n₁ n₂ _ _ _ hH
  isAtM3 := k13_memberIs_at h
  table := m3_rowM3 h
  pub := pubM3_at h
  noPub := m3_noPub_at h
  reads := k13_reads_at h H.first Q _ _ test carryX item n₁ n₂ _ _ _
  mat := hM
  coins := hC
  rows := hW
  keepsIs := fun s s' =>
    (head_keeps h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf cs) Kp w m3_place s s').trans
      (hK s s')
  ridesAre := fun _ _ _ => Iff.rfl
  replyLo := hb
  noneLaid := hN

end ProofFile.Honest.K13

#print axioms ProofFile.Honest.K13.k13_seated_head
#print axioms ProofFile.Honest.K13.k13_riders_head
