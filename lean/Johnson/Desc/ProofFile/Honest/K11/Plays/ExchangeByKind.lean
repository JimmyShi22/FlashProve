-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K11/Plays/ExchangeByKind.lean: THE KIND K11's WHOLE DEBT UNDER THE
FRAME's `ExchangeAtS` (Honest/Thread/SharesS.lean), AT THE FIRST CHAIN's THREAD AT THE LIBRARY's
HEAD, IN THE FORM BY KIND THAT THE FRAME's AUTHORS' GATHER ASKS: at every number b whose written
place has the kind K11, at every item that the row owes, but for one that is open in front and is a
pin, pinI, pinW or a constr at one of `P5J.parts4`. A JOIN OF THREE. One definition: a public test.
Lemmas; none of the library's goals.

  `onlyK11At`, `onlyK11W`, `onlyK11W_can_fail`, `k11_at_346`
      BY LEAN's KERNEL, on the library's written list of the 358 places (`P5J.At.ps`): no place
      but number 346 has the kind K11; a control: the test says no at 345; and number 346 has that
      kind
  `k11_number`
      so: where the written list has p at b and p has the kind K11: b = 346
  `k11_exchange_by_kind`
      THE SENTENCE. Under the premises of `exchange_at_head` (SeatedAtHead.lean of this folder),
      letter for letter

HOW THE FIVE OWED ITEMS FALL (`owes_at_346`, ExchangeWhole.lean of this folder). forms 24 9 "merged"
and wo 24: `exchange_at_head`. pinW: the frame's authors' `exchangeAt_pinW`, which asks nothing. pin
24 0 and pinI: open at 346 (`pinsOpen_at_346`): so the sentence's own clause exempts them.

WHERE IT PARTS FROM THE GATHER's HYPOTHESIS. IT STANDS AT `SaidOk`, NOT AT A LETTER Said. THE HALF
THAT ITS PREMISE FINDS IN THE PROVER's FIRST CHAIN IS THE EARLIER `headMergeHalf`, NOT THE ONE WITH
THE TABLES KEPT: a filling that lays the kept lot does not meet that premise; the bridge
(`headMergeKeepSame`, KeepPlays.lean of this folder) is not called here.

NEAR: `exchangeS_at_head` (ExchangeWhole.lean of this folder): the whole form,
`ExchangeS` at `SaidOk` at 346: by `exchangeS_iff` it gives this sentence too,
UNDER TWO PREMISES MORE: the thread's keeps at 346 gives `K11Keeps`, and `BehindS` at 346. WHAT IS
NEW HERE IS THAT THESE TWO FALL: they served the two pins alone, which the form by kind exempts.

WHAT STAYS A PREMISE: the head · the maker's base Bs · b₀ ≤ 346 · the prover's half at `IM.k11Place`
· FOUR FACTS ON THE SCRIPT (`K11ScriptMsg`, `K11CellsQ`): NO SCRIPT IS LAID ANYWHERE, AND NO PROVER:
whoever lays them pays these. All limits of SeatedAtHeadStatement.lean stand. `ExchangeAtS` is a
sentence from the pair `ThrS`: that the pair holds at any stand is not said. IT DOES NOT SAY THAT
THE VERIFIER ACCEPTS AN HONEST RUN, NOR ANY RUN.

Limits. THREE CLOSED FACTS BY EVALUATION IN LEAN's KERNEL, one of them a control, and two beneath.
The full size; the format's second hash function. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.Plays.ExchangeWhole

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K11
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain Strs Place KindName)
open VerifiableInference.Desc.First (Item)
open VerifiableInference.Desc.Sound (MsgT)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.SumLaw (SumCoins)
open ProofFile.Honest.FirstThread

/-- **A PUBLIC TEST**: no place of the written list but number n has the kind K11. -/
def onlyK11At (n : Nat) : Bool :=
  P5J.At.ps.zipIdx.all fun x => x.1.kind != KindName.K11 || x.2 == n

set_option maxRecDepth 1000000 in
/-- **At the written list: number 346 alone.** -/
theorem onlyK11W : onlyK11At 346 = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- It can fail: at 345 it says no. -/
theorem onlyK11W_can_fail : onlyK11At 345 = false := by decide +kernel

set_option maxRecDepth 1000000 in
/-- Number 346 has the kind K11. -/
theorem k11_at_346 : (P5J.At.ps[346]?).map (·.kind) = some KindName.K11 := by decide +kernel

/-- Its use. -/
theorem k11_number {b : Nat} {p : Place} (hb : P5J.At.ps[b]? = some p)
    (hk : p.kind = KindName.K11) : b = 346 := by
  have h := List.all_eq_true.1 onlyK11W (p, b) (List.mem_zipIdx_iff_getElem?.2 hb)
  have h2 : (p.kind != KindName.K11 || b == 346) = true := h
  rw [hk] at h2
  simp only [bne_self_eq_false, Bool.false_or, beq_iff_eq] at h2
  exact h2

/-- THE HEAD AND FIVE ARE PREMISES. **THE KIND's WHOLE DEBT UNDER `ExchangeAtS`, BY KIND, AT
`SaidOk`.** -/
theorem k11_exchange_by_kind (Z : VerifierAndGoals.PublicFiles) (D : WholeD) (r : LPFD.Full.RunPF) (Zp : ProofFile.Pub)
    (Np : H2U.Places4) (cF : Chain TS ProofFile.Cl) (x : VerifiableInference.Desc.First.Look.Place)
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (Bk : ProverCoinCounts) (W₀ Rc Ky Tr X₀ X : Type)
    (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr) (Bs : ProofFile.PureBase)
    (weights : W₀ → Weights)
    (c₀ : SumCoins (runName maskRowRun ⟨headMergePlace (_root_.K11.parOf Zp Bs.G₀), 1⟩ "sum")
      (runName indexMaskRun ⟨headMergePlace (_root_.K11.parOf Zp Bs.G₀), 1⟩ "ends")
      (headMergeJob (_root_.K11.parOf Zp Bs.G₀).lay))
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) (hb₀ : b₀ ≤ 346)
    (hhalf : ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.hs.find? fun g =>
      g.place == IM.k11Place) =
        some (headMergeHalf (headClaimsAt cF Zp Bs.G₀) weights (_root_.K11.parOf Zp Bs.G₀)))
    (hM : K11ScriptMsg (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread SaidOk 346
      (_root_.K11.parOf Zp Bs.G₀)
      (headMergeCoins (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
        (_root_.K11.parOf Zp Bs.G₀) (headClaimsAt cF Zp Bs.G₀) weights IM.k11Place c₀)
      id id (dataAtHead h Q carryX) 24)
    (hC : K11CellsQ Q (_root_.K11.parOf Zp Bs.G₀).lay weights Vd) :
    ∀ b p, P5J.At.ps[b]? = some p → p.kind = KindName.K11 →
      ∀ j : Item, j ∈ ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.row b).owes →
      (j ∈ (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.opened b →
        (∀ m t, j ≠ Item.pin m t) ∧ j ≠ Item.pinI ∧ j ≠ Item.pinW ∧
        ∀ m q, q ∈ P5J.parts4 → j ≠ Item.constr m q) →
      ExchangeAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread SaidOk b j := by
  intro b p hb hk j hj hx
  obtain rfl := k11_number hb hk
  obtain ⟨e1, e2⟩ := exchange_at_head Z D r Zp Np cF x h Bk W₀ Rc Ky Tr X₀ X H Q test carryX item n₁
    n₂ b₀ Vd Rd Kp w Bs weights c₀ hB hb₀ hhalf hM hC
  have hm := owes_at_346 j hj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl
  · exact e1
  · exact e2
  · exact exchangeAtS_of _ SaidOk (exchangeAt_pinW h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w 346)
  · exact absurd rfl ((hx pinsOpen_at_346.1).1 24 0)
  · exact absurd rfl (hx pinsOpen_at_346.2).2.1

end ProofFile.Honest.K11

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms ProofFile.Honest.K11.onlyK11At
#print axioms ProofFile.Honest.K11.onlyK11W
#print axioms ProofFile.Honest.K11.onlyK11W_can_fail
#print axioms ProofFile.Honest.K11.k11_at_346
#print axioms ProofFile.Honest.K11.k11_number
#print axioms ProofFile.Honest.K11.k11_exchange_by_kind
