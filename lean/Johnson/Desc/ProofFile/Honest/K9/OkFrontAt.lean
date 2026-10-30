-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/OkFrontAt.lean: K9's OWN SENTENCE `OkFront` (Honest/K9/TotalFront.lean: "what is
fixed in front of the draw meets the library's promise") AT THE FRAME's OWN THREAD AT THE LIBRARY's HEAD, AT ALL THREE
SORTS OF SEGMENT, at the library's own constants (Honest/K9/TotalFill.lean). Statements and proofs; no goal is stated.
  **`okFront_lay_at_head`**, **`okFront_att_at_head`**, **`okFront_head_at_head`**   at T := the thread of
      `lettersHead …`, b := the number of the segment's batching in the head's own table: `OkFront Lk p (phiFill tlD)
      ‹okFillLay | okFillAtt | okFillHead …› T b`, AT EVERY Lk AND p. Lk and p are read in the stand alone; of the
      stand its pair and what lies behind the batching's yes alone are spent; the stand nowhere asks that the thread's
      block at b be Lk's batching: at an Lk that is not the seated link the sentence may be idle. b is written at
      `P5J.At.links`, which is `P5J.fullLinks` by unfolding, not by a rewrite; its value: the frame's `batch_at`
      (Honest/Law/Rule/OpenForms.lean)
Each is `okFill_lay` | `okFill_att` | `okFill_head` (Honest/K9/OkLay.lean, OkAtt.lean, OkHead.lean) with its premises
on the state paid at a stand of the thread: "reached" by the frame's `thrS_rchAt` (Honest/Thread/ReachAtHead.lean) off
the stand's pair · the open ledger, what the lookup on the calls left, and at attention K5's two tests by the frame's
four bridges (Honest/Law/Rule/OkBridges.lean) off the pair's first half · "K9's lens reads a part" off the stand's own
yes. WHAT STAYS AS PREMISES: the opening O (the head's own `h.laid.opened` hands one of this form; it stays a letter
because its ground Bs stands in the constants) and the readings at the segment: off the opening's ground: the built
link, K4's numbers; off the public parameters: the digits' place and data, the attention plan, the two lookups'
places. BY OUR READER's READING they can be had under the head, NOT JOINED HERE: the built link, K4's numbers and the
plan at the same O by `seal_lay`, `seal_att`, `seal_head` (Honest/K9/TotalFill.lean) · the digits' by the library's
`P5J.k03_digAt_some` · the calls' place by `at_planes_is` · the digits' lookup's place: no payer found.
WHAT IS NOT CLAIMED. That a stand is there. The other sentences of `FrontShares`. No member: called by no line.
Nothing on any property.

-/
import Johnson.Desc.ProofFile.Honest.K9.OkLay
import Johnson.Desc.ProofFile.Honest.K9.OkAtt
import Johnson.Desc.ProofFile.Honest.K9.OkHead
import Johnson.Desc.ProofFile.Honest.Thread.ReachAtHead
import Johnson.Desc.ProofFile.Honest.Law.Rule.OkBridges

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open OnBytes.Model.Stages (LinkH)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.LinkJoin (batchAt)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.First.Look (placeAt)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread
open _root_.Desc.K14.Law (seatZ secondAt)

/-- K9's lens reads a part in front of a yes of the batching. -/
theorem part_of_behind {p : Desc.K9.Where} {g : S → Except String (List Claim × S)} {s t : S} {x : E}
    {y : S × Desc.K9.Part × List Claim} {G : Fork} (B : BatBehind p g s x y G t) :
    (Desc.K9.atS.get? s).isSome = true := by
  obtain ⟨t₁, ht, _, _⟩ := gathered_split p g s x y B.gathered
  obtain ⟨a, ha⟩ := draw_open p s t₁ x ht
  rw [ha]
  rfl

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- **At a feed-forward segment.** -/
theorem okFront_lay_at_head {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF (seatZ Zp Np)
      (secondAt Zp Np)) {g : ℕ} (hg : g < 12) {Xl : LinkH} (e3 : Bs.G₀.built[2 * g]? = some Xl)
    {xx : First.Look.Place} {tlD : HTailF2} (hd : First.Look.digAt (P5J.At.X Zp) (2 * g) = some (xx, tlD))
    {p4 : OnBytes.Desc.First.K4.Par} (hk : LPFK9.k4ParAt Zp Bs.G₀ (2 * g) = some p4) {pC pD : First.Look.P}
    (hC : placeAt (P5J.At.X Zp) (2 * g) false = some pC) (hD : placeAt (P5J.At.X Zp) (2 * g) true = some pD)
    (Lk : Link S ProofFile.Cl) (p : Desc.K9.Where) :
    OkFront Lk p (phiFill tlD) (okFillLay p4 (ProofFile.k8NU Bs.G₀ Xl) tlD pC pD)
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
      (batchAt P5J.At.links P5J.At.ps (2 * g)) := by
  intro κ s m En ds y cols s' x' z G St
  have hf : cF.blocksInOrder.length = 358 := Meaning.K2.flat_358 h.toAtMg.scope O
  have hb : batchAt P5J.At.links P5J.At.ps (2 * g) = 28 * g + 9 := by
    rw [batch_at.1 (2 * g) (by omega)]
    omega
  have hq := thrS_rchAt h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w () (by rw [hf, hb]; omega) St.thr
  rw [hb] at hq
  exact okFill_lay h O hg e3 hd hk hC hD _ s hq
    (bridge_hB h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w (by omega) St.thr.1) (part_of_behind St.bat)
    (bridge_hL h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w (by omega) St.thr.1)

/-- **At an attention segment.** -/
theorem okFront_att_at_head {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF (seatZ Zp Np)
      (secondAt Zp Np)) {g : ℕ} (hg : g < 12) {A : Attention.Plan} (hA : (P5J.At.X Zp).A[g]? = some A)
    {Xl : LinkH} (e3 : Bs.G₀.built[2 * g + 1]? = some Xl) {xx : First.Look.Place} {tlD : HTailF2}
    (hd : First.Look.digAt (P5J.At.X Zp) (2 * g + 1) = some (xx, tlD)) {pC pD : First.Look.P}
    (hC : placeAt (P5J.At.X Zp) (2 * g + 1) false = some pC)
    (hD : placeAt (P5J.At.X Zp) (2 * g + 1) true = some pD) (Lk : Link S ProofFile.Cl) (p : Desc.K9.Where) :
    OkFront Lk p (phiFill tlD) (okFillAtt A (ProofFile.k8NU Bs.G₀ Xl) tlD pC pD)
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
      (batchAt P5J.At.links P5J.At.ps (2 * g + 1)) := by
  intro κ s m En ds y cols s' x' z G St
  have hf : cF.blocksInOrder.length = 358 := Meaning.K2.flat_358 h.toAtMg.scope O
  have hb := batch_at.1 (2 * g + 1) (by omega)
  have hq := thrS_rchAt h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w () (by rw [hf, hb]; omega) St.thr
  rw [hb] at hq
  have hA' : Bs.G₀.W.A[g]? = some A := by
    rw [O.W]
    exact hA
  exact okFill_att h O hg hA' e3 hd hC hD _ s hq
    (bridge_hB h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w (by omega) St.thr.1) (part_of_behind St.bat)
    (bridge_hL h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w (by omega) St.thr.1)
    (bridge_h5 h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hg hA St.thr.1)
    (bridge_hpl h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hg hA St.thr.1)

/-- **At the head's segment.** -/
theorem okFront_head_at_head {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF (seatZ Zp Np)
      (secondAt Zp Np)) {Xl : LinkH} (e3 : Bs.G₀.built[24]? = some Xl) {xx : First.Look.Place} {tlD : HTailF2}
    (hd : First.Look.digAt (P5J.At.X Zp) 24 = some (xx, tlD)) {pC pD : First.Look.P}
    (hC : placeAt (P5J.At.X Zp) 24 false = some pC) (hD : placeAt (P5J.At.X Zp) 24 true = some pD)
    (Lk : Link S ProofFile.Cl) (p : Desc.K9.Where) :
    OkFront Lk p (phiFill tlD) (okFillHead Bs.G₀.W (ProofFile.k8NU Bs.G₀ Xl) tlD pC pD)
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread (batchAt P5J.At.links P5J.At.ps 24) := by
  intro κ s m En ds y cols s' x' z G St
  have hf : cF.blocksInOrder.length = 358 := Meaning.K2.flat_358 h.toAtMg.scope O
  have hq := thrS_rchAt h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w () (by rw [hf, batch_at.2]; omega) St.thr
  rw [batch_at.2] at hq
  exact okFill_head h O e3 hd hC hD _ s hq
    (bridge_hB h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w (by omega) St.thr.1) (part_of_behind St.bat)
    (bridge_hL h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w (by omega) St.thr.1)

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.part_of_behind
#print axioms ProofFile.Honest.K9.okFront_lay_at_head
#print axioms ProofFile.Honest.K9.okFront_att_at_head
#print axioms ProofFile.Honest.K9.okFront_head_at_head
