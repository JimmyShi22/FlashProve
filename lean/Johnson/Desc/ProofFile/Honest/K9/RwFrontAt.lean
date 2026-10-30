-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/RwFrontAt.lean: FOR THE ITEM "totalB": K9's OWN SENTENCE `RwFront`
(Honest/K9/TotalFront.lean: the item's fourth conjunct, at what is fixed in front) AT THE FRAME's OWN THREAD AT THE
LIBRARY's HEAD, AT ALL THREE SORTS OF SEGMENT, UNDER ONE PUBLIC PREMISE. Statements and proofs; no goal is stated.
  **`rwFront_lay_at_head`**, **`rwFront_att_at_head`**, **`rwFront_head_at_head`**   at T := the thread of
      `lettersHead …`, b := the number of the segment's batching in the head's own table, p what `IM.k9At Zp` names at
      the segment: `RwFront Lk p (phiFill tlD) pi8 T b`, at every Lk and tlD
Each is `rwFill_lay` | `rwFill_att` | `rwFill_head` (Honest/K9/RwFill.lean) at a stand of the thread: "reached" by the
frame's `thr_reach` (Honest/Thread/ReachFacts.lean) off the first half of the stand's field thr. Of the stand nothing
else is spent. WHAT STAYS: hE : `K9Asks.RowsAsked Zp` (the library's Johnson/Desc/First/Link/Law/K9RowsAskLaw.lean: at
each of the 25 segments the public test "the rows fit" says yes of the segment that stands in the public part's built
links): A PUBLIC PREMISE. PAID BY NOTHING THAT WAS FOUND: a search for the name over the Lean files finds thirteen
files (ten are the smallness test's); in
each it is the definition or a premise · kp · g < 12. Lk is read in the stand alone: at an Lk that is not the seated
link the sentence may be idle.
WHAT IS NOT CLAIMED. That a stand is there. `RowsAsked` at any public part. No member: called by no line. Nothing on
any property.

-/
import Johnson.Desc.ProofFile.Honest.K9.RwFill
import Johnson.Desc.ProofFile.Honest.K9.OkFrontAt
import Johnson.Desc.ProofFile.Honest.Thread.ReachFacts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.LinkJoin (batchAt pi8)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr) (hE : K9Asks.RowsAsked Zp)
include hE

/-- **At a feed-forward segment.** -/
theorem rwFront_lay_at_head {g : ℕ} (hg : g < 12) (Lk : Link S ProofFile.Cl) {p : Desc.K9.Where}
    (kp : IM.k9At Zp (2 * g) = some p) (tlD : HTailF2) :
    RwFront Lk p (phiFill tlD) pi8 (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
      (batchAt P5J.At.links P5J.At.ps (2 * g)) := by
  intro κ s m En ds y cols s' x' z G St
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hf : cF.blocksInOrder.length = 358 := Meaning.K2.flat_358 h.toAtMg.scope O
  have hb : batchAt P5J.At.links P5J.At.ps (2 * g) = 28 * g + 9 := by
    rw [batch_at.1 (2 * g) (by omega)]
    omega
  have hq := thr_reach h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w (by rw [hf, hb]; omega) St.thr.1
  rw [hb] at hq
  exact rwFill_lay hE h.scope h.reads O hg hq p kp tlD _

/-- **At an attention segment.** -/
theorem rwFront_att_at_head {g : ℕ} (hg : g < 12) (Lk : Link S ProofFile.Cl) {p : Desc.K9.Where}
    (kp : IM.k9At Zp (2 * g + 1) = some p) (tlD : HTailF2) :
    RwFront Lk p (phiFill tlD) pi8 (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
      (batchAt P5J.At.links P5J.At.ps (2 * g + 1)) := by
  intro κ s m En ds y cols s' x' z G St
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hf : cF.blocksInOrder.length = 358 := Meaning.K2.flat_358 h.toAtMg.scope O
  have hb := batch_at.1 (2 * g + 1) (by omega)
  have hq := thr_reach h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w (by rw [hf, hb]; omega) St.thr.1
  rw [hb] at hq
  exact rwFill_att hE h.scope h.reads O hg hq p kp tlD _

/-- **At the head's segment.** -/
theorem rwFront_head_at_head (Lk : Link S ProofFile.Cl) {p : Desc.K9.Where} (kp : IM.k9At Zp 24 = some p)
    (tlD : HTailF2) :
    RwFront Lk p (phiFill tlD) pi8 (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
      (batchAt P5J.At.links P5J.At.ps 24) := by
  intro κ s m En ds y cols s' x' z G St
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hf : cF.blocksInOrder.length = 358 := Meaning.K2.flat_358 h.toAtMg.scope O
  have hq := thr_reach h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w (by rw [hf, batch_at.2]; omega) St.thr.1
  rw [batch_at.2] at hq
  exact rwFill_head hE h.scope h.reads O hq p kp tlD _

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.rwFront_lay_at_head
#print axioms ProofFile.Honest.K9.rwFront_att_at_head
#print axioms ProofFile.Honest.K9.rwFront_head_at_head
