-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/TotalInPaid.lean: FOR THE ITEM "totalB": THE NAMED PREMISE `XkAtStand` OF
Honest/K9/TotalInAt.lean IS PAID, AND SO `TotalInBehind` (Honest/K9/TotalFront.lean) STANDS AT THE FRAME's OWN THREAD AT
THE LIBRARY's HEAD, AT EACH OF THE 25 SEGMENTS, AT own := THE TABLE's OWN GROUP, UNDER THE HEAD, l < 25 AND K9's SEAT.
Statements and proofs: calls; no goal is stated.
  `data_numbers`   the numbers of the head's own data (`h.𝔇.N`) are the table's (`P5J.At.N Zp cF`): by definition. So
      the table's group at a segment is the group that the library's meaning names in the item's own sentence
      (`mgAll_totalB`, `mgAll_forms`, Johnson/Desc/Sound/MgAll.lean: these say 𝔇.N.group); that the item "totalB" at a
      segment is the library's `.totalB` at that segment's number (Johnson/Desc/First/Link/Law/K09Rows.lean), and that
      the head's meaning is `mgAll` at h.𝔇: by reading, not typed
  `xkAtStand_at_head`   under the head and l < 25: `XkAtStand` at every Lk and p: one call of the frame's `xk_ew_front`
      (Honest/Thread/K9FormBehind.lean) at the form that a stand holds (in its field thr); the border's number is the
      table's (the library's `LPFK9.batch_nAt`)
  **`totalIn_paid`**   under the head, l < 25 and K9's seat Sd at l: `TotalInBehind Lk p T b ((P5J.At.N Zp cF).group
      l)`, T and b as in Honest/K9/TotalInAt.lean
GROUND: beside what lies beneath Honest/K9/TotalInAt.lean, seven files of the frame's under Honest/Thread/
(K9FormBehind.lean, FormXK.lean, FormXKFront.lean, FormXKPub.lean, HeadLetters.lean, PubPAtHead.lean, PubPAtK9.lean:
live, not sealed; each came to us as a single file that its house calls a trial build). They stand in turn over files of
ours (Honest/K9/XkAtHead.lean, XkEqReach.lean, XkFront.lean and what these import). This file is no better than any of
these. At the full size and the format's second hash function alone: the head's.
WHAT IS NOT CLAIMED. That a stand is there: where there is none, `xkAtStand_at_head` and `totalIn_paid` say nothing.
`XkAtStand` is read off the form that a stand carries in its field thr: paying it adds no fact about a run: all the
weight lies in that a stand is there. No member; `totalIn_paid` is called by Honest/K9/TotalAtt.lean, TotalHead.lean and
TotalLay.lean; `data_numbers` by no line. Nothing on any property.

-/
import Johnson.Desc.ProofFile.Honest.K9.TotalInAt
import Johnson.Desc.ProofFile.Honest.Thread.K9FormBehind

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.LinkJoin (batchAt)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)

/-- The numbers of the head's own data are the table's. -/
theorem data_numbers : h.𝔇.N = P5J.At.N Zp cF := rfl

variable {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- **The named premise is paid**: a stand holds the thread's form; the frame's lemma reads the five Bools off it. -/
theorem xkAtStand_at_head {l : ℕ} (hl : l < 25) (Lk : Link S ProofFile.Cl) (p : Desc.K9.Where) :
    XkAtStand h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w l Lk p := by
  intro κ s m En ds y cols s' x' z G St
  rw [← LPFK9.batch_nAt l hl]
  exact xk_ew_front h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w St.thr.1.2.2.1

/-- **`TotalInBehind` at the frame's own thread, under the head and K9's seat alone.** -/
theorem totalIn_paid {l : ℕ} (hl : l < 25) {kk : ℕ} {Lk : Link S ProofFile.Cl} {p : Desc.K9.Where}
    {ww : Desc.K9.SegSort × ℕ × Desc.K9.TWhere} (Sd : SeatedFree cF Zp l kk Lk p ww) :
    TotalInBehind Lk p (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
      (batchAt P5J.At.links P5J.At.ps l) ((P5J.At.N Zp cF).group l) :=
  totalIn_at_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hl Sd
    (xkAtStand_at_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hl Lk p)

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.data_numbers
#print axioms ProofFile.Honest.K9.xkAtStand_at_head
#print axioms ProofFile.Honest.K9.totalIn_paid
