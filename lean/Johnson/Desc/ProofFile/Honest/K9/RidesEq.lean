-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/RidesEq.lean: THE STATEMENT "RIDES PAST" (`RidesPastS`, Honest/Thread/PaysS.lean) AT THE SUB-PROTOCOL "THE ONE EQUATION" OF EACH OF THE 25
SEGMENTS, at the first chain's letters (`lettersHead`, Honest/Thread/FirstHead.lean) with a family f of the kinds' clauses of "keeps": an item that
is open at the member and that its row neither shuts nor owes passes over it.

The step turns the statement: its door takes mask entries and pushes one row onto the segment's group. Item by item, over the sorts that
Lean's kernel finds (Honest/K9/RidesSortsK9.lean):
  unmarked      the clause says: no mark behind
  pinW, a part of a later segment's relation      the library's laws ask nothing of the step
  a pin of the segment, pinI      each message's first sample row stays (Honest/K9/RowPushed.lean)
  pile          the statement behind extends the one in front, the trees and the pending rows stay
  a class of rows other than "equation"      a push at the end leaves the rows at the older places (RowPushed.lean)
  the claim on the weights      the library's law at this member (Honest/Thread/WoEqAt.lean)

  `set_rows`           laying this kind's part leaves the pending rows
  `eq_of_keeps`        the member's "keeps" gives the step's clause `EqKeeps`, from one premise on f at this kind
  `ridesPastAt_pile_eq`   the item pile
  **`k9_ridesPastS_eq`**   `RidesPastS` at 14 l + `IM.nAt l` + 4, at every Said; f, the riders and the number b₀ are variables

Limits. The library's hypothesis `AtMgA` is a premise, and hf: f at this kind gives this kind's clause at the place. Nothing here says that any item
holds at any state, or that the member accepts. This file proves no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K9.RowPushed
import Johnson.Desc.ProofFile.Honest.K9.RidesSortsK9
import Johnson.Desc.ProofFile.Honest.K9.KeepsAtPlace
import Johnson.Desc.ProofFile.Honest.Thread.KeepsBy
import Johnson.Desc.ProofFile.Honest.Thread.PaysS
import Johnson.Desc.ProofFile.Honest.Thread.SharesS
import Johnson.Desc.ProofFile.Honest.Thread.PinRides
import Johnson.Desc.ProofFile.Honest.Thread.HeadPinW
import Johnson.Desc.ProofFile.Honest.Thread.WoEqAt
import Johnson.Goal.HonestTrace.ConstrAtThread

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Chain Strs Wit Place KindName)
open VerifiableInference.Desc.First (S Item RowClass)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread

/-- Laying this kind's part leaves the pending rows. -/
theorem set_rows (s : S) (q : VerifiableInference.Desc.K9.Part) :
    (VerifiableInference.Desc.K9.atS.set s q).rows = s.rows := by
  show S.rows { (s.putLink q.L).putFork q.F with st := q.d.st, rowsOwed := q.owed } = S.rows s
  unfold S.rows S.putFork S.putLink
  cases h : s.here with
  | head a => by_cases ho : a.opened = true <;> simp [h, ho]
  | _ => simp [h]

theorem EqKeeps.rows {s s' : S} (K : EqKeeps s s') : s'.rows = s.rows := by
  obtain ⟨a, o, -, -, rfl⟩ := K.laid
  exact set_rows s _

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)

/-- The item pile passes over a member whose "keeps" gives the clause of "the one equation". -/
theorem ridesPastAt_pile_eq (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr) {b : ℕ}
    (hb : b ≤ cF.blocksInOrder.length) (h3 : 3 ≤ b) (h358 : b ≤ 358)
    (hk : ∀ s s', (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.keeps b s s' → EqKeeps s s') :
    RidesPastAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b Item.pile :=
  ridesPastAt_pile_older h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w fun _ s _ _ s' hA hK =>
    ⟨(hk s s' hK).rows, head_pileMasks h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hb hA,
      head_index h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hA (open_pinI h3 h358), eq_extends (hk s s' hK),
      eq_bookKept (hk s s' hK)⟩

variable (f : KindName → Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)
  (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)

/-- **The member's "keeps" gives the step's clause.** -/
theorem eq_of_keeps (hf : ∀ pl s s', pl.kind = KindName.K9 → f KindName.K9 pl s s' → k9KeepsAt cF Zp pl s s')
    {l : ℕ} (hl : l < 25) {s s' : TS} (hK : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w).thread.keeps (14 * l + IM.nAt l + 4) s s') : EqKeeps s s' := by
  obtain ⟨Lk, p, w', Qc, bE, bS, Sd, Hc⟩ := seats_at_head h hl
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have e := Hc.atE
  rw [Sd.hears] at e
  have hkind : bE.place.kind = KindName.K9 := kind_eq_at h hl e
  have a := (head_keeps_kind h H Q test carryX item n₁ n₂ b₀ Vd Rd f w (b := 14 * l + IM.nAt l + 4) e hkind s s').1 hK
  obtain ⟨-, -, e3⟩ := IM.k9Where_fields Hc.numbers
  have e1 := piece_at_seat h.scope h.reads O hl Hc.numbers
  exact eq_of_k9KeepsAt Hc (by show _ + 3 + 0 = p.pieceEq; omega) (hf _ _ _ hkind a)

/-- **"Rides past" at "the one equation" of each segment**, at every Said. -/
theorem k9_ridesPastS_eq (hf : ∀ pl s s', pl.kind = KindName.K9 → f KindName.K9 pl s s' → k9KeepsAt cF Zp pl s s')
    (l : ℕ) (hl : l < 25) : RidesPastS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w).thread Said (14 * l + IM.nAt l + 4) := by
  have hk : ∀ s s', (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w).thread.keeps (14 * l + IM.nAt l + 4) s s' → EqKeeps s s' :=
    fun s s' hK => eq_of_keeps h H Q test carryX item n₁ n₂ b₀ Vd Rd f w hf hl hK
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hlen : cF.blocksInOrder.length = 358 := Meaning.K2.flat_358 h.toAtMg.scope O
  have h9 : 7 ≤ IM.nAt l ∧ IM.nAt l ≤ 9 := by
    unfold IM.nAt
    split <;> omega
  have hb : 14 * l + IM.nAt l + 4 ≤ cF.blocksInOrder.length := by omega
  refine ridesPastS_shares _ _ fun i h1 h2 h3 => ?_
  rcases eq_open_cases hl h1 h2 h3 with ⟨t, e⟩ | e | e | e | e | ⟨c, hc, e⟩ | e | ⟨m, q, hq, e⟩
  · rw [e]
    exact ridesPastAtS_of _ _ (ridesPastAt_pin_eq h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w l t hk)
  · rw [e]
    exact ridesPastAtS_of _ _ (ridesPastAt_unmarked h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w fun s s' hK => (hk s s' hK).mark)
  · rw [e]
    exact ridesPastAtS_of _ _ (ridesPastAt_pinW h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w _)
  · rw [e]
    exact ridesPastAtS_of _ _ (ridesPastAt_pile_eq h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w hb (by omega)
      (by omega) hk)
  · rw [e]
    exact ridesPastAtS_of _ _ (ridesPastAt_pinI_eq h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w hk)
  · have ho : Item.row l c ∈ P5J.oAt (14 * l + IM.nAt l + 4) := eq_open_in hl (e ▸ h1)
    rw [e]
    exact ridesPastAtS_of _ _ (ridesPastAt_row_eq h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w hb l c (fun _ => ho) hk)
  · rw [e]
    exact ridesPastAtS_of _ _ (ridesPastAt_wo_eq_at h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w hl hb l hk)
  · rw [e]
    exact ridesPastAtS_of _ _ (OnBytes.HonestTrace.ridesPastAt_constr h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w _ m hq)

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.set_rows
#print axioms ProofFile.Honest.K9.EqKeeps.rows
#print axioms ProofFile.Honest.K9.ridesPastAt_pile_eq
#print axioms ProofFile.Honest.K9.eq_of_keeps
#print axioms ProofFile.Honest.K9.k9_ridesPastS_eq
