-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/RidesBat.lean: THE STATEMENT "RIDES PAST" (`RidesPastS`, Honest/Thread/PaysS.lean) AT THE BATCHING OF EACH OF THE 25 SEGMENTS, at the first
chain's letters (`lettersHead`, Honest/Thread/FirstHead.lean) with a family f of the kinds' clauses of "keeps": an item that is open at the member and
that its row neither shuts nor owes passes over it.

The batching draws, runs the order's runs of claims and lays this kind's part back. None of these turns the statement, the list of
commitment trees, the output record, the pending rows, or what the segment's own rounds left for the row on the weights. So every item
that rides here reads the same in front and behind. Item by item, over the sorts that Lean's kernel finds
(Honest/K9/RidesSortsK9.lean): unmarked; pinW; pile; pinI; a class of rows of the segment; the claim on the weights; a part of a later
segment's relation.

  `rests_rows`         the pending rows rest under the four writings of a run of claims
  `leftOf_of`          what is left for the row on the weights is read off two readings that the batching leaves
  `bat_of_keeps`       the member's "keeps" gives the step's clause `K9Keeps`, from one premise on f at this kind
  **`bat_same`**         under the clause: the seven fields, the pending rows and what is left are the same behind as in front
  `ridesPastAt_wo_same`   the claim on the weights, over a member that leaves these
  **`k9_ridesPastS_bat`**   `RidesPastS` at 14 l + `IM.nAt l` + 2, at every Said; f, the riders and the number b₀ are variables

Limits. The library's hypothesis `AtMgA` is a premise, and hf: f at this kind gives this kind's clause at the place. Nothing here says that any item
holds at any state, or that the member accepts. This file proves no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K9.RidesEq
import Johnson.Desc.ProofFile.Honest.K9.KeepsReadings
import Johnson.Desc.ProofFile.Honest.K9.KeepsPaid
import Johnson.Desc.ProofFile.Honest.Thread.RowPileRides
import Johnson.Desc.ProofFile.Honest.Thread.WoForward

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Chain Strs Wit Place KindName Link claimsInBy)
open VerifiableInference.Desc.First (S Item RowClass BookKept)
open VerifiableInference.Desc.LinkJoin (FieldRests)
open VerifiableInference.Desc.Sound (MsgT)
open Johnson.Desc.First.Walk.Law (leftOf rowAt rowBy)
open OnBytes.Means (Extends)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread

/-- The pending rows rest under the four writings. -/
theorem rests_rows : FieldRests S.rows where
  tl s tl := by
    unfold S.rows S.putTl
    cases h : s.here with
    | head a => by_cases ho : a.opened = true <;> simp [h, ho]
    | _ => simp [h]
  fork s G := by
    unfold S.rows S.putFork
    cases h : s.here with
    | head a => by_cases ho : a.opened = true <;> simp [h, ho]
    | _ => simp [h]
  wrote e _ _ _ hw := by
    obtain ⟨h1, rfl⟩ := hw
    unfold S.rows
    simp [h1]
  head s a G h := by
    unfold S.rows
    simp [h]

/-- What is left for the row on the weights, off two readings. -/
theorem leftOf_of {s s' : S} (e1 : s'.own? = s.own?) (e2 : headOf s' = headOf s) : leftOf s' = leftOf s := by
  have a : ∀ u : S, leftOf u = match u.own?.map (·.wo) with
      | some x => some x
      | none => (headOf u).bind (·.2.2) := by
    intro u
    unfold leftOf Johnson.Desc.First.Walk.leftLay VerifiableInference.Desc.First.Close.leftHead S.own? headOf
    cases u.here <;> rfl
  rw [a s', a s, e1, e2]

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **What the batching leaves.** -/
theorem bat_same (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l k : ℕ} {Lk : Link S ProofFile.Cl}
    {p : VerifiableInference.Desc.K9.Where}
    {w : VerifiableInference.Desc.K9.SegSort × ℕ × VerifiableInference.Desc.K9.TWhere} (hl : l < 25)
    (Sd : SeatedFree cF Zp l k Lk p w) {s s' : S} (K : K9Keeps p (claimsInBy Lk.each Lk.hear Lk.order) s s') :
    setLeaves s s' ∧ s'.rows = s.rows ∧ leftOf s' = leftOf s :=
  ⟨K.seven_of fun o ho run hr n e c e₁ hz => by
      obtain ⟨j, hj⟩ := List.getElem?_of_mem ho
      exact rests_at_head h hl Sd sevenOf rests_seven j o run hj hr n e (c, e₁) hz,
    bat_keeps_reading h hl Sd S.rows rests_rows set_rows K,
    leftOf_of (bat_keeps_reading h hl Sd S.own? rests_own set_own K)
      (bat_keeps_reading h hl Sd headOf rests_headOf set_headOf K)⟩

variable (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)

/-- The claim on the weights passes over a member that leaves the statement, the trees, the output record and what is left. -/
theorem ridesPastAt_wo_same (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr) {b : ℕ} (h3 : 3 ≤ b)
    (h358 : b ≤ 358) (m : ℕ)
    (hk : ∀ s s', (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.keeps b s s' →
      setLeaves s s' ∧ leftOf s' = leftOf s) :
    RidesPastAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b (Item.wo m) :=
  ridesPastAt_wo_older h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w m fun _ s _ _ s' hA hK => by
    obtain ⟨⟨e1, e2, -, -, -, e6, -⟩, e8⟩ := hk s s' hK
    refine ⟨?_, head_index h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hA (open_pinI h3 h358), ?_, ?_⟩
    · unfold rowAt rowBy
      rw [e8, e6, e1]
    · rw [e1]
      exact Extends.refl _
    · exact fun o _ => ⟨by rw [e2], fun q _ => by rw [e2]⟩

variable (f : KindName → Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)
  (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)

/-- **The member's "keeps" gives what the batching leaves, and no mark.** -/
theorem bat_of_keeps (hf : ∀ pl s s', pl.kind = KindName.K9 → f KindName.K9 pl s s' → k9KeepsAt cF Zp pl s s')
    {l : ℕ} (hl : l < 25) {s s' : TS} (hK : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w).thread.keeps (14 * l + IM.nAt l + 2) s s') :
    s'.failed = none ∧ setLeaves s s' ∧ s'.rows = s.rows ∧ leftOf s' = leftOf s := by
  obtain ⟨Lk, p, w', Qc, bE, bS, Sd, -⟩ := seats_at_head h hl
  have hkind := kind_bat_at h hl Sd.batching
  have a := (head_keeps_kind h H Q test carryX item n₁ n₂ b₀ Vd Rd f w (b := 14 * l + IM.nAt l + 2) Sd.batching hkind
    s s').1 hK
  have K := bat_of_k9KeepsAt Sd (hf _ _ _ hkind a)
  exact ⟨K.mark, bat_same h hl Sd K⟩

/-- **"Rides past" at the batching of each segment**, at every Said. -/
theorem k9_ridesPastS_bat (hf : ∀ pl s s', pl.kind = KindName.K9 → f KindName.K9 pl s s' → k9KeepsAt cF Zp pl s s')
    (l : ℕ) (hl : l < 25) : RidesPastS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w).thread Said (14 * l + IM.nAt l + 2) := by
  have hk : ∀ s s', (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w).thread.keeps (14 * l + IM.nAt l + 2) s s' →
      s'.failed = none ∧ setLeaves s s' ∧ s'.rows = s.rows ∧ leftOf s' = leftOf s :=
    fun s s' hK => bat_of_keeps h H Q test carryX item n₁ n₂ b₀ Vd Rd f w hf hl hK
  have h9 : 7 ≤ IM.nAt l ∧ IM.nAt l ≤ 9 := by
    unfold IM.nAt
    split <;> omega
  refine ridesPastS_shares _ _ fun i h1 h2 h3 => ?_
  rcases bat_open_cases hl h1 h2 h3 with e | e | e | e | ⟨c, -, e⟩ | e | ⟨m, q, hq, e⟩ <;> rw [e]
  · exact ridesPastAtS_of _ _ (ridesPastAt_unmarked h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w fun s s' hK => (hk s s' hK).1)
  · exact ridesPastAtS_of _ _ (ridesPastAt_pinW h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w _)
  · exact ridesPastAtS_of _ _ (ridesPastAt_pile h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w fun s s' hK =>
      ⟨(hk s s' hK).2.1.1, (hk s s' hK).2.1.2.1, (hk s s' hK).2.2.1⟩)
  · exact ridesPastAtS_of _ _ (ridesPastAt_pinI h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w fun s s' hK => (hk s s' hK).2.1.1)
  · exact ridesPastAtS_of _ _ (ridesPastAt_row h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w l c fun s s' hK =>
      ⟨(hk s s' hK).2.1.1, (hk s s' hK).2.1.2.1⟩)
  · exact ridesPastAtS_of _ _ (ridesPastAt_wo_same h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w (by omega)
      (by omega) l fun s s' hK => ⟨(hk s s' hK).2.1, (hk s s' hK).2.2.2⟩)
  · exact ridesPastAtS_of _ _ (OnBytes.HonestTrace.ridesPastAt_constr h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w _ m hq)

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.rests_rows
#print axioms ProofFile.Honest.K9.leftOf_of
#print axioms ProofFile.Honest.K9.bat_same
#print axioms ProofFile.Honest.K9.ridesPastAt_wo_same
#print axioms ProofFile.Honest.K9.bat_of_keeps
#print axioms ProofFile.Honest.K9.k9_ridesPastS_bat
