-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K4/Law/RidesPastColumn.lean: CONDITIONAL: on the library's hypothesis
h on the public files and on one hypothesis on the thread's parameter for `keeps`. THE FULL SIZE
ALONE.

What is here. THE THREADS' DEBT `RidesPastS` (Honest/Thread/PaysS.lean) AT THE MEMBER OF THE
FEED-FORWARD LAYERS' OWN ROUNDS (sub-protocol K4), WHOLE, at the first chain's thread at the
library's own parameters (`lettersHead`, Honest/Thread/FirstHead.lean): every item that is open in
front of the member and that its row neither shuts nor owes, if it holds of a witness in front,
holds of it at every state behind that the member's clause of keeps allows. From "∀ i" on it is
stated in the text of the column hR of `owesS_head_form` (Honest/Thread/GatherHeadForm.lean); the
guard in front is another: that column says b < bs.length, here the written list has a place of the
kind K4 at b; a gatherer comes from the one to the other by `head_place`
(Honest/Thread/HeadForm.lean) and a split on the place's kind. Nothing new is shown on any item: a
join. Which items ride: `riders_are_sorted` (Law/RidersSorted.lean): five sorts. Sort by
sort, a law that lies already is called: four in the library; the fifth, at "objects", with three
files beneath it (Law/ObjectsOnAll.lean, Law/ObjectsOnKeeps.lean, Law/ObjectsOn.lean), is no part of
the library yet:
  `unmarked`   `ridesPastAt_unmarked` (Honest/Thread/PinRides.lean): keeps gives "no mark behind"
  a class of rows   `ridesPastAt_row` (Honest/Thread/RowPileRides.lean): keeps leaves the statement
     and the book of trees
  `pile`   `ridesPastAt_pile` (the same file): these, and the rows on the table
  the run "objects"   `k4_ridesPastAtS_objects_at` (Law/ObjectsRidesHead.lean)
  a part of a segment's relation   `ridesPastAt_constr`
     (Johnson/Goal/HonestTrace/ConstrAtThread.lean): at the four parts of `P5J.parts4` the sentence
     reads neither the state nor the strings
What each asks of keeps is had from `K4KeepsM` (Law/KeepsStep.lean).

  `k4Keeps_rows`   K4's clause leaves the rows on the table.
  `k4_unmarked_rides`, `k4_row_rides`, `k4_pile_rides`, `k4_constraint_rides`   the four calls.
  `k4_pin_rides`, `k4_indexPin_rides`, `k4_tablePin_rides`   three calls more, at items that the
     member's row owes again (they are no riders): for whoever pays the exchange at these by the
     frame's `exchangeAtS_again` (Honest/Thread/SharesS.lean), which asks besides that the item is
     open in front and `BehindS`: both stay that caller's.
  `k4_ridesPast_column_at`   **the column at one member**, from A and hK.
  `k4_ridesPast_column`   **the column at every number of the kind K4, at the letters of
     `owesS_head_form`**: Rd the sentence of a list of clauses, keeps by the place's kind.
  `k4_ridesPastS`   `RidesPastS` there.

Not shown here. hK, clauseGivesKeeps: the thread's parameter for keeps, at K4's place, gives
`K4KeepsM`. A parameter that never holds meets it emptily; that `K4KeepsM` holds behind an accepting
step of the member is `k4_keepsM_step` (Law/KeepsStep.lean), under two hypotheses on the member. THE
STATEMENTS SPEAK ONLY WHERE THE THREAD STANDS IN FRONT OF THE MEMBER, keeps holds and the item's
sentence holds in front: where the thread stands nowhere they hold emptily. THAT THE THREAD STANDS
AT ANY RUN IS NOT SHOWN; of h together with the thread in front, keeps and an item's sentence no
example is known to us. Every limit of Law/ObjectsRidesHead.lean's head holds here. h: the library's
hypothesis
`P5J.AtMgA` (Johnson/P5J/MgAtAll.lean). THE FULL SIZE ALONE, and the format's second hash function alone
(`OnBytes.secondHashFunction`). It imports a module under Johnson/Goal/ outright, and more through
Law/ObjectsRidesHead.lean. A LAW, NOT A PART: no file that defines a part of the proof file's
description may import this one. Nothing on soundness, on completeness or on any other property.

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.RidersSorted
import Johnson.Desc.ProofFile.Honest.K4.Law.ObjectsRidesHead
import Johnson.Desc.ProofFile.Honest.K4.Law.KeepsStep
import Johnson.Desc.ProofFile.Honest.Thread.PinRides
import Johnson.Desc.ProofFile.Honest.Thread.RowPileRides
import Johnson.Desc.ProofFile.Honest.Thread.HeadPinW
import Johnson.Desc.ProofFile.Honest.Thread.KeepsBy
import Johnson.Desc.ProofFile.Honest.Thread.Riders
import Johnson.Goal.HonestTrace.ConstrAtThread
import Johnson.Desc.K13.Law.PileReadsOut
import Johnson.Road.K4.K04Tied

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes.Road.K4 (AtK4 k04_places_full atK4_full)
open OnBytes.Road.K4.More (PS)
open OnBytes.Maker (WholeD)
open OnBytes.HonestTrace (ridesPastAt_constr)
open VerifiableInference.Desc (Place Chain Strs KindName)
open VerifiableInference.Desc.First (Item RowClass flatPlacesOf)
open VerifiableInference.Desc.Sound (MsgT linksFull)
open VerifiableInference.Desc.K13.Law (rows_not_end)
open P5J (AtMgA CellsM TS parts4)
open ProofFile.Honest.FirstThread (Script WtF lettersHead ridesPastAt_unmarked ridesPastAt_pin
  ridesPastAt_pinI ridesPastAt_pinW ridesPastAt_row ridesPastAt_pile)

/-- **K4's clause of keeps leaves the rows on the table.** In front and behind the record stands in
a layers' segment, where these rows are the pending ones; what goes out is as it was. -/
theorem k4Keeps_rows {s s' : TS} (K : K4Keeps s s') : s'.rows = s.rows := by
  obtain ⟨R, a, _, _, ha, _⟩ := K
  obtain ⟨a', ha', _⟩ := R.here a ha
  exact rows_not_end (fun c hc => by rw [ha] at hc; cases hc)
    (fun c hc => by rw [ha'] at hc; cases hc) R.out

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X' : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X')
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)

/-! ## 1 Sort by sort, general in the thread's two parameters Rd and Kp -/

section
variable (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w₁ : Local W₀ Rc ProofFile.Inst Tr)
  (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X' → Prop)

/-- CONDITIONAL: on h, hp and hK. `unmarked` rides past a member whose clause of keeps
gives `K4KeepsM`. -/
theorem k4_unmarked_rides {b : Nat} {p : Place} (hp : P5J.At.ps[b]? = some p)
    (hK : ∀ s s', Kp p s s' → K4KeepsM s s') :
    RidesPastAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread Said b
      Item.unmarked :=
  ridesPastAtS_of _ Said (ridesPastAt_unmarked h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁
    fun s s' hk => (hK s s' (hk p hp)).2)

/-- CONDITIONAL: on h, hp and hK. A class of rows rides past such a member. -/
theorem k4_row_rides {b : Nat} {p : Place} (hp : P5J.At.ps[b]? = some p)
    (hK : ∀ s s', Kp p s s' → K4KeepsM s s') (m : Nat) (c : RowClass) :
    RidesPastAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread Said b
      (Item.row m c) :=
  ridesPastAtS_of _ Said (ridesPastAt_row h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ m c
    fun s s' hk => ⟨(hK s s' (hk p hp)).1.1.st, (hK s s' (hk p hp)).1.1.book⟩)

/-- CONDITIONAL: on h, hp and hK. `pile` rides past such a member. -/
theorem k4_pile_rides {b : Nat} {p : Place} (hp : P5J.At.ps[b]? = some p)
    (hK : ∀ s s', Kp p s s' → K4KeepsM s s') :
    RidesPastAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread Said b
      Item.pile :=
  ridesPastAtS_of _ Said (ridesPastAt_pile h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁
    fun s s' hk => ⟨(hK s s' (hk p hp)).1.1.st, (hK s s' (hk p hp)).1.1.book,
      k4Keeps_rows (hK s s' (hk p hp)).1⟩)

/-- CONDITIONAL: on h and hq. A part of a segment's relation, one of the four, rides past every
member: nothing is asked of keeps. -/
theorem k4_constraint_rides (b l : Nat) {q : P5J.TPart} (hq : q ∈ parts4) :
    RidesPastAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread Said b
      (Item.constr l q) :=
  ridesPastAtS_of _ Said (ridesPastAt_constr h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ b l hq)

/-- CONDITIONAL: on h, hp and hK. A moment's pin rides past such a member. -/
theorem k4_pin_rides {b : Nat} {p : Place} (hp : P5J.At.ps[b]? = some p)
    (hK : ∀ s s', Kp p s s' → K4KeepsM s s') (m t : Nat) :
    RidesPastAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread Said b
      (Item.pin m t) :=
  ridesPastAtS_of _ Said (ridesPastAt_pin h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ m t
    fun s s' hk => (hK s s' (hk p hp)).1.1.st)

/-- CONDITIONAL: on h, hp and hK. The index masks' pin rides past such a member. -/
theorem k4_indexPin_rides {b : Nat} {p : Place} (hp : P5J.At.ps[b]? = some p)
    (hK : ∀ s s', Kp p s s' → K4KeepsM s s') :
    RidesPastAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread Said b
      Item.pinI :=
  ridesPastAtS_of _ Said (ridesPastAt_pinI h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁
    fun s s' hk => (hK s s' (hk p hp)).1.1.st)

/-- CONDITIONAL: on h. The stored table's pin rides past every member. -/
theorem k4_tablePin_rides (b : Nat) :
    RidesPastAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread Said b
      Item.pinW :=
  ridesPastAtS_of _ Said (ridesPastAt_pinW h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ b)

/-! ## 2 The column at one member -/

/-- CONDITIONAL: on h, A and hK. **EVERY ITEM THAT IS OPEN IN FRONT OF K4's MEMBER AND THAT ITS ROW
NEITHER SHUTS NOR OWES RIDES PAST IT.** The end is an implication from the thread's sentence in
front, keeps and the item's own sentence in front. -/
theorem k4_ridesPast_column_at {b m : Nat} {p : Place} (A : AtK4 linksFull PS b m p)
    (hK : ∀ s s', Kp p s s' → K4KeepsM s s') :
    ∀ i ∈ (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.opened b,
      i ∉ ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.row b).shuts →
      i ∉ ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.row b).owes →
      RidesPastAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread Said b i := by
  intro (i : Item) hi hs ho
  rcases riders_are_sorted (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁)
    ridersAreSorted_full A hi hs ho with rfl | rfl | ⟨c, rfl⟩ | rfl | ⟨l, q, hq, rfl⟩
  · exact k4_unmarked_rides h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ Said A.here hK
  · exact k4_pile_rides h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ Said A.here hK
  · exact k4_row_rides h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ Said A.here hK m c
  · exact k4_ridesPastAtS_objects_at h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ Said b m A hK
  · exact k4_constraint_rides h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ Said b l hq

end

/-! ## 3 At every number of the kind, at the letters of the frame's gathering -/

section
variable (cs : List (RiderCl (Local W₀ Rc ProofFile.Inst Tr) TS))
  (f : KindName → Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)
  (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X' → Prop)

/-- CONDITIONAL: on h and clauseGivesKeeps: the kind's clause of keeps gives `K4KeepsM`. **THE
COLUMN hR OF `owesS_head_form` AT EVERY NUMBER OF THE KIND K4.** -/
theorem k4_ridesPast_column (clauseGivesKeeps : ∀ p s s', f KindName.K4 p s s' → K4KeepsM s s') :
    ∀ b p, P5J.At.ps[b]? = some p → p.kind = KindName.K4 →
      ∀ i ∈ (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf cs) (kpBy f)
          w).thread.opened b,
      i ∉ ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf cs) (kpBy f)
          w).thread.row b).shuts →
      i ∉ ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf cs) (kpBy f)
          w).thread.row b).owes →
      RidesPastAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf cs) (kpBy f)
          w).thread Said b i := by
  intro b p hb hk
  have hb' : (flatPlacesOf linksFull true)[b]? = some p := hb
  obtain ⟨g, hg, rfl, rfl⟩ := k04_places_full b p hb' hk
  exact k4_ridesPast_column_at h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf cs) (kpBy f) w Said
    (atK4_full g hg) fun s s' hkp => clauseGivesKeeps _ s s' ((kpBy_at f hk s s').1 hkp)

/-- CONDITIONAL: on h and clauseGivesKeeps. **`RidesPastS` AT EVERY NUMBER OF THE KIND K4.** -/
theorem k4_ridesPastS (clauseGivesKeeps : ∀ p s s', f KindName.K4 p s s' → K4KeepsM s s') :
    ∀ b p, P5J.At.ps[b]? = some p → p.kind = KindName.K4 →
      RidesPastS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf cs) (kpBy f)
          w).thread Said b :=
  fun b p hb hk => ridesPastS_shares _ Said
    (k4_ridesPast_column h H Q test carryX item n₁ n₂ b₀ Vd cs f w Said clauseGivesKeeps b p hb hk)

end

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.k4Keeps_rows
#print axioms ProofFile.Honest.K4.k4_unmarked_rides
#print axioms ProofFile.Honest.K4.k4_row_rides
#print axioms ProofFile.Honest.K4.k4_pile_rides
#print axioms ProofFile.Honest.K4.k4_constraint_rides
#print axioms ProofFile.Honest.K4.k4_pin_rides
#print axioms ProofFile.Honest.K4.k4_indexPin_rides
#print axioms ProofFile.Honest.K4.k4_tablePin_rides
#print axioms ProofFile.Honest.K4.k4_ridesPast_column_at
#print axioms ProofFile.Honest.K4.k4_ridesPast_column
#print axioms ProofFile.Honest.K4.k4_ridesPastS
