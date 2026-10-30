-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/PlaysAtArms.lean: the kind "the code switch" (K2): THE DEBT "IT
PLAYS", ASKED FROM THE PAIR (`PlaysS`, Honest/Thread/PaysS.lean), AT THE FRAME's OWN THREAD OF THE
FIRST CHAIN AT THE LIBRARY's HEAD (`lettersHead`, Honest/Thread/FirstHead.lean), AT THE KIND's TWO
ARMS: 339, the output head's switch, and 353, the switch behind the last segment: AT EVERY LETTER
`Said`: `switch_playsS` (PlaysScript.lean of this folder) WITH TWELVE OF ITS SIXTEEN PREMISES PAID
UNDER THE HEAD AND FOUR LEFT BY NAME. Four definitions with code: public tests; eight closed facts
by Lean's kernel, three of them controls; statements with their proofs: joins.

WHICH SLOT IT IS FOR. The frame's gather of the first chain's debts (`owesS_framesK`,
Honest/Thread/GatherSilentK9At.lean) asks `PlaysS` by
number: among its numbers are 339 (its premise hPhear, at link 24, at the link's sub-protocol number
1 in front of its batching) and 353 (hP353). Its end, `OwesS` at that thread, is one of the premises
from which a value of `ThreadsC` (Honest/Law/ThreadStratC.lean) is built; acceptance at a request
goes through that structure. At a member p of `switchPlaces` `switch_playsS_at` of this file gives
`PlaysS` at the number where the written list first bears p.place, under the same four premises;
under the head that is the member's own number in the chain's flat list (`borderNo_written`,
Honest/K1/Law/MembersByBorder.lean; the switch places' borders: `borders_at_head`,
SwitchBorders.lean of this folder): not called here.

  `rootsB`, `rootsAnyB`, `rootsW`, `rootsW_can_fail`   at each of the 25 written places the plan's
                    numbers state one root for each oracle message; with one root more: no, AT
                    EVERY PLACE
  `opensAllB`, `opensAllW`, `opensAllW_can_fail`   at each of the 25 written places every tree that
                    the switch reads is told in front of the place's number; counted nine
                    sub-protocols earlier: no
  `opensArmB`, `armsOpensW_can_fail`   THE SAME TEST AT ONE ARM ALONE: at 339 it says yes counted
                    nine sub-protocols earlier and no counted ten; at 353 yes at eight, no at nine
  `armsReadW`       each arm's switch reads three trees: so the test on the trees is not idle there
  `armsPlacesW`     the last two of the 25 written places are the two arms', in that order
  `arms_at_head`    so, under the head and the opening, a member of `switchPlaces` stands at each
                    arm's place: the ends' p is not asked of nothing
  `armNosW`         the written list of places first bears the two arms' places at 339 and 353
  `switch_playsS_at`   A TOOL, GENERAL IN THE PLACE: the debt at the number where the written list
                    first bears p.place. AT A LINK's PLACE IT HAS THE DEBT TOO, under the four
                    premises that are left, with the closing's public test paid: it is typed for the
                    arms
  `head_playsS_head`, `fin_playsS_head`   THE ENDS: at 339 and at 353

PAID INSIDE, UNDER THE HEAD AND THE OPENING: here (`k2_member_at_head`, RecordAtHead.lean) · place ·
rounds · oracles (`k2_block_at_head`, BlockAtHead.lean) · roots · opens (the two closed facts) ·
`Sizes.serves` · `Sizes.roomy` · `placeFits` · the number of answers (PublicAtHead.lean) · the
oracle messages' shapes (`place_shapes`, PlaysAtPlan.lean) · `closingOk` (`closing_at_head`,
ClosingAtHead.lean): all of this folder.

LEFT, BY NAME, ALL FOUR. ON THE PROVER H: (1) the half: the search in H.first finds the kind's half
at p (at the prover that the frame's maker returns: `head_half_fill`, `fin_half_fill`,
HalfAtArms.lean of this folder). ON THE SCRIPT Q, AT THE MEMBER's OWN TREES: (2) `K2Script`: it
reads the numbers' roots alone; it is asked at every name and dress. ON THE SCRIPT Q, AT EARLIER
MEMBERS' TREES: (3) the widths, at a stand of the pair. ON THE LETTERS Vd AND w: (4) if Vd holds of
w, its public instance passes `publicOk`. BESIDE THE FOUR STAND TWO LOOK-UPS AMONG THE BINDERS, no
debts: hP, hn: the lot's preparation and the plan's numbers at the place's link: `k2_block_at_head`
has both under the head.

Kin, of this folder. `opensB`, `opensW`, `opensW_can_fail` (PublicAtWritten.lean): the test on the
trees at the 23 links, by the number 14 (i + 1) + 2: `opensAllB` is its sister over all 25, by the
number where the written list first bears the place: of the 23 links it holds nothing that `opensW`
does not hold already. The two equations of `armNosW` are also the second and third limb of
`SwitchArm` (BlockAtHead.lean), there under the head and at a member of the plan's list: here they
are closed facts on the written list, so that no case on the arm is wanted.

Limits. THE FOUR ARE SHOWN MET TOGETHER NOWHERE. WHERE THE THREAD HAS NO STAND THE DEBT IS PAID FOR
NOTHING, AND NO STAND IS SHOWN. ONE DEBT OF FIVE. CLOSED FACTS BY LEAN's KERNEL, REPLAYED BY NO
INDEPENDENT CHECKER; the thresholds in `armsOpensW_can_fail` were read off a run of Lean's plain
evaluator first, then put to the kernel. The head and the opening are premises. The full size; the
format's second hash function. On returning and on what is laid: nothing on whether the verifier's step says
yes. NOT IN FRONT OF A LAW OVER COINS. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.PlaysScript
import Johnson.Desc.ProofFile.Honest.K2.Law.RecordAtHead
import Johnson.Desc.ProofFile.Honest.K2.Law.BlockAtHead
import Johnson.Desc.ProofFile.Honest.K2.Law.ClosingAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc (Block Chain Place Strs)
open VerifiableInference.Desc.First (S treesTold)
open VerifiableInference.Desc.First.K2Ties (toldFull)
open VerifiableInference.Desc.K2.Honest.Returns (headPlaceAt)
open VerifiableInference.Desc.Sound (MsgT)
open P1K2 (Prep Nums numsAt prepOf)
open IM (k2P k2PlaceF)
open P5J (AtMgA F0T TS CellsM)
open _root_.Desc.K14.Law (secondAt seatZ)
open ProofFile.Honest.FirstThread (lettersHead WtF Script)

/-- A PUBLIC TEST: at each written place the plan's numbers state one root, and d more, for each
oracle message. 0 is the test. -/
def rootsB (d : Nat) : Bool :=
  placesW.all fun p => (numsW p.place.link).any fun n =>
    (P1K2.oraclesAt n.grp n.codes n.sent).length == n.roots + d

/-- A PUBLIC TEST: at each written place every tree that the switch reads is told in front of the
number where the written list of places first bears the place. back: how many sub-protocols in front
of that number the told trees are counted; 0 is the test. -/
def opensAllB (back : Nat) : Bool :=
  placesW.all fun p => (numsW p.place.link).any fun n =>
    n.read.all fun t => decide (t.1 < treesTold toldFull (P5J.At.ps.findIdx (· == p.place) - back))

/-- For a control: `rootsB` with "at some place" for "at each place". -/
def rootsAnyB (d : Nat) : Bool :=
  placesW.any fun p => (numsW p.place.link).any fun n =>
    (P1K2.oraclesAt n.grp n.codes n.sent).length == n.roots + d

/-- For a control: `opensAllB`'s test at one arm alone: i = 0: the output head's switch; i = 1: the
switch behind the last segment. No where the list has no such place. -/
def opensArmB (i back : Nat) : Bool :=
  ((placesW.drop 23)[i]?).any fun p => (numsW p.place.link).any fun n =>
    n.read.all fun t => decide (t.1 < treesTold toldFull (P5J.At.ps.findIdx (· == p.place) - back))

set_option maxRecDepth 1000000 in
/-- BY LEAN's KERNEL. -/
theorem rootsW : rootsB 0 = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- A control: with one root more the test says no, at every place. -/
theorem rootsW_can_fail : rootsB 1 = false ∧ rootsAnyB 1 = false := by decide +kernel

set_option maxRecDepth 1000000 in
/-- BY LEAN's KERNEL. -/
theorem opensAllW : opensAllB 0 = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- A control: it fails at the links' places already. -/
theorem opensAllW_can_fail : opensAllB 9 = false := by decide +kernel

set_option maxRecDepth 1000000 in
/-- A control AT EACH ARM ALONE. -/
theorem armsOpensW_can_fail : opensArmB 0 9 = true ∧ opensArmB 0 10 = false ∧
    opensArmB 1 8 = true ∧ opensArmB 1 9 = false := by decide +kernel

set_option maxRecDepth 1000000 in
/-- BY LEAN's KERNEL: each arm's switch reads three trees. -/
theorem armsReadW : ((placesW.drop 23).all fun p =>
    (numsW p.place.link).any fun n => n.read.length == 3) = true ∧
    (placesW.drop 23).length = 2 := by decide +kernel

set_option maxRecDepth 1000000 in
/-- BY LEAN's KERNEL: which places the last two written places bear. -/
theorem armsPlacesW : (placesW.drop 23).map (·.place) = [headPlaceAt, k2PlaceF] := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- BY LEAN's KERNEL: the two arms' numbers. -/
theorem armNosW : P5J.At.ps.findIdx (· == headPlaceAt) = 339 ∧
    P5J.At.ps.findIdx (· == k2PlaceF) = 353 := by decide +kernel

variable {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
  {Wp : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}

/-- **Under the head and the opening a member of the plan's list stands at each arm's place.** -/
theorem arms_at_head (h : AtMgA OnBytes.secondHashFunction Wp D r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction Wp.pol Wp.lay Wp.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) :
    (∃ p ∈ switchPlaces Zp Bs.G₀, p.place = headPlaceAt) ∧
      ∃ p ∈ switchPlaces Zp Bs.G₀, p.place = k2PlaceF := by
  rw [places_at_head h.toAtMg O]
  have m₁ : headPlaceAt ∈ (placesW.drop 23).map (·.place) := by
    rw [armsPlacesW]
    simp
  have m₂ : k2PlaceF ∈ (placesW.drop 23).map (·.place) := by
    rw [armsPlacesW]
    simp
  obtain ⟨p, hp, ep⟩ := List.mem_map.1 m₁
  obtain ⟨p', hp', ep'⟩ := List.mem_map.1 m₂
  exact ⟨⟨p, List.mem_of_mem_drop hp, ep⟩, p', List.mem_of_mem_drop hp', ep'⟩

/-- hhalf, Sc, hW AND hv ARE PREMISES. **A TOOL, GENERAL IN THE PLACE: THE DEBT AT THE HEAD's
THREAD**, at a member of `switchPlaces` and the plan's numbers. Dt, readers: the lot's two letters.
-/
theorem switch_playsS_at (h : AtMgA OnBytes.secondHashFunction Wp D r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction Wp.pol Wp.lay Wp.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) {Bk : ProverCoinCounts}
    {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (Dt : RowDataOf ProofFile.Inst) (readers : Local W₀ Rc ProofFile.Inst Tr → Readers)
    {p : SwitchPlace} (hp : p ∈ switchPlaces Zp Bs.G₀) {Pp : Prep} {n : Nums}
    (hP : prepOf Zp Bs.G₀ = some Pp) (hn : numsAt Pp p.place.link = some n)
    (hhalf : (H.first.find? fun a => a.place == p.place) =
      some (switchHalf (coreSender freshTable) Dt readers
        (lotClosingAt Bs.G₀.first.layout (segmentsOf Zp Bs.G₀)) p))
    (Sc : ∀ (nm : String) (st : VerifiableInference.Desc.First.K2.At),
      K2Script (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
        (P5J.At.ps.findIdx (· == p.place)) (coreSender freshTable) Dt readers
        (lotClosingAt Bs.G₀.first.layout (segmentsOf Zp Bs.G₀)) p (k2P Zp p.place nm st n))
    (hW : ∀ t ∈ n.read, ∀ k s m E,
      ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
        (P5J.At.ps.findIdx (· == p.place)) k s m E →
      ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.tableAt (.own t.1) k
        m).2.words = t.2.2)
    (hv : Vd w →
      publicOk Dt Bs.G₀.first.layout p ((segmentsOf Zp Bs.G₀).take p.link) w.x = true) :
    PlaysS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
      (P5J.At.ps.findIdx (· == p.place)) := by
  obtain ⟨blk, hb, -⟩ := k2_member_at_head h O hp
  obtain ⟨Pp', n', nm, st, -, -, hP', hn', -, ⟨hpc, hro, hor⟩, -, -⟩ := k2_block_at_head h O hp hb
  obtain rfl : Pp' = Pp := Option.some.inj (hP'.symm.trans hP)
  obtain rfl : n' = n := Option.some.inj (hn'.symm.trans hn)
  have hpW : p ∈ placesW := by
    rw [← places_at_head h.toAtMg O]
    exact hp
  have a₁ : (numsW p.place.link).any (fun n =>
      (P1K2.oraclesAt n.grp n.codes n.sent).length == n.roots + 0) = true :=
    List.all_eq_true.1 rootsW p hpW
  rw [numsW_at_head h.toAtMg O hP, hn] at a₁
  have a₂ : (numsW p.place.link).any (fun n => n.read.all fun t =>
      decide (t.1 < treesTold toldFull (P5J.At.ps.findIdx (· == p.place) - 0))) = true :=
    List.all_eq_true.1 opensAllW p hpW
  rw [numsW_at_head h.toAtMg O hP, hn] at a₂
  exact switch_playsS _ Said _ blk Dt readers Bs.G₀.first.layout (segmentsOf Zp Bs.G₀) p
    (k2P Zp p.place nm st _) hb hpc (by rw [hpc]; exact hhalf) hro hor (beq_iff_eq.1 a₁)
    (fun t ht => by
      show t.1 < treesTo cF.blocksInOrder _
      rw [treesTo_at_head h.toAtMg O]
      exact of_decide_eq_true (List.all_eq_true.1 a₂ t ht))
    (Sc nm st) hW (serves_at_head h.toAtMg O p hp) (roomy_at_head h.toAtMg O p hp)
    (fits_at_head h.toAtMg O p hp) (place_shapes hP hp hn)
    (answers_at_head h.toAtMg O hP p hp _ hn) (closing_at_head h.toAtMg O p hp)
    (fun v hvv => by
      obtain ⟨rfl, hV⟩ := hvv
      exact hv hV)

/-- hhalf, Sc, hW AND hv ARE PREMISES. **THE DEBT AT 339, THE OUTPUT HEAD's SWITCH.** -/
theorem head_playsS_head (h : AtMgA OnBytes.secondHashFunction Wp D r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction Wp.pol Wp.lay Wp.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) {Bk : ProverCoinCounts}
    {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (Dt : RowDataOf ProofFile.Inst) (readers : Local W₀ Rc ProofFile.Inst Tr → Readers)
    {p : SwitchPlace} (hp : p ∈ switchPlaces Zp Bs.G₀) (hpp : p.place = headPlaceAt)
    {Pp : Prep} {n : Nums}
    (hP : prepOf Zp Bs.G₀ = some Pp) (hn : numsAt Pp p.place.link = some n)
    (hhalf : (H.first.find? fun a => a.place == p.place) =
      some (switchHalf (coreSender freshTable) Dt readers
        (lotClosingAt Bs.G₀.first.layout (segmentsOf Zp Bs.G₀)) p))
    (Sc : ∀ (nm : String) (st : VerifiableInference.Desc.First.K2.At),
      K2Script (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread 339
        (coreSender freshTable) Dt readers
        (lotClosingAt Bs.G₀.first.layout (segmentsOf Zp Bs.G₀)) p (k2P Zp p.place nm st n))
    (hW : ∀ t ∈ n.read, ∀ k s m E,
      ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 339 k s m E →
      ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.tableAt (.own t.1) k
        m).2.words = t.2.2)
    (hv : Vd w →
      publicOk Dt Bs.G₀.first.layout p ((segmentsOf Zp Bs.G₀).take p.link) w.x = true) :
    PlaysS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 339 := by
  have e : P5J.At.ps.findIdx (· == p.place) = 339 := by
    rw [hpp]
    exact armNosW.1
  have g := switch_playsS_at h O H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said Dt readers hp hP hn
    hhalf (by rw [e]; exact Sc) (by rw [e]; exact hW) hv
  rw [e] at g
  exact g

/-- hhalf, Sc, hW AND hv ARE PREMISES. **THE DEBT AT 353, BEHIND THE LAST SEGMENT.** -/
theorem fin_playsS_head (h : AtMgA OnBytes.secondHashFunction Wp D r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction Wp.pol Wp.lay Wp.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) {Bk : ProverCoinCounts}
    {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (Dt : RowDataOf ProofFile.Inst) (readers : Local W₀ Rc ProofFile.Inst Tr → Readers)
    {p : SwitchPlace} (hp : p ∈ switchPlaces Zp Bs.G₀) (hpp : p.place = k2PlaceF)
    {Pp : Prep} {n : Nums}
    (hP : prepOf Zp Bs.G₀ = some Pp) (hn : numsAt Pp p.place.link = some n)
    (hhalf : (H.first.find? fun a => a.place == p.place) =
      some (switchHalf (coreSender freshTable) Dt readers
        (lotClosingAt Bs.G₀.first.layout (segmentsOf Zp Bs.G₀)) p))
    (Sc : ∀ (nm : String) (st : VerifiableInference.Desc.First.K2.At),
      K2Script (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread 353
        (coreSender freshTable) Dt readers
        (lotClosingAt Bs.G₀.first.layout (segmentsOf Zp Bs.G₀)) p (k2P Zp p.place nm st n))
    (hW : ∀ t ∈ n.read, ∀ k s m E,
      ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 353 k s m E →
      ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.tableAt (.own t.1) k
        m).2.words = t.2.2)
    (hv : Vd w →
      publicOk Dt Bs.G₀.first.layout p ((segmentsOf Zp Bs.G₀).take p.link) w.x = true) :
    PlaysS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 353 := by
  have e : P5J.At.ps.findIdx (· == p.place) = 353 := by
    rw [hpp]
    exact armNosW.2
  have g := switch_playsS_at h O H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said Dt readers hp hP hn
    hhalf (by rw [e]; exact Sc) (by rw [e]; exact hW) hv
  rw [e] at g
  exact g

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.rootsB
#print axioms ProofFile.Honest.K2.Law.opensAllB
#print axioms ProofFile.Honest.K2.Law.rootsAnyB
#print axioms ProofFile.Honest.K2.Law.opensArmB
#print axioms ProofFile.Honest.K2.Law.rootsW
#print axioms ProofFile.Honest.K2.Law.rootsW_can_fail
#print axioms ProofFile.Honest.K2.Law.opensAllW
#print axioms ProofFile.Honest.K2.Law.opensAllW_can_fail
#print axioms ProofFile.Honest.K2.Law.armsOpensW_can_fail
#print axioms ProofFile.Honest.K2.Law.armsReadW
#print axioms ProofFile.Honest.K2.Law.armsPlacesW
#print axioms ProofFile.Honest.K2.Law.armNosW
#print axioms ProofFile.Honest.K2.Law.arms_at_head
#print axioms ProofFile.Honest.K2.Law.switch_playsS_at
#print axioms ProofFile.Honest.K2.Law.head_playsS_head
#print axioms ProofFile.Honest.K2.Law.fin_playsS_head
