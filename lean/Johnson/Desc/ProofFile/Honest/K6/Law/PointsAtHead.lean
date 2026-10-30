-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K6/Law/PointsAtHead.lean: THE OUTPUT HEAD's OWN SUB-PROTOCOL (K6): THE
PREMISE points OF `K6HeadDebts` AND OF `K6HeadBelow`, AND THE FIELD keyTie OF `K6Script`, UNDER THE
HYPOTHESIS h, AT THE BLANK GROUND (hG), WHERE THE THREAD STANDS: the two equations on public values
that Honest/K6/Law/PointsOfNumbers.lean left as premises are paid here under h and hG. No
definition; eight theorems.

What is here.
  `k6_rounds_of_cut`     GENERAL: how many rounds the first n blocks of a list declare, off the
                         library's rows of that list (`cutOf`,
                         Johnson/Desc/Ok/PlanWritten/CutTest.lean: a row holds its block's
                         number of rounds)
  `k6_cut340_closed`     A CLOSED FACT, BY LEAN's KERNEL: the first 340 rows of the library's
                         written list `cutFirstFull` hold 46,289 rounds in all
  `k6_count340_at_head`  under h: the first 340 members of the first chain's flat list declare
                         46,289 rounds: by the library's `P5J.pins_of_laid`
                         (Johnson/Goal/Skeleton/PinsOfLaid.lean): under h the flat list's rows
                         are the written ones
  `headLook_at_head`     under h and hG: what the small input's maker takes for the lookup on
                         the head's calls: the public structure's own shape, and 46,289
  `headLookShapeIs_at_head`  **(shape) PAID**
  `headLookBaseIs_at_head`   **(number) PAID**
  `k6_points_at_head`    **THE PREMISE points**
  `k6_keyTie_at_head`    **THE FIELD keyTie**; besides: b₀ ≤ 341

By. (shape): the authors of the kind "lookup"'s `head_calls_site_found`
(Honest/K3/Law/Thread/HeadCallsTie.lean) and `site_facts` (Honest/K3/Law/MemberSite.lean) against
our `HeadFull.place` (Honest/K6/Law/FitsOf.lean): both read the library's `placeAt` at link 24.
The pair: the lines of `headFitsB_of`'s inner step (FitsOf.lean), again.

Limits.
  * THAT THE THREAD STANDS AT ANY RUN: by nothing that we hold: where it stands nowhere the two tops
    hold for nothing.
  * h: the full size and the format's second hash function alone. hG: under h there is such a ground.
  * Two of the lookup's eleven fields are read: zx and zk.
  * IT IMPORTS BY NAME A MODULE UNDER lean/Johnson/Goal/ (Skeleton/PinsOfLaid.lean) and files of the
    authors of the kind "lookup". A law, no part.
  * Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K6.Law.PointsOfNumbers
import Johnson.Desc.ProofFile.Honest.K6.Law.FitsScope
import Johnson.Desc.ProofFile.Honest.K3.Law.MemberSite
import Johnson.Goal.Skeleton.PinsOfLaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K6
open VerifiableInference.Desc (Block Chain Strs Place)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.Kinds (Head.Law.readsOf)
open VerifiableInference.Desc.Kinds.Head (seatAt parOf given)
open VerifiableInference.Desc.Kinds.Head.Law (workOf)
open VerifiableInference.PlanWritten (cutOf cutFirstFull)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (Script WtF lettersHead)
open ProofFile.Honest.K3 (lookSites)
open ProofFile.Honest.K3.Law (site_facts)
open ProofFile.Honest.K3.Law.AtThr (headCallsShape head_calls_site_found)

/-- GENERAL: the rounds that the first n blocks declare, off the list's rows. -/
theorem k6_rounds_of_cut {S Cl : Type} : ∀ (bs : List (Block S Cl)) (n : Nat),
    ((bs.take n).flatMap (·.rounds)).length = (((cutOf bs).take n).map (·.2.2.1)).sum
  | [], n => by simp [cutOf]
  | _ :: _, 0 => by simp
  | b :: bs, n + 1 => by
    have ih := k6_rounds_of_cut bs n
    unfold cutOf at ih ⊢
    simp only [List.map_cons, List.take_succ_cons, List.flatMap_cons, List.length_append,
      List.sum_cons]
    rw [ih]

set_option maxRecDepth 100000 in
/-- **A closed fact at the library's written rows.** -/
theorem k6_cut340_closed : ((cutFirstFull.take 340).map (·.2.2.1)).sum = 46289 := by
  decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- CONDITIONAL: the hypothesis h. **The first 340 members declare 46,289 rounds.** -/
theorem k6_count340_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    ((cF.blocksInOrder.take 340).flatMap (·.rounds)).length = 46289 := by
  have hc : cutOf cF.blocksInOrder = cutFirstFull := (P5J.pins_of_laid h.scope h.laid).2
  rw [k6_rounds_of_cut, hc]
  exact k6_cut340_closed

/-- CONDITIONAL: h; hG. What the small input's maker takes for the lookup on the head's calls. -/
theorem headLook_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {G : Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) :
    headLookNumbers Zp G = some (G.W.HLy.fs, 46289) := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain rfl : Bs.G₀ = G := Option.some.inj (O.blank.symm.trans hG)
  have Fu := headFull_in_scope h.scope h.reads O.public
  have Tb := headTable_at_blank h.scope h.reads O (congrArg Prod.fst h.toAtMg.plans_written)
  obtain ⟨t1, _⟩ := steps_written Tb.cuts
  obtain ⟨Y, hY, hYn⟩ := Option.map_eq_some_iff.1 Tb.name
  have hYn' : Y.name = "H" := hYn
  obtain ⟨pc, ec, sc⟩ := Fu.place
  unfold headLookNumbers
  rw [hY, Tb.size]
  show (VerifiableInference.Desc.First.Look.placeAt Bs.G₀.W 24 false).bind (fun p =>
    p.shape.bind fun h => (Zp.roundsBefore? (headLookStep Y.name)).bind fun base =>
      some (h, base)) = _
  rw [ec, hYn']
  show pc.shape.bind (fun h => (Zp.roundsBefore? (headLookStep "H")).bind fun base =>
    some (h, base)) = _
  rw [sc, t1]
  rfl

/-- CONDITIONAL: h; hG. **(shape) IS PAID.** -/
theorem headLookShapeIs_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {G : Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) : HeadLookShapeIs Zp G := by
  have hL := headLook_at_head h hG
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain rfl : Bs.G₀ = G := Option.some.inj (O.blank.symm.trans hG)
  obtain ⟨pc, ec, sc⟩ := (headFull_in_scope h.scope h.reads O.public).place
  obtain ⟨s, hs, e1, e2, eS⟩ := head_calls_site_found h
  unfold lookSites at hs
  obtain ⟨a, _, hsa⟩ := List.mem_filterMap.1 hs
  obtain ⟨f1, f2, f3, f4, _⟩ := site_facts _ _ a s hsa
  rw [← f3, ← f4, e1, e2, ← O.W] at f1
  obtain rfl : s.p = pc := Option.some.inj (f1.symm.trans ec)
  have hsh : s.shape = Bs.G₀.W.HLy.fs := Option.some.inj (f2.symm.trans sc)
  unfold HeadLookShapeIs
  rw [hL, eS, hsh]
  rfl

/-- CONDITIONAL: h; hG. **(number) IS PAID.** -/
theorem headLookBaseIs_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {G : Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) : HeadLookBaseIs Zp G cF := by
  unfold HeadLookBaseIs headBaseOf
  rw [headLook_at_head h hG, k6_count340_at_head h]
  rfl

variable (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)
  (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)

/-- CONDITIONAL: the hypothesis h; hG; the thread. **THE PREMISE points OF `K6HeadDebts` AND OF
`K6HeadBelow`.** -/
theorem k6_points_at_head (cells : Tr → Cells) (weights : W₀ → Weights) {G : Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) : ∀ k s m E,
    ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 341 k s m E →
    (seatAt (P5J.At.X Zp).hS (Head.Law.readsOf (P5J.At.X Zp))).lookup s =
      some ((headWit' cells weights Zp G m.st.input).lookup m.st.heard) :=
  k6_points_of_numbers h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said cells weights G
    (headLookShapeIs_at_head h hG) (headLookBaseIs_at_head h hG)

/-- CONDITIONAL: the hypothesis h; hG; the thread; hb₀. **THE FIELD keyTie OF `K6Script`.** -/
theorem k6_keyTie_at_head (hb₀ : b₀ ≤ 341) (cells : Tr → Cells) (weights : W₀ → Weights)
    {G : Ground} (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) : ∀ k s m E,
    ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 341 k s m E →
    given (parOf (P5J.At.X Zp).hS (workOf (P5J.At.X Zp)))
        (seatAt (P5J.At.X Zp).hS (Head.Law.readsOf (P5J.At.X Zp))) s =
      .ok ((headWit' cells weights Zp G m.st.input).given
        (parOf (P5J.At.X Zp).hS (workOf (P5J.At.X Zp))) m.st.heard) :=
  k6_keyTie_of_numbers h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said hb₀ cells weights G
    (headLookShapeIs_at_head h hG) (headLookBaseIs_at_head h hG)

end ProofFile.Honest.K6

#print axioms ProofFile.Honest.K6.k6_rounds_of_cut
#print axioms ProofFile.Honest.K6.k6_cut340_closed
#print axioms ProofFile.Honest.K6.k6_count340_at_head
#print axioms ProofFile.Honest.K6.headLook_at_head
#print axioms ProofFile.Honest.K6.headLookShapeIs_at_head
#print axioms ProofFile.Honest.K6.headLookBaseIs_at_head
#print axioms ProofFile.Honest.K6.k6_points_at_head
#print axioms ProofFile.Honest.K6.k6_keyTie_at_head
