-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/K1RelsDigits.lean: the three relations of the library between
the verifier's states before and after the sending of a segment's digits (kind K1) that the lemma on
the open item `forms m k r` asks (`ridesPastAt_forms_rec_test`, FormsKinds.lean), at the first
chain's invariant at `lettersHead`, from the invariant before the step and the sub-protocol's
accepting step. No definition.

K1RelsAtHead.lean has two of them (`K1.RecRides`, `K1.ReadersStay`). The third is `K1.AheadMeets`
(Johnson/Desc/K1/Law/GoAtLaterForms.lean): an array that the table's numbers hold "ahead" before the
sending, and that is found after it under a new number, sits at the seat and has the shape that were
foretold. The library shows it from eight facts on the two states (`aheadMeets_of`,
Johnson/Desc/K1/Law/AheadAtDigits.lean), and joins these under the table's condition with a file's
strings (`hmeet_plus13`, same file). Here the same eight facts are supplied without strings:
  * the public test "frame.sentIs1" before the step: it is among the public items that are open at
    the border (`sent1Asked_full`, by Lean's kernel), whose tests the invariant holds
    (`xk_ew_front`, K9FormBehind.lean; `First.ePubAt_mem`, Johnson/Desc/First/EPubAt.lean)
  * the same test after the step, what the sending does to the list of trees, to the shapes and to
    the codes: the library's `sentIs_laterAt`, `laterSend_laterAt`, `laterSeated_blkL`,
    `laterGrows_laterAt`, off the decision's yes
  * the shape of the open segment's frame: `head_live` (HeadLive.lean)
  * the list of trees has a place for every message, and the plan's number of trees: `head_book`
    (RowPileForwardKinds.lean)
  * the executable test on the plan `aheadAtB`: the library's `hAtA_atAll`
    (Johnson/Desc/K1/Law/TestsAtAll.lean)

  1  `sent1Asked_full`, `sent1Asked_control`   the closed test and a negative test: in front of the
     sending of the reads of segment 3 the name is not among the open public items
  2  `k1_rels_digits`   the three relations, at one list of new numbers

Limits.
  * Full size only, and only under the library's hypothesis `AtMgA` at the hash function `secondHashFunction`
    (FirstAt.lean says which that is).
  * The lemma takes the sub-protocol's step. The condition `RidesPastAt` has the clause of `keeps`
    alone: to serve there, the conclusion has to be a part of that clause.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.K1RelsAtHead
import Johnson.Desc.ProofFile.Honest.Thread.RowPileForwardKinds
import Johnson.Desc.ProofFile.Honest.Thread.K9FormBehind
import Johnson.Desc.ProofFile.Honest.Thread.HeadLive
import Johnson.Desc.K1.Law.AheadAtDigits
import Johnson.Desc.K1.Law.CallsE

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Block Chain Strs Wit Place)
open VerifiableInference.Desc.First (Item Pub flatPlacesOf)
open VerifiableInference.Desc.Sound (MsgT linksFull moreAll)
open VerifiableInference.Desc.K13.Law (openAt)
open VerifiableInference.Desc.K1 (noL RecRides AheadMeets ReadersStay place_fifty k01_flat
  yesOf_of_yes rounds_blkL sentIs_laterAt gpOf laterSend_laterAt aheadMeets_of laterSeated_blkL
  laterGrows_laterAt hAtA_atAll pin1_atAll pin2_atAll formsAt_full formsAt_of inSetB inSet_of)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)

/-! ## 1 The closed test -/

set_option maxRecDepth 1000000 in
/-- In front of the sending of each segment's digits the segment's name "frame.sentIs1" is among the
public items that are open there. -/
theorem sent1Asked_full : ((List.range 25).all fun l =>
    inSetB moreAll IM.linksW IM.placesW (noL l true)
      (Pub.more (some l) "frame.sentIs1")) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A negative test: in front of the sending of the reads of segment 3 it is not. -/
theorem sent1Asked_control :
    inSetB moreAll IM.linksW IM.placesW (noL 3 false)
      (Pub.more (some 3) "frame.sentIs1") = false := by
  decide +kernel

/-! ## 2 The three relations -/

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- After the sending of the digits of segment `l`: `RecRides` and `AheadMeets` at one list of new
numbers; every item `forms` that is open before the step is the segment's own, and the readers'
answers at it stay. -/
theorem k1_rels_digits {l : Nat} (hl : l < 25) {blk : Block TS ProofFile.Cl}
    (hblk : cF.blocksInOrder[noL l true]? = some blk)
    {k : Coins Bk} {s s' : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    {ds : List Fmt.Drawn} {y : List Played × Mid (Local W₀ Rc ProofFile.Inst Tr) X}
    {cols : List VerifiableInference.Desc.OpenedColumn}
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
      (noL l true) k s m E)
    (hS : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Stepped blk k s m E ds y
      cols s') :
    ∃ new, RecRides new s s' ∧
      AheadMeets (h.𝔇.N.sent l) (h.𝔇.N.group l) new s s' ∧
      ∀ mm kk ρ, Item.forms mm kk ρ ∈ openAt linksFull (flatPlacesOf linksFull true)
          (noL l true) →
        mm = l ∧ ReadersStay h.𝔇.pubD mm kk ρ s s' := by
  have hT' := hT
  unfold Thr at hT'
  obtain ⟨-, -, hF, -, -, -, -⟩ := hT'
  have hyes : IM.Yes 0 blk s s' := ⟨roundsOf y.1, cols, cols.length, hS.2⟩
  have hb : noL l true ≤ cF.blocksInOrder.length :=
    Nat.le_of_lt (List.getElem?_eq_some_iff.1 hblk).1
  have hxE := xk_ew_front h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hF
  obtain ⟨b1, b2⟩ := head_book h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hT
  have hlive := head_live h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hb hT
    (place_fifty l hl true) rfl
  obtain ⟨-, -, hRS⟩ := k1_rels_behind h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hl true hblk hT hS
  obtain ⟨Bs, base₀, O⟩ := h.laid.opened
  obtain ⟨e, X₁, arrs, he, hu⟩ := k01_flat h.scope h.reads O l hl true
  obtain rfl : e = blk := Option.some.inj (he.symm.trans hblk)
  obtain ⟨-, rs, gs, hfit, hd⟩ := yesOf_of_yes hu hyes m.st.input.x.pub
  have hlen : rs.length = 2 := (VerifiableInference.Desc.Keeps.fit_length _ _ hfit).trans
    (rounds_blkL Zp Bs.G₀ l true X₁ arrs)
  obtain ⟨r₁, r₂, rfl⟩ := List.length_eq_two.1 hlen
  have h0 := VerifiableInference.Desc.First.ePubAt_mem _ _ _ _ _ _ (IM.xk_parts hxE).2.2.2.2 _
    (Or.inl (inSet_of (List.all_eq_true.1 sent1Asked_full l (List.mem_range.2 hl))))
  rw [VerifiableInference.Desc.First.pubAll_more_sentIs1] at h0
  have h1 := sentIs_laterAt Bs.G₀.first (gpOf Zp) l _ 2 arrs s s' _ _
    gs hd h.𝔇.pubD.dS1 l h0
  have hLS := laterSend_laterAt Bs.G₀.first (gpOf Zp) l _ 2 arrs s s' _
    gs rfl hd
  refine ⟨_, hLS.2.1, ?_, fun mm kk ρ ho => ⟨?_, hRS mm kk ρ ho⟩⟩
  · exact aheadMeets_of h0 h1 (fun Lk hLk => (hlive Lk hLk).2) hLS.2.2 b2
      (laterSeated_blkL Zp Bs.G₀ l true X₁ arrs s s' _ gs rfl hd).2.1
      (laterGrows_laterAt Bs.G₀.first (gpOf Zp) l _ 2 arrs s s' _ gs hd).1
      (by
        rw [b1]
        exact hAtA_atAll h O (pin1_atAll h) (pin2_atAll h) l hl)
  · have hk := List.all_eq_true.1 formsAt_full l (List.mem_range.2 hl)
    rw [Bool.and_eq_true] at hk
    exact eq_of_beq (formsAt_of hk.2 ho)

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.sent1Asked_full
#print axioms ProofFile.Honest.FirstThread.sent1Asked_control
#print axioms ProofFile.Honest.FirstThread.k1_rels_digits
