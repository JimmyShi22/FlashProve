-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K6/Law/RidesPastAll.lean: THE OUTPUT HEAD'S OWN ROUNDS (K6), BORDER
341: THE DEBT `RidesPastS` (Honest/Thread/PaysS.lean), WHOLE: every item that is open in front of
the member, that its row neither shuts nor owes, says of the state behind what it says of the state
in front. CONDITIONAL: h (the library's hypothesis on the first chain) · hK (at this sub-protocol's
place the thread's letter for `keeps` gives `K6Keeps`, Johnson/Desc/K6/Honest/Law/Keeps.lean). All
other letters of the thread are general.

  `riders_341`             THE CLOSED LIST: SEVEN ITEMS RIDE PAST THE BORDER: unmarked, pile, pinI,
                           row 24 carried, row 24 (sample 0), row 24 position and
                           formsT 24 3 "objects". By Lean's kernel, on the thread's written lists of
                           segments and places. CONDITIONAL: h, for the thread's sake alone
  `k6_ridesPast_unmarked`, `k6_ridesPast_pinI`, `k6_ridesPast_row` (every segment and class; three
  are spent),
  `k6_ridesPast_pile`      a share of the debt each. CONDITIONAL: h · hK
  `k6_ridesPastS_head`     THE DEBT. CONDITIONAL: h · hK: no other premise

No pin of a segment rides past this border: the one that is open there is owed again by the row.

How. `K6Keeps` turns three fields of the head's own record and nothing else (`K6Keeps.shape`,
Johnson/Desc/K6/Honest/Law/ObjectsOn.lean): so the statement, the book, what was put out and the
mark are the same in front and behind, by unfolding; the pending rows too, since at the head's own
record they are read off what was put out (`S.rows`, Johnson/Desc/First/State.lean). unmarked reads
the mark alone.
For pinI, row and pile the thread's authors have general laws, each from facts on `keeps`
(`ridesPastAt_pinI_older`, Honest/Thread/PinForward.lean; `ridesPastAt_row_older`, RowForward.lean;
`ridesPastAt_pile_older`, PileForward.lean): these are called. formsT 24 3 "objects":
`k6_ridesPastAtS_objects_head` (Honest/K6/Law/ObjectsRidesHead.lean). Three facts on the state in
front are drawn from the thread's sentence: "the statement is in order" and "the pending rows name
mask entries of the index masks' message alone" from `foldFacts_thr`
(Honest/Thread/ReachFacts.lean), by lines that are typed after `head_tidy`
(Honest/Thread/PinForwardKinds.lean) and `head_pileMasks` (Honest/Thread/RowPileForwardKinds.lean),
their authors' own: those two files are not imported, since they stand over other sub-protocols'
files; "the index masks' message is there" is `head_index` (Honest/Thread/HeadFences.lean).

Limits. A sentence "for all": it says nothing where the thread stands at no run, and that it stands
at any is not shown here. `RidesPastS` is a definition of the honest side's frame, a premise's form
of its rules: none of the library's goals, and no verifier's accept. NOTHING HERE SAYS THAT AN
ITEM'S SENTENCE HOLDS AT ANY STATE: the sentence in front is the form's own premise. The files on
the thread that are imported are their authors' working forms: in no sealed library. The head can be
met: it has a member at one example (`AtFullSide.Top.headMember_zFull`,
AtFullSide/Top/HeadMemberAtFull.lean). THE FULL SIZE ALONE, and the format's second hash function alone.
Modules under lean/Johnson/Goal/ are among what this file imports: it imports none by name and calls
nothing that is declared there. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K6.Law.ObjectsRidesHead
import Johnson.Desc.ProofFile.Honest.Thread.PinForward
import Johnson.Desc.ProofFile.Honest.Thread.RowForward
import Johnson.Desc.ProofFile.Honest.Thread.PileForward
import Johnson.Desc.ProofFile.Honest.Thread.HeadFences
import Johnson.Desc.ProofFile.Honest.Thread.OpenFacts
import Johnson.Desc.ProofFile.Honest.Thread.FirstRows
import Johnson.Desc.K6.Honest.Law.KeepsAtHead
import Johnson.Desc.Means.TestsBack

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K6
open ProofFile.Honest.FirstThread (Script WtF lettersHead head_keeps foldFacts_thr head_index open_pinI
  ridesPastAt_pinI_older ridesPastAt_row_older ridesPastAt_pile_older)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Place Strs Chain)
open VerifiableInference.Desc.First (RowClass start)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.Kinds.Head.Honest (K6Keeps plK6 k6_at341)
open P5J (AtMgA TS CellsM)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-! ## 1 Which items ride past the border -/

set_option maxRecDepth 1000000 in
/-- **SEVEN ITEMS RIDE PAST BORDER 341.** By the kernel, on the thread's closed lists of segments
and places. CONDITIONAL: the hypothesis h, for the thread's sake alone. -/
theorem riders_341 :
    ∀ i ∈ (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.opened 341,
      i ∉ ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.row 341).shuts →
      i ∉ ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.row 341).owes →
      i ∈ ([.unmarked, .pile, .pinI, .row 24 .carried, .row 24 (.sample 0), .row 24 .position,
        .formsT 24 3 "objects"] : List VerifiableInference.Desc.First.Item) := by
  have e : ∀ i ∈ fwdOpen (start P5J.At.links) (FirstRows.rows P5J.At.links P5J.At.ps) 341,
      i ∉ (FirstRows.rows P5J.At.links P5J.At.ps 341).shuts →
      i ∉ (FirstRows.rows P5J.At.links P5J.At.ps 341).owes →
      i ∈ ([.unmarked, .pile, .pinI, .row 24 .carried, .row 24 (.sample 0), .row 24 .position,
        .formsT 24 3 "objects"] : List VerifiableInference.Desc.First.Item) := by
    decide +kernel
  exact e

/-! ## 2 A share each -/

variable (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
  (hK : ∀ s s', Kp plK6 s s' → K6Keeps s s')
include hK

/-- **THE MARK.** CONDITIONAL: h; hK. -/
theorem k6_ridesPast_unmarked :
    RidesPastAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 341
      VerifiableInference.Desc.First.Item.unmarked := by
  intro k s m E s' ps v _ hk hw
  obtain ⟨_, _, _, _, _, _, _, rfl⟩ :=
    (hK s s' ((head_keeps h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w k6_at341 s s').1 hk)).shape
  exact hw

/-- **THE PIN OF THE INDEX MASKS' MESSAGE.** CONDITIONAL: h; hK. -/
theorem k6_ridesPast_pinI :
    RidesPastAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 341
      VerifiableInference.Desc.First.Item.pinI :=
  ridesPastAtS_of _ Said (ridesPastAt_pinI_older h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w
    fun _ s _ _ s' _ hk o q hq => by
      obtain ⟨_, _, _, _, _, _, _, rfl⟩ :=
        (hK s s' ((head_keeps h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w k6_at341 s s').1 hk)).shape
      exact hq)

/-- **THE ROWS OF A CLASS**, at every segment and class. CONDITIONAL: h; hK. -/
theorem k6_ridesPast_row (m : Nat) (c : RowClass) :
    RidesPastAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 341
      (VerifiableInference.Desc.First.Item.row m c) :=
  ridesPastAtS_of _ Said (ridesPastAt_row_older h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w m c
    fun k s mm E s' hA hk => by
      obtain ⟨_, _, _, _, _, _, _, rfl⟩ :=
        (hK s s' ((head_keeps h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w k6_at341 s s').1 hk)).shape
      obtain ⟨Bs, base, O⟩ := h.laid.opened
      have hb : 341 ≤ cF.blocksInOrder.length := by
        rw [Meaning.K2.flat_358 h.scope O]
        omega
      have hA' := hA
      unfold Thr at hA'
      obtain ⟨-, -, hF, -, -, -, -⟩ := hA'
      exact ⟨(OnBytes.Means.tidy4B_iff.1
          ((foldFacts_thr h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).tidy 341
            (mm.st.input.x.pub, s) ⟨hb, k, mm, E, hA, rfl⟩
            (Option.isNone_iff_eq_none.1 hF.1))).inOrder,
        ⟨rfl, fun _ _ => rfl, fun _ G hG => ⟨G, hG, rfl⟩, fun _ _ => rfl, fun _ _ _ => rfl⟩,
        fun _ hq => hq⟩)

/-- **THE PENDING ROWS ON THE TABLE OF WEIGHTS.** CONDITIONAL: h; hK. -/
theorem k6_ridesPast_pile :
    RidesPastAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 341
      VerifiableInference.Desc.First.Item.pile :=
  ridesPastAtS_of _ Said (ridesPastAt_pile_older h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w
    fun k s mm E s' hA hk => by
      obtain ⟨o, _, _, _, ho, _, _, rfl⟩ :=
        (hK s s' ((head_keeps h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w k6_at341 s s').1 hk)).shape
      have er : s.rows = s.out.pending := by
        simp only [VerifiableInference.Desc.First.S.rows, ho]
      obtain ⟨Bs, base, O⟩ := h.laid.opened
      have hb : 341 ≤ cF.blocksInOrder.length := by
        rw [Meaning.K2.flat_358 h.scope O]
        omega
      have hA' := hA
      unfold Thr at hA'
      obtain ⟨-, -, hF, -, -, -, -⟩ := hA'
      exact ⟨er.symm,
        (foldFacts_thr h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).pileMasks 341
          (mm.st.input.x.pub, s) ⟨hb, k, mm, E, hA, rfl⟩ (Option.isNone_iff_eq_none.1 hF.1),
        head_index h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hA (open_pinI (by omega) (by omega)),
        OnBytes.Means.Extends.refl _, fun _ _ => ⟨rfl, fun _ _ => rfl⟩⟩)

/-! ## 3 The debt -/

/-- **`RidesPastS` AT BORDER 341, WHOLE.** CONDITIONAL: h; hK: no other premise. -/
theorem k6_ridesPastS_head :
    RidesPastS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 341 :=
  ridesPastS_shares _ Said fun i h1 h2 h3 => by
    have key : ∀ j ∈ ([.unmarked, .pile, .pinI, .row 24 .carried, .row 24 (.sample 0),
        .row 24 .position, .formsT 24 3 "objects"] : List VerifiableInference.Desc.First.Item),
        RidesPastAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 341
          j := by
      intro j hj
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact k6_ridesPast_unmarked h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said hK
      · exact k6_ridesPast_pile h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said hK
      · exact k6_ridesPast_pinI h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said hK
      · exact k6_ridesPast_row h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said hK 24 .carried
      · exact k6_ridesPast_row h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said hK 24 (.sample 0)
      · exact k6_ridesPast_row h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said hK 24 .position
      · exact k6_ridesPastAtS_objects_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said k6_at341
          hK
    exact key i (riders_341 h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w i h1 h2 h3)

end ProofFile.Honest.K6

#print axioms ProofFile.Honest.K6.riders_341
#print axioms ProofFile.Honest.K6.k6_ridesPast_unmarked
#print axioms ProofFile.Honest.K6.k6_ridesPast_pinI
#print axioms ProofFile.Honest.K6.k6_ridesPast_row
#print axioms ProofFile.Honest.K6.k6_ridesPast_pile
#print axioms ProofFile.Honest.K6.k6_ridesPastS_head
