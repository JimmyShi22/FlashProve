-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/RowPileForwardKinds.lean: the hypotheses of RowForward.lean and
PileForward.lean, for the sub-protocols of two kinds whose step changes the statement: a sending of
oracle messages (kind K1) and the closing of a segment (kind K10). The hypotheses are of two sorts.
Facts on the state before the step are shown here wherever the invariant holds. Relations between
the two states are taken from the kind's clause of `keeps` as far as that clause has them; for kind
K1 the rest are hypotheses of the lemmas of part 4. No definition.

  1  `k10Keeps_rows`, `k10Keeps_extends`, `k10Keeps_bookKept`   kind K10: its clause
     (Johnson/Desc/K10/Honest/Keeps.lean) gives all relations that the item `pile` needs
  2  `k1Rest_extends`, `bookKept_of_rels`   kind K1: the statement after the step extends the one
     before it; every message keeps its place and the tree there
  3  `head_book`, `head_hold`, `head_pileMasks`   wherever the invariant holds: the list of
     commitment trees has the plan's number of trees and a place for every message; every place
     names a tree that is there; every mask entry that a pending row names belongs to the message of
     the index masks
  4  `ridesPastAt_pile_k10`, `ridesPastAt_pile_k1`, `ridesPastAt_row_k1`   the hypothesis
     `RidesPastAt` (Honest/Thread/Shares.lean) for the two items at such a sub-protocol
  5  `ridesPastAt_pile_k10_at`, `ridesPastAt_pile_k1_at`, `ridesPastAt_row_k1_at`   the lemmas of
     part 4 with `hidx` and `hF` shown (HeadFences.lean, OpenFacts.lean) and the relations of kind
     K1 under their one name (`K1LaterRels`, K1LaterRels.lean). What is left is `hk`, bounds on the
     number `b`, and for `row m c` that the item is open at `b` in the library's table

What part 4 leaves as hypotheses.
  * `hk`: `keeps b` gives the kind's clause. For kind K1 it also has to give relations that the
    common part of K1's clauses (`K1Rest`) does not contain. For `pile` these are two: every tree
    that is there stays, and the pending rows stay. For `row m c` they are five: the older messages
    stay, every group keeps its open rows, there is no new group, every tree that is there stays,
    and the place of a new message names a new tree. The library shows each of them from an
    accepting step of a sending (Johnson/Desc/K1/Law/RowAtLater.lean, GroupAtLater.lean,
    EarlierTreesUnchanged.lean, BookAtRecord.lean, PileAtLater.lean).
  * `hidx`: the message of the index masks is there.
  * `hF`: a condition on the plan alone. Every place of a class of sample rows names a tree below
    the plan's number of trees before the sub-protocol.

Limits.
  * Parts 3 to 5: full size only, and only under the library's hypothesis `AtMgA` at the hash
    function `secondHashFunction` (FirstAt.lean says which that is).
  * This file shows `hk` for no number `b`.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.RowForward
import Johnson.Desc.ProofFile.Honest.Thread.PileForward
import Johnson.Desc.ProofFile.Honest.Thread.PinForwardKinds
import Johnson.Desc.ProofFile.Honest.Thread.FormXK
import Johnson.Desc.ProofFile.Honest.Thread.HeadFences
import Johnson.Desc.ProofFile.Honest.Thread.OpenFacts
import Johnson.Desc.ProofFile.Honest.Thread.K1LaterRels
import Johnson.Desc.First.Link.Law.RidersLight
import Johnson.Desc.Means.GrowsTie
import Johnson.Desc.Sound.BookTestsLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Strs Wit Place)
open VerifiableInference.Desc.First (S Item RowClass BookKept openSets start)
open VerifiableInference.Desc.K1 (OldMsgs TreesOlder)
open VerifiableInference.Desc.K13 (pileMasksC)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open Meaning.K2 (PlacesStay)
open P5J (AtMgA CellsM TS F0T)

/-! ## 1 Kind K10 -/

/-- K10's clause leaves the pending rows. -/
theorem k10Keeps_rows {t t' : S} (k : ProofFile.Honest.K10.YesFree.K10Keeps t t') : t'.rows = t.rows :=
  (congrArg S.rows k.1.2).trans (VerifiableInference.Desc.LinkJoin.rows_putRec t _)

/-- Under K10's clause the statement after the step extends the one before it. -/
theorem k10Keeps_extends {t t' : S} (k : ProofFile.Honest.K10.YesFree.K10Keeps t t') :
    OnBytes.Means.Extends t.st t'.st := by
  obtain ⟨hc, -, hs, -⟩ := ProofFile.Honest.K10.YesFree.keeps_st k.1.1
  refine ⟨hc, fun o x hx => ?_⟩
  have e := hs o
  have hx' : (VerifiableInference.Desc.K9.recOf t).st.oracles[o]? = some x := hx
  rw [hx'] at e
  obtain ⟨x', h1, h2⟩ := Option.map_eq_some_iff.1 e
  exact ⟨x', h1, h2⟩

/-- K10's clause leaves the list of commitment trees. -/
theorem k10Keeps_bookKept {t t' : S} (k : ProofFile.Honest.K10.YesFree.K10Keeps t t') :
    BookKept t t' := by
  have e : t'.book = t.book := (ProofFile.Honest.K10.YesFree.keeps_six k).1
  intro o _
  rw [e]
  exact ⟨rfl, fun _ _ => rfl⟩

/-! ## 2 Kind K1 -/

/-- Under the common part of K1's clauses the statement after the step extends the one before
it. -/
theorem k1Rest_extends {s s' : S} (k : ProofFile.Honest.K1.K1Rest s s') :
    OnBytes.Means.Extends s.st s'.st :=
  OnBytes.Means.extends_of_grows k.2.2.2.2.1.1.1.1

/-- Every message of the statement before the step keeps its place and the tree there. -/
theorem bookKept_of_rels {s s' : S} (hP : PlacesStay s.book s'.book)
    (hT : TreesOlder s.book s'.book) (hn : s.book.place.size = s.st.oracles.size)
    (hold : ∀ (o : Nat) (x : Nat × Nat), s.book.place[o]? = some x → x.1 < s.book.trees.size) :
    BookKept s s' :=
  fun o ho => ⟨hP o (by omega), fun q hq => hT q.1 (hold o q hq)⟩

/-! ## 3 Wherever the invariant holds -/

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- The list of commitment trees has the plan's number of trees and a place for every message. -/
theorem head_book {b : Nat} {k : Coins Bk} {s : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X}
    {E : Env} (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b k s m E) :
    s.book.trees.size = (P5J.At.N Zp cF).treesAt P5J.At.ps[b]? ∧
      s.book.place.size = s.st.oracles.size := by
  have hT' := hT
  unfold Thr at hT'
  obtain ⟨-, -, hF, -, -, -, -⟩ := hT'
  obtain ⟨-, -, -, c4, -⟩ := IM.xk_parts
    (xk_of_form (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) hF)
  unfold VerifiableInference.Desc.First.bookAt at c4
  simp only [Bool.and_eq_true, beq_iff_eq] at c4
  exact ⟨c4.1.1, c4.1.2⟩

/-- Every place names a tree that is there. -/
theorem head_hold {b : Nat} {k : Coins Bk} {s : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X}
    {E : Env} (hb : b ≤ cF.blocksInOrder.length)
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b k s m E) :
    ∀ (o : Nat) (q : Nat × Nat), s.book.place[o]? = some q → q.1 < s.book.trees.size := by
  have hT' := hT
  unfold Thr at hT'
  obtain ⟨-, -, hF, -, -, -, -⟩ := hT'
  have e : VerifiableInference.Desc.Sound.bookFitsB s.book = true :=
    (foldFacts_thr h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).bookFits b (m.st.input.x.pub, s)
      ⟨hb, k, m, E, hT, rfl⟩ (Option.isNone_iff_eq_none.1 hF.1)
  intro o q hq
  obtain ⟨t, ht, -⟩ := (VerifiableInference.Desc.Sound.bookFitsB_iff s.book).1 e o q hq
  obtain ⟨hlt, -⟩ := Array.getElem?_eq_some_iff.1 ht
  exact hlt

/-- Every mask entry that a pending row names belongs to the message of the index masks. -/
theorem head_pileMasks {b : Nat} {k : Coins Bk} {s : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X}
    {E : Env} (hb : b ≤ cF.blocksInOrder.length)
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b k s m E) :
    pileMasksC s = true := by
  have hT' := hT
  unfold Thr at hT'
  obtain ⟨-, -, hF, -, -, -, -⟩ := hT'
  exact (foldFacts_thr h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).pileMasks b
    (m.st.input.x.pub, s) ⟨hb, k, m, E, hT, rfl⟩ (Option.isNone_iff_eq_none.1 hF.1)

/-! ## 4 The two items at a sub-protocol of kind K10 or K1 -/

/-- The item `pile` passes over a sub-protocol whose `keeps` gives K10's clause. -/
theorem ridesPastAt_pile_k10 {b : Nat} (hb : b ≤ cF.blocksInOrder.length)
    (hk : ∀ s s', (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.keeps b s s' →
      ProofFile.Honest.K10.YesFree.K10Keeps s s')
    (hidx : ∀ k s mm E,
      Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b k s mm E →
      s.out.indexMasks < s.st.oracles.size) :
    RidesPastAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b Item.pile :=
  ridesPastAt_pile_older h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w
    fun k s mm E s' hA hK =>
      ⟨k10Keeps_rows (hk s s' hK),
        head_pileMasks h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hb hA, hidx k s mm E hA,
        k10Keeps_extends (hk s s' hK), k10Keeps_bookKept (hk s s' hK)⟩

/-- The item `pile` passes over a sub-protocol whose `keeps` gives the common part of K1's
clauses and two relations more. -/
theorem ridesPastAt_pile_k1 {b : Nat} (hb : b ≤ cF.blocksInOrder.length)
    (hk : ∀ s s', (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.keeps b s s' →
      ProofFile.Honest.K1.K1Rest s s' ∧ TreesOlder s.book s'.book ∧ s'.rows = s.rows)
    (hidx : ∀ k s mm E,
      Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b k s mm E →
      s.out.indexMasks < s.st.oracles.size) :
    RidesPastAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b Item.pile :=
  ridesPastAt_pile_older h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w
    fun k s mm E s' hA hK =>
      ⟨(hk s s' hK).2.2,
        head_pileMasks h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hb hA, hidx k s mm E hA,
        k1Rest_extends (hk s s' hK).1,
        bookKept_of_rels (hk s s' hK).1.2.2.2.2.2.2.2.2 (hk s s' hK).2.1
          (head_book h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hA).2
          (head_hold h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hb hA)⟩

/-- The item `row m c` passes over a sub-protocol whose `keeps` gives the common part of K1's
clauses and five relations more, under one condition on the plan. -/
theorem ridesPastAt_row_k1 {b : Nat} (hb : b ≤ cF.blocksInOrder.length) (m : Nat) (c : RowClass)
    (hk : ∀ s s', (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.keeps b s s' →
      ProofFile.Honest.K1.K1Rest s s' ∧ OldMsgs s.st s'.st ∧
        (∀ (j : Nat) (G : OnBytes.Group), s.st.groups[j]? = some G →
          ∃ G' : OnBytes.Group, s'.st.groups[j]? = some G' ∧ G'.rows = G.rows) ∧
        s'.st.groups.size = s.st.groups.size ∧ TreesOlder s.book s'.book ∧
        ∀ o, s.book.place.size ≤ o → ∀ q, s'.book.place[o]? = some q → s.book.trees.size ≤ q.1)
    (hF : ∀ t, c = .sample t → ∀ q ∈ (P5J.At.N Zp cF).sent m t,
      q.1 < (P5J.At.N Zp cF).treesAt P5J.At.ps[b]?) :
    RidesPastAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b
      (Item.row m c) := by
  refine ridesPastAt_row_older h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w m c
    fun k s mm E s' hA hK => ?_
  obtain ⟨k1, k2, k3, k4, k5, k6⟩ := hk s s' hK
  obtain ⟨b1, b2⟩ := head_book h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hA
  have hR := rowKept_of_rels k2 k3 k1.2.2.2.2.2.2.2.2 k5 b2
    (head_hold h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hb hA)
  refine ⟨(head_tidy h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hb hA).inOrder, hR,
    classRows_sup _ m c hR k4 fun t ht => ?_⟩
  exact noNew_of_trees _ m t b2 k6 fun q hq => by
    rw [b1]
    exact hF t ht q hq

/-! ## 5 With `hidx` and `hF` shown -/

/-- The item `pile` passes over a sub-protocol from number 3 on whose `keeps` gives K10's clause. -/
theorem ridesPastAt_pile_k10_at {b : Nat} (hb : b ≤ cF.blocksInOrder.length) (h3 : 3 ≤ b) (h358 : b ≤ 358)
    (hk : ∀ s s', (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.keeps b s s' →
      ProofFile.Honest.K10.YesFree.K10Keeps s s') :
    RidesPastAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b Item.pile :=
  ridesPastAt_pile_k10 h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hb hk fun _ _ _ _ hA =>
    head_index h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hA (open_pinI h3 h358)

/-- The item `pile` passes over a sub-protocol from number 3 on whose `keeps` gives the common part
of K1's clauses and `K1LaterRels`. -/
theorem ridesPastAt_pile_k1_at {b : Nat} (hb : b ≤ cF.blocksInOrder.length) (h3 : 3 ≤ b) (h358 : b ≤ 358)
    (hk : ∀ s s', (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.keeps b s s' →
      ProofFile.Honest.K1.K1Rest s s' ∧ K1LaterRels s s') :
    RidesPastAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b Item.pile :=
  ridesPastAt_pile_k1 h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hb
    (fun s s' hK => ⟨(hk s s' hK).1, (hk s s' hK).2.2.2.2.1, (hk s s' hK).2.2.2.2.2.2⟩)
    fun _ _ _ _ hA =>
      head_index h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hA (open_pinI h3 h358)

/-- The item `row m c` passes over a sub-protocol at which it is open and whose `keeps` gives the
common part of K1's clauses and `K1LaterRels`. -/
theorem ridesPastAt_row_k1_at {b : Nat} (hb : b ≤ cF.blocksInOrder.length) (hps : b ≤ P5J.At.ps.length)
    (m : Nat) (c : RowClass)
    (ho : Item.row m c ∈ ((openSets P5J.At.links P5J.At.ps (start P5J.At.links))[b]?).getD [])
    (hk : ∀ s s', (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.keeps b s s' →
      ProofFile.Honest.K1.K1Rest s s' ∧ K1LaterRels s s') :
    RidesPastAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b
      (Item.row m c) :=
  ridesPastAt_row_k1 h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hb m c
    (fun s s' hK => ⟨(hk s s' hK).1, (hk s s' hK).2.1, (hk s s' hK).2.2.1, (hk s s' hK).2.2.2.1,
      (hk s s' hK).2.2.2.2.1, (hk s s' hK).2.2.2.2.2.1⟩)
    fun _ ht => head_fence h hps (open_pin_of_row (ht ▸ ho))

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.k10Keeps_rows
#print axioms ProofFile.Honest.FirstThread.k10Keeps_extends
#print axioms ProofFile.Honest.FirstThread.k10Keeps_bookKept
#print axioms ProofFile.Honest.FirstThread.k1Rest_extends
#print axioms ProofFile.Honest.FirstThread.bookKept_of_rels
#print axioms ProofFile.Honest.FirstThread.head_book
#print axioms ProofFile.Honest.FirstThread.head_hold
#print axioms ProofFile.Honest.FirstThread.head_pileMasks
#print axioms ProofFile.Honest.FirstThread.ridesPastAt_pile_k10
#print axioms ProofFile.Honest.FirstThread.ridesPastAt_pile_k1
#print axioms ProofFile.Honest.FirstThread.ridesPastAt_row_k1
#print axioms ProofFile.Honest.FirstThread.ridesPastAt_pile_k10_at
#print axioms ProofFile.Honest.FirstThread.ridesPastAt_pile_k1_at
#print axioms ProofFile.Honest.FirstThread.ridesPastAt_row_k1_at
