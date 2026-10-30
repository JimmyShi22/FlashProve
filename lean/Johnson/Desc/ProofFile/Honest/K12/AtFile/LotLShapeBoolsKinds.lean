-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/LotLShapeBoolsKinds.lean

It states no goal. No property of the protocol is claimed.

IN FRONT OF THE FIRST CHAIN's CLOSING
PROXIMITY TEST GROUP 25 IS THERE, NO TEST OF IT HAS BEGUN, AND ITS OPEN ROWS ARE, BY KIND AND IN ORDER, ONE
PLAIN ROW AND THEN 657 OF THE GENERATOR's KIND: from the promise's own test on the open rows
(`rowsHeld`, Johnson/Desc/First/Borders.lean), which a stand of the thread gives. Nothing of what the
last code switch does is read.

  `closingRowsAt`           (first place, count) of each class of rows at segment 25
  `closingClasses_written`, `closingRowsAt_written`, `closingKinds_written`   BY LEAN's KERNEL: of segment 25
                            the classes "carried" and "position" are open at border 354 · the plan's
                            numbers at the written shape, positions and seats are `closingRowsAt`; a
                            control · at these the kinds that are due are that list, every place is held
                            by a class, 658 rows are due; a control
  `rowsAt_closing`          under the head the table's numbers of rows at segment 25 are `closingRowsAt`
  `closingRows_of_held`     where `rowsHeld` says yes: the three facts on the state's group 25
  `closingRows_on_shape`    the same read off the shape (`coreSh`): whatever the shape shows as group 25 has
                            these kinds and no test begun; and it shows one
  `closingRows_at_stand`    at a stand of the thread in front of member 354

By what. `kinds_of_held` (Johnson/Desc/First/Link/Law/CountsOfHeld.lean); `kindsDue_of`, `coveredB_of`,
`rowsAtPlan_congr` (Johnson/LPFE1R/RowsDueAt.lean), whose `rowsAt_laid` says the like at the segments 0 to
24; `rowsDue_listed` (Johnson/Desc/First/Link/Law/EqNumbersOf.lean); `rowOpen_354`, `O354`
(Johnson/Loose/H2K12/PublicAt354.lean).
NAMED OPENLY: `posW`, `possAt_written` have their home in Johnson/Top/H0/Tw/K2C/PossWritten.lean (a module
Johnson.Top.H0.*); it comes in through Johnson.LPFE1R.RowsDueAt, which is imported here.

Limits.
- `rowsHeld` is a clause of the promise: a stand gives it; a bare reach does not.
- That a stand is reached is not said.
- Kinds and a count: nothing on what a row claims.
- Full size, the format's second hash function alone.
- Nothing on completeness, soundness or hiding.

NOT IN FRONT OF A LAW OVER COINS: `closingRows_at_stand` bears this label; the rule is at its home,
the head of Johnson/Bind/ForProver/FiveFieldsAt.lean.
This file's own ground, in the rule's terms.
- h speaks of the public files: it names no coin.
- w, the run's input, is a letter under no premise in front. It holds the committer's coins (its
  field rc) and the hidden input (its fields w₀ and trace).
- There k, s, m and E are the theorem's own binders. The letters s, m and E (the verifier's state,
  the state of the prover's side, the available tables) stand under hT : `Thr … 354 k s m E`: a
  premise of the first kind: it names k; by its text, at fixed s, m and E it can hold at some values
  of the coins and fail at others.
- One clause of the invariant says that the input of m is w and meets Vd, a letter for a predicate
  on the input: what it reads of the input is not fixed here.
- The thread's other letters (H, Q, test, carryX, item, n₁, n₂, b₀, Vd, Rd, Kp) stand under no
  premise in front that names a coin; the invariant reads them.
- The other theorems of this file name no coin: they bear none.
- What lifts the bar: for s, m and E the made terms would be those of the honest run at the border,
  as terms of w, k and the challenges, and the lemma would show the premises at them at every value
  of the coins. None is known to this file: the bar is flat.
-/
import Johnson.LPFE1R.RowsDueAt
import Johnson.Loose.H2K12.PublicAt354
import Johnson.Desc.Ground.Shape.Core
import Johnson.Desc.ProofFile.Honest.Thread.FirstHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.LotL
open OnBytes (Group RowKind)
open VerifiableInference.Desc (Chain Place Strs)
open VerifiableInference.Desc.First (S RowClass rowsHeld rowsDue rowsAtPlan possAt)
open VerifiableInference.Desc.First.K2Caller (posW possAt_written)
open VerifiableInference.Desc.LinkJoin (kindsOf coveredOf listedOf kindsDue_of coveredB_of
  kinds_of_held rowsDue_listed rowsAtPlan_congr)
open VerifiableInference.Desc.ReqLit (shapeFull)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.Ground.Sh (GrpSh coreSh grpSh grp_get)
open ProofFile.Honest.FirstThread (lettersHead Script WtF)
open P5J (AtMg AtMgA CellsM TS)

/-- The kinds of the rows that lie open in group 25 in front of the closing test. -/
def closingKinds : List RowKind := .plain :: List.replicate 657 .generator

/-- (first place, count) of each class of rows at segment 25. -/
def closingRowsAt : RowClass → ℕ × ℕ
  | .carried => (0, 1)
  | .position => (1, 657)
  | .equation => (658, 0)
  | .sample _ => (0, 0)

set_option maxRecDepth 1000000 in
/-- By the kernel: of segment 25 two classes of rows in the list are open at border 354. -/
theorem closingClasses_written : listedOf H2K12.O354 25 = [.carried, .position] := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- By the kernel: the plan's numbers of rows at segment 25, at the written shape, positions and
seats. The last clause is a control: at 218 positions a switch the class "position" has fewer. -/
theorem closingRowsAt_written :
    rowsAtPlan shapeFull posW P5T.N0Full 25 25 .carried = closingRowsAt .carried ∧
      rowsAtPlan shapeFull posW P5T.N0Full 25 25 .position = closingRowsAt .position ∧
      rowsAtPlan shapeFull posW P5T.N0Full 25 25 .equation = closingRowsAt .equation ∧
      ¬ rowsAtPlan shapeFull (fun _ => 218) P5T.N0Full 25 25 .position =
        closingRowsAt .position := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- By the kernel: at these classes and numbers the kinds that are due are the list, every place is
held by a class, and 658 rows are due. The last clause is a control: without the class "position" the
kinds are another list. -/
theorem closingKinds_written :
    kindsOf [.carried, .position] closingRowsAt = closingKinds ∧
      coveredOf [.carried, .position] closingRowsAt = true ∧
      (([.carried, .position] : List RowClass).map fun c => (closingRowsAt c).2).sum = 658 ∧
      ¬ kindsOf [.carried] closingRowsAt = closingKinds := by
  decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **Under the head the table's numbers of rows at segment 25 are the written plan's.** -/
theorem rowsAt_closing (h : AtMg OnBytes.secondHashFunction Z D₀ r Zp Np cF) :
    (P5J.At.N Zp cF).rowsAt 25 = closingRowsAt := by
  have hy := (P5J.pins_of_laid h.scope h.laid).1
  have e1 : P5T.numbersOf (P5J.At.pseats Zp) = P5T.N0Full :=
    (P5T.seats_in_scope h.scope h.laid.pub hy h.laid.laidPOf).2.2
  have e2 : P5J.At.shape Zp = shapeFull :=
    (VerifiableInference.PlanWritten.Joined.first_written_in_scope h.scope h.laid.pub hy).2.2.1.trans
      VerifiableInference.PlanWritten.request_shape_written
  have e3 : (P5J.At.N Zp cF).rowsAt 25 = rowsAtPlan shapeFull posW P5T.N0Full 25 25 := by
    show rowsAtPlan (P5J.At.shape Zp) (possAt cF.blocksInOrder 25) (P5T.numbersOf (P5J.At.pseats Zp)) 25 25 =
      _
    rw [e1, e2]
    exact rowsAtPlan_congr _ _ _ _ (possAt_written h.scope h.laid 25 (Nat.le_refl _))
  rw [e3]
  funext c
  cases c with
  | carried => exact closingRowsAt_written.1
  | position => exact closingRowsAt_written.2.1
  | equation => exact closingRowsAt_written.2.2.1
  | sample t => rfl

/-- **Where the promise's test on the open rows says yes**: group 25 is there, no test of it has
begun, and its open rows have the written kinds, in order. -/
theorem closingRows_of_held (h : AtMg OnBytes.secondHashFunction Z D₀ r Zp Np cF) {s : S}
    (hheld : rowsHeld (P5J.At.N Zp cF) H2K12.O354 s = true) :
    ∃ G : Group, s.st.groups[25]? = some G ∧ G.inRun = false ∧
      G.rows.toList.map (·.kind) = closingKinds := by
  have hdue : rowsDue (P5J.At.N Zp cF) H2K12.O354 25 = 658 := by
    rw [rowsDue_listed, rowsAt_closing h, closingClasses_written]
    exact closingKinds_written.2.2.1
  have h1 := List.all_eq_true.1 (by unfold rowsHeld at hheld; exact hheld) 25 H2K12.rowOpen_354
  cases hG : s.st.groups[(P5J.At.N Zp cF).groupAt 25]? with
  | none =>
    simp only [hG, hdue] at h1
    exact absurd h1 (by decide)
  | some G =>
    simp only [hG, Bool.and_eq_true] at h1
    refine ⟨G, hG, ?_, ?_⟩
    · have t := h1.1.1
      cases hr : G.inRun with
      | false => rfl
      | true =>
        rw [hr] at t
        cases t
    · rw [kinds_of_held hheld H2K12.rowOpen_354 hG (by
        rw [coveredB_of, rowsAt_closing h, closingClasses_written]
        exact closingKinds_written.2.1), kindsDue_of, rowsAt_closing h, closingClasses_written]
      exact closingKinds_written.1

/-- **The same read off the shape.** -/
theorem closingRows_on_shape (h : AtMg OnBytes.secondHashFunction Z D₀ r Zp Np cF) {s : S}
    (hheld : rowsHeld (P5J.At.N Zp cF) H2K12.O354 s = true) :
    (∃ Gs : GrpSh, (coreSh ⟨s.st, s.book, s.roots⟩).st.groups[25]? = some Gs) ∧
      ∀ Gs : GrpSh, (coreSh ⟨s.st, s.book, s.roots⟩).st.groups[25]? = some Gs →
        Gs.kinds = closingKinds ∧ Gs.inRun = false := by
  obtain ⟨G, hG, hr, hk⟩ := closingRows_of_held h hheld
  have e : (coreSh ⟨s.st, s.book, s.roots⟩).st.groups[25]? = some (grpSh G) := by
    show (VerifiableInference.Desc.Ground.Sh.stSh s.st).groups[25]? = _
    rw [grp_get, hG]
    rfl
  refine ⟨⟨grpSh G, e⟩, fun Gs hGs => ?_⟩
  obtain rfl : grpSh G = Gs := Option.some.inj (e.symm.trans hGs)
  exact ⟨hk, hr⟩

/-- **At a stand of the thread in front of the closing test.** -/
theorem closingRows_at_stand (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
    (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
    (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
    (w : Local W₀ Rc ProofFile.Inst Tr) {k : Coins Bk} {s : S} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X}
    {E : Env}
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread 354 k s m E) :
    rowsHeld (P5J.At.N Zp cF) H2K12.O354 s = true ∧
      ∃ G : Group, s.st.groups[25]? = some G ∧ G.inRun = false ∧
        G.rows.toList.map (·.kind) = closingKinds := by
  have h' := hT
  unfold Thr at h'
  obtain ⟨-, -, hF, -, -, -, -⟩ := h'
  obtain ⟨hf, -, hc⟩ := hF
  have hfail : s.failed = none :=
    Option.isNone_iff_eq_none.1 (show s.failed.isNone = true from hf)
  rcases hc with hc | ⟨hb, -, -, -⟩
  · exact absurd hfail hc
  simp only [Bool.and_eq_true] at hb
  have hheld : rowsHeld (P5J.At.N Zp cF) H2K12.O354 s = true := hb.1.1.1.1.2
  exact ⟨hheld, closingRows_of_held h.toAtMg hheld⟩

end ProofFile.Honest.K12.LotL

#print axioms ProofFile.Honest.K12.LotL.closingKinds
#print axioms ProofFile.Honest.K12.LotL.closingRowsAt
#print axioms ProofFile.Honest.K12.LotL.closingClasses_written
#print axioms ProofFile.Honest.K12.LotL.closingRowsAt_written
#print axioms ProofFile.Honest.K12.LotL.closingKinds_written
#print axioms ProofFile.Honest.K12.LotL.rowsAt_closing
#print axioms ProofFile.Honest.K12.LotL.closingRows_of_held
#print axioms ProofFile.Honest.K12.LotL.closingRows_on_shape
#print axioms ProofFile.Honest.K12.LotL.closingRows_at_stand
