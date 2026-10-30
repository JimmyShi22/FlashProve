-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LPFE1R/RowsDueAt.lean: e₁'s SHEET, ROW 156, THE OTHER SIDE AND THE JOIN: THE NUMBER OF ROWS
OF K10's FIRST DECLARED ROUND IS WHAT THE TABLE's NUMBERS COUNT: the plain rows that are due, the
members, the generator rows that are due; and the closed test coveredB
(Johnson/Desc/First/Link/Law/CountsOfHeld.lean) holds: IN THE GOALS' SCOPE, WHERE THE VERIFIER's OWN
VALUE IS LAID, AT ALL 25 LINKS. Definitions, closed facts by Lean's kernel at written values,
theorems. A law file; no running text imports it. THE LIGHT FORM (a brute walk that made the table's
open sets anew at every place was beyond the kernel).
  `coversC`, `covers_bind`, `covers_listed`   what an item covers is read off its class: so over the
                    open items only the listed classes (listedOf, EqNumbersOf.lean) count.
  `kindsOf cl ρ`, `coveredOf cl ρ`, `kindsDue_of`, `coveredB_of`   the kinds that are due, and the
                    test, as functions of the listed classes and of the numbers' rowsAt at the one
                    segment.
  `clW l`, `rowsLit l`   the written classes (link 0: the equation alone) and the written (first
                    place, count) of each class.
  `ix_is_batch`       BY THE KERNEL: K10's number is the batching's and three.
  `lit_rows`          BY THE KERNEL: at the written shape, seats and 219 positions a switch,
                    rowsAtPlan gives rowsLit, at all 25 links.
  `due_lit`           BY THE KERNEL, AT ALL 25 LINKS: coveredOf says yes, and plain + members +
                    generators = rowsQW l. `due_lit_bent`: the control: with one position's rows
                    fewer no link behind the first passes.
  `rowsAt_laid`       in scope, laid: (At.N Zp cF).rowsAt l = rowsLit l (by
                    possAt_written).
  `covered_laid`      coveredB (At.N Zp cF) (P5J.oAt (ixK10 l)) l = true.
  `k10_rows_due`      Q.rows = plainDue (At.N Zp cF) O l + (membersOf lo).length + gensDue (At.N
                    Zp cF) O l, O := P5J.oAt (ixK10 l), lo := the l-th written list.

Limits. At OnBytes.secondHashFunction. The full size alone. That b.rounds = (kind Q).rounds is a premise
(LPFK10.k10_rounds_sit pays it). Nothing on the verifier's state. "The value is laid" is spent here
also for the entry tests madeRow (by P5J.pins_of_laid's first half) and cutRow (through
RowsQAt.lean), both of Johnson/Desc/Laid/ProofAsks.lean. Nothing on soundness or on hiding.

-/
import Johnson.LPFE1R.RowsQAt
import Johnson.Desc.First.Link.Law.CountsOfHeld
import Johnson.Desc.First.Link.Law.EqNumbersOf
import Johnson.LPFK9R.FactsAtConstant
import Johnson.P5J.K10Open
import Johnson.P5T.CoreAtMg
import Johnson.P5T.PlanSeatsTie
import Johnson.Goal.Numbers.RequestWritten
import Johnson.Desc.First.Close.Law.CubeOfShapes
import Johnson.G.LinkLit

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.LinkJoin
open OnBytes
open OnBytes.Maker (WholeD)
open Johnson.G (linksFullLit)
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.First (S Numbers Item RowClass rowsDue rowsAtPlan possAt)
open VerifiableInference.Desc.First.Close (Par kind membersOf)
open VerifiableInference.Desc.First.K2Caller (posW possAt_written)
open VerifiableInference.Desc.ReqLit (shapeFull)
open LPFK10 (ixK10)
open ProofFile (Cl)

/-! ## Only the listed classes count -/

/-- The kind of a class whose run of places holds i. ρ: (first place, count) of a class. -/
def coversC (ρ : RowClass → ℕ × ℕ) (i : ℕ) (c : RowClass) : Option RowKind :=
  if decide ((ρ c).1 ≤ i ∧ i < (ρ c).1 + (ρ c).2) then some c.kind else none

theorem covers_bind (N : Numbers) (m i : ℕ) (it : Item) :
    covers N m i it = (clsOf m it).bind (coversC (N.rowsAt m) i) := by
  cases it with
  | row m' c =>
    rw [clsOf_row]
    unfold covers coversC
    by_cases h : (m' == m && c.inList) = true
    · simp [h]
    · simp [h]
  | _ => rfl

theorem covers_listed (N : Numbers) (O : List Item) (m i : ℕ) :
    O.filterMap (covers N m i) = (listedOf O m).filterMap (coversC (N.rowsAt m) i) := by
  unfold listedOf
  rw [List.filterMap_filterMap]
  exact List.filterMap_congr fun it _ => covers_bind N m i it

/-- The kinds that are due, off the listed classes. -/
def kindsOf (cl : List RowClass) (ρ : RowClass → ℕ × ℕ) : List RowKind :=
  (List.range ((cl.map fun c => (ρ c).2).sum)).map fun i =>
    ((cl.filterMap (coversC ρ i)).head?).getD .sample

/-- The closed test, off the listed classes. -/
def coveredOf (cl : List RowClass) (ρ : RowClass → ℕ × ℕ) : Bool :=
  (List.range ((cl.map fun c => (ρ c).2).sum)).all fun i =>
    ((cl.filterMap (coversC ρ i)).head?).isSome

theorem kindsDue_of (N : Numbers) (O : List Item) (m : ℕ) :
    kindsDue N O m = kindsOf (listedOf O m) (N.rowsAt m) := by
  unfold kindsDue kindsOf
  rw [rowsDue_listed]
  exact List.map_congr_left fun i _ => by rw [covers_listed]

theorem coveredB_of (N : Numbers) (O : List Item) (m : ℕ) :
    coveredB N O m = coveredOf (listedOf O m) (N.rowsAt m) := by
  unfold coveredB coveredOf
  rw [rowsDue_listed]
  congr 1
  funext i
  rw [covers_listed]

/-! ## At the written values -/

/-- The listed classes at K10's border of link l. -/
def clW (l : ℕ) : List RowClass := if l = 0 then [.equation] else [.carried, .position, .equation]

/-- (first place, count) of each class at link l. -/
def rowsLit (l : ℕ) : RowClass → ℕ × ℕ :=
  let a := if l == 0 then 0 else if l % 2 == 1 then 3 else 2
  let b := if l == 0 then 0 else if l % 2 == 1 then 3285 else 1314
  fun
    | .carried => (0, a)
    | .position => (a, b)
    | .equation => (a + b, 1)
    | .sample _ => (0, 0)

set_option maxRecDepth 1000000 in
theorem ix_is_batch : ((List.range 25).all fun l =>
    ixK10 l == batchAt P5J.fullLinks P5J.At.ps l + 1 + 1 + 1) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem lit_rows : ((List.range 25).all fun l =>
    decide (rowsAtPlan shapeFull posW P5T.N0Full 25 l .carried = rowsLit l .carried) &&
      decide (rowsAtPlan shapeFull posW P5T.N0Full 25 l .position = rowsLit l .position) &&
      decide (rowsAtPlan shapeFull posW P5T.N0Full 25 l .equation = rowsLit l .equation)) =
    true := by decide +kernel

/-- The closed test at (first place, count)s ρ. -/
def dueOfB (ρ : ℕ → RowClass → ℕ × ℕ) (l : ℕ) : Bool :=
  coveredOf (clW l) (ρ l) &&
    decide (((kindsOf (clW l) (ρ l)).filter (· == .plain)).length +
      (membersOf (linksFullLit.getD l [])).length +
      ((kindsOf (clW l) (ρ l)).filter (· == .generator)).length = rowsQW.getD l 0)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- **At the written numbers, at all 25 links.** -/
theorem due_lit : (List.range 25).all (dueOfB rowsLit) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- The control: with one generator row fewer no link behind the first passes. -/
theorem due_lit_bent : (List.range 25).filter (dueOfB fun l c =>
    match c with
    | .position => ((rowsLit l c).1, (rowsLit l c).2 - 1)
    | _ => rowsLit l c) = [0] := by decide +kernel

/-! ## In scope, where the value is laid -/

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S Cl}

/-- rowsAtPlan reads the positions at the one segment alone. -/
theorem rowsAtPlan_congr (s : Params.ReqShape) {t t' : ℕ → ℕ} (N : Numbers) (n m : ℕ)
    (h : t m = t' m) : rowsAtPlan s t N n m = rowsAtPlan s t' N n m := by
  funext c
  cases c <;> simp [rowsAtPlan, h]

/-- The table's rowsAt is the written one. -/
theorem rowsAt_laid (hW : VerifierAndGoals.InScope Z = true)
    (L : P5J.LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF) {l : ℕ} (hl : l < 25) :
    (P5J.At.N Zp cF).rowsAt l = rowsLit l := by
  have hy := (P5J.pins_of_laid hW L).1
  have e1 : P5T.numbersOf (P5J.At.pseats Zp) = P5T.N0Full :=
    (P5T.seats_in_scope hW L.pub hy L.laidPOf).2.2
  have e2 : P5J.At.shape Zp = shapeFull :=
    (VerifiableInference.PlanWritten.Joined.first_written_in_scope hW L.pub hy).2.2.1.trans
      VerifiableInference.PlanWritten.request_shape_written
  have e3 : (P5J.At.N Zp cF).rowsAt l = rowsAtPlan shapeFull posW P5T.N0Full 25 l := by
    show rowsAtPlan (P5J.At.shape Zp) (possAt cF.blocksInOrder 25) (P5T.numbersOf (P5J.At.pseats Zp)) 25 l =
      _
    rw [e1, e2]
    exact rowsAtPlan_congr _ _ _ _ (possAt_written hW L l (by omega))
  have a := List.all_eq_true.1 lit_rows l (List.mem_range.2 hl)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at a
  rw [e3]
  funext c
  cases c with
  | carried => exact a.1.1
  | position => exact a.1.2
  | equation => exact a.2
  | sample t => rfl

/-- The listed classes at K10's border. -/
theorem listed_at_k10 {l : ℕ} (hl : l < 25) : listedOf (P5J.oAt (ixK10 l)) l = clW l := by
  have e : ixK10 l = batchAt P5J.fullLinks P5J.At.ps l + 1 + 1 + 1 :=
    eq_of_beq (List.all_eq_true.1 ix_is_batch l (List.mem_range.2 hl))
  unfold P5J.oAt clW
  rw [e]
  exact LPFK9.listed_full l hl

/-- **The closed test on the plan, at the table's own numbers.** -/
theorem covered_laid (hW : VerifierAndGoals.InScope Z = true)
    (L : P5J.LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF) {l : ℕ} (hl : l < 25) :
    coveredB (P5J.At.N Zp cF) (P5J.oAt (ixK10 l)) l = true := by
  have a := List.all_eq_true.1 due_lit l (List.mem_range.2 hl)
  unfold dueOfB at a
  rw [Bool.and_eq_true] at a
  rw [coveredB_of, listed_at_k10 hl, rowsAt_laid hW L hl]
  exact a.1

/-- **K10's first round's number of rows is what the table's numbers count.** -/
theorem k10_rows_due (hW : VerifierAndGoals.InScope Z = true)
    (L : P5J.LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF) {l : ℕ} (hl : l < 25)
    {b : Block S Cl} (hb : cF.blocksInOrder[ixK10 l]? = some b) {Q : Par}
    (hr : b.rounds = (kind (Cl := Unit) Q).rounds) :
    Q.rows = plainDue (P5J.At.N Zp cF) (P5J.oAt (ixK10 l)) l +
      (membersOf (linksFullLit.getD l [])).length +
      gensDue (P5J.At.N Zp cF) (P5J.oAt (ixK10 l)) l := by
  have a := List.all_eq_true.1 due_lit l (List.mem_range.2 hl)
  unfold dueOfB at a
  rw [Bool.and_eq_true] at a
  unfold plainDue gensDue
  rw [kindsDue_of, listed_at_k10 hl, rowsAt_laid hW L hl, rows_q_at hW L hl hb hr]
  exact (of_decide_eq_true a.2).symm

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.covers_listed
#print axioms VerifiableInference.Desc.LinkJoin.kindsDue_of
#print axioms VerifiableInference.Desc.LinkJoin.coveredB_of
#print axioms VerifiableInference.Desc.LinkJoin.ix_is_batch
#print axioms VerifiableInference.Desc.LinkJoin.lit_rows
#print axioms VerifiableInference.Desc.LinkJoin.due_lit
#print axioms VerifiableInference.Desc.LinkJoin.due_lit_bent
#print axioms VerifiableInference.Desc.LinkJoin.rowsAt_laid
#print axioms VerifiableInference.Desc.LinkJoin.listed_at_k10
#print axioms VerifiableInference.Desc.LinkJoin.covered_laid
#print axioms VerifiableInference.Desc.LinkJoin.k10_rows_due
