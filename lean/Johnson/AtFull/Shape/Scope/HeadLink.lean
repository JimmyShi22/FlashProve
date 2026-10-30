-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Shape/Scope/HeadLink.lean: THE HEAD's LINK (members 337 to 352) AT TWO RECORDS THAT MEET
SameRead (Scope/Rel.lean): their first halves are one function. Statements and proofs.

  `k6GR_blind`, `three_blind`, `join_blind`   these steps read none of the six
                    numbers that `flatH` lays to 0 (MF, KF, epsF, clipC, theta, cap): by `rfl`
  `lookAt_head`, `placeAt_head`, `look_head`, `tests_head`   at link 24 a lookup's place and the
                    tests' place are one at the two records: the head's arm alone is read
  `tabOf_g_congr`, `rowsHead_g`   the batching's rows at the head have one run on shapes
  `‹place›_same`    the first half of each place of the row
  `HeadRow.at_first`   at a number below 16 the row answers with one of its sixteen places
  **`head_rel`**    the sixteen places go alike: Join's premise hH

Limits. Two premises: hN, that link 24 is the head's at X₀ (`hN_of_return`, Scope/AttNums.lean, gives
it at the stored files), and hR, the place of the reads, whose law is Scope/ReadsSorts.lean's. Laws
on terms; nothing is evaluated, nothing says that a step returns. Nothing on any property.
-/
import Johnson.AtFull.Shape.Scope.Join
import Johnson.AtFull.Shape.LettersAtX
import Johnson.AtFull.Shape.Scope.LettersSame

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Johnson.AtFull.Shape.Scope
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First.Shape
open VerifiableInference.Desc.First.Look (lookAt placeAt)

/-- The first halves are blind to the six numbers. -/
theorem k6GR_blind (h : Head.Shape) : k6GR h = k6GR (flatH h) := rfl

theorem three_blind (h : Head.Shape) (iU3 w : Nat) (name : String) :
    VerifiableInference.Desc.Kinds.Head.Shape.threeRunG h iU3
        (VerifiableInference.Desc.Kinds.Head.parOf h w) name =
      VerifiableInference.Desc.Kinds.Head.Shape.threeRunG (flatH h) iU3
        (VerifiableInference.Desc.Kinds.Head.parOf (flatH h) w) name := rfl

theorem join_blind (h : Head.Shape) (iU3 w : Nat) :
    VerifiableInference.Desc.Kinds.Head.Shape.joinRunG h iU3
        (VerifiableInference.Desc.Kinds.Head.parOf h w) =
      VerifiableInference.Desc.Kinds.Head.Shape.joinRunG (flatH h) iU3
        (VerifiableInference.Desc.Kinds.Head.parOf (flatH h) w) := rfl


/-- Two lists of rows with one key and one run on shapes at each place have one table of these. -/
theorem tabOf_g_congr {r r' : List ((Nat × String) × Row)}
    (h : List.Forall₂ (fun x y => x.1 = y.1 ∧ x.2.g = y.2.g) r r') (o : Nat × String) :
    (tabOf r o).g = (tabOf r' o).g := by
  induction h with
  | nil => rfl
  | @cons x y _ _ hxy _ ih =>
    obtain ⟨k, v⟩ := x
    obtain ⟨k', v'⟩ := y
    obtain ⟨e1, e2⟩ := hxy
    obtain rfl : k = k' := e1
    unfold tabOf at ih ⊢
    rw [List.lookup_cons, List.lookup_cons]
    cases o == k with
    | true => exact e2
    | false => exact ih

/-- At each number below 16 a row answers with one of its sixteen places. -/
theorem HeadRow.at_first {r r' : HeadRow Cell} (h0 : r.laid.1 = r'.laid.1)
    (h1 : r.reply.1 = r'.reply.1) (h2 : r.switch.1 = r'.switch.1)
    (h3 : r.lookCalls.1 = r'.lookCalls.1) (h4 : r.own.1 = r'.own.1) (h5 : r.reads.1 = r'.reads.1)
    (h6 : r.draw.1 = r'.draw.1) (h7 : r.digits.1 = r'.digits.1)
    (h8 : r.lookDigits.1 = r'.lookDigits.1) (h9 : r.merge.1 = r'.merge.1)
    (h10 : r.batch.1 = r'.batch.1) (h11 : r.behind.1 = r'.behind.1)
    (h12 : r.equation.1 = r'.equation.1) (h13 : r.close.1 = r'.close.1)
    (h14 : r.shut.1 = r'.shut.1) (h15 : r.cleared.1 = r'.cleared.1) (j : Nat) (hj : j < 16) :
    (r.at j).1 = (r'.at j).1 := by
  match j, hj with
  | 0, _ => exact h0
  | 1, _ => exact h1
  | 2, _ => exact h2
  | 3, _ => exact h3
  | 4, _ => exact h4
  | 5, _ => exact h5
  | 6, _ => exact h6
  | 7, _ => exact h7
  | 8, _ => exact h8
  | 9, _ => exact h9
  | 10, _ => exact h10
  | 11, _ => exact h11
  | 12, _ => exact h12
  | 13, _ => exact h13
  | 14, _ => exact h14
  | 15, _ => exact h15
  | _ + 16, h => exact absurd h (by omega)

section Cells
variable {X X₀ : Verify.Public} (Q : SameRead X X₀)
  (hN : (if X₀.p4 then 2 else 1) * X₀.NGr = 24)
include Q

theorem hS_V : X.hS.V = X₀.hS.V := by
  have e := congrArg Head.Shape.V Q.hS
  exact e
theorem hS_LIDB : X.hS.LIDB = X₀.hS.LIDB := by
  have e := congrArg Head.Shape.LIDB Q.hS
  exact e
theorem hS_lmbH : X.hS.lmbH = X₀.hS.lmbH := by
  have e := congrArg Head.Shape.lmbH Q.hS
  exact e
theorem work_same : VerifiableInference.Desc.Kinds.Head.Law.workAtW X =
    VerifiableInference.Desc.Kinds.Head.Law.workAtW X₀ := by
  show (Params.settingOf X.P.frame).workOf .field .request = _
  rw [Q.frame]

theorem step_same : (if X.p4 then 2 else 1) * X.NGr = (if X₀.p4 then 2 else 1) * X₀.NGr := by
  rw [Q.toSamePlans.p4, Q.toSamePlans.NGr]

include hN

/-- **The head's place of a lookup is one at the two records.** -/
theorem lookAt_head (d : Bool) : lookAt X 24 d = lookAt X₀ 24 d := by
  have h1 : (if X.p4 then 2 else 1) * X.NGr = 24 := (step_same Q).trans hN
  unfold lookAt
  simp only [h1, hN, beq_self_eq_true, if_true, Q.H, Q.HLy, Q.wsLay, hS_LIDB Q, hS_lmbH Q]

theorem placeAt_head (d : Bool) : placeAt X 24 d = placeAt X₀ 24 d := by
  unfold placeAt
  rw [lookAt_head Q hN, Q.frame]

theorem look_head (d : Bool) : (LW X).look 24 d = (LW X₀).look 24 d := by
  show lookOf X 24 d = lookOf X₀ 24 d
  have c : ¬ ((!d && 24 % 2 == 0 && decide (24 < 24)) = true) := by simp
  unfold lookOf
  rw [if_neg c, if_neg c, placeAt_head Q hN]

omit hN in
theorem claimShOf_same (n : Nat) :
    ProofFile.Honest.K3.Law.AtThr.claimShOf X n = ProofFile.Honest.K3.Law.AtThr.claimShOf X₀ n := by
  unfold ProofFile.Honest.K3.Law.AtThr.claimShOf
  rw [Q.wsLay, hS_V Q, Q.H]

theorem tests_head : VerifiableInference.Desc.K9.testsWhere X 24 0 =
    VerifiableInference.Desc.K9.testsWhere X₀ 24 0 := by
  have h1 : (if X.p4 then 2 else 1) * X.NGr = 24 := (step_same Q).trans hN
  unfold VerifiableInference.Desc.K9.testsWhere
  simp only [h1, hN, beq_self_eq_true, if_true, Q.H]

omit hN in
theorem reply_same : (TabL.headRow (LW X)).reply.1 = (TabL.headRow (LW X₀)).reply.1 := by
  show replyA (tailSh X.H.tl) = replyA (tailSh X₀.H.tl)
  rw [Q.H]

omit hN in
theorem switch_same : (TabL.headRow (LW X)).switch.1 = (TabL.headRow (LW X₀)).switch.1 := by
  show (TabL.switchHead (LW X)).1 = (TabL.switchHead (LW X₀)).1
  unfold TabL.switchHead
  rw [k2n_same Q, hpL_same Q]
  rfl

theorem lookCalls_same :
    (TabL.headRow (LW X)).lookCalls.1 = (TabL.headRow (LW X₀)).lookCalls.1 := by
  show (TabL.lookCalls (LW X) 24).1 = (TabL.lookCalls (LW X₀) 24).1
  unfold TabL.lookCalls
  rw [look_head Q hN]

omit hN in
theorem own_same : (TabL.headRow (LW X)).own.1 = (TabL.headRow (LW X₀)).own.1 := by
  show liftO (k6GR X.hS) = liftO (k6GR X₀.hS)
  rw [k6GR_blind X.hS, k6GR_blind X₀.hS, Q.hS]

theorem lookDigits_same :
    (TabL.headRow (LW X)).lookDigits.1 = (TabL.headRow (LW X₀)).lookDigits.1 := by
  show (TabL.lookHead (LW X)).1 = (TabL.lookHead (LW X₀)).1
  unfold TabL.lookHead
  rw [look_head Q hN]
  cases (LW X₀).look 24 true with
  | none => rfl
  | some s =>
    show liftQ (ProofFile.Honest.K3.Law.AtThr.headDigitsG s.1 s.2 X) =
      liftQ (ProofFile.Honest.K3.Law.AtThr.headDigitsG s.1 s.2 X₀)
    congr 1
    funext a
    unfold ProofFile.Honest.K3.Law.AtThr.headDigitsG ProofFile.Honest.K3.Law.AtThr.headDigitsU
    simp only [claimShOf_same Q]

omit hN in
theorem merge_same : (TabL.headRow (LW X)).merge.1 = (TabL.headRow (LW X₀)).merge.1 := by
  show liftO (mergeG (parAtC 76 (gOf X))) = liftO (mergeG (parAtC 76 (gOf X₀)))
  have e : parAtC 76 (gOf X) = parAtC 76 (gOf X₀) := by
    unfold parAtC
    simp only [gOf, built_same Q, Q.wsLay, Q.frame, Q.H]
  rw [e]

omit hN in
theorem draw_same : (TabL.headRow (LW X)).draw.1 = (TabL.headRow (LW X₀)).draw.1 := by
  show (TabL.draw (LW X) 24).1 = (TabL.draw (LW X₀) 24).1
  unfold TabL.draw
  rw [k8_same Q]

omit hN in
theorem digits_same : (TabL.headRow (LW X)).digits.1 = (TabL.headRow (LW X₀)).digits.1 := by
  show (TabL.digits (LW X) 24).1 = (TabL.digits (LW X₀) 24).1
  unfold TabL.digits
  rw [nums_same Q]
  rfl

omit hN in
theorem cleared_same : (TabL.headRow (LW X)).cleared.1 = (TabL.headRow (LW X₀)).cleared.1 := by
  show (TabL.cleared (LW X) 24).1 = (TabL.cleared (LW X₀) 24).1
  have hl : (LW X).links = (LW X₀).links := links_same Q
  unfold TabL.cleared
  rw [hl]
  cases (LW X₀).links[24]? with
  | none => rfl
  | some Y =>
    show liftQ (clearHeadGL (Johnson.Desc.First.Walk.Seat.pubOf Y) X.layers.wsLay _) =
      liftQ (clearHeadGL (Johnson.Desc.First.Walk.Seat.pubOf Y) X₀.layers.wsLay _)
    rw [Q.wsLay]
    rfl

theorem headBehind_same : (TabL.headRow (LW X)).behind.1 = (TabL.headRow (LW X₀)).behind.1 := by
  show (TabL.behind (LW X) 24).1 = (TabL.behind (LW X₀) 24).1
  have t : VerifiableInference.Desc.K9.testsWhere (LW X).XZ 24 0 =
      VerifiableInference.Desc.K9.testsWhere (LW X₀).XZ 24 0 := tests_head Q hN
  unfold TabL.behind
  rw [k8_same Q, t]
  cases (LW X₀).k8 24 with
  | none => rfl
  | some p8 =>
    cases VerifiableInference.Desc.K9.testsWhere (LW X₀).XZ 24 0 with
    | none => rfl
    | some w => rfl

omit hN in
theorem three_same (iU3 : Nat) (name : String) :
    VerifiableInference.Desc.Kinds.Head.Shape.threeRunG X.hS iU3
        (VerifiableInference.Desc.Kinds.Head.parOf X.hS
          (VerifiableInference.Desc.Kinds.Head.Law.workAtW X)) name =
      VerifiableInference.Desc.Kinds.Head.Shape.threeRunG X₀.hS iU3
        (VerifiableInference.Desc.Kinds.Head.parOf X₀.hS
          (VerifiableInference.Desc.Kinds.Head.Law.workAtW X₀)) name := by
  rw [work_same Q, three_blind X.hS iU3 _ name, three_blind X₀.hS iU3 _ name, Q.hS]

omit hN in
theorem join_same (iU3 : Nat) :
    VerifiableInference.Desc.Kinds.Head.Shape.joinRunG X.hS iU3
        (VerifiableInference.Desc.Kinds.Head.parOf X.hS
          (VerifiableInference.Desc.Kinds.Head.Law.workAtW X)) =
      VerifiableInference.Desc.Kinds.Head.Shape.joinRunG X₀.hS iU3
        (VerifiableInference.Desc.Kinds.Head.parOf X₀.hS
          (VerifiableInference.Desc.Kinds.Head.Law.workAtW X₀)) := by
  rw [work_same Q, join_blind X.hS iU3 _, join_blind X₀.hS iU3 _, Q.hS]

omit hN in
theorem rowsHead_g (iU3 lm : Nat) (o : Nat × String) :
    (tabOf (rowsHead X iU3 lm) o).g = (tabOf (rowsHead X₀ iU3 lm) o).g := by
  refine tabOf_g_congr ?_ o
  unfold rowsHead
  exact .cons ⟨rfl, rfl⟩ (.cons ⟨rfl, rfl⟩ (.cons ⟨rfl, three_same Q iU3 "norm"⟩
    (.cons ⟨rfl, join_same Q iU3⟩ (.cons ⟨rfl, three_same Q iU3 "policy"⟩
    (.cons ⟨rfl, rfl⟩ (.cons ⟨rfl, rfl⟩ (.cons ⟨rfl, rfl⟩ (.cons ⟨rfl, rfl⟩
    (.cons ⟨rfl, three_same Q iU3 "logits"⟩ (.cons ⟨rfl, rfl⟩ .nil))))))))))

theorem batch_same : (TabL.headRow (LW X)).batch.1 = (TabL.headRow (LW X₀)).batch.1 := by
  show (TabL.batch (LW X) 24).1 = (TabL.batch (LW X₀) 24).1
  have t : VerifiableInference.Desc.K9.testsWhere (LW X).XZ 24 0 =
      VerifiableInference.Desc.K9.testsWhere (LW X₀).XZ 24 0 := tests_head Q hN
  have q : placeAt (LW X).XG 24 false = placeAt (LW X₀).XG 24 false := placeAt_head Q hN false
  have u : (LW X).XG.H.tl.ix.U.getD 2 none = (LW X₀).XG.H.tl.ix.U.getD 2 none := by
    show X.H.tl.ix.U.getD 2 none = X₀.H.tl.ix.U.getD 2 none
    rw [Q.H]
  have k : (LW X).k9 24 = (LW X₀).k9 24 := rfl
  unfold TabL.batch
  rw [k, t]
  cases (LW X₀).k9 24 with
  | none => rfl
  | some p =>
    cases VerifiableInference.Desc.K9.testsWhere (LW X₀).XZ 24 0 with
    | none => rfl
    | some w =>
      simp only [beq_self_eq_true, if_true, u, q]
      cases (LW X₀).XG.H.tl.ix.U.getD 2 none with
      | none => rfl
      | some iU3 =>
        cases placeAt (LW X₀).XG 24 false with
        | none => rfl
        | some e =>
          show cellG p w.1 (rowsHead X iU3 e.lm) _ = cellG p w.1 (rowsHead X₀ iU3 e.lm) _
          unfold cellG
          simp only [rowsHead_g Q iU3 e.lm]

omit hN in
theorem close_same : (TabL.headRow (LW X)).close.1 = (TabL.headRow (LW X₀)).close.1 := by
  have e : (LW X).close = (LW X₀).close := rfl
  show (TabL.close (LW X) 24).1 = (TabL.close (LW X₀) 24).1
  unfold TabL.close
  rw [e]

/-- **THE HEAD's LINK AT THE TWO RECORDS: MEMBER BY MEMBER ONE FUNCTION.** hR: the reads' cell, whose
law is another file's. -/
theorem head_rel (hR : (TabL.headRow (LW X)).reads.1 = (TabL.headRow (LW X₀)).reads.1) (j : Nat)
    (hj : j < 16) :
    CellRel X X₀ (337 + j) ((TabL.headRow (LW X)).at j) ((TabL.headRow (LW X₀)).at j) :=
  cellRel_of_eq (oddAt_behind (by omega))
    (HeadRow.at_first (r := TabL.headRow (LW X)) (r' := TabL.headRow (LW X₀)) rfl (reply_same Q) (switch_same Q) (lookCalls_same Q hN) (own_same Q) hR
      (draw_same Q) (digits_same Q) (lookDigits_same Q hN) (merge_same Q) (batch_same Q hN)
      (headBehind_same Q hN) rfl (close_same Q) rfl (cleared_same Q) j hj)

end Cells

end Johnson.AtFull.Shape.Scope

#print axioms Johnson.AtFull.Shape.Scope.k6GR_blind
#print axioms Johnson.AtFull.Shape.Scope.three_blind
#print axioms Johnson.AtFull.Shape.Scope.join_blind
#print axioms Johnson.AtFull.Shape.Scope.head_rel
