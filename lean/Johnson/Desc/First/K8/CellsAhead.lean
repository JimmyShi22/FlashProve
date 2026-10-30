-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K8/CellsAhead.lean: THE SMALLNESS TEST AT THE TABLE OF JOINTS: THE ONE TABLE OF
CELLS OF ITS LAW: THE WITNESS'S CELLS OF THE OPEN SEGMENT'S ARRAYS, THOSE THAT ARE NOT YET SENT
AMONG THEM.

Behind the draw the array of digits is not yet sent: its sending is the segment's third. The table
of cells of the item "tie" (`cellsAt`, Johnson/Desc/Sound/CellsAt.lean) finds a cell through the
verifier's state and reads an array that is not yet sent as 0. The item "forms" of the run "small"
reads such an array AHEAD, off the witness at the seat that the plan gives its message (`dataQA`,
Johnson/Desc/Sound/FormsAhead.lean). The law of the draw has one table for what stands in front of
the draw and behind it. So that table is the one that reads ahead:
  `cellsAhead cs arr ms N m a w t r c`: where the state a.2 has an open segment's part p: the entry
    (t, r, c) of the forms' own world (`worldOwn p []`, Johnson/Desc/Sound/FormsQ.lean) over
    `dataQA`; 0 where there is no such part.
  `cellsAhead_sent`: **at an array whose message the state finds (`Named.msgNow L t = some o`) it is
    `cellsAt`**: so at all that the tie reads the two tables are one.
  `cellsAhead_putTl`, `cellsAhead_hear`: a yes of the draw's decision turns no cell of it.
A definition; statements and proofs.
Limits. Nothing on which seats the plan gives. Nothing on soundness.

-/
import Johnson.Desc.First.K8.LawCellsAt
import Johnson.Desc.First.K8.LawAtS
import Johnson.Desc.Sound.FormsAhead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8

open OnBytes OnBytes.Model VerifiableInference.Desc VerifiableInference.Desc.Sound
open OnBytes.Params (ReqArray)

variable {P Cells Tok : Type}

/-- **The law's table of cells.** -/
noncomputable def cellsAhead (cs : OnBytes.Codes) (arr : ℕ → ℕ → ℕ) (ms : List Mem) (N : Numbers)
    (m : ℕ) (a : P × S) (w : Wit Cells Tok MsgT) (t r c : ℕ) : Cb.Gl.E :=
  match K9.segAt? a.2 with
  | some p =>
    (worldOwn p [] (dataQA (N.sent m) (N.group m) p (seatTab cs arr ms w))).entry t r c
  | none => 0

/-- **At an array that is sent it is the tie's table.** -/
theorem cellsAhead_sent (cs : OnBytes.Codes) (arr : ℕ → ℕ → ℕ) (ms : List Mem) (N : Numbers)
    (m : ℕ) (z : P) (s : S) (w : Wit Cells Tok MsgT) {L : LinkCtx} {F : Fork} {tl : HTailF2}
    (hL : s.link? = some L) (hF : s.fork? = some F) (ht : s.tl? = some tl) {t o : ℕ}
    (ho : Named.msgNow L t = some o) (r c : ℕ) :
    cellsAhead cs arr ms N m (z, s) w t r c = cellsAt cs arr ms N m (z, s) w t r c := by
  unfold Named.msgNow at ho
  obtain ⟨wl, hw, hn⟩ := Option.bind_eq_some_iff.1 ho
  obtain ⟨x, a, hx, ha, e1, e2⟩ := reqArray_of_liesAt hw
  obtain ⟨q, hp, rfl⟩ : ∃ q, K9.segAt? s = some q ∧ q.L = L := by
    unfold K9.segAt?
    rw [hL, hF, ht]
    exact ⟨_, rfl, rfl⟩
  have hwi : q.L.check.frame.whereIs x.1 a.message = some o := by
    rw [← e1, ← e2, whereIs_namedNow]
    exact hn
  have hA : K9.aheadIn (N.sent m) (N.group m) q (x.1, x.2) = none := by
    unfold K9.aheadIn K9.aheadOf
    split
    · rw [ha]
      show (Option.filter _ (match q.L.check.frame.whereIs x.1 a.message with
        | some _ => none
        | none => _)) = none
      rw [hwi]
      rfl
    · rfl
  have hxx : ((s.link?.map fun (L : LinkCtx) => L.arrayOf).getD #[]).getD t default = x := by
    rw [hL]
    show q.L.arrayOf.getD t default = x
    rw [Array.getD_eq_getD_getElem?, hx]
    rfl
  rw [cellsAt_of_part cs arr ms N m (z, s) w t r c q hp]
  show (match K9.segAt? s with
    | some p =>
      (worldOwn p [] (dataQA (N.sent m) (N.group m) p (seatTab cs arr ms w))).entry t r c
    | none => 0) = (dataQ (N.group m) q (seatTab cs arr ms w)).cell
    (((s.link?.map fun (L : LinkCtx) => L.arrayOf).getD #[]).getD t default).1
    (((s.link?.map fun (L : LinkCtx) => L.arrayOf).getD #[]).getD t default).2 r c
  rw [hp, hxx]
  show (match q.L.arrayOf[t]? with
    | some b => (dataQA (N.sent m) (N.group m) q (seatTab cs arr ms w)).cell b.1 b.2 r c
    | none => 0) = _
  rw [hx]
  show (match K9.aheadIn (N.sent m) (N.group m) q (x.1, x.2) with
    | some h => cellA q.d.st.codes h (seatTab cs arr ms w) r c
    | none => (dataQ (N.group m) q (seatTab cs arr ms w)).cell x.1 x.2 r c) = _
  rw [hA]

/-- Another value of the smallness test's part turns no cell. -/
theorem cellsAhead_putTl (cs : OnBytes.Codes) (arr : ℕ → ℕ → ℕ) (ms : List Mem) (N : Numbers)
    (m : ℕ) (z : P) (s : S) (tl tl' : HTailF2) (ht : s.tl? = some tl) (w : Wit Cells Tok MsgT) :
    cellsAhead cs arr ms N m (z, s.putTl tl') w = cellsAhead cs arr ms N m (z, s) w := by
  funext t r c
  obtain ⟨e1, e2, _⟩ := putTl_rest s tl'
  unfold cellsAhead
  show (match K9.segAt? (s.putTl tl') with
    | some p => _
    | none => _) = (match K9.segAt? s with
    | some p => _
    | none => _)
  unfold K9.segAt?
  rw [putTl_link, putTl_fork, putTl_tl s tl tl' ht, ht]
  cases s.link? with
  | none => rfl
  | some L =>
    cases s.fork? with
    | none => rfl
    | some F =>
      show (match L.arrayOf[t]? with
        | some b => (dataQA (N.sent m) (N.group m) _ (seatTab cs arr ms w)).cell b.1 b.2 r c
        | none => 0) = (match L.arrayOf[t]? with
        | some b => (dataQA (N.sent m) (N.group m) _ (seatTab cs arr ms w)).cell b.1 b.2 r c
        | none => 0)
      cases L.arrayOf[t]? with
      | none => rfl
      | some b =>
        show (match K9.aheadIn (N.sent m) (N.group m) _ (b.1, b.2) with
          | some h => cellA (s.putTl tl').st.codes h (seatTab cs arr ms w) r c
          | none => (K9L.dataOf L.check.rows L.check.frame (s.putTl tl').st
              (tabQ (N.group m) (s.putTl tl').st (s.putTl tl').book
                (seatTab cs arr ms w))).cell b.1 b.2 r c) =
          (match K9.aheadIn (N.sent m) (N.group m) _ (b.1, b.2) with
          | some h => cellA s.st.codes h (seatTab cs arr ms w) r c
          | none => (K9L.dataOf L.check.rows L.check.frame s.st
              (tabQ (N.group m) s.st s.book (seatTab cs arr ms w))).cell b.1 b.2 r c)
        rw [e1, e2]
        rfl

/-- **Over a yes of the draw.** -/
theorem cellsAhead_hear {Cl : Type} (cs : OnBytes.Codes) (arr : ℕ → ℕ → ℕ) (ms : List Mem)
    (N : Numbers) (m : ℕ) (z : P) (p : Par) (s s' : S) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64)))
    (h : (approximateRangeProofDrawKind (Cl := Cl) atS p).decide s rs gs = .ok s') (w : Wit Cells Tok MsgT) :
    cellsAhead cs arr ms N m (z, s') w = cellsAhead cs arr ms N m (z, s) w := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hl⟩ := decide_ok atS p s s' rs gs h
  obtain ⟨tl, ht, rfl⟩ := atS_lay s s' _ _ hl
  exact cellsAhead_putTl cs arr ms N m z s tl _ ht w

end VerifiableInference.Desc.First.K8

#print axioms VerifiableInference.Desc.First.K8.cellsAhead_sent
#print axioms VerifiableInference.Desc.First.K8.cellsAhead_putTl
#print axioms VerifiableInference.Desc.First.K8.cellsAhead_hear
