-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K8/LawCellsAt.lean: THE SMALLNESS TEST AT THE TABLE OF JOINTS: WHICH MESSAGE THE
TABLE OF CELLS OF THE ITEM "tie" READS AT AN ARRAY THAT THE DRAWN MATRIX MULTIPLIES.

The item's table of cells is `cellsAt` (Johnson/Desc/Sound/CellsAt.lean): it finds an array's
message by the library's `reqArray` and `ReqFrame.whereIs`. The test `Named.namedB`
(Johnson/Desc/First/K8/Named.lean) finds it by `Order.liesAt` and `Order.namedNow`
(Johnson/Desc/First/K8/Order.lean). Here: the two ways are one.
  `whereIs_namedNow`: `f.whereIs w.born w.message = Order.namedNow f w`.
  `reqArray_of_liesAt`: where `Order.liesAt L t` finds a message, the link's own list names array t,
    `reqArray` finds its array in the layout, and the message is that array's.
  `cellsAt_at`: **at a state with an open link L whose list, layout and frame find the message
    number o for array t (`Named.msgNow L t = some o`): the cell (r, c) of array t is the sum, over
    the array's blocks, of the library's `cellOfBlock` at the main table of message o, read off the
    witness at o's seat by the state's own book (`tabQ`).**
Statements and proofs, by unfolding.
Limits. Nothing on which entries of that table a block reads. Nothing on soundness.

-/
import Johnson.Desc.First.K8.Named
import Johnson.Desc.Sound.CellsAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8

open OnBytes OnBytes.Model VerifiableInference.Desc VerifiableInference.Desc.Sound
open OnBytes.Params (ReqArray)
open VerifiableInference.Desc.K9L (cellOfBlock)

/-- The library's reading and the test's are one. -/
theorem whereIs_namedNow (f : ReqFrame) (w : Order.Lies) :
    f.whereIs w.born w.message = Order.namedNow f w := by
  unfold ReqFrame.whereIs Order.namedNow
  cases f.next <;> try rfl
  rw [if_neg (by decide)]
  split
  · rfl
  · cases (f.groups.getD f.link {}).born.idxOf? (w.born, w.message) <;> rfl

/-- What `liesAt` finds, in the library's words. -/
theorem reqArray_of_liesAt {L : LinkCtx} {t : ℕ} {w : Order.Lies} (h : Order.liesAt L t = some w) :
    ∃ (x : ℕ × String) (a : ReqArray), L.arrayOf[t]? = some x ∧
      OnBytes.reqArray L.check.rows.layout x.1 x.2 = some a ∧ w.born = x.1 ∧
      w.message = a.message := by
  unfold Order.liesAt at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
  obtain ⟨x, hx, a, ha, _, _, m, _, rfl⟩ := h
  refine ⟨x, a, hx, ?_, rfl, rfl⟩
  unfold OnBytes.reqArray
  cases hl : L.check.rows.layout.link[x.1]? with
  | none =>
    rw [List.getD_eq_getElem?_getD, hl] at ha
    simp at ha
  | some l =>
    rw [List.getD_eq_getElem?_getD, hl] at ha
    exact ha

/-- **The cell of an array whose message the test finds.** -/
theorem cellsAt_at {P Cells Tok : Type} (cs : OnBytes.Codes) (arr : ℕ → ℕ → ℕ) (ms : List Mem)
    (N : Numbers) (m : ℕ) (z : P) (s : S) (w : Wit Cells Tok MsgT) {L : LinkCtx} {F : Fork}
    {tl : HTailF2} (hL : s.link? = some L) (hF : s.fork? = some F) (ht : s.tl? = some tl)
    {t o : ℕ} (ho : Named.msgNow L t = some o) (r c : ℕ) :
    ∃ a : ReqArray, cellsAt cs arr ms N m (z, s) w t r c =
      (a.blocks.map fun b => cellOfBlock b (s.st.rowBits o .main) (s.st.placeBits o .main)
        (tabQ (N.group m) s.st s.book (seatTab cs arr ms w) o .main) r c).sum := by
  unfold Named.msgNow at ho
  obtain ⟨wl, hw, hn⟩ := Option.bind_eq_some_iff.1 ho
  obtain ⟨x, a, hx, ha, e1, e2⟩ := reqArray_of_liesAt hw
  obtain ⟨q, hp, eL, eS, eB⟩ : ∃ q, K9.segAt? s = some q ∧ q.L = L ∧ q.d.st = s.st ∧
      q.d.book = s.book := by
    unfold K9.segAt?
    rw [hL, hF, ht]
    exact ⟨_, rfl, rfl, rfl, rfl⟩
  have hxx : ((s.link?.map fun (L : LinkCtx) => L.arrayOf).getD #[]).getD t default = x := by
    rw [hL]
    show L.arrayOf.getD t default = x
    rw [Array.getD_eq_getD_getElem?, hx]
    rfl
  refine ⟨a, ?_⟩
  have hwi : L.check.frame.whereIs x.1 a.message = some o := by
    rw [← e1, ← e2, whereIs_namedNow]
    exact hn
  rw [cellsAt_of_part cs arr ms N m (z, s) w t r c q hp]
  show (dataQ (N.group m) q (seatTab cs arr ms w)).cell
    (((s.link?.map fun (L : LinkCtx) => L.arrayOf).getD #[]).getD t default).1
    (((s.link?.map fun (L : LinkCtx) => L.arrayOf).getD #[]).getD t default).2 r c = _
  rw [hxx]
  unfold dataQ
  rw [eL, eS, eB]
  show (match OnBytes.reqArray L.check.rows.layout x.1 x.2 with
    | none => (0 : Cb.Gl.E)
    | some a =>
      match L.check.frame.whereIs x.1 a.message with
      | none => (0 : Cb.Gl.E)
      | some o =>
        (a.blocks.map fun b => cellOfBlock b (s.st.rowBits o .main) (s.st.placeBits o .main)
          (tabQ (N.group m) s.st s.book (seatTab cs arr ms w) o .main) r c).sum) = _
  rw [ha]
  show (match L.check.frame.whereIs x.1 a.message with
    | none => (0 : Cb.Gl.E)
    | some o =>
      (a.blocks.map fun b => cellOfBlock b (s.st.rowBits o .main) (s.st.placeBits o .main)
        (tabQ (N.group m) s.st s.book (seatTab cs arr ms w) o .main) r c).sum) = _
  rw [hwi]

end VerifiableInference.Desc.First.K8

#print axioms VerifiableInference.Desc.First.K8.cellsAt_at
#print axioms VerifiableInference.Desc.First.K8.whereIs_namedNow
#print axioms VerifiableInference.Desc.First.K8.reqArray_of_liesAt
