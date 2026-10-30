-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K8/LawBlockIn.lean: THE APPROXIMATE RANGE PROOF (KIND K8; IN THE FILES BESIDE
THIS ONE: THE SMALLNESS TEST) AT THE TABLE OF JOINTS: A CELL OF THE ITEM "tie"'S TABLE READS A
MESSAGE'S TABLE INSIDE THE LAYOUT'S BLOCKS ALONE; SO, WHERE THE BLOCKS LIE INSIDE THE MESSAGE, TWO
WITNESSES WITH THE SAME MESSAGES HAVE THE SAME CELL. ("Block" in this file: a rectangle of a layout,
`LaidBlock`; never a sub-protocol.)

Why. The law of the sub-protocol in which the verifier samples the matrix, at two tables
(`k08_rowT`, Johnson/Desc/First/K8/LawTable.lean), asks a table entE that is a function of the
members' typed messages and agrees with the witness's table at every early cell (a cell of an array
that the sampled matrix multiplies). The witness's table is `cellsAt`
(Johnson/Desc/Sound/CellsAt.lean). A typed message holds the witness's table inside the message's
ranges alone (rows below its main rows, places below its length: `InMsg`, `msgs_forth`,
Johnson/Desc/Sound/World.lean). So one must know that `cellsAt` reads nothing outside these ranges.
  `covers_of_inBlock`: an index of the table at which the library's `inBlock` is not 0 is covered by
    the block, in the library's own word (`laidCovers`, OnBytes/Iop/ReqRows.lean).
  `cellOfBlock_congr`, `cellOfBlock_covers`: `cellOfBlock` (Johnson/Desc/First/Batch/Law/AsRow.lean)
    is the same at two tables that agree where `inBlock` is not 0; where the block covers.
  `BlockInMsg cs s R P b`: the block passes the library's `laidBlockOk` at a table of 2 ^ R rows and
    2 ^ P places, its rows end at or below the shape's main rows, and its places end at or below the
    main code's length. `blockInMsg_of_test`: from `laidBlockOk` and the test `blockIn`
    (Johnson/Desc/First/TailClaims/LayAtTest.lean).
  `msgTab`: a member's typed message as a table with one index, as `tabQ` counts it.
  `tabQ_of_msgs`: inside the message's ranges the one accessor `tabQ` at the witness is `msgTab` at
    the witness's typed messages.
  `array_of_msgNow`, `cellsAt_named`: `cellsAt_at` (Johnson/Desc/First/K8/LawCellsAt.lean) with the
    array named in front of the witness. That theorem says "there is an array" behind the witness,
    so at two witnesses it gives two arrays. The proof is that theorem's second half, typed again.
  `cellsAt_of_msgs`: **the cell as a function of the typed messages, written out.**
  `CellsIn cs l seat' ms N m s t o`: WHAT IS ASKED AT ARRAY t, as one Prop.
  `cellsAt_congr_msgs`: **under `CellsIn`: the same typed messages, the same cell.**
Statements and proofs.
Limits. `CellsIn` is a premise: shown at no verifier's state and at no plan here. It asks nothing
where the book has no seat of the segment for message o, or where no member of ms sits at that seat:
there `cellsAt` reads the zero table at every witness, in silence, and the congruence holds of
zeros. The toy at the file's end shows that `BlockInMsg` can be met and can fail, at one block.
Nothing on mask rows. Nothing on which element of the array an index holds. Nothing on soundness.

-/
import Johnson.Desc.First.K8.LawCellsAt
import Johnson.Desc.Sound.PinMove
import Johnson.Desc.First.TailClaims.LayAtTest

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8

open OnBytes OnBytes.Model VerifiableInference.Desc VerifiableInference.Desc.Sound Johnson.Pack
open OnBytes.Params (LaidBlock ReqArray)
open VerifiableInference.Desc.K9L (cellOfBlock inBlock BlockFacts blockFacts)
open VerifiableInference.Desc.K9 (seatAt)
open VerifiableInference.Desc.First.TailClaims.Law (blockIn)

/-! ## 1 Numbers -/

/-- A number with the same quotient by 2 ^ a as an aligned f lies in the stretch of 2 ^ a from f. -/
theorem stretch_of_div {f x a : ℕ} (hal : f % 2 ^ a = 0) (h : x / 2 ^ a = f / 2 ^ a) :
    f ≤ x ∧ x < f + 2 ^ a := by
  have h1 := Nat.div_add_mod f (2 ^ a)
  have h2 := Nat.div_add_mod x (2 ^ a)
  have h3 := Nat.mod_lt x (Nat.two_pow_pos a)
  rw [h] at h2
  rw [hal] at h1
  omega

/-- The last of A * B numbers lies in the last stretch of B. -/
theorem pred_mul_div {A B : ℕ} (hA : 0 < A) (hB : 0 < B) : (A * B - 1) / B = A - 1 := by
  obtain ⟨A', rfl⟩ : ∃ A', A = A' + 1 := ⟨A - 1, by omega⟩
  have e : (A' + 1) * B = A' * B + B := by ring
  apply Nat.div_eq_of_lt_le
  · rw [e, Nat.add_sub_cancel]
    omega
  · rw [Nat.add_sub_cancel, e]
    omega

/-! ## 2 One block -/

section
variable {K : Type} [CommRing K]

/-- Where `inBlock` is not 0, both of its tests hold. -/
theorem inBlock_ne {b : LaidBlock} {R P J : ℕ} (h : inBlock (K := K) b R P J ≠ 0) :
    J / 2 ^ b.rowBits % 2 ^ (R - b.rowBits) =
        b.firstRow / 2 ^ b.rowBits % 2 ^ (R - b.rowBits) ∧
      J / 2 ^ (R + b.placeBits) % 2 ^ (P - b.placeBits) =
        b.firstPlace / 2 ^ b.placeBits % 2 ^ (P - b.placeBits) := by
  unfold inBlock at h
  constructor
  · by_contra hc
    exact h (by rw [if_neg hc, zero_mul])
  · by_contra hc
    exact h (by rw [if_neg hc, mul_zero])

/-- **An index of the table at which `inBlock` is not 0 is covered by the block.** -/
theorem covers_of_inBlock {b : LaidBlock} {R P J : ℕ} (F : BlockFacts b R P)
    (hJ : J < 2 ^ (R + P)) (h : inBlock (K := K) b R P J ≠ 0) : laidCovers b R J = true := by
  obtain ⟨h1, h2⟩ := inBlock_ne h
  have eR : 2 ^ R = 2 ^ b.rowBits * 2 ^ (R - b.rowBits) := by
    rw [← Nat.pow_add, Nat.add_sub_cancel' F.hR]
  have eP : 2 ^ P = 2 ^ b.placeBits * 2 ^ (P - b.placeBits) := by
    rw [← Nat.pow_add, Nat.add_sub_cancel' F.hP]
  have r1 : J % 2 ^ R / 2 ^ b.rowBits = b.firstRow / 2 ^ b.rowBits := by
    rw [eR, Nat.mod_mul_right_div_self, h1]
    apply Nat.mod_eq_of_lt
    apply Nat.div_lt_of_lt_mul
    rw [← eR]
    exact F.rowLt
  have hpl : J / 2 ^ R < 2 ^ P := by
    apply Nat.div_lt_of_lt_mul
    rw [← Nat.pow_add]
    exact hJ
  have p1 : J / 2 ^ R / 2 ^ b.placeBits = b.firstPlace / 2 ^ b.placeBits := by
    rw [Nat.pow_add, ← Nat.div_div_eq_div_mul,
      Nat.mod_eq_of_lt (Nat.div_lt_of_lt_mul (eP ▸ hpl)),
      Nat.mod_eq_of_lt (Nat.div_lt_of_lt_mul (eP ▸ F.placeLt))] at h2
    exact h2
  obtain ⟨a1, a2⟩ := stretch_of_div F.alRow r1
  obtain ⟨a3, a4⟩ := stretch_of_div F.alPlace p1
  unfold laidCovers
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨a1, a2⟩, a3⟩, a4⟩

/-- `cellOfBlock` reads a table where `inBlock` is not 0, and nowhere else. -/
theorem cellOfBlock_congr (b : LaidBlock) (R P : ℕ) (tab tab' : ℕ → K)
    (h : ∀ J, J < 2 ^ (R + P) → inBlock (K := K) b R P J ≠ 0 → tab J = tab' J) (i c : ℕ) :
    cellOfBlock b R P tab i c = cellOfBlock b R P tab' i c := by
  unfold cellOfBlock
  apply Finset.sum_congr rfl
  intro J hJ
  by_cases h0 : inBlock (K := K) b R P J = 0
  · rw [h0, zero_mul, zero_mul]
  · rw [h J (Finset.mem_range.1 hJ) h0]

/-- **Two tables that agree where the block covers give one cell.** -/
theorem cellOfBlock_covers {b : LaidBlock} {R P : ℕ} (F : BlockFacts b R P) (tab tab' : ℕ → K)
    (h : ∀ J, laidCovers b R J = true → tab J = tab' J) (i c : ℕ) :
    cellOfBlock b R P tab i c = cellOfBlock b R P tab' i c :=
  cellOfBlock_congr b R P tab tab' (fun J hJ h0 => h J (covers_of_inBlock F hJ h0)) i c

end

/-- **The block lies inside the table and inside the message**: of the shape s, in a table of 2 ^ R
rows and 2 ^ P places. -/
structure BlockInMsg (cs : OnBytes.Codes) (s : OnBytes.OracleShape) (R P : ℕ) (b : LaidBlock) :
    Prop where
  /-- the library's test on a block in a table -/
  ok : laidBlockOk b R P = true
  /-- its rows are main rows of the message -/
  rows : b.firstRow + 2 ^ b.rowBits ≤ s.mainRows
  /-- its places are places of the message -/
  places : b.firstPlace + 2 ^ b.placeBits ≤ (pMain cs s).ell

/-- From the library's test and the test `blockIn`. -/
theorem blockInMsg_of_test {cs : OnBytes.Codes} {s : OnBytes.OracleShape} {R P : ℕ} {b : LaidBlock}
    (h : laidBlockOk b R P = true) (hb : blockIn s (pMain cs s).ell b = true) :
    BlockInMsg cs s R P b := by
  unfold blockIn at hb
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
  refine ⟨h, ?_, hb.2⟩
  have e := hb.1
  rw [← (blockFacts b R P h).hs, Nat.pow_add,
    pred_mul_div (Nat.two_pow_pos _) (Nat.two_pow_pos _)] at e
  have := Nat.two_pow_pos b.rowBits
  omega

/-- What the block covers lies inside the message's ranges. -/
theorem inMsg_of_covers {cs : OnBytes.Codes} {s : OnBytes.OracleShape} {R P J : ℕ} {b : LaidBlock}
    (B : BlockInMsg cs s R P b) (h : laidCovers b R J = true) :
    InMsg cs s false (J % 2 ^ R) (J / 2 ^ R) := by
  unfold laidCovers at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  unfold InMsg
  rw [if_neg (by decide)]
  exact ⟨Nat.lt_of_lt_of_le h.1.1.2 B.rows, Nat.lt_of_lt_of_le h.2 B.places⟩

/-! ## 3 The one accessor, at the typed messages -/

section
variable {P Cells Tok : Type} (cs : OnBytes.Codes) (l : List (OnBytes.OracleShape × ℕ))
  (seat' : Fin l.length → ℕ × ℕ) (arr : ℕ → ℕ → ℕ) (ms : List Mem)

/-- Member i's typed message as a main table with one index: entry J is row J % 2 ^ R, place
J / 2 ^ R, as `tabQ` counts. Outside the message's ranges: 0 (`toMsgT`). -/
noncomputable def msgTab (i : Fin l.length) (M : (sigOf cs l).Msg) (R J : ℕ) : Cb.Gl.E :=
  toMsgT cs l i (M i) false (J % 2 ^ R) (J / 2 ^ R)

/-- **Inside the message's ranges the witness's table is the typed message's.** q: the seat of
message o by the book; y: the member of ms at which `seatTab` reads that seat; i: a member of l that
is alike. -/
theorem tabQ_of_msgs (own : List (ℕ × ℕ)) (st : OnBytes.Statement) (book : OnBytes.TreeBook)
    (w : Wit Cells Tok MsgT) {o : ℕ} {q : ℕ × ℕ} {y : Mem} {i : Fin l.length}
    (hq : seatAt own book o = some q)
    (hy : ms.find? (fun y => decide (seatOf y = q)) = some y) (hA : Alike y ⟨⟨l, seat'⟩, i⟩)
    {J : ℕ} (hin : InMsg cs (l.get i).1 false (J % 2 ^ st.rowBits o .main)
      (J / 2 ^ st.rowBits o .main)) :
    tabQ own st book (seatTab cs arr ms w) o .main J =
      msgTab cs l i (msgsOf cs l seat' arr w) (st.rowBits o .main) J := by
  have e1 : y.1.l.get y.2 = l.get i := hA.1
  have e2 : y.1.seat y.2 = seat' i := hA.2
  unfold tabQ msgTab
  rw [hq, ← msgs_forth cs l seat' arr w i false _ _ hin]
  show seatTab cs arr ms w q false _ _ = _
  unfold seatTab
  rw [hy]
  show memTab cs arr w y false _ _ = _
  unfold memTab numOf
  rw [e1, e2]

/-! ## 4 The table of cells -/

/-- What `Named.msgNow` finds, in the library's words. -/
theorem array_of_msgNow {L : LinkCtx} {t o : ℕ} (ho : Named.msgNow L t = some o) :
    ∃ (x : ℕ × String) (a : ReqArray), L.arrayOf[t]? = some x ∧
      OnBytes.reqArray L.check.rows.layout x.1 x.2 = some a ∧
      L.check.frame.whereIs x.1 a.message = some o := by
  unfold Named.msgNow at ho
  obtain ⟨wl, hw, hn⟩ := Option.bind_eq_some_iff.1 ho
  obtain ⟨x, a, hx, ha, e1, e2⟩ := reqArray_of_liesAt hw
  refine ⟨x, a, hx, ha, ?_⟩
  rw [← e1, ← e2, whereIs_namedNow]
  exact hn

variable (N : Numbers) (m : ℕ) (z : P) (s : S)

/-- `cellsAt_at` with the array named in front of the witness. -/
theorem cellsAt_named {L : LinkCtx} {F : Fork} {tl : HTailF2} (hL : s.link? = some L)
    (hF : s.fork? = some F) (ht : s.tl? = some tl) {t o : ℕ} {x : ℕ × String} {a : ReqArray}
    (hx : L.arrayOf[t]? = some x) (ha : OnBytes.reqArray L.check.rows.layout x.1 x.2 = some a)
    (hwi : L.check.frame.whereIs x.1 a.message = some o) (w : Wit Cells Tok MsgT) (r c : ℕ) :
    cellsAt cs arr ms N m (z, s) w t r c =
      (a.blocks.map fun b => cellOfBlock b (s.st.rowBits o .main) (s.st.placeBits o .main)
        (tabQ (N.group m) s.st s.book (seatTab cs arr ms w) o .main) r c).sum := by
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

/-- **The cell as a function of the typed messages.** -/
theorem cellsAt_of_msgs {L : LinkCtx} {F : Fork} {tl : HTailF2} (hL : s.link? = some L)
    (hF : s.fork? = some F) (ht : s.tl? = some tl) {t o : ℕ} {x : ℕ × String} {a : ReqArray}
    (hx : L.arrayOf[t]? = some x) (ha : OnBytes.reqArray L.check.rows.layout x.1 x.2 = some a)
    (hwi : L.check.frame.whereIs x.1 a.message = some o) {q : ℕ × ℕ} {y : Mem} {i : Fin l.length}
    (hq : seatAt (N.group m) s.book o = some q)
    (hy : ms.find? (fun y => decide (seatOf y = q)) = some y) (hA : Alike y ⟨⟨l, seat'⟩, i⟩)
    (hb : ∀ b ∈ a.blocks,
      BlockInMsg cs (l.get i).1 (s.st.rowBits o .main) (s.st.placeBits o .main) b)
    (w : Wit Cells Tok MsgT) (r c : ℕ) :
    cellsAt cs arr ms N m (z, s) w t r c =
      (a.blocks.map fun b => cellOfBlock b (s.st.rowBits o .main) (s.st.placeBits o .main)
        (msgTab cs l i (msgsOf cs l seat' arr w) (s.st.rowBits o .main)) r c).sum := by
  rw [cellsAt_named cs arr ms N m z s hL hF ht hx ha hwi w r c]
  apply congrArg List.sum
  apply List.map_congr_left
  intro b hbm
  exact cellOfBlock_covers (blockFacts _ _ _ (hb b hbm).ok) _ _
    (fun J hJ => tabQ_of_msgs cs l seat' arr ms (N.group m) s.st s.book w hq hy hA
      (inMsg_of_covers (hb b hbm) hJ)) r c

/-- **WHAT IS ASKED AT ARRAY t, whose message has the number o**: where the open link's list names
the array, the layout has it, the book has a seat of segment m for message o, and a member of ms
sits there: the member at which `seatTab` reads that seat is alike a member of l, and every block of
the array lies inside that member's message. -/
def CellsIn (t o : ℕ) : Prop :=
  ∀ (L : LinkCtx) (x : ℕ × String) (a : ReqArray) (q : ℕ × ℕ) (y : Mem), s.link? = some L →
    L.arrayOf[t]? = some x → OnBytes.reqArray L.check.rows.layout x.1 x.2 = some a →
    seatAt (N.group m) s.book o = some q →
    ms.find? (fun y => decide (seatOf y = q)) = some y →
    ∃ i : Fin l.length, Alike y ⟨⟨l, seat'⟩, i⟩ ∧ ∀ b ∈ a.blocks,
      BlockInMsg cs (l.get i).1 (s.st.rowBits o .main) (s.st.placeBits o .main) b

/-- **The same typed messages, the same cell.** -/
theorem cellsAt_congr_msgs {L : LinkCtx} {F : Fork} {tl : HTailF2} (hL : s.link? = some L)
    (hF : s.fork? = some F) (ht : s.tl? = some tl) {t o : ℕ} (ho : Named.msgNow L t = some o)
    (C : CellsIn cs l seat' ms N m s t o) (w w' : Wit Cells Tok MsgT)
    (hm : msgsOf cs l seat' arr w = msgsOf cs l seat' arr w') (r c : ℕ) :
    cellsAt cs arr ms N m (z, s) w t r c = cellsAt cs arr ms N m (z, s) w' t r c := by
  obtain ⟨x, a, hx, ha, hwi⟩ := array_of_msgNow ho
  cases hq : seatAt (N.group m) s.book o with
  | none =>
    have e : ∀ v : Wit Cells Tok MsgT,
        tabQ (N.group m) s.st s.book (seatTab cs arr ms v) o .main = fun _ => 0 := by
      intro v
      funext J
      unfold tabQ
      rw [hq]
    rw [cellsAt_named cs arr ms N m z s hL hF ht hx ha hwi w r c,
      cellsAt_named cs arr ms N m z s hL hF ht hx ha hwi w' r c, e w, e w']
  | some q =>
    cases hy : ms.find? (fun y => decide (seatOf y = q)) with
    | none =>
      have e : ∀ v : Wit Cells Tok MsgT,
          tabQ (N.group m) s.st s.book (seatTab cs arr ms v) o .main = fun _ => 0 := by
        intro v
        funext J
        unfold tabQ
        rw [hq]
        show seatTab cs arr ms v q false _ _ = 0
        unfold seatTab
        rw [hy]
      rw [cellsAt_named cs arr ms N m z s hL hF ht hx ha hwi w r c,
        cellsAt_named cs arr ms N m z s hL hF ht hx ha hwi w' r c, e w, e w']
    | some y =>
      obtain ⟨i, hA, hb⟩ := C L x a q y hL hx ha hq hy
      rw [cellsAt_of_msgs cs l seat' arr ms N m z s hL hF ht hx ha hwi hq hy hA hb w r c,
        cellsAt_of_msgs cs l seat' arr ms N m z s hL hF ht hx ha hwi hq hy hA hb w' r c, hm]

end

/-! ## 5 A toy: `BlockInMsg` can be met, and it can fail -/

section Toy
open VerifiableInference.Desc.First.TailClaims.Law (toyCs toyShape toyBlock)

/-- Met: a block of 4 rows and 8 places in a message of 4 main rows of 8 places, in a table of 2 ^ 2
rows and 2 ^ 3 places. -/
example : BlockInMsg toyCs toyShape 2 3 toyBlock := blockInMsg_of_test (by decide) (by decide)
/-- Not met: the same block, four rows lower: aligned, inside a table of 2 ^ 3 rows, but in rows
that the message does not have. -/
example : laidBlockOk { toyBlock with firstRow := 4 } 3 3 = true ∧
    ¬ BlockInMsg toyCs toyShape 3 3 { toyBlock with firstRow := 4 } :=
  ⟨by decide, fun B => absurd B.rows (by decide)⟩

end Toy

end VerifiableInference.Desc.First.K8

#print axioms VerifiableInference.Desc.First.K8.covers_of_inBlock
#print axioms VerifiableInference.Desc.First.K8.cellOfBlock_covers
#print axioms VerifiableInference.Desc.First.K8.blockInMsg_of_test
#print axioms VerifiableInference.Desc.First.K8.tabQ_of_msgs
#print axioms VerifiableInference.Desc.First.K8.cellsAt_named
#print axioms VerifiableInference.Desc.First.K8.cellsAt_of_msgs
#print axioms VerifiableInference.Desc.First.K8.cellsAt_congr_msgs
