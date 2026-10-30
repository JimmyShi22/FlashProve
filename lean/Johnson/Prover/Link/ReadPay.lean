-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/ReadPay.lean: THE FORM's HALF AT A SWITCH: WHO PAYS THE LETTER OF THE READING
(ReadFront, Johnson/Prover/Link/ReadFront.lean), from what rides (ReadSeat,
Johnson/Prover/Link/ReadSeat.lean) and numbers. What rides passes over the sending of a switch,
whatever the switch takes; the carried rows behind a fold have no kept row; a group of columns at
the list of the draws stands at the list; and ReadFront follows at what the step behind the sending
reads, with the rooms asked at the statement IN FRONT OF the switch.

Main names (namespace Johnson.Prover.Link).
  sharesOk_congr   the guard G9 reads a statement at the tree's parts alone.
  stA_old, stA_size, bookSentP_old   an old message, and an old tree WHOLE, behind a sending.
  ReadSeat.sent   what rides passes over the sending: for every record of what the switch takes.
  keptRows_foldOutput   no kept member: no kept row.
  colsStand_map, dealt_stand   the dealt columns: as many as the listed positions; they stand.
  readFront_of_seat   ReadFront, of what rides and numbers: a re-packing.
  readFront_sent   THE PAYER: at a step whose statement, book and old rows are the sending's and the
    fold's terms (three equations, which hold by unfolding at the switch's own input).

By: admitted_other, stSent_old (OnBytes/Slice/BlkStLaws.lean) · partsLaid_old, treesSent_old
(OnBytes/Slice/BlkSentSeat.lean) · bookSentP_keeps (Johnson/Desc/K12/Law/SwTies.lean) ·
foldOutput_keptRows (OnBytes/Slice/BlkFoldOut.lean) · listOfT_eq (OnBytes/Chain/Draws.lean).

Limits. ReadSeat, the rooms, the test on the rows' own numbers, the tree's length, and the key and
the width of the dealt columns are premises. That ReadSeat holds at a new tree, and rides over the
rest of a stage: not here. "mask" is the library's name: nothing is said of what a mask does.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.ReadSeat
import Johnson.Desc.K12.Law.SwTies
import OnBytes.Slice.BlkFoldOut

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Link
open OnBytes OnBytes.Slice
open VerifiableInference.Desc
open H2K.Sw (Taken bookSentP bookSentP_keeps)

/-! ## What shares a leaf is read at the tree's parts alone -/

/-- The guard G9 reads a statement at the tree's parts alone. -/
theorem sharesOk_congr (S S' : Statement) (tr : Tree)
    (h : ∀ o ∈ tr.parts.toList, S'.oracles[o]? = S.oracles[o]?) :
    sharesOk S' tr = sharesOk S tr := by
  unfold sharesOk
  rw [List.filterMap_congr fun o ho => by rw [h o ho]]

/-! ## Over the sending of a switch -/

/-- An old message behind the sending of a switch. -/
theorem stA_old (D : Taken) (T : SwitchTarget) (others : Array OracleNotice) (S : Statement)
    (o : Nat) (h : o < S.oracles.size) : (D.stA T others S).oracles[o]? = S.oracles[o]? := by
  unfold Taken.stA
  rw [admitted_other _ _ _ _ _ o (Nat.ne_of_gt h), stSent_old S _ o h]

theorem stA_size (D : Taken) (T : SwitchTarget) (others : Array OracleNotice) (S : Statement) :
    S.oracles.size ≤ (D.stA T others S).oracles.size := by
  unfold Taken.stA admitted
  show _ ≤ (Array.modify _ _ _).size
  rw [Array.size_modify]
  show _ ≤ (S.oracles ++ _).size
  rw [Array.size_append]
  exact Nat.le_add_right _ _

/-- An old tree behind a sending: WHOLE. -/
theorem bookSentP_old (ft roots : Nat) (S : Statement) (Bk : TreeBook)
    (sent : Array OracleNotice) (lay : TreeLay) (t : Nat) (h : t < Bk.trees.size) :
    (bookSentP ft roots S Bk sent lay).trees[t]? = Bk.trees[t]? := by
  show (partsLaid sent lay _ Bk.trees.size (treesSent _ _ _ Bk.trees))[t]? = _
  rw [partsLaid_old _ _ _ _ _ t h, treesSent_old _ _ _ _ t h]

/-- **R1. What rides passes over the sending of a switch, whatever the switch takes.** -/
theorem ReadSeat.sent {S : Statement} {Bk : TreeBook} {ms : List Nat} {id t : Nat} {tr : Tree}
    (H : ReadSeat S Bk ms id t tr) (ft roots : Nat) (T : SwitchTarget)
    (others : Array OracleNotice) (D : Taken) :
    ReadSeat (D.stA T others S) (bookSentP ft roots S Bk (sentOf T others) D.lay) ms id t tr where
  inBook := by
    have ht : t < Bk.trees.size := by
      rcases Nat.lt_or_ge t Bk.trees.size with h1 | h1
      · exact h1
      · have := H.inBook
        rw [Array.getElem?_eq_none h1] at this
        cases this
    rw [bookSentP_old _ _ _ _ _ _ t ht]
    exact H.inBook
  place := fun p h => (bookSentP_keeps _ _ _ _ _ _).place _ _ (H.place p h)
  parts := H.parts
  once := H.once
  shares := by
    rw [sharesOk_congr S _ tr fun o ho => stA_old D T others S o (H.there o (by
      rw [H.parts] at ho
      simpa using ho))]
    exact H.shares
  there := fun o ho => Nat.lt_of_lt_of_le (H.there o ho) (stA_size D T others S)

/-! ## The carried rows behind a fold -/

/-- **R2.** No kept member: no kept row. -/
theorem keptRows_foldOutput (S : Statement) (F : FoldShape) (row : GroupRow) (o : Nat) (eps : E)
    (gamma : List E) (claim : E) (hk : ∀ w, F.layout.kept.getD w false = false) :
    (foldOutput S F row o eps gamma claim).keptRows = 0 := by
  rw [foldOutput_keptRows]
  generalize List.range F.layout.members.size = l
  induction l with
  | nil => rfl
  | cons i l ih =>
    rw [List.foldl_cons, hk i]
    exact ih

/-! ## The dealt columns -/

/-- Columns that are laid along a list stand at it. -/
theorem colsStand_map (κ W : Nat) (col : Nat → List UInt64) (hw : ∀ x, (col x).length = W) :
    ∀ xs : List Nat, Own.colsStand κ W (xs.map fun x => (κ, x, col x)) xs = true
  | [] => rfl
  | x :: xs => by
    have ih := colsStand_map κ W col hw xs
    unfold Own.colsStand at ih ⊢
    rw [List.map_cons, List.zip_cons_cons, List.all_cons, ih, hw x]
    simp

/-- **R3. A group of columns at the list of the draws, under one key, of one width**: as many as the
listed positions, and they stand at the list. -/
theorem dealt_stand (κ W a : Nat) (poss : List Nat) (col : Nat → List UInt64)
    (hp : ∀ x ∈ poss, x < 2 ^ a) (hw : ∀ x, (col x).length = W) :
    ((Fmt.listOf (poss.map (· % 2 ^ a))).map fun x => (κ, x, col x)).length =
        (Positions.ofDraws a poss).all.size ∧
      Own.colsStand κ W ((Fmt.listOf (poss.map (· % 2 ^ a))).map fun x => (κ, x, col x))
        (Positions.ofDraws a poss).all.toList = true := by
  have e : poss.map (· % 2 ^ a) = poss := by
    rw [List.map_congr_left fun x hx => Nat.mod_eq_of_lt (hp x hx), List.map_id']
  have ea : (Positions.ofDraws a poss).all = (Fmt.listOf poss).toArray := by
    show (listOfT poss).toArray = _
    rw [listOfT_eq]
  rw [e, ea]
  exact ⟨by simp, colsStand_map κ W col hw _⟩

/-! ## ReadFront -/

/-- **R4. ReadFront, of what rides and numbers.** -/
theorem readFront_of_seat (i : Tw.L9.SwIn) (pos : Positions) (ms : List Nat) (id t : Nat)
    (tr : Tree) (H : ReadSeat i.st i.book ms id t tr) (hm : i.old.layout.members = ms.toArray)
    (hf : i.old.fresh = id) (masks : i.old.masks = 2) (keptRows : i.old.keptRows = 0)
    (noKept : ∀ w, i.old.layout.kept.getD w false = false)
    (shape : Own.shapeFits i.old = true) (log : tr.shape.logN = pos.logN)
    (dealt : i.opened.length = pos.all.size)
    (stand : Own.colsStand (tr.number - i.firstTree)
      (tr.shape.mainWidth + tr.shape.maskWidth) i.opened pos.all.toList = true)
    (roomZ : ∀ w x, w < i.old.layout.members.size →
      i.st.oracles[i.old.layout.members.getD w 0]? = some x → 0 < x.shape.maskRows →
      ∃ f, i.old.layout.maskFirst.getD w none = some f ∧
        f + x.shape.maskRows ≤ 2 ^ i.old.layout.h)
    (roomM : ∀ w x, w < i.old.layout.members.size →
      i.st.oracles[i.old.layout.members.getD w 0]? = some x → 0 < x.shape.mainRows →
      ∃ f, i.old.layout.mainFirst.getD w none = some f ∧
        f + x.shape.mainRows ≤ 2 ^ i.old.layout.k)
    (fresh : ∀ x, i.st.oracles[i.old.fresh]? = some x → x.shape.maskRows = 2 ^ i.old.layout.h) :
    ReadFront i pos t tr := by
  have hids : singleRowsOracles i.old = (ms ++ [id]).toArray := by
    unfold singleRowsOracles
    rw [masks, hm, hf]
    simp
  refine ⟨masks, keptRows, noKept, shape, fun p h => ?_, H.inBook, ?_, H.shares, ?_, log, dealt,
    stand, fun p h => ?_, roomZ, roomM, fresh⟩
  · have h' : p < (ms ++ [id]).length := by simpa [hids] using h
    have e : (singleRowsOracles i.old)[p] = (ms ++ [id])[p] := by simp [hids]
    rw [e]
    exact H.place p h'
  · rw [H.parts, hids]
    simp only [List.all_toArray, List.contains_toArray, List.all_eq_true]
    exact fun x hx => List.contains_iff_mem.2 hx
  · rw [H.once]
    simp
  · have h' : p < (ms ++ [id]).length := by simpa [hids] using h
    have e : (singleRowsOracles i.old)[p] = (ms ++ [id])[p] := by simp [hids]
    rw [e, Array.getElem?_eq_getElem (H.there _ (List.getElem_mem h'))]
    rfl

/-- **R5. ReadFront at what a switch's step behind its sending reads**: S, Bk: the statement and the
book IN FRONT OF THE SWITCH; the rooms and the fresh message's rows are asked there. For every D. -/
theorem readFront_sent (i : Tw.L9.SwIn) (pos : Positions) (S S₀ : Statement) (Bk : TreeBook)
    (ms : List Nat) (id t : Nat) (tr : Tree) (H : ReadSeat S Bk ms id t tr) (ft roots : Nat)
    (T : SwitchTarget) (others : Array OracleNotice) (D : Taken)
    (hst : i.st = D.stA T others S)
    (hbk : i.book = bookSentP ft roots S Bk (sentOf T others) D.lay)
    (F : FoldShape) (row₀ : GroupRow) (eps : E) (gamma : List E) (claim : E)
    (hold : i.old = foldOutput S₀ F row₀ id eps gamma claim)
    (hm : F.layout.members = ms.toArray) (noKept : ∀ w, F.layout.kept.getD w false = false)
    (shape : Own.shapeFits i.old = true) (log : tr.shape.logN = pos.logN)
    (dealt : i.opened.length = pos.all.size)
    (stand : Own.colsStand (tr.number - i.firstTree)
      (tr.shape.mainWidth + tr.shape.maskWidth) i.opened pos.all.toList = true)
    (roomZ : ∀ w x, w < ms.length → S.oracles[ms.getD w 0]? = some x → 0 < x.shape.maskRows →
      ∃ f, F.layout.maskFirst.getD w none = some f ∧ f + x.shape.maskRows ≤ 2 ^ F.layout.h)
    (roomM : ∀ w x, w < ms.length → S.oracles[ms.getD w 0]? = some x → 0 < x.shape.mainRows →
      ∃ f, F.layout.mainFirst.getD w none = some f ∧ f + x.shape.mainRows ≤ 2 ^ F.layout.k)
    (fresh : ∀ x, S.oracles[id]? = some x → x.shape.maskRows = 2 ^ F.layout.h) :
    ReadFront i pos t tr := by
  have hl : i.old.layout = F.layout := by rw [hold]; rfl
  have hmem : ∀ w, w < ms.length → i.old.layout.members.getD w 0 = ms.getD w 0 := by
    intro w _
    rw [hl, hm]
    simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]
  have hsz : i.old.layout.members.size = ms.length := by rw [hl, hm]; simp
  have hold' : ∀ o ∈ ms ++ [id], i.st.oracles[o]? = S.oracles[o]? := fun o ho => by
    rw [hst]
    exact stA_old D T others S o (H.there o ho)
  refine readFront_of_seat i pos ms id t tr (by rw [hst, hbk]; exact H.sent ft roots T others D)
    (by rw [hl]; exact hm) (by rw [hold]; rfl) (by rw [hold]; rfl)
    (by rw [hold]; exact keptRows_foldOutput _ _ _ _ _ _ _ noKept) (by rw [hl]; exact noKept) shape
    log dealt stand (fun w x hw hx h0 => ?_) (fun w x hw hx h0 => ?_) fun x hx => ?_
  · rw [hsz] at hw
    rw [hmem w hw, hold' _ (List.mem_append_left _ (by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hw]
      exact List.getElem_mem hw))] at hx
    rw [hl]
    exact roomZ w x hw hx h0
  · rw [hsz] at hw
    rw [hmem w hw, hold' _ (List.mem_append_left _ (by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hw]
      exact List.getElem_mem hw))] at hx
    rw [hl]
    exact roomM w x hw hx h0
  · have e : i.old.fresh = id := by rw [hold]; rfl
    rw [e, hold' id (List.mem_append_right _ (List.mem_singleton.2 rfl))] at hx
    rw [hl]
    exact fresh x hx

end Johnson.Prover.Link
