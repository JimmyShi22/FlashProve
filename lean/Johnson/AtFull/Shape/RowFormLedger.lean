-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/RowFormLedger.lean: THE VERIFIER's TEST OF ITS OWN LEDGER "THE WRITTEN-OUT
WEIGHTS OF A VIRTUAL ROW ARE ITS PRODUCT FORM's", OVER ALL THE LISTED ARRAYS (`termsV`,
Johnson/Desc/First/Batch/Shape/DoorParts.lean: one clause of `oneV`, the test on values at "the one
equation", ValsBool.lean) ACCEPTS AT THE LEDGER THAT THE STEP "THE WEIGHTS OF EVERY VIRTUAL ROW"
LEAVES (`coefAll`, OnBytes/Tie/Pv/Lookup/Ends/FoCoef.lean): FROM FOURTEEN PREMISES ON THE STEP's
LETTERS AND ONE ON THE LEDGER IN FRONT. General laws on plain data; no head; nothing is evaluated.

What it is for. RowFormWritten.lean shows the test at four makes of ONE row. Here the step's writes
are walked in their own order, and each is one of these makes once its letters are the right ones:
the array's number of rows for the powers' count, 2^(the point's size) for a piece's number of rows,
an aligned first row, and so on. These are gathered in one record, `CoefLetters`.

How. `EachRow Φ F`: every virtual row of the ledger meets Φ; one write keeps it where the change
keeps it (`eachRow_onRow`), and so does a row of writes (`eachRow_foldl`). The step is the library's
five stages: the first is walked by the library's law on a loop (`Fo.forIn_inv`), two are folds
(`Fo.coefPieces_eq`, `Fo.coefMats_eq`), two are written out. That no write turns an array's number
of rows or its kind is the library's (`Fo.Frame`; `kind_onRow`, OnBytes/Tie/Pv/Tail/EndCoef.lean).
Which write came last at a place is not argued: every write leaves a row at which the form holds,
whatever stood there. But the makes with a point or with ones do not clear the row's lists of
factors. So "no row has lists" is carried through the tables' and the pieces' writes, and behind the
two rows under powers "no row of another array has lists": hence the premise `apart`, that the
planes' array is not the digits'.

Main names.
* `EachRow`, `EachRow.mono`, `eachRow_onRow`, `eachRow_foldl`.
* `NoLists row`; `RowFormAt R row`: where the row has a product form, FormHolds in an array of R
  rows; `rowFormAt_tree`. `rowFormAt_one`, `rowFormAt_ones32`, `rowFormAt_table32`,
  `rowFormAt_powers`, `rowFormAt_piece`: the step's own five changes of a row. `pieceW_block`: a
  piece's weights are RowFormWritten.lean's blockTab. `piecePoint tl g a`. `clog2_32`.
* `CoefLetters tl g F`: tables (an array that gets one weight has one row) · pieceRows, pieceFits,
  pieceAligned, pieceFirst · reads, ties (the two vectors are the powers of the batching element) ·
  digits, planes, matRows (three numbers of rows) · point0, point1 (the two points have at least
  five coordinates) · apart · mats.
* `RowClean`, `RowCleanBut zz`: what is carried. `rowClean_of_fresh`: a ledger in which no row has a
  form or lists is clean. `forms_tables`: the first stage.
* **`forms_coefAll`**: at the letters, from a clean ledger: behind the step RowFormAt at every
  virtual row.
* `rowV_of`, `termsV_of`, **`termsV_coefAll`**: the verifier's own Bool, with the door shut as oneV
  asks it. `of_everyFrom`, `rowFormAt_of_rowV`: the test on one row, the other way.
* `powered_letters`: reads, ties and mats from the library's `Powered`
  (OnBytes/Tie/Pv/Tail/EndClosed.lean; `powersF_spec` there).
* With code: `coefTablesB`, `coefPiecesB`, `coefPowersB`, `coefPlanesB`, `coefMatsB`;
  `coefLettersB`, the five conjoined; **`coefLetters_of_B`**: its yes gives the fourteen letters.
  `coefPlanesB_can_fail`: it says no at a ledger without arrays. `rowsCleanB`,
  `rowClean_of_rowsCleanB`: the premise on the ledger in front; `rowsFreshB`,
  `rowClean_of_rowsFreshB`: a stronger test (no row has a form at all). `termsV_of_tests`: the
  clause from the yes of coefLettersB and rowsCleanB.

Limits. IMPLICATIONS. THE FOURTEEN LETTERS AND THE CLEAN LEDGER IN FRONT ARE PREMISES: nobody pays
them here, but for three of the letters from Powered; that a state reached in front of the step has
them is not shown; no example in Lean shows that they can hold together. THE JOIN AT THE OTHER END
IS OWED TOO: the tops speak of the ledger that the step leaves; oneV asks its clause at the ledger
of the state in front of "the one equation"; that this ledger has the arrays that the step left
(that nothing which runs between writes a virtual row's weights, form or lists, or an array's number
of rows) is not shown here. The tests with code are one way: a yes gives the premises.
`coefPlanesB_can_fail` is a control of one clause of one of the five tests, at the bluntest input:
the other thirteen clauses and the two tests on the rows have no failing case here. The letters are
asked whether or not the place that is written is there; tables is asked at every number n, and the
step reads n < 4. One of oneV's clauses: the test on the forms' sizes (termsB) and the other tests
on values are not treated. Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.RowFormWritten
import OnBytes.Tie.Pv.Lookup.Ends.FoCoef
import Johnson.Desc.First.Batch.Shape.DoorParts
import OnBytes.Tie.Pv.Tail.EndClosed
import OnBytes.Tie.Pv.Tail.EndCoef

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open Fo (rowAt HasRow Frame coefAll coefTables coefPieces coefPowers coefBZ coefMats allPieces
  pieceF pieceW)
open VerifiableInference.Desc.K9.Shape (rowV termsV)

/-! ## 1 A property of every virtual row, along writes -/

/-- Every virtual row of the ledger meets Φ. Φ is told the array's number, the array's number of
rows, and the row. -/
def EachRow (Φ : Nat → Nat → HRow → Prop) (F : Fork) : Prop :=
  ∀ t e, HasRow F t e → Φ t (F.trees.getD t {}).R (rowAt F t e)

/-- A weaker property follows. -/
theorem EachRow.mono {Φ Ψ : Nat → Nat → HRow → Prop} {F : Fork}
    (h : ∀ t R row, Φ t R row → Ψ t R row) (hF : EachRow Φ F) : EachRow Ψ F :=
  fun t e hr => h _ _ _ (hF t e hr)

/-- One write keeps it, where the change keeps it at that array. -/
theorem eachRow_onRow {Φ : Nat → Nat → HRow → Prop} {F : Fork} (t r : Nat) (f : HRow → HRow)
    (h : EachRow Φ F)
    (hf : ∀ row, Φ t (F.trees.getD t {}).R row → Φ t (F.trees.getD t {}).R (f row)) :
    EachRow Φ (onRow F t r f) := by
  intro t' e hr
  have fr := Fo.frame_onRow F t r f
  have hr' : HasRow F t' e :=
    ⟨Nat.lt_of_lt_of_eq hr.1 fr.1, Nat.lt_of_lt_of_eq hr.2 (fr.2 t').2⟩
  rw [(fr.2 t').1]
  by_cases hte : t = t' ∧ r = e
  · obtain ⟨rfl, rfl⟩ := hte
    rw [Fo.rowAt_onRow_eq F f hr']
    exact hf _ (h _ _ hr')
  · rw [Fo.rowAt_onRow_ne F f hte]
    exact h _ _ hr'

/-- A row of writes keeps it. F₀: the ledger of whose numbers of rows the law of one write
speaks. -/
theorem eachRow_foldl {α : Type} {Φ : Nat → Nat → HRow → Prop} (F₀ : Fork) (tr ro : α → Nat)
    (f : Fork → α → HRow → HRow) :
    ∀ (l : List α) (F : Fork), Frame F₀ F → EachRow Φ F →
      (∀ a ∈ l, ∀ G, Frame F₀ G → ∀ row, Φ (tr a) (F₀.trees.getD (tr a) {}).R row →
        Φ (tr a) (F₀.trees.getD (tr a) {}).R (f G a row)) →
      EachRow Φ (l.foldl (fun F a => onRow F (tr a) (ro a) (f F a)) F)
  | [], _, _, h, _ => h
  | a :: l, F, hS, h, hf => by
    show EachRow Φ (l.foldl _ (onRow F (tr a) (ro a) (f F a)))
    refine eachRow_foldl F₀ tr ro f l _ (hS.trans (Fo.frame_onRow _ _ _ _))
      (eachRow_onRow _ _ _ h fun row hrow => ?_) fun b hb => hf b (List.mem_cons_of_mem _ hb)
    rw [(hS.2 _).1] at hrow ⊢
    exact hf a List.mem_cons_self F hS row hrow

/-! ## 2 The makes, at a number of rows -/

/-- The row has no lists of factors. -/
def NoLists (row : HRow) : Prop := row.rowLo = #[] ∧ row.rowHi = #[]

/-- Where the row has a product form, its written-out weights are the form's, in an array of R
rows. -/
def RowFormAt (R : Nat) (row : HRow) : Prop := row.rowForm = true → FormHolds { R := R } row

/-- In an array X it is FormHolds X row: FormHolds reads of X its number of rows alone (by
unfolding). -/
theorem rowFormAt_tree (X : HTree) (row : HRow) (h : RowFormAt X.R row) (hf : row.rowForm = true) :
    FormHolds X row := h hf

/-- Five bits number 32 rows. -/
theorem clog2_32 : clog2 32 = 5 := rfl

/-- The tables' change of a row, in an array of one row. -/
theorem rowFormAt_one (row : HRow) (h : NoLists row) :
    RowFormAt 1 (formOnes { row with coef := #[oneE] }) :=
  fun _ => formHolds_ones { R := 1 } row h.1 h.2

/-- The change of the planes' third row, in an array of 32 rows. -/
theorem rowFormAt_ones32 (row : HRow) (h : NoLists row) :
    RowFormAt 32 (formOnes { row with coef := Array.replicate 32 oneE }) :=
  fun _ => formHolds_ones { R := 32 } row h.1 h.2

/-- The change of the planes' first two rows, in an array of 32 rows, at a point of five
coordinates. -/
theorem rowFormAt_table32 (row : HRow) (z : Array E) (h : NoLists row) (hz : z.size = 5) :
    RowFormAt 32 (formPoint { row with coef := eqTab z } z 0) :=
  fun _ => formHolds_table { R := 32 } row z h.1 h.2 (clog2_32.trans hz.symm)

/-- The change of a row under powers, where the vector is the powers and their count is the
array's number of rows. Nothing is asked of the row in front. -/
theorem rowFormAt_powers (row : HRow) (b : E) (R n : Nat) (v : Array E) (hv : v = powers b n)
    (hn : R = n) : RowFormAt R (formPowers { row with coef := v } b n) := by
  subst hv
  subst hn
  exact fun _ => formHolds_powers { R := R } row b

/-- A piece's written-out weights are the table on a block, where the piece has as many rows as the
table has entries. -/
theorem pieceW_block (c : CallZ) (zk : Array E) (p : Piece) (R : Nat)
    (h : p.Rp = 2 ^ (zk.extract (c.call.n - p.b) (c.call.n - p.b + p.a)).size) :
    pieceW c zk p R = blockTab (zk.extract (c.call.n - p.b) (c.call.n - p.b + p.a)) p.r0 R := by
  unfold pieceW blockTab
  rw [h]

/-- The point of a piece's equality polynomial. a: the call's number and the piece. -/
def piecePoint (tl : HTailF2) (g : Forest.Heard) (a : Nat × Piece) : Array E :=
  (g.zk.getD a.1 #[]).extract ((tl.zOf a.1).call.n - a.2.b) ((tl.zOf a.1).call.n - a.2.b + a.2.a)

/-- A piece's change of a row, at the piece's four letters. -/
theorem rowFormAt_piece (tl : HTailF2) (g : Forest.Heard) (G : Fork) (a : Nat × Piece) (R : Nat)
    (hR : (G.trees.getD a.2.tree {}).R = R) (h1 : a.2.Rp = 2 ^ (piecePoint tl g a).size)
    (h2 : (piecePoint tl g a).size ≤ clog2 R) (h3 : a.2.r0 % 2 ^ (piecePoint tl g a).size = 0)
    (h4 : a.2.r0 < 2 ^ clog2 R) (row : HRow) (h : NoLists row) :
    RowFormAt R (pieceF tl g G a row) := by
  intro _
  unfold pieceF
  rw [hR, pieceW_block _ _ _ _ h1]
  exact formHolds_block { R := R } row (piecePoint tl g a) a.2.r0 h.1 h.2 h2 h3 h4

/-! ## 3 The letters -/

/-- **The letters at which each write of the step is of one of the four makes.** F: the ledger in
front. -/
structure CoefLetters (tl : HTailF2) (g : Forest.Heard) (F : Fork) : Prop where
  tables : ∀ n t, tl.ix.U.getD n none = some t →
    ((F.trees.getD t {}).kind == HKind.table) = true → (F.trees.getD t {}).R = 1
  pieceRows : ∀ a ∈ allPieces tl, a.2.Rp = 2 ^ (piecePoint tl g a).size
  pieceFits : ∀ a ∈ allPieces tl, (piecePoint tl g a).size ≤ clog2 (F.trees.getD a.2.tree {}).R
  pieceAligned : ∀ a ∈ allPieces tl, a.2.r0 % 2 ^ (piecePoint tl g a).size = 0
  pieceFirst : ∀ a ∈ allPieces tl, a.2.r0 < 2 ^ clog2 (F.trees.getD a.2.tree {}).R
  reads : tl.vt = powers F.theta tl.tau
  ties : tl.vp = powers F.theta tl.tau
  digits : (F.trees.getD tl.ix.ZZ {}).R = tl.tau
  planes : (F.trees.getD tl.ix.BZ {}).R = 32
  point0 : 5 ≤ (g.zb 0).size
  point1 : 5 ≤ (g.zb 1).size
  apart : tl.ix.BZ ≠ tl.ix.ZZ
  mats : ∀ mu, mu < tl.NM →
    tl.rowX.getD mu #[] = powers (powE F.theta tl.stepF) (tl.shp.getD mu {}).mS
  matRows : ∀ mu, mu < tl.NM → (F.trees.getD (tl.gtTree.getD mu 0) {}).R = (tl.shp.getD mu {}).mS

/-- No lists of factors; and the form holds where there is one. -/
def RowClean (_ : Nat) (R : Nat) (row : HRow) : Prop := NoLists row ∧ RowFormAt R row

/-- The same, but that the rows of array zz may have lists. -/
def RowCleanBut (zz : Nat) (t : Nat) (R : Nat) (row : HRow) : Prop :=
  (t ≠ zz → NoLists row) ∧ RowFormAt R row

/-! ## 4 The five stages -/

/-- The first stage: the tables' rows. -/
theorem forms_tables (tl : HTailF2) (F : Fork)
    (hT : ∀ n t, tl.ix.U.getD n none = some t →
      ((F.trees.getD t {}).kind == HKind.table) = true → (F.trees.getD t {}).R = 1)
    (h0 : EachRow RowClean F) : EachRow RowClean (coefTables tl F) := by
  have key : (Frame F (coefTables tl F) ∧
      ∀ t, ((coefTables tl F).trees.getD t {}).kind = (F.trees.getD t {}).kind) ∧
      EachRow RowClean (coefTables tl F) := by
    unfold coefTables
    refine Fo.forIn_inv (fun s => (Frame F s ∧
      ∀ t, (s.trees.getD t {}).kind = (F.trees.getD t {}).kind) ∧ EachRow RowClean s) _
      (fun n s hs => ?_) _ _ ⟨⟨Fo.Frame.refl F, fun _ => rfl⟩, h0⟩
    dsimp only
    split
    · rename_i t hU
      split
      · rename_i hk
        refine ⟨_, rfl, ⟨hs.1.1.trans (Fo.frame_onRow _ _ _ _),
          fun t' => (OnBytes.Tie.Pv.Tail.Port.kind_onRow _ _ _ _ _).trans (hs.1.2 t')⟩,
          eachRow_onRow _ _ _ hs.2 fun row hrow => ?_⟩
        have hR : (s.trees.getD t {}).R = 1 := by
          rw [(hs.1.1.2 t).1]
          exact hT n t hU (by rw [← hs.1.2 t]; exact hk)
        rw [hR]
        exact ⟨⟨hrow.1.1, hrow.1.2⟩, rowFormAt_one row hrow.1⟩
      · exact ⟨_, rfl, hs⟩
    · exact ⟨_, rfl, hs⟩
  exact key.2

/-- **BEHIND THE STEP EVERY VIRTUAL ROW THAT HAS A PRODUCT FORM HAS THE FORM's WEIGHTS WRITTEN
OUT**: at the letters, from a ledger in which no row has lists of factors and every form that is
there holds. -/
theorem forms_coefAll (tl : HTailF2) (g : Forest.Heard) (F : Fork) (hL : CoefLetters tl g F)
    (h0 : EachRow RowClean F) : EachRow (fun _ R row => RowFormAt R row) (coefAll tl g F) := by
  -- the tables
  have s1 : Frame F (coefTables tl F) := Fo.frame_tables tl F
  have a1 : EachRow RowClean (coefTables tl F) := forms_tables tl F hL.tables h0
  -- the pieces
  have s2 : Frame F (coefPieces tl g (coefTables tl F)) := s1.trans (Fo.frame_pieces tl g _)
  have a2 : EachRow RowClean (coefPieces tl g (coefTables tl F)) := by
    rw [Fo.coefPieces_eq]
    exact eachRow_foldl F (fun a : Nat × Piece => a.2.tree) (fun a => a.2.row) (pieceF tl g)
      _ _ s1 a1 fun a ha G hG row hrow =>
        ⟨⟨hrow.1.1, hrow.1.2⟩, rowFormAt_piece tl g G a _ (hG.2 _).1 (hL.pieceRows a ha)
          (hL.pieceFits a ha) (hL.pieceAligned a ha) (hL.pieceFirst a ha) row hrow.1⟩
  -- the two rows under powers
  have s3 : Frame F (coefPowers tl F.theta (coefPieces tl g (coefTables tl F))) :=
    s2.trans (Fo.frame_powers tl _ _)
  have a3 : EachRow (RowCleanBut tl.ix.ZZ)
      (coefPowers tl F.theta (coefPieces tl g (coefTables tl F))) := by
    have b0 : EachRow (RowCleanBut tl.ix.ZZ) (coefPieces tl g (coefTables tl F)) :=
      a2.mono fun _ _ _ h => ⟨fun _ => h.1, h.2⟩
    unfold coefPowers
    refine eachRow_onRow _ _ _ (eachRow_onRow _ _ _ b0 fun row _ => ?_) fun row _ => ?_
    · rw [(s2.2 _).1]
      exact ⟨fun hne => absurd rfl hne, rowFormAt_powers row _ _ _ _ hL.reads hL.digits⟩
    · rw [((Fo.frame_onRow _ _ _ _).2 _).1, (s2.2 _).1]
      exact ⟨fun hne => absurd rfl hne, rowFormAt_powers row _ _ _ _ hL.ties hL.digits⟩
  -- the planes' three rows
  have s4 : Frame F (coefBZ tl g (coefPowers tl F.theta (coefPieces tl g (coefTables tl F)))) :=
    s3.trans (Fo.frame_bz tl g _)
  have z0 : ((g.zb 0).extract 0 5).size = 5 := by
    rw [Array.size_extract]
    have := hL.point0
    omega
  have z1 : ((g.zb 1).extract 0 5).size = 5 := by
    rw [Array.size_extract]
    have := hL.point1
    omega
  have a4 : EachRow (RowCleanBut tl.ix.ZZ)
      (coefBZ tl g (coefPowers tl F.theta (coefPieces tl g (coefTables tl F)))) := by
    unfold coefBZ
    refine eachRow_onRow _ _ _ (eachRow_onRow _ _ _ (eachRow_onRow _ _ _ a3 fun row hrow => ?_)
      fun row hrow => ?_) fun row hrow => ?_
    · rw [(s3.2 _).1, hL.planes]
      exact ⟨fun _ => ⟨(hrow.1 hL.apart).1, (hrow.1 hL.apart).2⟩,
        rowFormAt_table32 row _ (hrow.1 hL.apart) z0⟩
    · rw [((Fo.frame_onRow _ _ _ _).2 _).1, (s3.2 _).1, hL.planes]
      exact ⟨fun _ => ⟨(hrow.1 hL.apart).1, (hrow.1 hL.apart).2⟩,
        rowFormAt_table32 row _ (hrow.1 hL.apart) z1⟩
    · rw [((Fo.frame_onRow _ _ _ _).2 _).1, ((Fo.frame_onRow _ _ _ _).2 _).1, (s3.2 _).1,
        hL.planes]
      exact ⟨fun _ => ⟨(hrow.1 hL.apart).1, (hrow.1 hL.apart).2⟩,
        rowFormAt_ones32 row (hrow.1 hL.apart)⟩
  -- the matrices' rows
  unfold coefAll
  rw [Fo.coefMats_eq]
  exact eachRow_foldl F (fun mu => tl.gtTree.getD mu 0) (fun _ => 0)
    (fun _ mu row => formPowers { row with coef := tl.rowX.getD mu #[] } (powE F.theta tl.stepF)
      (tl.shp.getD mu {}).mS) _ _ s4 (a4.mono fun _ _ _ h => h.2)
    fun mu hmu _ _ row _ => rowFormAt_powers row _ _ _ _ (hL.mats mu (List.mem_range.1 hmu))
      (hL.matRows mu (List.mem_range.1 hmu))

/-! ## 5 The verifier's own test -/

/-- The test on one row. -/
theorem rowV_of (X : HTree) (row : HRow) (h : RowFormAt X.R row) : rowV X row = true := by
  unfold rowV
  cases hf : row.rowForm with
  | false => rfl
  | true => exact formHolds_test (rowFormAt_tree X row h hf)

/-- What a yes of the verifier's loop says. -/
theorem of_everyFrom (p : Nat → Bool) : ∀ (count i : Nat),
    VerifiableInference.Desc.K9.everyFrom p count i = true →
      ∀ j, i ≤ j → j < i + count → p j = true
  | 0, _, _, _, h1, h2 => by omega
  | count + 1, i, h, j, h1, h2 => by
    rw [VerifiableInference.Desc.K9.everyFrom, Bool.and_eq_true] at h
    rcases Nat.eq_or_lt_of_le h1 with rfl | h3
    · exact h.1
    · exact of_everyFrom p count (i + 1) h.2 j h3 (by omega)

/-- The test on one row, the other way. -/
theorem rowFormAt_of_rowV (X : HTree) (row : HRow) (h : rowV X row = true) :
    RowFormAt X.R row := by
  intro hf i hi
  have h' : VerifiableInference.Desc.K9.everyBelow X.R (fun i =>
      (productWritten (rowProduct X row)).getD i zeroE == row.coef.getD i zeroE) = true := by
    unfold rowV at h
    rw [hf] at h
    exact h
  exact beq_iff_eq.1 (of_everyFrom _ _ _ h' i (Nat.zero_le _) (by rw [Nat.zero_add]; exact hi))

/-- **The test over the listed arrays accepts at every ledger with these arrays.** -/
theorem termsV_of (L : LinkCtx) (F : Fork) (h : EachRow (fun _ R row => RowFormAt R row) F) :
    termsV L F = true := by
  unfold termsV
  rw [List.all_eq_true]
  intro ti _
  show ((F.trees.getD ti {}).rows.all (rowV (F.trees.getD ti {}))) = true
  refine Array.all_eq_true'.2 fun x hx => ?_
  obtain ⟨e, he, rfl⟩ := Array.mem_iff_getElem.1 hx
  by_cases ht : ti < F.trees.size
  · have e1 : rowAt F ti e = (F.trees.getD ti {}).rows[e] := by
      unfold rowAt
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem he]
      rfl
    rw [← e1]
    exact rowV_of _ _ (h ti e ⟨ht, he⟩)
  · exfalso
    have e0 : F.trees.getD ti {} = {} := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (Nat.le_of_not_lt ht)]
      rfl
    rw [e0] at he
    exact Nat.not_lt_zero _ he

/-- **THE CLAUSE OF "THE ONE EQUATION"'s TEST ON VALUES, BEHIND THE STEP, WITH THE DOOR SHUT.** -/
theorem termsV_coefAll (L : LinkCtx) (tl : HTailF2) (g : Forest.Heard) (F : Fork)
    (hL : CoefLetters tl g F) (h0 : EachRow RowClean F) :
    termsV L { coefAll tl g F with doorShutF := true } = true :=
  termsV_of L _ (forms_coefAll tl g F hL h0)

/-- A ledger in which no row has a form or lists of factors is clean. -/
theorem rowClean_of_fresh (F : Fork)
    (h : ∀ t e, HasRow F t e → (rowAt F t e).rowForm = false ∧ NoLists (rowAt F t e)) :
    EachRow RowClean F := fun t e hr =>
  ⟨(h t e hr).2, fun hf => absurd hf (by rw [(h t e hr).1]; exact Bool.false_ne_true)⟩

/-! ## 6 Who lays three of the letters -/

/-- **What the library says of the step that sets what follows from the batching element**
(Powered, OnBytes/Tie/Pv/Tail/EndClosed.lean; powersF_spec there) **gives the letters reads, ties
and mats.** At any theta: the letters want it at the ledger's own, F.theta. -/
theorem powered_letters {tl : HTailF2} {theta : E}
    (hP : OnBytes.Tie.Pv.Tail.Port.Powered tl theta) :
    tl.vt = powers theta tl.tau ∧ tl.vp = powers theta tl.tau ∧
      ∀ mu, tl.rowX.getD mu #[] = powers (powE theta tl.stepF) (tl.shp.getD mu {}).mS := by
  refine ⟨hP.vt, hP.vp, fun mu => ?_⟩
  rw [hP.rowX]
  by_cases hmu : mu < tl.shp.size
  · exact OnBytes.Tie.Pv.Tail.Port.getD_map _ _ _ _ _ hmu
  · simp [Array.getD, hmu]
    rfl

/-! ## 7 The premises with code -/

/-- The letter tables, with code. -/
def coefTablesB (tl : HTailF2) (F : Fork) : Bool :=
  (List.range tl.ix.U.size).all fun n =>
    match tl.ix.U.getD n none with
    | some t => !((F.trees.getD t {}).kind == HKind.table) || (F.trees.getD t {}).R == 1
    | none => true

/-- The pieces' four letters, with code. -/
def coefPiecesB (tl : HTailF2) (g : Forest.Heard) (F : Fork) : Bool :=
  (allPieces tl).all fun a =>
    a.2.Rp == 2 ^ (piecePoint tl g a).size &&
      decide ((piecePoint tl g a).size ≤ clog2 (F.trees.getD a.2.tree {}).R) &&
      a.2.r0 % 2 ^ (piecePoint tl g a).size == 0 &&
      decide (a.2.r0 < 2 ^ clog2 (F.trees.getD a.2.tree {}).R)

/-- reads, ties and digits, with code. -/
def coefPowersB (tl : HTailF2) (F : Fork) : Bool :=
  tl.vt == powers F.theta tl.tau && tl.vp == powers F.theta tl.tau &&
    (F.trees.getD tl.ix.ZZ {}).R == tl.tau

/-- planes, point0, point1 and apart, with code. -/
def coefPlanesB (tl : HTailF2) (g : Forest.Heard) (F : Fork) : Bool :=
  (F.trees.getD tl.ix.BZ {}).R == 32 && decide (5 ≤ (g.zb 0).size) &&
    decide (5 ≤ (g.zb 1).size) && tl.ix.BZ != tl.ix.ZZ

/-- mats and matRows, with code. -/
def coefMatsB (tl : HTailF2) (F : Fork) : Bool :=
  (List.range tl.NM).all fun mu =>
    tl.rowX.getD mu #[] == powers (powE F.theta tl.stepF) (tl.shp.getD mu {}).mS &&
      (F.trees.getD (tl.gtTree.getD mu 0) {}).R == (tl.shp.getD mu {}).mS

/-- **The fourteen letters as one test.** -/
def coefLettersB (tl : HTailF2) (g : Forest.Heard) (F : Fork) : Bool :=
  coefTablesB tl F && coefPiecesB tl g F && coefPowersB tl F && coefPlanesB tl g F && coefMatsB tl F

/-- **Its yes gives the letters.** -/
theorem coefLetters_of_B {tl : HTailF2} {g : Forest.Heard} {F : Fork}
    (h : coefLettersB tl g F = true) : CoefLetters tl g F := by
  unfold coefLettersB at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  unfold coefTablesB at h1
  rw [List.all_eq_true] at h1
  unfold coefPiecesB at h2
  simp only [List.all_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h2
  unfold coefPowersB at h3
  simp only [Bool.and_eq_true, beq_iff_eq] at h3
  unfold coefPlanesB at h4
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne] at h4
  unfold coefMatsB at h5
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq] at h5
  refine
    { tables := fun n t hU hk => ?_
      pieceRows := fun a ha => (h2 a ha).1.1.1
      pieceFits := fun a ha => (h2 a ha).1.1.2
      pieceAligned := fun a ha => (h2 a ha).1.2
      pieceFirst := fun a ha => (h2 a ha).2
      reads := h3.1.1, ties := h3.1.2, digits := h3.2
      planes := h4.1.1.1, point0 := h4.1.1.2, point1 := h4.1.2, apart := h4.2
      mats := fun mu hmu => (h5 mu hmu).1, matRows := fun mu hmu => (h5 mu hmu).2 }
  have hn : n < tl.ix.U.size := by
    by_contra hc
    have e0 : tl.ix.U.getD n none = none := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (Nat.le_of_not_lt hc)]
      rfl
    rw [e0] at hU
    cases hU
  have h6 := h1 n (List.mem_range.2 hn)
  rw [hU] at h6
  simp only [hk, Bool.not_true, Bool.false_or, beq_iff_eq] at h6
  exact h6

/-- The test can say no: at a ledger without arrays the planes' array has not 32 rows. -/
theorem coefPlanesB_can_fail (tl : HTailF2) (g : Forest.Heard) : coefPlanesB tl g {} = false := by
  simp [coefPlanesB, Array.getD]

/-- No virtual row has a product form or lists of factors, with code. -/
def rowsFreshB (F : Fork) : Bool :=
  F.trees.all fun X => X.rows.all fun row =>
    !row.rowForm && row.rowLo.isEmpty && row.rowHi.isEmpty

/-- Its yes gives a clean ledger. -/
theorem rowClean_of_rowsFreshB {F : Fork} (h : rowsFreshB F = true) : EachRow RowClean F := by
  refine rowClean_of_fresh F fun t e hr => ?_
  unfold rowsFreshB at h
  obtain ⟨ht, he⟩ := hr
  have e1 : F.trees.getD t {} = F.trees[t]'ht := by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem ht]
    rfl
  have e2 : rowAt F t e = (F.trees.getD t {}).rows[e]'he := by
    unfold rowAt
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem he]
    rfl
  have hX := Array.all_eq_true'.1 h (F.trees.getD t {}) (by rw [e1]; exact Array.getElem_mem _)
  have hrow := Array.all_eq_true'.1 hX (rowAt F t e) (by rw [e2]; exact Array.getElem_mem _)
  simp only [Bool.and_eq_true, Bool.not_eq_true', Array.isEmpty_iff] at hrow
  exact ⟨hrow.1.1, hrow.1.2, hrow.2⟩

/-- The premise on the ledger in front itself, with code: no row has lists of factors, and the
verifier's own test on the row accepts. -/
def rowsCleanB (F : Fork) : Bool :=
  F.trees.all fun X => X.rows.all fun row =>
    row.rowLo.isEmpty && row.rowHi.isEmpty && rowV X row

/-- Its yes gives a clean ledger. -/
theorem rowClean_of_rowsCleanB {F : Fork} (h : rowsCleanB F = true) : EachRow RowClean F := by
  intro t e hr
  unfold rowsCleanB at h
  obtain ⟨ht, he⟩ := hr
  have e1 : F.trees.getD t {} = F.trees[t]'ht := by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem ht]
    rfl
  have e2 : rowAt F t e = (F.trees.getD t {}).rows[e]'he := by
    unfold rowAt
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem he]
    rfl
  have hX := Array.all_eq_true'.1 h (F.trees.getD t {}) (by rw [e1]; exact Array.getElem_mem _)
  have hrow := Array.all_eq_true'.1 hX (rowAt F t e) (by rw [e2]; exact Array.getElem_mem _)
  simp only [Bool.and_eq_true, Array.isEmpty_iff] at hrow
  exact ⟨⟨hrow.1.1, hrow.1.2⟩, rowFormAt_of_rowV _ _ hrow.2⟩

/-- **THE CLAUSE FROM THE TWO TESTS WITH CODE.** -/
theorem termsV_of_tests (L : LinkCtx) {tl : HTailF2} {g : Forest.Heard} {F : Fork}
    (h1 : coefLettersB tl g F = true) (h2 : rowsCleanB F = true) :
    termsV L { coefAll tl g F with doorShutF := true } = true :=
  termsV_coefAll L tl g F (coefLetters_of_B h1) (rowClean_of_rowsCleanB h2)

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.EachRow.mono
#print axioms Johnson.AtFull.Shape.eachRow_onRow
#print axioms Johnson.AtFull.Shape.eachRow_foldl
#print axioms Johnson.AtFull.Shape.rowFormAt_tree
#print axioms Johnson.AtFull.Shape.clog2_32
#print axioms Johnson.AtFull.Shape.rowFormAt_one
#print axioms Johnson.AtFull.Shape.rowFormAt_ones32
#print axioms Johnson.AtFull.Shape.rowFormAt_table32
#print axioms Johnson.AtFull.Shape.rowFormAt_powers
#print axioms Johnson.AtFull.Shape.pieceW_block
#print axioms Johnson.AtFull.Shape.rowFormAt_piece
#print axioms Johnson.AtFull.Shape.forms_tables
#print axioms Johnson.AtFull.Shape.forms_coefAll
#print axioms Johnson.AtFull.Shape.rowV_of
#print axioms Johnson.AtFull.Shape.of_everyFrom
#print axioms Johnson.AtFull.Shape.rowFormAt_of_rowV
#print axioms Johnson.AtFull.Shape.termsV_of
#print axioms Johnson.AtFull.Shape.termsV_coefAll
#print axioms Johnson.AtFull.Shape.rowClean_of_fresh
#print axioms Johnson.AtFull.Shape.powered_letters
#print axioms Johnson.AtFull.Shape.coefLetters_of_B
#print axioms Johnson.AtFull.Shape.coefPlanesB_can_fail
#print axioms Johnson.AtFull.Shape.rowClean_of_rowsFreshB
#print axioms Johnson.AtFull.Shape.rowClean_of_rowsCleanB
#print axioms Johnson.AtFull.Shape.termsV_of_tests
