-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K12/Honest/OwnFoldLaws.lean: a fold of the proximity test whose own first message
brings the fresh mask table: the description's fold and the proximity test's part over it return
ok, and what they return is written out; and the claim that they return is true at three folded
messages, under premises on what the rounds show. From the test on a view's format (`roundsFit`,
Johnson/Desc/Block.lean), one test on the plan (`foldCutOwn`) and what is asked in front
(`FoldFrontOwn`): Johnson/Desc/K12/Honest/OwnFold.lean.

How. The verifier's two cases part where the table is entered, and in the number of roots that
"FOLD epsilon"'s entry must state. Behind the entering the text is one. So: the entering is written
out (`recvP_own`); `enteredT` meets the premise of the first case's laws (`front_entered`); and
each of these laws that reads the structure in front can be called there.

Main names.
  `rootEntry_of`, `fit_root`, `heard_root`, `foldCutOwn_of`   the tests, unfolded; the round with
      the root is heard.
  `treesMade_own`   the one announced table is always placed, and alone: `ownLay`.
  `recvL_own`, `recvP_own`   the entering accepts, and what it leaves: from the shape's test and
      "statement and book count the same number of oracle messages".
  `shape_own`, `maskFits_own`, `spend_own`, `rowFits_own`   the tests behind the entering: the two
      on the mask hold by the new message's construction; the two others are carried over.
  **`front_entered`**   `FoldFrontOwn` in front gives `FoldFront` at `enteredT`, with the new
      message's number as the mask's. `front_of_test`: an accepting `frontOwnB` gives
      `FoldFrontOwn`. `front_k_pos`: 1 ≤ k.
  `guard_entered`, `seat_own`   the verifier's test on the group's trees (guard (g) of `guardedProximityTestParts`'s
      batching) makes the state behind the entering for itself: it is `enteredT`'s; and where that
      test finds the new message: in part 0 of the new tree, with `ownShape` and the number
      firstTree + roots.
  `foldD_own`   `foldD` returns ok at `none`.
  `foldE_own`, `foldJ_own`, **`fold5_yes_own`**   the plain part; the part of
      Johnson/Desc/K12/Join.lean; the part of `guardedProximityTestParts`: it returns `foldTOwn`.
  **`fold_V_own`**   the single rows in `foldTOwn` are true at the three folded messages: `fold_V`
      (Johnson/Prover/Link/FoldHolds.lean) at `enteredT`.
  `foldTOwn_keeps`, `foldTOwn_oracles`   the structure behind, field by field.

Limits.
- The premises are premises: that a structure in a run meets `FoldFrontOwn`, or a plan
  `foldCutOwn`, is not shown here (the plan: OwnFoldPlan.lean; one synthetic example:
  OwnFoldToy.lean; neither is in this library).
- Only `decide` is served. What the fold's block asks of the plan alone in this case (one oracle
  message told at "FOLD epsilon"; `planOk`) is not here.
- `fold5_yes_own` is general in the stage's number j. Where the masks come early (`P12.early`,
  which `guardedProximityTestParts` asks of the plan) the frame's question behind each stage, "the next mask has not
  come", excludes an empty field `mask` from stage 1 on: there the law speaks of structures that no
  run of the block reaches.
- One premise reads elements: `FoldFrontOwn.rowFits`, as in the first case (the head of
  Johnson/Prover/Link/FormFoldLaws.lean says how).
- `fold_V_own` uses one clause of `FoldFrontOwn`: `rowFits`. It is `fold_holds` (FoldHolds.lean) at
  the statement `withOwn`: nothing in it is about the entering.
- In `fold_V_own` μ, φ and W are free variables; no prover is named. It says nothing at a table φ
  that does not pair with the coefficients W (`Pairs`). FoldHolds.lean's head speaks of a table
  that is sent ahead of the fold: here the fold's own first message brings its root. So to lay the
  table off the same W that the rounds read, with its tail, is the task of whoever writes this
  fold's prover, not of an earlier sender. That the tree under that root holds φ's code words is
  not said here: the part is shown no root (no view holds a root, and `roundsFit` compares a round
  with its entry's items without the roots), so φ can be tied to that tree only where its columns
  are opened.
- At k = 0 `FoldFrontOwn` cannot be met, and every theorem that takes it says nothing.
- `foldD_own` and what stands on it hold at every value that the fold's own rounds sample.
- Nothing on completeness of a protocol, on soundness or on what is hidden.
-/
import Johnson.Desc.K12.Honest.OwnFold
import Johnson.Prover.Link.FoldHolds
import Johnson.Desc.Own.FoldMean

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Params OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.First.Close
open Johnson.Prover.Link

/-! ## 1 The tests on the plan, unfolded; the round with the root -/

theorem rootEntry_of {name : String} {items : Nat} {e : Fmt.Entry}
    (h : rootEntry name items e = true) :
    (e.name == name) = true ∧ e.drawNZ = 0 ∧ e.count = 1 ∧ e.msg = 24 * items + 32 ∧ e.roots = 1 ∧
      e.answers = 0 ∧ e.poss = 0 ∧ e.trits = 0 ∧ e.drawE = 1 ∧ e.rows = 0 := by
  unfold rootEntry at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := h
  exact ⟨beq_iff_eq.2 h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

/-- What `roundsFit` holds of one round with a root and elements: a view shows no root. -/
theorem fit_root {name : String} {items : Nat} {d : Fmt.DeclaredRound} {r : Fmt.RoundView}
    (he : rootEntry name items d.entry = true) (hf : roundsFit [d] [r] = true) :
    r.vals.map itemOf = List.replicate items Fmt.Item.e ∧ r.drawn.elems.length = 1 ∧
      r.drawn.poss.length = 0 ∧ r.drawn.trits.length = 0 := by
  obtain ⟨_, _, _, h4, h5, h6, h7, h8, h9, _⟩ := rootEntry_of he
  unfold roundsFit at hf
  simp only [Bool.and_eq_true, beq_iff_eq] at hf
  obtain ⟨⟨⟨⟨⟨⟨⟨f1, f2⟩, f3⟩, f4⟩, _⟩, _⟩, _⟩, _⟩ := hf
  refine ⟨?_, f2.trans h9, f3.trans h7, f4.trans h8⟩
  rw [f1]
  show (d.entry.cut).filter (· != .root) = _
  unfold Fmt.Entry.cut
  rw [h4, h5, h6]
  have e : (24 * items + 32 - 24 * 0 - 32 * 1) / 24 = items := by omega
  rw [e]
  simp

/-- **The round with one root and elements is heard.** -/
theorem heard_root (name : String) (items : Nat) (d : Fmt.DeclaredRound) (r : Fmt.RoundView)
    (he : rootEntry name items d.entry = true) (hf : roundsFit [d] [r] = true) :
    heard name items d.entry r 1 = .ok (sentOf r, drawnOf r) ∧ (sentOf r).length = items := by
  obtain ⟨g1, g2, g3, g4⟩ := fit_root he hf
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, _⟩ := rootEntry_of he
  obtain ⟨a1, a2, a3⟩ := all_e r.vals items g1
  refine ⟨?_, a2⟩
  obtain ⟨x, hx⟩ : ∃ x, r.drawn.elems = [x] := List.length_eq_one_iff.1 g2
  unfold heard
  rw [h1, h2, h3, h4, h5, h6, h7, h8, h9, a3, g2, g3, g4, hx]
  erw [a1]
  simp only [First.Close.need, got, beq_self_eq_true, Bool.and_self, Nat.mul_one]
  show (Except.ok (sentOf r, E.ofTriple x) : Except String (List E × E)) = _
  unfold drawnOf
  rw [hx]
  rfl

theorem foldCutOwn_of {k : Nat} {dE : Fmt.DeclaredRound} {dR : List Fmt.DeclaredRound}
    (h : foldCutOwn k (dE :: dR) = true) :
    rootEntry "FOLD epsilon" 1 dE.entry = true ∧ dR.length = k ∧
      (dR.all fun d => elemEntry "FOLD round" 2 d.entry) = true ∧
      ((dE :: dR).all fun d => d.stored.isEmpty && d.opens.isEmpty) = true := by
  unfold foldCutOwn at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

/-! ## 2 The entering -/

/-- A function applied to the last entry of an array. -/
theorem modify_last {α : Type} (a : Array α) (x : α) (f : α → α) :
    (a.push x).modify a.size f = a.push (f x) := by
  apply Array.ext_getElem?
  intro i
  rw [Array.getElem?_modify, Array.getElem?_push, Array.getElem?_push]
  by_cases h : a.size = i
  · subst h
    simp
  · have h' : ¬ i = a.size := fun e => h e.symm
    simp [h, h']

/-- One announced message without a main row, with m + 1 mask rows and no sample: it is placed alone
in a tree of its own. -/
theorem treesMade_one (codes : Codes) (zc m cls : Nat) :
    Own.treesMade codes
      #[{ shape := { maskRows := m + 1, maskCode := zc, answers := 0 }, leafClass := cls }] =
      some { tree := #[0], part := #[0]
             shapes := #[{ logN := (codes.mask.getD zc default).logN
                           logNzk := (codes.mask.getD zc default).logN
                           mainSymbols := #[0], maskSymbols := #[(m + 1) * 3] }] } := by
  have hfill : (List.range 1).foldlM
      (Own.fillStep codes
        #[{ shape := { maskRows := m + 1, maskCode := zc, answers := 0 }, leafClass := cls }] #[0])
      ((#[{}], #[], #[0]) : Array TreeShape × Array Nat × Array Nat) =
      some (#[{ logNzk := (codes.mask.getD zc default).logN
                mainSymbols := #[0], maskSymbols := #[(m + 1) * 3] }], #[0], #[(m + 1) * 3]) := by
    simp [List.range_succ, Own.fillStep]
  show (match (List.range 1).foldlM
      (Own.fillStep codes
        #[{ shape := { maskRows := m + 1, maskCode := zc, answers := 0 }, leafClass := cls }] #[0])
      ((#[{}], #[], #[0]) : Array TreeShape × Array Nat × Array Nat) with
    | none => none
    | some filled => Own.closeTrees #[0] filled) = _
  rw [hfill]
  show Own.closeTrees #[0] _ = _
  unfold Own.closeTrees
  simp [TreeShape.mainWidth, TreeShape.maskWidth]

/-- **The fold's own table is always placed, and alone.** -/
theorem treesMade_own (codes : Codes) (F : FoldShape) :
    Own.treesMade codes #[foldMaskNotice F] = some (ownLay codes F) := by
  obtain ⟨m, hm⟩ : ∃ m, 2 ^ F.layout.h = m + 1 :=
    ⟨2 ^ F.layout.h - 1, by have := Nat.two_pow_pos F.layout.h; omega⟩
  unfold foldMaskNotice ownLay ownShape
  rw [hm]
  exact treesMade_one codes F.maskCode m F.maskLeafClass

theorem stSent_own (S : Statement) (F : FoldShape) :
    stSent S #[foldMaskNotice F] = withOwn S F := by
  unfold stSent withOwn
  simp

/-- **The test in front of the entering accepts.** -/
theorem recvL_own (S : Statement) (B : TreeBook) (F : FoldShape)
    (hs : Own.foldShapeFits S F = true) (hb : S.oracles.size = B.place.size) :
    Ground.ok (Ground.recvL S B #[foldMaskNotice F]) = true := by
  have H := (Own.foldShapeFits_iff S F).1 hs
  unfold Own.FoldShapeFit at H
  obtain ⟨c, zk, _, hz, _⟩ := H
  have hlt : F.maskCode < S.codes.mask.size := (Array.getElem?_eq_some_iff.1 hz).1
  have h1 : Own.sentShapeFits S.codes (foldMaskNotice F).shape = true := by
    unfold Own.sentShapeFits foldMaskNotice
    simp [hlt]
  have h2 : Own.treesCan S.codes #[foldMaskNotice F] = true := by
    unfold Own.treesCan
    rw [treesMade_own]
    rfl
  unfold Ground.ok Ground.recvL Ground.sentL
  simp [h1, h2, hb]

/-- **The entering, written out.** d: the ground's carried structure. -/
theorem recvP_own {Lc : Type} (firstTree : Nat) (d : _root_.Desc.Plain.DState Lc) (F : FoldShape)
    (hs : Own.foldShapeFits d.st F = true) (hb : d.st.oracles.size = d.book.place.size) :
    Ground.recvP firstTree d #[foldMaskNotice F] =
      some (#[d.st.oracles.size],
        { d with st := withOwn d.st F, book := ownBook firstTree d.st d.book d.roots F
                 roots := d.roots + 1 }) := by
  have e1 : (Array.range (#[foldMaskNotice F] : Array OracleNotice).size).map
      (· + d.st.oracles.size) = #[d.st.oracles.size] := by
    apply Array.toList_inj.1
    simp [Array.toList_range, List.range_succ]
  have e2 : partsLaid #[foldMaskNotice F] (ownLay d.st.codes F) d.st.oracles.size
      d.book.trees.size
      (treesSent firstTree (ownLay d.st.codes F).shapes.toList d.roots d.book.trees) =
      d.book.trees.push (ownTree firstTree d.roots d.st.oracles.size d.st.codes F) := by
    show ((d.book.trees.push
      { shape := ownShape d.st.codes F, number := firstTree + d.roots, src := .own d.roots }).modify
        d.book.trees.size fun x => { x with
          parts := x.parts.push d.st.oracles.size
          oneList := x.oneList || (foldMaskNotice F).shape.answers == 0 }) = _
    rw [modify_last]
    rfl
  have e3 : d.book.place ++ (Array.range (#[foldMaskNotice F] : Array OracleNotice).size).map
      (fun i => (d.book.trees.size + (ownLay d.st.codes F).tree.getD i 0,
        (ownLay d.st.codes F).part.getD i 0)) = d.book.place.push (d.book.trees.size, 0) := by
    apply Array.toList_inj.1
    simp [Array.toList_range, List.range_succ, ownLay]
  unfold Ground.recvP
  rw [if_pos (recvL_own d.st d.book F hs hb), treesMade_own, Option.map_some]
  simp only [e1, e2, e3, stSent_own]
  rfl

/-! ## 3 The tests behind the entering -/

theorem own_get (S : Statement) (F : FoldShape) :
    (withOwn S F).oracles[S.oracles.size]? = some { shape := (foldMaskNotice F).shape } := by
  show (S.oracles.push _)[S.oracles.size]? = _
  rw [Array.getElem?_push, if_pos rfl]

theorem old_get (S : Statement) (F : FoldShape) {o : Nat} {x : OnBytes.Oracle}
    (h : S.oracles[o]? = some x) : (withOwn S F).oracles[o]? = some x := by
  obtain ⟨hi, e⟩ := Array.getElem?_eq_some_iff.1 h
  show (S.oracles.push _)[o]? = _
  rw [Array.getElem?_push_lt hi, e]

/-- The shape's test is carried over: it reads the codes and the members, which are older. -/
theorem shape_own {S : Statement} {F : FoldShape} (F' : FoldShape)
    (h : Own.foldShapeFits S F = true) : Own.foldShapeFits (withOwn S F') F = true := by
  have H := (Own.foldShapeFits_iff S F).1 h
  unfold Own.FoldShapeFit Own.ShapeFitAt at H
  obtain ⟨c, zk, hc, hz, h1, h2, h3, h4, h5, h6, h7, hall, i, hi, x, hx, hr⟩ := H
  rw [Own.foldShapeFits_iff]
  unfold Own.FoldShapeFit Own.ShapeFitAt
  refine ⟨c, zk, hc, hz, h1, h2, h3, h4, h5, h6, h7, fun i hi => ?_, i, hi, x, old_get S F' hx,
    hr⟩
  have M := hall i hi
  unfold Own.MemberFit at M ⊢
  obtain ⟨y, hy, r⟩ := M
  exact ⟨y, old_get S F' hy, r⟩

/-- **The new message can be the fold's fresh mask**: by its construction; and it is no member,
since every member is older. -/
theorem maskFits_own {S : Statement} {F : FoldShape} (h : Own.foldShapeFits S F = true) :
    Own.foldMaskFits (withOwn S F) F S.oracles.size = true := by
  have H := (Own.foldShapeFits_iff S F).1 h
  unfold Own.FoldShapeFit Own.ShapeFitAt at H
  obtain ⟨c, zk, _, _, _, _, _, _, _, _, _, hall, _⟩ := H
  rw [Own.foldMaskFits_iff]
  unfold Own.FoldMaskFit
  refine ⟨_, own_get S F, rfl, rfl, rfl, rfl, rfl, fun hm => ?_⟩
  obtain ⟨i, hi, e⟩ := Array.mem_iff_getElem.1 hm
  have M := hall i hi
  unfold Own.MemberFit at M
  obtain ⟨y, hy, _⟩ := M
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi, Option.getD_some, e,
    Array.getElem?_eq_none (Nat.le_refl _)] at hy
  cases hy

/-- **The new message can be spent as a mask**: by its construction. -/
theorem spend_own (S : Statement) (F : FoldShape) :
    Ground.ok (Ground.spendAsMaskL (withOwn S F) S.oracles.size) = true := by
  unfold Ground.spendAsMaskL
  simp only [own_get]
  rfl

/-- The new message has no main row: no main table's index bits turn. -/
theorem tableBits_own (S : Statement) (F : FoldShape) (o : Nat) :
    (withOwn S F).tableBits o .main = S.tableBits o .main := by
  unfold Statement.tableBits Statement.rowBits Statement.placeBits
  by_cases e : o = S.oracles.size
  · subst e
    rw [own_get, Array.getElem?_eq_none (Nat.le_refl _)]
    rfl
  · cases h : S.oracles[o]? with
    | some x =>
      rw [old_get S F h]
      rfl
    | none =>
      have hn : (withOwn S F).oracles[o]? = none := by
        show (S.oracles.push _)[o]? = none
        rw [Array.getElem?_push, if_neg e]
        exact h
      rw [hn]

/-- **The test on the row is carried over.** -/
theorem rowFits_own (S : Statement) (F F' : FoldShape) (row : GroupRow) :
    Own.foldRowFits (withOwn S F') F row = Own.foldRowFits S F row := by
  unfold Own.foldRowFits
  simp only [tableBits_own]
  rfl

section Part
variable {p : P12} {j : Nat} {cur : Fmt.M1.Stage} {cut : List Fmt.DeclaredRound} {t : T12}
  {row : GroupRow} {L : GroupLayout} {c : IoppStage} {n : Nat × Nat}

/-- **`enteredT` meets what the first case's laws ask in front of a fold**, with the new message's
number as the mask's. -/
theorem front_entered (H : FoldFrontOwn p j cur t row L c n) :
    FoldFront p j cur (enteredT p t (ioppFoldShape c L)) row L c n t.st.oracles.size where
  pass := H.pass
  stage := H.stage
  next := H.next
  shape := shape_own _ H.shape
  mask := rfl
  maskFits := maskFits_own H.shape
  spend := spend_own _ _
  rowFits := (rowFits_own _ _ _ _).trans H.rowFits
  group := H.group

/-- The verifier's own test on the group's trees (guard (g) of `guardedProximityTestParts`'s batching) makes the
state behind the entering for itself (`H2K.First.entered`, Johnson/Desc/K12/Law/FirstOk.lean): it
is the one written out here. -/
theorem guard_entered (H : FoldFrontOwn p j cur t row L c n) :
    H2K.First.entered p t c L = some (t.st.oracles.size,
      (enteredT p t (ioppFoldShape c L)).st, (enteredT p t (ioppFoldShape c L)).book) := by
  unfold H2K.First.entered
  rw [H.mask]
  show ((Ground.recvP p.nums.firstTree
    (⟨t.st, t.book, t.roots, [], ()⟩ : _root_.Desc.Plain.DState Unit)
    #[foldMaskNotice (ioppFoldShape c L)]).bind fun x =>
      (x.1[0]?).map fun id => (id, x.2.st, x.2.book)) = _
  rw [recvP_own p.nums.firstTree _ _ H.shape H.inStep]
  rfl

/-- Where that test finds the new message: part 0 of the new tree, which has the shape `ownShape`
and the number firstTree + roots. -/
theorem seat_own (H : FoldFrontOwn p j cur t row L c n) :
    H2K.First.seatOf (enteredT p t (ioppFoldShape c L)).st (enteredT p t (ioppFoldShape c L)).book
      t.st.oracles.size =
      some ⟨t.st.oracles.size, (foldMaskNotice (ioppFoldShape c L)).shape, t.book.trees.size, 0,
        ownShape t.st.codes (ioppFoldShape c L), p.nums.firstTree + t.roots⟩ := by
  have e0 : (enteredT p t (ioppFoldShape c L)).st.oracles[t.st.oracles.size]? =
      some { shape := (foldMaskNotice (ioppFoldShape c L)).shape } := own_get _ _
  have e1 : (enteredT p t (ioppFoldShape c L)).book.place[t.st.oracles.size]? =
      some (t.book.trees.size, 0) := by
    show (t.book.place.push _)[t.st.oracles.size]? = _
    rw [H.inStep, Array.getElem?_push, if_pos rfl]
  have e2 : (enteredT p t (ioppFoldShape c L)).book.trees[t.book.trees.size]? =
      some (ownTree p.nums.firstTree t.roots t.st.oracles.size t.st.codes (ioppFoldShape c L)) := by
    show (t.book.trees.push _)[t.book.trees.size]? = _
    rw [Array.getElem?_push, if_pos rfl]
  unfold H2K.First.seatOf
  rw [e0, e1]
  show ((enteredT p t (ioppFoldShape c L)).book.trees[t.book.trees.size]?).map _ = _
  rw [e2]
  rfl

/-- An accepting `frontOwnB` gives `FoldFrontOwn`. -/
theorem front_of_test (h : frontOwnB p j cur t = true) :
    ∃ row L c n, FoldFrontOwn p j cur t row L c n := by
  unfold frontOwnB at h
  split at h
  · rename_i row L c n h1 h2 h3
    simp only [Bool.and_eq_true, beq_iff_eq, Option.isNone_iff_eq_none] at h
    exact ⟨row, L, c, n, h1, h2, h3, h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩
  · cases h

/-- A stage without a row variable has no such fold. -/
theorem front_k_pos (H : FoldFrontOwn p j cur t row L c n) : 1 ≤ c.k := by
  have K := (Own.foldShapeFits_iff _ _).1 H.shape
  unfold Own.FoldShapeFit Own.ShapeFitAt at K
  obtain ⟨_, _, _, _, h1, _⟩ := K
  exact h1

end Part

/-! ## 4 The fold -/

/-- **`foldD` returns ok where no message is handed in as the mask.** -/
theorem foldD_own {Lc : Type} (firstTree : Nat) (d : _root_.Desc.Plain.DState Lc) (F : FoldShape)
    (row : GroupRow) (cut : List Fmt.DeclaredRound) (rs : List Fmt.RoundView)
    (hc : foldCutOwn F.layout.k cut = true) (hf : roundsFit cut rs = true)
    (h1 : Own.foldShapeFits d.st F = true) (hb : d.st.oracles.size = d.book.place.size)
    (h4 : Own.foldRowFits d.st F row = true) :
    foldD firstTree d F row none (cut.map (·.entry)) rs =
      .ok (foldOutAt (withOwn d.st F) F row d.st.oracles.size rs,
        { d with st := spent (withOwn d.st F) d.st.oracles.size
                 book := ownBook firstTree d.st d.book d.roots F, roots := d.roots + 1 }) := by
  cases cut with
  | nil => cases hc
  | cons dE dR =>
    cases rs with
    | nil => cases hf
    | cons rE rR =>
      obtain ⟨c1, c2, c3, _⟩ := foldCutOwn_of hc
      obtain ⟨f1, f2⟩ := Bool.and_eq_true_iff.1 ((H2K.Fit.roundsFit_cons _ _ _ _).symm.trans hf)
      obtain ⟨hh, hl⟩ := heard_root "FOLD epsilon" 1 dE rE c1 f1
      obtain ⟨sum, hs⟩ : ∃ x, sentOf rE = [x] := List.length_eq_one_iff.1 hl
      have hrows : ((dE :: dR).map (·.entry)).all (·.rows == 0) = true := by
        rw [List.all_map, List.all_cons, Bool.and_eq_true]
        refine ⟨beq_iff_eq.2 (rootEntry_of c1).2.2.2.2.2.2.2.2.2, ?_⟩
        rw [List.all_eq_true] at c3 ⊢
        exact fun x hx => beq_iff_eq.2 (elemEntry_of (c3 x hx)).2.2.2.2.2.2.2.2.2
      have hsp : Ground.spendAsMaskP
          ({ d with st := withOwn d.st F, book := ownBook firstTree d.st d.book d.roots F
                    roots := d.roots + 1 } : _root_.Desc.Plain.DState Lc) d.st.oracles.size =
          some { d with st := spent (withOwn d.st F) d.st.oracles.size
                        book := ownBook firstTree d.st d.book d.roots F
                        roots := d.roots + 1 } := by
        unfold Ground.spendAsMaskP
        rw [if_pos (spend_own d.st F)]
        rfl
      have hlen : ((dR.map (·.entry)).length == F.layout.k && rR.length == F.layout.k) = true := by
        rw [List.length_map, ← H2K.Sw.roundsFit_length _ _ f2, c2]
        simp
      rw [List.map_cons, foldD, hlen, ← List.map_cons, hrows, h1]
      simp only [First.Close.need, if_true]
      rw [named_ok (recvL_own d.st d.book F h1 hb), recvP_own firstTree d F h1 hb]
      show (do
        First.Close.need "K10.maskfits" (Own.foldMaskFits (withOwn d.st F) F d.st.oracles.size)
        First.Close.named (Ground.spendAsMaskL (withOwn d.st F) d.st.oracles.size)
        let d2 ← got "K10.maskfits" (Ground.spendAsMaskP
          ({ d with st := withOwn d.st F, book := ownBook firstTree d.st d.book d.roots F
                    roots := d.roots + 1 } : _root_.Desc.Plain.DState Lc) d.st.oracles.size)
        match ← heard "FOLD epsilon" 1 dE.entry rE (d.roots + 1 - d.roots) with
        | ([sum], eps) =>
          First.Close.need "K10.rowfits" (Own.foldRowFits d2.st F row)
          let (gamma, claim) ← rounds (dR.map (·.entry)) rR (maddE sum eps row.target)
          pure (foldOutput d2.st F row d.st.oracles.size eps gamma claim, d2)
        | _ => .error "K10.items" :
          Except String (SingleRows × _root_.Desc.Plain.DState Lc)) = _
      rw [maskFits_own h1, named_ok (spend_own d.st F), hsp, Nat.add_sub_cancel_left, hh, hs]
      show (do
        First.Close.need "K10.rowfits"
          (Own.foldRowFits (spent (withOwn d.st F) d.st.oracles.size) F row)
        let (gamma, claim) ← rounds (dR.map (·.entry)) rR (maddE sum (drawnOf rE) row.target)
        pure (foldOutput (spent (withOwn d.st F) d.st.oracles.size) F row d.st.oracles.size
            (drawnOf rE) gamma claim,
          { d with st := spent (withOwn d.st F) d.st.oracles.size
                   book := ownBook firstTree d.st d.book d.roots F, roots := d.roots + 1 }) :
          Except String (SingleRows × _root_.Desc.Plain.DState Lc)) = _
      rw [foldRowFits_spent, rowFits_own, h4, rounds_yes dR rR _ c3 f2]
      show (Except.ok (foldOutput (spent (withOwn d.st F) d.st.oracles.size) F row
          d.st.oracles.size (drawnOf rE) (rR.map drawnOf)
          (claimOf rR (maddE sum (drawnOf rE) row.target)),
        { d with st := spent (withOwn d.st F) d.st.oracles.size
                 book := ownBook firstTree d.st d.book d.roots F, roots := d.roots + 1 }) :
          Except String (SingleRows × _root_.Desc.Plain.DState Lc)) = _
      show _ = (Except.ok (foldOutput (spent (withOwn d.st F) d.st.oracles.size) F row
          d.st.oracles.size (drawnOf rE) (rR.map drawnOf)
          (claimOf rR (maddE ((sentOf rE).getD 0 zeroE) (drawnOf rE) row.target)),
        { d with st := spent (withOwn d.st F) d.st.oracles.size
                 book := ownBook firstTree d.st d.book d.roots F, roots := d.roots + 1 }) :
          Except String (SingleRows × _root_.Desc.Plain.DState Lc))
      rw [hs]
      rfl

/-! ## 5 The part in the kind's block -/

section Part
variable {p : P12} {j : Nat} {cur : Fmt.M1.Stage} {cut : List Fmt.DeclaredRound} {t : T12}
  {row : GroupRow} {L : GroupLayout} {c : IoppStage} {n : Nat × Nat}

/-- **The plain part returns ok.** -/
theorem foldE_own (H : FoldFrontOwn p j cur t row L c n) (hc : foldCutOwn c.k cut = true)
    (rs : List Fmt.RoundView) (hf : roundsFit cut rs = true) :
    H2K.foldE (ioppFoldShape c L) row t.mask (lay p cut none t rs []) =
      .ok (foldOut (enteredT p t (ioppFoldShape c L)) row L c t.st.oracles.size rs,
        { lay p cut none t rs [] with
          d := { (lay p cut none t rs []).d with
                 st := spent (withOwn t.st (ioppFoldShape c L)) t.st.oracles.size
                 book := ownBook p.nums.firstTree t.st t.book t.roots (ioppFoldShape c L)
                 roots := t.roots + 1 }
          entries := [], rounds := [], last := (cut.map (·.entry)).getLast?, asked := false }) := by
  have lc : cut.length = 1 + c.k := by
    cases cut with
    | nil => cases hc
    | cons dE dR =>
      rw [List.length_cons, (foldCutOwn_of hc).2.1]
      omega
  have lr : rs.length = 1 + c.k := (H2K.Sw.roundsFit_length _ _ hf).symm.trans lc
  have hD := foldD_own p.nums.firstTree (lay p cut none t rs []).d (ioppFoldShape c L) row cut rs
    hc hf H.shape H.inStep H.rowFits
  unfold H2K.foldE
  rw [H.mask]
  have e1 : (lay p cut none t rs []).entries.take (1 + (ioppFoldShape c L).layout.k) =
      cut.map (·.entry) := by
    show (cut.map (·.entry)).take (1 + c.k) = _
    exact List.take_of_length_le (by rw [List.length_map, lc])
  have e2 : (lay p cut none t rs []).rounds.take (1 + (ioppFoldShape c L).layout.k) = rs :=
    List.take_of_length_le (le_of_eq lr)
  have e3 : (lay p cut none t rs []).entries.drop (1 + (ioppFoldShape c L).layout.k) = [] := by
    show (cut.map (·.entry)).drop (1 + c.k) = _
    exact List.drop_eq_nil_of_le (by rw [List.length_map, lc])
  have e4 : (lay p cut none t rs []).rounds.drop (1 + (ioppFoldShape c L).layout.k) = [] :=
    List.drop_eq_nil_of_le (le_of_eq lr)
  have g1 : (lay p cut none t rs []).owed.isNone = true := rfl
  have g2 : (decide (1 + (ioppFoldShape c L).layout.k ≤ (lay p cut none t rs []).entries.length) &&
      decide (1 + (ioppFoldShape c L).layout.k ≤ (lay p cut none t rs []).rounds.length)) =
      true := by
    rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
    refine ⟨?_, le_of_eq lr.symm⟩
    show 1 + c.k ≤ (cut.map (·.entry)).length
    rw [List.length_map, lc]
  simp only [g1, g2, e1, e2, e3, e4, H2K.need, if_true]
  show (do
    let x ← (First.Close.foldD p.nums.firstTree (lay p cut none t rs []).d (ioppFoldShape c L) row
      none (cut.map (·.entry)) rs).mapError ("fold: " ++ ·)
    pure (x.1,
      { lay p cut none t rs [] with
        d := x.2, entries := [], rounds := [], last := (cut.map (·.entry)).getLast?
        asked := false }) : Except String (SingleRows × H2K.PS)) = _
  rw [hD]
  rfl

/-- **The part of Johnson/Desc/K12/Join.lean accepts, and the structure behind is `foldTOwn`.** -/
theorem foldJ_own (H : FoldFrontOwn p j cur t row L c n) (hc : foldCutOwn c.k cut = true)
    (rs : List Fmt.RoundView) (hf : roundsFit cut rs = true) :
    (foldJ p j cur cut).decide t rs [] = .ok (foldTOwn p t row L c n rs) := by
  have hg : Ground.ok (Ground.newGroupL
      (spent (withOwn t.st (ioppFoldShape c L)) t.st.oracles.size) n.1 n.2) = true := H.group
  simp only [foldJ, H.pass, H.stage, H.next]
  rw [foldE_own H hc rs hf]
  show (do
    let y ← H2K.newGroupE n.1 n.2
      { lay p cut none t rs [] with
        d := { (lay p cut none t rs []).d with
               st := spent (withOwn t.st (ioppFoldShape c L)) t.st.oracles.size
               book := ownBook p.nums.firstTree t.st t.book t.roots (ioppFoldShape c L)
               roots := t.roots + 1 }
        entries := [], rounds := [], last := (cut.map (·.entry)).getLast?, asked := false }
    back t y.2 (.single
      (foldOut (enteredT p t (ioppFoldShape c L)) row L c t.st.oracles.size rs) y.1) t.mask :
      Except String T12) = _
  unfold H2K.newGroupE Ground.newGroupP
  rw [if_pos hg]
  simp only [H2K.opt, Except.map]
  unfold back
  show (do
    VerifiableInference.Desc.need "(v): a round, an entry or a column is left over"
      (([] : List Fmt.RoundView).isEmpty && ([] : List Fmt.Entry).isEmpty && (keyed p cut []).isEmpty)
    pure { t with
      st := Ground.withGroup (spent (withOwn t.st (ioppFoldShape c L)) t.st.oracles.size) n.1 n.2
      book := ownBook p.nums.firstTree t.st t.book t.roots (ioppFoldShape c L)
      roots := t.roots + 1
      pass := .single (foldOut (enteredT p t (ioppFoldShape c L)) row L c t.st.oracles.size rs)
        (spent (withOwn t.st (ioppFoldShape c L)) t.st.oracles.size).groups.size
      mask := t.mask } : Except String T12) = _
  rw [keyed_nil, H.mask]
  rfl

/-- **The fold's part of `guardedProximityTestParts` accepts where the fold sends its own fresh table, and the
structure behind is `foldTOwn`.** rs: its rounds as the view has them; `Block.step` shows them
without the sealed digest. -/
theorem fold5_yes_own (H : FoldFrontOwn p j cur t row L c n) (hc : foldCutOwn c.k cut = true)
    (rs : List Fmt.RoundView) (hf : roundsFit cut rs = true) :
    (guardedProximityTestParts.fold p j cur cut).decide t (rs.map noDigest) [] =
      .ok (foldTOwn p t row L c n (rs.map noDigest)) := by
  have hf' : roundsFit cut (rs.map noDigest) = true :=
    (H2K.Onto.roundsFit_noDigest cut rs).trans hf
  show (do
    VerifiableInference.Desc.need "(z): a drawn position is out of its round's range"
      (inRange cut (rs.map noDigest))
    (foldJ p j cur cut).decide t (rs.map noDigest) [] : Except String T12) = _
  rw [inRange_fold hf', foldJ_own H hc _ hf']
  rfl

end Part

/-! ## 6 The structure behind -/

/-- **The structure behind the fold**: seven equations, and the definition once more. -/
theorem foldTOwn_keeps (p : P12) (t : T12) (row : GroupRow) (L : GroupLayout) (c : IoppStage)
    (n : Nat × Nat) (rs : List Fmt.RoundView) :
    (foldTOwn p t row L c n rs).st.codes = t.st.codes ∧
    (foldTOwn p t row L c n rs).book =
      ownBook p.nums.firstTree t.st t.book t.roots (ioppFoldShape c L) ∧
    (foldTOwn p t row L c n rs).roots = t.roots + 1 ∧ (foldTOwn p t row L c n rs).g = t.g ∧
    (foldTOwn p t row L c n rs).mask = none ∧
    (foldTOwn p t row L c n rs).st.groups = t.st.groups.push { code := n.1, maskCode := n.2 } ∧
    (foldTOwn p t row L c n rs).pass =
      .single (foldOut (enteredT p t (ioppFoldShape c L)) row L c t.st.oracles.size rs)
        t.st.groups.size ∧
    foldTOwn p t row L c n rs =
      { foldT (enteredT p t (ioppFoldShape c L)) row L c n t.st.oracles.size rs with
        mask := none } :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The oracle messages behind: those in front, and the fresh table, marked as spent. -/
theorem foldTOwn_oracles (p : P12) (t : T12) (row : GroupRow) (L : GroupLayout) (c : IoppStage)
    (n : Nat × Nat) (rs : List Fmt.RoundView) :
    (foldTOwn p t row L c n rs).st.oracles =
      t.st.oracles.push
        { shape := (foldMaskNotice (ioppFoldShape c L)).shape, spentAsMask := true } := by
  show (t.st.oracles.push { shape := (foldMaskNotice (ioppFoldShape c L)).shape }).modify
    t.st.oracles.size (fun x => { x with spentAsMask := true }) = _
  rw [modify_last]

/-! ## 7 The values -/

section AtD
variable (s : Sg) (μ : s.cIn.J → GE) (φ : s.cFr.J → GE)
  (W : HIdx (sVars GE 2 (s.h + s.g)) → GE) (γ : HPt (sVars GE 2 (s.h + s.g)))

/-- **The single rows in `foldTOwn` are true at the three folded messages.** μ: the stage's
message, at which the claim in front is true. φ: the fresh table, which pairs with the coefficients
W. rE: the round "FOLD epsilon", which shows the sum of the polynomial with these coefficients. rR:
the rounds "FOLD round", which show the honest round polynomials' coefficients. -/
theorem fold_V_own {p : P12} {j : ℕ} {cur : Fmt.M1.Stage} {t : T12} {row : GroupRow}
    {L : GroupLayout} {c : IoppStage} {n : ℕ × ℕ} (H : FoldFrontOwn p j cur t row L c n)
    (rE : Fmt.RoundView) (rR : List Fmt.RoundView) (hk : c.k = s.h + s.g) (hh : c.h = s.h)
    (hZ : (t.st.codes.mask.getD c.maskCode default).ell = s.Z.l)
    (hin : (Slf.idf (E := GE) (J := s.cIn.J)).Holds (stmG s row) μ) (hP : Pairs s s.Z.l W φ)
    (hσ : readE ((sentOf rE).getD 0 zeroE) = hMu (sVars GE 2 (s.h + s.g)) W)
    (hR : Shows (s.h + s.g) rR (foldQ s (vecG s row) μ W (readE (drawnOf rE)) γ) γ) :
    (Slf.idf (E := GE) (J := s.cMid.J)).Holds
      (stmS s (foldOut (enteredT p t (ioppFoldShape c L)) row L c t.st.oracles.size (rE :: rR)))
      (foldMsg s μ φ (sPt 2 (s.h + s.g) γ)) :=
  fold_V s μ φ W γ (front_entered H) rE rR hk hh hZ hin hP hσ hR

end AtD

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.rootEntry_of
#print axioms ProofFile.Honest.K12.fit_root
#print axioms ProofFile.Honest.K12.heard_root
#print axioms ProofFile.Honest.K12.foldCutOwn_of
#print axioms ProofFile.Honest.K12.modify_last
#print axioms ProofFile.Honest.K12.treesMade_one
#print axioms ProofFile.Honest.K12.treesMade_own
#print axioms ProofFile.Honest.K12.stSent_own
#print axioms ProofFile.Honest.K12.recvL_own
#print axioms ProofFile.Honest.K12.recvP_own
#print axioms ProofFile.Honest.K12.own_get
#print axioms ProofFile.Honest.K12.old_get
#print axioms ProofFile.Honest.K12.shape_own
#print axioms ProofFile.Honest.K12.maskFits_own
#print axioms ProofFile.Honest.K12.spend_own
#print axioms ProofFile.Honest.K12.tableBits_own
#print axioms ProofFile.Honest.K12.rowFits_own
#print axioms ProofFile.Honest.K12.front_entered
#print axioms ProofFile.Honest.K12.guard_entered
#print axioms ProofFile.Honest.K12.seat_own
#print axioms ProofFile.Honest.K12.front_of_test
#print axioms ProofFile.Honest.K12.front_k_pos
#print axioms ProofFile.Honest.K12.foldD_own
#print axioms ProofFile.Honest.K12.foldE_own
#print axioms ProofFile.Honest.K12.foldJ_own
#print axioms ProofFile.Honest.K12.fold5_yes_own
#print axioms ProofFile.Honest.K12.foldTOwn_keeps
#print axioms ProofFile.Honest.K12.foldTOwn_oracles
#print axioms ProofFile.Honest.K12.fold_V_own
