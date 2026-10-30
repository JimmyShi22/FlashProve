-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/SwTies.lean: what the next joint asks of the record behind a code switch of the
proximity test.

From `Did` (Johnson/Desc/K12/Law/SwDid.lean) and the public facts: the codes stay, the new tree has
its seat, the layout, no kept form, the mask's number, the form in order. Statements and proofs.
How the file was made: most of it is a port by a program, as Johnson/Desc/K12/Law/SwClaim.lean (each
such theorem stands under a line "ported from ..."), with the context's book, first tree and count
of roots as plain letters, `bookSent c` as `bookSentP` and `Seat c` as `SeatP`. Typed by hand:
`modify_keeps`, `openOne_keeps`, `foldlM_keeps'`, `readOld_keeps` (the plain reading turns the
book's counts of lists alone), `Did.bookKeepsB`, `Did.bookKeepsR`, `Did.seat`, `did_mask`.
Limits: No statement and no proof of this file reaches a routine that runs in a context of the
program `verify-on-bytes` (`OnBytes.Ctx`, `OnBytes.Blk`, `OnBytes.Chan`); that program's plain
records and pure functions, some with names that begin with `Blk.`, and lemmas on them, are used. No
soundness is claimed. Nothing here is about hiding.
-/
import Johnson.Desc.K12.Law.SwClaim
import Johnson.Desc.K12.Law.FoldLaw

set_option autoImplicit false
namespace H2K.Sw
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun
open Iop Prob Cb Cb.Ood _root_.Run
open VerifiableInference.Desc (noDigest)

-- ported from OnBytes/Slice/BlkSeat.lean: Seat.keeps
/-- A seat stays a seat as long as the book and the statement keep what is public. -/
theorem SeatP.keeps {S S' : Statement} {Bk Bk' : TreeBook} {ids : List Nat} {n logN : Nat} {shapes
    : List OracleShape}
    (h : SeatP S Bk ids n logN shapes) (hb : BookKeeps Bk Bk') (hs : ShapesKeep S S') :
    SeatP S' Bk' ids n logN shapes := by
  obtain ⟨t, tree, h1, h2, h3, h4, h5, h6⟩ := h.tree
  obtain ⟨T', k1, e1, e2, _⟩ := hb.tree t tree h1
  refine ⟨h.len, ⟨t, T', k1, e2.trans h2, ?_, ?_, ?_, fun w hw => hb.place _ _ (h6 w hw)⟩,
    fun w hw => ?_⟩
  · rw [e1]
    exact h3
  · rw [e1]
    exact h4
  · rw [e1]
    exact h5
  · obtain ⟨x, hx, ex⟩ := h.shape w hw
    obtain ⟨x', hx', ex'⟩ := hs _ x hx
    exact ⟨x', hx', ex'.trans ex⟩

-- ported from OnBytes/Slice/BlkSentSeat.lean: bookSent_keeps
/-- The book after a prover's message with oracle messages keeps what the book before it
said. -/
theorem bookSentP_keeps (ft roots : Nat) (S : Statement) (Bk : TreeBook) (sent : Array
    OracleNotice) (lay : TreeLay) :
    BookKeeps Bk (bookSentP ft roots S Bk sent lay) := by
  constructor
  · intro o p h
    have ho : o < Bk.place.size := by
      rcases Nat.lt_or_ge o Bk.place.size with h1 | h1
      · exact h1
      · rw [Array.getElem?_eq_none h1] at h
        cases h
    show (Bk.place ++ _)[o]? = some p
    rw [Array.getElem?_append_left ho]
    exact h
  · intro t T h
    have ht : t < Bk.trees.size := by
      rcases Nat.lt_or_ge t Bk.trees.size with h1 | h1
      · exact h1
      · rw [Array.getElem?_eq_none h1] at h
        cases h
    refine ⟨T, ?_, rfl, rfl, rfl⟩
    show (partsLaid sent lay _ Bk.trees.size (treesSent _ _ _ Bk.trees))[t]? = some T
    rw [partsLaid_old _ _ _ _ _ t ht, treesSent_old _ _ _ _ t ht]
    exact h

-- ported from OnBytes/Slice/BlkSentSeat.lean: seat_of_sent
/-- The oracle messages of one prover's message that the program has put in one tree are the
parts of that tree, in the order of sending. S, Bk: the statement and the book before the message.
S2, B2: a statement and a book behind it: the book is the book after the message, the statement has
the shapes of the statement after it. sh: the tree's shape. Asked besides: the shape lists the
messages' symbols (`hmain`, `hmask`),
and before the message the book has as many places as the statement has oracle messages (`hp`). -/
theorem seatP_of_sent (ft roots : Nat) (S S2 : Statement) (Bk B2 : TreeBook) (sent : Array
    OracleNotice) (lay : TreeLay) (sh : TreeShape)
    (hp : S.oracles.size = Bk.place.size) (hb : B2 = bookSentP ft roots S Bk sent lay)
    (hs : ∀ i : Nat, (S2.oracles[i]?).map (·.shape)
      = ((stSent S sent).oracles[i]?).map (·.shape))
    (h1 : lay.shapes = #[sh])
    (ht : ∀ i, i < sent.size → lay.tree.getD i 0 = 0 ∧ lay.part.getD i 0 = i)
    (hmain : sh.mainSymbols
      = ((sent.toList.map (·.shape)).map fun s => s.mainRows * s.mainDeg).toArray)
    (hmask : sh.maskSymbols
      = ((sent.toList.map (·.shape)).map fun s => s.maskRows * 3).toArray) :
    SeatP S2 B2 ((List.range sent.size).map (· + S.oracles.size))
      (ft + roots) sh.logN (sent.toList.map (·.shape)) := by
  have hid : ∀ w, w < sent.size →
      ((List.range sent.size).map (· + S.oracles.size)).getD w 0
        = w + S.oracles.size := by
    intro w hw
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hw]
    rfl
  refine ⟨by simp, ?_, ?_⟩
  · -- the tree
    have hpub := partsLaid_public sent lay S.oracles.size Bk.trees.size
      (treesSent ft lay.shapes.toList roots Bk.trees) Bk.trees.size
    rw [h1] at hpub
    have hnew : (treesSent ft (#[sh] : Array TreeShape).toList roots
        Bk.trees)[Bk.trees.size]?
          = some
            { shape := sh, number := ft + roots, src := .own roots } := by
      show (Bk.trees.push _)[Bk.trees.size]? = _
      rw [Array.getElem?_push_size]
    rw [hnew] at hpub
    cases htree : (partsLaid sent lay S.oracles.size Bk.trees.size
        (treesSent ft (#[sh] : Array TreeShape).toList roots Bk.trees))[
          Bk.trees.size]? with
    | none => rw [htree] at hpub; cases hpub
    | some tree =>
      rw [htree] at hpub
      obtain ⟨e1, e2⟩ := Prod.mk.inj (Option.some.inj hpub)
      refine ⟨Bk.trees.size, tree, ?_, e2, by rw [e1], by rw [e1]; exact hmain,
        by rw [e1]; exact hmask, fun w hw => ?_⟩
      · rw [hb]
        show (partsLaid _ lay _ _ (treesSent _ lay.shapes.toList _ _))[_]? = _
        rw [h1]
        exact htree
      · have hw' : w < sent.size := by simpa using hw
        rw [hid w hw', hb]
        show (Bk.place ++ _)[w + S.oracles.size]? = _
        rw [hp, Array.getElem?_append_right (Nat.le_add_left _ _), Nat.add_sub_cancel,
          Array.getElem?_map, Array.getElem?_range, if_pos hw']
        show some (Bk.trees.size + lay.tree.getD w 0, lay.part.getD w 0) = _
        rw [(ht w hw').1, (ht w hw').2, Nat.add_zero]
  · -- the shapes
    intro w hw
    have hw' : w < sent.size := by simpa using hw
    have hs : ((S2.oracles[w + S.oracles.size]?).map (·.shape))
        = some (sent[w]).shape := by
      rw [hs, Nat.add_comm, stSent_new, Array.getElem?_eq_getElem hw']
      rfl
    rw [hid w hw']
    cases hx : S2.oracles[w + S.oracles.size]? with
    | none => rw [hx] at hs; cases hs
    | some x =>
      rw [hx] at hs
      refine ⟨x, rfl, (Option.some.inj hs).trans ?_⟩
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, Array.getElem?_toList,
        Array.getElem?_eq_getElem hw']
      rfl

section
variable {ft : Nat} {cols : List Tw.L9.Col} {old : SingleRows} {T : SwitchTarget}
  {nc nz a b gp : ℕ} {others : Array OracleNotice} {S S' : Statement} {Bk Bk' : TreeBook}
  {roots : Nat} {out : Switched} {row : GroupRow} {lay : GroupLayout} {theta : E} {D : Taken}

-- ported from OnBytes/Slice/BlkCsKeeps.lean: CsRan.shape_at
/-- After a switch and the batching behind it (Did) each oracle message has the shape that it had
after the sending. -/
theorem Did.shape_at (h : Did ft cols old T gp others S Bk roots S' Bk' out row lay theta D) (i :
    Nat) :
    (S'.oracles[i]?).map (·.shape)
      = ((stSent S (sentOf T others)).oracles[i]?).map (·.shape) := by
  rw [h.st]
  show ((closeLedgers (D.stR T gp others S) _).oracles[i]?).map (·.shape) = _
  rw [closeLedgers_shape]
  unfold Taken.stR Taken.stJ Taken.stA
  rw [(withRows_oracles gp D.rows _).1, joined_shape, (ledgerShut_shape _ T _ i).2, admitted_shape]

-- ported from OnBytes/Slice/BlkCsKeeps.lean: CsRan.shapesKeep
/-- a switch and the batching behind it (Did) keeps each older oracle message, with its shape. -/
theorem Did.shapesKeep (h : Did ft cols old T gp others S Bk roots S' Bk' out row lay theta D) :
    ShapesKeep S S' := by
  intro o x hx
  have ho : o < S.oracles.size := by
    rcases Nat.lt_or_ge o S.oracles.size with h1 | h1
    · exact h1
    · rw [Array.getElem?_eq_none h1] at hx
      cases hx
  have h1 := h.shape_at o
  rw [stSent_old S _ o ho, hx] at h1
  cases hx' : S'.oracles[o]? with
  | none => rw [hx'] at h1; cases h1
  | some x' => rw [hx'] at h1; exact ⟨x', rfl, Option.some.inj h1⟩

-- ported from OnBytes/Slice/BlkCsKeeps.lean: CsRan.codes
/-- a switch and the batching behind it (Did) changes no code. -/
theorem Did.codes (h : Did ft cols old T gp others S Bk roots S' Bk' out row lay theta D) :
    S'.codes = S.codes := by
  rw [h.st]
  show (closeLedgers (D.stR T gp others S) _).codes = _
  rw [closeLedgers_codes]
  exact (D.stR_shape T gp others S).1

-- ported from OnBytes/Slice/BlkCsReadAt.lean: CsRan.shapesKeepB
/-- Each older oracle message is there, with its shape, when the old rows are read. -/
theorem Did.shapesKeepB (_h : Did ft cols old T gp others S Bk roots S' Bk' out row lay theta D) :
    ShapesKeep S (D.stA T others S) := by
  intro o x hx
  have ho : o < S.oracles.size := by
    rcases Nat.lt_or_ge o S.oracles.size with h1 | h1
    · exact h1
    · rw [Array.getElem?_eq_none h1] at hx
      cases hx
  have h1 : ((D.stA T others S).oracles[o]?).map (·.shape)
      = ((stSent S (sentOf T others)).oracles[o]?).map (·.shape) := by
    unfold Taken.stA
    rw [admitted_shape]
  rw [stSent_old S _ o ho, hx] at h1
  cases hx' : (D.stA T others S).oracles[o]? with
  | none =>
    rw [hx'] at h1
    cases h1
  | some x' =>
    rw [hx'] at h1
    exact ⟨x', rfl, Option.some.inj h1⟩

-- ported from OnBytes/Slice/BlkCsReadAt.lean: CsRan.listed
/-- A drawn position is in the list by which the trees are opened. -/
theorem Did.listed (h : Did ft cols old T gp others S Bk roots S' Bk' out row lay theta D) (x : ℕ)
    (hx : x ∈ D.rC.drawn.poss) : x ∈ out.positions.all := by
  rw [h.positions]
  show x ∈ (listOfT D.rC.drawn.poss).toArray
  rw [listOfT_eq]
  exact List.mem_toArray.2 ((Fmt.listOf_mem _ x).2 hx)

-- ported from OnBytes/Slice/BlkCsReadAt.lean: CsRan.logN_eq
/-- The list of positions has the logN of the old main code, which is the stage's. -/
theorem Did.logN_eq {s s' : Sg} {nc nz : ℕ}
    (h : Did ft cols old T gp others S Bk roots S' Bk' out row lay theta D) (P : CsProg s s'
        S.codes old nc nz) :
    out.positions.logN = s.C.a := by
  have hC : codeOf D.code = s.C := by
    have k := P.code
    rw [h.code] at k
    exact Option.some.inj k
  rw [h.positions, ← hC]
  rfl

-- ported from OnBytes/Slice/BlkCsTie.lean: CsRan.noKept
/-- The row that a switch and the batching behind it (Did) into a new group returns has no form on a
kept member. -/
theorem Did.noKept
    (h : Did ft cols old (switchTargetStage nc nz a b 1) gp others S Bk roots S' Bk' out row lay
        theta D)
    (hm : D.G.members = #[]) (hk : D.G.kept = #[]) (hr : D.G.rows = #[]) : row.kept = #[] := by
  refine combine_noKept _ gp _ theta row h.row (h.fits hm hr) fun i => ?_
  show lay.kept.getD i false = false
  rw [h.lay_eq hm hk]
  cases i <;> rfl

-- ported from OnBytes/Slice/BlkCsTie.lean: CsRan.vars
/-- After a switch and the batching behind it (Did) into a new group, each tensor of the returned
row's form on the main
table has at least one variable. -/
theorem Did.vars
    (h : Did ft cols old (switchTargetStage nc nz a b 1) gp others S Bk roots S' Bk' out row lay
        theta D)
    (hm : D.G.members = #[]) (hk : D.G.kept = #[]) (hr : D.G.rows = #[]) :
    ∀ v ∈ row.c.tensors, 1 ≤ v.vars := by
  intro v hv
  have h1 : lay.k ≤ v.vars := combine_vars _ gp _ theta row h.row (h.fits hm hr) v hv
  have h2 : lay.k = max (max a b) 1 := by rw [h.lay_eq hm hk]
  omega

-- ported from OnBytes/Slice/BlkCsTie.lean: CsRan.layAt
/-- The layout that a switch and the batching behind it (Did) into a new group returns has the new
oracle message as its
one member, from the row 0 on in both tables. -/
theorem Did.layAt
    (h : Did ft cols old (switchTargetStage nc nz a b 1) gp others S Bk roots S' Bk' out row lay
        theta D)
    (hm : D.G.members = #[]) (hk : D.G.kept = #[]) :
    LayAt [S.oracles.size] #[some 0] #[some 0] lay := by
  rw [h.lay_eq hm hk]
  exact ⟨rfl, fun w hw => by
    obtain rfl : w = 0 := by simpa using hw
    rfl, rfl, rfl⟩

-- ported from OnBytes/Slice/BlkProxOrder.lean: csRan_order
/-- The row that a switch and the batching behind it (Did) returns has a form in order, if the old
claim has. -/
theorem did_order
    (h : Did ft cols old T gp others S Bk roots S' Bk' out row lay theta D) (hkept : old.kept = #[])
    (hmasks : old.masks = 2) (hno : switchKept old = #[]) (hm : D.G.members = #[])
    (hr : D.G.rows = #[]) (hc : OrderForm old.c) : OrderForm row.c := by
  obtain ⟨W, _, hrun⟩ := h.run_rows hkept hmasks hno hm hr
  refine combine_order _ gp _ theta row (fun r hr' => ?_) h.row
  have hr2 : r ∈ (runRows (D.stR T gp others S) (D.grown S)).toList := hr'
  rw [hrun] at hr2
  unfold csRowsB at hr2
  simp only [List.mem_cons, List.mem_flatMap, List.not_mem_nil, or_false] at hr2
  rcases hr2 with rfl | rfl | ⟨x, _, rfl | rfl | rfl⟩
  · exact orderRow_carriedRow W old hc
  · exact orderRow_of_plain (plainRow_form S.codes T.shape _ ⟨_, D.beta⟩ 0 D.smp h.form)
  · exact orderRow_of_plain (plainRow_genMain _ _ _)
  · exact orderRow_of_plain (plainRow_genMask _ _ _ _)
  · exact orderRow_of_plain (plainRow_genMask _ _ _ _)

-- ported from OnBytes/Slice/BlkCsSeat.lean: CsRan.seatB
/-- The oracle messages of a switch are the parts of one tree, before the old rows are read.
sh: the tree's shape. The tree's number is that of the chain's first tree plus the number of roots
received before the switch. The hypotheses are those named in the file's head. -/
theorem Did.seatB (h : Did ft cols old T gp others S Bk roots S' Bk' out row lay theta D) (sh :
    TreeShape)
    (h1 : D.lay.shapes = #[sh])
    (ht : ∀ i, i < (sentOf T others).size → D.lay.tree.getD i 0 = 0 ∧ D.lay.part.getD i 0 = i)
    (hmain : sh.mainSymbols
      = (((sentOf T others).toList.map (·.shape)).map fun s => s.mainRows * s.mainDeg).toArray)
    (hmask : sh.maskSymbols
      = (((sentOf T others).toList.map (·.shape)).map fun s => s.maskRows * 3).toArray) :
    SeatP (D.stA T others S) (bookSentP ft roots S Bk (sentOf T others) D.lay) ((List.range (sentOf
        T others).size).map (· + S.oracles.size))
      (ft + roots) sh.logN ((sentOf T others).toList.map (·.shape)) :=
  seatP_of_sent ft roots S _ Bk _ (sentOf T others) D.lay sh h.places rfl
    (fun i => by
      unfold Taken.stA
      rw [admitted_shape]) h1 ht hmain hmask

/-! ## By hand: the plain reading keeps what is public of the book -/

theorem modify_keeps (B : TreeBook) (t : Nat) :
    BookKeeps B { B with trees := B.trees.modify t fun x => { x with lists := x.lists + 1 } } := by
  refine ⟨fun _ _ h => h, fun t' T h => ?_⟩
  show ∃ T', (B.trees.modify t fun x => { x with lists := x.lists + 1 })[t']? = some T' ∧ _
  rw [Array.getElem?_modify, h]
  by_cases e : t = t'
  · exact ⟨{ T with lists := T.lists + 1 }, by simp [e], rfl, rfl, rfl⟩
  · exact ⟨T, by simp [e], rfl, rfl, rfl⟩

theorem openOne_keeps (S : Statement) (ft : Nat) (pos : Positions) (B0 : TreeBook) (t : Nat)
    (s s' : TreeBook × List Tw.L9.Col × Array (Nat × Array Nat × Array (Array F)))
    (h : Tw.L9.openOne S ft pos B0 t s = .ok s') : BookKeeps s.1 s'.1 := by
  unfold Tw.L9.openOne at h
  split at h
  · dsimp only at h
    repeat' split at h
    all_goals first
      | (cases h; exact modify_keeps _ _)
      | cases h
  · cases h

theorem foldlM_keeps' {α σ : Type} (R : σ → σ → Prop) (hr : ∀ s, R s s)
    (ht : ∀ a b c, R a b → R b c → R a c) (f : σ → α → Except String σ)
    (hf : ∀ s a s', f s a = .ok s' → R s s') : ∀ (l : List α) (s s' : σ),
    l.foldlM f s = .ok s' → R s s'
  | [], s, s', h => by cases h; exact hr s
  | a :: l, s, s', h => by
    rw [List.foldlM_cons] at h
    obtain ⟨s1, h1, h2⟩ := H2K.FoldLaw.bind_ok h
    exact ht _ _ _ (hf _ _ _ h1) (foldlM_keeps' R hr ht f hf l s1 s' h2)

theorem readOld_keeps (i : Tw.L9.SwIn) (pos : Positions) (B : TreeBook) (left : List Tw.L9.Col)
    (ys : Array E) (h : Tw.L9.readOld i pos = .ok (B, left, ys)) : BookKeeps i.book B := by
  unfold Tw.L9.readOld at h
  dsimp only at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · rename_i B' left' cols' hfold
        split at h
        · cases h
        · split at h
          · cases h
          · cases h
            exact foldlM_keeps'
              (fun (a b : TreeBook × List Tw.L9.Col × Array (Nat × Array Nat × Array (Array F))) =>
                BookKeeps a.1 b.1) (fun _ => BookKeeps.refl _)
              (fun _ _ _ h1 h2 => h1.trans h2) _
              (fun s a s' hs => openOne_keeps _ _ _ _ _ _ _ hs) _ _ _ hfold

/-- The book behind the sending keeps the book in front. -/
theorem Did.bookKeepsB (_h : Did ft cols old T gp others S Bk roots S' Bk' out row lay theta D) :
    BookKeeps Bk (bookSentP ft roots S Bk (sentOf T others) D.lay) :=
  bookSentP_keeps ft roots S Bk _ D.lay

/-- The book behind the switch keeps the book behind the sending. -/
theorem Did.bookKeepsR (h : Did ft cols old T gp others S Bk roots S' Bk' out row lay theta D) :
    BookKeeps (bookSentP ft roots S Bk (sentOf T others) D.lay) Bk' := by
  obtain ⟨i, left, _, hb, _, _, _, hr⟩ := h.read
  rw [← hb]
  exact readOld_keeps i _ _ _ _ hr

/-- The same as seatB, behind the switch. -/
theorem Did.seat (h : Did ft cols old T gp others S Bk roots S' Bk' out row lay theta D)
    (sh : TreeShape) (h1 : D.lay.shapes = #[sh])
    (ht : ∀ i, i < (sentOf T others).size → D.lay.tree.getD i 0 = 0 ∧ D.lay.part.getD i 0 = i)
    (hmain : sh.mainSymbols
      = (((sentOf T others).toList.map (·.shape)).map fun s => s.mainRows * s.mainDeg).toArray)
    (hmask : sh.maskSymbols
      = (((sentOf T others).toList.map (·.shape)).map fun s => s.maskRows * 3).toArray) :
    SeatP S' Bk' ((List.range (sentOf T others).size).map (· + S.oracles.size))
      (ft + roots) sh.logN ((sentOf T others).toList.map (·.shape)) := by
  refine (h.seatB sh h1 ht hmain hmask).keeps h.bookKeepsR (shapesKeep_of_map _ _ fun i => ?_)
  rw [h.shape_at i]
  unfold Taken.stA
  rw [admitted_shape]

/-- The mask that came with the switch's message has the number after the new oracle message's. -/
theorem did_mask (h : Did ft cols old T gp others S Bk roots S' Bk' out row lay theta D)
    (ho : others.size = 1) : out.others[0]? = some (S.oracles.size + 1) := by
  rw [h.riders, ho]
  simp

end

end H2K.Sw
