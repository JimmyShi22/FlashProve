-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K13/GuardsLeft.lean: kind K13, the members' batching: THE THREE GUARDS
THAT GuardsAtM3.lean OF THIS FOLDER LEAVES (`K13GuardsLeft`: count, fit, form), CUT INTO CLAUSES,
AND SHOWN FROM: the tie of the filler's pile to the state's (`RowsTie`, ExchangeAtM3.lean) (the
filler: the parameter `pile`: the honest side's own account of the rows on the pile, made of the
instance and of the challenges heard); a test with code on the filler's pile; the guard count
itself, under the thread; and two clauses on the mask entries. SO OF THE THREE IT SHOWS TWO, fit AND
form: count IS A PREMISE. Definitions with code; statements with their proofs: general in the
thread's parameters, and at the library's own.

Why. The three guards read of the state's pile: how many rows there are; of each row its column
point's length, whether it has a weight, each weight's number of variables; and which message its
mask entries are of. All but the last are functions of what `rowReads`
(Johnson/Desc/K13/Honest/PileReads.lean) keeps of a row: its weights and its column point. `RowsTie`
says that the filler's pile and the state's agree in just that. So what the guards ask of the
state's pile can be asked of the filler's, which is made of public data and challenges.
Main names:
  `pileFits P l`: **the test**, on a list of rows' weights and column points.
  `indexShapeFits`, `pileMasksFit`: the two clauses of `memberRowsFit` (OnBytes/Iop/Lin.lean) that
    read more: the index masks' message's shape; which message the rows' mask entries are of.
  `count_of_pileFits`, `form_of_pileFits`, `fit_of_pileFits`: the three guards from these.
  `MasksOwed`: the two clauses as one structure. `guardsLeft_of_reads`: `K13GuardsLeft` at a state.
  `k13_guardsLeft_of_rows`: **under the thread, at every thread's parameters**: from `RowsTie`,
    `ReplyRides`, the test at the filler's pile WHERE THE FILLER YIELDS A ROW, the guard count under
    the thread, that the plan expects a row, and `MasksOwed` under the thread.
  `fillerI`, `fillerI_meets`, `fillerI_fails_outright`: a synthetic filler that yields no row where
    the challenges are too few: it meets that premise, and fails it asked at every list outright.
  `k13_pileMasks_at`: at the library's own parameters the clause on the rows' mask entries holds
    under the thread at border 355: by `LPFK9.masks_reached` (Johnson/LPFK9R/ThreeK13Fields.lean).
  `k13_guardsLeft_at`: **there: the three guards under the thread: of the two clauses on the mask
    entries the one on the message's shape stays a premise** (hShape); so do hW (`RowsTie`), hY
    (`ReplyRides`), hfill (the test at the filler's pile) and hcount (the guard count).
  `k13_accepted_rows_at`: **so `Accepted` at 355, at every `fall`**, from h, the kind's half's
    place, `RowsTie`, `ReplyRides`, the test at the filler's pile, the guard count and that one
    clause.
  `guardsLeft_instance`, and nineteen `#guard` lines: at the synthetic state and pile of
    Johnson/Desc/K13/Honest/ReadyToy.lean each of the three tests accepts; each of the six
    clauses of the test on the pile, each of the four on the message's shape, and the one on the
    rows' mask entries rejects at an altered value.

What is not claimed. That a filler's pile passes the test. That any filler's pile passes the test
where it yields a row, but the synthetic one's here. `RowsTie`, `ReplyRides` and the guard count at
any thread. The clause on the index masks' message's shape under the thread: IndexShapeAtM3.lean of
this folder shows it at the library's own parameters. The converses: the guards are not shown to
give the test (form asks one number of variables for all weights, not the plan's). Nothing on any
property.
-/
import Johnson.Desc.ProofFile.Honest.K13.GuardsAtM3
import Johnson.Desc.ProofFile.Honest.K13.ExchangeAtM3
import Johnson.LPFK9R.ThreeK13Fields
import Johnson.Desc.K13.Own
import Johnson.Desc.K13.Honest.ReadyToy

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K13
open OnBytes OnBytes.Params
open VerifiableInference.Desc (Chain Strs)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K13 (Where)
open VerifiableInference.Desc.K13.Honest (rowReads)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (Letters lettersAt Script WtF)

/-! ## 1 The three guards, cut into clauses -/

/-- **A test with code on the rows' weights and column points**: there are the plan's number of
rows, and at least one; the matrix has more than one column; each row has kCol coordinates, a
weight, and kRow variables in each weight. IT FOLLOWS THE LIBRARY's OWN CUT OF THE TWO TESTS
(Johnson/Desc/K13/Own.lean: `pileOnTable` with `rowOnTable`, `pileForm` with `rowForm`;
`pileOnTable_agrees`, `pileForm_agrees`, OwnLaws.lean): the clauses of these that read a row's point
and weights; it stays a definition of its own since it is said of what `rowReads` keeps of a row,
not of a row. -/
def pileFits (P : Where) (l : List (List Tensor × List E)) : Bool :=
  l.length == P.rows && !l.isEmpty && decide (1 ≤ P.lin.kCol) &&
    l.all fun q => q.2.length == P.lin.kCol && !q.1.isEmpty && q.1.all (·.vars == P.lin.kRow)

/-- The clause of `memberRowsFit` on the index masks' message's shape: there is such a message, and
it passes the library's own test `K13.Own.masksMessageFits` (Johnson/Desc/K13/Own.lean): no main
row, a mask row, an answer, the mask code of the request's own group. -/
def indexShapeFits (st : Statement) (L : LinShape) (im : Nat) : Bool :=
  match st.oracles[im]? with
  | none => false
  | some x => VerifiableInference.Desc.K13.Own.masksMessageFits x.shape L

/-- The clause of `memberRowsFit` on the rows' mask entries: each is the index masks' message's. It
is the body of the library's `K13.pileMasksC` (Johnson/Desc/K13/PubK13.lean), which is said of a
state's rows, at a given number and a given pile. -/
def pileMasksFit (im : Nat) (pending : List TensorRow) : Bool :=
  pending.all fun r => r.masks.all fun m => m.1.oracle == im

/-- What the test says of one row. -/
theorem pileFits_row {P : Where} {pending : List TensorRow}
    (h : pileFits P (pending.map rowReads) = true) {r : TensorRow} (hr : r ∈ pending) :
    r.psi.length = P.lin.kCol ∧ r.g.isEmpty = false ∧ ∀ t ∈ r.g, t.vars = P.lin.kRow := by
  unfold pileFits at h
  simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨a, b⟩, c⟩ := h.2 (rowReads r) (List.mem_map_of_mem hr)
  exact ⟨a, b, c⟩

/-- **The guard "count"** is a clause of the test. -/
theorem count_of_pileFits {P : Where} {pending : List TensorRow}
    (h : pileFits P (pending.map rowReads) = true) : pending.length = P.rows := by
  unfold pileFits at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.length_map] at h
  exact h.1.1.1

/-- **The guard "form"** follows from the test. -/
theorem form_of_pileFits {P : Where} {pending : List TensorRow}
    (h : pileFits P (pending.map rowReads) = true) : Batt.fits P.lin.kCol pending = true := by
  have hk : 1 ≤ P.lin.kCol := by
    unfold pileFits at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.1.2
  cases pending with
  | nil =>
    unfold pileFits at h
    simp at h
  | cons r l =>
    obtain ⟨-, hr2, hr3⟩ := pileFits_row h (List.mem_cons_self ..)
    have hh : r.g.head?.map Tensor.vars = some P.lin.kRow := by
      cases hg : r.g with
      | nil =>
        rw [hg] at hr2
        cases hr2
      | cons t _ =>
        show some t.vars = _
        rw [hr3 t (by rw [hg]; exact List.mem_cons_self ..)]
    show (decide (1 ≤ P.lin.kCol) && (r :: l).all fun s =>
      s.psi.length == P.lin.kCol && !s.g.isEmpty &&
        s.g.all fun t => some t.vars == r.g.head?.map Tensor.vars) = true
    rw [hh, Bool.and_eq_true]
    refine ⟨decide_eq_true hk, List.all_eq_true.2 fun s hs => ?_⟩
    obtain ⟨a, b, c⟩ := pileFits_row h hs
    rw [a, b]
    simp only [beq_self_eq_true, Bool.not_false, Bool.and_self, Bool.true_and]
    exact List.all_eq_true.2 fun t ht => by rw [c t ht]; exact beq_self_eq_true _

/-- **The guard "fit"** follows from the test and the two clauses on the mask entries' message. -/
theorem fit_of_pileFits {P : Where} {st : Statement} {im : Nat} {pending : List TensorRow}
    (h : pileFits P (pending.map rowReads) = true) (hs : indexShapeFits st P.lin im = true)
    (hm : pileMasksFit im pending = true) : memberRowsFit st P.lin im pending = true := by
  have hk : 0 < P.lin.kCol := by
    unfold pileFits at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.1.2
  have hne : pending.isEmpty = false := by
    unfold pileFits at h
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_map] at h
    exact h.1.1.2
  unfold memberRowsFit
  unfold indexShapeFits at hs
  cases hx : st.oracles[im]? with
  | none =>
    rw [hx] at hs
    cases hs
  | some x =>
    rw [hx] at hs
    show (x.shape.mainRows == 0 && decide (0 < x.shape.maskRows) && decide (0 < x.shape.answers) &&
      x.shape.maskCode == P.lin.ownMaskCode && !pending.isEmpty && decide (0 < P.lin.kCol) &&
      pending.all fun r => (r.masks.all fun m => m.1.oracle == im) &&
        r.psi.length == P.lin.kCol && r.g.all (·.vars == P.lin.kRow)) = true
    have hs' : (x.shape.mainRows == 0 && decide (0 < x.shape.maskRows) &&
      decide (0 < x.shape.answers) && x.shape.maskCode == P.lin.ownMaskCode) = true := hs
    rw [hs', hne, decide_eq_true hk]
    simp only [Bool.not_false, Bool.and_self, Bool.true_and]
    refine List.all_eq_true.2 fun r hr => ?_
    obtain ⟨a, -, c⟩ := pileFits_row h hr
    rw [List.all_eq_true.1 hm r hr, a]
    simp only [beq_self_eq_true, Bool.and_self, Bool.true_and]
    exact List.all_eq_true.2 fun t ht => by rw [c t ht]; exact beq_self_eq_true _

/-- **What is still owed on the mask entries**: two clauses on the state. -/
structure MasksOwed (P : Where) (s : S) : Prop where
  shape : indexShapeFits s.st P.lin s.out.indexMasks = true
  masks : pileMasksFit s.out.indexMasks s.out.pending = true

/-- **The three guards that were left**, from the test on the pile's weights and column points and
the two clauses on the mask entries. -/
theorem guardsLeft_of_reads {P : Where} {s : S}
    (h : pileFits P (s.out.pending.map rowReads) = true) (hM : MasksOwed P s) :
    K13GuardsLeft P s :=
  ⟨count_of_pileFits h, fit_of_pileFits h hM.shape hM.masks, form_of_pileFits h⟩

/-! ## 2 Under the thread, at every thread's parameters -/

section
variable {Bk : ProverCoinCounts} {Cl W₀ Rc Xi Tr X Pp Cells Tok M : Type}
  (L : Letters Bk Cl W₀ Rc Xi Tr X Pp Cells Tok M)

/-- **The three guards under the thread.** hW: the filler's pile agrees with the state's in the
rows' weights and column points. hY: the thread gives the reply. hfill: WHERE THE FILLER YIELDS A
ROW AT ALL, ITS PILE PASSES THE TEST: AT EVERY INSTANCE AND ALL CHALLENGES: the test has code; the
premise is a sentence over all instances and all lists of challenges: A LAW TO BE SHOWN OF A
FILLER's TEXT, NO TEST THAT CAN BE RUN. (Asked at every list of challenges outright it would be
false of a filler that yields no row where the challenges are too few: the test rejects the empty
list.) hcount: the guard "count" under the thread; hpos: the plan expects a row: with hW they give
that the filler's pile is not empty there. hM: what is still owed on the mask entries. -/
theorem k13_guardsLeft_of_rows {b : Nat} {pile : PileOf Xi} {asked : Xi → E} {P : Where}
    (hW : RowsTie L b pile asked) (hY : ReplyRides L b asked)
    (hfill : ∀ x heard, pile x heard ≠ [] → pileFits P ((pile x heard).map rowReads) = true)
    (hcount : ∀ k s m En, Thr L.thread b k s m En → s.out.pending.length = P.rows)
    (hpos : 0 < P.rows) (hM : ∀ k s m En, Thr L.thread b k s m En → MasksOwed P s) :
    ∀ k s m En, Thr L.thread b k s m En → K13GuardsLeft P s := fun k s m En hT => by
  have e := hW k s m En hT (hY k s m En hT) ⟨[], [], [], none⟩
  have hl : (pile m.st.input.x (m.st.heard ++ [⟨[], [], [], none⟩])).length = P.rows := by
    have q := congrArg List.length e
    rw [List.length_map, List.length_map] at q
    exact q.trans (hcount k s m En hT)
  have hne : pile m.st.input.x (m.st.heard ++ [⟨[], [], [], none⟩]) ≠ [] := fun h0 => by
    rw [h0] at hl
    exact absurd hl.symm (Nat.ne_of_gt hpos)
  exact guardsLeft_of_reads (e ▸ hfill _ _ hne) (hM k s m En hT)

end

/-! ## 3 At the library's own parameters -/

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Tr X : Type}
  (hs : List (Placed (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X))
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (stored : Local W₀ Rc ProofFile.Inst Tr → Nat → Nat → Option (List UInt64))
  (ans : Nat → Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (test : Nat → TS → Option String)
  (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ : Nat)
  (valid : Local W₀ Rc ProofFile.Inst Tr → Prop) (rides : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
  (keeps : Nat → TS → TS → Prop)

/-- **The clause on the rows' mask entries, under the thread at border 355**: by the library's fact
at reached states. -/
theorem k13_pileMasks_at {k : Coins Bk} {s : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {En : Env}
    (hT : Thr (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).thread 355 k s
      m En) :
    pileMasksFit s.out.indexMasks s.out.pending = true := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have q := LPFK9.masks_reached h.scope h.reads O 355 _
    (k13_reach_at h hs Q stored ans test carryX item n₁ n₂ valid rides keeps hT)
  obtain ⟨f, hf⟩ :=
    (k13_guard_form_at h hs Q stored ans test carryX item n₁ n₂ valid rides keeps hT).2.1
  have e : s.rows = s.out.pending := by
    unfold VerifiableInference.Desc.First.S.rows
    rw [hf]
  unfold VerifiableInference.Desc.K13.pileMasksC at q
  show (s.out.pending.all fun r => r.masks.all fun m => m.1.oracle == s.out.indexMasks) = true
  rw [← e]
  exact q

/-- **The three guards under the thread at border 355**: of the two clauses on the mask entries the
one on the message's shape stays a premise; that the plan expects a row is shown (`m3_rows`). -/
theorem k13_guardsLeft_at {pile : PileOf ProofFile.Inst} {asked : ProofFile.Inst → E}
    (hW : RowsTie (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps) 355 pile
      asked)
    (hY : ReplyRides (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps) 355
      asked)
    (hfill : ∀ x heard, pile x heard ≠ [] →
      pileFits h.𝔇.P13 ((pile x heard).map rowReads) = true)
    (hcount : ∀ k s m En,
      Thr (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).thread 355 k s
        m En →
      s.out.pending.length = h.𝔇.P13.rows)
    (hShape : ∀ k s m En,
      Thr (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).thread 355 k s
        m En →
      indexShapeFits s.st h.𝔇.P13.lin s.out.indexMasks = true) :
    ∀ k s m En,
      Thr (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).thread 355 k s
        m En → K13GuardsLeft h.𝔇.P13 s :=
  k13_guardsLeft_of_rows _ hW hY hfill hcount (by rw [m3_rows h]; decide) fun k s m En hT =>
    ⟨hShape k s m En hT,
      k13_pileMasks_at h hs Q stored ans test carryX item n₁ n₂ valid rides keeps hT⟩

/-- **WHAT ACCEPTANCE COSTS THEN, at every `fall`**: h; hH: the kind's half's place among the
thread's halves; the tie of the filler's pile to the state's; that the thread gives the reply; the
test at the filler's pile where it yields a row; the guard "count" under the thread; the clause on
the index masks' message's shape. -/
theorem k13_accepted_rows_at {weights : W₀ → Weights} {pile : PileOf ProofFile.Inst}
    {asked : ProofFile.Inst → E}
    (hH : ∀ blk, cF.blocksInOrder[355]? = some blk →
      (hs.find? fun g => g.place == blk.place) = some (proverSideOfClaimCombination weights pile h.𝔇.P13))
    (hW : RowsTie (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps) 355 pile
      asked)
    (hY : ReplyRides (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps) 355
      asked)
    (hfill : ∀ x heard, pile x heard ≠ [] →
      pileFits h.𝔇.P13 ((pile x heard).map rowReads) = true)
    (hcount : ∀ k s m En,
      Thr (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).thread 355 k s
        m En →
      s.out.pending.length = h.𝔇.P13.rows)
    (hShape : ∀ k s m En,
      Thr (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).thread 355 k s
        m En →
      indexShapeFits s.st h.𝔇.P13.lin s.out.indexMasks = true)
    (fall : Nat → TS → List Fmt.Drawn → Option String) :
    Accepted (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).thread fall
      355 :=
  k13_accepted_left_at h hs Q stored ans test carryX item n₁ n₂ valid rides keeps hH hY
    (k13_guardsLeft_at h hs Q stored ans test carryX item n₁ n₂ valid rides keeps hW hY hfill
      hcount hShape) fall

/-! ## 4 The three tests at a synthetic pile: each accepts, and each can reject -/

section
open VerifiableInference.Desc.K13.Honest.ReadyToy (P pile0 stateAt)

/-- The lawful state's statement with the shape of its message number 0 altered. -/
def shapeTurned (f : OracleShape → OracleShape) : Statement :=
  { (stateAt pile0).st with
    oracles := (stateAt pile0).st.oracles.modify 0 fun x => { x with shape := f x.shape } }

/-- The lawful shape of the test on the table with the matrix's columns cut to one. -/
def oneColumn : LinShape :=
  { P.lin with kLo := 0, fold := { P.lin.fold with index := { P.lin.fold.index with v := 0 } } }

-- the test on the rows' weights and column points accepts at the lawful pile
#guard pileFits P (pile0.map rowReads)
-- it rejects: a row too few; a row without a weight; a coordinate too few; a weight of one variable
#guard !pileFits P ((pile0.drop 1).map rowReads)
#guard !pileFits P ((pile0.map fun r => { r with g := [] }).map rowReads)
#guard !pileFits P ((pile0.map fun r => { r with psi := r.psi.drop 1 }).map rowReads)
#guard !pileFits P ((pile0.map fun r => { r with g := [Tensor.eq [oneE]] }).map rowReads)
-- it rejects the empty list at the lawful plan
#guard !pileFits P []
-- its two other clauses, each at values at which that clause alone fails: no row, at a plan of no
-- rows; a matrix of one column, at rows without a coordinate
#guard !pileFits { P with rows := 0 } []
#guard !pileFits { P with lin := oneColumn }
  ((pile0.map fun r => { r with psi := [] }).map rowReads)
#guard oneColumn.kCol == 0 && oneColumn.kRow == P.lin.kRow
-- it reads no target and no mask form
#guard pileFits P ((pile0.map fun r => { r with target := oneE, masks := [] }).map rowReads)
-- the two clauses on the mask entries accept at the lawful state, and reject at another number
#guard indexShapeFits (stateAt pile0).st P.lin (stateAt pile0).out.indexMasks
#guard !indexShapeFits (stateAt pile0).st P.lin ((stateAt pile0).out.indexMasks + 1)
-- (there is no message of that number.) EACH OF ITS FOUR CLAUSES ON THE SHAPE CAN REJECT: a main
-- row; no mask row; no answer; another mask code
#guard !indexShapeFits (shapeTurned fun o => { o with mainRows := 1 }) P.lin 0
#guard !indexShapeFits (shapeTurned fun o => { o with maskRows := 0 }) P.lin 0
#guard !indexShapeFits (shapeTurned fun o => { o with answers := 0 }) P.lin 0
#guard !indexShapeFits (shapeTurned fun o => { o with maskCode := o.maskCode + 1 }) P.lin 0
#guard (stateAt pile0).out.indexMasks == 0 && indexShapeFits (shapeTurned id) P.lin 0
#guard pileMasksFit (stateAt pile0).out.indexMasks (stateAt pile0).out.pending
#guard !pileMasksFit ((stateAt pile0).out.indexMasks + 1) (stateAt pile0).out.pending

/-- A synthetic filler of the sort "all or nothing": no row where fewer than two challenges were
heard; the lawful pile elsewhere. -/
def fillerI : PileOf Unit := fun _ heard => if heard.length < 2 then [] else pile0

set_option maxRecDepth 100000 in
/-- **It meets the premise hfill of `k13_guardsLeft_of_rows`**: where it yields a row its pile
passes the test. -/
theorem fillerI_meets : ∀ x heard, fillerI x heard ≠ [] →
    pileFits P ((fillerI x heard).map rowReads) = true := by
  intro x heard hne
  by_cases hh : heard.length < 2
  · exact absurd (if_pos hh) hne
  · have e : fillerI x heard = pile0 := if_neg hh
    rw [e]
    decide +kernel

/-- **It fails the same sentence asked at every list of challenges outright**: at no challenge it
yields no row, and the test rejects the empty list. -/
theorem fillerI_fails_outright :
    ¬ ∀ x heard, pileFits P ((fillerI x heard).map rowReads) = true := fun hall => by
  have q := hall () []
  have e : fillerI () [] = [] := rfl
  rw [e] at q
  exact absurd q (by decide)

set_option maxRecDepth 100000 in
/-- **The premises of `guardsLeft_of_reads` are met together** at the synthetic state. -/
theorem guardsLeft_instance : K13GuardsLeft P (stateAt pile0) :=
  guardsLeft_of_reads (by decide +kernel) ⟨by decide +kernel, by decide +kernel⟩

end

end ProofFile.Honest.K13

#print axioms ProofFile.Honest.K13.pileFits_row
#print axioms ProofFile.Honest.K13.count_of_pileFits
#print axioms ProofFile.Honest.K13.form_of_pileFits
#print axioms ProofFile.Honest.K13.fit_of_pileFits
#print axioms ProofFile.Honest.K13.guardsLeft_of_reads
#print axioms ProofFile.Honest.K13.k13_guardsLeft_of_rows
#print axioms ProofFile.Honest.K13.k13_pileMasks_at
#print axioms ProofFile.Honest.K13.k13_guardsLeft_at
#print axioms ProofFile.Honest.K13.guardsLeft_instance
#print axioms ProofFile.Honest.K13.k13_accepted_rows_at
#print axioms ProofFile.Honest.K13.fillerI_meets
#print axioms ProofFile.Honest.K13.fillerI_fails_outright
