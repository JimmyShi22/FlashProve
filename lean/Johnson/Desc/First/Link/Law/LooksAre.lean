-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/LooksAre.lean: «THE LEDGER's ARRAYS HAVE THE PLAN's SHAPES, ALONG THE
LINK»: A PROPERTY OF A LEDGER BESIDE `GoesOn` (Johnson/Desc/First/Batch/Law/FitsAtS.lean), WHICH
CARRIES THE ARRAYS' LOOKS (`goesOn_looks`). Definitions and theorems. No text already in the library turns.

Why. Two laws on the batching ask of the ledger's arrays more than their widths: the public test
`totalIn` (Johnson/Desc/First/Batch/FormsIn.lean) ranges over the ledger's arrays and reads each
one's number of rows; the approximate range proof's run of claims wants each table's array to be of
the kind "table", with one row and a first virtual row. An array is BUILT by the planner's two
routines alone (`t2AddN`, `t2AddP`, OnBytes/Model/Trees.lean), which read no proof; every later
writer turns its virtual rows' fields or its mark "committed".
What is said.
  `look X`: an array's kind, number of rows R, number of columns K, number of virtual rows: the
    `shapeAt` (OnBytes/Tie/Pv/Tail/EndCoef.lean) of one array (`shapeAt_look`).
    `LooksAre sh F`: the ledger F's arrays have, in order, just the looks sh.
  MADE. `looks_laid`, `looks_start`: the ledger from which a sub-proof starts
    (`startFork`, Johnson/Desc/First/Walk/FirstQuiet.lean) has the looks of the arrays X.Fp of the
    LETTER X; that X is a link's public structure off the plan is said where X is laid
    (`frames_keep`, LooksSeated.lean; `okHead_at`, Johnson/LPFK9R/LooksSeat.lean).
  KEPT. `looks_trees`, `looks_map`, `looks_frame`: by whatever leaves the arrays; their looks; all
    but the weights' values (`treesFrame`). `looks_rests`: **the five closure rules `ForkRests`**
    (Johnson/Desc/First/Link/Law/SizedRides.lean): so by `rests_fork` it passes an accepting call of
    each of the nine known runs (`looks_runs`); `looks_puts`: a lookup's run, where it writes a
    ledger with the same arrays. `rests_and`: two properties that rest, together. `looks_fill`,
    `looks_draw`: the batching's draw. `looks_add`: the adding of any list of claims.
    `looks_batch`, `looks_behind`, `looks_shut`: **an accepting step of the batching, of the frame's
    sub-protocol behind it, of the shutting.**
  SPENT. `looks_size`, `looks_get`: the number of arrays; one array's look. `unitLook sh t`: A TEST
    ON sh: number t is of the kind "table", has one row, and a virtual row. `shape_at`,
    `shape_of_looks`, `shape_letter`: **a form of the fourth premise of `fuEq_full`
    (Johnson/Desc/First/Link/Law/FullEq.lean); that theorem's own fourth premise is
    `okLooks`.** `ledgerIn_of_four`,
    `totalIn_of_four`, `totalIn_of_looks`: **the public test `totalIn` from its four shares**, the
    third and fourth ranging over sh's length.
  A MEMBER AND NEGATIVE TESTS. `looks_toy`, `looks_toy_no`, `unit_toy`, `unit_toy_no`.
Limits. (1) That a link's OTHER sub-protocols between the laying of its ledger and the batching
(the sendings, the lookups, the callers' own rounds) keep the property is not shown HERE: it is
shown in the files Looks*.lean beside this one. (2) The runs'
share at the batching and behind it is a premise, as in SizedRides.lean; at the nine known runs it
is `rests_fork`. (3) `totalIn`'s other shares (the sizes on slots; the mask row's seat; each array
is there; each virtual row has a weight a row) are premises. (4) That `unitLook` says yes at a
plan's looks is evaluated at the small configuration alone
(LooksAtSmall.lean [not in this library]): no theorem.
(5) `shape_letter` COUNTS FOR NOTHING: its debt hL
is its conclusion over a wider range: it begs. hL ranges
over ALL states t with `Fx9 … q t` and `FullAt nU t`, not over states on a run from a laid ledger:
none of the kept-lemmas of this file reaches it. Were "goes on" not to carry the looks
(the arrays' widths alone), hL could be paid, at a letter ψ that does not see the ledger, only
where no such state had a read at a table's array. In this library "goes on" carries the looks
(Johnson/Desc/First/Batch/Law/FitsAtS.lean: `goesOn_looks`), and what this theorem ends in is had
otherwise inside `fuEq_full`'s proof: from a clause of Ok on the snapshot's ledger (`okLooks`: a
premise of `fuEq_full`), by `shape_at`: not through this theorem.
The implication is true as typed. Nothing on soundness.
Words. "The ledger": the structure Fork. "The verifier's state": what the verifier carries from one
sub-protocol to the next.
-/
import Johnson.Desc.First.Link.Law.SizedRides
import Johnson.Desc.First.Link.Law.PayLayers
import Johnson.Desc.First.Walk.FirstQuiet
import Johnson.Desc.First.Batch.FormsIn
import OnBytes.Tie.Pv.Tail.EndAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open OnBytes.PscRun (Later Sized)
open OnBytes.Model.Road (SameSlots)
open OnBytes.Desc.First.K4 (Core hideRun_core paid_core)
open OnBytes.Tie.Pv.Tail.Port (readsList segsOf uOf hasRow)
open VerifiableInference.Desc.First.TailClaims.Law (eq_side coefBody_inv)
open VerifiableInference.Desc.First.TailClaims (equations coefBody)
open VerifiableInference.Desc.K9 (atS Where shut drawn drawnClean ledgerIn totalIn maskSeat arrayIn)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.JoinAtBlocks
open VerifiableInference.Desc.PhiAll
open Johnson.Desc.First.Walk (LinkPub startFork emptySlots weightsAtZero)

/-! ## 1 The property -/

/-- It is the reading of one array's kind and sizes (`shapeAt`,
OnBytes/Tie/Pv/Tail/EndCoef.lean). -/
theorem shapeAt_look (F : Fork) (t : ℕ) :
    OnBytes.Tie.Pv.Tail.Port.shapeAt F t = look (F.trees.getD t {}) := rfl

/-- **The ledger's arrays have, in order, just these looks.** -/
def LooksAre (sh : List Look) (F : Fork) : Prop := F.trees.toList.map look = sh

section
variable {sh : List Look}

theorem looks_trees {F G : Fork} (h : G.trees = F.trees) (hF : LooksAre sh F) : LooksAre sh G := by
  unfold LooksAre at hF ⊢
  rw [h]
  exact hF

theorem looks_map {F G : Fork} (h : G.trees.map look = F.trees.map look) (hF : LooksAre sh F) :
    LooksAre sh G := by
  unfold LooksAre at hF ⊢
  rw [← Array.toList_map, h, Array.toList_map]
  exact hF

/-- By whatever leaves all but the weights' values. -/
theorem looks_frame {F G : Fork} (h : treesFrame G.trees = treesFrame F.trees)
    (hF : LooksAre sh F) : LooksAre sh G := looks_map (looks_of_frame _ _ h) hF

end

/-! ## 2 Made -/

/-- The ledger that is laid off a list of arrays has their looks. -/
theorem looks_laid (F : Fork) (ns : ℕ) :
    LooksAre (F.trees.toList.map look) (emptySlots (weightsAtZero F) ns) := by
  unfold LooksAre emptySlots weightsAtZero
  simp only [Array.toList_map, List.map_map]
  exact List.map_congr_left fun T _ => look_rows_map T _

/-- **The ledger from which a sub-proof starts has the looks of the arrays X.Fp**, X a letter. -/
theorem looks_start (X : LinkPub) (ns : ℕ) :
    LooksAre (X.Fp.trees.toList.map look) (startFork X ns) := looks_laid X.Fp ns

/-! ## 3 Kept -/

/-- **The five closure rules.** -/
theorem looks_rests (sh : List Look) : ForkRests (LooksAre sh) where
  later _ _ hc _ := looks_trees hc.trees
  hide _ _ _ _ _ h := looks_trees (hideRun_core h).trees
  paid F i := looks_trees (paid_core F i).trees
  eq _ _ _ _ _ _ _ he := looks_trees (eq_side he).trees
  coef tl g F h := coefBody_inv (LooksAre sh)
    (fun r t' r' f hr => looks_map (by
      unfold HTailF2.onRow
      exact map_modify_same look (fun X => { X with rows := X.rows.modify r' f })
        (fun X => look_rows_modify X r' f) r.trees t') hr) tl g F h

/-- Two properties that rest, together. -/
theorem rests_and {P Q : Fork → Prop} (hP : ForkRests P) (hQ : ForkRests Q) :
    ForkRests fun F => P F ∧ Q F where
  later F G hc hl h := ⟨hP.later F G hc hl h.1, hQ.later F G hc hl h.2⟩
  hide F G a v k hr h := ⟨hP.hide F G a v k hr h.1, hQ.hide F G a v k hr h.2⟩
  paid F i h := ⟨hP.paid F i h.1, hQ.paid F i h.2⟩
  eq a b c F d F1 e he h := ⟨hP.eq a b c F d F1 e he h.1, hQ.eq a b c F d F1 e he h.2⟩
  coef tl g F h := ⟨hP.coef tl g F h.1, hQ.coef tl g F h.2⟩

/-- **So it passes an accepting call of each of the nine known runs.** -/
theorem looks_runs (sh : List Look) :
    RunRests fun e e₁ => HasFork (LooksAre sh) e → HasFork (LooksAre sh) e₁ :=
  rests_fork (looks_rests sh)

/-- **A lookup's run**: where an accepting call turns the state by a writing of a ledger with the
same arrays, the property passes. -/
theorem looks_puts {sh : List Look} {e e₁ : S}
    (h : ∀ F, e.fork? = some F → ∃ G : Fork, e₁ = e.putFork G ∧ G.trees = F.trees) :
    HasFork (LooksAre sh) e → HasFork (LooksAre sh) e₁ := by
  rintro ⟨F, hF, hl⟩
  obtain ⟨G, rfl, hG⟩ := h F hF
  exact ⟨G, fork_putFork e F hF G, looks_trees hG hl⟩

/-- The filling of the weights that are not yet there. -/
theorem looks_fill {sh : List Look} (F : Fork) (T : Tail2) (h : LooksAre sh F) :
    LooksAre sh (t2FillL F T) := looks_map (fold_looks _ _) h

/-- **The batching's draw.** -/
theorem looks_draw {sh : List Look} (rows : ℕ) (chi : E) (owed : Option ℕ) (used : ℕ)
    (L : LinkCtx) (F : Fork) (o : K9.Drawn) (h : drawnClean rows chi owed used L F = .ok o)
    (hF : LooksAre sh F) : LooksAre sh o.F := by
  unfold drawnClean at h
  obtain ⟨o', ho, h⟩ := ok_bind h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain rfl : o' = o := Except.ok.inj h
  unfold drawn at ho
  obtain ⟨_, _, ho⟩ := ok_bind ho
  obtain ⟨_, _, ho⟩ := ok_bind ho
  obtain ⟨_, _, ho⟩ := ok_bind ho
  obtain ⟨_, _, ho⟩ := ok_bind ho
  obtain ⟨_, _, ho⟩ := ok_bind ho
  rw [← Except.ok.inj ho]
  exact looks_trees (F := t2FillL F L.list) rfl (looks_fill F L.list hF)

/-- **The adding of any list of claims.** -/
theorem looks_add {sh : List Look} {F G : Fork} {l : List Claim} (hs : F.LS.size = F.ns)
    (h : addAll F l = some G) (hF : LooksAre sh F) : LooksAre sh G :=
  looks_frame (addAll_total Reading.gl ⟨fun _ => 0, fun _ _ _ => 0⟩ l F G hs h).2.2.2 hF

/-- The property that the batching's runs hand on. -/
abbrev SizedLooks (sh : List Look) (F : Fork) : Prop :=
  (Sized F ∧ F.LS.size = F.ns) ∧ LooksAre sh F

theorem sizedLooks_rests (sh : List Look) : ForkRests (SizedLooks sh) :=
  rests_and sizedLS_rests (looks_rests sh)

/-- **At the batching.** -/
theorem looks_batch (sh : List Look) (L : Link S Claim) (p : Where)
    (hb₁ : DrawMoves atS p [.add (claimsInBy L.each L.hear L.order)] L.batchB)
    (hk : ∀ o ∈ L.order, ∀ run, At L o run → ∀ n e c e₁, run n e = .ok (c, e₁) →
      HasFork (SizedLooks sh) e → HasFork (SizedLooks sh) e₁)
    (ft : ℕ) (s : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (s' : S) (k : ℕ)
    (h : L.batchB.step ft s rs cols = .ok (s', k)) (hs : ledgerOk s = true)
    (hl : HasFork (LooksAre sh) s) : HasFork (LooksAre sh) s' := by
  obtain ⟨r, x, a, o, cls, _, _, ha, hd, hy⟩ := hb₁ ft s rs cols s' k h
  obtain ⟨u, c, c', ⟨e, q, G, hg, hq, hadd, rfl⟩, ⟨rfl, _⟩, _⟩ := hy
  obtain ⟨F0, hF0, hS0⟩ := (ledgerOk_iff s).1 hs
  obtain rfl : F0 = a.F := Option.some.inj (hF0.symm.trans (fork_part s a ha))
  obtain ⟨F0', hF0', hl0⟩ := hl
  obtain rfl : F0' = a.F := Option.some.inj (hF0'.symm.trans (fork_part s a ha))
  obtain ⟨hsame, hLS⟩ := drawn_same _ _ _ _ _ _ _ hd
  have hls : a.F.LS.size = a.F.ns := (drawnClean_tests _ _ _ _ _ _ _ hd).2.2.2.2.2.2.1
  have h0 : HasFork (SizedLooks sh)
      (atS.set s { a with owed := o.owed, L := o.L, F := o.F }) :=
    ⟨o.F, fork_of_set s _ (by rw [ha]; rfl), ⟨sized_same hsame hS0, by
      rw [hLS, hsame.ns]; exact hls⟩, looks_draw _ _ _ _ _ _ _ hd hl0⟩
  have h1 : HasFork (SizedLooks sh) e :=
    gather_holds (HasFork (SizedLooks sh)) (fun _ => []) []
      (runsIn L.hear L.order)
      (fun r' hr' n e0 c0 e1 hr0 hx => by
        obtain ⟨o', ho', e'⟩ := List.mem_filterMap.1 hr'
        obtain ⟨run, hrun, rfl⟩ := Option.map_eq_some_iff.1 e'
        exact hk o' ho' run hrun n e0 c0 e1 hr0 hx) ([], _) (c, e)
      (fold_gstep L.each L.hear L.order ([], _) (c, e) hg) h0
  obtain ⟨F1, hF1, ⟨_, hL1⟩, hk1⟩ := h1
  obtain rfl : F1 = q.F := Option.some.inj (hF1.symm.trans (fork_part e q hq))
  exact ⟨G, fork_of_set e _ (by rw [hq]; rfl), looks_add hL1 hadd hk1⟩

/-- **At the frame's sub-protocol behind the batching.** -/
theorem looks_behind (sh : List Look) (L : Link S Claim)
    (hk : ∀ o ∈ L.orderAfter, ∀ run, AtAfter L o run → ∀ e e₁, run e = .ok e₁ →
      HasFork (LooksAre sh) e → HasFork (LooksAre sh) e₁)
    (ft : ℕ) (s : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (s' : S) (k : ℕ)
    (h : L.behindB.step ft s rs cols = .ok (s', k)) (hl : HasFork (LooksAre sh) s) :
    HasFork (LooksAre sh) s' := by
  obtain ⟨rs', gs, hd⟩ := step_decide L.behindB _ _ _ _ _ k h
  obtain ⟨cls, hy⟩ := (behind_isMoves atS L).dec _ _ _ _ hd
  obtain ⟨u, c, c', ⟨hq, _⟩, ⟨rfl, _⟩, _⟩ := hy
  exact ran_holds (HasFork (LooksAre sh)) L.hear L.orderAfter _ _
    (afterIn_ran L.hear L.orderAfter _ _ (Link.afterIn_of_runBehind hq))
    (fun o ho run hl x x₁ hr hx => hk o ho run hl x x₁ hr hx) hl

/-- **At the shutting.** -/
theorem looks_shut {Cl : Type} (sh : List Look) (pw : Where) (piece : ℕ) (b₅ : Block S Cl)
    (hb₅ : ∀ ft s rs cols x, b₅.step ft s rs cols = .ok x →
      (shut (Cl := Cl) pw piece).step ft s rs cols = .ok x)
    (ft : ℕ) (s : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (s' : S) (k : ℕ)
    (h : b₅.step ft s rs cols = .ok (s', k)) (hl : HasFork (LooksAre sh) s) :
    HasFork (LooksAre sh) s' := by
  obtain ⟨L, _, rfl⟩ := shut_inv pw piece _ _ _ _ _ k (hb₅ _ _ _ _ _ h)
  have e : (s.putLink (K9.closed L L.check.frame)).fork? = s.fork? := by
    obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
    cases here with
    | head x => by_cases ho : x.opened = true <;> simp [S.putLink, S.fork?, ho]
    | _ => rfl
  obtain ⟨G, hG, hP⟩ := hl
  exact ⟨G, e.trans hG, hP⟩

/-! ## 4 Spent -/

section
variable {sh : List Look}

/-- As many arrays as looks. -/
theorem looks_size {F : Fork} (h : LooksAre sh F) : F.trees.size = sh.length := by
  unfold LooksAre at h
  rw [← h]
  simp

/-- One array's look. -/
theorem looks_get {F : Fork} (h : LooksAre sh F) (t : ℕ) (x : Look) (hx : sh[t]? = some x) :
    t < F.trees.size ∧ look (F.trees.getD t {}) = x := by
  unfold LooksAre at h
  rw [← h, List.getElem?_map] at hx
  obtain ⟨X, hX, rfl⟩ := Option.map_eq_some_iff.1 hx
  rw [Array.getElem?_toList] at hX
  obtain ⟨ht, rfl⟩ := Array.getElem?_eq_some_iff.1 hX
  refine ⟨ht, ?_⟩
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem ht, Option.getD_some]

end

/-- **A test on the looks**: number t is of the kind "table", has one row, and a virtual row. -/
def unitLook (sh : List Look) (t : ℕ) : Bool :=
  match sh[t]? with
  | some x => x.1 == HKind.table && x.2.1 == 1 && decide (0 < x.2.2.2)
  | none => false

/-- What a yes gives at a ledger with these looks. -/
theorem shape_at {sh : List Look} {F : Fork} (h : LooksAre sh F) (t : ℕ)
    (hu : unitLook sh t = true) :
    hasRow F t 0 ∧ ((F.trees.getD t {}).kind == HKind.table) = true ∧
      (F.trees.getD t {}).R = 1 := by
  unfold unitLook at hu
  cases e : sh[t]? with
  | none =>
    rw [e] at hu
    exact nomatch hu
  | some x =>
    rw [e] at hu
    have hu' : (x.1 == HKind.table && x.2.1 == 1 && decide (0 < x.2.2.2)) = true := hu
    obtain ⟨ht, rfl⟩ := looks_get h t x e
    simp only [look, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hu'
    exact ⟨⟨ht, hu'.2⟩, by rw [hu'.1.1]; rfl, hu'.1.2⟩

/-- A read of the list is a read of one of the tables. -/
theorem reads_mem (tl : HTailF2) (funs : Array HFun) (x : HFun × ℕ)
    (hx : x ∈ readsList tl funs) : x.1 ∈ funs.toList := by
  unfold readsList at hx
  obtain ⟨mu, _, hx⟩ := List.mem_flatMap.1 hx
  obtain ⟨un, _, hx⟩ := List.mem_flatMap.1 hx
  obtain ⟨Fn, hFn, hx⟩ := List.mem_flatMap.1 hx
  unfold segsOf at hx
  split at hx
  · obtain ⟨sg, _, rfl⟩ := List.mem_map.1 hx
    exact hFn
  · exact nomatch hx

/-- **Each read's table's array has a first virtual row, is of the kind "table", has one row.** -/
theorem shape_of_looks {sh : List Look} {F : Fork} (ts : HTailF2) (funs : Array HFun)
    (h : LooksAre sh F) (hB : ∀ Fn ∈ funs.toList, unitLook sh (uOf ts Fn) = true) :
    ∀ x ∈ readsList ts funs, hasRow F (uOf ts x.1) 0 ∧
      ((F.trees.getD (uOf ts x.1) {}).kind == HKind.table) = true ∧
      (F.trees.getD (uOf ts x.1) {}).R = 1 :=
  fun x hx => shape_at h _ (hB x.1 (reads_mem ts funs x hx))

/-- **A FORM OF THE FOURTH PREMISE OF `fuEq_full`**, under one named debt:
at a full state that goes on from q the ledger has some looks at which the test says yes of every
table's array. IT COUNTS FOR NOTHING: see the file's Limit (5): the debt ranges over all such
states. -/
theorem shape_letter {β : Type} (u : HTailF2) (ψ : S → β) (Ok : Q β → Prop) (nU : Array ℕ)
    (hL : ∀ q t ts funs, Fx9 (phiAll u ψ) Ok q t → FullAt nU t → t.tl? = some ts →
      t.funs? = some funs → ∃ sh, HasFork (LooksAre sh) t ∧
        ∀ Fn ∈ funs.toList, unitLook sh (uOf ts Fn) = true) :
    ∀ q t b ts funs, Fx9 (phiAll u ψ) Ok q t → FullAt nU t → atS.get? t = some b →
      t.tl? = some ts → t.funs? = some funs → ∀ x ∈ readsList ts funs,
        hasRow b.F (uOf ts x.1) 0 ∧
          ((b.F.trees.getD (uOf ts x.1) {}).kind == HKind.table) = true ∧
          (b.F.trees.getD (uOf ts x.1) {}).R = 1 := by
  intro q t b ts funs hf hfull hb hts hfu
  obtain ⟨sh, ⟨G, hG, hl⟩, hB⟩ := hL q t ts funs hf hfull hts hfu
  obtain rfl : G = b.F := Option.some.inj (hG.symm.trans (fork_part t b hb))
  exact shape_of_looks ts funs hl hB

/-- **The test on the ledger from its four shares.** -/
theorem ledgerIn_of_four (own : List (ℕ × ℕ)) (a : K9.Part)
    (t1 : a.F.LS.size = a.F.ns ∧ a.F.vp.size = a.F.ns ∧ a.F.mf.size = a.F.ns)
    (t2 : (maskSeat own a).isSome = true)
    (t3 : ∀ t, t < a.F.trees.size → (arrayIn own a t).isSome = true)
    (t4 : ∀ t, t < a.F.trees.size → ((a.F.trees.getD t {}).rows.all fun R =>
      R.coef.size == (a.F.trees.getD t {}).R) = true) : ledgerIn own a = true := by
  unfold ledgerIn
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range]
  exact ⟨⟨⟨⟨t1.1, t1.2.1⟩, t1.2.2⟩, t2⟩, fun t ht => ⟨t3 t ht, t4 t ht⟩⟩

/-- **The public test at a state.** -/
theorem totalIn_of_four (own : List (ℕ × ℕ)) (t : S) (a : K9.Part) (ha : atS.get? t = some a)
    (t1 : a.F.LS.size = a.F.ns ∧ a.F.vp.size = a.F.ns ∧ a.F.mf.size = a.F.ns)
    (t2 : (maskSeat own a).isSome = true)
    (t3 : ∀ i, i < a.F.trees.size → (arrayIn own a i).isSome = true)
    (t4 : ∀ i, i < a.F.trees.size → ((a.F.trees.getD i {}).rows.all fun R =>
      R.coef.size == (a.F.trees.getD i {}).R) = true) : totalIn own t = true := by
  unfold totalIn
  rw [ha]
  exact ledgerIn_of_four own a t1 t2 t3 t4

/-- **The same where the ledger has the looks sh**: the third and the fourth share range over sh's
length, and the fourth holds each virtual row's number of weights against sh's number of rows. -/
theorem totalIn_of_looks (sh : List Look) (own : List (ℕ × ℕ)) (t : S) (a : K9.Part)
    (ha : atS.get? t = some a) (hl : HasFork (LooksAre sh) t)
    (t1 : a.F.LS.size = a.F.ns ∧ a.F.vp.size = a.F.ns ∧ a.F.mf.size = a.F.ns)
    (t2 : (maskSeat own a).isSome = true)
    (t3 : ∀ i, i < sh.length → (arrayIn own a i).isSome = true)
    (t4 : ∀ i x, sh[i]? = some x → ∀ R ∈ (a.F.trees.getD i {}).rows, R.coef.size = x.2.1) :
    totalIn own t = true := by
  obtain ⟨G, hG, hl⟩ := hl
  obtain rfl : G = a.F := Option.some.inj (hG.symm.trans (fork_part t a ha))
  have hn := looks_size hl
  refine totalIn_of_four own t a ha t1 t2 (fun i hi => t3 i (hn ▸ hi)) fun i hi => ?_
  have hi' : i < sh.length := hn ▸ hi
  have hx : sh[i]? = some sh[i] := List.getElem?_eq_getElem hi'
  obtain ⟨_, e⟩ := looks_get hl i _ hx
  refine Array.all_eq_true_iff_forall_mem.2 fun R hR => ?_
  rw [beq_iff_eq, t4 i _ hx R hR, ← e]
  rfl

/-! ## 5 A member, and negative tests -/

/-- A ledger with one table's vector has that look. -/
theorem looks_toy : LooksAre [(HKind.table, 1, 3, 1)]
    { trees := #[{ R := 1, K := 3, rows := #[{}] }] } := rfl

/-- NEGATIVE: with two rows it has not. -/
theorem looks_toy_no : ¬ LooksAre [(HKind.table, 1, 3, 1)]
    { trees := #[{ R := 2, K := 3, rows := #[{}] }] } := by
  intro h
  simp [LooksAre, look] at h

theorem unit_toy : unitLook [(HKind.table, 1, 3, 1)] 0 = true := rfl

/-- NEGATIVE: two rows · the kind "symbols" · no virtual row · no such array. -/
theorem unit_toy_no : unitLook [(HKind.table, 2, 3, 1)] 0 = false ∧
    unitLook [(HKind.symbols, 1, 3, 1)] 0 = false ∧ unitLook [(HKind.table, 1, 3, 0)] 0 = false ∧
    unitLook [(HKind.table, 1, 3, 1)] 1 = false := ⟨rfl, rfl, rfl, rfl⟩

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.shapeAt_look
#print axioms VerifiableInference.Desc.LinkJoin.looks_frame
#print axioms VerifiableInference.Desc.LinkJoin.looks_laid
#print axioms VerifiableInference.Desc.LinkJoin.looks_start
#print axioms VerifiableInference.Desc.LinkJoin.looks_rests
#print axioms VerifiableInference.Desc.LinkJoin.looks_runs
#print axioms VerifiableInference.Desc.LinkJoin.looks_puts
#print axioms VerifiableInference.Desc.LinkJoin.rests_and
#print axioms VerifiableInference.Desc.LinkJoin.looks_fill
#print axioms VerifiableInference.Desc.LinkJoin.looks_draw
#print axioms VerifiableInference.Desc.LinkJoin.looks_add
#print axioms VerifiableInference.Desc.LinkJoin.sizedLooks_rests
#print axioms VerifiableInference.Desc.LinkJoin.looks_batch
#print axioms VerifiableInference.Desc.LinkJoin.looks_behind
#print axioms VerifiableInference.Desc.LinkJoin.looks_shut
#print axioms VerifiableInference.Desc.LinkJoin.looks_size
#print axioms VerifiableInference.Desc.LinkJoin.looks_get
#print axioms VerifiableInference.Desc.LinkJoin.shape_at
#print axioms VerifiableInference.Desc.LinkJoin.reads_mem
#print axioms VerifiableInference.Desc.LinkJoin.shape_of_looks
#print axioms VerifiableInference.Desc.LinkJoin.shape_letter
#print axioms VerifiableInference.Desc.LinkJoin.ledgerIn_of_four
#print axioms VerifiableInference.Desc.LinkJoin.totalIn_of_four
#print axioms VerifiableInference.Desc.LinkJoin.totalIn_of_looks
#print axioms VerifiableInference.Desc.LinkJoin.looks_toy
#print axioms VerifiableInference.Desc.LinkJoin.looks_toy_no
#print axioms VerifiableInference.Desc.LinkJoin.unit_toy
#print axioms VerifiableInference.Desc.LinkJoin.unit_toy_no
