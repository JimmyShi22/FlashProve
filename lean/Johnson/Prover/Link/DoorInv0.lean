-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/DoorInv0.lean: THE FORM's HALF AT THE LINK: THE LOOP's INVARIANT IS MET AT STAGE
0: FormInv (Johnson/Prover/Link/FormInv.lean), all thirteen fields, at the state behind the
batching; and the state's halves of "the link's first tree" in the library's form (SeatP,
Johnson/Desc/K12/Law/SwDid.lean; LayAt, OnBytes/Slice/BlkTies.lean). Off the library's structure
of facts (LinkRanR), the plan's share (DoorPlan) and one public test more.

Main names (namespace Johnson.Prover.Link).
  seatPlanL, seatPlanOk, seatPlan_of_ok   ONE PUBLIC TEST MORE, with code: the one tree's length,
      its two lists of symbols, its width; the members' degree; the third message has a row.
  ran_step, ran_groups, lay0   statement and book in step; one group more; the layout as LayAt.
  seatP0   SeatP AT THE DOOR, behind the test's beginning.
  left0   nothing is left untested behind the batching (Johnson/Desc/ChainEndLaw.lean): no field of
      FormInv: it stands beside it.
  formInv0   THE STATEMENT; the tree's number and shape are handed beside it.
  colFirst0   the shapes' five facts, LayAt and SeatP together.

By calls: foldFront_first (FormFirst.lean); testFront_of_ran, ran_layout, ran_size, ran_group,
ran_oracle0, ran_oracle1, ran_oracle2 (DoorPay.lean); readSeat_of_ran, msg_size (DoorSeat.lean);
begun_shape (OnBytes/Slice/BlkLinkSeat.lean); ReadSeat.begun (ReadRide.lean); combine_noKept0
(Johnson/Desc/K12/Law/BatNoKept.lean); combine_dense (OnBytes/Slice/BlkProxDense.lean);
InOrder.begun (Johnson/Desc/Means/Order.lean); begun_group (Johnson/Desc/K12/Law/FitsLen.lean);
begun_sizes, withRows_sizes, bookSent_sizes (OnBytes/Slice/BlkProxKeeps.lean); closeLedgers_get
(BlkProxEarlierMessagesAndGroups.lean).

Limits. left0 stands AT THE CHAIN's START ALONE (no group and no oracle message in front); formInv0
does not ask that. PREMISES OF formInv0 THAT ARE PAID ELSEWHERE: "in order" in front of the
batching; the roots; the batching's own equation; the written column's length; AND THE FIELD "decl"
(what the plan's round "CS" declares), asked of every tree with that number, shape and length.
Members of seatPlanOk: Johnson/Prover/Link/DoorInv0Members.lean. The letters are the link's own
(S.rows, ceilLog2 S.rows, cur): nothing ties them here to the sizes' structure of the values'
half. Nothing on values. Nothing on soundness.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.DoorPayGp
import Johnson.Prover.Link.FormInv
import Johnson.Prover.Link.ReadRide
import Johnson.Desc.K12.Law.SwDid
import Johnson.Desc.K12.Law.FitsLen
import OnBytes.Slice.BlkTies

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Link
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Means
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.Pub (sgOf)
open H2K.Sw (SeatP)
open OnBytes.Slice.ProxRun (combine_dense)

/-! ## 1 One public test more: the one tree's numbers -/

/-- **The one tree's numbers, with code**: sh: its shape, off the library's laying of the link's one
message. The clause under the caption "fresh" is `0 < maskRows` of the shape of
`foldMaskNotice (linkFoldShape S)`. -/
def seatPlanL (S : LinkShape) (K : Codes) (cur : Fmt.M1.Stage) : List (String × Bool) :=
  match (layTrees K (linkMessage S 1)).bind (·.shapes[0]?) with
  | some sh =>
    let shapes := [rowShape S, rowShape S, (foldMaskNotice (linkFoldShape S)).shape]
    [("log", decide (sh.logN = cur.C.a)),
     ("mainSymbols",
       decide (sh.mainSymbols = (shapes.map fun s => s.mainRows * s.mainDeg).toArray)),
     ("maskSymbols", decide (sh.maskSymbols = (shapes.map fun s => s.maskRows * 3).toArray)),
     ("width", decide (sh.mainWidth + sh.maskWidth = 3 * (S.rows + (S.rows + 1)))),
     ("deg", decide ((rowShape S).mainDeg = 3)),
     ("fresh", decide (0 < (foldMaskNotice (linkFoldShape S)).shape.maskRows))]
  | none => [("the tree", false)]

/-- The test: every clause accepts. -/
def seatPlanOk (S : LinkShape) (K : Codes) (cur : Fmt.M1.Stage) : Bool :=
  (seatPlanL S K cur).all (·.2)

theorem seatPlan_of_ok {S : LinkShape} {K : Codes} {cur : Fmt.M1.Stage} {lay : TreeLay}
    {sh : TreeShape} (h : seatPlanOk S K cur = true) (hl : layTrees K (linkMessage S 1) = some lay)
    (hs : lay.shapes[0]? = some sh) :
    sh.logN = cur.C.a ∧
      sh.mainSymbols = ([rowShape S, rowShape S, (foldMaskNotice (linkFoldShape S)).shape].map
        fun s => s.mainRows * s.mainDeg).toArray ∧
      sh.maskSymbols = ([rowShape S, rowShape S, (foldMaskNotice (linkFoldShape S)).shape].map
        fun s => s.maskRows * 3).toArray ∧
      sh.mainWidth + sh.maskWidth = 3 * (S.rows + (S.rows + 1)) ∧ (rowShape S).mainDeg = 3 ∧
      0 < (foldMaskNotice (linkFoldShape S)).shape.maskRows := by
  unfold seatPlanOk seatPlanL at h
  rw [hl] at h
  simp only [Option.bind_some, hs, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
    decide_eq_true_eq] at h
  exact h

/-! ## 2 The small fields -/

section Ran
variable {S : LinkShape} {first further : TableKey} {c c1 : Ctx} {x : LinkRun} {D : LinkDataR}
  (hR : LinkRanR S first further c c1 x D)

include hR

theorem ran_step : c1.st.oracles.size = c1.book.place.size := by
  rw [ran_size hR, hR.book, (ProxRun.bookSent_sizes c _ _).2, hR.placed]

/-- The layout in the library's form: two members, none kept; their blocks' first rows. -/
theorem lay0 : LayAt [c.st.oracles.size, c.st.oracles.size + 1]
    #[some 0, some (2 ^ ceilLog2 S.rows)] #[none, none]
    (layoutOf c1.st (linkGrpR S D.rec0 D.rec1 D.rows0 D.rows1 D.rE c.st.oracles.size)) := by
  rw [ran_layout hR]
  exact ⟨rfl, fun w _ => match w with
    | 0 => rfl
    | 1 => rfl
    | _ + 2 => rfl, rfl, rfl⟩

theorem ran_groups : c1.st.groups.size = c.st.groups.size + 1 := by
  rw [hR.st]
  unfold linkStR linkSt
  show (Array.modify _ _ _).size = _
  rw [Array.size_modify, (ProxRun.withRows_sizes _ _ _).2, (ProxRun.withRows_sizes _ _ _).2]
  unfold Slice.withMessageInGroup admitted
  simp only [Array.size_modify]
  show (c.st.groups.push _).size = _
  rw [Array.size_push]

end Ran

/-! ## 3 Behind the batching -/

section Door
variable {S : LinkShape} {first further : TableKey} {c c1 : Ctx} {x : LinkRun} {D : LinkDataR}
  (hR : LinkRanR S first further c c1 x D) {p : P12} {cur nxt : Fmt.M1.Stage} {i n : Nat × Nat}
  (Pl : DoorPlan S c.st.codes p cur nxt i n) {t : T12} (hst : t.st = c1.st)
  (hb : t.book = c1.book) (hg : t.g = x.group) (hm : t.mask = x.mask)

include hR Pl hst hb

/-- **SeatP AT THE DOOR**: the three messages are the parts of the one tree, in the library's form,
behind the test's beginning. -/
theorem seatP0 (hp : seatPlanOk S c.st.codes cur = true) (g : Nat) (G : Group) :
    SeatP (begun t.st g G) t.book
      [c.st.oracles.size, c.st.oracles.size + 1, c.st.oracles.size + 2]
      (c.ch.firstTree + c.ch.roots) cur.C.a
      [rowShape S, rowShape S, (foldMaskNotice (linkFoldShape S)).shape] := by
  obtain ⟨T, sh, ⟨a1, a2, -, -, -, -⟩, b1, b2, b3, -⟩ := readSeat_of_ran hR Pl hst hb
  obtain ⟨q1, q2, q3, -, -, -⟩ := seatPlan_of_ok hp hR.laid b1
  have o0 := congrArg (Option.map (·.shape)) (ran_oracle0 hR)
  have o1 := congrArg (Option.map (·.shape)) (ran_oracle1 hR)
  have o2 := congrArg (Option.map (·.shape)) (ran_oracle2 hR Pl.ahead)
  rw [← hst] at o0 o1 o2
  have sh_of : ∀ (o : Nat) (s : OracleShape), (t.st.oracles[o]?).map (·.shape) = some s →
      ∃ y, (begun t.st g G).oracles[o]? = some y ∧ y.shape = s := by
    intro o s h
    have h' := (begun_shape t.st g G o).trans h
    cases hy : (begun t.st g G).oracles[o]? with
    | none => rw [hy] at h'; cases h'
    | some y => rw [hy] at h'; exact ⟨y, rfl, Option.some.inj h'⟩
  refine ⟨rfl, ⟨c.book.trees.size, T, a1, b3, by rw [b2]; exact q1, by rw [b2]; exact q2,
    by rw [b2]; exact q3, fun w hw => ?_⟩, fun w hw => ?_⟩
  · have hw' : w < 3 := hw
    match w, hw' with
    | 0, _ => exact a2 0 (by simp)
    | 1, _ => exact a2 1 (by simp)
    | 2, _ => exact a2 2 (by simp)
  · have hw' : w < 3 := hw
    match w, hw' with
    | 0, _ => exact sh_of _ _ o0
    | 1, _ => exact sh_of _ _ o1
    | 2, _ => exact sh_of _ _ o2

include hg hm

-- left0 reads neither hb nor hm.
omit hb hm in
/-- **NOTHING IS LEFT UNTESTED BEHIND THE BATCHING**, at the chain's start: the one group's test has
begun; the two sampled messages are in it. -/
theorem left0 (z0 : c.st.groups.size = 0) (z1 : c.st.oracles.size = 0) :
    ChainEnd.NothingLeft (begun t.st t.g
      (linkGrpR S D.rec0 D.rec1 D.rows0 D.rows1 D.rE c.st.oracles.size)) := by
  have hG : t.st.groups[t.g]? =
      some (linkGrpR S D.rec0 D.rec1 D.rows0 D.rows1 D.rE c.st.oracles.size) := by
    rw [hst, hg]; exact ran_group hR
  have hg0 : t.g = 0 := by rw [hg, hR.group, z0]
  rw [hg0] at hG ⊢
  have hB := begun_group t.st 0 _ hG
  have hsz := ProxRun.begun_sizes t.st 0
    (linkGrpR S D.rec0 D.rec1 D.rows0 D.rows1 D.rE c.st.oracles.size)
  have hgs : t.st.groups.size = 1 := by rw [hst, ran_groups hR, z0]
  have hos : t.st.oracles.size = 3 := by rw [hst, ran_size hR, msg_size hR Pl, z1]
  constructor
  · intro j hj
    have hj' : j = 0 := by rw [hsz.2, hgs] at hj; omega
    subst hj'
    have e := Array.getElem?_eq_getElem hj
    rw [hB] at e
    rw [← Option.some.inj e]
  · intro j hj hs
    refine ⟨0, ?_, _, hB, rfl⟩
    have hj3 : j < 3 := by rw [hsz.1, hos] at hj; exact hj
    have e := Array.getElem?_eq_getElem hj
    have hcl : (begun t.st 0
        (linkGrpR S D.rec0 D.rec1 D.rows0 D.rows1 D.rE c.st.oracles.size)).oracles[j]? =
        (t.st.oracles[j]?).map fun y =>
          if j ∈ (linkGrpR S D.rec0 D.rec1 D.rows0 D.rows1 D.rE c.st.oracles.size).members.toList
          then ProxRun.shut y else y := ProxRun.closeLedgers_get _ _ _
    have h0 := ran_oracle0 hR
    have h1 := ran_oracle1 hR
    have h2 := ran_oracle2 hR Pl.ahead
    rw [← hst, z1] at h0 h1 h2
    rw [z0] at h0 h1
    rw [hcl] at e
    match j, hj3 with
    | 0, _ =>
      rw [h0] at e
      rw [← Option.some.inj e]
      split <;> exact List.mem_singleton.2 rfl
    | 1, _ =>
      rw [h1] at e
      rw [← Option.some.inj e]
      split <;> exact List.mem_singleton.2 rfl
    | 2, _ =>
      rw [h2] at e
      rw [← Option.some.inj e] at hs
      exfalso
      revert hs
      split <;> exact fun h => Bool.noConfusion h

/-- **THE FORM's HALF OF THE LOOP's INVARIANT IS MET AT STAGE 0**: at the state behind the
batching. x: the element that "BAT" sampled; row: the batched claim. The tree's shape
and number are handed beside it; what the plan's round "CS" declares is a premise on such a tree. -/
theorem formInv0 (hp : seatPlanOk S c.st.codes cur = true) (ho : InOrder t.st)
    (hroots : p.nums.free = t.roots) (θ : E) (row : GroupRow)
    (hc : Bat.combine (begun t.st t.g
        (linkGrpR S D.rec0 D.rec1 D.rows0 D.rows1 D.rE c.st.oracles.size)) t.g
      ⟨layoutOf t.st (linkGrpR S D.rec0 D.rec1 D.rows0 D.rows1 D.rE c.st.oracles.size),
        runRows t.st (linkGrpR S D.rec0 D.rec1 D.rows0 D.rows1 D.rE c.st.oracles.size)⟩ θ =
      some row)
    (l : Laid) (col : ℕ → List UInt64)
    (hcol : ∀ y, (col y).length = 3 * (S.rows + (S.rows + 1)))
    (hdecl : ∀ T : Tree, T.number = c.ch.firstTree + c.ch.roots →
      D.lay.shapes[0]? = some T.shape → T.shape.logN = cur.C.a →
      ∀ dS dC, ((l.drop (1 + cur.k)).take 2).map (·.1) = [dS, dC] →
        ∃ o, dC.opens = [o] ∧ o.1.tree = T.number ∧ o.1.a = cur.C.a ∧
          o.1.W = T.shape.mainWidth + T.shape.maskWidth) :
    ∃ T : Tree,
      FormInv p 0 cur l
        (batT t (linkGrpR S D.rec0 D.rec1 D.rows0 D.rows1 D.rE c.st.oracles.size) row) col row
        (layoutOf t.st (linkGrpR S D.rec0 D.rec1 D.rows0 D.rows1 D.rE c.st.oracles.size))
        ⟨i.1, i.2, cur.k, cur.h⟩ n (c.st.oracles.size + 2) c.book.trees.size T ∧
      T.number = c.ch.firstTree + c.ch.roots ∧ D.lay.shapes[0]? = some T.shape := by
  obtain ⟨T, sh, hS, b1, b2, b3, -⟩ := readSeat_of_ran hR Pl hst hb
  obtain ⟨q1, -, -, q4, -, -⟩ := seatPlan_of_ok hp hR.laid b1
  subst b2
  have H := testFront_of_ran hR Pl hst hg hm ho
  have hL := lay0 hR
  rw [← hst] at hL
  refine ⟨T, ⟨foldFront_first H θ row hc, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, q1,
    hdecl T b3 b1 q1, fun y => (hcol y).trans q4.symm⟩, b3, b1⟩
  · exact H2K.Pin.combine_noKept0 _ _ _ _ _ hc fun j => by
      show (layoutOf t.st _).kept.getD j false = false
      rw [hst, ran_layout hR]
      match j with
      | 0 => rfl
      | 1 => rfl
      | _ + 2 => rfl
  · intro j hj
    rw [hL.members] at hj
    exact hL.kept j hj
  · show (layoutOf t.st _).k = cur.h + (cur.k - cur.h)
    rw [H.layK, Pl.layH]
    omega
  · exact H.layH
  · exact combine_dense _ _ _ _ _ H.dense hc
  · exact ho.begun t.g _ H.group
  · show (begun t.st t.g _).oracles.size = t.book.place.size
    rw [(ProxRun.begun_sizes _ _ _).1, hst, hb]
    exact ran_step hR
  · show t.roots = p.nums.free + 0
    exact hroots.symm
  · show ReadSeat (begun t.st t.g _) t.book (layoutOf t.st _).members.toList _ _ _
    rw [hL.members]
    exact hS.begun t.g _

omit hg hm in
/-- **The state's halves of "the link's first tree"**, in the letters of the law that reads that
tree's words back: the shapes' five facts, the layout, the seat. -/
theorem colFirst0 (hp : seatPlanOk S c.st.codes cur = true) (g : Nat) (G : Group) :
    (rowShape S).mainRows = S.rows ∧ (rowShape S).mainDeg = 3 ∧ (rowShape S).maskRows = 0 ∧
      (foldMaskNotice (linkFoldShape S)).shape.mainRows = 0 ∧
      0 < (foldMaskNotice (linkFoldShape S)).shape.maskRows ∧
      LayAt [c.st.oracles.size, c.st.oracles.size + 1] #[some 0, some (2 ^ ceilLog2 S.rows)]
        #[none, none]
        (layoutOf t.st (linkGrpR S D.rec0 D.rec1 D.rows0 D.rows1 D.rE c.st.oracles.size)) ∧
      SeatP (begun t.st g G) t.book
        [c.st.oracles.size, c.st.oracles.size + 1, c.st.oracles.size + 2]
        (c.ch.firstTree + c.ch.roots) cur.C.a
        [rowShape S, rowShape S, (foldMaskNotice (linkFoldShape S)).shape] := by
  obtain ⟨T, sh, -, b1, -⟩ := readSeat_of_ran hR Pl hst hb
  obtain ⟨-, -, -, -, q5, q6⟩ := seatPlan_of_ok hp hR.laid b1
  exact ⟨rfl, q5, rfl, rfl, q6, hst ▸ lay0 hR, seatP0 hR Pl hst hb hp g G⟩

end Door

end Johnson.Prover.Link

#print axioms Johnson.Prover.Link.seatPlan_of_ok
#print axioms Johnson.Prover.Link.ran_step
#print axioms Johnson.Prover.Link.lay0
#print axioms Johnson.Prover.Link.ran_groups
#print axioms Johnson.Prover.Link.seatP0
#print axioms Johnson.Prover.Link.left0
#print axioms Johnson.Prover.Link.formInv0
#print axioms Johnson.Prover.Link.colFirst0
