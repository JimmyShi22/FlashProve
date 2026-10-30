-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/DoorPayGp.lean: THE FORM's HALF AT THE LINK: THE LAST OF THE DOOR's PREMISES:
THE TWO TESTS ON THE RECORD BEHIND THE BATCHING (gpOk, Johnson/Desc/K12/Law/FirstOk.lean; labelsOk,
FirstCut.lean) SAY YES, at the chain's start, from a test on the plan's public numbers alone.

The idea. The clauses of the two tests read of their record: the codes; the layout; the members'
seats and the further message's seat; the list of trees; the declared openings; of the book only
each listed tree's number and shape; of the row only whether it has a kept form. At the chain's
start all these are public. So the plan's share is THE DESCRIPTION's OWN CLAUSES AT A PUBLIC
SKELETON: no clause is said again here.

Main names (namespace Johnson.Prover.Link).
  SameRead D D'   two records of the tests agree in what the clauses read.
  gpL_congr, num_congr   then the clauses are the same.
  skelOf S K p k sh   THE SKELETON: three messages 0, 1, 2: parts 0, 1, 2 of tree 0, whose number
      is 0.
  gpPlanOk S K p cur   THE PLAN's SHARE, with code: both tests' clauses at the skeleton, and: cur is
      the place's first stage.
  seatOf_of   a seat from its three look-ups.
  gpOf_ran   the real record behind the batching is there, and agrees with the skeleton.
  gp_of_ran   THE STATEMENT: both tests say yes at every row without a kept form.
  door_premises'   door_premises (Johnson/Prover/Link/DoorPay.lean) with gpPlanOk in the place of
      the two tests.

By calls: readSeat_of_ran (Johnson/Prover/Link/DoorSeat.lean); ran_layout, ran_oracle0, ran_oracle1,
ran_oracle2, ran_of_front, ran_group, door_premises (DoorPay.lean); begun_shape
(OnBytes/Slice/BlkLinkSeat.lean); begun_codes.

Limits. AT THE CHAIN's START ALONE, AND FOR A CHAIN THAT COUNTS ITS TREES FROM 0: no oracle message,
no tree and no root in front; the CONTEXT's firstTree is 0 (c.ch.firstTree): four premises of
gpOf_ran and gp_of_ran, met by rfl in door_premises'. The skeleton's tree has the number 0 by its
make. The PLAN's nums.firstTree is another number: nothing here ties the two.
Members of gpPlanOk: Johnson/Prover/Link/DoorGpMembers.lean. door_premises' still has as premises:
DoorPlan, gpPlanOk, five closed tests on the plan, LinkSeats, "in order" and the count of the open
rows. That the six blocks say yes is not shown here. Nothing on values. Nothing on soundness.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.DoorSeat
import Johnson.Desc.K12.Law.FirstCut
import Johnson.Desc.K15.HsemSays

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Link
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Means
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.First (Plain Seat1 seatOf gpL gpOf gpAll gpOk labelsL labelsOk opensOf keyAt logAt widthAt
  numAt entered)
open Desc.K15 (St P15 frontBlock blocksOrV first entries ctxOf parK1 t12Of)

/-! ## 1 What the two tests read of their record -/

/-- Two records that agree in what the clauses read. -/
structure SameRead (D D' : Plain) : Prop where
  codes : D.st.codes = D'.st.codes
  lay : D.L = D'.L
  mems : D.mems = D'.mems
  fresh : D.fresh = D'.fresh
  ts : D.ts = D'.ts
  opens : D.opens = D'.opens
  trees : ∀ t ∈ D.ts, (D.book.trees[t]?).map (fun T => (T.number, T.shape)) =
    (D'.book.trees[t]?).map fun T => (T.number, T.shape)

theorem map_trees {α : Type} (f : Nat × TreeShape → α) (d : α) (B B' : TreeBook) (t : Nat)
    (h : (B.trees[t]?).map (fun T => (T.number, T.shape)) =
      (B'.trees[t]?).map fun T => (T.number, T.shape)) :
    ((B.trees[t]?).map fun T => f (T.number, T.shape)).getD d =
      ((B'.trees[t]?).map fun T => f (T.number, T.shape)).getD d := by
  have e := congrArg (fun o => (o.map f).getD d) h
  simpa [Option.map_map, Function.comp_def] using e

/-- **The clauses of the first test are the same at two records that agree in what is read.** -/
theorem gpL_congr (p : P12) (a : Fmt.M1.Stage) (row row' : GroupRow) {D D' : Plain}
    (h : SameRead D D') (hk : row.kept.isEmpty = row'.kept.isEmpty) :
    gpL p a row D = gpL p a row' D' := by
  have k1 : D'.ts.map (keyAt p.nums.firstTree D.book) =
      D'.ts.map (keyAt p.nums.firstTree D'.book) := by
    refine List.map_congr_left fun t ht => ?_
    exact congrArg (· - p.nums.firstTree) (map_trees (·.1) 0 _ _ t (h.trees t (h.ts ▸ ht)))
  have k2 : D'.ts.map (logAt D.book) = D'.ts.map (logAt D'.book) :=
    List.map_congr_left fun t ht => map_trees (·.2.logN) 0 _ _ t (h.trees t (h.ts ▸ ht))
  have k3 : D'.ts.map (widthAt D.book) = D'.ts.map (widthAt D'.book) :=
    List.map_congr_left fun t ht =>
      map_trees (fun x => x.2.mainWidth + x.2.maskWidth) 0 _ _ t (h.trees t (h.ts ▸ ht))
  unfold gpL
  simp only [h.codes, h.lay, h.mems, h.fresh, h.ts, h.opens, hk, k1, k2, k3]

theorem num_congr {D D' : Plain} (h : SameRead D D') :
    D.ts.map (numAt D.book) = D'.ts.map (numAt D'.book) := by
  rw [← h.ts]
  exact List.map_congr_left fun t ht => map_trees (·.1) 0 _ _ t (h.trees t ht)

/-! ## 2 The public skeleton at the chain's start -/

/-- **The record of the two tests at the chain's start, of public numbers alone**: S: the link's
shape; K: the codes; sh: the one tree's shape. -/
def skelOf (S : LinkShape) (K : Codes) (p : P12) (k : Nat) (sh : TreeShape) : Plain where
  st := { codes := K }
  book := { trees := #[{ shape := sh }] }
  L := linkLay S { codes := K }
  mems := [⟨0, rowShape S, 0, 0, sh, 0⟩, ⟨1, rowShape S, 0, 1, sh, 0⟩]
  fresh := ⟨2, (foldMaskNotice (linkFoldShape S)).shape, 0, 2, sh, 0⟩
  ts := [0]
  opens := opensOf p k

/-- **The plan's share of the two tests**: the description's own clauses at the skeleton. -/
def gpPlanOk (S : LinkShape) (K : Codes) (p : P12) (cur : Fmt.M1.Stage) : Bool :=
  match (layTrees K (linkMessage S 1)).bind (·.shapes[0]?) with
  | some sh =>
    H2K.First.ok (gpL p cur {} (skelOf S K p cur.k sh)) &&
      ((skelOf S K p cur.k sh).opens.map (·.1.tree) ==
        (skelOf S K p cur.k sh).ts.map (numAt (skelOf S K p cur.k sh).book)) &&
      decide (p.nums.stages.head? = some cur)
  | none => false

/-! ## 3 The real record behind the batching, at the chain's start -/

/-- A seat, from its three look-ups. -/
theorem seatOf_of {T : Statement} {B : TreeBook} {id : Nat} {s : OracleShape} {q : Nat × Nat}
    {tr : Tree} (h1 : (T.oracles[id]?).map (·.shape) = some s) (h2 : B.place[id]? = some q)
    (h3 : B.trees[q.1]? = some tr) :
    seatOf T B id = some ⟨id, s, q.1, q.2, tr.shape, tr.number⟩ := by
  unfold seatOf
  cases hx : T.oracles[id]? with
  | none => rw [hx] at h1; cases h1
  | some x =>
    rw [hx] at h1
    obtain rfl : x.shape = s := Option.some.inj h1
    simp [h2, h3]

section Start
variable {S : LinkShape} {first further : TableKey} {c c1 : Ctx} {x : LinkRun} {D : LinkDataR}
  (hR : LinkRanR S first further c c1 x D) {p : P12} {cur nxt : Fmt.M1.Stage} {i n : Nat × Nat}
  (Pl : DoorPlan S c.st.codes p cur nxt i n) {t : T12} (hst : t.st = c1.st)
  (hb : t.book = c1.book) (hg : t.g = x.group) (hm : t.mask = x.mask)
  (z1 : c.st.oracles.size = 0) (z2 : c.book.trees.size = 0) (z3 : c.ch.firstTree = 0)
  (z4 : c.ch.roots = 0)

include hR Pl hst hb hg hm z1 z2 z3 z4

/-- **The record of the two tests behind the batching agrees with the skeleton in what is read.** -/
theorem gpOf_ran (row : GroupRow) (sh : TreeShape) (hsh : D.lay.shapes[0]? = some sh) :
    ∃ Dr, gpOf p (batT t (linkGrpR S D.rec0 D.rec1 D.rows0 D.rows1 D.rE c.st.oracles.size) row)
        cur (layoutOf t.st (linkGrpR S D.rec0 D.rec1 D.rows0 D.rows1 D.rE c.st.oracles.size)) =
        some Dr ∧ SameRead Dr (skelOf S c.st.codes p cur.k sh) := by
  obtain ⟨T, sh', ⟨a1, a2, -, -, -, -⟩, b1, b2, b3, -⟩ := readSeat_of_ran hR Pl hst hb
  obtain rfl : sh = sh' := Option.some.inj (hsh.symm.trans b1)
  rw [z2] at a1
  rw [z3, z4, Nat.add_zero] at b3
  have hL : layoutOf t.st (linkGrpR S D.rec0 D.rec1 D.rows0 D.rows1 D.rE c.st.oracles.size) =
      linkLay S c.st := by rw [hst]; exact ran_layout hR
  have hLs : linkLay S c.st = linkLay S { codes := c.st.codes } := by
    unfold linkLay
    rw [z1]
    rfl
  have p0 : t.book.place[0]? = some (0, 0) := by
    have h := a2 0 (by simp)
    simpa [z1, z2] using h
  have p1 : t.book.place[1]? = some (0, 1) := by
    have h := a2 1 (by simp)
    simpa [z1, z2] using h
  have p2 : t.book.place[2]? = some (0, 2) := by
    have h := a2 2 (by simp)
    simpa [z1, z2] using h
  have o0 := congrArg (Option.map (·.shape)) (ran_oracle0 hR)
  have o1 := congrArg (Option.map (·.shape)) (ran_oracle1 hR)
  have o2 := congrArg (Option.map (·.shape)) (ran_oracle2 hR Pl.ahead)
  rw [← hst, z1] at o0 o1 o2
  have s0 := seatOf_of (T := begun t.st t.g
    (linkGrpR S D.rec0 D.rec1 D.rows0 D.rows1 D.rE c.st.oracles.size))
    ((begun_shape _ _ _ 0).trans o0) p0 a1
  have s1 := seatOf_of (T := begun t.st t.g
    (linkGrpR S D.rec0 D.rec1 D.rows0 D.rows1 D.rE c.st.oracles.size))
    ((begun_shape _ _ _ 1).trans o1) p1 a1
  have s2 := seatOf_of (T := begun t.st t.g
    (linkGrpR S D.rec0 D.rec1 D.rows0 D.rows1 D.rE c.st.oracles.size))
    ((begun_shape _ _ _ 2).trans o2) p2 a1
  have hmk : t.mask = some 2 := by rw [hm, hR.mask, if_pos Pl.ahead, z1]
  have hsA : stageAt p 0 cur = some ⟨i.1, i.2, cur.k, cur.h⟩ := by
    unfold stageAt
    rw [Pl.idx0]
    rfl
  have hmem : (linkLay S c.st).members.toList = [0, 1] := by simp [linkLay, z1]
  have hT : (T.number, T.shape) = (0, sh) := by rw [b2, b3]
  rw [hL]
  refine ⟨⟨begun t.st t.g (linkGrpR S D.rec0 D.rec1 D.rows0 D.rows1 D.rE c.st.oracles.size), t.book,
    linkLay S c.st,
    [⟨0, rowShape S, 0, 0, T.shape, T.number⟩, ⟨1, rowShape S, 0, 1, T.shape, T.number⟩],
    ⟨2, (foldMaskNotice (linkFoldShape S)).shape, 0, 2, T.shape, T.number⟩,
    Fmt.listOf ([0, 0] ++ [0]), opensOf p cur.k⟩, ?_, ?_⟩
  · unfold gpOf
    rw [hsA]
    simp only [Option.bind_some, entered, batT, hmk, hmem, List.mapM_cons, List.mapM_nil, s0, s1,
      s2, Option.map_some, Option.pure_def, Option.bind_eq_bind]
    rfl
  · refine ⟨?_, hLs, ?_, ?_, (by decide : Fmt.listOf ([0, 0] ++ [0]) = [0]), rfl, ?_⟩
    · show (begun t.st t.g _).codes = c.st.codes
      rw [begun_codes, hst, hR.codes]
    · show [(⟨0, _, 0, 0, T.shape, T.number⟩ : Seat1), ⟨1, _, 0, 1, T.shape, T.number⟩] = _
      rw [b2, b3]
      rfl
    · show (⟨2, _, 0, 2, T.shape, T.number⟩ : Seat1) = _
      rw [b2, b3]
      rfl
    · intro τ hτ
      have e : τ = 0 := by
        have h' : τ ∈ Fmt.listOf ([0, 0] ++ [0]) := hτ
        have h2 : Fmt.listOf ([0, 0] ++ [0]) = [0] := by decide
        rw [h2] at h'
        exact List.mem_singleton.1 h'
      subst e
      show (t.book.trees[0]?).map _ = _
      rw [a1]
      exact congrArg some hT

/-- **THE TWO TESTS ON THE RECORD BEHIND THE BATCHING SAY YES**, from the plan's share. -/
theorem gp_of_ran (hgp : gpPlanOk S c.st.codes p cur = true) (row : GroupRow)
    (hk : row.kept = #[]) :
    gpOk p (batT t (linkGrpR S D.rec0 D.rec1 D.rows0 D.rows1 D.rE c.st.oracles.size) row) = true ∧
      labelsOk p (batT t (linkGrpR S D.rec0 D.rec1 D.rows0 D.rows1 D.rE c.st.oracles.size) row) =
        true := by
  obtain ⟨T, sh, -, hsh, -⟩ := readSeat_of_ran hR Pl hst hb
  unfold gpPlanOk at hgp
  rw [hR.laid] at hgp
  simp only [Option.bind_some, hsh, Bool.and_eq_true, decide_eq_true_eq] at hgp
  obtain ⟨⟨g1, g2⟩, g3⟩ := hgp
  obtain ⟨rest, hst'⟩ : ∃ rest, p.nums.stages = cur :: rest := by
    cases hs : p.nums.stages with
    | nil => rw [hs] at g3; cases g3
    | cons a l =>
      rw [hs] at g3
      exact ⟨l, by rw [Option.some.inj g3]⟩
  obtain ⟨Dr, e, hS⟩ := gpOf_ran hR Pl hst hb hg hm z1 z2 z3 z4 row sh hsh
  constructor
  · unfold gpOk gpAll
    rw [hst']
    show H2K.First.ok (match gpOf p _ cur _ with
      | some D => gpL p cur row D
      | none => _) = true
    rw [e]
    show H2K.First.ok (gpL p cur row Dr) = true
    rw [gpL_congr p cur row {} hS (by rw [hk])]
    exact g1
  · unfold labelsOk labelsL
    rw [hst']
    show H2K.First.ok (match gpOf p _ cur _ with
      | some D => [("opens.tree", D.opens.map (·.1.tree) == D.ts.map (numAt D.book))]
      | none => _) = true
    rw [e]
    show H2K.First.ok [("opens.tree", Dr.opens.map (·.1.tree) == Dr.ts.map (numAt Dr.book))] = true
    rw [hS.opens, num_congr hS]
    simp [H2K.First.ok, g2]

end Start

/-! ## 4 At the chain's start -/

/-- **FROM THE SIX FRONT BLOCKS' YES TO THE DOOR's PREMISES**: door_premises
(Johnson/Prover/Link/DoorPay.lean) with the plan's share in the place of the two tests. -/
theorem door_premises' (P : P15) (x : TableKey × TableKey) {p : P12} {cur nxt : Fmt.M1.Stage}
    {i n : Nat × Nat} (Pl : DoorPlan P.S P.codes p cur nxt i n)
    (hgp : gpPlanOk P.S P.codes p cur = true) (hl : P.codes.lengthsOk = true)
    (hpl : VerifiableInference.Desc.K1.planOkOwn (parK1 P) = true) (hs : P.set.samples = 1)
    (es5 : List Fmt.Entry) (he : entries P = some es5) (es : List Fmt.Entry)
    (hi0 : x.1.item = 0) (hi1 : x.2.item = 1) (kok : linkOk P.codes P.S 1 = true) (d' : St)
    (G' : Group) (rs rest : List Fmt.RoundView) (cols cols' : List OpenedColumn)
    (h : foldBlocks 0 (frontBlock P :: blocksOrV P) (first P.codes x) rs cols =
      .ok (d', rest, cols'))
    (hS : LinkSeats P.par d' G') (ho : InOrder d'.st) (cut : List Fmt.DeclaredRound)
    (hcount : ∀ d ∈ cut, d.entry.rows = G'.rows.size + 2) :
    TestFront p cur nxt (t12Of d') G' i n 2 ∧ BatOwes p cut (t12Of d') G' ∧
      FrontOwes p (t12Of d') G' ∧
      ∃ X D, LinkRanR P.S x.1 x.2 (ctxOf es (first P.codes x) rs cols)
        (ctxOf (es.drop 5) d' rest cols') X D ∧ X.group = d'.loc.g ∧
        X.mask = d'.loc.firstMask := by
  obtain ⟨X, D, hR, e1, e2⟩ :=
    ran_of_front P x hl hpl hs es5 he es d' rs rest cols cols' hi0 hi1 kok h
  have hG : G' = linkGrpR P.S D.rec0 D.rec1 D.rows0 D.rows1 D.rE 0 := by
    have a := hS.group
    have b := ran_group hR
    rw [e1] at b
    exact Option.some.inj (a.symm.trans b)
  refine door_premises P x Pl hl hpl hs es5 he es hi0 hi1 kok d' G' rs rest cols cols' h hS ho cut
    hcount fun row hk => ?_
  rw [hG]
  exact gp_of_ran hR Pl (t := t12Of d') rfl rfl e1.symm e2.symm rfl rfl rfl rfl hgp row hk

end Johnson.Prover.Link

#print axioms Johnson.Prover.Link.map_trees
#print axioms Johnson.Prover.Link.gpL_congr
#print axioms Johnson.Prover.Link.num_congr
#print axioms Johnson.Prover.Link.seatOf_of
#print axioms Johnson.Prover.Link.gpOf_ran
#print axioms Johnson.Prover.Link.gp_of_ran
#print axioms Johnson.Prover.Link.door_premises'
