-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/BlkLinkRan.lean: what a run of the steps of the program's link has done.

The steps of the link (OnBytes/Iop/Link.lean: `linkStepsVerify`) draw a fold point, make a group,
receive the oracle messages of the two folded rows (and, if masks are sent ahead, the fresh mask of
the test's first fold), sample the two, let them join the group, draw positions, read the columns of
the two stored tables there, turn them into open rows, draw a point of comparison and add the
equality row. This file writes down, as a definition (`LinkRan`), what a run of them on a view is to
have done, at `S.table.answers = 0` and one answer to a sample: which five rounds of the view it has
taken and what it has read in them, which opened columns it has taken, which rows it has made, and
which statement, book and channel it leaves. It then looks the statement up: the group, the two
oracle messages, and the rows that a proximity test on the group takes in.

Main definitions.
 `rowShape`             the shape of an oracle message that holds a folded row.
 `LinkSent`             what a run of the link's sending has done.
 `linkSt`               the statement after the steps, as a function of the statement before them.
 `LinkData`, `LinkRan`  what a run of the steps takes of a view and makes of it; what it has done.
 `linkGrp`, `linkOracle`   the group and a folded row's oracle message after the steps.
Main theorems.
 `linkSend_inv`     a run of the link's sending.
 `linkSt_codes`, `linkSt_group`, `linkSt_oracle0`, `linkSt_oracle1`   the statement, looked up.
 `linkSt_runRows`   the rows that the test takes in: the equality row, the two sample rows, the rows
                    of the first table's draws, those of the copy's.
Not claimed. Nothing at other `S.table.answers`, or for more than one answer to a sample. That a run
of the steps meets `LinkRan`: here only the sending is taken apart (`linkSend_inv`). Nothing on what
a row's coefficients are. Nothing on the dry run. Nothing on soundness.
-/
import OnBytes.Slice.BlkLinkRun

set_option autoImplicit false

namespace OnBytes.Slice

open Params (LinkShape FoldeqShape)

/-- The shape of an oracle message that holds a folded row, with one answer to its sample. -/
abbrev rowShape (S : LinkShape) : OracleShape := (S.side false 1).u

/-- The oracle messages of the link's one message, in the statement after their receiving. -/
theorem linkSent_oracles (S : LinkShape) (T : Statement) :
    (stSent T (linkMessage S 1)).oracles[T.oracles.size]? = some { shape := rowShape S } ∧
    (stSent T (linkMessage S 1)).oracles[T.oracles.size + 1]? = some { shape := rowShape S } ∧
    (S.masksAhead = true → (stSent T (linkMessage S 1)).oracles[T.oracles.size + 2]? =
      some { shape := (foldMaskNotice (linkFoldShape S)).shape }) := by
  refine ⟨?_, ?_, ?_⟩
  · have h := stSent_new T (linkMessage S 1) 0
    rw [Nat.add_zero] at h
    rw [h]
    unfold linkMessage
    rw [Array.getElem?_append_left (show 0 < 2 by decide)]
    rfl
  · rw [stSent_new T (linkMessage S 1) 1]
    unfold linkMessage
    rw [Array.getElem?_append_left (show 1 < 2 by decide)]
    rfl
  · intro hm
    rw [stSent_new T (linkMessage S 1) 2]
    simp [linkMessage, hm]

/-- The numbers of the link's oracle messages. -/
theorem linkSent_ids (S : LinkShape) (n0 : Nat) :
    ((Array.range (linkMessage S 1).size).map (· + n0)).toList =
      if S.masksAhead = true then [n0, n0 + 1, n0 + 2] else [n0, n0 + 1] := by
  cases hm : S.masksAhead
  · have hs : (linkMessage S 1).size = 2 := by simp [linkMessage, hm]
    rw [hs]
    simp [Array.range, List.ofFn_succ, Nat.add_comm]
  · have hs : (linkMessage S 1).size = 3 := by simp [linkMessage, hm]
    rw [hs]
    simp [Array.range, List.ofFn_succ, Nat.add_comm]

/-- The two folded rows' oracle messages are sampled, the fresh mask is not. -/
theorem linkSent_todo (S : LinkShape) (T : Statement) :
    todoOf (stSent T (linkMessage S 1))
      ((Array.range (linkMessage S 1).size).map (· + T.oracles.size)) =
      [T.oracles.size, T.oracles.size + 1] := by
  obtain ⟨q0, q1, q2⟩ := linkSent_oracles S T
  unfold todoOf
  rw [linkSent_ids]
  cases hm : S.masksAhead
  · simp [List.filter, q0, q1]
    rfl
  · simp [List.filter, q0, q1, q2 hm]
    rfl

/-- What a run of the link's sending, on a view, has done. lay: how the trees are placed; beta: the
factor of the seed; y0, y1: the two answers; row0, row1: the left sides of the two sample rows;
places: the pad of a folded row's oracle message; r2, r3: the rounds of the seed and of the answers;
rest: the rounds after them. -/
structure LinkSent (S : LinkShape) (c c' : Ctx) (ids : Array Nat) (lay : TreeLay) (beta y0 y1 : E)
    (row0 row1 : Row) (places : List PadPlace) (r2 r3 : Fmt.RoundView) (rest : List Fmt.RoundView) : Prop where
  laid : layTrees c.st.codes (linkMessage S 1) = some lay
  numbers : ids = (Array.range (linkMessage S 1).size).map (· + c.st.oracles.size)
  pending : c.ch.pending = r2 :: r3 :: rest
  vals2 : r2.vals = []
  factor : (r2.drawn.elems.map E.ofTriple).drop (Send.cube c.st.codes (rowShape S)).bits = [beta]
  nz : isZeroE beta = false
  vals3 : r3.vals = [.answer y0.triple, .answer y1.triple]
  form0 : Send.form c.st.codes (rowShape S) c.st.oracles.size
    ⟨(r2.drawn.elems.map E.ofTriple).take (Send.cube c.st.codes (rowShape S)).bits, beta⟩ 0 =
      some row0
  form1 : Send.form c.st.codes (rowShape S) (c.st.oracles.size + 1)
    ⟨(r2.drawn.elems.map E.ofTriple).take (Send.cube c.st.codes (rowShape S)).bits, beta⟩ 0 =
      some row1
  pad : Send.pad c.st.codes (rowShape S) = some places
  st : c'.st = admitted (admitted (stSent c.st (linkMessage S 1)) c.st.oracles.size (rowShape S)
      places #[{ row0 with target := y0 }]) (c.st.oracles.size + 1) (rowShape S) places
      #[{ row1 with target := y1 }]
  book : c'.book = bookSent c (linkMessage S 1) lay
  left : c'.ch.pending = rest
  entries : c'.ch.entries = c.ch.entries.drop 2
  dry : c'.ch.dry = false
  opened : c'.ch.opened = c.ch.opened
  failed : c'.failed = c.failed
  firstTree : c'.ch.firstTree = c.ch.firstTree
  samples : c'.ch.samples = c.ch.samples
  roots : c'.ch.roots = c.ch.roots + lay.shapes.size
  placed : c.st.oracles.size = c.book.place.size

/-- A run of the link's sending, with one answer to a sample. -/
theorem linkSend_inv (S : LinkShape) (ids : Array Nat) (c c' : Ctx) (hd : c.ch.dry = false)
    (h : (sendVerify (linkMessage S 1)).Yields c ids c') :
    ∃ lay beta y0 y1 row0 row1 places r2 r3 rest,
      LinkSent S c c' ids lay beta y0 y1 row0 row1 places r2 r3 rest := by
  obtain ⟨cR, hR, hV⟩ := sendVerify_inv _ _ _ _ _ h
  obtain ⟨lay, hlay, hpl, hids, hcR⟩ := receiveOracles_inv _ _ _ _ hd hR
  -- what the receiving has left
  have hdR : cR.ch.dry = false := by rw [hcR]; exact hd
  have hstR : cR.st = stSent c.st (linkMessage S 1) := by rw [hcR]
  have hbkR : cR.book = bookSent c (linkMessage S 1) lay := by rw [hcR]
  have hpeR : cR.ch.pending = c.ch.pending := by rw [hcR]; rfl
  have henR : cR.ch.entries = c.ch.entries := by rw [hcR]
  have hopR : cR.ch.opened = c.ch.opened := by rw [hcR]
  have hfaR : cR.failed = c.failed := by rw [hcR]
  have hftR : cR.ch.firstTree = c.ch.firstTree := by rw [hcR]
  have hsaR : cR.ch.samples = c.ch.samples := by rw [hcR]
  have hroR : cR.ch.roots = c.ch.roots + lay.shapes.size := by rw [hcR]
  have hcodes : cR.st.codes = c.st.codes := by rw [hstR]; rfl
  obtain ⟨q0, q1, -⟩ := linkSent_oracles S c.st
  obtain ⟨shapes, drawn, seeds, c1, c2, hsh, hclose, hseeds, hnz, hrun, hend⟩ :=
    verify_inv ids true cR c' hdR hV
  -- the two folded rows' oracle messages are sampled
  have htodo : todoOf cR.st ids = [c.st.oracles.size, c.st.oracles.size + 1] := by
    rw [hstR, hids]
    exact linkSent_todo S c.st
  have hshapes : shapes = [rowShape S, rowShape S] := by
    rw [htodo, hstR] at hsh
    simp only [List.mapM_cons, List.mapM_nil, q0, q1] at hsh
    exact (Option.some.inj hsh).symm
  subst hshapes
  have hans : (rowShape S).answers = 1 := rfl
  simp only [List.foldl_cons, List.foldl_nil, hans, Nat.zero_max, Nat.max_self, hcodes]
    at hclose hseeds
  obtain ⟨beta, hbeta, rfl⟩ := seedsOf_one _ _ _ hseeds
  have hb0 : isZeroE beta = false := by simpa using hnz
  -- the round of the seed
  obtain ⟨e, es, r2, rest1, k1, k2, _, k4, k5, rfl, _, _, _, k9, k10, _, k12, k13, k14, k15, k16,
    k17, k18, k19⟩ := Blk.close_inv _ _ _ _ _ _ hdR hclose
  -- the two answers
  rw [htodo] at hrun
  obtain ⟨_, c3, ⟨rows0, c4, hans0, hadm0⟩, _, c5, ⟨rows1, c6, hans1, hadm1⟩, _, rfl⟩ := hrun
  obtain ⟨_, c7, ⟨seed0, row0, y0, hs0, hform0, hrecv0, rfl⟩, rfl, rfl⟩ := hans0
  obtain ⟨_, c8, ⟨seed1, row1, y1, hs1, hform1, hrecv1, rfl⟩, rfl, rfl⟩ := hans1
  obtain rfl := Option.some.inj hs0
  obtain rfl := Option.some.inj hs1
  obtain ⟨r3, rest, vs, p1, p2, p3, p4⟩ := Blk.recvAnswer_inv _ _ _ k15 hrecv0
  obtain ⟨x0, places, a1, a2, _, _, _, a6⟩ := admit_inv _ _ _ _ hadm0
  have hst4 : c4.st = stSent c.st (linkMessage S 1) := p4.st.trans (k12.trans hstR)
  rw [hst4] at a1 a2 a6
  obtain rfl := Option.some.inj (q0.symm.trans a1)
  have hd3 : c3.ch.dry = false := by rw [a6]; exact p4.dry.trans k15
  obtain ⟨r3', rest', vs', s1, s2, s3, s4⟩ := Blk.recvAnswer_inv _ _ _ hd3 hrecv1
  obtain ⟨x1, places', b1, b2, _, _, _, b6⟩ := admit_inv _ _ _ _ hadm1
  have hst3 : c3.st = admitted (stSent c.st (linkMessage S 1)) c.st.oracles.size (rowShape S)
      places #[{ row0 with target := y0 }] := by
    rw [a6]
    rfl
  have hst6 : c6.st = admitted (stSent c.st (linkMessage S 1)) c.st.oracles.size (rowShape S)
      places #[{ row0 with target := y0 }] := s4.st.trans hst3
  rw [hst6] at b1 b2 b6
  rw [admitted_other _ _ _ _ _ _ (Nat.ne_of_lt (Nat.lt_succ_self _))] at b1
  obtain rfl := Option.some.inj (q1.symm.trans b1)
  obtain rfl : places = places' := Option.some.inj (a2.symm.trans b2)
  -- the round of the answers
  have hp3 : c3.ch.pending = { r3 with vals := vs } :: rest := by rw [a6]; exact p3
  obtain ⟨rfl, rfl⟩ := List.cons.inj (hp3.symm.trans s1)
  have hvs : vs = .answer y1.triple :: vs' := s2
  have hd2 : c2.ch.dry = false := by rw [b6]; exact s4.dry.trans hd3
  have hend' : (Blk.closeEmpty "SEND answer").Yields c2 () c' := by simpa using hend
  unfold Blk.closeEmpty at hend'
  obtain ⟨dA, c9, t1, t2⟩ := (Blk.yields_bind _ _ _ _ _).1 hend'
  obtain ⟨_, rfl⟩ := (Blk.yields_pure _ _ _ _).1 t2
  obtain ⟨e', es', rA, restA, u1, _, _, u4, u5, _, _, _, _, u9, u10, _, u12, u13, u14, u15, u16,
    u17, u18, u19⟩ := Blk.close_inv _ _ _ _ _ _ hd2 t1
  have hp2 : c2.ch.pending = { r3 with vals := vs' } :: rest := by rw [b6]; exact s3
  obtain ⟨rfl, rfl⟩ := List.cons.inj (hp2.symm.trans u4)
  have hvs' : vs' = [] := u5
  -- the plan's entries
  have hen2 : c2.ch.entries = es := by
    rw [b6]
    exact s4.entries.trans ((congrArg (·.ch.entries) a6).trans (p4.entries.trans k10))
  rw [hcodes] at hform0 hform1
  refine ⟨lay, beta, y0, y1, row0, row1, places, r2, r3, rest, hlay, hids, ?_, k5, hbeta, hb0, ?_,
    hform0, hform1, a2, ?_, ?_, u9, ?_, u15, ?_, ?_, ?_, ?_, ?_, hpl⟩
  · rw [← hpeR, k4, ← k9, p1]
  · rw [p2, hvs, hvs']
  · rw [u12, b6]
    rfl
  · rw [u13, b6]
    exact s4.book.trans ((congrArg (·.book) a6).trans (p4.book.trans (k13.trans hbkR)))
  · rw [u10, ← henR, k1]
    have : es = e' :: es' := hen2.symm.trans u1
    rw [this]
    rfl
  · rw [u16, b6]
    exact s4.opened.trans ((congrArg (·.ch.opened) a6).trans (p4.opened.trans (k16.trans hopR)))
  · rw [u14, b6]
    exact s4.failed.trans ((congrArg (·.failed) a6).trans (p4.failed.trans (k14.trans hfaR)))
  · rw [u18, b6]
    exact s4.firstTree.trans ((congrArg (·.ch.firstTree) a6).trans
      (p4.firstTree.trans (k18.trans hftR)))
  · rw [u19, b6]
    exact s4.samples.trans ((congrArg (·.ch.samples) a6).trans
      (p4.samples.trans (k19.trans hsaR)))
  · rw [u17, b6]
    exact s4.roots.trans ((congrArg (·.ch.roots) a6).trans (p4.roots.trans (k17.trans hroR)))

/-- The numbers of the link's oracle messages, one by one. -/
theorem linkSent_at (S : LinkShape) (n0 : Nat) :
    ((Array.range (linkMessage S 1).size).map (· + n0))[0]? = some n0 ∧
    ((Array.range (linkMessage S 1).size).map (· + n0))[1]? = some (n0 + 1) ∧
    ((Array.range (linkMessage S 1).size).map (· + n0))[2]? =
      if S.masksAhead = true then some (n0 + 2) else none := by
  have h := linkSent_ids S n0
  refine ⟨?_, ?_, ?_⟩
  · rw [← Array.getElem?_toList, h]
    split <;> rfl
  · rw [← Array.getElem?_toList, h]
    split <;> rfl
  · rw [← Array.getElem?_toList, h]
    split <;> rfl

/-! ## Joints of the block's text -/

/-- The place where the block takes the fresh mask's number, if the mask was sent ahead. -/
theorem maskJoint {β : Type} (b : Bool) (o : Option Nat) (jp : Option Nat → Blk β) (c : Ctx) (x : β)
    (c' : Ctx)
    (h : (if b = true then (do
        let y ← (do
          let l ← Blk.get o
          pure (some l))
        jp y) else (do
        let y ← pure none
        jp y)).Yields c x c') :
    ∃ mask, (if b = true then o = mask ∧ mask.isSome = true else mask = none) ∧
      (jp mask).Yields c x c' := by
  cases b
  · obtain ⟨y, c1, h1, h2⟩ := (Blk.yields_bind _ _ _ _ _).1 h
    obtain ⟨rfl, rfl⟩ := (Blk.yields_pure _ _ _ _).1 h1
    exact ⟨none, rfl, h2⟩
  · obtain ⟨y, c1, h1, h2⟩ := (Blk.yields_bind _ _ _ _ _).1 h
    obtain ⟨l, c2, h3, h4⟩ := (Blk.yields_bind _ _ _ _ _).1 h1
    obtain ⟨e1, rfl⟩ := (Blk.yields_get _ _ _ _).1 h3
    obtain ⟨rfl, rfl⟩ := (Blk.yields_pure _ _ _ _).1 h4
    exact ⟨some l, ⟨e1, rfl⟩, h2⟩

/-- Reading a row's target for a note changes nothing. -/
theorem groupTarget_inv (g i : Nat) (t : E) (c c' : Ctx) (h : (groupTarget g i).Yields c t c') :
    c' = c := by
  unfold groupTarget at h
  obtain ⟨G, c1, h1, h2⟩ := (Blk.yields_bind _ _ _ _ _).1 h
  obtain ⟨_, e1⟩ := (yields_group _ _ _ _).1 h1
  obtain ⟨_, e2⟩ := (Blk.yields_pure _ _ _ _).1 h2
  exact e2.trans e1

/-! ## The steps of the link -/

/-- The link's group as it is made: no member, no row. -/
def linkGrp0 (S : LinkShape) : Group := { code := S.code, maskCode := S.maskCode }

/-- The link's group with its first member. -/
def linkGrp1 (S : LinkShape) (n0 : Nat) : Group :=
  { linkGrp0 S with
    members := (linkGrp0 S).members.insertIdxIfInBounds
      ((linkGrp0 S).members.filter (· < n0)).size n0
    kept := (linkGrp0 S).kept.insertIdxIfInBounds
      ((linkGrp0 S).members.filter (· < n0)).size false }

/-- The statement after the link's steps, from the statement T before them. places: the pad of
a folded row's oracle message; s0, s1: the two sample rows; rows0, rows1: the rows of the two
tables' draws; rE: the equality row. -/
def linkSt (S : LinkShape) (T : Statement) (places : List PadPlace) (s0 s1 : Row)
    (rows0 rows1 : List Row) (rE : Row) : Statement :=
  withRow (withRows (withRows
    (withMessageInGroup (withMessageInGroup
                  (admitted (admitted (stSent (withGroup T S.code S.maskCode) (linkMessage S 1))
                    T.oracles.size (rowShape S) places #[s0]) (T.oracles.size + 1) (rowShape S) places #[s1])
                  T.groups.size T.oracles.size false (linkGrp0 S))
      T.groups.size (T.oracles.size + 1) false (linkGrp1 S T.oracles.size))
    T.groups.size rows0) T.groups.size rows1) T.groups.size rE

/-- How a reader finds the opening of one of the two stored tables. -/
def linkStored (S : LinkShape) (key : TableKey) (further : Bool) : Fmt.Stored :=
  ⟨S.table.tree, S.table.saltBytes, key.item, if further then S.columnsFirst else 0,
    if further then S.columnsFurther else S.columnsFirst⟩

/-- What a run of the link's steps takes of a view and makes of it. -/
structure LinkData where
  /-- the five rounds, and the rounds after them -/
  r1 : Fmt.RoundView
  r2 : Fmt.RoundView
  r3 : Fmt.RoundView
  r4 : Fmt.RoundView
  r5 : Fmt.RoundView
  rest : List Fmt.RoundView
  /-- how the trees of the link's message are placed -/
  lay : TreeLay
  /-- the factor of the seed, and the two answers -/
  beta : E
  y0 : E
  y1 : E
  /-- the left sides of the two sample rows; the pad of a folded row's oracle message -/
  row0 : Row
  row1 : Row
  places : List PadPlace
  /-- the drawn positions, and the columns of the two stored tables that were read -/
  pos : Positions
  cols0 : Array (Array F)
  cols1 : Array (Array F)
  /-- the rows of the two tables' draws; the equality row -/
  rows0 : List Row
  rows1 : List Row
  rE : Row

/-- What a run of the link's steps, on a view, has done, at `S.table.answers = 0` and one
answer to a sample. -/
structure LinkRan (S : LinkShape) (first further : TableKey) (c c' : Ctx) (x : LinkRun)
    (D : LinkData) : Prop where
  ok : linkOk c.st.codes S 1 = true
  /-- the five rounds -/
  pending : c.ch.pending = D.r1 :: D.r2 :: D.r3 :: D.r4 :: D.r5 :: D.rest
  left : c'.ch.pending = D.rest
  vals1 : D.r1.vals = []
  gamma : x.gamma = D.r1.drawn.elems.map E.ofTriple
  gammaLen : x.gamma.length = S.table.v
  vals2 : D.r2.vals = []
  factor : (D.r2.drawn.elems.map E.ofTriple).drop (Send.cube c.st.codes (rowShape S)).bits =
    [D.beta]
  nz : isZeroE D.beta = false
  vals3 : D.r3.vals = [.answer D.y0.triple, .answer D.y1.triple]
  vals4 : D.r4.vals = []
  pos : D.pos = Positions.ofDraws S.table.code.logN D.r4.drawn.poss
  draws : D.pos.draws.size = S.columnsFirst + S.columnsFurther
  vals5 : D.r5.vals = []
  phi : x.phi = D.r5.drawn.elems.map E.ofTriple
  phiLen : x.phi.length = S.entryBits
  /-- what the block returns -/
  uFirst : x.first = ⟨c.st.oracles.size, vectorLay c.st.codes (rowShape S) S.rowsHigh⟩
  uFurther : x.further = ⟨c.st.oracles.size + 1, vectorLay c.st.codes (rowShape S) S.rowsHigh⟩
  group : x.group = c.st.groups.size
  mask : x.mask = if S.masksAhead = true then some (c.st.oracles.size + 2) else none
  /-- the rows -/
  form0 : Send.form c.st.codes (rowShape S) c.st.oracles.size
    ⟨(D.r2.drawn.elems.map E.ofTriple).take (Send.cube c.st.codes (rowShape S)).bits, D.beta⟩ 0 =
      some D.row0
  form1 : Send.form c.st.codes (rowShape S) (c.st.oracles.size + 1)
    ⟨(D.r2.drawn.elems.map E.ofTriple).take (Send.cube c.st.codes (rowShape S)).bits, D.beta⟩ 0 =
      some D.row1
  pad : Send.pad c.st.codes (rowShape S) = some D.places
  size0 : D.cols0.size = (storedList (linkStored S first false) D.pos).toArray.size
  rows0 : columnRows (S.side false 1) (foldeqWeights x.gamma) D.pos 0 x.first
    (storedList (linkStored S first false) D.pos).toArray D.cols0 = some D.rows0
  size1 : D.cols1.size = (storedList (linkStored S further true) D.pos).toArray.size
  rows1 : columnRows (S.side true 1) (foldeqWeights x.gamma) D.pos S.columnsFirst x.further
    (storedList (linkStored S further true) D.pos).toArray D.cols1 = some D.rows1
  eqRow : linkEqualityRow S x.phi x.first x.further S.cut = some D.rE
  /-- what the adding of the open rows has tested of them -/
  checked : ∀ r ∈ D.rE :: (D.rows0 ++ D.rows1), RowChecked c'.st r
  /-- what the run leaves -/
  st : c'.st = linkSt S c.st D.places { D.row0 with target := D.y0 } { D.row1 with target := D.y1 }
    D.rows0 D.rows1 D.rE
  laid : layTrees c.st.codes (linkMessage S 1) = some D.lay
  book : c'.book = bookSent c (linkMessage S 1) D.lay
  /-- the view's next opened columns were those of the first table, then those of the copy -/
  opened : c.ch.opened =
    viewColumns (Fmt.storedKey first.item) (storedList (linkStored S first false) D.pos).toArray
      D.cols0 ++
    (viewColumns (Fmt.storedKey further.item) (storedList (linkStored S further true) D.pos).toArray
      D.cols1 ++ c'.ch.opened)
  entries : c'.ch.entries = c.ch.entries.drop 5
  dry : c'.ch.dry = false
  failed : c'.failed = c.failed
  firstTree : c'.ch.firstTree = c.ch.firstTree
  samples : c'.ch.samples = c.ch.samples
  roots : c'.ch.roots = c.ch.roots + D.lay.shapes.size
  placed : c.st.oracles.size = c.book.place.size

/-! ## The statement after the steps, looked up -/

section
variable (S : LinkShape) (T : Statement) (places : List PadPlace) (s0 s1 : Row)
  (rows0 rows1 : List Row) (rE : Row)

/-- The codes are as before. -/
theorem linkSt_codes : (linkSt S T places s0 s1 rows0 rows1 rE).codes = T.codes := by
  unfold linkSt
  rw [(withRow_oracles _ _ _).2, (withRows_oracles _ _ _).2, (withRows_oracles _ _ _).2]
  rfl

/-- The link's group after the steps: the two oracle messages, and the rows as they were
made. -/
theorem linkSt_group :
    (linkSt S T places s0 s1 rows0 rows1 rE).groups[T.groups.size]? = some
      { code := S.code, maskCode := S.maskCode
        members := #[T.oracles.size, T.oracles.size + 1], kept := #[false, false]
        rows := ((#[] ++ rows0.toArray) ++ rows1.toArray).push rE } := by
  unfold linkSt
  have h0 : (admitted (admitted (stSent (withGroup T S.code S.maskCode) (linkMessage S 1))
      T.oracles.size (rowShape S) places #[s0]) (T.oracles.size + 1) (rowShape S) places
      #[s1]).groups[T.groups.size]? = some (linkGrp0 S) := by
    rw [(admitted_groups _ _ _ _ _).1, (admitted_groups _ _ _ _ _).1, (stSent_groups _ _).1,
      withGroup_group]
    rfl
  have h1 := joined_group _ T.groups.size T.oracles.size false _ h0
  have h2 := joined_group _ T.groups.size (T.oracles.size + 1) false (linkGrp1 S T.oracles.size) h1
  rw [withRow_group _ _ _ _ (withRows_group _ _ _ _ (withRows_group _ _ _ _ h2))]
  simp [linkGrp1, linkGrp0]

/-- The group as `linkSt_group` gives it. -/
def linkGrp (n0 : Nat) : Group :=
  { code := S.code, maskCode := S.maskCode, members := #[n0, n0 + 1], kept := #[false, false]
    rows := ((#[] ++ rows0.toArray) ++ rows1.toArray).push rE }

/-- A folded row's oracle message after the steps: sampled, with its one sample row, a member of
the link's group. -/
def linkOracle (g : Nat) (s : Row) : Oracle :=
  { shape := rowShape S, sampled := true, sampleRows := #[s]
    pad := places.map fun q => (q.part, q.index), ledger := freshLedger T.codes (rowShape S)
    groups := [g] }

/-- The first table's folded row's oracle message after the steps. -/
theorem linkSt_oracle0 :
    (linkSt S T places s0 s1 rows0 rows1 rE).oracles[T.oracles.size]? =
      some (linkOracle S T places T.groups.size s0) := by
  have q0 : (stSent (withGroup T S.code S.maskCode) (linkMessage S 1)).oracles[T.oracles.size]? =
      some { shape := rowShape S } := (linkSent_oracles S (withGroup T S.code S.maskCode)).1
  have hne : T.oracles.size + 1 ≠ T.oracles.size := Nat.succ_ne_self _
  unfold linkSt
  rw [(withRow_oracles _ _ _).1, (withRows_oracles _ _ _).1, (withRows_oracles _ _ _).1,
    joined_other _ _ _ _ _ _ hne,
    joined_same _ _ _ _ _ _ ((admitted_other _ _ _ _ _ _ hne).trans
      (admitted_same _ _ _ _ _ _ q0))]
  rfl

/-- The copy's folded row's oracle message after the steps. -/
theorem linkSt_oracle1 :
    (linkSt S T places s0 s1 rows0 rows1 rE).oracles[T.oracles.size + 1]? =
      some (linkOracle S T places T.groups.size s1) := by
  have q1 : (stSent (withGroup T S.code S.maskCode)
      (linkMessage S 1)).oracles[T.oracles.size + 1]? = some { shape := rowShape S } :=
    (linkSent_oracles S (withGroup T S.code S.maskCode)).2.1
  have hne : T.oracles.size ≠ T.oracles.size + 1 := (Nat.succ_ne_self _).symm
  unfold linkSt
  rw [(withRow_oracles _ _ _).1, (withRows_oracles _ _ _).1, (withRows_oracles _ _ _).1,
    joined_same _ _ _ _ _ _ ((joined_other _ _ _ _ _ _ hne).trans
      (admitted_same _ _ _ _ _ _ ((admitted_other _ _ _ _ _ _ hne).trans q1)))]
  rfl

/-- The rows that the proximity test on the link's group takes in: the equality row, the two
sample rows, the rows of the first table's draws, those of the copy's. -/
theorem linkSt_runRows (hE : rE.kind = .plain) (h0 : ∀ r ∈ rows0, r.kind = .generator)
    (h1 : ∀ r ∈ rows1, r.kind = .generator) :
    runRows (linkSt S T places s0 s1 rows0 rows1 rE) (linkGrp S rows0 rows1 rE T.oracles.size) =
      (rE :: s0 :: s1 :: (rows0 ++ rows1)).toArray := by
  have f0 : rows0.filter (fun x => x.kind == .plain) = [] :=
    List.filter_eq_nil_iff.2 fun r hr => by rw [h0 r hr]; decide
  have f1 : rows1.filter (fun x => x.kind == .plain) = [] :=
    List.filter_eq_nil_iff.2 fun r hr => by rw [h1 r hr]; decide
  have g0 : rows0.filter (fun x => x.kind == .generator) = rows0 :=
    List.filter_eq_self.2 fun r hr => by rw [h0 r hr]; rfl
  have g1 : rows1.filter (fun x => x.kind == .generator) = rows1 :=
    List.filter_eq_self.2 fun r hr => by rw [h1 r hr]; rfl
  unfold runRows linkGrp
  simp [linkSt_oracle0, linkSt_oracle1, linkOracle, f0, f1, g0, g1, hE]

end

end OnBytes.Slice

#print axioms OnBytes.Slice.linkSent_oracles
#print axioms OnBytes.Slice.linkSent_ids
#print axioms OnBytes.Slice.linkSent_todo
#print axioms OnBytes.Slice.linkSend_inv
#print axioms OnBytes.Slice.linkSent_at
#print axioms OnBytes.Slice.maskJoint
#print axioms OnBytes.Slice.groupTarget_inv
#print axioms OnBytes.Slice.linkSt_codes
#print axioms OnBytes.Slice.linkSt_group
#print axioms OnBytes.Slice.linkSt_oracle0
#print axioms OnBytes.Slice.linkSt_oracle1
#print axioms OnBytes.Slice.linkSt_runRows
