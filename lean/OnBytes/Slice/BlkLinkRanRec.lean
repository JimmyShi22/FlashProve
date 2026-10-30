-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/BlkLinkRanRec.lean: what a run of the steps of the program's link has done, for any
two keys.

OnBytes/Slice/BlkLinkRan.lean writes down what a run of the link's steps (OnBytes/Iop/Link.lean:
`linkStepsVerify`) on a view is to have done, at `S.table.answers = 0`. This file does it for
any two keys. Three things are new in the run's course. The test of a key's seeds says
something: no seed's factor is the program's 0 (three words 0: `isZeroE`; that it reads as no 0 in
the field asks besides that its words are below the prime: OnBytes/Slice/ManyBlkKeysRec.lean). Each
of the two calls by which a folded row's oracle message joins the link's group
(OnBytes/Iop/Foldeq.lean: `foldeqJoined`) adds one open row for each seed of its key. And two values
are kept as notes after the second of them, which changes nothing else. (The equality row's cut,
`S.cut`, is shorter by the pads; the field `eqRow` has it as the shape's number.) The number of
answers of a record is any number here; a sample of a folded row has one answer, as in
BlkLinkRan.lean.

The group's open rows are created in this order: the first table's record's rows, the copy's, the
rows of the first table's draws, those of the copy's, the equality row. A member joins between the
first two lists. Joining changes a group's members and adding a row changes its rows, so the two can
be exchanged (`joined_withRows`), and the statement after the steps is `linkSt` of BlkLinkRan.lean
with the records' rows laid before the rows of the first table's draws (`linkStR`). So that file's
look-ups of the group, of the two oracle messages and of the codes serve here as they are.

Main definitions.
 `recRowsR`               the rows of a key's record, one for each seed.
 `linkStR`                the statement after the steps.
 `LinkDataR`, `LinkRanR`  what a run of the steps takes of a view and makes of it; what it has done.
 `linkGrpR`               the group after the steps.
Main theorems.
 `foldeqRequire_invR`, `foldeqJoined_invR`   the two calls on a key, taken apart.
 `linkSteps_invR`    a run of the link's steps.
 `linkSt_groupR`     the group after the steps.
 `linkSt_runRowsR`   the rows that the test takes in: the first table's record's rows, the copy's,
                     the equality row, the two sample rows, the rows of the first table's draws,
                     those of the copy's.
Not claimed. Nothing for more than one answer to a sample of a folded row. Nothing on what a row's
coefficients are. Of what the call that adds an open row tests, `RowChecked` keeps the terms'
variables, the runs' steps and the forms' fit: nothing on a row's single entries, which a record's
row has, and nothing on the pads of the members' samples. The rows' kinds are hypotheses of
`linkSt_runRowsR`. Nothing on the dry run. Nothing on soundness.

-/
import OnBytes.Slice.BlkLinkRan

set_option autoImplicit false

namespace OnBytes.Slice

open Params (LinkShape FoldeqShape)

/-! ## The two calls on a key -/

/-- The rows of a key's record on a folded row: one for each seed, in the seeds' order. -/
def recRowsR (S : FoldeqShape) (key : TableKey) (eqGamma : Array E) (u : FoldedRow) :
    Option (List Row) :=
  key.seeds.zipIdx.mapM fun x => foldeqRecordRow S x.1 key.record x.2 eqGamma u

/-- The public conditions on a table's shape and key hold, no seed's factor is the program's 0
(three words 0: `isZeroE`; that it reads as no 0 in the field asks besides that its words are below
the prime: OnBytes/Slice/ManyBlkKeysRec.lean), and nothing changes. -/
theorem foldeqRequire_invR (key : TableKey) (S : FoldeqShape) (c c' : Ctx) (hd : c.ch.dry = false)
    (h : (foldeqRequire key S).Yields c () c') :
    foldeqOk c.st.codes S = true ∧ key.fits S.index = true ∧
      (key.seeds.all fun x => !isZeroE x.beta) = true ∧ c' = c := by
  unfold foldeqRequire at h
  obtain ⟨st, c1, h1, a1⟩ := (Blk.yields_bind _ _ _ _ _).1 h
  obtain ⟨eS, e1⟩ := (Blk.yields_statement _ _ _).1 h1
  obtain ⟨_, c2, h2, a2⟩ := (Blk.yields_bind _ _ _ _ _).1 a1
  obtain ⟨k2, e2⟩ := (Blk.yields_must _ _ _).1 h2
  obtain ⟨_, c3, h3, a3⟩ := (Blk.yields_bind _ _ _ _ _).1 a2
  obtain ⟨k3, e3⟩ := (Blk.yields_must _ _ _).1 h3
  have e3' : c3 = c := e3.trans (e2.trans e1)
  rw [e3'] at a3
  obtain ⟨k4, e4⟩ := (Blk.yields_test _ _ _ hd).1 a3
  rw [eS] at k2
  exact ⟨k2, k3, k4, e4⟩

/-- A folded row's oracle message joins its group, for any key: the rows of the key's record are
there, they have passed those tests of the call that adds an open row which `RowChecked` keeps, and
they are appended to the group's rows. -/
theorem foldeqJoined_invR (S : FoldeqShape) (key : TableKey) (eqGamma : Array E) (oracle g : Nat)
    (u : FoldedRow) (c c' : Ctx) (hd : c.ch.dry = false)
    (h : (foldeqJoined S key eqGamma oracle g).Yields c u c') :
    u = ⟨oracle, vectorLay c.st.codes S.u S.rowsHigh⟩ ∧
      ∃ G x l, c.st.groups[g]? = some G ∧ c.st.oracles[oracle]? = some x ∧
        recRowsR S key eqGamma u = some l ∧
        (∀ r ∈ l, RowChecked (withMessageInGroup c.st g oracle false G) r) ∧
        c' = { c with st := withRows (withMessageInGroup c.st g oracle false G) g l } := by
  unfold foldeqJoined at h
  obtain ⟨st, c1, h1, a1⟩ := (Blk.yields_bind _ _ _ _ _).1 h
  obtain ⟨eS, e1⟩ := (Blk.yields_statement _ _ _).1 h1
  obtain ⟨_, c2, h2, a2⟩ := (Blk.yields_bind _ _ _ _ _).1 a1
  rw [e1] at h2
  obtain ⟨G, x, k1, k2, _, _, _, e2⟩ := join_inv _ _ _ _ _ h2
  obtain ⟨_, c3, h3, a3⟩ := (Blk.yields_bind _ _ _ _ _).1 a2
  have hd2 : c2.ch.dry = false := by rw [e2]; exact hd
  obtain ⟨l, k3, k4, e3⟩ := addRowsOnView_inv _ _ _ _ hd2 h3
  obtain ⟨e4, e5⟩ := (Blk.yields_pure _ _ _ _).1 a3
  refine ⟨by rw [e4, eS], G, x, l, k1, k2, by rw [e4]; exact k3, fun r hr => ?_, ?_⟩
  · have k5 := (k4 r hr).2
    rw [e2] at k5
    exact k5
  · rw [e5, e3, e2]

/-! ## Joining a group and adding rows to it -/

/-- Rows added in two turns are the rows of the two lists, added in one. -/
theorem withRows_append (S : Statement) (g : Nat) (a b : List Row) :
    withRows S g (a ++ b) = withRows (withRows S g a) g b := List.foldl_append

/-- Of the group before it, the statement after a joining takes the members alone. -/
theorem joined_members (S : Statement) (g o : Nat) (k : Bool) {G G' : Group}
    (h : G.members = G'.members) : withMessageInGroup S g o k G = withMessageInGroup S g o k G' := by
  unfold withMessageInGroup
  rw [h]

/-- A new row and a new member of a group can be exchanged. -/
theorem joined_withRow (S : Statement) (g o : Nat) (k : Bool) (G : Group) (r : Row) :
    withMessageInGroup (withRow S g r) g o k G = withRow (withMessageInGroup S g o k G) g r := by
  have hg : ∀ (A : Array Group) (f1 f2 : Group → Group), (∀ X, f2 (f1 X) = f1 (f2 X)) →
      (A.modify g f1).modify g f2 = (A.modify g f2).modify g f1 := by
    intro A f1 f2 hf
    apply Array.ext_getElem?
    intro i
    simp only [Array.getElem?_modify]
    by_cases hi : g = i
    · simp only [if_pos hi]
      cases A[i]? with
      | none => rfl
      | some X => exact congrArg some (hf X)
    · simp only [if_neg hi]
  unfold withMessageInGroup withRow
  simp only
  congr 1
  refine hg _ _ _ ?_
  intro X
  rfl

/-- New rows and a new member of a group can be exchanged. -/
theorem joined_withRows (g o : Nat) (k : Bool) (G : Group) : ∀ (l : List Row) (S : Statement),
    withMessageInGroup (withRows S g l) g o k G = withRows (withMessageInGroup S g o k G) g l
  | [], _ => rfl
  | r :: l, S => by
    show withMessageInGroup (withRows (withRow S g r) g l) g o k G =
      withRows (withRow (withMessageInGroup S g o k G) g r) g l
    rw [joined_withRows g o k G l, joined_withRow]

/-- A new member of a group changes no table's number of index bits. -/
theorem joined_tableBits (S : Statement) (g o : Nat) (k : Bool) (G : Group) (o' : Nat)
    (part : Part) : (withMessageInGroup S g o k G).tableBits o' part = S.tableBits o' part := by
  unfold Statement.tableBits Statement.rowBits Statement.placeBits withMessageInGroup
  simp only [Array.getElem?_modify]
  by_cases hi : o = o'
  · simp only [if_pos hi]
    cases S.oracles[o']? <;> rfl
  · simp only [if_neg hi]

/-- What was tested of a row holds after a new member has joined a group. -/
theorem RowChecked.joinedR {S : Statement} {row : Row} (h : RowChecked S row) (g o : Nat) (k : Bool)
    (G : Group) : RowChecked (withMessageInGroup S g o k G) row :=
  ⟨fun t ht => (h.terms t ht).trans (joined_tableBits _ _ _ _ _ _ _).symm, h.runs,
    fun f hf => by rw [joined_tableBits]; exact h.forms f hf⟩

/-! ## The steps of the link -/

/-- The statement after the link's steps, from the statement T before them. places: the pad of
a folded row's oracle message; s0, s1: the two sample rows; rec0, rec1: the rows of the two tables'
records; rows0, rows1: the rows of the two tables' draws; rE: the equality row. The group's open
rows stand in the order in which the program creates them. -/
def linkStR (S : LinkShape) (T : Statement) (places : List PadPlace) (s0 s1 : Row)
    (rec0 rec1 rows0 rows1 : List Row) (rE : Row) : Statement :=
  linkSt S T places s0 s1 (rec0 ++ (rec1 ++ rows0)) rows1 rE

/-- What a run of the link's steps takes of a view and makes of it. -/
structure LinkDataR extends LinkData where
  /-- the rows of the first table's record, and of the copy's -/
  rec0 : List Row
  rec1 : List Row

/-- What a run of the link's steps, on a view, has done, for any two keys and
one answer to a sample of a folded row. -/
structure LinkRanR (S : LinkShape) (first further : TableKey) (c c' : Ctx) (x : LinkRun)
    (D : LinkDataR) : Prop where
  ok : linkOk c.st.codes S 1 = true
  /-- the two keys: their sizes fit the tables' shape, and no seed's factor is the program's 0
  (three words 0: `isZeroE`; that it reads as no 0 in the field asks besides that its words are
  below the prime: OnBytes/Slice/ManyBlkKeysRec.lean) -/
  fits0 : first.fits S.table = true
  fits1 : further.fits S.table = true
  nz0 : (first.seeds.all fun s => !isZeroE s.beta) = true
  nz1 : (further.seeds.all fun s => !isZeroE s.beta) = true
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
  rec0 : recRowsR (S.side false 1) first (foldeqWeights x.gamma) x.first = some D.rec0
  rec1 : recRowsR (S.side true 1) further (foldeqWeights x.gamma) x.further = some D.rec1
  size0 : D.cols0.size = (storedList (linkStored S first false) D.pos).toArray.size
  rows0 : columnRows (S.side false 1) (foldeqWeights x.gamma) D.pos 0 x.first
    (storedList (linkStored S first false) D.pos).toArray D.cols0 = some D.rows0
  size1 : D.cols1.size = (storedList (linkStored S further true) D.pos).toArray.size
  rows1 : columnRows (S.side true 1) (foldeqWeights x.gamma) D.pos S.columnsFirst x.further
    (storedList (linkStored S further true) D.pos).toArray D.cols1 = some D.rows1
  eqRow : linkEqualityRow S x.phi x.first x.further S.cut = some D.rE
  /-- what `RowChecked` keeps of the tests that the adding of the open rows has made of them -/
  checked : ∀ r ∈ D.rE :: (D.rec0 ++ (D.rec1 ++ (D.rows0 ++ D.rows1))), RowChecked c'.st r
  /-- what the run leaves -/
  st : c'.st = linkStR S c.st D.places { D.row0 with target := D.y0 }
    { D.row1 with target := D.y1 } D.rec0 D.rec1 D.rows0 D.rows1 D.rE
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

/-- A run of the link's steps, taken apart: for any two keys. -/
theorem linkSteps_invR (S : LinkShape) (first further : TableKey) (x : LinkRun) (c c' : Ctx)
    (hd : c.ch.dry = false) (hs : c.ch.samples = 1)
    (h : (linkStepsVerify S first further).Yields c x c') :
    ∃ D, LinkRanR S first further c c' x D := by
  unfold linkStepsVerify at h
  obtain ⟨n, b1, h1, a1⟩ := (Blk.yields_bind _ _ _ _ _).1 h
  obtain ⟨en, e1⟩ := (yields_samples _ _ _).1 h1
  rw [hs] at en
  subst en
  obtain ⟨st, b2, h2, a2⟩ := (Blk.yields_bind _ _ _ _ _).1 a1
  obtain ⟨est, e2⟩ := (Blk.yields_statement _ _ _).1 h2
  obtain ⟨_, b3, h3, a3⟩ := (Blk.yields_bind _ _ _ _ _).1 a2
  obtain ⟨kok, e3⟩ := (Blk.yields_must _ _ _).1 h3
  have e3' : b3 = c := e3.trans (e2.trans e1)
  rw [est, e1] at kok
  obtain ⟨_, b4, h4, a4⟩ := (Blk.yields_bind _ _ _ _ _).1 a3
  rw [e3'] at h4
  obtain ⟨_, kf0, kz0, e4⟩ := foldeqRequire_invR _ _ _ _ hd h4
  obtain ⟨_, b5, h5, a5⟩ := (Blk.yields_bind _ _ _ _ _).1 a4
  rw [e4] at h5
  obtain ⟨_, kf1, kz1, e5⟩ := foldeqRequire_invR _ _ _ _ hd h5
  -- the fold point
  obtain ⟨gamma, cG, h6, a6⟩ := (Blk.yields_bind _ _ _ _ _).1 a5
  rw [e5] at h6
  obtain ⟨dG, kG, eg, lg⟩ := drawPoint_inv _ _ _ _ _ h6
  obtain ⟨eG, esG, r1, rest1, g1, _, _, g4, g5, edG, _, _, _, g9, g10, _, g12, g13, g14, g15, g16,
    g17, g18, g19⟩ := Blk.close_inv _ _ _ _ _ _ hd kG
  -- the group
  obtain ⟨group, cN, h7, a7⟩ := (Blk.yields_bind _ _ _ _ _).1 a6
  obtain ⟨egr, eN⟩ := newGroup_inv _ _ _ _ _ h7
  have hdN : cN.ch.dry = false := by rw [eN]; exact g15
  -- the sending
  obtain ⟨ids, cS, h8, a8⟩ := (Blk.yields_bind _ _ _ _ _).1 a7
  obtain ⟨lay, beta, y0, y1, row0, row1, places, r2, r3, rest3, LS⟩ :=
    linkSend_inv S ids cN cS hdN h8
  obtain ⟨mask, km, a9⟩ := maskJoint _ _ _ _ _ _ a8
  -- the two oracle messages join the group
  obtain ⟨o0, b9, h9, a10⟩ := (Blk.yields_bind _ _ _ _ _).1 a9
  obtain ⟨ko0, e9⟩ := (Blk.yields_get _ _ _ _).1 h9
  obtain ⟨u0, cJ0, h10, a11⟩ := (Blk.yields_bind _ _ _ _ _).1 a10
  rw [e9] at h10
  obtain ⟨eu0, G0, x0, rec0, j1, _, kr0, chr0, eJ0⟩ :=
    foldeqJoined_invR _ _ _ _ _ _ _ _ LS.dry h10
  have hdJ0 : cJ0.ch.dry = false := by rw [eJ0]; exact LS.dry
  obtain ⟨o1, b11, h11, a12⟩ := (Blk.yields_bind _ _ _ _ _).1 a11
  obtain ⟨ko1, e11⟩ := (Blk.yields_get _ _ _ _).1 h11
  obtain ⟨u1, cJ1, h12, a13⟩ := (Blk.yields_bind _ _ _ _ _).1 a12
  rw [e11] at h12
  obtain ⟨eu1, G1, x1, rec1, j3, _, kr1, chr1, eJ1⟩ :=
    foldeqJoined_invR _ _ _ _ _ _ _ _ hdJ0 h12
  have hdJ1 : cJ1.ch.dry = false := by rw [eJ1]; exact hdJ0
  -- two values of the records are kept
  obtain ⟨cM, NM, a14⟩ : ∃ c1, Blk.SameButNotes cJ1 c1 ∧ _ := by
    obtain ⟨_, n1, k1, hA⟩ := (Blk.yields_bind _ _ _ _ _).1 a13
    obtain ⟨_, n2, k2, hA⟩ := (Blk.yields_bind _ _ _ _ _).1 hA
    obtain ⟨_, n3, k3, hA⟩ := (Blk.yields_bind _ _ _ _ _).1 hA
    obtain ⟨_, n4, k4, hA⟩ := (Blk.yields_bind _ _ _ _ _).1 hA
    have q1 := groupTarget_inv _ _ _ _ _ k1
    have q2 := Blk.yields_note _ _ _ _ k2
    have q3 := groupTarget_inv _ _ _ _ _ k3
    have q4 := Blk.yields_note _ _ _ _ k4
    rw [q1] at q2
    rw [q3] at q4
    exact ⟨n4, sameButNotes_trans q2 q4, hA⟩
  have hdM : cM.ch.dry = false := by rw [NM.ch]; exact hdJ1
  -- the positions
  obtain ⟨drawn, cP, h15, a15⟩ := (Blk.yields_bind _ _ _ _ _).1 a14
  obtain ⟨dP, eP, kP, _, _, _, edr⟩ := closePositions_inv _ _ _ _ _ h15
  obtain ⟨eP', esP, r4, rest4, p1, _, _, p4, p5, edP, _, _, _, p9, p10, _, p12, p13, p14, p15, p16,
    p17, p18, p19⟩ := Blk.close_inv _ _ _ _ _ _ hdM kP
  obtain ⟨_, b16, h16, a16⟩ := (Blk.yields_bind _ _ _ _ _).1 a15
  obtain ⟨kdr, e16⟩ := (Blk.yields_must _ _ _).1 h16
  obtain ⟨Gq, b17, h17, a17⟩ := (Blk.yields_bind _ _ _ _ _).1 a16
  obtain ⟨_, e17⟩ := (yields_group _ _ _ _).1 h17
  have e17' : b17 = cP := e17.trans e16
  -- the columns
  obtain ⟨_, cK0, h18, a18⟩ := (Blk.yields_bind _ _ _ _ _).1 a17
  rw [e17'] at h18
  obtain ⟨q0, rows0, cR0, s0, t0, chk0, N0⟩ := foldeqColumnsVerify_inv _ _ _ _ _ _ _ _ _ p15 h18
  obtain ⟨vx, vo, vs, vF, vb⟩ := Blk.readStored_inv _ _ q0.1 q0.2 _ _ p15 s0
  have cK0' : cK0.ch = cR0.ch := N0.ch
  have hdK0 : cK0.ch.dry = false := by rw [cK0']; exact vF.dry.trans p15
  obtain ⟨_, cK1, h19, a19⟩ := (Blk.yields_bind _ _ _ _ _).1 a18
  obtain ⟨q1, rows1, cR1, s1, t1, chk1, N1⟩ :=
    foldeqColumnsVerify_inv _ _ _ _ _ _ _ _ _ hdK0 h19
  obtain ⟨wx, wo, ws, wF, wb⟩ := Blk.readStored_inv _ _ q1.1 q1.2 _ _ hdK0 s1
  -- note, twice
  obtain ⟨_, b20, h20, a20⟩ := (Blk.yields_bind _ _ _ _ _).1 a19
  have e20 := groupTarget_inv _ _ _ _ _ h20
  obtain ⟨_, b21, h21, a21⟩ := (Blk.yields_bind _ _ _ _ _).1 a20
  have N2 := Blk.yields_note _ _ _ _ h21
  obtain ⟨_, b22, h22, a22⟩ := (Blk.yields_bind _ _ _ _ _).1 a21
  have e22 := groupTarget_inv _ _ _ _ _ h22
  obtain ⟨_, b23, h23, a23⟩ := (Blk.yields_bind _ _ _ _ _).1 a22
  have N3 := Blk.yields_note _ _ _ _ h23
  -- the point of comparison
  obtain ⟨phi, cF, h24, a24⟩ := (Blk.yields_bind _ _ _ _ _).1 a23
  obtain ⟨dF, kF, ef, lf⟩ := drawPoint_inv _ _ _ _ _ h24
  -- the context before that round, part by part
  have c23 : b23.ch = cR1.ch := by rw [N3.ch, e22, N2.ch, e20, N1.ch]
  have s23 : b23.st = withRows cR1.st group rows1 := by rw [N3.st, e22, N2.st, e20, N1.st]
  have k23 : b23.book = cR1.book := by rw [N3.book, e22, N2.book, e20, N1.book]
  have f23 : b23.failed = cR1.failed := by rw [N3.failed, e22, N2.failed, e20, N1.failed]
  have hd23 : b23.ch.dry = false := by rw [c23]; exact wF.dry.trans hdK0
  obtain ⟨eF, esF, r5, rest5, f1, _, _, f4, f5, edF, _, _, _, f9, f10, _, f12, f13, f14, f15, f16,
    f17, f18, f19⟩ := Blk.close_inv _ _ _ _ _ _ hd23 kF
  -- the equality row
  obtain ⟨rE, b25, h25, a25⟩ := (Blk.yields_bind _ _ _ _ _).1 a24
  obtain ⟨krE, e25⟩ := (Blk.yields_get _ _ _ _).1 h25
  obtain ⟨_, cE, h26, a26⟩ := (Blk.yields_bind _ _ _ _ _).1 a25
  rw [e25] at h26
  obtain ⟨_, chkE, eE⟩ := addRow_inv _ _ _ _ f15 h26
  obtain ⟨_, b27, h27, a27⟩ := (Blk.yields_bind _ _ _ _ _).1 a26
  have N4 := Blk.yields_note _ _ _ _ h27
  obtain ⟨ex, e28⟩ := (Blk.yields_pure _ _ _ _).1 a27
  -- numbers and names
  have sN : cN.st = withGroup c.st S.code S.maskCode := by rw [eN, g12]
  have oN : cN.st.oracles.size = c.st.oracles.size := by rw [sN]; rfl
  have cdN : cN.st.codes = c.st.codes := by rw [sN]; rfl
  have hgr : group = c.st.groups.size := by rw [egr, g12]
  obtain ⟨i0, i1, i2⟩ := linkSent_at S c.st.oracles.size
  have hids := LS.numbers
  rw [oN] at hids
  have ho0 : o0 = c.st.oracles.size := by
    rw [hids, i0] at ko0
    exact (Option.some.inj ko0).symm
  have ho1 : o1 = c.st.oracles.size + 1 := by
    rw [hids, i1] at ko1
    exact (Option.some.inj ko1).symm
  have sS := LS.st
  rw [oN, sN] at sS
  have hG0 : G0 = linkGrp0 S := by
    rw [sS, (admitted_groups _ _ _ _ _).1, (admitted_groups _ _ _ _ _).1, (stSent_groups _ _).1,
      hgr, withGroup_group] at j1
    exact (Option.some.inj j1).symm
  have sJ0 : cJ0.st = withRows (withMessageInGroup cS.st group o0 false G0) group rec0 := by rw [eJ0]
  have hG1 : G1.members = (linkGrp1 S c.st.oracles.size).members := by
    rw [sJ0, withRows_group _ _ _ _ (joined_group _ _ _ _ _ j1), hG0, ho0] at j3
    rw [← Option.some.inj j3]
    rfl
  have sJ1 : cJ1.st = withRows (withMessageInGroup cJ0.st group o1 false G1) group rec1 := by rw [eJ1]
  have cdS : cS.st.codes = c.st.codes := by rw [sS]; rfl
  have cdJ0 : cJ0.st.codes = c.st.codes := by
    rw [sJ0, (withRows_oracles _ _ _).2]
    exact cdS
  -- the rounds
  have hpN : cN.ch.pending = rest1 := by rw [eN]; exact g9
  have hr1 : rest1 = r2 :: r3 :: rest3 := hpN.symm.trans LS.pending
  have hpJ1 : cM.ch.pending = rest3 := by rw [NM.ch, eJ1, eJ0]; exact LS.left
  have hr3 : rest3 = r4 :: rest4 := hpJ1.symm.trans p4
  have hp23 : b23.ch.pending = rest4 := by
    rw [c23, wF.pending, cK0', vF.pending]
    exact p9
  have hr4 : rest4 = r5 :: rest5 := hp23.symm.trans f4
  have ec' : c' = b27 := e28
  have chE : b27.ch = cF.ch := by rw [N4.ch, eE]
  -- the opened columns
  have hoP : cP.ch.opened = c.ch.opened := by
    rw [p16, NM.ch, eJ1, eJ0]
    show cS.ch.opened = _
    rw [LS.opened, eN]
    exact g16
  rw [hoP, vx] at vo
  rw [cK0', wx] at wo
  rw [vx] at t0 vs
  rw [wx] at t1 ws
  -- the plan's entries
  have hen : c'.ch.entries = c.ch.entries.drop 5 := by
    have z1 : cN.ch.entries = esG := by rw [eN]; exact g10
    have z2 : esG.drop 2 = eP' :: esP := by
      rw [← z1, ← LS.entries, ← p1, NM.ch, eJ1, eJ0]
    have z3 : esP = eF :: esF := by
      rw [← p10, ← f1, c23, wF.entries, cK0', vF.entries]
    rw [ec', chE, f10, g1, List.drop_succ_cons, show (4 : Nat) = 2 + 2 from rfl, ← List.drop_drop,
      z2, z3]
    rfl
  -- what was tested of the open rows, in the last statement
  have sR0 : cR0.st = cP.st := vF.st
  have sR1 : cR1.st = withRows cP.st group rows0 := by
    rw [wF.st, N0.st]
    show withRows cR0.st group rows0 = _
    rw [sR0]
  have sF : cF.st = withRows (withRows cP.st group rows0) group rows1 := by rw [f12, s23, sR1]
  have sC : c'.st = withRow cF.st group rE := by rw [ec', N4.st, eE]
  have oR1 : cR1.st.oracles = cP.st.oracles ∧ cR1.st.codes = cP.st.codes := by
    rw [sR1]
    exact withRows_oracles _ _ _
  have oF : cF.st.oracles = cP.st.oracles ∧ cF.st.codes = cP.st.codes := by
    rw [sF]
    exact ⟨(withRows_oracles _ _ _).1.trans (withRows_oracles _ _ _).1,
      (withRows_oracles _ _ _).2.trans (withRows_oracles _ _ _).2⟩
  have oC : c'.st.oracles = cF.st.oracles ∧ c'.st.codes = cF.st.codes := by
    rw [sC]
    exact withRow_oracles _ _ _
  have oP1 : cP.st.oracles = (withMessageInGroup cJ0.st group o1 false G1).oracles ∧
      cP.st.codes = (withMessageInGroup cJ0.st group o1 false G1).codes := by
    rw [p12, NM.st, sJ1]
    exact withRows_oracles _ _ _
  have oJ0 : cJ0.st.oracles = (withMessageInGroup cS.st group o0 false G0).oracles ∧
      cJ0.st.codes = (withMessageInGroup cS.st group o0 false G0).codes := by
    rw [sJ0]
    exact withRows_oracles _ _ _
  have hchk : ∀ r ∈ rE :: (rec0 ++ (rec1 ++ (rows0 ++ rows1))), RowChecked c'.st r := by
    intro r hr
    rcases List.mem_cons.1 hr with rfl | hr
    · exact chkE.congr oC.1 oC.2
    · rcases List.mem_append.1 hr with hr | hr
      · exact (((chr0 r hr).congr oJ0.1 oJ0.2).joinedR group o1 false G1).congr
          (oC.1.trans (oF.1.trans oP1.1)) (oC.2.trans (oF.2.trans oP1.2))
      · rcases List.mem_append.1 hr with hr | hr
        · exact (chr1 r hr).congr (oC.1.trans (oF.1.trans oP1.1)) (oC.2.trans (oF.2.trans oP1.2))
        · rcases List.mem_append.1 hr with hr | hr
          · exact (chk0 r hr).congr (oC.1.trans (oF.1.trans (congrArg (·.oracles) sR0).symm))
              (oC.2.trans (oF.2.trans (congrArg (·.codes) sR0).symm))
          · exact (chk1 r hr).congr (oC.1.trans (oF.1.trans oR1.1.symm))
              (oC.2.trans (oF.2.trans oR1.2.symm))
  subst ex
  refine ⟨⟨⟨r1, r2, r3, r4, r5, rest5, lay, beta, y0, y1, row0, row1, places, drawn.1, q0.2, q1.2,
    rows0, rows1, rE⟩, rec0, rec1⟩, ?_⟩
  have hfac := LS.factor
  have hf0 := LS.form0
  have hf1 := LS.form1
  have hpad := LS.pad
  have hlaid := LS.laid
  rw [cdN] at hfac hf0 hf1 hpad hlaid
  rw [oN] at hf0 hf1
  simp only [Bool.and_eq_true, beq_iff_eq] at kdr
  exact
    { ok := kok
      fits0 := kf0
      fits1 := kf1
      nz0 := kz0
      nz1 := kz1
      rec0 := kr0
      rec1 := kr1
      pending := by
        show c.ch.pending = r1 :: r2 :: r3 :: r4 :: r5 :: rest5
        rw [g4, hr1, hr3, hr4]
      left := by
        show c'.ch.pending = rest5
        rw [ec', chE]
        exact f9
      vals1 := g5
      gamma := by
        show gamma = r1.drawn.elems.map E.ofTriple
        rw [eg, edG]
      gammaLen := lg
      vals2 := LS.vals2
      factor := hfac
      nz := LS.nz
      vals3 := LS.vals3
      vals4 := p5
      pos := by
        show drawn.1 = _
        rw [edr, edP]
      draws := kdr.2
      vals5 := f5
      phi := by
        show phi = r5.drawn.elems.map E.ofTriple
        rw [ef, edF]
      phiLen := lf
      uFirst := by
        show u0 = _
        rw [eu0, ho0, cdS]
        rfl
      uFurther := by
        show u1 = _
        rw [eu1, ho1, cdJ0]
        rfl
      group := hgr
      mask := by
        show mask = _
        rw [hids, i2] at km
        cases hm : S.masksAhead
        · rw [hm] at km
          exact km
        · rw [hm] at km
          exact km.1.symm
      form0 := hf0
      form1 := hf1
      pad := hpad
      size0 := vs
      rows0 := t0
      size1 := ws
      rows1 := t1
      eqRow := krE
      checked := hchk
      st := by
        rw [sC, sF, p12, NM.st, sJ1, sJ0, joined_withRows, joined_members _ _ _ _ hG1, sS, hG0, ho0,
          ho1, hgr]
        unfold linkStR linkSt
        rw [withRows_append, withRows_append]
      laid := hlaid
      book := by
        rw [ec', N4.book, eE]
        show cF.book = _
        rw [f13, k23, wb, N0.book]
        show cR0.book = _
        rw [vb, p13, NM.book, eJ1, eJ0]
        show cS.book = _
        rw [LS.book]
        unfold bookSent
        rw [oN, eN]
        show _ = _
        rw [g13, g18, g17]
      opened := by
        rw [ec', chE, f16, c23]
        exact vo.trans (congrArg (HAppend.hAppend _) wo)
      entries := hen
      dry := by
        rw [ec', chE]
        exact f15
      failed := by
        rw [ec', N4.failed, eE]
        show cF.failed = _
        rw [f14, f23, wF.failed, N0.failed]
        show cR0.failed = _
        rw [vF.failed, p14, NM.failed, eJ1, eJ0]
        show cS.failed = _
        rw [LS.failed, eN]
        exact g14
      firstTree := by
        rw [ec', chE, f18, c23, wF.firstTree, cK0', vF.firstTree, p18, NM.ch, eJ1,
          eJ0]
        show cS.ch.firstTree = _
        rw [LS.firstTree, eN]
        exact g18
      samples := by
        rw [ec', chE, f19, c23, wF.samples, cK0', vF.samples, p19, NM.ch, eJ1, eJ0]
        show cS.ch.samples = _
        rw [LS.samples, eN]
        exact g19
      roots := by
        rw [ec', chE, f17, c23, wF.roots, cK0', vF.roots, p17, NM.ch, eJ1, eJ0]
        show cS.ch.roots = _
        rw [LS.roots, eN]
        show cG.ch.roots + _ = _
        rw [g17]
      placed := by
        have h := LS.placed
        rw [oN, eN] at h
        exact h.trans (congrArg (·.place.size) g13) }

/-! ## The statement after the steps, looked up -/

section
variable (S : LinkShape) (T : Statement) (places : List PadPlace) (s0 s1 : Row)
  (rec0 rec1 rows0 rows1 : List Row) (rE : Row)

/-- The link's group after the steps. -/
def linkGrpR (n0 : Nat) : Group := linkGrp S (rec0 ++ (rec1 ++ rows0)) rows1 rE n0

/-- The link's group after the steps: the two oracle messages, and the rows as they were made. -/
theorem linkSt_groupR :
    (linkStR S T places s0 s1 rec0 rec1 rows0 rows1 rE).groups[T.groups.size]? =
      some (linkGrpR S rec0 rec1 rows0 rows1 rE T.oracles.size) :=
  linkSt_group S T places s0 s1 _ rows1 rE

/-- The rows that the proximity test on the link's group takes in: the rows of the first table's
record, those of the copy's, the equality row, the two sample rows, the rows of the first table's
draws, those of the copy's. -/
theorem linkSt_runRowsR (hE : rE.kind = .plain) (hr0 : ∀ r ∈ rec0, r.kind = .plain)
    (hr1 : ∀ r ∈ rec1, r.kind = .plain) (h0 : ∀ r ∈ rows0, r.kind = .generator)
    (h1 : ∀ r ∈ rows1, r.kind = .generator) :
    runRows (linkStR S T places s0 s1 rec0 rec1 rows0 rows1 rE)
        (linkGrpR S rec0 rec1 rows0 rows1 rE T.oracles.size) =
      (rec0 ++ (rec1 ++ rE :: s0 :: s1 :: (rows0 ++ rows1))).toArray := by
  have f0 : rows0.filter (fun x => x.kind == .plain) = [] :=
    List.filter_eq_nil_iff.2 fun r hr => by rw [h0 r hr]; decide
  have f1 : rows1.filter (fun x => x.kind == .plain) = [] :=
    List.filter_eq_nil_iff.2 fun r hr => by rw [h1 r hr]; decide
  have g0 : rows0.filter (fun x => x.kind == .generator) = rows0 :=
    List.filter_eq_self.2 fun r hr => by rw [h0 r hr]; rfl
  have g1 : rows1.filter (fun x => x.kind == .generator) = rows1 :=
    List.filter_eq_self.2 fun r hr => by rw [h1 r hr]; rfl
  have p0 : rec0.filter (fun x => x.kind == .plain) = rec0 :=
    List.filter_eq_self.2 fun r hr => by rw [hr0 r hr]; rfl
  have p1 : rec1.filter (fun x => x.kind == .plain) = rec1 :=
    List.filter_eq_self.2 fun r hr => by rw [hr1 r hr]; rfl
  have q0 : rec0.filter (fun x => x.kind == .generator) = [] :=
    List.filter_eq_nil_iff.2 fun r hr => by rw [hr0 r hr]; decide
  have q1 : rec1.filter (fun x => x.kind == .generator) = [] :=
    List.filter_eq_nil_iff.2 fun r hr => by rw [hr1 r hr]; decide
  unfold runRows linkStR linkGrpR linkGrp
  simp [linkSt_oracle0, linkSt_oracle1, linkOracle, f0, f1, g0, g1, p0, p1, q0, q1, hE]

end

end OnBytes.Slice
