-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/BlkCsRun.lean: a run of the program's code switch, taken apart.

The program's code switch (OnBytes/Iop/Cs.lean: `csVerify`) is a block: a sequence of calls that
change what the verifier holds. A run on a view (`c.ch.dry = false`) takes a proof's rounds and
opened columns as data (`Fmt.View`); nothing here asks where they come from. This file says what a
run of that block on a view has done, call by call, with no arithmetic: which rounds of the view it
has taken and what these rounds held, which pure functions it has applied to what, and what it has
left.

The case that is treated: no kept member (a member of the old group whose main rows are not folded
with the others; at a switch a further oracle message takes its rows); one answer to the sample of
the new oracle message; any other oracle messages in the same prover's message, if they are not
sampled (a fold's fresh mask or the last step's masking word can be sent there).

The result, `csVerify_inv`. There are an element theta and a record D (`CsTaken`) of what the run
has taken and made, such that `CsRan` holds:
 - the first round sent roots alone and drew a point and one factor other than 0; the second sent
   one answer and drew positions and theta; the plan's entries have the names of these rounds;
 - the new oracle message has the next free number; its sample row is `Send.form` at the seed, with
   the answer as its target;
 - the old rows were read at the drawn positions (the run of that call is shown as it is, with the
   statement, the book of trees and the opened columns from which it starts);
 - the claims are `switchRows` of the symbols read, in the statement in which the new oracle
   message has joined its group;
 - the row that is returned is `Bat.combine`, at theta, of the group's rows in their fixed order;
 - what is left: the statement, the book, the rounds and entries after the two, the counts.
`CsTaken.runRows_fresh` gives the fixed order for a group that had no member and no row: the plain
rows among the claims, the sample row, the generator rows.

Main definitions: `ledgerShut`, `sentOf`, `CsTaken` (with `z`, `sample`, `stA`, `stJ`, `stR`,
`grown`), `CsRan`.
Main theorems: `singleRowsRead_inv`, `singleRowsRead_frame`, `todo_one`, `sendOne_inv`,
`switchAdmit_inv`, `switchVerify_inv`, `csVerify_inv`, `CsRan.group0`, `CsTaken.runRows_fresh`.
Not claimed. What the sample row's, the claims' or the combined row's coefficients are. Nothing on
the dry run (`Blk.rounds`, which runs a block on no proof to describe its rounds). Nothing on
soundness.
-/
import OnBytes.Iop.Cs
import OnBytes.Iop.OpenLaws
import OnBytes.Slice.BlkCalls
import OnBytes.Slice.BlkSendRun
import OnBytes.Slice.BlkStLaws

set_option autoImplicit false

namespace OnBytes.Slice

/-! ## What reading the old rows leaves as it was -/

/-- A run of the reading of a complex of single rows: the columns of its oracle messages are read,
and the symbols are made of them. -/
theorem singleRowsRead_inv (s : SingleRows) (pos : Positions) (y : Array E) (c c' : Ctx)
    (h : (singleRowsRead s pos).Yields c y c') :
    ∃ opened, (Blk.readOpened (singleRowsOracles s) pos).Yields c opened c' ∧
      singleRowsSymbols s opened pos.all.size = some y := by
  unfold singleRowsRead at h
  obtain ⟨opened, c1, h1, a1⟩ := (Blk.yields_bind _ _ _ _ _).1 h
  obtain ⟨hy, rfl⟩ := (Blk.yields_get _ _ _ _).1 a1
  exact ⟨opened, h1, hy⟩

/-- Reading a complex of single rows, on a view, leaves as it was all that `Blk.Frame` lists: the
statement, the rounds and entries to come, the counts, whether a named test has failed. Nothing is
said here on the opened columns that remain to be read or on the book of trees. -/
theorem singleRowsRead_frame (s : SingleRows) (pos : Positions) (y : Array E) (c c' : Ctx)
    (hd : c.ch.dry = false) (h : (singleRowsRead s pos).Yields c y c') : Blk.Frame c c' := by
  obtain ⟨opened, h1, _⟩ := singleRowsRead_inv s pos y c c' h
  obtain ⟨_, _, _, _, _, _, _, hf, _⟩ := Blk.readOpened_inv _ _ _ _ _ hd h1
  exact hf

/-! ## The sending of one sampled oracle message, with others that are not sampled -/

/-- The i-th oracle message that has just been sent has the number of answers of its notice. -/
theorem sent_answers (S : Statement) (sent : Array OracleNotice) (i : Nat) :
    (((stSent S sent).oracles[i + S.oracles.size]?).map (·.shape.answers)).getD 0 =
      ((sent[i]?).map (·.shape.answers)).getD 0 := by
  show (((S.oracles ++ sent.map fun n => ({ shape := n.shape } : Oracle))[i + S.oracles.size]?).map
    (·.shape.answers)).getD 0 = _
  rw [Array.getElem?_append_right (Nat.le_add_left _ _), Nat.add_sub_cancel, Array.getElem?_map]
  cases sent[i]? <;> rfl

/-- If the first notice asks for answers and the others ask for none, the list of the oracle
messages to sample (`todoOf`) holds the first alone. -/
theorem todo_one (S : Statement) (N : OracleNotice) (others : Array OracleNotice)
    (h0 : N.shape.answers ≠ 0) (ho : ∀ n ∈ others, n.shape.answers = 0) :
    todoOf (stSent S (#[N] ++ others))
      ((Array.range (#[N] ++ others).size).map (· + S.oracles.size)) = [S.oracles.size] := by
  unfold todoOf
  have hs : (#[N] ++ others).size = others.size + 1 := by simp [Nat.add_comm]
  rw [Array.toList_map, Array.toList_range, hs, List.range_succ_eq_map, List.map_cons,
    List.filter_cons]
  have hp0 : ((((stSent S (#[N] ++ others)).oracles[0 + S.oracles.size]?).map
      (·.shape.answers)).getD 0 != 0) = true := by
    have h00 : (#[N] ++ others)[0]? = some N := by
      rw [Array.getElem?_append_left (by simp)]
      rfl
    rw [sent_answers, h00]
    simpa using h0
  rw [if_pos hp0, Nat.zero_add]
  refine congrArg (S.oracles.size :: ·) (List.filter_eq_nil_iff.2 fun x hx => ?_)
  simp only [List.mem_map, List.mem_range] at hx
  obtain ⟨i, ⟨j, hj, rfl⟩, rfl⟩ := hx
  have hj1 : (#[N] ++ others)[j + 1]? = others[j]? := by
    rw [Array.getElem?_append_right (by simp)]
    simp
  rw [sent_answers, hj1, Array.getElem?_eq_getElem hj]
  simp [ho _ (Array.getElem_mem hj)]

/-- The first oracle message that has just been sent has the next free number and, so far, nothing
but its notice's shape. -/
theorem sent_first (S : Statement) (N : OracleNotice) (others : Array OracleNotice) :
    (stSent S (#[N] ++ others)).oracles[S.oracles.size]? = some { shape := N.shape } := by
  show (S.oracles ++ (#[N] ++ others).map fun n => ({ shape := n.shape } : Oracle))[S.oracles.size]?
    = _
  rw [Array.getElem?_append_right (Nat.le_refl _), Nat.sub_self, Array.getElem?_map,
    Array.getElem?_append_left (by simp)]
  rfl

/-- A run, on a view, of the sending of one sampled oracle message with one answer, with others in
the same prover's message that are not sampled. The block takes the round of the seed, in which
nothing but roots is sent, and the first item of the next round, which is the answer. -/
theorem sendOne_inv (N : OracleNotice) (others : Array OracleNotice) (ids : Array Nat) (c c' : Ctx)
    (hd : c.ch.dry = false) (h1 : N.shape.answers = 1) (ho : ∀ n ∈ others, n.shape.answers = 0)
    (h : (sendVerify (#[N] ++ others) false).Yields c ids c') :
    ∃ lay e es r1 r2 rest vs beta row alpha places,
      layTrees c.st.codes (#[N] ++ others) = some lay ∧
      c.st.oracles.size = c.book.place.size ∧
      ids = (Array.range (#[N] ++ others).size).map (· + c.st.oracles.size) ∧
      c.ch.entries = e :: es ∧ e.name = "SEND seed" ∧
      c.ch.pending = r1 :: r2 :: rest ∧ r1.vals = [] ∧
      (r1.drawn.elems.map E.ofTriple).drop (Send.cube c.st.codes N.shape).bits = [beta] ∧
      isZeroE beta = false ∧
      Send.form c.st.codes N.shape c.st.oracles.size
        ⟨(r1.drawn.elems.map E.ofTriple).take (Send.cube c.st.codes N.shape).bits, beta⟩ 0
        = some row ∧
      r2.vals = .answer alpha.triple :: vs ∧ Send.pad c.st.codes N.shape = some places ∧
      c'.ch.pending = { r2 with vals := vs } :: rest ∧ c'.ch.entries = es ∧ c'.ch.dry = false ∧
      c'.ch.opened = c.ch.opened ∧ c'.failed = c.failed ∧
      c'.st = admitted (stSent c.st (#[N] ++ others)) c.st.oracles.size N.shape places
        #[{ row with target := alpha }] ∧
      c'.book = bookSent c (#[N] ++ others) lay ∧
      c'.ch.firstTree = c.ch.firstTree ∧ c'.ch.roots = c.ch.roots + lay.shapes.size := by
  obtain ⟨cR, hR, hV⟩ := sendVerify_inv _ _ _ _ _ h
  obtain ⟨lay, hlay, hplaces, hids, hcR⟩ := receiveOracles_inv _ _ _ _ hd hR
  -- what the receiving has left
  have hdR : cR.ch.dry = false := by rw [hcR]; exact hd
  have hstR : cR.st = stSent c.st (#[N] ++ others) := by rw [hcR]
  have hbkR : cR.book = bookSent c (#[N] ++ others) lay := by rw [hcR]
  have hpeR : cR.ch.pending = c.ch.pending := by rw [hcR]; rfl
  have henR : cR.ch.entries = c.ch.entries := by rw [hcR]
  have hopR : cR.ch.opened = c.ch.opened := by rw [hcR]
  have hfaR : cR.failed = c.failed := by rw [hcR]
  obtain ⟨shapes, drawn, seeds, c1, c2, hsh, hclose, hseeds, hnz, hrun, hend⟩ :=
    verify_inv ids false cR c' hdR hV
  -- the first message alone is sampled
  have htodo : todoOf cR.st ids = [c.st.oracles.size] := by
    rw [hstR, hids]
    exact todo_one c.st N others (by omega) ho
  have hshapes : shapes = [N.shape] := by
    rw [htodo, hstR] at hsh
    simp only [List.mapM_cons, List.mapM_nil, sent_first] at hsh
    exact (Option.some.inj hsh).symm
  subst hshapes
  have hcodes : cR.st.codes = c.st.codes := by rw [hstR]; rfl
  simp only [List.foldl_cons, List.foldl_nil, h1, Nat.zero_max, hcodes] at hclose hseeds
  obtain ⟨beta, hbeta, rfl⟩ := seedsOf_one _ _ _ hseeds
  have hb0 : isZeroE beta = false := by simpa using hnz
  -- the round of the seed
  obtain ⟨e, es, r1, rest1, k1, k2, _, k4, k5, rfl, _, _, _, k9, k10, _, k12, k13, k14, k15, k16,
    k17, k18, _⟩ :=
    Blk.close_inv _ _ _ _ _ _ hdR hclose
  -- the one answer
  rw [htodo] at hrun
  obtain ⟨_, c3, ⟨rows, c4, hans, hadm⟩, _, rfl⟩ := hrun
  rw [show (c.st.oracles.size, N.shape).2.answers = 1 from h1] at hans
  obtain ⟨_, c5, ⟨seed, row, alpha, hs, hform, hrecv, rfl⟩, rfl, rfl⟩ := hans
  obtain rfl :
      (⟨(r1.drawn.elems.map E.ofTriple).take (Send.cube c.st.codes N.shape).bits, beta⟩ :
        SampleSeed) = seed :=
    Option.some.inj hs
  obtain ⟨r2, rest, vs, q1, q2, q3, q4⟩ := Blk.recvAnswer_inv _ _ _ k15 hrecv
  -- the message is admitted
  obtain ⟨x, places, a1, a2, _, _, _, a6⟩ := admit_inv _ _ _ _ hadm
  have hst5 : c4.st = stSent c.st (#[N] ++ others) := q4.st.trans (k12.trans hstR)
  rw [hst5] at a1 a2 a6
  obtain rfl : ({ shape := N.shape } : Oracle) = x :=
    Option.some.inj ((sent_first c.st N others).symm.trans a1)
  have hc' : c' = c2 := by simpa using hend
  rw [hcodes] at hform
  rw [k9] at q1
  subst q1
  refine ⟨lay, e, es, r1, r2, rest, vs, beta, row, alpha, places, hlay, hplaces, hids, henR ▸ k1,
    k2,
    hpeR ▸ k4, k5, hbeta, hb0, hform, q2, a2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hc', a6]; exact q3
  · rw [hc', a6]; exact q4.entries.trans k10
  · rw [hc', a6]; exact q4.dry.trans k15
  · rw [hc', a6]; exact q4.opened.trans (k16.trans hopR)
  · rw [hc', a6]; exact q4.failed.trans (k14.trans hfaR)
  · rw [hc', a6]; rfl
  · rw [hc', a6]; exact q4.book.trans (k13.trans hbkR)
  · rw [hc', a6]
    refine (q4.firstTree.trans k18).trans ?_
    rw [hcR]
  · rw [hc', a6]
    refine (q4.roots.trans k17).trans ?_
    rw [hcR]

/-! ## The new oracle message joins its group, and the claims become open rows -/

/-- The statement in which the ledger of g is closed, if g has mask rows. -/
def ledgerShut (S : Statement) (T : SwitchTarget) (g : Nat) : Statement :=
  if 0 < T.shape.maskRows then closeLedgers S [g] else S

/-- A run, on a view, of the end of a switch without kept members. G: the group before. rows:
the claims on the new oracle message. -/
theorem switchAdmit_inv (old : SingleRows) (T : SwitchTarget) (gp : Nat) (out : Switched)
    (y : Array E) (c c' : Ctx) (hd : c.ch.dry = false) (hk : T.kept = #[])
    (h : (switchAdmit old T gp out y).Yields c () c') :
    ∃ G rows, (ledgerShut c.st T out.g).groups[gp]? = some G ∧ G.inRun = false ∧
      switchRows (withMessageInGroup (ledgerShut c.st T out.g) gp out.g false G) old T out.g out.kept
        out.positions y = some rows ∧
      (∀ r ∈ rows, r.kind ≠ .sample ∧
        RowChecked (withMessageInGroup (ledgerShut c.st T out.g) gp out.g false G) r) ∧
      c' = { c with
        st := withRows (withMessageInGroup (ledgerShut c.st T out.g) gp out.g false G) gp rows } := by
  unfold switchAdmit at h
  -- the ledger
  have h0 : ∃ c0, c0 = { c with st := ledgerShut c.st T out.g } ∧
      (do
        Blk.join gp out.g
        forIn (out.kept.zip T.kept) PUnit.unit fun p _ => do
            Blk.join gp p.fst p.snd.keptAgain
            pure (ForInStep.yield PUnit.unit)
        let S ← Blk.statement
        Blk.addRowsOnView gp fun _ => switchRows S old T out.g out.kept out.positions y :
        Blk Unit).Yields c0 () c' := by
    by_cases hm : 0 < T.shape.maskRows
    · simp only [hm, if_true] at h
      obtain ⟨_, c0, k1, k2⟩ := (Blk.yields_bind _ _ _ _ _).1 h
      obtain ⟨_, e0⟩ := onOracle_inv _ _ _ _ k1
      refine ⟨c0, ?_, k2⟩
      rw [e0]
      unfold ledgerShut
      rw [if_pos hm]
      rfl
    · simp only [hm, if_false] at h
      obtain ⟨_, c0, k1, k2⟩ := (Blk.yields_bind _ _ _ _ _).1 h
      obtain ⟨_, e0⟩ := (Blk.yields_pure _ _ _ _).1 k1
      refine ⟨c0, ?_, k2⟩
      rw [e0]
      unfold ledgerShut
      rw [if_neg hm]
  obtain ⟨c0, e0, a0⟩ := h0
  have hd0 : c0.ch.dry = false := by rw [e0]; exact hd
  obtain ⟨_, c1, h1, a1⟩ := (Blk.yields_bind _ _ _ _ _).1 a0
  obtain ⟨G, x, hG, _, _, hrun, _, e1⟩ := join_inv _ _ _ _ _ h1
  obtain ⟨_, c2, h2, a2⟩ := (Blk.yields_bind _ _ _ _ _).1 a1
  -- no kept member: the loop has no turn
  have e2 : c2 = c1 := by
    have hz : (out.kept.zip T.kept).toList = [] := by rw [hk]; simp
    rw [← Array.forIn_toList, hz, List.forIn_nil] at h2
    exact ((Blk.yields_pure _ _ _ _).1 h2).2
  obtain ⟨S, c3, h3, a3⟩ := (Blk.yields_bind _ _ _ _ _).1 a2
  obtain ⟨eS, e3⟩ := (Blk.yields_statement _ _ _).1 h3
  have hd3 : c3.ch.dry = false := by rw [e3, e2, e1]; exact hd0
  obtain ⟨rows, hrows, hkind, e4⟩ := addRowsOnView_inv _ _ _ _ hd3 a3
  have est : c0.st = ledgerShut c.st T out.g := by rw [e0]
  rw [est] at hG e1
  have eS' : S = withMessageInGroup (ledgerShut c.st T out.g) gp out.g false G := by rw [eS, e2, e1]
  rw [eS'] at hrows
  rw [show c3.st = withMessageInGroup (ledgerShut c.st T out.g) gp out.g false G by rw [e3, ← eS, eS']] at hkind
  refine ⟨G, rows, hG, hrun, hrows, hkind, ?_⟩
  rw [e4, e3, e2, e1, e0]

/-! ## The switch up to its rows -/

/-- The oracle messages of the prover's message of a switch without kept members. -/
def sentOf (T : SwitchTarget) (others : Array OracleNotice) : Array OracleNotice :=
  #[⟨T.shape, T.leafClass⟩] ++ others

/-- A run of the switch that draws an element after the positions, cut at its calls. ids: the
numbers of the oracle messages sent; cA: the context after the sending; d: what the round of the
positions drew; cB: the context after that round; y: the symbols read; cC: the context after the
reading; cD: the same with intermediate values kept. -/
theorem switchVerify_inv (old : SingleRows) (T : SwitchTarget) (gp : Nat)
    (others : Array OracleNotice) (out : Switched) (theta : E) (c c' : Ctx) (hk : T.kept = #[])
    (h : (switchVerify old T gp others true).Yields c (out, theta) c') :
    ∃ ids cA code d e cB y cC cD,
      switchTargetCheck c.st old T = true ∧
      (sendVerify (sentOf T others) false).Yields c ids cA ∧
      c.st.codes.base[old.code]? = some code ∧
      (Blk.close "CS" .positions).Yields cA d cB ∧ cB.ch.last = some e ∧ e.logN = code.logN ∧
      0 < e.poss ∧ d.elems.map E.ofTriple = [theta] ∧
      out = { g := ids.getD 0 noId, kept := #[], others := ids.extract 1 ids.size,
              positions := Positions.ofDraws code.logN d.poss } ∧
      (singleRowsRead old out.positions).Yields cB y cC ∧ Blk.SameButNotes cC cD ∧
      (switchAdmit old T gp out y).Yields cD () c' := by
  unfold switchVerify at h
  obtain ⟨S, c1, h1, a1⟩ := (Blk.yields_bind _ _ _ _ _).1 h
  obtain ⟨rfl, rfl⟩ := (Blk.yields_statement _ _ _).1 h1
  obtain ⟨_, c2, h2, a2⟩ := (Blk.yields_bind _ _ _ _ _).1 a1
  obtain ⟨hcheck, rfl⟩ := (Blk.yields_must _ _ _).1 h2
  obtain ⟨ids, cA, h3, a3⟩ := (Blk.yields_bind _ _ _ _ _).1 a2
  obtain ⟨code, c4, h4, a4⟩ := (Blk.yields_bind _ _ _ _ _).1 a3
  obtain ⟨hcode, e4⟩ := (Blk.yields_get _ _ _ _).1 h4
  subst e4
  obtain ⟨drawn, cB, h5, a5⟩ := (Blk.yields_bind _ _ _ _ _).1 a4
  obtain ⟨d, e, hclose, hlast, hlog, hpos, rfl⟩ := closePositions_inv _ _ _ _ _ h5
  have hsent : (#[(⟨T.shape, T.leafClass⟩ : OracleNotice)] ++
      T.kept.map (fun k => (⟨k.shape, k.leafClass⟩ : OracleNotice)) ++ others)
      = sentOf T others := by
    rw [hk]
    simp [sentOf]
  rw [hsent] at h3
  have hkept : ids.extract 1 (1 + T.kept.size) = #[] := by
    rw [hk]
    simp
  have hoth : ids.extract (1 + T.kept.size) = ids.extract 1 ids.size := by
    rw [hk]
    rfl
  -- the round has drawn one element after the positions
  change (match true, d.elems.map E.ofTriple with
    | true, [x] => _
    | false, [] => _
    | _, _ => _ : Blk (Switched × E)).Yields cB (out, theta) c' at a5
  cases hel : d.elems.map E.ofTriple with
  | nil =>
    rw [hel] at a5
    obtain ⟨_, _, k, _⟩ := (Blk.yields_bind _ _ _ _ _).1 a5
    cases k
  | cons x l =>
    cases l with
    | cons x' l' =>
      rw [hel] at a5
      obtain ⟨_, _, k, _⟩ := (Blk.yields_bind _ _ _ _ _).1 a5
      cases k
    | nil =>
      rw [hel] at a5
      obtain ⟨_, c6, h6, a6⟩ := (Blk.yields_bind _ _ _ _ _).1 a5
      obtain ⟨rfl, e6⟩ := (Blk.yields_pure _ _ _ _).1 h6
      subst e6
      obtain ⟨y, cC, h7, a7⟩ := (Blk.yields_bind _ _ _ _ _).1 a6
      obtain ⟨_, c8, h8, a8⟩ := (Blk.yields_bind _ _ _ _ _).1 a7
      obtain ⟨_, c9, h9, a9⟩ := (Blk.yields_bind _ _ _ _ _).1 a8
      obtain ⟨_, cD, h10, a10⟩ := (Blk.yields_bind _ _ _ _ _).1 a9
      obtain ⟨_, c11, h11, a11⟩ := (Blk.yields_bind _ _ _ _ _).1 a10
      obtain ⟨hout, rfl⟩ := (Blk.yields_pure _ _ _ _).1 a11
      obtain ⟨eo, rfl⟩ := Prod.mk.inj hout
      have n1 := Blk.yields_noteBy _ _ _ _ h8
      have n2 := Blk.yields_noteBy _ _ _ _ h9
      have n3 := Blk.yields_noteBy _ _ _ _ h10
      have hn : Blk.SameButNotes cC cD :=
        ⟨n3.ch.trans (n2.ch.trans n1.ch), n3.st.trans (n2.st.trans n1.st),
          n3.book.trans (n2.book.trans n1.book), n3.failed.trans (n2.failed.trans n1.failed)⟩
      rw [hkept, hoth] at eo h7 h11
      rw [← eo] at h7 h11
      exact ⟨ids, _, code, d, e, _, y, cC, cD, hcheck, h3, hcode, hclose, hlast, hlog, hpos, hel,
        eo, h7, hn, h11⟩

/-! ## The whole switch -/

/-- What a run of the code switch has taken of a view and has made on its way. -/
structure CsTaken where
  /-- how the oracle messages sent are placed in trees -/
  lay : TreeLay
  /-- the plan's entry of the round of the seed -/
  eS : Fmt.Entry
  /-- the plan's entry of the round of the positions -/
  eC : Fmt.Entry
  /-- the plan's entries after these two -/
  es : List Fmt.Entry
  /-- the view's round of the seed -/
  rS : Fmt.RoundView
  /-- the view's round of the positions -/
  rC : Fmt.RoundView
  /-- the view's rounds after these two -/
  rest : List Fmt.RoundView
  /-- the factor of the seed -/
  beta : E
  /-- the answer -/
  alpha : E
  /-- the left side of the sample row -/
  smp : Row
  /-- the pad of the sample -/
  places : List PadPlace
  /-- the old main code -/
  code : Code
  /-- the symbols read of the old rows -/
  y : Array E
  /-- the context before the reading of the old rows -/
  cB : Ctx
  /-- the context after that reading -/
  cC : Ctx
  /-- the group before the switch -/
  G : Group
  /-- the claims on the new oracle message -/
  rows : List Row

namespace CsTaken
variable (D : CsTaken) (T : SwitchTarget) (gp : Nat) (others : Array OracleNotice) (c : Ctx)

/-- The point of the seed. -/
def z : List E := (D.rS.drawn.elems.map E.ofTriple).take (Send.cube c.st.codes T.shape).bits

/-- The sample row. -/
def sample : Row := { D.smp with target := D.alpha }

/-- The statement after the sending. -/
def stA : Statement :=
  admitted (stSent c.st (sentOf T others)) c.st.oracles.size T.shape D.places #[D.sample]

/-- The statement in which the new oracle message is a member of its group. -/
def stJ : Statement :=
  withMessageInGroup (ledgerShut (D.stA T others c) T c.st.oracles.size) gp c.st.oracles.size false D.G

/-- The statement with the claims as open rows. -/
def stR : Statement := withRows (D.stJ T gp others c) gp D.rows

/-- The group with its new member and the claims. -/
def grown : Group :=
  { D.G with
    members := D.G.members.insertIdxIfInBounds
      (D.G.members.filter (· < c.st.oracles.size)).size c.st.oracles.size
    kept := D.G.kept.insertIdxIfInBounds (D.G.members.filter (· < c.st.oracles.size)).size false
    rows := D.G.rows ++ D.rows.toArray }

end CsTaken

/-- What a run of the code switch, on a view, has done. -/
structure CsRan (old : SingleRows) (T : SwitchTarget) (gp : Nat) (others : Array OracleNotice)
    (c c' : Ctx) (out : Switched) (row : GroupRow) (lay : GroupLayout) (theta : E)
    (D : CsTaken) : Prop where
  check : switchTargetCheck c.st old T = true
  trees : layTrees c.st.codes (sentOf T others) = some D.lay
  /-- before the switch the book had a place for each oracle message, and for no other -/
  places : c.st.oracles.size = c.book.place.size
  entries : c.ch.entries = D.eS :: D.eC :: D.es
  nameS : D.eS.name = "SEND seed"
  nameC : D.eC.name = "CS"
  pending : c.ch.pending = D.rS :: D.rC :: D.rest
  /-- the first round sends roots alone and draws the point and one factor, which is not 0 -/
  valsS : D.rS.vals = []
  seed : (D.rS.drawn.elems.map E.ofTriple).drop (Send.cube c.st.codes T.shape).bits = [D.beta]
  factor : isZeroE D.beta = false
  form : Send.form c.st.codes T.shape c.st.oracles.size ⟨D.z T c, D.beta⟩ 0 = some D.smp
  pad : Send.pad c.st.codes T.shape = some D.places
  /-- the second round sends the answer and draws positions and one element -/
  valsC : D.rC.vals = [.answer D.alpha.triple]
  elem : D.rC.drawn.elems.map E.ofTriple = [theta]
  code : c.st.codes.base[old.code]? = some D.code
  logN : D.eC.logN = D.code.logN
  poss : D.rC.drawn.poss.length = D.eC.poss
  g : out.g = c.st.oracles.size
  kept : out.kept = #[]
  /-- the other oracle messages of the prover's message have the numbers after it -/
  riders : out.others = (Array.range others.size).map (· + (c.st.oracles.size + 1))
  positions : out.positions = Positions.ofDraws D.code.logN D.rC.drawn.poss
  /-- the old rows are read -/
  read : (singleRowsRead old out.positions).Yields D.cB D.y D.cC
  stB : D.cB.st = D.stA T others c
  bookB : D.cB.book = bookSent c (sentOf T others) D.lay
  openedB : D.cB.ch.opened = c.ch.opened
  dryB : D.cB.ch.dry = false
  firstB : D.cB.ch.firstTree = c.ch.firstTree
  rootsB : D.cB.ch.roots = c.ch.roots + D.lay.shapes.size
  /-- the claims -/
  group : (ledgerShut (D.stA T others c) T c.st.oracles.size).groups[gp]? = some D.G
  fresh : D.G.inRun = false
  rows : switchRows (D.stJ T gp others c) old T c.st.oracles.size #[] out.positions D.y
    = some D.rows
  kinds : ∀ r ∈ D.rows, r.kind ≠ .sample ∧ RowChecked (D.stJ T gp others c) r
  /-- the batching -/
  layout : (D.stR T gp others c).layout gp = some lay
  count : D.eC.rows = (runRows (D.stR T gp others c) (D.grown c)).size
  row : Bat.combine (begun (D.stR T gp others c) gp (D.grown c)) gp
    ⟨lay, runRows (D.stR T gp others c) (D.grown c)⟩ theta = some row
  /-- what is left -/
  st : c'.st = begun (D.stR T gp others c) gp (D.grown c)
  book : c'.book = D.cC.book
  opened : c'.ch.opened = D.cC.ch.opened
  failed : c'.failed = c.failed
  dry : c'.ch.dry = false
  pending' : c'.ch.pending = D.rest
  entries' : c'.ch.entries = D.es
  settled : c'.ch.settled = true
  firstTree : c'.ch.firstTree = c.ch.firstTree
  roots : c'.ch.roots = c.ch.roots + D.lay.shapes.size

/-- A run of the code switch on a view, taken apart: without kept members, with one answer to the
sample, and with other oracle messages in the same prover's message that are not sampled. -/
theorem csVerify_inv (old : SingleRows) (T : SwitchTarget) (gp : Nat)
    (others : Array OracleNotice) (out : Switched) (row : GroupRow) (lay : GroupLayout)
    (c c' : Ctx) (hd : c.ch.dry = false) (hk : T.kept = #[]) (h1 : T.shape.answers = 1)
    (ho : ∀ n ∈ others, n.shape.answers = 0)
    (h : (csVerify old T gp others).Yields c (out, row, lay) c') :
    ∃ theta D, CsRan old T gp others c c' out row lay theta D := by
  unfold csVerify at h
  obtain ⟨⟨out', theta⟩, c1, hsw, a1⟩ := (Blk.yields_bind _ _ _ _ _).1 h
  obtain ⟨input, c2, h2, a2⟩ := (Blk.yields_bind _ _ _ _ _).1 a1
  obtain ⟨_, c3, h3, a3⟩ := (Blk.yields_bind _ _ _ _ _).1 a2
  obtain ⟨S, c4, h4, a4⟩ := (Blk.yields_bind _ _ _ _ _).1 a3
  obtain ⟨row', c5, h5, a5⟩ := (Blk.yields_bind _ _ _ _ _).1 a4
  obtain ⟨hres, e5⟩ := (Blk.yields_pure _ _ _ _).1 a5
  obtain ⟨rfl, hres2⟩ := Prod.mk.inj hres
  obtain ⟨rfl, hlay⟩ := Prod.mk.inj hres2
  -- the switch up to its rows
  obtain ⟨ids, cA, code, d, e, cB, y, cC, cD, hcheck, hsend, hcode, hclose, hlast, hlog, _, hel,
    hout, hread, hnotes, hadm⟩ := switchVerify_inv old T gp others out theta c c1 hk hsw
  -- the sending
  obtain ⟨lay0, eS, es1, r1, r2, rest, vs, beta, smp, alpha, places, s1, s0, s2, s3, s4, s5, s6, s7,
    s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20⟩ :=
    sendOne_inv ⟨T.shape, T.leafClass⟩ others ids c cA hd h1 ho hsend
  -- the round of the positions
  obtain ⟨e', es, r, rest', k1, k2, _, k4, k5, rfl, _, k8, _, k9, k10, k11, k12, k13, k14, k15, k16,
    k17, k18, _⟩ :=
    Blk.close_inv _ _ _ _ _ _ s14 hclose
  obtain rfl : e' = e := Option.some.inj (k11.symm.trans hlast)
  rw [s12] at k4
  obtain ⟨rfl, rfl⟩ := List.cons.inj k4
  have hvs : vs = [] := k5
  subst hvs
  rw [s13] at k1
  subst k1
  -- the reading and the kept values
  have hkeep := singleRowsRead_frame old _ y cB cC k15 hread
  have hdD : cD.ch.dry = false := by rw [hnotes.ch]; exact hkeep.dry.trans k15
  have hstD : cD.st = admitted (stSent c.st (sentOf T others)) c.st.oracles.size T.shape places
      #[{ smp with target := alpha }] :=
    hnotes.st.trans (hkeep.st.trans (k12.trans s17))
  -- the number of the new oracle message
  have hg : out.g = c.st.oracles.size := by
    rw [hout, s2]
    have h0 : (Array.range (#[(⟨T.shape, T.leafClass⟩ : OracleNotice)] ++ others).size)[0]?
        = some 0 := by
      rw [Array.getElem?_eq_getElem (by simp)]
      simp
    simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map, h0]
    simp
  have hriders : out.others = (Array.range others.size).map (· + (c.st.oracles.size + 1)) := by
    rw [hout, s2]
    refine Array.ext (by simp) fun i h1 h2 => ?_
    simp only [Array.getElem_extract, Array.getElem_map, Array.getElem_range]
    omega
  -- the claims
  obtain ⟨G, rows, g1, g2, g3, g4, g5⟩ := switchAdmit_inv old T gp out y cD c1 hdD hk hadm
  have hkept : out.kept = #[] := by rw [hout]
  rw [hstD, hg] at g1 g4 g5
  rw [hstD, hg, hkept] at g3
  -- the beginning of the test on the group
  obtain ⟨G4, L, b1, _, _, b4, b5, b6⟩ := beginRun_inv _ _ _ _ h2
  have hst1 : c1.st = withRows (withMessageInGroup (ledgerShut (admitted (stSent c.st (sentOf T others))
                  c.st.oracles.size T.shape places #[{ smp with target := alpha }]) T c.st.oracles.size) gp
      c.st.oracles.size false G) gp rows := by rw [g5]
  rw [hst1] at b1 b4 b5 b6
  rw [withRows_group gp rows _ _ (joined_group _ gp c.st.oracles.size false G g1)] at b1
  have hG4 := Option.some.inj b1
  subst hG4
  -- the number of rows, and the batching
  have hch2 : c2.ch = cC.ch := by rw [b6, g5]; exact hnotes.ch
  have hd2 : c2.ch.dry = false := by rw [hch2]; exact hkeep.dry.trans k15
  obtain ⟨e2, q1, q2, q3⟩ := requireRows_inv _ _ _ hd2 h3
  have he2 : e2 = e' := by
    rw [hch2, hkeep.last, hlast] at q1
    exact (Option.some.inj q1).symm
  rw [he2] at q1 q2
  obtain ⟨eS4, e4⟩ := (Blk.yields_statement _ _ _).1 h4
  have hd4 : c4.ch.dry = false := by rw [e4, q3]; exact hd2
  obtain ⟨hrow, e5'⟩ := (Blk.yields_getOnView _ _ _ _ _ hd4).1 h5
  have hc' : c' = { c2 with ch := { c2.ch with askedRows := true } } := by rw [e5, e5', e4, q3]
  have hS : S = c2.st := by rw [eS4, q3]
  rw [hS, b6, b5] at hrow
  rw [b5] at q2 hlay
  refine ⟨theta,
    ⟨lay0, eS, e', es, r1, r2, rest, beta, alpha, smp, places, code, y, cB, cC, G, rows⟩,
    { check := hcheck, trees := s1, places := s0, entries := s3, nameS := s4, nameC := k2,
      pending := s5,
      valsS := s6, seed := s7, factor := s8, form := s9, pad := s11, valsC := s10, elem := hel,
      code := hcode, logN := hlog, poss := k8, g := hg, kept := hkept, riders := hriders,
      positions := by rw [hout], read := hread, stB := k12.trans s17, bookB := k13.trans s18,
      openedB := k16.trans s15, dryB := k15, firstB := k18.trans s19,
      rootsB := k17.trans s20, group := g1, fresh := g2, rows := g3, kinds := g4,
      layout := hlay ▸ b4, count := q2, row := hlay ▸ hrow, st := ?_, book := ?_, opened := ?_,
      failed := ?_, dry := ?_, pending' := ?_, entries' := ?_, settled := ?_, firstTree := ?_,
      roots := ?_ }⟩
  · rw [hc', b6]; rfl
  · rw [hc', b6, g5]; exact hnotes.book
  · rw [hc']
    show c2.ch.opened = _
    rw [hch2]
  · rw [hc', b6, g5]
    exact hnotes.failed.trans (hkeep.failed.trans (k14.trans s16))
  · rw [hc']; exact hd2
  · rw [hc']
    show c2.ch.pending = _
    rw [hch2]
    exact hkeep.pending.trans k9
  · rw [hc']
    show c2.ch.entries = _
    rw [hch2]
    exact hkeep.entries.trans k10
  · rw [hc']
    show Chan.settled { c2.ch with askedRows := true } = true
    unfold Chan.settled
    simp [q1]
  · rw [hc']
    show c2.ch.firstTree = _
    rw [hch2]
    exact hkeep.firstTree.trans (k18.trans s19)
  · rw [hc']
    show c2.ch.roots = _
    rw [hch2]
    exact hkeep.roots.trans (k17.trans s20)

/-! ## The rows that are batched, for a group that has just been made -/

section
variable {old : SingleRows} {T : SwitchTarget} {gp : Nat} {others : Array OracleNotice} {c c' : Ctx}
  {out : Switched} {row : GroupRow} {lay : GroupLayout} {theta : E} {D : CsTaken}

/-- Closing a ledger leaves the groups as they were. -/
theorem ledgerShut_groups (S : Statement) (T : SwitchTarget) (g : Nat) :
    (ledgerShut S T g).groups = S.groups := by
  unfold ledgerShut
  split <;> rfl

/-- The group before the switch is the group that the statement had at the start. -/
theorem CsRan.group0 (h : CsRan old T gp others c c' out row lay theta D) :
    c.st.groups[gp]? = some D.G := by
  have h1 := h.group
  rw [ledgerShut_groups] at h1
  exact h1

/-- An oracle message that has been admitted has the sample rows with which it was admitted. -/
theorem admitted_sampleRows (S : Statement) (o : Nat) (s : OracleShape) (places : List PadPlace)
    (rows : Array Row) (ho : o < S.oracles.size) :
    ((admitted S o s places rows).oracles[o]?).map (·.sampleRows) = some rows := by
  unfold admitted
  simp only [Array.getElem?_modify, if_true, Array.getElem?_eq_getElem ho, Option.map_some]

/-- Closing a ledger leaves the sample rows as they were. -/
theorem ledgerShut_sampleRows (S : Statement) (T : SwitchTarget) (g o : Nat) :
    ((ledgerShut S T g).oracles[o]?).map (·.sampleRows) = (S.oracles[o]?).map (·.sampleRows) := by
  unfold ledgerShut
  split
  · unfold closeLedgers
    simp only [List.foldl_cons, List.foldl_nil, Array.getElem?_modify]
    split
    · rw [Option.map_map]
      rfl
    · rfl
  · rfl

/-- Joining a group leaves the sample rows as they were. -/
theorem joined_sampleRows (S : Statement) (g o : Nat) (kept : Bool) (G : Group) (i : Nat) :
    ((withMessageInGroup S g o kept G).oracles[i]?).map (·.sampleRows)
      = (S.oracles[i]?).map (·.sampleRows) := by
  unfold withMessageInGroup
  simp only [Array.getElem?_modify]
  split
  · rw [Option.map_map]
    rfl
  · rfl

/-- The sample rows of the new oracle message, in the statement with the claims. -/
theorem CsTaken.sampleRows_stR (D : CsTaken) (T : SwitchTarget) (gp : Nat)
    (others : Array OracleNotice) (c : Ctx) :
    ((D.stR T gp others c).oracles[c.st.oracles.size]?).map (·.sampleRows) = some #[D.sample] := by
  have hlt : c.st.oracles.size < (stSent c.st (sentOf T others)).oracles.size := by
    unfold stSent sentOf
    simp
    omega
  unfold CsTaken.stR CsTaken.stJ CsTaken.stA
  rw [(withRows_oracles gp D.rows _).1, joined_sampleRows, ledgerShut_sampleRows,
    admitted_sampleRows _ _ _ _ _ hlt]

/-- The rows that the switch batches, if the group had no member and no row before: the plain
rows among the claims, the sample row of the new oracle message, the generator rows. -/
theorem CsTaken.runRows_fresh (D : CsTaken) (T : SwitchTarget) (gp : Nat)
    (others : Array OracleNotice) (c : Ctx) (hm : D.G.members = #[]) (hr : D.G.rows = #[]) :
    runRows (D.stR T gp others c) (D.grown c) =
      D.rows.toArray.filter (·.kind == .plain) ++ #[D.sample] ++
        D.rows.toArray.filter (·.kind == .generator) := by
  have hrows : (D.grown c).rows = D.rows.toArray := by
    unfold CsTaken.grown
    simp [hr]
  have hmem : (D.grown c).members = #[c.st.oracles.size] := by
    unfold CsTaken.grown
    simp [hm, Array.insertIdxIfInBounds]
  unfold runRows
  rw [hrows, hmem]
  have hs := D.sampleRows_stR T gp others c
  simp only [List.foldl_toArray', List.foldl_cons, List.foldl_nil, hs, Option.getD_some,
    Array.empty_append]

end

end OnBytes.Slice

#print axioms OnBytes.Slice.CsTaken.runRows_fresh
#print axioms OnBytes.Slice.singleRowsRead_frame
#print axioms OnBytes.Slice.sendOne_inv
#print axioms OnBytes.Slice.switchAdmit_inv
#print axioms OnBytes.Slice.switchVerify_inv
#print axioms OnBytes.Slice.csVerify_inv
#print axioms OnBytes.Slice.singleRowsRead_inv
#print axioms OnBytes.Slice.sent_answers
#print axioms OnBytes.Slice.todo_one
#print axioms OnBytes.Slice.sent_first
#print axioms OnBytes.Slice.ledgerShut_groups
#print axioms OnBytes.Slice.CsRan.group0
#print axioms OnBytes.Slice.admitted_sampleRows
#print axioms OnBytes.Slice.ledgerShut_sampleRows
#print axioms OnBytes.Slice.joined_sampleRows
#print axioms OnBytes.Slice.CsTaken.sampleRows_stR
