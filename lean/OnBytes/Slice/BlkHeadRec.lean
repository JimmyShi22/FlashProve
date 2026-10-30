-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/BlkHeadRec.lean: the program's link, run on the view of a written transcript, at
any two keys that hold a pair of records: from the start to the joint before the first fold.

The first statement of OnBytes/Slice/BlkChain.lean, `HeadRuns`, is on the link's steps and the
batching after them. This file proves it for
any two keys that hold a pair of records r with n answers each. The joint that is reached
(OnBytes/Slice/BlkJoints.lean: `GroupAt`) says that the row which the program holds, read in the
field, is the sum of the rows of OnBytes/Slice/RowsXRec.lean, at the statement that the library's
verifier holds after the five rounds from r on (OnBytes/Slice/CorePeelRec.lean: `st4R`), under the
powers of the element that the batching round draws, in the order of `RowNo.port`
(OnBytes/Slice/BatSemRec.lean). The sample map of a row is `recZ` (OnBytes/Slice/RecordRead.lean).

How the proof goes. The two runs are taken apart
(OnBytes/Slice/BlkLinkRanRec.lean, BlkBat.lean). The program's rows are the rows of RowsXRec.lean
(OnBytes/Slice/BlkLinkJoinRec.lean: `head_rowsR`), and the batching adds them up
(OnBytes/Slice/BlkLinkHeadRec.lean, BlkLinkRec.lean: `stmG_rowsXR`). `headRuns_atR` states the claim
outright and does not go by the records of readings of OnBytes/Slice/ChainSem.lean.
OnBytes/Slice/ManyHeadRec.lean says so at the written link of a chain of any number of stages.


Main definition.
 `HeadKeepsR`   what the two runs keep and leave, beside the claim.
Main theorems.
 `head_invR`      the runs of `HeadRuns`, taken apart, with the rounds named.
 `head_claimR`    the row that the batching returns is the sum of the link's rows.
 `headKeeps_ofR`  `HeadKeepsR` from the start of a run on a view.
 `head_fieldsR`, `headRuns_atR`   the joint after the head: its clauses; as `HeadRuns`.
What is asked: public facts on sizes, shapes and draws (`LinkSizes`, `LinkFit`, `BatDraws`, three
pads for each answer have room in a row's message); that the two keys hold the records of r
(`KeyHasR`, OnBytes/Slice/BlkRecRow.lean), which is asked only of keys whose sizes fit the tables'
shape and of which no seed's factor is the program's 0 (`isZeroE`: three words 0), since the program
tests both; that the keys name the items 0 and 1; and in the last two theorems `HeadKeepsR`.
Not claimed. One thing stays a hypothesis of `headKeeps_ofR`: the tie of the group's columns to the
written oracles. Where a key's record and seeds come from. Nothing on the dry run. Nothing on
soundness.

-/
import OnBytes.Slice.BlkHead
import OnBytes.Slice.BlkLinkHeadRec
import OnBytes.Slice.BlkLinkJoinRec

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb Cb.Ood _root_.Run
open Params (LinkShape IoppStage)

section
variable (S : Sz) (t₀ : ℕ) (Λ : LinkShape) (first further : TableKey) (st1 : IoppStage)
  (s : Start) (V : Fmt.View) (d1 d2 d3 d4 d5 dA : PQ.RD)
  (m1 : (wRound d1).Msg) (c1 : (wRound d1).Chal) (m2 : (wRound d2).Msg)
  (c2 : (wRound d2).Chal) (m3 : (wRound d3).Msg) (c3 : (wRound d3).Chal)
  (m4 : (wRound d4).Msg) (c4 : (wRound d4).Chal) (m5 : (wRound d5).Msg) (c5 : (wRound d5).Chal)
  (mA : (wRound dA).Msg) (cA : (wRound dA).Chal) (rest0 : List Fmt.RoundView)

/-- The run of the head, taken apart, with the rounds named: for any two keys. -/
theorem head_invR
    (hV : V.rounds = rvW d1 m1 c1 :: rvW d2 m2 c2 :: rvW d3 m3 c3 :: rvW d4 m4 c4 ::
      rvW d5 m5 c5 :: rvW dA mA cA :: rest0)
    (hs : s.samples = 1)
    (x : LinkRun) (c1' : Ctx) (answers : Nat) (ca : Ctx) (St : Statement) (cb : Ctx)
    (row : GroupRow) (L : GroupLayout) (cd ce : Ctx) (G : Group) (cf : Ctx)
    (h1 : (linkStepsVerify Λ first further).Yields (startCtx s V) x c1')
    (h2 : Blk.samples.Yields c1' answers ca) (h3 : Blk.statement.Yields ca St cb)
    (h5 : (batVerify x.group).Yields cb (row, L) cd)
    (h6 : (Blk.note "BAT: target" row.target).Yields cd () ce)
    (h7 : (Blk.group x.group).Yields ce G cf) :
    ∃ (D : LinkDataR) (G0 : Group) (θ : E),
      LinkRanR Λ first further (startCtx s V) c1' x D ∧ BatRan x.group c1' cd G0 L θ row ∧
      D.r1 = rvW d1 m1 c1 ∧ D.r2 = rvW d2 m2 c2 ∧ D.r3 = rvW d3 m3 c3 ∧ D.r4 = rvW d4 m4 c4 ∧
      D.r5 = rvW d5 m5 c5 ∧ (rvOf dA mA cA).els = [θ.triple] ∧ cd.ch.pending = rest0 ∧
      Blk.SameButNotes cd cf ∧ cd.st.groups[x.group]? = some G ∧ answers = c1'.ch.samples := by
  obtain ⟨D, hR⟩ := linkSteps_invR Λ first further x (startCtx s V) c1' rfl hs h1
  obtain ⟨hans, rfl⟩ := (yields_samples _ _ _).1 h2
  obtain ⟨-, rfl⟩ := (Blk.yields_statement _ _ _).1 h3
  obtain ⟨G0, θ, e, es, r, rest, hB, -, -, -, hp, -, hel, hp', -, -⟩ :=
    batVerify_inv x.group row L _ cd hR.dry h5
  have hn := Blk.yields_note _ _ _ _ h6
  obtain ⟨hg, rfl⟩ := (yields_group _ _ _ _).1 h7
  have e0 := hR.pending
  rw [startCtx_pending, hV] at e0
  injection e0 with a1 e0
  injection e0 with a2 e0
  injection e0 with a3 e0
  injection e0 with a4 e0
  injection e0 with a5 e0
  have e6 : r :: rest = rvW dA mA cA :: rest0 := by rw [← hp, hR.left, ← e0]
  injection e6 with a6 a7
  refine ⟨D, G0, θ, hR, hB, a1.symm, a2.symm, a3.symm, a4.symm, a5.symm, ?_, ?_, hn, ?_, hans⟩
  · rw [← rvW_elems, ← a6]
    exact hel
  · rw [hp', a7]
  · rw [← hn.st]
    exact hg

end

/-! ## The claim after the batching -/

section
variable (S : Sz) (t₀ lg n : ℕ) (Λ : LinkShape) (first further : TableKey)
  (d1 d2 d3 d4 d5 dA : PQ.RD)
  (m1 : (wRound d1).Msg) (c1 : (wRound d1).Chal) (m2 : (wRound d2).Msg)
  (c2 : (wRound d2).Chal) (m3 : (wRound d3).Msg) (c3 : (wRound d3).Chal)
  (m4 : (wRound d4).Msg) (c4 : (wRound d4).Chal) (m5 : (wRound d5).Msg) (c5 : (wRound d5).Chal)

/-- The row that the batching returns, read in the field, is the sum of the link's rows, the rows of
the two records among them, under the powers of the drawn element. r: a pair of records with n
answers each. Asked, beside public sizes: the two keys hold the two records of r, if their sizes fit
the tables' shape and no seed's factor is the program's 0 (`isZeroE`: three words 0), which the run
has tested (`hK0`, `hK1`); the five rounds that the run took are the written ones; each opened
column under a stored table's key is that table's column (`hop`); and the row's first `S.P.Z.l`
coefficients on the mask table read as 0 (`hmask`). -/
theorem head_claimR (c c' cd : Ctx) (x : LinkRun) (D : LinkDataR) (G0 : Group) (L : GroupLayout)
    (θ : E) (row : GroupRow) (hS : LinkSizes S Λ c.st.codes)
    (hF : LinkFit S Λ (Λ.side false 1) (Λ.side true 1)) (hd : BatDraws S d1 d2 d3 d4 d5 dA)
    (hn0 : (Λ.side false 1).columns = Λ.columnsFirst)
    (hn1 : (Λ.side true 1).columns = Λ.columnsFurther)
    (hi0 : first.item = 0) (hi1 : further.item = 1) (hpads : 3 * n ≤ S.P.T.l)
    (r : (S.lkR (recZ S.P.T.l lg n)).X0)
    (hK0 : first.fits Λ.table = true → (first.seeds.all fun x => !isZeroE x.beta) = true →
      KeyHasR S.P.v lg n (Λ.side false 1).index first r.1)
    (hK1 : further.fits Λ.table = true → (further.seeds.all fun x => !isZeroE x.beta) = true →
      KeyHasR S.P.v lg n (Λ.side true 1).index further r.2)
    (y : (S.lkR (recZ S.P.T.l lg n)).E0.Str)
    (hR : LinkRanR Λ first further c c' x D) (hB : BatRan x.group c' cd G0 L θ row)
    (a1 : D.r1 = rvW d1 m1 c1) (a2 : D.r2 = rvW d2 m2 c2) (a3 : D.r3 = rvW d3 m3 c3)
    (a4 : D.r4 = rvW d4 m4 c4) (a5 : D.r5 = rvW d5 m5 c5)
    (hop : ∀ o ∈ c.ch.opened,
      (o.1 = Fmt.storedKey 0 → storedOf S.P.T.a y 0 o.2.1 = some o.2.2) ∧
      (o.1 = Fmt.storedKey 1 → storedOf S.P.T.a y 1 o.2.1 = some o.2.2))
    (hmask : ∀ i, i < S.P.Z.l → readV row.d i = 0) :
    stmG (S.sg t₀) row =
      sumStmR (RowNo.port S (recZ S.P.T.l lg n) n fun σ => Equiv.refl (Fin n) σ) t₀
        (rowsXR S (recZ S.P.T.l lg n) n (Equiv.refl (Fin n)) t₀
          (st4R S (recZ S.P.T.l lg n) r d1 d2 d3 d4 d5 y c1 m2 c2 m3 c4 c5).1).1
        (rowsXR S (recZ S.P.T.l lg n) n (Equiv.refl (Fin n)) t₀
          (st4R S (recZ S.P.T.l lg n) r d1 d2 d3 d4 d5 y c1 m2 c2 m3 c4 c5).1).2 (readE θ) := by
  have hK0 := hK0 hR.fits0 hR.nz0
  have hK1 := hK1 hR.fits1 hR.nz1
  have hbits := hS.bits
  have haR : ceilLog2 Λ.rows = S.P.aR := by rw [hS.rows]; rfl
  have hpl : (rvOf d4 m4 c4).poss.length = S.P.nu0 + S.P.nuj := hd.r4.poss_length m4 c4
  have hdr : D.pos.draws.toList = (rvOf d4 m4 c4).poss := by
    rw [hR.pos, a4]
    rfl
  -- the columns that were read are the stored tables'
  have hat : ∀ (key : ℕ) (l : List ℕ) (cols : Array (Array F)) (i xx : ℕ) (col : Array F),
      cols.size = l.toArray.size → l.toArray.idxOf? xx = some i → cols[i]? = some col →
      (key, xx, col.toList) ∈ viewColumns key l.toArray cols := by
    intro key l cols i xx col hsz hi hc
    rw [List.idxOf?_toArray] at hi
    obtain ⟨h1, h2, -⟩ := List.idxOf?_eq_some_iff.1 hi
    have h3 : i < l.toArray.size := h1
    have h4 : i < cols.size := hsz ▸ h3
    have h5 := mem_viewColumns key l.toArray cols i h3 h4
    have e1 : l.toArray.getD i 0 = xx := by
      rw [← h2]
      simp [Array.getD, h1]
    have e2 : cols.getD i #[] = col := by
      rw [Array.getElem?_eq_getElem h4] at hc
      rw [← Option.some.inj hc]
      simp [Array.getD, h4]
    rwa [e1, e2] at h5
  have hcol0 : ∀ (i : ℕ) (col : Array F) (xx : S.Pos),
      (storedList (linkStored Λ first false) D.pos).toArray.idxOf? xx.val = some i →
      D.cols0[i]? = some col → col.toList = (y.1 xx).2 := by
    intro i col xx hi hc
    have hm : (Fmt.storedKey first.item, xx.val, col.toList) ∈ c.ch.opened := by
      rw [hR.opened]
      exact List.mem_append_left _ (hat _ _ _ i xx.val col hR.size0 hi hc)
    have h0 := (hop _ hm).1 (by rw [hi0])
    unfold storedOf at h0
    rw [dif_pos xx.isLt, if_pos rfl] at h0
    exact (Option.some.inj h0).symm
  have hcol1 : ∀ (i : ℕ) (col : Array F) (xx : S.Pos),
      (storedList (linkStored Λ further true) D.pos).toArray.idxOf? xx.val = some i →
      D.cols1[i]? = some col → col.toList = (y.2 xx).2 := by
    intro i col xx hi hc
    have hm : (Fmt.storedKey further.item, xx.val, col.toList) ∈ c.ch.opened := by
      rw [hR.opened]
      exact List.mem_append_right _
        (List.mem_append_left _ (hat _ _ _ i xx.val col hR.size1 hi hc))
    have h0 := (hop _ hm).2 (by rw [hi1])
    unfold storedOf at h0
    rw [dif_pos xx.isLt, if_neg Nat.one_ne_zero, if_pos rfl] at h0
    exact (Option.some.inj h0).symm
  -- what the program drew and received is what the written rounds hold
  have hmt : ∀ l : List (UInt64 × UInt64 × UInt64), (l.map E.ofTriple).map E.triple = l := by
    intro l
    rw [List.map_map]
    exact List.map_id l
  have hgamma : x.gamma.map E.triple = (rvOf d1 m1 c1).els := by
    rw [hR.gamma, hmt, a1]
    rfl
  have hphi : x.phi.map E.triple = (rvOf d5 m5 c5).els := by
    rw [hR.phi, hmt, a5]
    rfl
  have hz : ((D.r2.drawn.elems.map E.ofTriple).take
      (Send.cube c.st.codes (rowShape Λ)).bits).map E.triple =
      (rvOf d2 m2 c2).els.take (S.P.aR + S.P.aP) := by
    rw [List.map_take, hmt, a2, hbits]
    rfl
  have hbeta : D.beta.triple = (rvOf d2 m2 c2).els.getD (S.P.aR + S.P.aP) Fmt.Fld.zeroE := by
    have h0 := getD_of_drop _ _ _ (E.ofTriple Fmt.Fld.zeroE) hR.factor
    rw [hbits, List.getD_map, a2] at h0
    rw [← h0]
    rfl
  have hsent : (rvOf d3 m3 c3).sent = [D.y0.triple, D.y1.triple] := by
    rw [← rvW_sent, ← a3, hR.vals3]
    rfl
  have hy0 : D.y0.triple = (rvOf d3 m3 c3).sent.getD 0 Fmt.Fld.zeroE := by rw [hsent]; rfl
  have hy1 : D.y1.triple = (rvOf d3 m3 c3).sent.getD 1 Fmt.Fld.zeroE := by rw [hsent]; rfl
  have hl0 : ((D.pos.draws.toList.drop 0).take (Λ.side false 1).columns).length = S.P.nu0 := by
    rw [hdr, hn0, hS.n0, List.length_take, List.length_drop, hpl]
    omega
  have hl1 : ((D.pos.draws.toList.drop Λ.columnsFirst).take (Λ.side true 1).columns).length =
      S.P.nuj := by
    rw [hdr, hn1, hS.n0, hS.n1, List.length_take, List.length_drop, hpl]
    omega
  have hD0 : ∀ i, i < S.P.nu0 →
      ((D.pos.draws.toList.drop 0).take (Λ.side false 1).columns).getD i 0 =
        (rvOf d4 m4 c4).poss.getD i 0 := by
    intro i hi
    rw [hdr, hn0, hS.n0, List.drop_zero, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_take_of_lt hi]
  have hD1 : ∀ i, i < S.P.nuj →
      ((D.pos.draws.toList.drop Λ.columnsFirst).take (Λ.side true 1).columns).getD i 0 =
        (rvOf d4 m4 c4).poss.getD (S.P.nu0 + i) 0 := by
    intro i hi
    rw [hdr, hn1, hS.n0, hS.n1, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_take_of_lt hi, List.getElem?_drop]
  have heq := hR.eqRow
  rw [hR.uFirst, hR.uFurther] at heq
  have hc0 := hR.rows0
  rw [hR.uFirst] at hc0
  have hc1 := hR.rows1
  rw [hR.uFurther] at hc1
  have hq0 := hR.rec0
  rw [hR.uFirst] at hq0
  have hq1 := hR.rec1
  rw [hR.uFurther] at hq1
  have hrows := head_rowsR S lg n Λ c.st.codes hS hF d1 d2 d3 d4 d5 dA hd y m1 c1 m2 c2 m3 c3 m4 c4
    m5 c5 c.st.oracles.size x.gamma x.phi _ D.beta D.y0 D.y1 _ _ D.rE D.row0 D.row1 D.rows0 D.rows1
    _ _ _ _ hgamma hz hbeta hy0 hy1 hl0 hl1 hD0 hD1 hphi heq hR.form0 hR.form1 hc0 hc1 hcol0 hcol1
    r first further D.rec0 D.rec1 hpads hK0 hK1 hq0 hq1
  -- the number of rows
  have hlen : D.rowsR.length = S.nRowsR n := by
    have e0 := (colRows_getD _ _ _ _ _ _ _ hc0).1
    have e1 := (colRows_getD _ _ _ _ _ _ _ hc1).1
    have e2 := (recRows_getD _ _ _ _ _ hq0).1.trans hK0.seeds_length
    have e3 := (recRows_getD _ _ _ _ _ hq1).1.trans hK1.seeds_length
    unfold LinkDataR.rowsR Sz.nRowsR
    simp only [List.length_append, List.length_cons]
    rw [e0, e1, e2, e3, hl0, hl1]
    omega
  refine stmG_rowsXR S (recZ S.P.T.l lg n) n (Equiv.refl (Fin n)) t₀ hF.pow _ D.rowsR
    c.st.oracles.size (c.st.oracles.size + 1) (readE θ) row hrows ?_ ?_ hmask
  · have h0 := hR.bat_target hB rdE
    rw [hlen] at h0
    exact h0
  · intro a r p hr _
    have h0 := hR.bat_main hB rdE a r p (by rw [haR]; exact hr)
    rw [hlen, haR] at h0
    exact h0

end

/-! ## The joint after the head -/

/-- What the runs of the link's steps and of the batching keep and leave, beside the claim. V:
the view. K: the statement's codes. nZ: the number of entries of the group's mask table. Tie: what
ties the columns of the group's members and of the fresh mask to the written oracles. -/
def HeadKeepsR (Λ : LinkShape) (first further : TableKey) (c : Ctx) (V : Fmt.View) (K : Codes)
    (nZ : ℕ) (Tie : Ctx → GroupRow → GroupLayout → Nat → Prop) : Prop :=
  ∀ (x : LinkRun) (D : LinkDataR) (c' cd : Ctx) (G0 : Group) (L : GroupLayout) (θ : E)
    (row : GroupRow), LinkRanR Λ first further c c' x D → BatRan x.group c' cd G0 L θ row →
    c'.ch.samples = 1 ∧ OnView V cd ∧ cd.st.codes = K ∧ cd.ch.roots = 1 ∧ PlainForm row.c ∧
      (∀ i, i < nZ → readV row.d i = 0) ∧
      ∃ o, x.mask = some o ∧ ∀ cf, Blk.SameButNotes cd cf → Tie cf row L o

/-- What the two runs keep and leave, from the start of a run on a view. Left as a hypothesis:
the tie on columns. -/
theorem headKeeps_ofR (Λ : LinkShape) (first further : TableKey) (s : Start) (V : Fmt.View)
    (K : Codes) (nZ : ℕ) (Tie : Ctx → GroupRow → GroupLayout → Nat → Prop) (h0 : s.firstTree = 0)
    (hK : s.st.codes = K) (hs : s.samples = 1)
    (hlay : ∀ lay, layTrees s.st.codes (linkMessage Λ 1) = some lay → lay.shapes.size = 1)
    (hahead : Λ.masksAhead = true)
    (hnZ : nZ ≤ 2 ^ ((linkLay Λ s.st).h + (linkLay Λ s.st).logEllZk))
    (hTie : ∀ (x : LinkRun) (D : LinkDataR) (c' cd : Ctx) (G0 : Group) (L : GroupLayout) (θ : E)
      (row : GroupRow) (cf : Ctx), LinkRanR Λ first further (startCtx s V) c' x D →
      BatRan x.group c' cd G0 L θ row → Blk.SameButNotes cd cf →
      Tie cf row L (s.st.oracles.size + 2)) :
    HeadKeepsR Λ first further (startCtx s V) V K nZ Tie := by
  intro x D c' cd G0 L θ row hR hB
  obtain ⟨k1, -, k3, k4, k5, -, k7⟩ := hR.bat_keeps hB
  refine ⟨hR.samples.trans hs, ⟨k5, k4.trans h0, k7⟩, k1.trans hK, ?_, hR.bat_plain hB,
    fun i hi => hR.bat_mask hB rdE i (Nat.lt_of_lt_of_le hi hnZ), s.st.oracles.size + 2, ?_,
    fun cf hn => hTie x D c' cd G0 L θ row cf hR hB hn⟩
  · rw [k3, hlay D.lay hR.laid]
    rfl
  · rw [hR.mask, if_pos hahead]
    rfl

section
variable (S : Sz) (t₀ lg n : ℕ) (Λ : LinkShape) (first further : TableKey) (st1 : IoppStage)
  (s : Start) (V : Fmt.View) (K : Codes) (Tie : Ctx → GroupRow → GroupLayout → Nat → Prop)
  (d1 d2 d3 d4 d5 dA : PQ.RD)
  (m1 : (wRound d1).Msg) (c1 : (wRound d1).Chal) (m2 : (wRound d2).Msg)
  (c2 : (wRound d2).Chal) (m3 : (wRound d3).Msg) (c3 : (wRound d3).Chal)
  (m4 : (wRound d4).Msg) (c4 : (wRound d4).Chal) (m5 : (wRound d5).Msg) (c5 : (wRound d5).Chal)
  (mA : (wRound dA).Msg) (cA : (wRound dA).Chal) (rest0 : List Fmt.RoundView)

/-- The link's steps and the batching, on the view of a written transcript: what is known after
them. r: a pair of records with n answers each, which the two keys hold if they pass the program's
two tests on keys. -/
theorem head_fieldsR (r : (S.lkR (recZ S.P.T.l lg n)).X0) (y : (S.lkR (recZ S.P.T.l lg n)).E0.Str)
    (hV : V.rounds = rvW d1 m1 c1 :: rvW d2 m2 c2 :: rvW d3 m3 c3 :: rvW d4 m4 c4 ::
      rvW d5 m5 c5 :: rvW dA mA cA :: rest0)
    (hop : ∀ o ∈ V.opened,
      (o.1 = Fmt.storedKey 0 → storedOf S.P.T.a y 0 o.2.1 = some o.2.2) ∧
      (o.1 = Fmt.storedKey 1 → storedOf S.P.T.a y 1 o.2.1 = some o.2.2))
    (hs : s.samples = 1) (hi0 : first.item = 0) (hi1 : further.item = 1) (hpads : 3 * n ≤ S.P.T.l)
    (hK0 : first.fits Λ.table = true → (first.seeds.all fun x => !isZeroE x.beta) = true →
      KeyHasR S.P.v lg n (Λ.side false 1).index first r.1)
    (hK1 : further.fits Λ.table = true → (further.seeds.all fun x => !isZeroE x.beta) = true →
      KeyHasR S.P.v lg n (Λ.side true 1).index further r.2)
    (hS : LinkSizes S Λ s.st.codes) (hF : LinkFit S Λ (Λ.side false 1) (Λ.side true 1))
    (hd : BatDraws S d1 d2 d3 d4 d5 dA)
    (hn0 : (Λ.side false 1).columns = Λ.columnsFirst)
    (hn1 : (Λ.side true 1).columns = Λ.columnsFurther)
    (hkeep : HeadKeepsR Λ first further (startCtx s V) V K S.P.Z.l Tie)
    (x : LinkRun) (c1' : Ctx) (answers : Nat) (ca : Ctx) (St : Statement) (cb : Ctx)
    (row : GroupRow) (L : GroupLayout) (cd ce : Ctx) (G : Group) (cf : Ctx)
    (h1 : (linkStepsVerify Λ first further).Yields (startCtx s V) x c1')
    (h2 : Blk.samples.Yields c1' answers ca) (h3 : Blk.statement.Yields ca St cb)
    (h5 : (batVerify x.group).Yields cb (row, L) cd)
    (h6 : (Blk.note "BAT: target" row.target).Yields cd () ce)
    (h7 : (Blk.group x.group).Yields ce G cf) :
    (OnView V cf ∧ cf.ch.pending = rest0 ∧ cf.st.codes = K ∧ cf.ch.roots = 1 ∧ answers = 1) ∧
      stmG (S.sg t₀) row =
        sumStmR (RowNo.port S (recZ S.P.T.l lg n) n fun σ => Equiv.refl (Fin n) σ) t₀
          (rowsXR S (recZ S.P.T.l lg n) n (Equiv.refl (Fin n)) t₀
            (st4R S (recZ S.P.T.l lg n) r d1 d2 d3 d4 d5 y c1 m2 c2 m3 c4 c5).1).1
          (rowsXR S (recZ S.P.T.l lg n) n (Equiv.refl (Fin n)) t₀
            (st4R S (recZ S.P.T.l lg n) r d1 d2 d3 d4 d5 y c1 m2 c2 m3 c4 c5).1).2 (drawnE dA cA) ∧
      PlainForm row.c ∧ ∃ o, x.mask = some o ∧ Tie cf row L o := by
  obtain ⟨D, G0, θ, hR, hB, a1, a2, a3, a4, a5, hθ, hp, hn, -, hans⟩ :=
    head_invR Λ first further s V d1 d2 d3 d4 d5 dA m1 c1 m2 c2 m3 c3 m4 c4 m5 c5 mA cA rest0 hV hs
      x c1' answers ca St cb row L cd ce G cf h1 h2 h3 h5 h6 h7
  obtain ⟨k1, k2, k3, k4, k5, k6, o, k7, k8⟩ := hkeep x D c1' cd G0 L θ row hR hB
  have hdraw : drawnE dA cA = readE θ := by
    rw [readE_def]
    exact gOne_of_els dA mA cA hθ
  refine ⟨⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, hans.trans k1⟩, ?_, k5, o, k7, k8 cf hn⟩
  · rw [hn.ch]
    exact k2.dry
  · rw [hn.ch]
    exact k2.first
  · rw [hn.ch]
    exact k2.opened
  · rw [hn.ch]
    exact hp
  · rw [hn.st]
    exact k3
  · rw [hn.ch]
    exact k4
  · rw [hdraw]
    exact head_claimR S t₀ lg n Λ first further d1 d2 d3 d4 d5 dA m1 c1 m2 c2 m3 c3 m4 c4 m5 c5
      (startCtx s V) c1' cd x D G0 L θ row hS hF hd hn0 hn1 hi0 hi1 hpads r hK0 hK1 y hR hB a1 a2 a3
      a4 a5 hop k6

/-- The link's steps and the batching lead from the start of a run on the view of a written
transcript to the joint before the first fold, at the sum of the rows of
OnBytes/Slice/RowsXRec.lean under the powers of the element that the batching round draws.
`HeadKeepsR` is a hypothesis (`hkeep`). -/
theorem headRuns_atR (r : (S.lkR (recZ S.P.T.l lg n)).X0)
    (y : (S.lkR (recZ S.P.T.l lg n)).E0.Str)
    (hV : V.rounds = rvW d1 m1 c1 :: rvW d2 m2 c2 :: rvW d3 m3 c3 :: rvW d4 m4 c4 ::
      rvW d5 m5 c5 :: rvW dA mA cA :: rest0)
    (hop : ∀ o ∈ V.opened,
      (o.1 = Fmt.storedKey 0 → storedOf S.P.T.a y 0 o.2.1 = some o.2.2) ∧
      (o.1 = Fmt.storedKey 1 → storedOf S.P.T.a y 1 o.2.1 = some o.2.2))
    (hs : s.samples = 1) (hi0 : first.item = 0) (hi1 : further.item = 1) (hpads : 3 * n ≤ S.P.T.l)
    (hK0 : first.fits Λ.table = true → (first.seeds.all fun x => !isZeroE x.beta) = true →
      KeyHasR S.P.v lg n (Λ.side false 1).index first r.1)
    (hK1 : further.fits Λ.table = true → (further.seeds.all fun x => !isZeroE x.beta) = true →
      KeyHasR S.P.v lg n (Λ.side true 1).index further r.2)
    (hS : LinkSizes S Λ s.st.codes) (hF : LinkFit S Λ (Λ.side false 1) (Λ.side true 1))
    (hd : BatDraws S d1 d2 d3 d4 d5 dA)
    (hn0 : (Λ.side false 1).columns = Λ.columnsFirst)
    (hn1 : (Λ.side true 1).columns = Λ.columnsFurther)
    (hkeep : HeadKeepsR Λ first further (startCtx s V) V K S.P.Z.l Tie) :
    HeadRuns Λ first further st1 (startCtx s V)
      (GroupAt V K 1 (S.sg t₀)
        (sumStmR (RowNo.port S (recZ S.P.T.l lg n) n fun σ => Equiv.refl (Fin n) σ) t₀
          (rowsXR S (recZ S.P.T.l lg n) n (Equiv.refl (Fin n)) t₀
            (st4R S (recZ S.P.T.l lg n) r d1 d2 d3 d4 d5 y c1 m2 c2 m3 c4 c5).1).1
          (rowsXR S (recZ S.P.T.l lg n) n (Equiv.refl (Fin n)) t₀
            (st4R S (recZ S.P.T.l lg n) r d1 d2 d3 d4 d5 y c1 m2 c2 m3 c4 c5).1).2 (drawnE dA cA))
        rest0 Tie) := by
  intro x c1' answers ca St cb row L cd ce G cf h1 h2 h3 _ h5 h6 h7 _
  obtain ⟨⟨k1, k2, k3, k4, k5⟩, k6, k7, k8⟩ :=
    head_fieldsR S t₀ lg n Λ first further s V K Tie d1 d2 d3 d4 d5 dA m1 c1 m2 c2 m3 c3 m4 c4 m5 c5
      mA cA rest0 r y hV hop hs hi0 hi1 hpads hK0 hK1 hS hF hd hn0 hn1 hkeep x c1' answers ca St cb
      row L cd ce G cf h1 h2 h3 h5 h6 h7
  exact ⟨⟨k1, k2, k3, k4, k5⟩, k6, k7, k8⟩

end

end OnBytes.Slice
