-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/FormBehindAny.lean: behind an accepted code switch of the proximity test and the
batching behind it, the form's half of the invariant (`FormInv`, Johnson/Prover/Link/FormInv.lean)
holds at the next stage, WHATEVER TREES THE OLD ROWS STOOD IN.

Why. `formInv_next` (Johnson/Prover/Link/FormClose.lean) says the like at written states, where the
old rows stood in one tree. A proximity test's first stage may read a group whose members stand in
several trees. Here the state in front of the switch and the two states behind are letters; what is
known of them comes from the two acceptances, by the library's `switchUnfolds`
(Johnson/Desc/K12/Law/SwUnfold.lean).

Main names (namespace `Johnson.Prover.Link`).
  `SwitchPlan p K j cur next n`   a premise: what is public at the switch; no clause on an old tree.
      `StepPlan.switchPlan`: `StepPlan` (Johnson/Prover/Link/FormStepPlan.lean) gives it
  `SwitchIn`   a premise: what the state in front of the switch is asked. Its clause on the count
      of roots is "those in front of the test, and one a switch"
  `group_did`   the group that the switch finds is the statement's
  `formInv_any`   the statement: `FormInv`, `LayAt` and `SeatP` at the state behind the batching
  `left_any`   nothing is left untested behind the switch, where nothing was in front of the fold:
      the one statement here that asks that, and the statement's form behind the fold
  `switchIn_of_inv`   a member of `SwitchIn`: at a stage whose old rows stand in one tree, `FormInv`
      and `StepPlan` give it behind the written fold. It pays neither of the two acceptances

Of any layout of TREES, not of rows: the single rows in front have two mask rows and no kept member
(`FoldedFit`, OnBytes/Slice/BlkProxSeg.lean).

Limits. The two acceptances, `SwitchPlan`, `SwitchIn` and the next stage's `StepPlan` are asked. A
further stage follows the next one: the switch into the last stage is not served by `formInv_any`.
`left_any` asks the statement in the form "the mask spent, then the new group opened", over a letter
S₀: where the fold sends its own table, S₀ is the statement behind that sending; that a fold leaves
such a statement is asked, not shown. At old rows in several trees nothing here meets `SwitchIn` or
the two acceptances. Nothing on values or on soundness.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.FormClose
import Johnson.Prover.Link.FormBehindRead
import Johnson.Prover.Link.FormBehindOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Link
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.Sw
open H2K.Pub (sgOf)

/-- **What is public at a switch that is not the last**: no clause on an old tree. -/
structure SwitchPlan (p : P12) (K : Codes) (j : ℕ) (cur next : Fmt.M1.Stage) (n : IoppStage) :
    Prop where
  early : p.early = true
  one : p.answers = 1
  stageN : stageAt p (j + 1) next = some n
  idx : p.idx[j + 1]? = some (n.code, n.maskCode)
  hkN : next.h ≤ next.k
  fits : CsFit (sgOf cur) (sgOf next)
  codeN : (K.base[n.code]?).map codeOf = some (sgOf next).C
  zkN : (K.mask[n.maskCode]?).map codeOf = some (sgOf next).Z
  nk : n.k = (sgOf next).h + (sgOf next).g
  nh : n.h = (sgOf next).h
  lengths : K.lengthsOk = true
  bounds : 2 ^ ((sgOf next).h + (sgOf next).g) * (sgOf next).C.l ≤ 2 ^ 63 ∧
    2 ^ (sgOf next).h * (sgOf next).Z.l ≤ 2 ^ 63
  trees : Own.treesCan K (swNotices p n false) = true
  oneTree : OneTree K (OnBytes.Slice.sentOf (swTarget p n) (othersOf false n)) (sgOf next).C.a

theorem StepPlan.switchPlan {p : P12} {K : Codes} {j : ℕ} {cur next : Fmt.M1.Stage} {l : Laid}
    {c n : IoppStage} {dS dC : Fmt.DeclaredRound} (Pl : StepPlan p K j cur next false l c n dS dC) :
    SwitchPlan p K j cur next n :=
  ⟨Pl.early, Pl.one, Pl.stageN, Pl.idx, Pl.hkN, Pl.fits, Pl.codeN, Pl.zkN, Pl.nk, Pl.nh,
    Pl.lengths, Pl.bounds, Pl.trees, Pl.oneTree⟩

/-- **What the state in front of a switch is asked.** gp: the number of the group that the fold has
opened. -/
structure SwitchIn (p : P12) (j : ℕ) (cur next : Fmt.M1.Stage) (n : IoppStage) (gp : ℕ) (t1 : T12)
    (rows : SingleRows) (rC : Fmt.RoundView) : Prop where
  pass : t1.pass = .single rows gp
  group : t1.st.groups[gp]? = some { code := n.code, maskCode := n.maskCode }
  order : Means.InOrder t1.st
  roots : t1.roots = p.nums.free + j
  ff : FoldedFit (sgOf cur) (sgOf next) t1.st.codes n.code n.maskCode rows
  dense : DenseForm rows.c
  cfits : Means.CFits (ceilLog2 (sgOf cur).C.l) rows.c
  range : ∀ x ∈ rC.drawn.poss, x < 2 ^ (sgOf cur).C.a
  old : OldIn t1.st t1.book rows

/-- The group that the switch finds is the statement's. -/
theorem group_did {ft : ℕ} {cols : List Tw.L9.Col} {old : SingleRows} {T : SwitchTarget} {gp : ℕ}
    {others : Array OracleNotice} {S S' : Statement} {Bk Bk' : TreeBook} {roots : ℕ}
    {out : Switched} {row : GroupRow} {lay : GroupLayout} {theta : E} {D : Taken} {G₀ : Group}
    (h : Did ft cols old T gp others S Bk roots S' Bk' out row lay theta D)
    (hg : S.groups[gp]? = some G₀) : D.G = G₀ := by
  have k := h.group
  rw [shut_groups] at k
  exact (Option.some.inj (hg.symm.trans k)).symm

/-- **`FormInv` behind a switch, whatever trees the old rows stood in.** -/
theorem formInv_any {p : P12} {j : ℕ} {cur next nx : Fmt.M1.Stage} {last' : Bool} {l' : Laid}
    {n n' : IoppStage} {dS' dC' : Fmt.DeclaredRound} {gp : ℕ} {t1 t2 t3 : T12}
    {rows : SingleRows} {rS rC : Fmt.RoundView} {gs : List (List (ℕ × List UInt64))}
    {cut : List Fmt.DeclaredRound} (Pl : SwitchPlan p t1.st.codes j cur next n)
    (In : SwitchIn p j cur next n gp t1 rows rC)
    (h2 : (switchJ p j cur next false cut).decide t1 [rS, rC] gs = .ok t2)
    (h3 : (behindJ p (j + 1) next cut).decide t2 [] [] = .ok t3)
    (Pl' : StepPlan p t1.st.codes (j + 1) next nx last' l' n n' dS' dC')
    (rest' : List Fmt.M1.Stage)
    (hD : Dealt next (nx :: rest') ((listsOf p.nums).drop (j + 1)) l')
    (hst : p.nums.stages.drop (j + 1) = next :: nx :: rest') (hown : p.nums.ownMask = false)
    (tabM tabZ : ℕ → GE) (tM tZ fM fT : ℕ → ℕ → GE) :
    ∃ row' lay tr', t3.pass = .claim row' lay ∧
      FormInv p (j + 1) next l' t3 (stageColW (sgOf next) tabM tabZ tM tZ fM fT) row' lay n
        (n'.code, n'.maskCode) (t1.st.oracles.size + 1) t1.book.trees.size tr' ∧
      LayAt [t1.st.oracles.size] #[some 0] #[some 0] lay ∧
      SeatP t3.st t3.book [t1.st.oracles.size, t1.st.oracles.size + 1]
        (p.nums.firstTree + (p.nums.free + j)) (sgOf next).C.a (stageShapes (sgOf next) n) := by
  obtain ⟨out, row', lay, theta, D, -, hrC, hdT, hp3, hm3⟩ :=
    switchUnfolds p j cur next false cut t1 t2 t3 rS rC gs rows _ n Pl.early Pl.one In.pass
      Pl.stageN h2 h3
  have hG : D.G = { code := n.code, maskCode := n.maskCode } := group_did hdT In.group
  have hm : D.G.members = #[] := by rw [hG]
  have hk : D.G.kept = #[] := by rw [hG]
  have hr : D.G.rows = #[] := by rw [hG]
  have ek : n.k = next.k := by
    rw [Pl.nk]
    exact Nat.add_sub_cancel' Pl.hkN
  have eh : n.h = next.h := Pl.nh
  have en : (⟨n.code, n.maskCode, next.k, next.h⟩ : IoppStage) = n := by
    rw [← ek, ← eh]
  have eT : swTarget p n = switchTargetStage n.code n.maskCode n.k n.h 1 := by
    unfold swTarget
    rw [Pl.one]
  have hd : Did p.nums.firstTree (keyed p cut gs) rows (swTarget p n) gp
      (othersOf false n) t1.st t1.book t1.roots t3.st t3.book out row' lay theta D := by
    rw [eT]
    exact hdT
  have hdS := hdT
  rw [Pl.nk, Pl.nh] at hdS
  -- the statement stays in order
  have hfit : Blk.shapeOk t1.st.codes (swTarget p n).shape = true := by
    have h := recv_of (p := p) (n := n) (last := false) t1.st t1.book (lt_of_map_some Pl.codeN)
      (lt_of_map_some Pl.zkN) Pl.trees hdT.places
    simp only [Ground.ok, Ground.recvL, Ground.sentL, List.all_append, List.all_cons,
      List.all_nil, Bool.and_true, Bool.and_eq_true] at h
    have h1 := h.1.1
    rw [swNotices_eq, Array.all_eq_true_iff_forall_mem] at h1
    exact h1 ⟨(swTarget p n).shape, (swTarget p n).leafClass⟩ (by simp)
  rw [eT, Pl.nk, Pl.nh] at hfit
  obtain ⟨hORs, hO3⟩ := inOrder_did Pl.fits hdS In.ff hG Pl.bounds In.cfits In.dense
    (by rw [hrC]; exact In.range) In.order Pl.lengths hfit
  have hOR : Means.InOrder (D.stR (switchTargetStage n.code n.maskCode n.k n.h 1) gp
      (othersOf false n) t1.st) := by
    rw [Pl.nk, Pl.nh]
    exact hORs
  have hlay := hdT.lay_eq hm hk
  obtain ⟨sh, l1, l2, l3, l4, l5⟩ := Pl.oneTree D.lay hd.trees
  -- the seat in the soundness side's form
  have hseat := hd.seat sh l1 l3 l4 l5
  have e2 : (List.range (OnBytes.Slice.sentOf (swTarget p n) (othersOf false n)).size).map
      (· + t1.st.oracles.size) = [t1.st.oracles.size, t1.st.oracles.size + 1] := by
    show [0 + _, 1 + _] = _
    rw [Nat.zero_add, Nat.add_comm 1]
  have eT' : swTarget p n = switchTargetStage n.code n.maskCode ((sgOf next).h + (sgOf next).g)
      (sgOf next).h 1 := by
    rw [eT, Pl.nk, Pl.nh]
  rw [e2, l2, In.roots, eT'] at hseat
  have hQ : SeatP t3.st t3.book [t1.st.oracles.size, t1.st.oracles.size + 1]
      (p.nums.firstTree + (p.nums.free + j)) (sgOf next).C.a (stageShapes (sgOf next) n) := hseat
  -- the seat for the reading
  have hR := readSeat_did hd sh rfl l1
    (fun i hi => l3 i (by
      show i < 2
      exact hi))
    (by
      show p.answers ≠ 0
      rw [Pl.one]
      exact Nat.one_ne_zero) rfl In.old
  have hmem : lay.members.toList = [t1.st.oracles.size] := by
    rw [hlay]
  have hfolds := Pl'.folds
  have hroots : t3.roots = p.nums.free + (j + 1) := by
    have a := roots_behind p j cur next false cut t1 t2 t3 rS rC gs h2 h3
    have b := trees_did hd
    rw [l1] at b
    have c : (#[sh] : Array TreeShape).size = 1 := rfl
    rw [c] at b
    rw [b, In.roots] at a
    omega
  refine ⟨row', lay, _, hp3, ⟨?_, hdT.noKept hm hk hr, ?_, ?_, ?_,
    dense_behind hd In.ff.kept In.ff.prog.masks In.ff.prog.noKept hm hr In.dense, hO3,
    step_behind hd, hroots, by rw [hmem]; exact hR, l2,
    fun dS2 dC2 hcut => decl_later p.nums j next nx rest' _ _ _ _ _ _ _ n hown hst hD Pl.hkN eh hR
      hQ dS2 dC2 hcut,
    fun y => width_later next n _ _ _ _ _ _ _ tabM tabZ tM tZ fM fT Pl.hkN eh hR hQ y⟩,
    hdT.layAt hm hk, hQ⟩
  · have h := foldFront_behind p j (nn := (n'.code, n'.maskCode)) (next := next) (nx := nx) t3 hdT
      In.ff.kept In.ff.prog.masks In.ff.prog.noKept In.dense hG hOR ek eh (code_of_map Pl.codeN)
      (code_of_map Pl.zkN) (code_of_map Pl'.codeN) (code_of_map Pl'.zkN) Pl'.ok Pl'.shortN Pl'.vars
      Pl.idx Pl'.idx rfl hp3 (hm3.trans (did_mask hd rfl))
    rw [en] at h
    exact h
  · intro i hi
    rw [hlay] at hi ⊢
    obtain rfl : i = 0 := by simpa using hi
    rfl
  · rw [hlay]
    show max (max n.k n.h) 1 = _
    rw [Pl.nk, Pl.nh]
    omega
  · rw [hlay]
    exact Pl.nh

/-- **Nothing is left untested behind a switch and its batching, where nothing was in front of the
fold.** S₀, id: the statement in front of the fold's spending of its mask, and the mask. -/
theorem left_any {p : P12} {j : ℕ} {cur next : Fmt.M1.Stage} {last : Bool} {n : IoppStage}
    {S₀ : Statement} {id : ℕ} {t1 t2 t3 : T12} {rows : SingleRows} {rS rC : Fmt.RoundView}
    {gs : List (List (ℕ × List UInt64))} {cut : List Fmt.DeclaredRound} (he : p.early = true)
    (h1 : p.answers = 1) (hn : stageAt p (j + 1) next = some n)
    (hpass : t1.pass = .single rows S₀.groups.size)
    (hst : t1.st = Ground.withGroup (spent S₀ id) n.code n.maskCode)
    (hl : ChainEnd.NothingLeft S₀)
    (h2 : (switchJ p j cur next last cut).decide t1 [rS, rC] gs = .ok t2)
    (h3 : (behindJ p (j + 1) next cut).decide t2 [] [] = .ok t3) : ChainEnd.NothingLeft t3.st := by
  obtain ⟨out, row', lay, theta, D, -, -, hd, -, -⟩ :=
    switchUnfolds p j cur next last cut t1 t2 t3 rS rC gs rows _ n he h1 hpass hn h2 h3
  rw [hst] at hd
  have hg : (Ground.withGroup (spent S₀ id) n.code n.maskCode).groups[S₀.groups.size]? =
      some { code := n.code, maskCode := n.maskCode } := by
    show (S₀.groups.push _)[S₀.groups.size]? = _
    rw [Array.getElem?_push_size]
  have hm : D.G.members = #[] := by rw [group_did hd hg]
  cases last with
  | false => exact left_step id n.code n.maskCode hl hd hm
  | true => exact left_step id n.code n.maskCode hl hd hm

/-- **A member of `SwitchIn`**: behind the written fold of a stage whose old rows stand in one tree.
-/
theorem switchIn_of_inv {p : P12} {j : ℕ} {cur next : Fmt.M1.Stage} {last : Bool} {l : Laid}
    {c n : IoppStage} {dS dC : Fmt.DeclaredRound} {t : T12} {col : ℕ → List UInt64} {row : GroupRow}
    {L : GroupLayout} {id tN : ℕ} {tr : Tree}
    (Pl : StepPlan p t.st.codes j cur next last l c n dS dC)
    (I : FormInv p j cur l t col row L c (n.code, n.maskCode) id tN tr) (rsF : List Fmt.RoundView)
    (fitF : roundsFit ((l.take (1 + cur.k)).map (·.1)) rsF = true) (rS rC : Fmt.RoundView)
    (fitS : roundsFit [dS, dC] [rS, rC] = true) :
    SwitchIn p j cur next n t.st.groups.size
      (foldT t row L c (n.code, n.maskCode) id (rsF.map noDigest))
      (foldOut t row L c id (rsF.map noDigest)) rC := by
  have hlen : (rsF.map noDigest).length = 1 + c.k := by
    rw [List.length_map, Sound.roundsFit_len _ _ fitF, length_of_foldCut Pl.cutF]
  obtain ⟨rE, rR, hrs⟩ : ∃ rE rR, rsF.map noDigest = rE :: rR := by
    cases h : rsF.map noDigest with
    | nil => rw [h] at hlen; simp at hlen; omega
    | cons rE rR => exact ⟨rE, rR, rfl⟩
  have hR : rR.length = c.k := by
    rw [hrs, List.length_cons] at hlen
    omega
  rw [hrs]
  have ff := foldedFit_of_front p j cur t row L c (n.code, n.maskCode) id rE rR (sgOf cur)
    (sgOf next) I.front Pl.codes Pl.zk Pl.codeN Pl.zkN Pl.sized.small I.kept0 I.keptL
    (hR.trans Pl.codes.k)
  obtain ⟨cd, hcd, ecd⟩ := Pl.codes.base
  have hc : Means.CFits (ceilLog2 (sgOf cur).C.l) (foldOut t row L c id (rE :: rR)).c := by
    have h1 := cfits_foldOutput (spent t.st id) (ioppFoldShape c L) row id (drawnOf rE)
      (rR.map drawnOf) (claimOf rR (maddE ((sentOf rE).getD 0 zeroE) (drawnOf rE) row.target))
      (by rw [List.length_map]; exact hR)
      ((Own.foldRowFits_agrees _ _ _).trans ((foldRowFits_spent _ _ _ _).trans I.front.rowFits))
    have e : ((spent t.st id).codes.base.getD (ioppFoldShape c L).code default).ell =
        (sgOf cur).C.l := by
      show (t.st.codes.base.getD c.code default).ell = _
      rw [Array.getD_eq_getD_getElem?, hcd]
      exact congrArg (·.l) ecd
    rw [e] at h1
    exact h1
  have hp : DenseForm (foldOut t row L c id (rE :: rR)).c :=
    denseForm_foldOutput (spent t.st id) (ioppFoldShape c L) row id (drawnOf rE) (rR.map drawnOf) _
      I.dense
  obtain ⟨-, ⟨-, -, -, g5⟩, -⟩ := fit_says fitS
  obtain ⟨-, -, -, -, -, -, -, -, -, c10, -⟩ := switchCut_says Pl.cutSw
  have hids : ∀ o ∈ singleRowsOracles (foldOut t row L c id (rE :: rR)),
      o ∈ L.members.toList ++ [id] := by
    intro o ho
    have ho' : o ∈ L.members.push id := ho
    rcases Array.mem_push.1 ho' with h1 | h1
    · exact List.mem_append_left _ (Array.mem_toList_iff.2 h1)
    · exact List.mem_append_right _ (List.mem_singleton.2 h1)
  have hG : (foldT t row L c (n.code, n.maskCode) id (rE :: rR)).st.groups[t.st.groups.size]? =
      some { code := n.code, maskCode := n.maskCode } := by
    show (t.st.groups.push _)[t.st.groups.size]? = _
    simp
  refine ⟨rfl, hG, inOrder_foldT t row L c _ id _ I.order, I.roots, ff, hp, hc, ?_, ?_, ?_⟩
  · intro z hz
    have := List.all_eq_true.1 g5 z hz
    rw [c10] at this
    exact of_decide_eq_true this
  · intro o ho
    have hos : (Ground.withGroup (spent t.st id) n.code n.maskCode).oracles.size =
        t.st.oracles.size := by
      simp [Ground.withGroup, spent]
    show o < (Ground.withGroup (spent t.st id) n.code n.maskCode).oracles.size
    rw [hos]
    exact I.seat.there o (hids o ho)
  · intro o ho pl hpl
    obtain ⟨q, hq, e⟩ := List.getElem_of_mem (hids o ho)
    have h1 := I.seat.place q hq
    rw [e] at h1
    have h2 : t.book.place[o]? = some pl := hpl
    obtain rfl : (tN, q) = pl := Option.some.inj (h1.symm.trans h2)
    show tN < t.book.trees.size
    rcases Nat.lt_or_ge tN t.book.trees.size with h3 | h3
    · exact h3
    · have := I.seat.inBook
      rw [Array.getElem?_eq_none h3] at this
      cases this

end Johnson.Prover.Link
