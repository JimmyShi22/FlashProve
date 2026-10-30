-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Reads/LiesBehind.lean: which of the 22 clauses of `Lies` (Reads/HeadAtRecord.lean) a
yes of the description's own steps at the output head's link brings.

What is shown. Steps: they speak of the written texts `K8.ReadsQuiet.head` and
`K8.ReadsQuiet.tables` (Johnson/Desc/K8/ReadsQuiet.lean) and of the seat's laying `setHeard`
(Johnson/Stored/HeadSeatAt.lean).
  `stepTab`, `partsLen`: what adding a table does to the vector's length and to the table of the
    tables. They read a line's matrix, parts, run and name, and not its array.
  `parts_len`, `addAsk_tab`, `fold_tab`, `fold_bare`: adding tables line after line does just that.
  `shapesH`, `asks_bare`, `planTab`: the fifteen lines without their arrays; the table of the tables
    that they give over a list of matrices.
  `tab_public`: **a yes of the text that makes the head's tables: their table of the tables is
    `planTab` of the shape and the plan's matrices.** So the clause tab holds at the filling whose
    public table is `planTab`.
  `laid_by_hearing`: behind a yes of the seat's `setHeard`: the state holds what was heard, the copy
    g1 in it is what the lookup heard, Zl is the last ls + lt coordinates of its point, and the two
    numbers of calls are 0. These are the clauses hX1, hX2, hqH, hqN.
  `Kept s s'`: where s stands in the head's link, so does s', with the same fields for what was
    heard and for what the lookup heard.
  `kept_refl`, `kept_trans`, `kept_putLink`, `kept_putFork`: tools.
  `kept_commit`: **a yes of a commitment's block at the state (`K1.commitAtS`,
    Johnson/Desc/K1/AtS.lean) keeps the two fields.**
  `claims_lay_nothing`: the seat's two layings of a run of claims return the state as it stands.
  `Core Z s o cov x t`, `Core.lies`: `Lies` without its clause letters, 21 clauses; with the letters
    it is `Lies`. The kind's letters are read where a run of claims is run, which is later than the
    quiet step: so what the steps bring is stated without them.
  `core_of_steps`: **`Core` at the state behind the reads' quiet step**, from: a yes of `setHeard`;
    `Kept` from there to the state in front of the quiet step; a yes of the quiet step; and seven
    clauses by name.
  `andThen_ok`: a tool: a yes of two blocks as one.
  `core_of_pieces`: **`Core` behind two yeses of the description's own texts at the head's link**:
    the kind's decision on its own rounds (`decideBy`, Johnson/Desc/Kinds/HeadFrame.lean), and then
    the block of a commitment with the reads' quiet step laid behind it (`K8.ReadsQuiet.behind`,
    Johnson/Desc/K8/ReadsQuietAt.lean, which says that the quiet step is seated so at the place of
    the reads' sending). `Kept` is no premise there.

Count, in `core_of_pieces`. Of the 21 clauses fourteen follow: nine from the yes of the quiet step
(here, opened, covered, heard, made, laid, mats, funs, nm); one is the law on the plan (tab); four
from what the hearing lays, kept by the commitment's block (hX1, hX2, hqH, hqN). Seven are premises:
cols; the sizes of four heard points; the sizes of the lookup's two points on the planes.

Limits. That the two texts of `core_of_pieces` stand one behind the other in the seated description,
with these parameters, is not shown here: `Kept` is shown of a commitment's block and of the two
writings, and is a premise of `core_of_steps`. The seven are shown by nothing here. No state of a
run is shown. Nothing on soundness.


-/
import Johnson.Desc.Reads.HeadAtRecord
import Johnson.Desc.Kinds.Law.HeardBack
import Johnson.Desc.K1.AtS
import Johnson.Desc.K8.ReadsQuietAt
import Johnson.Desc.Kinds.Law.Heard

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Reads.AtSeat

open OnBytes (E)
open OnBytes.Model (TMat HFun longPoint)
open OnBytes.Model.Head (Shape HL HPlanH2 Covered Tables costWeights ztOf)
open OnBytes.Road (bind_some)
open OnBytes.Road.Hd (Ask addAsk partStep addFun_eq asksH)
open VerifiableInference.Desc.First (S HeadOwn)
open VerifiableInference.Desc.K8 (ReadsQuiet.tables ReadsQuiet.head ReadsQuiet.PH
  ReadsQuiet.head_ok ReadsQuiet.closed_fields)
open VerifiableInference.Desc.Kinds
open VerifiableInference.Desc.Kinds.Head
open VerifiableInference.Desc.Kinds.Head.Law

/-! ## 1. The table of the tables is a function of the plan -/

/-- The vector's length behind n parts of a table. -/
def partsLen (mats : Array TMat) (M0 Lf p : ℕ) (n : ℕ) : ℕ :=
  (List.range n).foldl
    (fun w q => w + (mats.getD (M0 + q) {}).k * ((mats.getD (M0 + q) {}).m / Lf)) p

/-- What adding a table does to the length and to the table of the tables. -/
def stepTab (mats : Array TMat) (s : ℕ × List (String × ℕ × ℕ)) (a : Ask) :
    Option (ℕ × List (String × ℕ × ℕ)) :=
  if partsLen mats a.1 a.2.2.1 s.1 a.2.1 == s.1 then none
  else some (partsLen mats a.1 a.2.2.1 s.1 a.2.1,
    s.2 ++ [(a.2.2.2.2, s.1, partsLen mats a.1 a.2.2.1 s.1 a.2.1 - s.1)])

theorem parts_len (mats : Array TMat) (M0 Lf : ℕ) (phi : Array E) (funs : Array HFun) (p : ℕ) :
    ∀ n, ((List.range n).foldl (partStep mats M0 Lf phi) (funs, p)).2 = partsLen mats M0 Lf p n
  | 0 => rfl
  | n + 1 => by
    have ih := parts_len mats M0 Lf phi funs p n
    unfold partsLen at ih ⊢
    rw [List.range_succ, List.foldl_append, List.foldl_append]
    generalize (List.range n).foldl (partStep mats M0 Lf phi) (funs, p) = r at ih ⊢
    show r.2 + (mats.getD (M0 + n) {}).k * ((mats.getD (M0 + n) {}).m / Lf) = _
    rw [ih]
    rfl

theorem addAsk_tab (mats : Array TMat) (t : Tables) (a : Ask) :
    (addAsk mats t a).map (fun u => (u.p, u.tab)) = stepTab mats (t.p, t.tab) a := by
  unfold addAsk stepTab
  rw [addFun_eq, parts_len]
  by_cases hz : (partsLen mats a.1 a.2.2.1 t.p a.2.1 == t.p) = true
  · rw [if_pos hz, if_pos hz]
    rfl
  · rw [if_neg hz, if_neg hz]
    rfl

theorem fold_tab (mats : Array TMat) : ∀ (asks : List Ask) (t : Tables),
    (asks.foldlM (addAsk mats) t).map (fun u => (u.p, u.tab)) =
      asks.foldlM (stepTab mats) (t.p, t.tab)
  | [], _ => rfl
  | a :: rest, t => by
    rw [List.foldlM_cons, List.foldlM_cons, ← addAsk_tab]
    cases h : addAsk mats t a with
    | none => rfl
    | some u => exact fold_tab mats rest u

/-- A line without its array. -/
def bare (a : Ask) : Ask := (a.1, a.2.1, a.2.2.1, #[], a.2.2.2.2)

theorem fold_bare (mats : Array TMat) : ∀ (asks : List Ask) (s : ℕ × List (String × ℕ × ℕ)),
    asks.foldlM (stepTab mats) s = (asks.map bare).foldlM (stepTab mats) s
  | [], _ => rfl
  | a :: rest, s => by
    rw [List.map_cons, List.foldlM_cons, List.foldlM_cons]
    have e : stepTab mats s (bare a) = stepTab mats s a := rfl
    rw [e]
    cases stepTab mats s a with
    | none => rfl
    | some u => exact fold_bare mats rest u

/-- The fifteen lines without their arrays. -/
def shapesH (h : Shape) : List Ask :=
  [(0, h.NHf, 2 ^ h.la, #[], "hf@Z"), (0, h.NHf, 2 ^ h.la, #[], "hf@phiZ"),
   (h.NHf + 1 + 1 + 1, 1, 2 ^ h.la, #[], "xbL@Z_V"),
   (h.NHf + 1 + 1 + 1, 1, 2 ^ h.la, #[], "xbL@Y_N"),
   (h.NHf, 1, h.T, #[], "hd@zt_FC"), (h.NHf, 1, h.T, #[], "hd@r_H"),
   (h.NHf + 1, 1, h.T, #[], "hr@zt_ROW"), (h.NHf + 1, 1, h.T, #[], "hr@P_V"),
   (h.NHf + 1, 1, h.T, #[], "hr@r_tV"), (h.NHf + 1, 1, h.T, #[], "hr@rt_N"),
   (h.NHf + 1, 1, h.T, #[], "hr@phiC"), (h.NHf + 1, 1, h.T, #[], "hr@rhoC"),
   (h.NHf + 1 + 1, 1, 2 ^ h.lmbH, #[], "bH-bits-0"),
   (h.NHf + 1 + 1, 1, 2 ^ h.lmbH, #[], "bH-bits-1"),
   (h.NHf + 1 + 1, 1, 2 ^ h.lmbH, #[], "bH-pin")]

/-- They are the library's fifteen lines, whatever the arrays. -/
theorem asks_bare (h : Shape) (L : HL) (x : OnBytes.Model.Head.Heard)
    (ZV YN phiC rhoCv : Array E) (qFC qROW : ℕ) (b0 b1 : Array E) :
    (asksH h L x ZV YN phiC rhoCv qFC qROW b0 b1).map bare = shapesH h := by
  simp only [asksH, shapesH, List.map_cons, List.map_nil, bare]

/-- The table of the tables that the fifteen lines give over a list of matrices. -/
def planTab (h : Shape) (mats : Array TMat) : List (String × ℕ × ℕ) :=
  (((shapesH h).foldlM (stepTab mats) (0, [])).map (·.2)).getD []

/-- **The table of the tables is a function of the shape and the plan's matrices.** -/
theorem tab_public {h : Shape} {L : HL} {hp : HPlanH2} {cov : Covered}
    {x : OnBytes.Model.Head.Heard} {t : Tables} (e : ReadsQuiet.tables h L hp cov x = .ok t) :
    t.tab = planTab h hp.tl.mats := by
  obtain ⟨ZV, lowN, qFC, qROW, b0, b1, -, hf⟩ := tables_fold e
  have e1 := fold_tab hp.tl.mats (asksH h L x ZV (longPoint lowN.2 x.tN.r)
    (costWeights cov (ztOf h L x.g1 x.qH)).1 (costWeights cov (ztOf h L x.g1 x.qH)).2.2 qFC qROW
    b0 b1) ({} : Tables)
  rw [hf, fold_bare] at e1
  rw [asks_bare] at e1
  unfold planTab
  have e3 : (shapesH h).foldlM (stepTab hp.tl.mats) (0, []) = some (t.p, t.tab) := e1.symm
  rw [e3]
  rfl

/-! ## 2. What the hearing lays -/

/-- **Behind a yes of the seat's laying of what was heard.** -/
theorem laid_by_hearing (h : Shape) (iU3 : ℕ) {s s2 : S} {H : HeardAll}
    (e : (seatAt h iU3).setHeard s H = .ok s2) :
    ∃ o x, s2.here = .head o ∧ o.x = some x ∧ o.lookHeard = some x.g1 ∧
      x.Zl = Point.last x.g1.zx (h.ls + h.lt) ∧ x.qH = 0 ∧ x.qN = 0 ∧ x.PV = H.1.pV ∧
      x.wpl.r = H.1.squares.r ∧ x.tV.r = H.1.products.r ∧
      x.tH.r = H.2.2.logits.r.extract 0 h.lt := by
  obtain ⟨o, G, -, hG, rfl⟩ := setHeard_form h iU3 e
  exact ⟨_, _, rfl, rfl, hG, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## 3. The whole -/

/-- Where s stands in the head's link, so does s', with the same fields for what was heard and for
what the lookup heard. -/
def Kept (s s' : S) : Prop :=
  ∀ o, s.here = .head o → ∃ o', s'.here = .head o' ∧ o'.x = o.x ∧ o'.lookHeard = o.lookHeard

theorem kept_refl (s : S) : Kept s s := fun o ho => ⟨o, ho, rfl, rfl⟩

theorem kept_trans {s s' s'' : S} (h1 : Kept s s') (h2 : Kept s' s'') : Kept s s'' := by
  intro o ho
  obtain ⟨o', ho', a1, a2⟩ := h1 o ho
  obtain ⟨o'', ho'', b1, b2⟩ := h2 o' ho'
  exact ⟨o'', ho'', b1.trans a1, b2.trans a2⟩

/-- Writing the link's state keeps the two fields. -/
theorem kept_putLink (s : S) (L' : OnBytes.Model.LinkCtx) : Kept s (s.putLink L') := by
  intro o ho
  unfold S.putLink
  rw [ho]
  by_cases hop : o.opened = true
  · exact ⟨{ o with L := L' }, by simp [hop], rfl, rfl⟩
  · exact ⟨o, by simp [hop, ho], rfl, rfl⟩

/-- Writing the ledger keeps the two fields. -/
theorem kept_putFork (s : S) (F' : OnBytes.Model.Fork) : Kept s (s.putFork F') := by
  intro o ho
  unfold S.putFork
  rw [ho]
  by_cases hop : o.opened = true
  · exact ⟨{ o with F := F' }, by simp [hop], rfl, rfl⟩
  · exact ⟨o, by simp [hop, ho], rfl, rfl⟩

/-- **A commitment's block at the state keeps the two fields.** -/
theorem kept_commit {Cl : Type} (P : VerifiableInference.Desc.K1.Par) (link moment : ℕ)
    (arrays : Option (List ℕ)) {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (ℕ × List UInt64))}
    (h : (VerifiableInference.Desc.K1.commitAtS (Cl := Cl) P link moment arrays).decide s rs gs =
      .ok s') : Kept s s' := by
  unfold VerifiableInference.Desc.K1.commitAtS at h
  dsimp only at h
  split at h
  · rename_i L0 F0 tl0 _ _ _
    generalize (VerifiableInference.Desc.K1.commitOwn P link moment arrays).decide _ rs gs = r
      at h
    cases r with
    | error e => cases h
    | ok y =>
      have e : ((VerifiableInference.Desc.K1.laid s y.held.w).putLink y.held.L).putFork y.held.F =
          s' := Except.ok.inj h
      rw [← e]
      have k0 : Kept s (VerifiableInference.Desc.K1.laid s y.held.w) :=
        fun o ho => ⟨o, ho, rfl, rfl⟩
      exact kept_trans (kept_trans k0 (kept_putLink _ _)) (kept_putFork _ _)
  · cases h

/-- The seat's two layings of a run of claims return the state as it stands. -/
theorem claims_lay_nothing (h : Shape) (iU3 : ℕ) (s : S) (w : SumOnMatrix) (k : List Form) :
    (seatAt h iU3).setWeightClaim s w = s ∧ (seatAt h iU3).setKeyForms s k = s := ⟨rfl, rfl⟩

/-- `Lies` without its clause letters: 21 clauses. It names none of the kind's letters. -/
structure Core (Z : Fill) (s : S) (o : HeadOwn) (cov : Covered) (x : OnBytes.Model.Head.Heard)
    (t : Tables) : Prop where
  here : s.here = .head o
  opened : o.opened = true
  covered : s.covered Z.h.T Z.h.V = .ok cov
  heard : o.x = some x
  made : ReadsQuiet.tables Z.h Z.L Z.hp cov x = .ok t
  laid : o.t = some t
  cols : ∃ tr, o.F.trees[Z.iU3]? = some tr ∧ tr.K = Z.cols
  mats : o.tl.mats = Z.hp.tl.mats
  funs : o.tl.funs = t.funs
  nm : o.tl.NM = Z.hp.tl.NM
  tab : t.tab = Z.tab
  hX1 : o.lookHeard = some x.g1
  hX2 : x.Zl = Point.last x.g1.zx (Z.h.ls + Z.h.lt)
  hqH : x.qH < 6
  hqN : x.qN < 6
  hsPV : x.PV.size = Z.h.lt
  hsSq : x.wpl.r.size = (letI := sizesOf Z.h; Norm.lNI + Norm.lPd) + Z.h.lt
  hsTV : x.tV.r.size = Z.h.lt
  hsTH : x.tH.r.size = Z.h.lt
  hzb0 : x.g1.zb0.size = x.g1.shape.kT + x.g1.shape.cK + 5
  hzb1 : x.g1.zb1.size = x.g1.shape.kT + x.g1.shape.cK + 5

/-- With the letters, it is Lies. -/
theorem Core.lies {Z : Fill} {s : S} {o : HeadOwn} {cov : Covered}
    {x : OnBytes.Model.Head.Heard} {t : Tables} (Q : Core Z s o cov x t) {g : Given}
    {bh : Behind} {pl : Places}
    (hl : lettersAt (parOf Z.h Z.work) (seatAt Z.h Z.iU3) s = .ok (g, bh, pl)) :
    Lies Z s o cov x t g bh pl :=
  { here := Q.here, opened := Q.opened, covered := Q.covered, heard := Q.heard, made := Q.made
    laid := Q.laid, cols := Q.cols, mats := Q.mats, funs := Q.funs, nm := Q.nm, letters := hl
    tab := Q.tab, hX1 := Q.hX1, hX2 := Q.hX2, hqH := Q.hqH, hqN := Q.hqN, hsPV := Q.hsPV
    hsSq := Q.hsSq, hsTV := Q.hsTV, hsTH := Q.hsTH, hzb0 := Q.hzb0, hzb1 := Q.hzb1 }

/-- **Core, behind the reads' quiet step.** -/
theorem core_of_steps (Z : Fill) (hZ : Z.tab = planTab Z.h Z.hp.tl.mats)
    (place : VerifiableInference.Desc.Place)
    {s1 s2 s3 s4 : S} {H : HeardAll} (e2 : (seatAt Z.h Z.iU3).setHeard s1 H = .ok s2)
    (kept : Kept s2 s3) {rs : List Fmt.RoundView} {gs : List (List (ℕ × List UInt64))}
    (hd : (ReadsQuiet.head ⟨place, Z.h, Z.L, Z.hp⟩).decide s3 rs gs = .ok s4)
    (hcols : ∀ o, s4.here = .head o → ∃ tr, o.F.trees[Z.iU3]? = some tr ∧ tr.K = Z.cols)
    (hsPV : H.1.pV.size = Z.h.lt)
    (hsSq : H.1.squares.r.size = (letI := sizesOf Z.h; Norm.lNI + Norm.lPd) + Z.h.lt)
    (hsTV : H.1.products.r.size = Z.h.lt)
    (hsTH : (H.2.2.logits.r.extract 0 Z.h.lt).size = Z.h.lt)
    (hzb : ∀ o G, s2.here = .head o → o.lookHeard = some G →
      G.zb0.size = G.shape.kT + G.shape.cK + 5 ∧ G.zb1.size = G.shape.kT + G.shape.cK + 5) :
    ∃ o cov x t, Core Z s4 o cov x t := by
  obtain ⟨o2, x2, h2, hx2, hG2, hZl, hqH, hqN, p1, p2, p3, p4⟩ := laid_by_hearing Z.h Z.iU3 e2
  obtain ⟨o3, h3, hx3, hG3⟩ := kept o2 h2
  obtain ⟨a, cov, x, t, tl', ha, hop, hcov, hx, ht, hc, rfl⟩ := ReadsQuiet.head_ok hd
  obtain ⟨_, c2, c3, c4, _, _, _, _, _, _, _⟩ := ReadsQuiet.closed_fields hc
  have hao : a = o3 := by
    rw [h3] at ha
    exact (VerifiableInference.Desc.First.Here.head.inj ha).symm
  subst hao
  have hxx : x = x2 := by
    rw [hx3, hx2] at hx
    exact (Option.some.inj hx).symm
  subst hxx
  obtain ⟨z0, z1⟩ := hzb o2 x.g1 h2 hG2
  exact ⟨{ a with t := some t, tl := tl' }, cov, x, t,
    { here := rfl, opened := hop, covered := hcov, heard := hx, made := ht, laid := rfl
      cols := hcols _ rfl, mats := c4, funs := c2, nm := c3
      tab := (tab_public ht).trans hZ.symm, hX1 := hG3.trans hG2, hX2 := hZl
      hqH := by rw [hqH]; decide, hqN := by rw [hqN]; decide
      hsPV := by rw [p1]; exact hsPV, hsSq := by rw [p2]; exact hsSq
      hsTV := by rw [p3]; exact hsTV, hsTH := by rw [p4]; exact hsTH
      hzb0 := z0, hzb1 := z1 }⟩

/-! ## 4. Behind the two pieces of the head's link -/

/-- A yes of two blocks as one is a yes of the first and then of the second. -/
theorem andThen_ok {T Cl : Type} {name : String} {p q : VerifiableInference.Desc.Block T Cl}
    {s s' : T} {rs : List Fmt.RoundView} {gs : List (List (ℕ × List UInt64))}
    (h : (p.andThen name q).decide s rs gs = .ok s') :
    ∃ m, p.decide s (rs.take p.rounds.length) (gs.take p.openings) = .ok m ∧
      q.decide m (rs.drop p.rounds.length) (gs.drop p.openings) = .ok s' := by
  have h' : ((p.decide s (rs.take p.rounds.length) (gs.take p.openings)).bind fun m =>
      q.decide m (rs.drop p.rounds.length) (gs.drop p.openings)) = .ok s' := h
  cases hp : p.decide s (rs.take p.rounds.length) (gs.take p.openings) with
  | error e =>
    rw [hp] at h'
    cases h'
  | ok m =>
    rw [hp] at h'
    exact ⟨m, rfl, h'⟩

/-- **Core, behind a yes of the kind's decision on its own rounds and a yes of the block of the
reads' sending with the quiet step laid behind it.** -/
theorem core_of_pieces (Z : Fill) (hZ : Z.tab = planTab Z.h Z.hp.tl.mats)
    (place : VerifiableInference.Desc.Place) {rounds : Given → List Round}
    {hear : Given → Hear HeardAll} {weights : Given → Behind → SumOnMatrix} {s0 s2 s4 : S}
    {rs4 : List Fmt.RoundView}
    (h4 : decideBy rounds hear weights (parOf Z.h Z.work) (seatAt Z.h Z.iU3) s0 rs4 = .ok s2)
    (P : VerifiableInference.Desc.K1.Par) (link moment : ℕ) (arrays : Option (List ℕ))
    {rs : List Fmt.RoundView} {gs : List (List (ℕ × List UInt64))}
    (h5 : (VerifiableInference.Desc.K8.ReadsQuiet.behind
      (VerifiableInference.Desc.K1.commitAtS P link moment arrays)
      (ReadsQuiet.head ⟨place, Z.h, Z.L, Z.hp⟩)).decide s2 rs gs = .ok s4)
    (hcols : ∀ o, s4.here = .head o → ∃ tr, o.F.trees[Z.iU3]? = some tr ∧ tr.K = Z.cols)
    (hsz : ∀ o x, s2.here = .head o → o.x = some x →
      x.PV.size = Z.h.lt ∧
      x.wpl.r.size = (letI := sizesOf Z.h; Norm.lNI + Norm.lPd) + Z.h.lt ∧
      x.tV.r.size = Z.h.lt ∧ x.tH.r.size = Z.h.lt ∧
      x.g1.zb0.size = x.g1.shape.kT + x.g1.shape.cK + 5 ∧
      x.g1.zb1.size = x.g1.shape.kT + x.g1.shape.cK + 5) :
    ∃ o cov x t, Core Z s4 o cov x t := by
  obtain ⟨F, H, w, s1, s2', -, e2, hs2⟩ := decideBy_ok h4
  have hs2' : s2 = s2' := hs2
  subst hs2'
  obtain ⟨s3, c1, c2⟩ := andThen_ok h5
  obtain ⟨o2, x2, q2, hx2, hG2, -, -, -, p1, p2, p3, p4⟩ := laid_by_hearing Z.h Z.iU3 e2
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hsz o2 x2 q2 hx2
  refine core_of_steps Z hZ place e2 (kept_commit P link moment arrays c1) c2 hcols
    (by rw [← p1]; exact a1) (by rw [← p2]; exact a2) (by rw [← p3]; exact a3)
    (by rw [← p4]; exact a4) fun o G ho hG => ?_
  have e : o = o2 := by
    rw [q2] at ho
    exact (VerifiableInference.Desc.First.Here.head.inj ho).symm
  subst e
  have eG : G = x2.g1 := by
    rw [hG2] at hG
    exact (Option.some.inj hG).symm
  subst eG
  exact ⟨a5, a6⟩

end VerifiableInference.Reads.AtSeat

#print axioms VerifiableInference.Reads.AtSeat.parts_len
#print axioms VerifiableInference.Reads.AtSeat.addAsk_tab
#print axioms VerifiableInference.Reads.AtSeat.fold_tab
#print axioms VerifiableInference.Reads.AtSeat.fold_bare
#print axioms VerifiableInference.Reads.AtSeat.asks_bare
#print axioms VerifiableInference.Reads.AtSeat.tab_public
#print axioms VerifiableInference.Reads.AtSeat.laid_by_hearing
#print axioms VerifiableInference.Reads.AtSeat.kept_refl
#print axioms VerifiableInference.Reads.AtSeat.kept_trans
#print axioms VerifiableInference.Reads.AtSeat.kept_putLink
#print axioms VerifiableInference.Reads.AtSeat.kept_putFork
#print axioms VerifiableInference.Reads.AtSeat.kept_commit
#print axioms VerifiableInference.Reads.AtSeat.claims_lay_nothing
#print axioms VerifiableInference.Reads.AtSeat.Core.lies
#print axioms VerifiableInference.Reads.AtSeat.core_of_steps
#print axioms VerifiableInference.Reads.AtSeat.andThen_ok
#print axioms VerifiableInference.Reads.AtSeat.core_of_pieces
