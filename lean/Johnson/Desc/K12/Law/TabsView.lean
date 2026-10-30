-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/TabsView.lean: the columns of a real view of the proximity test (the kind K12)
are columns of tables: at a view that passes the two tests of Block.step there are written oracles
whose columns are the view's.

Why. The verifier accK of the lemma on the proximity test (Johnson/Desc/K12/Law/K12Lemma.lean) is
Block.step at a written view: its columns are read off written oracles. That accK says yes at any
transcript was not shown. Johnson/Desc/K12/Law/RoundIsOf.lean brings a yes of the step at a real
view to a yes of accK, under one premise: that the real view's columns are the written columns of
some oracles. This file pays that premise. It is Johnson/Desc/K12/Law/ViewWide.lean read backwards.
Definitions, statements and proofs.
Main names:
  `forall₂_at`, `pick`, `nOpen_opens`, `laid_stored`, `getLast_at`: tools.
  `WOk`, `wants_fit`: the wants of declared rounds that store nothing are, group by group, those of
    the declared openings: the positions of a group differ (they are a Fmt.listOf), each lies inside
    the opening's depth, each want has the opening's width.
  `gfit_of_kpw`, `gfit_view`: so the groups that Block.step shows the decision at a view that passes
    its two tests fit the openings that the test declares behind "BAT" (GFit,
    Johnson/Desc/K12/Law/TabsFrom.lean).
  `TabAt`: a written round and oracle are a table for the first switch's i-th opening.
  `Ready`, `ready_of`, `Ready.group`: what the premises on the place and the record give, in one
    bundle.
  `book_tables`, `tab_deep`: a table for each of the book's trees D.ts; such tables are as deep and
    as wide as the book's trees.
  `tabs_join`: with such tables, for every first message there are transcripts of the blocks with
    that message's oracle at which the view's columns are the written ones.
  `tables_of_view`: there are W0, fM and a transcript τ₀ with DeepK, fM a function of the first
    message's oracle alone, and the view's columns are colsOf at srcK over these letters. Here fM is
    the constant W0 D.fresh.t.
  `alone_of_ok`: what the yes of the test aloneOk (Johnson/Desc/K12/Law/AloneOk.lean) says: no
    member of the group under test shares the mask's tree.
  `tables_of_view_own`: the same at fM := orc1 c, the letter that reads the mask's table off the
    chain's first message, where the mask is the test's own.
How. The i-th of the book's trees D.ts is opened by the first switch's i-th declared opening, once
(D.ts is a Fmt.listOf: no place stands twice), so the i-th group alone speaks of it, and
table_of_gok gives an oracle with that group's columns. Its written round is any round with the
opening's shape as its tree. Depth and width are the book's by gpL's clauses opens.a and opens.W. In
the own arm the mask's tree is the last of D.ts, its written round is the chain's first (ownTieOk),
and the first message is given the oracle. The later stages' tables and the transcripts are
tabsFirst's (Johnson/Desc/K12/Law/TabsFrom.lean).
Limits: No soundness is claimed, and nothing is said on hiding.
tables_of_view gives the CONSTANT fM: the first mask's table stands among W0's, whatever the first
message. That meets DeepK and the statement asked for; where the mask is the test's own it is not
the letter at which the law is spent: tables_of_view_own is.
Premises of both: planOk, dealOk and tieOk (tests on the plan); gpOf's value D and the yes of gpL at
it (tests on the record); the chain's make; Block.Fits at the view (the step's own two tests). Of
tables_of_view_own also: p.nums.ownMask = true and ownTieOk (the plan); the last of D.ts is
D.fresh.t (the test lastOk of Johnson/Desc/K12/Law/OwnSeat.lean gives it) and aloneOk D (the
record). The last two are a run's word, and aloneOk has been evaluated nowhere yet; neither is
proved from the text that enters the mask.
No premise on the columns' words: since each tree is opened once, and the positions of a group
differ, no two dealt columns can clash.
The tables are made to fit the opened columns: outside the opened positions nothing is said of them,
and nothing is said of what a prover committed to.
Every theorem of this file is proved outright; what each rests on is printed at the file's end.

-/
import Johnson.Desc.K12.Law.TabsFrom
import Johnson.Desc.K12.Law.OwnTieLaw
import Johnson.Desc.K12.Law.AloneOk

set_option autoImplicit false
namespace H2K.First
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun
open Iop Prob Cb Cb.Ood _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.JointK H2K.Sw
open H2K.Pub (WR writtenOf kk sgOf chainFrom Letters)
open H2K.Onto (Orcs orcsOf tr_with)

/-- Two lists that stand in a relation member by member, read at a number. -/
theorem forall₂_at {α β : Type} (R : α → β → Prop) {l : List α} {m : List β}
    (h : List.Forall₂ R l m) : ∀ (i : ℕ) (a : α), l[i]? = some a → ∃ b, m[i]? = some b ∧ R a b := by
  induction h with
  | nil => intro i a h; cases h
  | cons h1 _ ih =>
    intro i a h
    cases i with
    | zero =>
      obtain rfl := Option.some.inj h
      exact ⟨_, rfl, h1⟩
    | succ i => exact ih i a h

/-- The wants of one declared opening: the positions differ, each is inside the opening's depth, and
each want has the opening's width. -/
def WOk (o : Fmt.Shape × Fmt.TreeSource) (g : List Want) : Prop :=
  (g.map (·.2.1)).Nodup ∧ ∀ w ∈ g, w.2.1 < 2 ^ o.1.a ∧ w.2.2 = o.1.W

/-- The groups of wants of declared rounds that store nothing are, group by group, those of the
declared openings. -/
theorem wants_fit (F : ℕ) : ∀ (ds : List Fmt.DeclaredRound) (Rs : List Fmt.Drawn),
    (∀ d ∈ ds, d.stored = []) → ds.length = Rs.length →
    List.Forall₂ WOk (ds.flatMap (·.opens)) (groupsOf F ds Rs)
  | [], [], _, _ => List.Forall₂.nil
  | [], _ :: _, _, h => by cases h
  | _ :: _, [], _, h => by cases h
  | d :: ds, R :: Rs, hst, hl => by
    rw [groupsOf_cons, List.flatMap_cons]
    refine List.rel_append ?_ (wants_fit F ds Rs (fun x hx => hst x (List.mem_cons_of_mem _ hx))
      (Nat.succ.inj hl))
    unfold grp1
    rw [hst d List.mem_cons_self, List.map_nil, List.nil_append]
    refine List.forall₂_map_right_iff.2 (List.forall₂_same.2 fun o _ => ⟨?_, ?_⟩)
    · rw [List.map_map]
      have e : ((fun w : Want => w.2.1) ∘ fun x : ℕ => ((o.1.tree - F, x,
          o.1.W) : Want)) = id := rfl
      rw [e, List.map_id]
      exact (Fmt.listOf_incr _).imp fun h => Nat.ne_of_lt h
    · intro w hw
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hw
      exact ⟨listOf_lt _ _ _ (Nat.pow_pos (by omega)) hx, rfl⟩

/-- Columns whose key, position and width are the wants, laid into groups, fit the openings. -/
theorem gfit_of_kpw {ops : List (Fmt.Shape × Fmt.TreeSource)} {groups : List (List Want)}
    (h : List.Forall₂ WOk ops groups) : ∀ cs : List VerifiableInference.Desc.OpenedColumn,
    cs.map kpw = groups.flatMap id → GFit ops (regroup (groups.map (·.length)) cs) := by
  induction h with
  | nil => intro cs _; exact List.Forall₂.nil
  | @cons o g ops groups h1 _ ih =>
    intro cs hk
    have hk' : cs.map kpw = g ++ groups.flatMap id := by rw [hk, List.flatMap_cons]; rfl
    have t1 : (cs.take g.length).map kpw = g := by
      rw [List.map_take, hk', List.take_left' rfl]
    have t2 : (cs.drop g.length).map kpw = groups.flatMap id := by
      rw [List.map_drop, hk', List.drop_left' rfl]
    show List.Forall₂ GOk (o :: ops) (((cs.take g.length).map fun c => (c.2.1, c.2.2)) ::
      regroup (groups.map (·.length)) (cs.drop g.length))
    refine List.Forall₂.cons ⟨?_, ?_⟩ (ih _ t2)
    · have e : ((cs.take g.length).map fun c => (c.2.1, c.2.2)).map (·.1) = g.map (·.2.1) := by
        conv_rhs => rw [← t1]
        rw [List.map_map, List.map_map]
        rfl
      rw [e]
      exact h1.1
    · intro x hx
      obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hx
      have hm : kpw c ∈ g := by
        rw [← t1]
        exact List.mem_map.2 ⟨c, hc, rfl⟩
      exact h1.2 _ hm

/-- A value for each member of a list without a double, by the member. -/
theorem pick {β : Type} (ts : List ℕ) (hnd : ts.Nodup) (P : ℕ → β → Prop)
    (h : ∀ (i z : ℕ), ts[i]? = some z → ∃ u, P i u) (dflt : β) :
    ∃ W : ℕ → β, ∀ (i z : ℕ), ts[i]? = some z → P i (W z) := by
  classical
  refine ⟨fun z => if hz : ∃ i, ts[i]? = some z then
    Classical.choose (h (Classical.choose hz) z (Classical.choose_spec hz)) else dflt, ?_⟩
  intro i z hi
  have hz : ∃ i, ts[i]? = some z := ⟨i, hi⟩
  have e : Classical.choose hz = i := by
    have h1 := Classical.choose_spec hz
    obtain ⟨a1, a2⟩ := List.getElem?_eq_some_iff.1 h1
    obtain ⟨b1, b2⟩ := List.getElem?_eq_some_iff.1 hi
    exact (List.Nodup.getElem_inj_iff hnd).1 (a2.trans b2.symm)
  simp only [dif_pos hz]
  have key : ∀ (j : ℕ) (hj : ts[j]? = some z), j = i → P i (Classical.choose (h j z hj)) := by
    intro j hj ej
    subst ej
    exact Classical.choose_spec (h j z hj)
  exact key (Classical.choose hz) (Classical.choose_spec hz) e

theorem nOpen_opens : ∀ (cut : List Fmt.DeclaredRound), (∀ d ∈ cut, d.stored = []) →
    nOpen cut = (cut.flatMap (·.opens)).length
  | [], _ => rfl
  | d :: l, h => by
    rw [nOpen_cons, List.flatMap_cons, List.length_append, h d List.mem_cons_self,
      nOpen_opens l fun x hx => h x (List.mem_cons_of_mem _ hx)]
    simp

/-- The place's declared rounds store nothing. -/
theorem laid_stored (p : P12) : ∀ x ∈ (laidOf p).map (·.1), x.stored = [] := by
  intro d hd
  unfold laidOf at hd
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hd
  cases hrn : H2U.roundsOfNums p.nums with
  | none =>
    rw [hrn] at hx
    simp at hx
  | some rds =>
    rw [hrn] at hx
    exact roundsOfNums_stored _ rds hrn _ (List.of_mem_zip hx).1

/-- The real view's groups fit the openings that the test declares behind "BAT". -/
theorem gfit_view (p : P12) (F : ℕ) (hplan : (proximityTestKind guardedProximityTestParts p : Blk').planOk = true)
    (hbat : nOpen (((laidOf p).take 1).map (·.1)) = 0) (rs : List Fmt.RoundView)
    (cols : List VerifiableInference.Desc.OpenedColumn) (hfit : (proximityTestKind guardedProximityTestParts p : Blk').Fits F rs cols) :
    GFit (((laidS p).map (·.1)).flatMap (·.opens)) ((proximityTestKind guardedProximityTestParts p : Blk').shown F rs cols) := by
  have hrd := H2K.Sw.k12_rounds guardedProximityTestParts p hplan
  obtain ⟨hf1, hf2⟩ := hfit
  have hlen : (proximityTestKind guardedProximityTestParts p : Blk').rounds.length = (rs.map (·.drawn)).length := by
    rw [List.length_map]
    exact roundsFit_length _ _ hf1
  have hk : (cols.take ((proximityTestKind guardedProximityTestParts p : Blk').want F rs).length).map kpw =
      (groupsOf F (proximityTestKind guardedProximityTestParts p : Blk').rounds (rs.map (·.drawn))).flatMap id := beq_iff_eq.1 hf2
  have hG0 := gfit_of_kpw (wants_fit F (proximityTestKind guardedProximityTestParts p : Blk').rounds (rs.map (·.drawn))
    (by rw [hrd]; exact laid_stored p) hlen)
    (cols.take ((proximityTestKind guardedProximityTestParts p : Blk').want F rs).length) hk
  have hops : (proximityTestKind guardedProximityTestParts p : Blk').rounds.flatMap (·.opens) =
      ((laidS p).map (·.1)).flatMap (·.opens) := by
    rw [hrd]
    conv_lhs => rw [← List.take_append_drop 1 ((laidOf p).map (·.1)), List.flatMap_append,
      ← List.map_take, opens_nil _ hbat, List.nil_append, ← List.map_drop]
    rfl
  rw [hops] at hG0
  exact hG0

/-- The written round and oracle u are a table for the first switch's i-th opening: the round's tree
has the opening's shape, and the columns of the i-th dealt group are the oracle's. -/
def TabAt (D : Plain) (G : Gs) (i : ℕ) (u : WO) : Prop :=
  ∀ o, D.opens[i]? = some o → u.1.tree = some o.1 ∧
    ∀ grp, G[i]? = some grp → ∀ x ∈ grp, x.2 = colW u.1 u.2 x.1

/-- What the premises on the place and on the record give, in one bundle. -/
structure Ready (p : P12) (a : Fmt.M1.Stage) (D : Plain) (G : Gs) : Prop where
  cut0 : nOpen (cutF (laidS p) a.k) = 0
  opens : D.opens = (cutS (laidS p) a.k).flatMap (·.opens)
  len : D.opens.length = D.ts.length
  nodup : D.ts.Nodup
  fit : GFit (((laidS p).map (·.1)).flatMap (·.opens)) G

theorem Ready.group {p : P12} {a : Fmt.M1.Stage} {D : Plain} {G : Gs} (h : Ready p a D G) (i : ℕ)
    (o : Fmt.Shape × Fmt.TreeSource) (ho : D.opens[i]? = some o) :
    ∃ grp, G[i]? = some grp ∧ GOk o grp := by
  refine forall₂_at GOk h.fit i o ?_
  rw [opens_split (laidS p) a.k h.cut0, ← h.opens,
    List.getElem?_append_left (List.getElem?_eq_some_iff.1 ho).1]
  exact ho

theorem ready_of (p : P12) (F : ℕ) (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (t : T12)
    (row : GroupRow) (L : GroupLayout) (D : Plain)
    (hplan : (proximityTestKind guardedProximityTestParts p : Blk').planOk = true) (hdeal : dealOk p = true)
    (htie : tieOk p = true) (hs : p.nums.stages = a :: rest) (hD : gpOf p t a L = some D)
    (hok : H2K.First.ok (gpL p a row D) = true) (rs : List Fmt.RoundView)
    (cols : List VerifiableInference.Desc.OpenedColumn) (hfit : (proximityTestKind guardedProximityTestParts p : Blk').Fits F rs cols) :
    Ready p a D ((proximityTestKind guardedProximityTestParts p : Blk').shown F rs cols) := by
  obtain ⟨_, _, _, hbat, _, _⟩ := tied_of_ok p a rest hs htie
  have hDl := dealt_of_ok p a rest hs hdeal
  have hm := made_of p t a L D hD
  refine ⟨?_, ?_, ?_, ?_, gfit_view p F hplan hbat rs cols hfit⟩
  · cases rest with
    | nil => exact absurd rfl hDl.1
    | cons nxt rest' => exact hDl.1
  · rw [hm.opens, ← opensOf_cut]
    rfl
  · have := congrArg List.length (opens_a_of_ok p a row D hok)
    rwa [List.length_map, List.length_map] at this
  · rw [hm.ts]
    exact (Fmt.listOf_incr _).imp fun h => Nat.ne_of_lt h

/-- A table for each of the book's trees that the first switch opens. d0: any written round. -/
theorem book_tables {p : P12} {a : Fmt.M1.Stage} {D : Plain} {G : Gs} (h : Ready p a D G)
    (d0 : PQ.RD) : ∃ W0 : ℕ → WO, ∀ (i z : ℕ), D.ts[i]? = some z → TabAt D G i (W0 z) := by
  refine pick D.ts h.nodup (TabAt D G) ?_ ⟨d0, (wRound d0).dOrc⟩
  intro i z hz
  have hi : i < D.opens.length := by
    rw [h.len]
    exact (List.getElem?_eq_some_iff.1 hz).1
  obtain ⟨grp, hg, hgok⟩ := h.group i D.opens[i] (List.getElem?_eq_getElem hi)
  obtain ⟨orc, horc⟩ := table_of_gok { d0 with tree := some D.opens[i].1 } D.opens[i] rfl grp hgok
  refine ⟨⟨_, orc⟩, fun o' ho' => ?_⟩
  obtain rfl := Option.some.inj ((List.getElem?_eq_getElem hi).symm.trans ho')
  exact ⟨rfl, fun grp' hg' => by
    obtain rfl := Option.some.inj (hg.symm.trans hg')
    exact horc⟩

/-- Such tables are as deep and as wide as the book's trees. -/
theorem tab_deep (p : P12) (a : Fmt.M1.Stage) (row : GroupRow) (D : Plain) (G : Gs)
    (hok : H2K.First.ok (gpL p a row D) = true) (i z : ℕ) (hi : D.ts[i]? = some z) (u : WO)
    (hu : TabAt D G i u) :
    PQ.posN u.1.tree = 2 ^ logAt D.book z ∧ PQ.colW u.1.tree = widthAt D.book z := by
  have ha := congrArg (·[i]?) (opens_a_of_ok p a row D hok)
  have hWd := congrArg (·[i]?) (opens_W_of_ok p a row D hok)
  simp only [List.getElem?_map, hi, Option.map_some] at ha hWd
  cases ho : D.opens[i]? with
  | none =>
    rw [ho] at ha
    cases ha
  | some o =>
    rw [ho] at ha hWd
    rw [(hu o ho).1]
    exact ⟨congrArg (2 ^ ·) (Option.some.inj ha), Option.some.inj hWd⟩

/-- With tables W for the book's trees: for every first message m1 there are transcripts b of the
blocks, with m1's oracle in their first message, at which the view's columns are the written ones.
-/
theorem tabs_join (p : P12) (F : ℕ) (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) {s : Sg}
    (c : Chain s) (w0 : WR) (ws : List WR) (D : Plain) (hdeal : dealOk p = true)
    (htie : tieOk p = true) (hs : p.nums.stages = a :: rest) (hst : stagesOf c = p.nums.stages)
    (hw : writtenOf p.nums = some (w0 :: ws)) (hr : c.rds = ws.map WR.rd) (rs : List Fmt.RoundView)
    (cols : List VerifiableInference.Desc.OpenedColumn) (hfit : (proximityTestKind guardedProximityTestParts p : Blk').Fits F rs cols)
    (hR : Ready p a D ((proximityTestKind guardedProximityTestParts p : Blk').shown F rs cols)) (W : ℕ → WO)
    (hW : ∀ (i z : ℕ), D.ts[i]? = some z →
      TabAt D ((proximityTestKind guardedProximityTestParts p : Blk').shown F rs cols) i (W z)) (m1 : H2K.Pub.Msg1 c) :
    ∃ b : c.Bl, orc1 c (H2K.Pub.msg1 c b) = orc1 c m1 ∧
      cols.take ((proximityTestKind guardedProximityTestParts p : Blk').want F rs).length =
        colsOf (groupsOf F (proximityTestKind guardedProximityTestParts p : Blk').rounds (rs.map (·.drawn)))
          (srcK p c b D.ts fun z x => colW (W z).1 (W z).2 x) := by
  obtain ⟨w0', w', hw', hbat, _, hT⟩ := tied_of_ok p a rest hs htie
  obtain ⟨rfl, rfl⟩ := List.cons.inj (Option.some.inj (hw.symm.trans hw'))
  have hDl := dealt_of_ok p a rest hs hdeal
  have hnS : nOpen (cutS (laidS p) a.k) = ((cutS (laidS p) a.k).flatMap (·.opens)).length := by
    refine nOpen_opens _ fun d hd => laid_stored p d ?_
    unfold cutS at hd
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hd
    exact List.mem_map.2 ⟨x, List.mem_of_mem_drop (List.mem_of_mem_drop (List.mem_of_mem_take hx)),
      rfl⟩
  obtain ⟨b, hb, hF⟩ := tabsFirst p c a rest (laidS p) ws (hst.trans hs) hr hDl hT D.ts
    (fun z x => colW (W z).1 (W z).2 x) ((proximityTestKind guardedProximityTestParts p : Blk').shown F rs cols) hR.fit
    (by
      intro i grp hi hg x hx
      rw [hnS, ← hR.opens] at hi
      have hi' : i < D.ts.length := by rw [← hR.len]; exact hi
      have hz : D.ts[i]? = some D.ts[i] := List.getElem?_eq_getElem hi'
      have hget : D.ts.getD i 0 = D.ts[i] := by rw [List.getD_eq_getElem?_getD, hz]; rfl
      rw [hget]
      exact (hW i _ hz _ (List.getElem?_eq_getElem hi)).2 grp hg x hx)
    hnS m1
  refine ⟨b, hb, cols_of_follows _ _ _ (beq_iff_eq.1 hfit.2) fun i grp hi x hx => ?_⟩
  unfold srcK
  rw [hbat, if_neg (Nat.not_lt_zero _), Nat.sub_zero]
  exact hF i grp hi x hx

theorem fresh_in (p : P12) (t : T12) (a : Fmt.M1.Stage) (L : GroupLayout) (D : Plain)
    (hm : Made p t a L D) : D.fresh.t ∈ D.ts := by
  rw [hm.ts, Fmt.listOf_mem]
  exact List.mem_append_right _ (List.mem_singleton.2 rfl)

theorem mem_in (p : P12) (t : T12) (a : Fmt.M1.Stage) (L : GroupLayout) (D : Plain)
    (hm : Made p t a L D) (i : Fin D.mems.length) : (D.mems.get i).t ∈ D.ts := by
  rw [hm.ts, Fmt.listOf_mem]
  exact List.mem_append_left _ (List.mem_map.2 ⟨_, List.get_mem _ i, rfl⟩)

/-- **The view's columns are columns of tables**, with the mask's table among W0's. -/
theorem tables_of_view (p : P12) (F : ℕ) (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) {s : Sg}
    (c : Chain s) (w0 : WR) (ws : List WR) (t : T12) (row : GroupRow) (L : GroupLayout) (D : Plain)
    (hplan : (proximityTestKind guardedProximityTestParts p : Blk').planOk = true) (hdeal : dealOk p = true)
    (htie : tieOk p = true) (hs : p.nums.stages = a :: rest) (hst : stagesOf c = p.nums.stages)
    (hw : writtenOf p.nums = some (w0 :: ws)) (hr : c.rds = ws.map WR.rd)
    (hD : gpOf p t a L = some D) (hok : H2K.First.ok (gpL p a row D) = true)
    (r0 : Fmt.RoundView) (rs' : List Fmt.RoundView) (cols : List VerifiableInference.Desc.OpenedColumn)
    (hfit : (proximityTestKind guardedProximityTestParts p : Blk').Fits F (r0 :: rs') cols) :
    ∃ (W0 : ℕ → WO) (fM : H2K.Pub.Msg1 c → WO) (τ₀ : Tr (PQ.uL (ckP .two) c.rds)),
      DeepK D W0 fM ∧ (∀ m m', orc1 c m = orc1 c m' → fM m = fM m') ∧
      cols.take ((proximityTestKind guardedProximityTestParts p : Blk').want F (r0 :: rs')).length =
        colsOf (groupsOf F (proximityTestKind guardedProximityTestParts p : Blk').rounds ((r0 :: rs').map (·.drawn)))
          (srcK p c (blOf c τ₀) D.ts fun z x =>
            colW (wAt c W0 D.fresh.t fM (blOf c τ₀) z).1 (wAt c W0 D.fresh.t fM (blOf c τ₀) z).2 x)
    := by
  have hm := made_of p t a L D hD
  have hR := ready_of p F a rest t row L D hplan hdeal htie hs hD hok (r0 :: rs') cols hfit
  obtain ⟨W0, hW0⟩ := book_tables hR (WR.rd w0)
  have hat : ∀ z ∈ D.ts, PQ.posN (W0 z).1.tree = 2 ^ logAt D.book z ∧
      PQ.colW (W0 z).1.tree = widthAt D.book z := by
    intro z hz
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hz
    exact tab_deep p a row D _ hok i z hi _ (hW0 i z hi)
  have hfr := fresh_in p t a L D hm
  have hdeep : DeepK D W0 (fun _ : H2K.Pub.Msg1 c => W0 D.fresh.t) := by
    refine ⟨fun i => ?_, fun _ => ?_, fun _ _ _ => rfl, fun z hz _ => (hat z hz).2,
      fun _ => (hat _ hfr).2⟩
    · rw [← (keyAt_of (F := 0) (hm.mem i).2).2]
      exact (hat _ (mem_in p t a L D hm i)).1
    · rw [← (keyAt_of (F := 0) hm.fresh).2]
      exact (hat _ hfr).1
  obtain ⟨τd, _⟩ := tr_with c.rds (dOrcs c.rds)
  obtain ⟨b, _, hb⟩ := tabs_join p F a rest c w0 ws D hdeal htie hs hst hw hr (r0 :: rs') cols hfit
    hR W0 hW0 (H2K.Pub.msg1 c (blOf c τd))
  refine ⟨W0, fun _ => W0 D.fresh.t, c.trL b, hdeep, fun _ _ _ => rfl, ?_⟩
  rw [blOf_trL]
  have hwA : wAt c W0 D.fresh.t (fun _ => W0 D.fresh.t) b = W0 := Function.update_eq_self _ _
  rw [hwA]
  exact hb

theorem alone_of_ok (D : Plain) (h : aloneOk D = true) (i : Fin D.mems.length) :
    (D.mems.get i).t ≠ D.fresh.t := by
  unfold aloneOk at h
  rw [List.all_eq_true] at h
  exact bne_iff_ne.1 (h _ (List.get_mem _ i))

theorem getLast_at {α : Type} (l : List α) (x : α) (h : l.getLast? = some x) :
    l[l.length - 1]? = some x := by
  rw [List.getLast?_eq_getElem?] at h
  exact h

/-- **The same where the mask is the test's own**: the letter fM reads the mask's table off the
chain's first message. -/
theorem tables_of_view_own (p : P12) (F : ℕ) (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) {s : Sg}
    (c : Chain s) (w0 : WR) (ws : List WR) (t : T12) (row : GroupRow) (L : GroupLayout) (D : Plain)
    (hplan : (proximityTestKind guardedProximityTestParts p : Blk').planOk = true) (hdeal : dealOk p = true)
    (htie : tieOk p = true) (hs : p.nums.stages = a :: rest) (hst : stagesOf c = p.nums.stages)
    (hw : writtenOf p.nums = some (w0 :: ws)) (hr : c.rds = ws.map WR.rd)
    (hD : gpOf p t a L = some D) (hok : H2K.First.ok (gpL p a row D) = true)
    (ho : p.nums.ownMask = true) (hown : ownTieOk p = true)
    (hl : D.ts.getLast? = some D.fresh.t) (hal : aloneOk D = true)
    (r0 : Fmt.RoundView) (rs' : List Fmt.RoundView) (cols : List VerifiableInference.Desc.OpenedColumn)
    (hfit : (proximityTestKind guardedProximityTestParts p : Blk').Fits F (r0 :: rs') cols) :
    ∃ (W0 : ℕ → WO) (τ₀ : Tr (PQ.uL (ckP .two) c.rds)),
      DeepK D W0 (orc1 c) ∧
      cols.take ((proximityTestKind guardedProximityTestParts p : Blk').want F (r0 :: rs')).length =
        colsOf (groupsOf F (proximityTestKind guardedProximityTestParts p : Blk').rounds ((r0 :: rs').map (·.drawn)))
          (srcK p c (blOf c τ₀) D.ts fun z x =>
            colW (wAt c W0 D.fresh.t (orc1 c) (blOf c τ₀) z).1
              (wAt c W0 D.fresh.t (orc1 c) (blOf c τ₀) z).2 x) := by
  have hm := made_of p t a L D hD
  have hR := ready_of p F a rest t row L D hplan hdeal htie hs hD hok (r0 :: rs') cols hfit
  obtain ⟨W0, hW0⟩ := book_tables hR (WR.rd w0)
  have hfr := fresh_in p t a L D hm
  -- the first written round behind "BAT" sends the shape of the first switch's last opening
  obtain ⟨wE, o, e1, e2, e3, _⟩ := ownTie_of_ok p a rest hs ho hown
  rw [← hm.opens] at e2
  have e1' : ws[0]? = some wE := by
    have : writtenB p = ws := by
      unfold writtenB
      rw [hw]
      rfl
    rw [← this]
    exact e1
  have hiT := getLast_at _ _ hl
  have hiO := getLast_at _ _ e2
  rw [hR.len] at hiO
  obtain ⟨grp, hg, hgok⟩ := hR.group _ o hiO
  obtain ⟨τd, _⟩ := tr_with c.rds (dOrcs c.rds)
  -- a first message with a table for that opening
  have hm1 : ∃ m1 : H2K.Pub.Msg1 c, (∀ m, (orc1 c m).1.tree = some o.1) ∧
      ∀ x ∈ grp, x.2 = colW (orc1 c m1).1 (orc1 c m1).2 x.1 := by
    cases c with
    | last s e dL dB fu fs εb =>
      have hd : dL = WR.rd wE := by
        have h0 : ([dL, dB] : List PQ.RD)[0]? = (ws.map WR.rd)[0]? := congrArg (·[0]?) hr
        rw [List.getElem?_map, e1'] at h0
        exact Option.some.inj h0
      obtain ⟨orc, horc⟩ := table_of_gok dL o (by rw [hd]; exact e3) grp hgok
      exact ⟨(orc, (H2K.Pub.msg1 _ (blOf _ τd)).2), fun _ => by rw [← e3]; exact congrArg _ hd,
        horc⟩
    | step s s' hf n0 e dE dT dS dC fW fZ fG εf εc next =>
      have hd : dE = WR.rd wE := by
        have h0 : (foldRds s dE dT ++ ([dS, dC] ++ next.rds))[0]? = (ws.map WR.rd)[0]? :=
          congrArg (·[0]?) hr
        rw [List.getElem?_map, e1'] at h0
        exact Option.some.inj h0
      obtain ⟨orc, horc⟩ := table_of_gok dE o (by rw [hd]; exact e3) grp hgok
      exact ⟨(orc, (H2K.Pub.msg1 _ (blOf _ τd)).2), fun _ => by rw [← e3]; exact congrArg _ hd,
        horc⟩
  obtain ⟨m1, ht1, hc1⟩ := hm1
  -- the tables, with the mask's read off the first message
  have hW : ∀ (i z : ℕ), D.ts[i]? = some z →
      TabAt D ((proximityTestKind guardedProximityTestParts p : Blk').shown F (r0 :: rs') cols) i
        (Function.update W0 D.fresh.t (orc1 c m1) z) := by
    intro i z hi
    by_cases ez : z = D.fresh.t
    · subst ez
      rw [Function.update_self]
      have ei : i = D.ts.length - 1 := by
        obtain ⟨a1, a2⟩ := List.getElem?_eq_some_iff.1 hi
        obtain ⟨b1, b2⟩ := List.getElem?_eq_some_iff.1 hiT
        exact (List.Nodup.getElem_inj_iff hR.nodup).1 (a2.trans b2.symm)
      subst ei
      intro o' ho'
      obtain rfl := Option.some.inj (hiO.symm.trans ho')
      exact ⟨ht1 m1, fun grp' hg' => by
        obtain rfl := Option.some.inj (hg.symm.trans hg')
        exact hc1⟩
    · rw [Function.update_of_ne ez]
      exact hW0 i z hi
  have hatF : ∀ m, PQ.posN (orc1 c m).1.tree = 2 ^ logAt D.book D.fresh.t ∧
      PQ.colW (orc1 c m).1.tree = widthAt D.book D.fresh.t := by
    intro m
    have h1 := tab_deep p a row D _ hok _ _ hiT _ (hW _ _ hiT)
    rw [Function.update_self, ht1 m1] at h1
    rw [ht1 m]
    exact h1
  have hdeep : DeepK D W0 (orc1 c) := by
    refine ⟨fun i => ?_, fun m => ?_, fun i _ e => absurd e (alone_of_ok D hal i),
      fun z hz _ => ?_, fun m => (hatF m).2⟩
    · rw [← (keyAt_of (F := 0) (hm.mem i).2).2]
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 (mem_in p t a L D hm i)
      exact (tab_deep p a row D _ hok j _ hj _ (hW0 j _ hj)).1
    · rw [← (keyAt_of (F := 0) hm.fresh).2]
      exact (hatF m).1
    · obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hz
      exact (tab_deep p a row D _ hok j _ hj _ (hW0 j _ hj)).2
  obtain ⟨b, hb1, hb⟩ := tabs_join p F a rest c w0 ws D hdeal htie hs hst hw hr (r0 :: rs') cols
      hfit
    hR _ hW m1
  refine ⟨W0, c.trL b, hdeep, ?_⟩
  rw [blOf_trL]
  have hwA : wAt c W0 D.fresh.t (orc1 c) b = Function.update W0 D.fresh.t (orc1 c m1) := by
    unfold wAt
    rw [hb1]
  rw [hwA]
  exact hb

end H2K.First

#print axioms H2K.First.gfit_view
#print axioms H2K.First.tables_of_view
#print axioms H2K.First.tables_of_view_own
