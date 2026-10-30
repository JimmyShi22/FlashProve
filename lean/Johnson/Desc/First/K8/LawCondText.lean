-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K8/LawCondText.lean: THE SMALLNESS TEST: THE CONDITIONS THAT ITS ROW OF THE TABLE
OF JOINTS ASKS OF ITS RECORD IN FRONT OF THE DRAW, FROM THE TEXT OF THE STEP THAT CLOSES THE LIST OF
TABLES.

The row of the block of the draw (`k08_row`, Johnson/Desc/First/K8/LawRow.lean) holds under a
condition on the carried record in front. Beside "no collision" it has two clauses on the smallness
test's record there: `SameLay (recOf tl0 s) tl0` (Johnson/Desc/First/K8/LawLay.lean: the symbol
arrays' numbers, the arrays' index and the digits' columns are the public record's) and `Extra s`
(Johnson/Desc/First/K8/LawItems.lean: the shapes fit the matrices; every table lies on the third
vector of reads). THAT RECORD IS LAID BY THE STEP THAT CLOSES THE LIST
(Johnson/Desc/K8/ReadsQuiet.lean): it is the place's own parameter, closed, with the list in the
list's place (Johnson/Desc/First/K8/LawReadyText.lean). So:
  `sameLay_of_tl`, `extra_of_tl`: at a record s whose smallness test's record is tlP, closed, with
    the list f: `SameLay tlP tl0` gives the first; `Port.Fits tlP` and "every table of f lies on the
    third vector" give the second.
  `layers_lays_tl`, `head_lays_tl`: WHICH LIST: behind a yes of the step at a layers' link: what the
    link's own rounds returned; at the head's link: the tables that the step itself makes.
  `LaysFrom tlP c`: where the decision of c goes on, the smallness test's record behind is tlP,
    closed, with some list; it passes to the block joined behind ANY block, and along `Block.Under`.
  `cond_of_laysFrom`; `cond_at_layers`, `cond_at_head`: **both clauses right behind the step AS IT
    IS SEATED** (any c under the step joined behind a block own: `Block.Under`: a yes of c is the
    same yes of the joint: what a seat's block has, whatever guards it lays).
  `tables_tree`: every table that the head's step makes lies on the third vector of reads: by the
    make of `tableAdded` (Johnson/Desc/Own/HeadTabs.lean). `cond_at_head_whole`: **so at the head's
    link nothing is asked of the list.**
Statements and proofs.
Limits. RIGHT BEHIND THE STEP: a block between it and the draw must leave the smallness test's
record. `SameLay P.tl tl0` and `Port.Fits P.tl` are facts on public values: shown at no value here;
at tl0 := P.tl with any list the first holds by `rfl`. AT A LAYERS' LINK, THAT EVERY TABLE OF THE
CLOSED LIST LIES ON THE THIRD VECTOR OF READS IS A PREMISE: on the record in front of own at a
layers' link it cannot even be said here, since own may turn what the link's own rounds returned: so
it is asked of the list that is closed. An attention link is not covered.

-/
import Johnson.Desc.First.K8.LawReadyText
import Johnson.Desc.First.K8.LawRow

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Ready

open OnBytes.Model
open VerifiableInference.Desc.K8 (ReadsQuiet.layers ReadsQuiet.head ReadsQuiet.PG ReadsQuiet.PH)

/-- The layout's clause, at a record whose smallness test's record is tlP, closed. -/
theorem sameLay_of_tl (tlP tl0 : HTailF2) (f : Array HFun) (s : S)
    (h : s.tl? = some { tlP with funClosed := true, funs := f }) (hl : SameLay tlP tl0) :
    SameLay (recOf tl0 s) tl0 := by
  unfold recOf
  rw [h]
  exact ⟨hl.gt, hl.ix, hl.mz, hl.off⟩

/-- The two further conditions there. -/
theorem extra_of_tl (tlP : HTailF2) (f : Array HFun) (s : S)
    (h : s.tl? = some { tlP with funClosed := true, funs := f })
    (hF : OnBytes.Tie.Pv.Tail.Port.Fits tlP) (ht : ∀ Fn ∈ f.toList, Fn.tree = 2) : Extra s := by
  intro tl e
  rw [h] at e
  obtain rfl := Option.some.inj e
  exact ⟨hF.of_same rfl rfl rfl, ht⟩

/-- Which list the step at a layers' link closes. -/
theorem layers_lays_tl (P : ReadsQuiet.PG) {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (h : (ReadsQuiet.layers P).decide s rs gs = .ok s') :
    ∃ a own, s.here = .lay a ∧ a.own = some own ∧
      s'.tl? = some { P.tl with funClosed := true, funs := own.funs } := by
  obtain ⟨a, own, tl', ha, ho, hc, e⟩ := VerifiableInference.Desc.K8.ReadsQuiet.layers_ok h
  obtain ⟨_, e', _, _⟩ := VerifiableInference.Desc.K8.ReadsQuiet.closed_ok hc
  refine ⟨a, own, ha, ho, ?_⟩
  rw [e, e']
  rfl

/-- Which list the step at the head's link closes. -/
theorem head_lays_tl (P : ReadsQuiet.PH) {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (h : (ReadsQuiet.head P).decide s rs gs = .ok s') :
    ∃ cov x t, VerifiableInference.Desc.K8.ReadsQuiet.tables P.h P.L P.hp cov x = .ok t ∧
      s'.tl? = some { P.hp.tl with funClosed := true, funs := t.funs } := by
  obtain ⟨a, cov, x, t, tl', _, ho, _, _, ht, hc, e⟩ :=
    VerifiableInference.Desc.K8.ReadsQuiet.head_ok h
  obtain ⟨_, e', _, _⟩ := VerifiableInference.Desc.K8.ReadsQuiet.closed_ok hc
  refine ⟨cov, x, t, ht, ?_⟩
  rw [e, e']
  simp [S.tl?, ho]

/-! ## Every table that the head's step makes lies on the third vector of reads -/

/-- One table more keeps it. -/
theorem tableAdded_tree (mats : Array TMat) (t t' : Head.Tables) (M0 parts Lf : Nat)
    (phi : Array OnBytes.E) (nm : String) (h : ∀ Fn ∈ t.funs.toList, Fn.tree = 2)
    (e : VerifiableInference.Desc.Own.tableAdded mats t M0 parts Lf phi nm = some t') :
    ∀ Fn ∈ t'.funs.toList, Fn.tree = 2 := by
  have key : ∀ (l : List Nat) (s : Array HFun × Nat), (∀ Fn ∈ s.1.toList, Fn.tree = 2) →
      ∀ Fn ∈ (l.foldl (fun (s : Array HFun × Nat) q =>
        (s.1.push { mat := M0 + q, len := Lf, phi := phi, tree := 2, start := s.2 },
          s.2 + (mats.getD (M0 + q) {}).k * ((mats.getD (M0 + q) {}).m / Lf))) s).1.toList,
        Fn.tree = 2 := by
    intro l
    induction l with
    | nil => exact fun s hs => hs
    | cons q l ih =>
      intro s hs
      refine ih _ fun Fn hFn => ?_
      simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hFn
      rcases hFn with hFn | rfl
      · exact hs Fn hFn
      · rfl
  unfold VerifiableInference.Desc.Own.tableAdded at e
  simp only at e
  split at e
  · exact nomatch e
  · obtain rfl := Option.some.inj e
    exact key (List.range parts) (t.funs, t.p) h

/-- A run of such steps keeps it. -/
theorem tablesAdded_tree (mats : Array TMat) :
    ∀ (asks : List (Nat × Nat × Nat × Array OnBytes.E × String)) (t t' : Head.Tables),
      (∀ Fn ∈ t.funs.toList, Fn.tree = 2) →
      asks.foldlM (fun t a => VerifiableInference.Desc.Own.tableAdded mats t a.1 a.2.1 a.2.2.1
        a.2.2.2.1 a.2.2.2.2) t = some t' → ∀ Fn ∈ t'.funs.toList, Fn.tree = 2
  | [], t, t', h, e => by
    obtain rfl : t = t' := Option.some.inj e
    exact h
  | a :: l, t, t', h, e => by
    rw [List.foldlM_cons] at e
    cases h1 : VerifiableInference.Desc.Own.tableAdded mats t a.1 a.2.1 a.2.2.1 a.2.2.2.1
        a.2.2.2.2 with
    | none =>
      rw [h1] at e
      exact nomatch e
    | some t1 =>
      rw [h1] at e
      exact tablesAdded_tree mats l t1 t' (tableAdded_tree mats t t1 _ _ _ _ _ h h1) e

/-- **Every table that the head's step makes lies on the third vector of reads.** -/
theorem tables_tree {h : Head.Shape} {L : Head.HL} {hp : Head.HPlanH2} {cov : Head.Covered}
    {x : Head.Heard} {t : Head.Tables}
    (e : VerifiableInference.Desc.K8.ReadsQuiet.tables h L hp cov x = .ok t) :
    ∀ Fn ∈ t.funs.toList, Fn.tree = 2 := by
  unfold VerifiableInference.Desc.K8.ReadsQuiet.tables at e
  obtain ⟨_, _, e⟩ := VerifiableInference.Desc.K8.ReadsQuiet.bind_ok e
  obtain ⟨_, _, e⟩ := VerifiableInference.Desc.K8.ReadsQuiet.bind_ok e
  obtain ⟨_, _, e⟩ := VerifiableInference.Desc.K8.ReadsQuiet.bind_ok e
  obtain ⟨_, _, e⟩ := VerifiableInference.Desc.K8.ReadsQuiet.bind_ok e
  obtain ⟨_, _, e⟩ := VerifiableInference.Desc.K8.ReadsQuiet.bind_ok e
  obtain ⟨_, _, e⟩ := VerifiableInference.Desc.K8.ReadsQuiet.bind_ok e
  obtain ⟨_, _, e⟩ := VerifiableInference.Desc.K8.ReadsQuiet.bind_ok e
  obtain ⟨_, _, e⟩ := VerifiableInference.Desc.K8.ReadsQuiet.bind_ok e
  obtain ⟨t', e8, e⟩ := VerifiableInference.Desc.K8.ReadsQuiet.bind_ok e
  obtain ⟨_, _, e⟩ := VerifiableInference.Desc.K8.ReadsQuiet.bind_ok e
  simp only [pure, Except.pure, Except.ok.injEq] at e
  subst e
  exact tablesAdded_tree _ _ {} t' (fun _ h => by simp at h)
    (VerifiableInference.Desc.K8.ReadsQuiet.named_ok e8)

/-- Where the decision of c goes on, the smallness test's record behind it is tl0, closed, with some
list. -/
def LaysFrom {Cl : Type} (tl0 : HTailF2) (c : Block S Cl) : Prop :=
  ∀ s rs gs s', c.decide s rs gs = .ok s' →
    ∃ funs, s'.tl? = some { tl0 with funClosed := true, funs := funs }

theorem ClosesFrom.laysFrom {Cl : Type} {tl0 : HTailF2} {c : Block S Cl} (h : ClosesFrom tl0 c) :
    LaysFrom tl0 c := fun s rs gs s' hd => (h s rs gs s' hd).1

/-- Joined behind any block. -/
theorem LaysFrom.behind {Cl : Type} {tl0 : HTailF2} {q : Block S Cl} (h : LaysFrom tl0 q)
    (own : Block S Cl) (name : String) : LaysFrom tl0 (Block.andThen name own q) := by
  intro s rs gs s' H
  obtain ⟨t, _, H⟩ :=
    bindOk (x := own.decide s (rs.take own.rounds.length) (gs.take own.openings)) H
  exact h _ _ _ _ H

theorem LaysFrom.guards {Cl : Type} {tl0 : HTailF2} {c b : Block S Cl} (h : LaysFrom tl0 b)
    (g : Guards c b) : LaysFrom tl0 c := fun s rs gs s' hd => h s rs gs s' (g.yes hd)

theorem LaysFrom.under {Cl Cl' : Type} {tl0 : HTailF2} {c : Block S Cl'} {b : Block S Cl}
    (h : LaysFrom tl0 b) (u : c.Under b) : LaysFrom tl0 c :=
  fun s rs gs s' hd => h s rs gs s' (u s rs gs s' hd)

/-- **Both clauses right behind such a block.** -/
theorem cond_of_laysFrom {Cl : Type} (tlP tl0 : HTailF2) (c : Block S Cl) (h : LaysFrom tlP c)
    (hl : SameLay tlP tl0) (hF : OnBytes.Tie.Pv.Tail.Port.Fits tlP)
    (s s' : S) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (hd : c.decide s rs gs = .ok s')
    (ht : ∀ tl, s'.tl? = some tl → ∀ Fn ∈ tl.funs.toList, Fn.tree = 2) :
    SameLay (recOf tl0 s') tl0 ∧ Extra s' := by
  obtain ⟨f, hf⟩ := h s rs gs s' hd
  exact ⟨sameLay_of_tl tlP tl0 f s' hf hl, extra_of_tl tlP f s' hf hF (ht _ hf)⟩

/-- At a layers' link, at the step as it is seated. -/
theorem cond_at_layers {Cl : Type} (P : ReadsQuiet.PG) (own : Block S Unit) (c : Block S Cl)
    (g : c.Under (VerifiableInference.Desc.K8.ReadsQuiet.behind own (ReadsQuiet.layers P)))
    (tl0 : HTailF2) (hl : SameLay P.tl tl0) (hF : OnBytes.Tie.Pv.Tail.Port.Fits P.tl)
    (s s' : S) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (hd : c.decide s rs gs = .ok s')
    (ht : ∀ tl, s'.tl? = some tl → ∀ Fn ∈ tl.funs.toList, Fn.tree = 2) :
    SameLay (recOf tl0 s') tl0 ∧ Extra s' :=
  cond_of_laysFrom P.tl tl0 c (((layers_closesFrom P).laysFrom.behind own own.name).under g) hl hF
    s s' rs gs hd ht

/-- At the head's link. -/
theorem cond_at_head {Cl : Type} (P : ReadsQuiet.PH) (own : Block S Unit) (c : Block S Cl)
    (g : c.Under (VerifiableInference.Desc.K8.ReadsQuiet.behind own (ReadsQuiet.head P)))
    (tl0 : HTailF2) (hl : SameLay P.hp.tl tl0) (hF : OnBytes.Tie.Pv.Tail.Port.Fits P.hp.tl)
    (s s' : S) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (hd : c.decide s rs gs = .ok s')
    (ht : ∀ tl, s'.tl? = some tl → ∀ Fn ∈ tl.funs.toList, Fn.tree = 2) :
    SameLay (recOf tl0 s') tl0 ∧ Extra s' :=
  cond_of_laysFrom P.hp.tl tl0 c (((head_closesFrom P).laysFrom.behind own own.name).under g) hl
    hF s s' rs gs hd ht

/-- **At the head's link nothing is asked of the list**: the step makes it. -/
theorem cond_at_head_whole {Cl : Type} (P : ReadsQuiet.PH) (own : Block S Unit) (c : Block S Cl)
    (g : c.Under (VerifiableInference.Desc.K8.ReadsQuiet.behind own (ReadsQuiet.head P)))
    (tl0 : HTailF2) (hl : SameLay P.hp.tl tl0) (hF : OnBytes.Tie.Pv.Tail.Port.Fits P.hp.tl)
    (s s' : S) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (hd : c.decide s rs gs = .ok s') : SameLay (recOf tl0 s') tl0 ∧ Extra s' := by
  obtain ⟨t, _, H⟩ :=
    bindOk (x := own.decide s (rs.take own.rounds.length) (gs.take own.openings))
      (g s rs gs s' hd)
  obtain ⟨cov, x, tb, htb, hf⟩ := head_lays_tl P H
  exact ⟨sameLay_of_tl P.hp.tl tl0 tb.funs s' hf hl,
    extra_of_tl P.hp.tl tb.funs s' hf hF (tables_tree htb)⟩

end VerifiableInference.Desc.First.K8.Ready

#print axioms VerifiableInference.Desc.First.K8.Ready.tables_tree
#print axioms VerifiableInference.Desc.First.K8.Ready.cond_at_head_whole
#print axioms VerifiableInference.Desc.First.K8.Ready.sameLay_of_tl
#print axioms VerifiableInference.Desc.First.K8.Ready.extra_of_tl
#print axioms VerifiableInference.Desc.First.K8.Ready.layers_lays_tl
#print axioms VerifiableInference.Desc.First.K8.Ready.head_lays_tl
#print axioms VerifiableInference.Desc.First.K8.Ready.cond_of_laysFrom
#print axioms VerifiableInference.Desc.First.K8.Ready.cond_at_layers
#print axioms VerifiableInference.Desc.First.K8.Ready.cond_at_head
