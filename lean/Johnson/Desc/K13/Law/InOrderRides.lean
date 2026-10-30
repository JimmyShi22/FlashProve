-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/InOrderRides.lean: THE FIRST CHAIN's ITEM "in order" RIDES AT FURTHER
BLOCKS (K1's three, the quiet steps, the chain's last).

"In order" at the table of joints is filled by inOrderK13 (Johnson/Desc/K13/Law/FillK13.lean):
Tidy's test on the statement, and three values of
the record that are the plan's: the statement's codes, the request's shape and the rows' layout IN
THE WALK's OWN STATE OF THE CALLS (S.check).
At K13's two blocks (M:3, M:4) it rides by inOrderK13_rides (FillFromSentences.lean), whose premise
is that S.check stays WHOLE. K1's opening
TURNS S.check (the frame's group, moment, own …; sent; inLink; moments): so here the rule is typed
at just the three values.

  PlanSame s s'        the three values stay · refl · trans · of_check (where S.check stays whole)
  inOrderK13_rides'    the rule at PlanSame (inOrderK13_rides is its corollary at of_check)
  sendAtS_plan · commitAtS_plan · firstAtS_plan     K1's three blocks at the record: Decides
  PlanSame
  openingZero_plan     the joined block at G0:1 (the opening, then "link 0: opened")
  layers_plan · head_plan · blockAt_plan · behind_plan   the quiet steps K8.ReadsQuiet, and a block
  with such a step joined behind it
  firstEnd_plan        the first chain's last block (the record returns)
  inOrderK13_step      FROM A STEP's YES: where a block keeps "tidy in front, tidy behind" (Steps:
  Tidy/Chains.lean) and Decides PlanSame
  inOrder_send | _commit | _opening   so at K1's three blocks, by First.oursFirst_steps
  commitAtS_live       INSIDE A LINK: a later moment leaves the shape and the rows' layout in the
  link's own copy (S.live), which S.leaveLink lays
                       back over S.check: for whoever rides the two equations past the step that
                       leaves a link

OBJECT   the blocks' own texts (K1/AtS.lean · K1/First.lean · K8/ReadsQuiet.lean ·
K13/FirstEnd.lean), through decide | step
USER     the sentences «inOrder» of the table's layer at these blocks' places (typed by nobody yet)
What is not claimed. Part 1's frame's steps but "link 0: opened": so not the step that leaves a
link. That a description lays these blocks at
these places. Nothing on soundness.

-/
import Johnson.Desc.K13.Law.FillK13
import Johnson.Desc.Tidy.Chains
import Johnson.Desc.Means.TestsBack
import Johnson.Desc.K1.Law.LaterAtRecord
import Johnson.Desc.K1.Law.OpeningZero
import Johnson.Desc.K1.Law.KeptAtRecord
import Johnson.Desc.K1.Law.Around
import Johnson.Desc.K1.KeepsAtS
import Johnson.Goal.Meaning.RecK1
import Johnson.Desc.Tidy.Still
import Johnson.Desc.K8.ReadsQuietAt
import Johnson.Desc.BlockKeeps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Model OnBytes.Params Desc.Plain
open OnBytes.Means (Tidy tidy4B tidy4B_iff)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Keeps (Decides Steps andThen_decides quiet_decides)
open VerifiableInference.Desc.Ground (By TidyStay groundKeeps_grows)

variable {Cl : Type}

/-! ## 1 The three values, and the rule -/

/-- The three values of the record that "in order" holds against the plan stay. -/
def PlanSame (s s' : S) : Prop :=
  s'.st.codes = s.st.codes ∧ s'.check.frame.shape = s.check.frame.shape ∧ s'.check.rows.layout =
      s.check.rows.layout

theorem PlanSame.refl (s : S) : PlanSame s s := ⟨rfl, rfl, rfl⟩

theorem PlanSame.trans {a b c : S} (h : PlanSame a b) (k : PlanSame b c) : PlanSame a c :=
  ⟨k.1.trans h.1, k.2.1.trans h.2.1, k.2.2.trans h.2.2⟩

/-- Where the walk's own state of the calls stays whole. -/
theorem PlanSame.of_check {s s' : S} (hc : s'.st.codes = s.st.codes) (hk : s'.check = s.check) :
    PlanSame s s' :=
  ⟨hc, by rw [hk], by rw [hk]⟩

/-- **"In order" goes on wherever "tidy" does and the three values stay.** -/
theorem inOrderK13_rides' {cs : Codes} {sh : Params.ReqShape} {ly : Params.ReqLayout} {s s' : S}
    (ht : Tidy s.st → Tidy s'.st) (hp : PlanSame s s') (h : inOrderK13 cs sh ly s = true) :
        inOrderK13 cs sh ly s' = true := by
  unfold inOrderK13 at h ⊢
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h ⊢
  obtain ⟨⟨⟨t, c1⟩, c2⟩, c3⟩ := h
  exact ⟨⟨⟨tidy4B_iff.2 (ht (tidy4B_iff.1 t)), hp.1.trans c1⟩, hp.2.1.trans c2⟩, hp.2.2.trans c3⟩

/-! ## 2 K1's three blocks at the record -/

theorem putLink_check (s : S) (X : LinkCtx) : (s.putLink X).check = s.check := by
  unfold S.putLink
  split <;> first | rfl | (split <;> rfl)

theorem putFork_check (s : S) (X : Fork) : (s.putFork X).check = s.check := by
  unfold S.putFork
  split <;> first | rfl | (split <;> rfl)

/-- **W's sending.** S.check stays whole. -/
theorem sendAtS_plan (P : K1.Par) : Decides PlanSame (K1.sendAtS P : Block S Cl) := by
  intro s rs gs s' h
  refine PlanSame.of_check (K1.sendAtS_kept P s s' rs gs h).1 ?_
  simp only [K1.sendAtS] at h
  split at h
  · split at h
    · obtain ⟨y, -, rfl⟩ := Keeps.emap_ok h
      rfl
    · cases h
  · cases h

/-- **A segment's later moment.** It writes the link's own copy; S.check stays whole. -/
theorem commitAtS_plan (P : K1.Par) (link moment : Nat) (arrays : Option (List Nat)) :
    Decides PlanSame (K1.commitAtS P link moment arrays : Block S Cl) := by
  intro s rs gs s' h
  have hc := _root_.Meaning.K2.codes_of_grows (K1.Rel.commitAtS_keeps groundKeeps_grows P link
      moment arrays) h
  obtain ⟨L, L', F', w, -, -, e⟩ := VerifiableInference.Desc.K1.commitAtS_rec P link moment arrays s
      s' rs gs h
  refine PlanSame.of_check hc ?_
  rw [e, putFork_check, putLink_check]
  rfl

/-- The opening leaves the rows' state. -/
theorem firstOwn_rows {P : K1.Par} {owed : Option Nat} {c c' : ChainCheck} {d d' : DState Unit} {rs
    : List Fmt.RoundView}
    (h : K1.firstOwn P owed c d rs = .ok (c', d')) : c'.rows = c.rows := by
  unfold K1.firstOwn at h
  obtain ⟨_, _, h⟩ := _root_.Meaning.K2.bindE h
  obtain ⟨_, _, h⟩ := _root_.Meaning.K2.bindE h
  obtain ⟨_, _, h⟩ := _root_.Meaning.K2.bindE h
  obtain ⟨_, _, h⟩ := _root_.Meaning.K2.bindE h
  obtain ⟨_, _, h⟩ := _root_.Meaning.K2.bindE h
  obtain ⟨_, _, h⟩ := _root_.Meaning.K2.bindE h
  obtain ⟨⟨g, d₁⟩, _, h⟩ := _root_.Meaning.K2.bindE h
  obtain ⟨_, _, h⟩ := _root_.Meaning.K2.bindE h
  obtain ⟨⟨ids, d₂⟩, _, h⟩ := _root_.Meaning.K2.bindE h
  obtain ⟨_, _, h⟩ := _root_.Meaning.K2.bindE h
  obtain ⟨mask, _, h⟩ := _root_.Meaning.K2.bindE h
  obtain ⟨⟨f₂, d₃⟩, _, h⟩ := _root_.Meaning.K2.bindE h
  cases h
  rfl

/-- **The first segment's opening.** It TURNS S.check: the shape and the rows stay. -/
theorem firstAtS_plan (q : Params.First) (gp : GPar) : Decides PlanSame (K1.firstSegmentOpening q gp : Block S
    Cl) := by
  intro s rs gs s' h
  have hc := _root_.Meaning.K2.codes_of_grows (K1.Rel.firstAtS_keeps groundKeeps_grows q gp) h
  simp only [K1.firstSegmentOpening] at h
  obtain ⟨_, _, h⟩ := _root_.Meaning.K2.bindE h
  obtain ⟨⟨c, d⟩, h1, h⟩ := _root_.Meaning.K2.bindE h
  cases h
  exact ⟨hc, (_root_.Meaning.K2.firstOwn_frame h1).1, congrArg (·.layout) (firstOwn_rows h1)⟩

/-- **The joined block at G0:1**: the opening, then "link 0: opened". -/
theorem openingZero_plan (q : Params.First) (gp : GPar) (nm : String) (X :
    Johnson.Desc.First.Walk.LayPar) (fvs : List Bool)
    (kCol : Nat) : Decides PlanSame (K1.openingZero q gp nm X fvs kCol : Block S Cl) :=
  andThen_decides PlanSame (fun _ _ _ => PlanSame.trans) nm _ _ (firstAtS_plan q gp)
    (quiet_decides PlanSame _ _ _ _ _ fun s t h => by
      obtain ⟨a, e⟩ := Johnson.Desc.First.Walk.Tied.openLayZero_eq h
      rw [e]
      exact ⟨rfl, rfl, rfl⟩)

/-! ## 3 The quiet steps, and a block with such a step joined behind it -/

theorem layers_plan (P : K8.ReadsQuiet.PG) : Decides PlanSame (K8.ReadsQuiet.layers P) := fun s rs
    gs s' h =>
  have f := K8.ReadsQuiet.layers_frame h
  PlanSame.of_check (by rw [f.2.2.1]) f.2.2.2.2.2.1

theorem head_plan (P : K8.ReadsQuiet.PH) : Decides PlanSame (K8.ReadsQuiet.head P) := fun s rs gs s'
    h =>
  have f := K8.ReadsQuiet.head_frame h
  PlanSame.of_check (by rw [f.2.2.1]) f.2.2.2.2.2.1

theorem blockAt_plan (G : Array Layer.HPlan2) (hS : Head.Shape) (HLy : Head.HL) (H : Head.HPlanH2)
    (kinds : List (Nat × Nat)) (l : Nat)
    (b : Block S Unit) (h : K8.ReadsQuiet.blockAt G hS HLy H kinds l = some b) : Decides PlanSame b
        := by
  unfold K8.ReadsQuiet.blockAt at h
  obtain ⟨k, -, h⟩ := Option.bind_eq_some_iff.1 h
  split at h
  · obtain ⟨hp, -, rfl⟩ := Option.map_eq_some_iff.1 h
    exact layers_plan _
  · split at h
    · obtain rfl := Option.some.inj h
      exact head_plan _
    · cases h

theorem behind_plan (own q : Block S Unit) (ho : Decides PlanSame own) (hq : Decides PlanSame q) :
    Decides PlanSame (K8.ReadsQuiet.behind own q) :=
  andThen_decides PlanSame (fun _ _ _ => PlanSame.trans) _ own q ho hq

/-! ## 4 The seal -/

theorem firstEnd_plan (piece : Nat) (front : List (Block S Cl)) : Decides PlanSame (First.firstEnd
    piece front) := by
  intro s rs gs s' h
  have e : s' = s := Keeps.chainEnd_same 1 piece true _ First.endAsks h
  rw [e]
  exact PlanSame.refl s

/-! ## 5 From a step's yes -/

/-- **"In order" through a block's step.** -/
theorem inOrderK13_step {cs : Codes} {sh : Params.ReqShape} {ly : Params.ReqLayout} {b : Block S Cl}
    (hs : Steps (By TidyStay fun s : S => s.st) b) (hp : Decides PlanSame b) (hplan : b.planOk =
        true) (ft : Nat) (s : S)
    (rs : List Fmt.RoundView) (cols : List OpenedColumn) (s' : S) (n : Nat) (hst : b.step ft s rs cols = .ok (s',
                        n))
    (h : inOrderK13 cs sh ly s = true) : inOrderK13 cs sh ly s' = true :=
  inOrderK13_rides' (hs hplan ft s rs cols s' n hst) (Keeps.steps_of_decides hp hplan ft s rs cols
      s' n hst) h

theorem inOrder_send {cs : Codes} {sh : Params.ReqShape} {ly : Params.ReqLayout} (P : K1.Par)
    (hplan : (K1.sendAtS P : Block S Cl).planOk = true) (ft : Nat) (s : S) (rs : List Fmt.RoundView) (cols
               : List OpenedColumn) (s' : S) (n : Nat)
    (hst : (K1.sendAtS P : Block S Cl).step ft s rs cols = .ok (s', n)) (h : inOrderK13 cs sh ly s =
        true) :
    inOrderK13 cs sh ly s' = true :=
  inOrderK13_step (First.oursFirst_steps (.send P)) (sendAtS_plan P) hplan ft s rs cols s' n hst h

theorem inOrder_commit {cs : Codes} {sh : Params.ReqShape} {ly : Params.ReqLayout} (P : K1.Par)
    (link moment : Nat)
    (arrays : Option (List Nat)) (hplan : (K1.commitAtS P link moment arrays : Block S Cl).planOk =
        true) (ft : Nat) (s : S)
    (rs : List Fmt.RoundView) (cols : List OpenedColumn) (s' : S) (n : Nat)
    (hst : (K1.commitAtS P link moment arrays : Block S Cl).step ft s rs cols = .ok (s', n)) (h :
        inOrderK13 cs sh ly s = true) :
    inOrderK13 cs sh ly s' = true :=
  inOrderK13_step (First.oursFirst_steps (.commit P link moment arrays)) (commitAtS_plan P link
      moment arrays) hplan ft s rs cols s' n hst h

theorem inOrder_opening {cs : Codes} {sh : Params.ReqShape} {ly : Params.ReqLayout} (q :
    Params.First) (gp : GPar)
    (hplan : (K1.firstSegmentOpening q gp : Block S Cl).planOk = true) (ft : Nat) (s : S) (rs : List Fmt.RoundView)
        (cols : List OpenedColumn) (s' : S) (n : Nat)
    (hst : (K1.firstSegmentOpening q gp : Block S Cl).step ft s rs cols = .ok (s', n)) (h : inOrderK13 cs sh ly
                   s = true) :
    inOrderK13 cs sh ly s' = true :=
  inOrderK13_step (First.oursFirst_steps (.opening q gp)) (firstAtS_plan q gp) hplan ft s rs cols s'
      n hst h

/-! ## 6 Inside a link: the link's own copy -/

/-- A later moment leaves the rows' state of the copy that it turns. -/
theorem laterOwn_rows {P : K1.Par} {owed : Option Nat} {c c' : ChainCheck} {w w' : DState Unit} {rs
    : List Fmt.RoundView}
    (h : K1.laterOwn P owed c w rs = .ok (c', w')) : c'.rows = c.rows := by
  obtain ⟨ids, d₁, f', -, -, e⟩ := K1.laterOwn_ok P owed c c' w w' rs h
  rw [e]

theorem commitStep_rows {P : K1.Par} {owed : Option Nat} {ts : List Nat} {x y : _root_.L3.St (DState
    Unit)} {rs : List Fmt.RoundView}
    (h : _root_.L3.commitStep (K1.laterOwn P owed) ts x rs = .ok y) : y.L.check.rows =
        x.L.check.rows := by
  unfold _root_.L3.commitStep at h
  obtain ⟨_, _, h⟩ := _root_.Meaning.K2.bindE h
  obtain ⟨⟨check, w⟩, h1, h⟩ := _root_.Meaning.K2.bindE h
  obtain ⟨⟨L, F⟩, h2, h⟩ := _root_.Meaning.K2.bindE h
  cases h
  unfold _root_.L3.commitBehind at h2
  obtain ⟨F', _, h2⟩ := _root_.Meaning.K2.bindE h2
  split at h2
  · cases h2
    exact laterOwn_rows h1
  · cases h2

/-- **A segment's later moment leaves the shape and the rows' layout IN THE LINK's OWN COPY**
(S.live inside a link), which S.leaveLink
lays back over S.check. The shape: Meaning.K2.commitStep_frame. -/
theorem commitAtS_live (P : K1.Par) (link moment : Nat) (arrays : Option (List Nat)) (s s' : S) (rs
    : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (h : (K1.commitAtS P link moment arrays : Block S
        Cl).decide s rs gs = .ok s') :
    s'.live.frame.shape = s.live.frame.shape ∧ s'.live.rows.layout = s.live.rows.layout := by
  simp only [K1.commitAtS] at h
  split at h
  · rename_i L F tl hL hF htl
    obtain ⟨y, hy, rfl⟩ := Keeps.emap_ok h
    have hk : y.held.L.check.frame.shape = L.check.frame.shape ∧ y.held.L.check.rows = L.check.rows
        := by
      simp only [K1.commitOwn] at hy
      split at hy
      · split at hy
        · cases hy
        · obtain ⟨x, hx, rfl⟩ := Keeps.emap_ok hy
          exact ⟨(_root_.Meaning.K2.commitStep_frame hx).1, commitStep_rows hx⟩
      · cases hy
    have hl' : (((K1.laid s y.held.w).putLink y.held.L).putFork y.held.F).link? = some y.held.L :=
        by
      cases hs : s.here with
      | lay a => simp [S.putFork, S.putLink, S.link?, K1.laid, hs]
      | att a => simp [S.putFork, S.putLink, S.link?, K1.laid, hs]
      | head a =>
        have ho : a.opened = true := by
          by_contra hn
          simp [S.link?, hs, hn] at hL
        simp [S.putFork, S.putLink, S.link?, K1.laid, hs, ho]
      | between => simp [S.link?, hs] at hL
      | fin a => simp [S.link?, hs] at hL
      | mem a => simp [S.link?, hs] at hL
    simp only [S.live, hL, hl']
    exact ⟨hk.1, congrArg (·.layout) hk.2⟩
  · cases h

end VerifiableInference.Desc.K13.Law
