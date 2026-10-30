-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/StoredLists.lean: the library's lists on stored tables, round by round.

In the case with stored tables the library (Run/PlanQX.lean) keeps the openings of stored tables in
one list for the whole chain, each with the number of its round, and looks them up by that number.
The strict reader's description (`Fmt.SpecX`) has one list for each round. This file rewrites the
library's functions on the first form as plain functions on the second.

Main definitions: `xoOf`, `xsOf`, `Cut`, `SameLengths`.
Main theorems: `xsAt_xsOf`, `offStored_rounds`, `storedB_eq`, `wantedX_eq`, `fullX_true`.
It claims nothing on what a chain proves.
-/
import Run.PlanQXRun
import Run.PageIsTabProofs
import OnBytes.Tie.StoredRead

set_option autoImplicit false

namespace OnBytes.Tie
open Run Run.PQ

/-- An opening of a stored table in round i, in the library's form. -/
def xoOf (i : ℕ) (s : Fmt.Stored) : XO := ⟨i, s.item == 1, s.lo, s.count⟩

/-- All openings of stored tables of a chain, in the library's form. -/
def xsOf (tss : List (List Fmt.Stored)) : List XO :=
  tss.zipIdx.flatMap fun t => t.1.map fun s => ⟨t.2, s.item == 1, s.lo, s.count⟩

/-- This is the library's own list. -/
theorem xs_eq (D : XD) : D.xs = xsOf D.stored := rfl

/-- Of one round's openings, the filter by the round's number i keeps all or none. -/
theorem filter_round_map (ts : List Fmt.Stored) (k i : ℕ) :
    ((ts.map fun s => (⟨k, s.item == 1, s.lo, s.count⟩ : XO)).filter (·.round == i)) =
      if k = i then ts.map (xoOf i) else [] := by
  by_cases h : k = i
  · subst h
    rw [if_pos rfl, List.filter_eq_self.2]
    · rfl
    · intro x hx
      obtain ⟨s, _, rfl⟩ := List.mem_map.1 hx
      simp
  · rw [if_neg h, List.filter_eq_nil_iff]
    intro x hx
    obtain ⟨s, _, rfl⟩ := List.mem_map.1 hx
    simp [h]

/-- The same as `xsAt_xsOf` below, for lists that are numbered from k on. -/
theorem xsAt_from : ∀ (tss : List (List Fmt.Stored)) (k i : ℕ),
    xsAt ((tss.zipIdx k).flatMap fun t => t.1.map fun s =>
        (⟨t.2, s.item == 1, s.lo, s.count⟩ : XO)) i =
      if k ≤ i then (tss.getD (i - k) []).map (xoOf i) else []
  | [], k, i => by
    by_cases h : k ≤ i
    · rw [if_pos h]
      rfl
    · rw [if_neg h]
      rfl
  | ts :: tss, k, i => by
    have ih := xsAt_from tss (k + 1) i
    unfold xsAt at ih ⊢
    rw [List.zipIdx_cons, List.flatMap_cons, List.filter_append, ih, filter_round_map]
    rcases Nat.lt_trichotomy i k with h | h | h
    · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      rfl
    · subst h
      rw [if_pos rfl, if_neg (by omega), if_pos (Nat.le_refl _), Nat.sub_self, List.append_nil]
      rfl
    · rw [if_neg (by omega), if_pos (by omega), if_pos (by omega), List.nil_append,
        show i - k = (i - (k + 1)) + 1 by omega]
      rfl

/-- The openings behind round i are those of the description's list number i. -/
theorem xsAt_xsOf (tss : List (List Fmt.Stored)) (i : ℕ) :
    xsAt (xsOf tss) i = (tss.getD i []).map (xoOf i) := by
  have h := xsAt_from tss 0 i
  rw [if_pos (Nat.zero_le _), Nat.sub_zero] at h
  exact h

/-- A round as read, cut in two: without the stored tables' openings, and these openings. -/
abbrev Cut : Type := Fmt.RoundOut × List (Fmt.Shape × List ℕ × Fmt.OpenOut)

/-- Each round has as many openings of stored tables as its list says. -/
abbrev SameLengths (tss : List (List Fmt.Stored)) (rc : List Cut) : Prop :=
  List.Forall₂ (fun (ts : List Fmt.Stored) (p : Cut) => ts.length = p.2.length) tss rc

/-- If a list is known from its place k on, it is known from its place k + 1 on. -/
theorem getD_step {α : Type} (whole : List (List α)) (k : ℕ) (ts : List α) (tss : List (List α))
    (hw : ∀ j, whole.getD (k + j) [] = (ts :: tss).getD j []) :
    ∀ j, whole.getD (k + 1 + j) [] = tss.getD j [] := by
  intro j
  have h := hw (j + 1)
  rw [show k + 1 + j = k + (j + 1) by omega, h]
  rfl

/-- The same as `offStored_rounds` below, for rounds that are numbered from k on. -/
theorem offStored_from (whole : List (List Fmt.Stored)) : ∀ (tss : List (List Fmt.Stored))
    (rc : List Cut) (k : ℕ), SameLengths tss rc →
    (∀ j, whole.getD (k + j) [] = tss.getD j []) →
    (((rc.map roundWithStoredOpenings).zipIdx k).map fun r =>
        { r.1 with opens := r.1.opens.drop (xsAt (xsOf whole) r.2).length }) = rc.map (·.1)
  | _, _, _, .nil, _ => rfl
  | ts :: tss, p :: rc, k, .cons h t, hw => by
    have ih := offStored_from whole tss rc (k + 1) t (getD_step whole k ts tss hw)
    have h0 : whole.getD k [] = ts := hw 0
    rw [List.map_cons, List.zipIdx_cons, List.map_cons, ih, List.map_cons]
    congr 1
    show { roundWithStoredOpenings p with opens := (p.2 ++ p.1.opens).drop (xsAt (xsOf whole) k).length } = p.1
    rw [xsAt_xsOf, h0, List.length_map, List.drop_left' h.symm]
    rfl

/-- With the stored tables' openings taken off, o's rounds are the parts without them, under the two
hypotheses of `storedB_eq` below. -/
theorem offStored_rounds (tss : List (List Fmt.Stored)) (o : Fmt.ChainOut)
    (rc : List (Fmt.RoundOut × List (Fmt.Shape × List ℕ × Fmt.OpenOut)))
    (ho : o.rounds.toList = rc.map roundWithStoredOpenings)
    (hl : List.Forall₂ (fun (ts : List Fmt.Stored)
      (p : Fmt.RoundOut × List (Fmt.Shape × List ℕ × Fmt.OpenOut)) => ts.length = p.2.length)
      tss rc) :
    (offStored (xsOf tss) o).rounds.toList = rc.map (·.1) := by
  unfold offStored
  rw [ho]
  exact offStored_from tss tss rc 0 hl fun j => by rw [Nat.zero_add]

/-- The same as `storedB_eq` below, for rounds that are numbered from k on. -/
theorem storedB_from (whole : List (List Fmt.Stored)) : ∀ (tss : List (List Fmt.Stored))
    (rc : List Cut) (k : ℕ), SameLengths tss rc →
    (∀ j, whole.getD (k + j) [] = tss.getD j []) →
    (((rc.map roundWithStoredOpenings).zipIdx k).flatMap fun r =>
        ((xsAt (xsOf whole) r.2).zip r.1.opens).map fun y =>
          (y.1.which, y.2.1.W,
            (⟨y.2.1.a, y.2.2.1, y.2.2.2.cols, y.2.2.2.salts, y.2.2.2.given⟩ : OpenB))) =
      (tss.zip rc).flatMap fun y => (y.1.zip y.2.2).map fun z =>
        (z.1.item == 1, z.2.1.W, obOf z.2)
  | _, _, _, .nil, _ => rfl
  | ts :: tss, p :: rc, k, .cons h t, hw => by
    have ih := storedB_from whole tss rc (k + 1) t (getD_step whole k ts tss hw)
    have h0 : whole.getD k [] = ts := hw 0
    rw [List.map_cons, List.zipIdx_cons, List.flatMap_cons, ih, List.zip_cons_cons,
      List.flatMap_cons]
    congr 1
    show (((xsAt (xsOf whole) k).zip (p.2 ++ p.1.opens)).map _) = _
    have hz : ((ts.map (xoOf k)).zip (p.2 ++ p.1.opens)) = (ts.map (xoOf k)).zip p.2 := by
      have e := List.zip_append (l₁ := ts.map (xoOf k)) (r₁ := []) (l₂ := p.2) (r₂ := p.1.opens)
        (by rw [List.length_map, h])
      rw [List.append_nil] at e
      rw [e, List.zip_nil_left, List.append_nil]
    rw [xsAt_xsOf, h0, hz, List.zip_map_left, List.map_map]
    rfl

/-- The library's list `storedB` is the rounds' openings of stored tables, round behind round, each
with its table, if o's rounds are rc with the stored openings joined in, and each round has as many
stored openings as tables. -/
theorem storedB_eq (tss : List (List Fmt.Stored)) (o : Fmt.ChainOut)
    (rc : List (Fmt.RoundOut × List (Fmt.Shape × List ℕ × Fmt.OpenOut)))
    (ho : o.rounds.toList = rc.map roundWithStoredOpenings)
    (hl : List.Forall₂ (fun (ts : List Fmt.Stored)
      (p : Fmt.RoundOut × List (Fmt.Shape × List ℕ × Fmt.OpenOut)) => ts.length = p.2.length)
      tss rc) :
    storedB (xsOf tss) o =
      (tss.zip rc).flatMap fun y => (y.1.zip y.2.2).map fun z =>
        (z.1.item == 1, z.2.1.W, obOf z.2) := by
  unfold storedB
  rw [ho]
  exact storedB_from tss tss rc 0 hl fun j => by rw [Nat.zero_add]

/-- The same as `wantedX_eq` below, for rounds that are numbered from i on. -/
theorem wantedXL_from (S : Fmt.Spec) (a : ℕ) (whole : List (List Fmt.Stored)) :
    ∀ (rs : List Fmt.Round) (ros : List Fmt.RoundOut) (tss : List (List Fmt.Stored))
      (acc : List ByteArray) (sent i : ℕ), TabTR rs ros acc → tss.length = ros.length →
    (∀ j, whole.getD (i + j) [] = tss.getD j []) →
    (∀ r ∈ rs, ∀ x ∈ r.opens, ∃ n, TabGood S x n) →
    wantedXL a (rds S) (xsOf whole) i (rdsFrom S sent rs) (ros.map (·.drawn)) =
      (tss.zip ros).flatMap fun y =>
        (y.1.flatMap fun t =>
          (Fmt.listOf ((Fmt.partOf t y.2.drawn.poss).map (· % 2 ^ a))).map fun x =>
            (PQ.storedKey (t.item == 1), x)) ++
        y.2.opens.flatMap fun x => x.2.1.map fun z => (x.1.tree - S.firstTree, z)
  | [], [], [], _, _, _, _, _, _, _ => rfl
  | [], [], _ :: _, _, _, _, _, hl, _, _ => by simp at hl
  | [], _ :: _, _, _, _, _, t, _, _, _ => t.elim
  | _ :: _, [], _, _, _, _, t, _, _, _ => t.elim
  | _ :: _, _ :: _, [], _, _, _, _, hl, _, _ => by simp at hl
  | r :: rs, ro :: ros, ts :: tss, acc, sent, i, t, hl, hw, hg => by
    have ih := wantedXL_from S a whole rs ros tss _ (sent + r.entry.roots) (i + 1) t.2
      (by simpa using hl) (getD_step whole i ts tss hw)
      fun r' hr' => hg r' (List.mem_cons_of_mem _ hr')
    have h0 : whole.getD i [] = ts := hw 0
    rw [List.zip_cons_cons, List.flatMap_cons, ← ih,
      ← tab_wantRound S _ _ t.1 (hg r List.mem_cons_self)]
    show (((xsAt (xsOf whole) i).flatMap fun o =>
      (o.list a ro.drawn).map fun x => (PQ.storedKey o.which, x)) ++ _) ++ _ = _
    rw [xsAt_xsOf, h0, List.flatMap_map]
    rfl

/-- What the drawn positions ask for, round by round: first the stored tables, each at the list of
its part of the draws, then the chain's own trees. `ros` are the rounds without the stored tables'
openings. It holds if there is one list of tables for each round, the rounds read fit the
description's (`TabTR`), and S's rounds open only trees that the chain itself sends (`TabGood`). -/
theorem wantedX_eq (S : Fmt.Spec) (a : ℕ) (tss : List (List Fmt.Stored))
    (ros : List Fmt.RoundOut) (hl : tss.length = ros.length) (ht : TabTR S.rounds ros [])
    (hg : ∀ r ∈ S.rounds, ∀ x ∈ r.opens, ∃ n, TabGood S x n) :
    wantedX a (rds S) (xsOf tss) (ros.map (·.drawn)) =
      (tss.zip ros).flatMap fun y =>
        (y.1.flatMap fun t =>
          (Fmt.listOf ((Fmt.partOf t y.2.drawn.poss).map (· % 2 ^ a))).map fun x =>
            (PQ.storedKey (t.item == 1), x)) ++
        y.2.opens.flatMap fun x => x.2.1.map fun z => (x.1.tree - S.firstTree, z) :=
  wantedXL_from S a tss S.rounds ros tss [] 0 0 ht hl (fun j => by rw [Nat.zero_add]) hg

/-- Parts that lie one behind the other end at or behind the place where they begin. -/
theorem partsFrom_mono : ∀ (ts : List Fmt.Stored) (i n : ℕ), Fmt.partsFrom i ts = some n → i ≤ n
  | [], i, n, h => by
    simp only [Fmt.partsFrom, Option.some.injEq] at h
    omega
  | t :: ts, i, n, h => by
    rw [Fmt.partsFrom] at h
    split at h
    · have := partsFrom_mono ts _ n h
      omega
    · cases h

/-- Parts that lie one behind the other end within the number that they reach. -/
theorem partsFrom_le : ∀ (ts : List Fmt.Stored) (i n : ℕ), Fmt.partsFrom i ts = some n →
    ∀ t ∈ ts, t.lo + t.count ≤ n
  | [], _, _, _, _, ht => by cases ht
  | s :: ts, i, n, h, t, ht => by
    rw [Fmt.partsFrom] at h
    split at h
    · rename_i hs
      have hlo : s.lo = i := by simpa using hs
      rcases List.mem_cons.1 ht with e | ht'
      · have := partsFrom_mono ts _ n h
        rw [e]
        omega
      · exact partsFrom_le ts _ n h t ht'
    · cases h

/-- No part of the draws is shortened, if each part ends within its round's draws, for rounds that
are numbered from k on. -/
theorem fullX_from (whole : List Fmt.Drawn) : ∀ (tss : List (List Fmt.Stored))
    (Ds : List Fmt.Drawn) (k : ℕ),
    List.Forall₂ (fun (ts : List Fmt.Stored) (D : Fmt.Drawn) =>
      ∀ t ∈ ts, t.lo + t.count ≤ D.poss.length) tss Ds →
    (∀ j, whole[k + j]? = Ds[j]?) →
    (((tss.zipIdx k).flatMap fun t => t.1.map fun s =>
        (⟨t.2, s.item == 1, s.lo, s.count⟩ : XO)).all fun o =>
      match whole[o.round]? with
      | none => false
      | some D => (o.raw D).length == o.count) = true
  | _, _, _, .nil, _ => rfl
  | ts :: tss, D :: Ds, k, .cons h t, hw => by
    have ih := fullX_from whole tss Ds (k + 1) t fun j => by
      have e := hw (j + 1)
      rw [show k + 1 + j = k + (j + 1) by omega, e]
      rfl
    have h0 : whole[k]? = some D := hw 0
    rw [List.zipIdx_cons, List.flatMap_cons, List.all_append, ih, Bool.and_true,
      List.all_eq_true]
    intro o ho
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 ho
    show (match whole[k]? with
      | none => false
      | some D => ((D.poss.drop s.lo).take s.count).length == s.count) = true
    rw [h0]
    show (((D.poss.drop s.lo).take s.count).length == s.count) = true
    rw [beq_iff_eq, List.length_take, List.length_drop]
    have := h s hs
    omega

/-- No part of the draws is shortened, if each part ends within its round's draws. -/
theorem fullX_true (tss : List (List Fmt.Stored)) (Ds : List Fmt.Drawn)
    (h : List.Forall₂ (fun (ts : List Fmt.Stored) (D : Fmt.Drawn) =>
      ∀ t ∈ ts, t.lo + t.count ≤ D.poss.length) tss Ds) :
    everyOpeningHasItsDraws (xsOf tss) Ds = true :=
  fullX_from Ds tss Ds 0 h fun j => by rw [Nat.zero_add]

end OnBytes.Tie

#print axioms OnBytes.Tie.xsAt_xsOf
#print axioms OnBytes.Tie.offStored_rounds
#print axioms OnBytes.Tie.storedB_eq
#print axioms OnBytes.Tie.wantedX_eq
#print axioms OnBytes.Tie.partsFrom_le
#print axioms OnBytes.Tie.fullX_true
